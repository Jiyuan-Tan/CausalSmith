import { afterEach, beforeAll, describe, expect, it } from "vitest";
import { execFile } from "node:child_process";
import { mkdtemp, mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import process from "node:process";
import { promisify } from "node:util";
import { withWpRegistryLock, writeWpRegistry } from "../src/presentation/wp_registry.js";
import { withBundleMetaLock } from "../src/presentation/meta_store.js";
import { withBundleEmitLock } from "../src/presentation/emit_lock.js";

const execFileP = promisify(execFile);
const TOOLS = join(import.meta.dirname, "..");
const TSX = join(TOOLS, "node_modules", "tsx", "dist", "cli.mjs");

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

/** A throwaway git checkout holding two bundles, committed on two different author dates so the
 *  backfill's "paper.tex last changed" lookup has something real to read. */
async function fixtureRepo(): Promise<{ repoRoot: string; presentation: string }> {
  const top = await mkdtemp(join(tmpdir(), "backfill-"));
  dirs.push(top);
  const repoRoot = join(top, "CausalSmith");
  const presentation = join(repoRoot, "doc", "presentation");
  const git = (args: string[], env: NodeJS.ProcessEnv = {}) =>
    execFileP("git", args, { cwd: top, env: { ...process.env, ...env } });
  await git(["init", "-q", "-b", "main"]);
  await git(["config", "user.email", "t@example.invalid"]);
  await git(["config", "user.name", "T"]);
  for (const [id, created] of [["stat_b_v1", "2026-07-21"], ["stat_a_v1", "2026-06-13"]] as const) {
    await mkdir(join(presentation, id), { recursive: true });
    await writeFile(join(presentation, id, "paper.tex"), `% ${id}\n\\documentclass{article}\n`);
    await writeFile(join(presentation, id, "meta.json"), `${JSON.stringify({
      qid: id.slice(0, -3), spec: "v1", title: id, tldr: "", abstract: "a", area: "Stat",
      authorship: "Jiyuan Tan", created, wp_number: null, score: 7, score_rationale: "r",
      license: "CC-BY-4.0",
    }, null, 2)}\n`);
  }
  await git(["add", "-A"]);
  await git(["commit", "-qm", "bundles"], { GIT_AUTHOR_DATE: "2026-08-25T12:00:00+00:00", GIT_COMMITTER_DATE: "2026-08-25T12:00:00+00:00" });
  return { repoRoot, presentation };
}

async function runBackfill(repoRoot: string, write: boolean) {
  return execFileP(process.execPath, [
    TSX, join(TOOLS, "bin", "backfill_paper_identity.ts"), "--repo-root", repoRoot,
    ...(write ? ["--write"] : []),
  ], { cwd: TOOLS, maxBuffer: 16 * 1024 * 1024 });
}

const readJson = async (path: string) => JSON.parse(await readFile(path, "utf8")) as Record<string, unknown>;

describe("paper-identity backfill", () => {
  beforeAll(() => {
    // The script is spawned through tsx; the suite's own node is reused, nothing is installed.
    expect(TSX).toContain("tsx");
  });

  it("ranks by (created, bundle id), leaves the tree untouched on a dry run", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    const before = await readFile(join(presentation, "stat_a_v1", "meta.json"), "utf8");
    const { stdout } = await runBackfill(repoRoot, false);
    expect(stdout).toContain("DRY RUN");
    expect(stdout).toContain("CSWP-2026-001");
    expect(await readFile(join(presentation, "stat_a_v1", "meta.json"), "utf8")).toBe(before);
    await expect(readFile(join(presentation, "_wp_registry.json"), "utf8")).rejects.toThrow("ENOENT");
  });

  it("writes the registry and both bundles, preserving externally owned keys", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    expect(await readJson(join(presentation, "_wp_registry.json")))
      .toEqual({ stat_a_v1: "CSWP-2026-001", stat_b_v1: "CSWP-2026-002" });
    const a = await readJson(join(presentation, "stat_a_v1", "meta.json"));
    expect(a.wp_number).toBe("CSWP-2026-001");
    expect(a.created).toBe("2026-06-13");
    expect(a.revised).toBe("2026-08-25"); // the commit's author date, later than created ⇒ v2
    expect(a.version).toBe(2);
    // the backfill owns four fields and must not disturb anything else
    expect(a.authorship).toBe("Jiyuan Tan");
    expect(a.score).toBe(7);
    expect(a.license).toBe("CC-BY-4.0");
    expect(await readFile(join(presentation, "stat_a_v1", "meta.json"), "utf8")).toMatch(/\n\}\n$/);
  });

  it("is a no-op when rerun over a completed backfill", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    const snapshot = await readFile(join(presentation, "stat_b_v1", "meta.json"), "utf8");
    const { stdout } = await runBackfill(repoRoot, true);
    expect(stdout).toContain("0 meta.json to update");
    expect(stdout).toContain("registry unchanged");
    expect(await readFile(join(presentation, "stat_b_v1", "meta.json"), "utf8")).toBe(snapshot);
  });

  it("resumes after an interruption between the registry write and the metadata writes", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    // A complete run, then rewind the bundle files to exactly the state an interruption right
    // after the registry write would have left: registry present, no meta.json touched yet.
    await runBackfill(repoRoot, true);
    const registry = await readFile(join(presentation, "_wp_registry.json"), "utf8");
    await execFileP("git", ["checkout", "--", "CausalSmith/doc/presentation"], { cwd: join(repoRoot, "..") });
    await writeFile(join(presentation, "_wp_registry.json"), registry);
    expect((await readJson(join(presentation, "stat_a_v1", "meta.json"))).wp_number).toBeNull();

    // The rerun must FINISH the job — not refuse it as a partial backfill, and not renumber.
    const { stdout } = await runBackfill(repoRoot, true);
    expect(stdout).toContain("2 meta.json to update");
    expect(await readFile(join(presentation, "_wp_registry.json"), "utf8")).toBe(registry);
    expect((await readJson(join(presentation, "stat_a_v1", "meta.json"))).wp_number).toBe("CSWP-2026-001");
    expect((await readJson(join(presentation, "stat_b_v1", "meta.json"))).wp_number).toBe("CSWP-2026-002");
  });

  it("gives a bundle added after the initial backfill max+1, never a colliding rank", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    // A newcomer whose `created` would rank it FIRST — ranking again would hand it 001, which
    // stat_a_v1 already has and may already have published.
    await mkdir(join(presentation, "stat_new_v1"), { recursive: true });
    await writeFile(join(presentation, "stat_new_v1", "paper.tex"), "% new\n");
    await writeFile(join(presentation, "stat_new_v1", "meta.json"), `${JSON.stringify({
      qid: "stat_new", spec: "v1", title: "N", tldr: "", abstract: "a", area: "Stat",
      authorship: null, created: "2026-01-02", wp_number: null, score: null, score_rationale: null,
    }, null, 2)}\n`);
    await runBackfill(repoRoot, true);
    const registry = await readJson(join(presentation, "_wp_registry.json"));
    expect(registry).toEqual({
      stat_a_v1: "CSWP-2026-001", stat_b_v1: "CSWP-2026-002", stat_new_v1: "CSWP-2026-003",
    });
    expect(new Set(Object.values(registry)).size).toBe(3);
  });
});

describe("paper-identity backfill: the registry transaction", () => {
  it("writes nothing at all when any bundle fails validation", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    const path = join(presentation, "stat_b_v1", "meta.json");
    const before = await readFile(path, "utf8");
    await writeFile(path, before.replace('"2026-07-21"', '"2026-02-31"'));
    await expect(runBackfill(repoRoot, true)).rejects.toThrow();
    // the registry is authoritative and permanent: a bad input must not leave numbers behind
    await expect(readFile(join(presentation, "_wp_registry.json"), "utf8")).rejects.toThrow("ENOENT");
    expect((await readJson(join(presentation, "stat_a_v1", "meta.json"))).wp_number).toBeNull();
  });

  it("waits for the registry lock and allocates against what it finds there", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    // Stand in for a P4 emit holding the lock and taking CSWP-2026-001 while the backfill starts.
    let releasedAt = 0;
    const holder = withWpRegistryLock(repoRoot, async () => {
      await writeWpRegistry(repoRoot, { some_p4_bundle: "CSWP-2026-001" });
      await new Promise((r) => setTimeout(r, 1_200));
      releasedAt = Date.now();
    });
    await new Promise((r) => setTimeout(r, 100));
    const started = Date.now();
    const run = runBackfill(repoRoot, true);
    await holder;
    await run;
    expect(Date.now() - started).toBeGreaterThan(900); // it blocked rather than racing
    expect(releasedAt).toBeGreaterThan(0);
    const registry = await readJson(join(presentation, "_wp_registry.json"));
    // the concurrent assignment survived, and the backfill allocated around it
    expect(registry.some_p4_bundle).toBe("CSWP-2026-001");
    expect(Object.keys(registry).sort()).toEqual(["some_p4_bundle", "stat_a_v1", "stat_b_v1"]);
    expect(new Set(Object.values(registry)).size).toBe(3);
    expect(Object.values(registry)).not.toContain("CSWP-2026-001".replace("001", "001x"));
  });
});

describe("paper-identity backfill: r3", () => {
  const ENV = "CAUSALSMITH_PAPER_SERIES_PREFIX";

  async function runIn(repoRoot: string, args: string[], env: NodeJS.ProcessEnv = {}) {
    return execFileP(process.execPath, [TSX, join(TOOLS, "bin", "backfill_paper_identity.ts"), ...args], {
      cwd: TOOLS, maxBuffer: 16 * 1024 * 1024, env: { ...process.env, ...env },
    }).catch((e: { stdout?: string; stderr?: string; code?: number }) => e);
  }

  it("refuses a recorded number from another series before writing any registry", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    const path = join(presentation, "stat_a_v1", "meta.json");
    await writeFile(path, (await readFile(path, "utf8")).replace('"wp_number": null', '"wp_number": "CSWP-2026-001"'));
    const r = await runIn(repoRoot, ["--repo-root", repoRoot, "--write"], { [ENV]: "AIWP7" });
    expect(String((r as { stderr?: string }).stderr)).toMatch(/belongs to series CSWP, but this checkout publishes AIWP7/);
    await expect(readFile(join(presentation, "_wp_registry.json"), "utf8")).rejects.toThrow("ENOENT");
  });

  it("refuses a recorded number whose year disagrees with created, and an untrimmed one", { timeout: 60_000 }, async () => {
    for (const [bad, pattern] of [["CSWP-2025-001", /series year 2025/], [" CSWP-2026-001", /malformed/]] as const) {
      const { repoRoot, presentation } = await fixtureRepo();
      const path = join(presentation, "stat_a_v1", "meta.json");
      await writeFile(path, (await readFile(path, "utf8")).replace('"wp_number": null', `"wp_number": ${JSON.stringify(bad)}`));
      const r = await runIn(repoRoot, ["--repo-root", repoRoot, "--write"]);
      expect(String((r as { stderr?: string }).stderr)).toMatch(pattern);
      await expect(readFile(join(presentation, "_wp_registry.json"), "utf8")).rejects.toThrow("ENOENT");
    }
  });

  it("accepts a relative --repo-root", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    const r = await execFileP(process.execPath, [
      TSX, join(TOOLS, "bin", "backfill_paper_identity.ts"), "--repo-root", "./CausalSmith", "--write",
    ], { cwd: join(repoRoot, ".."), maxBuffer: 16 * 1024 * 1024 });
    expect(r.stdout).toContain("CSWP-2026-001");
    expect(await readJson(join(presentation, "_wp_registry.json")))
      .toEqual({ stat_a_v1: "CSWP-2026-001", stat_b_v1: "CSWP-2026-002" });
  });

  it("skips a bundle whose identity moved after planning, writing nothing for it", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    // Hold the registry lock so the run blocks in phase 2 with phase 1 already planned, then
    // change a bundle underneath it — exactly what a concurrent P4 emit would do.
    let changed = "";
    const holder = withWpRegistryLock(repoRoot, async () => {
      await new Promise((r) => setTimeout(r, 1_500));
      const path = join(presentation, "stat_a_v1", "meta.json");
      const meta = JSON.parse(await readFile(path, "utf8")) as Record<string, unknown>;
      meta.version = 5;
      meta.revised = "2026-09-01";
      meta.versions = [{ v: 1, date: "2026-06-13", paper_sha256: "aaa" }];
      changed = `${JSON.stringify(meta, null, 2)}\n`;
      await writeFile(path, changed);
    });
    await new Promise((r) => setTimeout(r, 150));
    const run = runIn(repoRoot, ["--repo-root", repoRoot, "--write"]);
    await holder;
    const r = await run;
    expect(String((r as { stderr?: string }).stderr)).toMatch(/SKIPPED 1 bundle\(s\).*stat_a_v1/s);
    expect((r as { code?: number }).code).toBe(1);
    // untouched: the planned patch was NOT applied over the newer state
    expect(await readFile(join(presentation, "stat_a_v1", "meta.json"), "utf8")).toBe(changed);
    // the other bundle still completed
    expect((await readJson(join(presentation, "stat_b_v1", "meta.json"))).wp_number).toBe("CSWP-2026-002");
  });
});

describe("paper-identity backfill: the hash is taken inside the locked transaction", () => {
  it("skips a bundle whose paper.tex changed while it waited for the metadata lock", { timeout: 60_000 }, async () => {
    // The stale-hash window: phase 1 hashes A, phase 3 then WAITS for the bundle's metadata lock,
    // and a concurrent P4 re-pins paper.tex to B in between. Hashing before acquiring the lock
    // recorded A as the current version's hash — wrong, and enough to make the next identical
    // emit bump the version over nothing.
    const { repoRoot, presentation } = await fixtureRepo();
    const bundle = join(presentation, "stat_a_v1");
    const original = await readFile(join(bundle, "paper.tex"), "utf8");
    let changedTo = "";
    const holder = withBundleMetaLock(bundle, async () => {
      await new Promise((r) => setTimeout(r, 1_800));
      changedTo = `${original}% re-pinned by a concurrent emit\n`;
      await writeFile(join(bundle, "paper.tex"), changedTo);
    });
    await new Promise((r) => setTimeout(r, 120));
    const run = execFileP(process.execPath, [
      TSX, join(TOOLS, "bin", "backfill_paper_identity.ts"), "--repo-root", repoRoot, "--write",
    ], { cwd: TOOLS, maxBuffer: 16 * 1024 * 1024 })
      .catch((e: { stdout?: string; stderr?: string; code?: number }) => e);
    await holder;
    const r = await run;

    expect(String((r as { stderr?: string }).stderr)).toMatch(/SKIPPED 1 bundle\(s\).*stat_a_v1/s);
    expect((r as { code?: number }).code).toBe(1);
    const meta = await readJson(join(bundle, "meta.json"));
    // nothing was written for it: no number, and certainly not the stale hash of the old bytes
    expect(meta.wp_number).toBeNull();
    expect(meta.versions).toBeUndefined();
    expect(await readFile(join(bundle, "paper.tex"), "utf8")).toBe(changedTo);
    // the untouched sibling still completed
    expect((await readJson(join(presentation, "stat_b_v1", "meta.json"))).wp_number).toBe("CSWP-2026-002");
  });
});

describe("paper-identity backfill: the emit lock", () => {
  it("skips a bundle being emitted and completes the others", { timeout: 60_000 }, async () => {
    // A live P4 is rewriting paper.tex. Nothing the backfill records about that manuscript can be
    // trusted while that is true, so it declines the bundle rather than racing it.
    const { repoRoot, presentation } = await fixtureRepo();
    const busy = join(presentation, "stat_a_v1");
    const holder = withBundleEmitLock(busy, () => new Promise((r) => setTimeout(r, 2_500)), { wait: false });
    await new Promise((r) => setTimeout(r, 120));
    const r = await execFileP(process.execPath, [
      TSX, join(TOOLS, "bin", "backfill_paper_identity.ts"), "--repo-root", repoRoot, "--write",
    ], { cwd: TOOLS, maxBuffer: 16 * 1024 * 1024 })
      .catch((e: { stdout?: string; stderr?: string; code?: number }) => e);
    await holder;

    expect(String((r as { stderr?: string }).stderr)).toMatch(/stat_a_v1: an emit of this bundle is in progress/);
    expect((r as { code?: number }).code).toBe(1);
    // nothing written for the busy bundle...
    expect((await readJson(join(busy, "meta.json"))).wp_number).toBeNull();
    // ...and the idle one completed, so one busy paper does not stall the batch
    expect((await readJson(join(presentation, "stat_b_v1", "meta.json"))).wp_number).toBe("CSWP-2026-002");
    // the number was still reserved for the skipped bundle, so a rerun finishes it unchanged
    expect((await readJson(join(presentation, "_wp_registry.json"))).stat_a_v1).toBe("CSWP-2026-001");
  });

  it("releases every lock it took, leaving only the gitignored sentinels", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    // proper-lockfile's `<sentinel>.lock` DIRECTORY is the mutex; none may survive the run.
    for (const dir of [presentation, join(presentation, "stat_a_v1"), join(presentation, "stat_b_v1")]) {
      expect((await readdir(dir)).filter((e) => e.endsWith(".lock.lock"))).toEqual([]);
    }
    // The sentinels themselves do remain, and are the exact names .gitignore lists.
    const bundleEntries = await readdir(join(presentation, "stat_a_v1"));
    expect(bundleEntries.filter((e) => e.endsWith(".lock")).sort()).toEqual([".emit.lock", ".meta.lock"]);
    expect((await readdir(presentation)).filter((e) => e.endsWith(".lock"))).toEqual([".wp_registry.lock"]);
  });
});

describe("paper-identity backfill: it FILLS, it never rewrites", () => {
  it("leaves a bundle P4 has since advanced completely alone", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    // P4 moves the paper on: v3, a newer date, a full history.
    const path = join(presentation, "stat_a_v1", "meta.json");
    const advanced = { ...(await readJson(path)), version: 3, revised: "2026-09-10",
      versions: [
        { v: 1, date: "2026-06-13", paper_sha256: "a" },
        { v: 2, date: "2026-08-25", paper_sha256: "b" },
        { v: 3, date: "2026-09-10", paper_sha256: "c" },
      ] };
    const text = `${JSON.stringify(advanced, null, 2)}\n`;
    await writeFile(path, text);
    const { stdout } = await runBackfill(repoRoot, true);
    expect(await readFile(path, "utf8")).toBe(text); // not rolled back to v2
    expect(stdout).toMatch(/already has identity/);
  });

  it("does not manufacture a v2 on a rerun just because git dates moved", { timeout: 60_000 }, async () => {
    const { repoRoot, presentation } = await fixtureRepo();
    await runBackfill(repoRoot, true);
    const before = await readFile(join(presentation, "stat_b_v1", "meta.json"), "utf8");
    // a later commit touching paper.tex — the kind a date-pin commit produces
    await writeFile(join(presentation, "stat_b_v1", "paper.tex"), "% touched\n\\documentclass{article}\n");
    const git = (a: string[]) => execFileP("git", a, { cwd: join(repoRoot, "..") });
    await git(["add", "-A"]);
    await git(["commit", "-qm", "pin dates"]);
    await runBackfill(repoRoot, true);
    expect(await readFile(join(presentation, "stat_b_v1", "meta.json"), "utf8")).toBe(before);
  });
});
