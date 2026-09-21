import { afterEach, describe, expect, it, vi } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join } from "node:path";
import type { PaperDeps, StageIO } from "../src/presentation/pipeline.js";

const subprocess = vi.hoisted(() => {
  const fn = vi.fn();
  // Node's real `execFile` carries a `util.promisify.custom` that resolves `{stdout, stderr}`.
  // A bare mock does not, so `promisify(mock)` resolves only the first callback argument and
  // every `const { stdout } = await execFileP(...)` in the stage reads `undefined`. The stage
  // tests that stop early never notice; a completed run dies on it. Reproduce the real contract.
  Object.defineProperty(fn, Symbol.for("nodejs.util.promisify.custom"), {
    value: (...args: unknown[]) =>
      new Promise((resolve, reject) => {
        fn(...args, (err: unknown, stdout: unknown, stderr: unknown) =>
          err ? reject(err) : resolve({ stdout: stdout ?? "", stderr: stderr ?? "" }));
      }),
  });
  return fn;
});
vi.mock("node:child_process", async (importOriginal) => ({
  ...await importOriginal<typeof import("node:child_process")>(),
  execFile: subprocess,
}));

import { stageP4 } from "../src/presentation/stages/p4_emit.js";
import { stageP5 } from "../src/presentation/stages/p5_review.js";
import { assertP2AssemblyFresh, recordP2Assembly } from "../src/presentation/assembly_freshness.js";
import { readWpRegistry } from "../src/presentation/wp_registry.js";
import { fileSha256 } from "../src/presentation/paper_stamp.js";
import { readBundleMeta, updateBundleMeta } from "../src/presentation/meta_store.js";
import { withBundleEmitLock } from "../src/presentation/emit_lock.js";
import { loadPriorReview } from "../src/presentation/revision_brief.js";
import { freshPaperState } from "../src/presentation/state.js";

const dirs: string[] = [];
afterEach(async () => {
  subprocess.mockReset();
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

/** A minimal bundle that reaches the compile. The sentinel on the post-compile `git` call stops
 *  the stage right after it, which is exactly the boundary the stamp must already be written at. */
async function p4Fixture(prevMeta?: Record<string, unknown>) {
  const repoRoot = await mkdtemp(join(tmpdir(), "p4-stamp-"));
  dirs.push(repoRoot);
  const outDir = join(repoRoot, "doc", "presentation", "stat_demo_v1");
  for (const dir of ["sections", "proofs"]) await mkdir(join(outDir, dir), { recursive: true });
  for (const [name, body] of Object.entries({
    "paper.tex": "\\documentclass{article}\n\\date{\\today}\n\\begin{document}\nA finite example.\n\\end{document}\n",
    "appendix_proofs.tex": "",
    "front_matter.tex": "A finite example.",
    "formal_layer.json": JSON.stringify({ commit: null, blocks: [] }),
    "outline.md": "# Title\nExample\n# Sections\n",
    "references.bib": "",
    "equivalence_cache.json": "{}",
  })) await writeFile(join(outDir, name), body);
  if (prevMeta) await writeFile(join(outDir, "meta.json"), `${JSON.stringify(prevMeta, null, 2)}\n`);
  await recordP2Assembly(outDir);
  const runCodex = vi.fn(async () => { throw new Error("unexpected paid dispatch"); });
  const io = {
    outDir,
    state: { notes: [] },
    ctx: { repoRoot, qid: "stat_demo", spec: "v1", deps: { dryRun: false, runCodex } },
  } as unknown as StageIO;
  subprocess.mockImplementation((file, _args, _options, callback) => {
    callback(file === "latexmk" ? null : new Error("post-compile sentinel"), "");
  });
  return { io, outDir, repoRoot, runCodex };
}

describe("P4 stamps the bundle before it compiles", () => {
  it("assigns a number, pins the date and writes paper_stamp.tex ahead of latexmk", async () => {
    const { io, outDir, repoRoot } = await p4Fixture({ created: "2026-07-21" });
    let stampAtCompile = "";
    let paperAtCompile = "";
    subprocess.mockImplementation((file, _args, _options, callback) => {
      if (file === "latexmk") {
        // the stamp is a compile INPUT, so it must already be on disk at this instant
        stampAtCompile = readFileSync(join(outDir, "paper_stamp.tex"), "utf8");
        paperAtCompile = readFileSync(join(outDir, "paper.tex"), "utf8");
        return callback(null, "");
      }
      callback(new Error("post-compile sentinel"), "");
    });
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    expect(stampAtCompile).toContain("\\renewcommand*{\\csstampid}{CSWP-2026-001v1}");
    expect(stampAtCompile).toContain("\\renewcommand*{\\csstampdate}{21 Jul 2026}");
    expect(paperAtCompile).toContain("\\date{\\cspaperdate}");
    expect(await readFile(join(outDir, "paper.tex"), "utf8")).toContain("\\date{\\cspaperdate}");
    expect(await readWpRegistry(repoRoot, "CSWP")).toEqual({ [basename(outDir)]: "CSWP-2026-001" });
    expect(io.state.notes.some((n) => n.includes("CSWP-2026-001v1"))).toBe(true);
  });

  it("leaves the Zenodo deposit sidecar untouched and outside the assembly digest", async () => {
    const { io, outDir } = await p4Fixture({ created: "2026-07-21" });
    // written by bin/zenodo_deposit.ts; losing it would orphan a live deposit
    const sidecar = '{\n  "deposition_id": 4242,\n  "conceptrecid": 4241,\n  "state": "unsubmitted",\n  "environment": "sandbox"\n}\n';
    await writeFile(join(outDir, "zenodo.json"), sidecar);
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    expect(await readFile(join(outDir, "zenodo.json"), "utf8")).toBe(sidecar);
    // and it is not an authored assembly input, so rewriting it cannot block the next emit
    await writeFile(join(outDir, "zenodo.json"), sidecar.replace("unsubmitted", "done"));
    await expect(assertP2AssemblyFresh(outDir)).resolves.toBeUndefined();
  });

  it("preserves a sandbox DOI in meta while keeping it off page 1", async () => {
    const { io, outDir } = await p4Fixture({
      created: "2026-07-21", wp_number: "CSWP-2026-001", doi: "10.5072/zenodo.77", version_doi: "10.5072/zenodo.78",
    });
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    const stamp = await readFile(join(outDir, "paper_stamp.tex"), "utf8");
    expect(stamp).toContain("\\renewcommand*{\\csstampdoi}{}");
    expect(stamp).not.toContain("10.5072");
    // the reservation itself is immutable state and must survive the emit verbatim
    expect(io.state.notes.some((n) =>
      n.includes("no published DOI on page 1") && n.includes("10.5072/zenodo.77"))).toBe(true);
  });

  it("re-uses the recorded number and does not renumber or re-date a second emit", async () => {
    const { io, outDir } = await p4Fixture({ created: "2026-07-21" });
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    const first = await readFile(join(outDir, "paper_stamp.tex"), "utf8");
    const sha = await fileSha256(join(outDir, "paper.tex"));
    // simulate the meta P4 would have written had the emit run to completion
    await writeFile(join(outDir, "meta.json"), `${JSON.stringify({
      created: "2026-07-21", wp_number: "CSWP-2026-001", version: 1, revised: "2026-07-21",
      versions: [{ v: 1, date: "2026-07-21", paper_sha256: sha }],
      doi: "10.5281/zenodo.5", version_doi: "10.5281/zenodo.6", score: 7.2, score_rationale: "ok",
    }, null, 2)}\n`);
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    const second = await readFile(join(outDir, "paper_stamp.tex"), "utf8");
    expect(second).toContain("\\renewcommand*{\\csstampid}{CSWP-2026-001v1}");
    // the DOI arrived between emits: it reaches page 1 through this one small file
    expect(second).toContain("\\renewcommand*{\\csstamplink}{https://doi.org/10.5281/zenodo.5}");
    expect(first).not.toContain("doi.org");
  });
});

describe("P4 holds the bundle's emit lock for the whole emit", () => {
  it("makes a second concurrent emit of the same bundle wait rather than interleave", async () => {
    const { io, outDir } = await completedP4Fixture();
    const order: string[] = [];
    // Stand in for another emit already in progress on this bundle.
    const holder = withBundleEmitLock(outDir, async () => {
      order.push("other-emit-in");
      await new Promise((r) => setTimeout(r, 700));
      order.push("other-emit-out");
    }, { wait: false });
    await new Promise((r) => setTimeout(r, 80));
    const mine = stageP4(io).then(() => order.push("p4-done"));
    await Promise.all([holder, mine]);
    // P4 did not begin until the other emit had finished
    expect(order).toEqual(["other-emit-in", "other-emit-out", "p4-done"]);
    expect((await readBundleMeta(outDir)).wp_number).toBe(`CSWP-${new Date().getUTCFullYear()}-001`);
  }, 20_000);

  it("releases the lock when the emit fails, so the bundle is not wedged", async () => {
    const { io, outDir } = await completedP4Fixture({ qid: "stat_demo", created: "2026-02-31" });
    await expect(stageP4(io)).rejects.toThrow(/real calendar date/);
    // still acquirable immediately, and without waiting
    expect(await withBundleEmitLock(outDir, async () => "free", { wait: false })).toBe("free");
  });

  it("takes no emit lock for a dry run, which writes only its stub", async () => {
    const { io, outDir } = await p4Fixture({ created: "2026-07-21" });
    (io.ctx.deps as { dryRun: boolean }).dryRun = true;
    const holder = withBundleEmitLock(outDir, () => new Promise((r) => setTimeout(r, 400)), { wait: false });
    await new Promise((r) => setTimeout(r, 60));
    await expect(stageP4(io)).resolves.toBeUndefined(); // not blocked by the holder
    expect(await readFile(join(outDir, "p4.stub"), "utf8")).toBe("dry-run\n");
    await holder;
  });
});

describe("P4 dry run", () => {
  it("writes its stub without needing a valid series, because it mints no number", async () => {
    const { io, outDir } = await p4Fixture({ created: "2026-07-21" });
    (io.ctx.deps as { dryRun: boolean }).dryRun = true;
    process.env.CAUSALSMITH_PAPER_SERIES_PREFIX = "bad-prefix";
    try {
      await expect(stageP4(io)).resolves.toBeUndefined();
      expect(await readFile(join(outDir, "p4.stub"), "utf8")).toBe("dry-run\n");
      // and nothing was stamped or numbered
      await expect(readFile(join(outDir, "paper_stamp.tex"), "utf8")).rejects.toThrow("ENOENT");
    } finally {
      delete process.env.CAUSALSMITH_PAPER_SERIES_PREFIX;
    }
  });

  it("still refuses a real emit under the same bad configuration, before writing anything", async () => {
    const { io, outDir } = await p4Fixture({ created: "2026-07-21" });
    const macrosBefore = await readFile(join(outDir, "paper_macros.tex"), "utf8").catch(() => null);
    process.env.CAUSALSMITH_PAPER_SERIES_PREFIX = "bad-prefix";
    try {
      await expect(stageP4(io)).rejects.toThrow(/Invalid paperSeriesPrefix/);
      expect(await readFile(join(outDir, "paper_macros.tex"), "utf8").catch(() => null)).toBe(macrosBefore);
      expect(subprocess).not.toHaveBeenCalled();
    } finally {
      delete process.env.CAUSALSMITH_PAPER_SERIES_PREFIX;
    }
  });
});

describe("P5 records what the referee actually read", () => {
  async function p5Fixture(paper: string) {
    const dir = await mkdtemp(join(tmpdir(), "p5-stamp-"));
    dirs.push(dir);
    await writeFile(join(dir, "paper.tex"), paper);
    await writeFile(join(dir, "formal_layer.json"), '{"commit":null,"blocks":[]}\n');
    await writeFile(join(dir, "lean_snippets.json"), '{"commit":"","snippets":{}}\n');
    await writeFile(join(dir, "meta.json"), '{\n  "qid": "q",\n  "wp_number": "CSWP-2026-001"\n}\n');
    const deps: PaperDeps = {
      runClaude: async () => "",
      runCodex: async () => ({
        stdout: JSON.stringify({
          recommendation: "minor_revision", score: 7.5, score_rationale: "Solid.",
          summary: "s", strengths: [], findings: [], questions_for_authors: [],
        }),
        stderr: "",
      }),
      dryRun: false,
    };
    const io = {
      ctx: { repoRoot: dir, qid: "q", spec: "v1", deps, outDir: dir },
      state: freshPaperState("q", "v1"),
      bank: {} as StageIO["bank"],
      outDir: dir,
    } satisfies StageIO;
    return { io, dir };
  }

  it("hashes the on-disk paper.tex, not the stripped reviewer copy, so the site can match review to version", async () => {
    // A `% lean:` comment is in the file but NOT in what refereeTexFor sends; hashing the
    // referee's copy would therefore produce a digest that matches nothing in the bundle.
    const paper = "A submission. % lean: demo_decl\n";
    const { io, dir } = await p5Fixture(paper);
    await stageP5(io);
    const review = JSON.parse(await readFile(join(dir, "p5_review.json"), "utf8"));
    expect(review.manuscript_sha256).toBe(await fileSha256(join(dir, "paper.tex")));
    expect(review.reviewed_at).toMatch(/^\d{4}-\d{2}-\d{2}$/);
    // the score sink is untouched by the addition
    expect(JSON.parse(await readFile(join(dir, "meta.json"), "utf8")).score).toBe(7.5);
  });

  it("hashes the bytes the referee was SENT, even if paper.tex changes while the model runs", async () => {
    // The race the audit found: P4 re-emits mid-review, and P5 then stamps the NEW manuscript's
    // hash onto a review of the OLD one — the precise claim this field exists to make.
    const dir = await mkdtemp(join(tmpdir(), "p5-race-"));
    dirs.push(dir);
    const reviewed = "the manuscript the referee actually read\n";
    await writeFile(join(dir, "paper.tex"), reviewed);
    await writeFile(join(dir, "formal_layer.json"), '{"commit":null,"blocks":[]}\n');
    await writeFile(join(dir, "lean_snippets.json"), '{"commit":"","snippets":{}}\n');
    const reviewedSha = await fileSha256(join(dir, "paper.tex"));
    const deps: PaperDeps = {
      runClaude: async () => "",
      runCodex: async (args) => {
        // the referee sees the original text...
        expect(args.prompt).toContain("the manuscript the referee actually read");
        // ...and a concurrent P4 replaces the file before the answer comes back
        await writeFile(join(dir, "paper.tex"), "a different, later manuscript\n");
        return {
          stdout: JSON.stringify({
            recommendation: "accept", score: 9, score_rationale: "", summary: "s",
            strengths: [], findings: [], questions_for_authors: [],
          }),
          stderr: "",
        };
      },
      dryRun: false,
    };
    const io = {
      ctx: { repoRoot: dir, qid: "q", spec: "v1", deps, outDir: dir },
      state: freshPaperState("q", "v1"), bank: {} as StageIO["bank"], outDir: dir,
    } satisfies StageIO;
    await stageP5(io);
    const review = JSON.parse(await readFile(join(dir, "p5_review.json"), "utf8"));
    expect(review.manuscript_sha256).toBe(reviewedSha);
    expect(review.manuscript_sha256).not.toBe(await fileSha256(join(dir, "paper.tex")));
  });

  it("injects the score without reverting a DOI written while the referee was running", async () => {
    const { io, dir } = await p5Fixture("a submission\n");
    await updateBundleMeta(dir, (m) => { m.doi = "10.5281/zenodo.31"; m.authorship = "Jiyuan Tan"; });
    await stageP5(io);
    const meta = await readBundleMeta(dir);
    expect(meta.score).toBe(7.5);
    expect(meta.doi).toBe("10.5281/zenodo.31");
    expect(meta.authorship).toBe("Jiyuan Tan");
    expect(meta.wp_number).toBe("CSWP-2026-001"); // the fixture's pre-existing key, untouched
  });

  it("keeps the archived-history behaviour, so every draw carries its own provenance", async () => {
    const { io, dir } = await p5Fixture("v1 text\n");
    await stageP5(io);
    const firstSha = JSON.parse(await readFile(join(dir, "p5_review.json"), "utf8")).manuscript_sha256;
    await writeFile(join(dir, "paper.tex"), "v2 text\n");
    await stageP5(io);
    const archived = JSON.parse(await readFile(join(dir, "p5_review_history", "round_000.json"), "utf8"));
    const current = JSON.parse(await readFile(join(dir, "p5_review.json"), "utf8"));
    expect(archived.manuscript_sha256).toBe(firstSha);
    expect(current.manuscript_sha256).not.toBe(firstSha);
  });

  it("leaves every existing reader of p5_review.json working on a legacy file that lacks the fields", async () => {
    const dir = await mkdtemp(join(tmpdir(), "p5-legacy-"));
    dirs.push(dir);
    await writeFile(join(dir, "p5_review.json"), `${JSON.stringify({
      recommendation: "major_revision", score: 5.5, summary: "s",
      findings: [{ severity: "major", section: "2", issue: "i", fix: "f" }],
    }, null, 2)}\n`);
    const prior = await loadPriorReview(dir);
    expect(prior).toMatchObject({ recommendation: "major_revision", score: 5.5 });
    expect(prior!.findings).toHaveLength(1);
  });
});

/**
 * A P4 emit that runs ALL THE WAY to the final metadata write.
 *
 * Every other stage test here stops at the compile, which is why the audit could delete the
 * identity fields — or reset authorship, or drop an unknown key — from P4's output and still see
 * green. The only seams stubbed are the external processes (git, latexmk, lake, the paper-index
 * lint) and the one model call; pandoc runs for real, and so does the whole merge.
 */
async function completedP4Fixture(prevMeta?: Record<string, unknown>) {
  const repoRoot = await mkdtemp(join(tmpdir(), "p4-full-"));
  dirs.push(repoRoot);
  const outDir = join(repoRoot, "doc", "presentation", "stat_demo_v1");
  const leanSubdir = join("CausalSmith", "Stat", "Demo_Research");
  await mkdir(join(repoRoot, leanSubdir), { recursive: true });
  for (const dir of ["sections", "proofs"]) await mkdir(join(outDir, dir), { recursive: true });
  const modPrefix = "CausalSmith.Stat.Demo_Research";
  for (const [name, body] of Object.entries({
    "paper.tex": "\\documentclass{article}\n\\date{\\today}\n\\begin{document}\n\\begin{abstract}\nA finite example.\n\\end{abstract}\nBody text.\n\\end{document}\n",
    "appendix_proofs.tex": "",
    "front_matter.tex": "A finite example.",
    "formal_layer.json": JSON.stringify({ commit: null, blocks: [] }),
    "outline.md": "# Title\nA Demonstration Paper\n# Sections\n",
    "references.bib": "",
    "equivalence_cache.json": "{}",
    // Seeds modTargets, so P4 has a module to index without a crosswalk entry to resolve.
    "paper_library_index.json": JSON.stringify({ modules: { [modPrefix]: {} }, entries: [] }),
  })) await writeFile(join(outDir, name), body);
  if (prevMeta) await writeFile(join(outDir, "meta.json"), `${JSON.stringify(prevMeta, null, 2)}\n`);
  await recordP2Assembly(outDir);

  const indexed = {
    modules: { [modPrefix]: {} },
    entries: [{
      name: `${modPrefix}.demo_bound`, module: modPrefix, file: "Demo.lean", line: 1,
      kind: "theorem", statement: "theorem demo_bound : True", source: "theorem demo_bound : True := trivial",
      doc: "A demonstration bound.",
    }],
  };
  /** Runs when latexmk is invoked — lets a test simulate a concurrent writer mid-emit. */
  let duringCompile: (() => void) | null = null;
  subprocess.mockImplementation((file: string, args: string[], _options: unknown, callback: Function) => {
    if (file === "lake" && args.includes("paper_index")) {
      writeFileSync(args[args.indexOf("--out") + 1]!, JSON.stringify(indexed));
    }
    if (file === "latexmk") duringCompile?.();
    // git rev-parse wants a sha on stdout; every other call only has to succeed.
    callback(null, "0".repeat(40) + "\n", "");
    return undefined;
  });

  const runCodex = vi.fn(async () => ({ stdout: "A one-line demonstration summary.", stderr: "" }));
  const io = {
    outDir,
    state: { ...freshPaperState("stat_demo", "v1"), notes: [] },
    bank: { leanSubdir, crosswalk: [], graph: { nodes: [], edges: [] }, noteMd: "" },
    ctx: { repoRoot, qid: "stat_demo", spec: "v1", outDir, deps: { dryRun: false, runCodex } },
  } as unknown as StageIO;
  return { io, outDir, repoRoot, runCodex, onCompile: (fn: () => void) => { duringCompile = fn; } };
}

describe("a P4 emit that reaches the final metadata write", () => {
  it("writes its own identity fields and touches nobody else's", async () => {
    const prior = {
      qid: "stat_demo", spec: "v1", title: "Old title", tldr: "", abstract: "old",
      area: "Stat", authorship: "Jiyuan Tan", created: "2026-07-21",
      wp_number: "CSWP-2026-001", version: 1, revised: "2026-07-21",
      versions: [{ v: 1, date: "2026-07-21", paper_sha256: "stale" }],
      doi: "10.5281/zenodo.55", version_doi: "10.5281/zenodo.56",
      score: 7.2, score_rationale: "Solid.",
      license: "CC-BY-4.0", future_field: { nested: [1, 2] },
    };
    const { io, outDir } = await completedP4Fixture(prior);
    await stageP4(io);
    const meta = await readBundleMeta(outDir);

    // externally owned — P4 never names these, so they cannot be lost
    expect(meta.authorship).toBe("Jiyuan Tan");
    expect(meta.doi).toBe("10.5281/zenodo.55");
    expect(meta.version_doi).toBe("10.5281/zenodo.56");
    expect(meta.score).toBe(7.2);
    expect(meta.score_rationale).toBe("Solid.");
    // keys this code has never heard of survive too
    expect(meta.license).toBe("CC-BY-4.0");
    expect(meta.future_field).toEqual({ nested: [1, 2] });
    // P4-owned fields are written
    expect(meta.wp_number).toBe("CSWP-2026-001");
    expect(meta.title).toBe("A Demonstration Paper");
    expect(meta.created).toBe("2026-07-21");
    expect(meta.version).toBe(2); // the recorded hash was "stale", so the bytes moved
    expect(meta.revised).toBe(new Date().toISOString().slice(0, 10));
    // key order is preserved, with nothing reshuffled
    expect(Object.keys(meta)).toEqual(Object.keys(prior));
    expect(await readFile(join(outDir, "meta.json"), "utf8")).toMatch(/\n\}\n$/);
  });

  it("does not revert a DOI published by another process DURING the emit", async () => {
    // This is the exact race the audit found: P4 read meta.json before the compile, and used to
    // write that snapshot back minutes later.
    const { io, outDir, onCompile } = await completedP4Fixture({
      qid: "stat_demo", spec: "v1", title: "T", tldr: "", abstract: "a", area: "Stat",
      authorship: null, created: "2026-07-21", wp_number: "CSWP-2026-001", version: 1,
      revised: "2026-07-21", versions: [{ v: 1, date: "2026-07-21", paper_sha256: "stale" }],
      doi: null, version_doi: null, score: null, score_rationale: null,
    });
    onCompile(() => {
      writeFileSync(join(outDir, "meta.json"), `${JSON.stringify({
        ...JSON.parse(readFileSync(join(outDir, "meta.json"), "utf8")),
        doi: "10.5281/zenodo.9001", version_doi: "10.5281/zenodo.9002", score: 8.4,
      }, null, 2)}\n`);
    });
    await stageP4(io);
    const meta = await readBundleMeta(outDir);
    expect(meta.doi).toBe("10.5281/zenodo.9001");
    expect(meta.version_doi).toBe("10.5281/zenodo.9002");
    expect(meta.score).toBe(8.4);
    expect(meta.wp_number).toBe("CSWP-2026-001");
    // ...and it says the PDF it just built does not carry that DOI, because the stamp predates it
    expect(io.state.notes.some((n) => n.includes("does not carry it"))).toBe(true);
  });

  it("keeps a locked writer's update that overlaps P4's own critical section", async () => {
    // The r1 late-DOI test wrote BEFORE P4 reached its write, and the r2 attempt evaluated its
    // waiter before `onCompile` had installed the real contender, so it awaited an
    // already-resolved placeholder. Here the contender is started during the compile and awaited
    // only AFTER stageP4 returns, so it is genuinely in flight across P4's critical section.
    const { io, outDir, onCompile } = await completedP4Fixture({
      qid: "stat_demo", spec: "v1", title: "T", tldr: "", abstract: "a", area: "Stat",
      authorship: null, created: "2026-07-21", wp_number: "CSWP-2026-001", version: 1,
      revised: "2026-07-21", versions: [{ v: 1, date: "2026-07-21", paper_sha256: "stale" }],
      doi: null, version_doi: null, score: null, score_rationale: null,
    });
    const order: string[] = [];
    let contender: Promise<unknown> | null = null;
    onCompile(() => {
      order.push("contender-started");
      contender = updateBundleMeta(outDir, (m) => {
        // What this mutator SEES proves serialisation: it is a complete document, either
        // before or after P4's own write, never a half-applied one.
        order.push(`contender-critical-section(version=${String(m.version)})`);
        m.doi = "10.5281/zenodo.777";
        m.version_doi = "10.5281/zenodo.778";
      });
    });
    await stageP4(io);
    expect(contender).not.toBeNull(); // the hook really ran, so the waiter below is the real one
    await contender;

    expect(order.filter((e) => e.startsWith("contender-critical-section"))).toHaveLength(1);
    // it observed a coherent version — 1 (before P4's write) or 2 (after), never undefined
    expect(order.join("|")).toMatch(/contender-critical-section\(version=[12]\)/);
    const meta = await readBundleMeta(outDir);
    // neither side lost its update
    expect(meta.doi).toBe("10.5281/zenodo.777");
    expect(meta.version_doi).toBe("10.5281/zenodo.778");
    expect(meta.version).toBe(2);
    expect(meta.wp_number).toBe("CSWP-2026-001");
    expect(meta.title).toBe("A Demonstration Paper");
  });

  it("gives a first-ever emit the canonical key order and a v1 dated today", async () => {
    const { io, outDir } = await completedP4Fixture();
    await stageP4(io);
    const meta = await readBundleMeta(outDir);
    expect(Object.keys(meta)).toEqual([
      "qid", "spec", "title", "tldr", "abstract", "area", "authorship", "created",
      "wp_number", "version", "revised", "versions", "doi", "version_doi", "score", "score_rationale",
    ]);
    expect(meta.wp_number).toBe(`CSWP-${new Date().getUTCFullYear()}-001`);
    expect(meta.version).toBe(1);
    expect(meta.created).toBe(new Date().toISOString().slice(0, 10));
    expect(meta.doi).toBeNull();
    expect(meta.authorship).toBeNull();
    expect((meta.versions as Array<{ paper_sha256: string }>)[0]!.paper_sha256)
      .toBe(await fileSha256(join(outDir, "paper.tex")));
  });

  it("refuses to emit when the recorded created date is present but not a real date", async () => {
    const { io } = await completedP4Fixture({ qid: "stat_demo", created: "2026-02-31" });
    await expect(stageP4(io)).rejects.toThrow(/created="?2026-02-31"?.*real calendar date/s);
  });

  it("refuses to emit when meta.json claims a number the registry gave to another bundle", async () => {
    const { io, repoRoot } = await completedP4Fixture({
      qid: "stat_demo", created: "2026-07-21", wp_number: "CSWP-2026-004",
    });
    await writeFile(
      join(repoRoot, "doc", "presentation", "_wp_registry.json"),
      '{\n  "some_other_bundle": "CSWP-2026-004"\n}\n',
    );
    await expect(stageP4(io)).rejects.toThrow("already assigned that number to some_other_bundle");
  });
});
