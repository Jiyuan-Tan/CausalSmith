// Tests that pin what earlier rounds only claimed.
//
// The delta audit found several guards that no test could kill: the suite stayed green
// when they were removed. A guard a mutant survives is a guard a refactor deletes
// unnoticed, so each block below is written to go RED for one specific deletion, and
// the deletion it targets is named.
//
// It also closes the one piece of advice the tool gave that could not be followed:
// `abandon --discard-stamped-doi` was the documented way out of a lost first
// reservation, and it ran reconcile first, which refused for the very reason the
// operator was trying to resolve.

import { describe, it, expect, beforeEach } from "vitest";
import { execFile } from "node:child_process";
import { mkdir, mkdtemp, readFile, rm, symlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import { SANDBOX, ZenodoClient } from "../src/zenodo/client.js";
import { abandon, publish, reconcile, reserve, type DepositContext } from "../src/zenodo/deposit.js";
import {
  bundleMarker, readSidecar, sidecarPath, withCommandLock,
  CommandLockCompromisedError, COMMAND_LOCK_FILE, type LockAcquirer,
} from "../src/zenodo/bundle.js";
import { minimalPdf } from "./zenodo_fixtures.js";

const execFileAsync = promisify(execFile);
const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";
const META = {
  qid: "stat_demo", spec: "spec", title: "A demo paper", abstract: "An abstract.",
  area: "Stat", created: "2026-07-21", version: 1, revised: "2026-07-21", score: 8,
};

let dir: string;
let calls: { method: string; url: string }[];
let logs: string[];
let warns: string[];

beforeEach(async () => {
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-r5-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = []; logs = []; warns = [];
});

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));

function fakeZenodo() {
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = 100;
  let creations = 0;
  let conceptrecid = 99;
  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url });
    const json = (s: number, v: unknown) => new Response(JSON.stringify(v), { status: s });
    const u = new URL(url);
    if (method === "GET" && u.pathname.endsWith("/deposit/depositions") && u.search) {
      const q = decodeURIComponent(u.searchParams.get("q") ?? "").replace(/^"|"$/g, "");
      return json(200, [...drafts.values()].filter(
        (d) => d.submitted === false &&
          String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "")
            .split("\n").some((l) => l.trim() === q)));
    }
    if (method === "POST" && u.pathname.endsWith("/deposit/depositions")) {
      const id = nextId++;
      creations += 1;
      if (creations > 1) conceptrecid = 99 + 1000 * (creations - 1);
      const dep = {
        id, conceptrecid, state: "unsubmitted", submitted: false,
        metadata: { ...(JSON.parse(body ?? "{}").metadata ?? {}), prereserve_doi: { doi: `10.5281/zenodo.${id}`, recid: id } },
        links: { bucket: `https://sandbox.zenodo.org/api/files/b-${id}` }, files: [],
      };
      drafts.set(id, dep);
      return json(201, dep);
    }
    const pub = /\/deposit\/depositions\/(\d+)\/actions\/publish$/.exec(u.pathname);
    if (method === "POST" && pub) {
      const id = Number(pub[1]);
      const d = drafts.get(id)!;
      drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: `10.5072/zenodo.${d.conceptrecid}`, doi: `10.5072/zenodo.${id}` });
      return json(202, drafts.get(id));
    }
    const dep = /\/deposit\/depositions\/(\d+)$/.exec(u.pathname);
    if (dep) {
      const id = Number(dep[1]);
      if (method === "GET") {
        const d = drafts.get(id);
        return d ? json(200, d) : json(404, { message: "The persistent identifier does not exist." });
      }
      if (method === "PUT") {
        const d = drafts.get(id) ?? {};
        drafts.set(id, { ...d, metadata: { ...(d.metadata as object), ...JSON.parse(body ?? "{}").metadata } });
        return json(200, drafts.get(id));
      }
      if (method === "DELETE") {
        // A REPEATED delete is 404, which is what makes `allow404` load bearing.
        if (!drafts.has(id)) return json(404, { message: "The persistent identifier does not exist." });
        drafts.delete(id);
        return new Response(null, { status: 204 });
      }
    }
    if (method === "PUT" && u.pathname.includes("/api/files/")) {
      return json(201, { key: u.pathname.split("/").pop(), size: 10, checksum: "md5:fake" });
    }
    return json(500, { message: `unrouted ${method} ${u.pathname}` });
  };
  return { impl, drafts };
}

function ctxFor(
  impl: (url: string, init?: RequestInit) => Promise<Response>,
  over: Partial<DepositContext> = {},
): DepositContext {
  return {
    bundleDir: dir,
    client: new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl,
      sleep: async () => {}, maxRetries: 1,
    }),
    writeMeta: false, allowUnstamped: false,
    siteBaseUrl: "https://causalsmith.org",
    titlePrefix: "[TEST] ",
    log: (l) => logs.push(l), warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...over,
  };
}

/** The state a lost first reservation leaves: a recorded draft that is gone remotely. */
async function lostFirstReservation(impl: (u: string, i?: RequestInit) => Promise<Response>,
                                    drafts: Map<number, unknown>) {
  await reserve(ctxFor(impl, { writeMeta: true }));
  const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
  drafts.delete(id);
  return id;
}

// ===========================================================================
// A — the advised remedy has to actually work
// ===========================================================================

describe("abandon --discard-stamped-doi is a remedy that can be applied", () => {
  it("clears a lost first reservation whose draft is gone remotely", async () => {
    const { impl, drafts } = fakeZenodo();
    await lostFirstReservation(impl, drafts);
    // This is precisely what reconcile's refusal tells the operator to run.
    await abandon(ctxFor(impl, { writeMeta: true }), { discardStampedDoi: true });
    expect((await readSidecar(dir)).sandbox).toBeUndefined();
    expect((await meta()).doi).toBeNull();
    expect((await meta()).version_doi).toBeNull();
  });

  it("still REFUSES that state without the flag", async () => {
    const { impl, drafts } = fakeZenodo();
    await lostFirstReservation(impl, drafts);
    await expect(abandon(ctxFor(impl, { writeMeta: true })))
      .rejects.toThrow(/--discard-stamped-doi|no longer exists/i);
    expect((await readSidecar(dir)).sandbox).toBeTruthy();
  });

  it("clears the lingering-concept-DOI state, which reserve points at", async () => {
    const { impl } = fakeZenodo();
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      schema: 2,
      sandbox: {
        environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: 99,
        concept_doi: "10.5072/zenodo.99", marker: bundleMarker(dir, "sandbox"),
        published: null, draft: null, publishing: null, pending_reserve: null,
        updated_at: "2026-09-21T11:00:00.000Z",
      },
    }, null, 2)}\n`);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, doi: "10.5072/zenodo.99", version_doi: "10.5072/zenodo.100",
    }, null, 2)}\n`);

    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    await abandon(ctxFor(impl), { discardStampedDoi: true });
    expect((await readSidecar(dir)).sandbox).toBeUndefined();
    expect((await meta()).doi).toBeNull();
    // …and reserve is unblocked.
    await expect(reserve(ctxFor(impl))).resolves.toBeTruthy();
  });

  it("refuses up front when --no-write-meta forbids clearing meta.json", async () => {
    const { impl, drafts } = fakeZenodo();
    await lostFirstReservation(impl, drafts);
    await expect(abandon(ctxFor(impl, { writeMeta: true, metaWritesForbidden: true }),
      { discardStampedDoi: true })).rejects.toThrow(/--no-write-meta/);
    // Nothing half-cleared: the record survives the refusal.
    expect((await readSidecar(dir)).sandbox).toBeTruthy();
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });
});

// ===========================================================================
// B2 — `allow404` on DELETE is load bearing
// ===========================================================================

describe("a repeated DELETE returns 404 and that is not an error", () => {
  it("deleteDraft reports alreadyGone rather than throwing", async () => {
    // Removing `allow404: true` from deleteDraft makes this throw ZenodoError 404.
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {},
    });
    expect(await c.deleteDraft(id)).toEqual({ alreadyGone: false });
    expect(drafts.has(id)).toBe(false);
    expect(await c.deleteDraft(id)).toEqual({ alreadyGone: true });
  });
});

// ===========================================================================
// B3 — the REAL links.latest_draft shapes, as probed on the sandbox
// ===========================================================================

describe("links.latest_draft, in the shapes Zenodo actually returns", () => {
  /** Publish v1 and then answer the latest_draft link however `linkTarget` says. */
  function withLatestDraft(linkTarget: (pubId: number) => {
    url: string; reply: (id: number) => Response;
  }) {
    const { impl: base, drafts } = fakeZenodo();
    let spec: { url: string; reply: (id: number) => Response } | null = null;
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      if (spec && url === spec.url && (init?.method ?? "GET") === "GET") {
        calls.push({ method: "GET", url });
        return spec.reply(0);
      }
      const res = await base(url, init);
      // Attach the link once the record is published.
      if ((init?.method ?? "GET") === "POST" && url.includes("/actions/publish")) {
        const body = await res.clone().json() as { id: number };
        spec = linkTarget(body.id);
        const d = drafts.get(body.id)!;
        d.links = { ...(d.links as object), latest_draft: spec.url };
      }
      return res;
    };
    return { impl, drafts };
  }

  async function publishV1(impl: (u: string, i?: RequestInit) => Promise<Response>) {
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "paper.pdf"), minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl));
  }

  it("does NOT adopt a self-pointing link (the probed shape with no open draft)", async () => {
    // Probed on sandbox: a published record with no draft still returns
    // links.latest_draft, pointing at ITSELF, 200, submitted:true.
    // A mutant that adopts any non-null latest_draft fails here.
    const { impl } = withLatestDraft((pubId) => ({
      url: `https://sandbox.zenodo.org/api/deposit/depositions/${pubId}`,
      reply: () => new Response(JSON.stringify({
        id: pubId, conceptrecid: 99, state: "done", submitted: true,
        metadata: { notes: bundleMarker(dir, "sandbox") },
        links: { latest_draft: `https://sandbox.zenodo.org/api/deposit/depositions/${pubId}` },
      }), { status: 200 }),
    }));
    await publishV1(impl);
    await reconcile(ctxFor(impl));
    const s = await readSidecar(dir);
    expect(s.sandbox?.draft).toBeNull();
    expect(s.sandbox?.published?.deposition_id).toBe(100);
  });

  it("tolerates a stale link that now 404s", async () => {
    const { impl } = withLatestDraft(() => ({
      url: "https://sandbox.zenodo.org/api/deposit/depositions/98765",
      reply: () => new Response(JSON.stringify({ message: "The persistent identifier does not exist." }), { status: 404 }),
    }));
    await publishV1(impl);
    await expect(reconcile(ctxFor(impl))).resolves.toBeTruthy();
    expect((await readSidecar(dir)).sandbox?.draft).toBeNull();
  });

  it("STOPS on a 403 from the link rather than treating it as 'no draft'", async () => {
    // A mutant that swallows every error from getByUrlOrNull fails here.
    const { impl } = withLatestDraft(() => ({
      url: "https://sandbox.zenodo.org/api/deposit/depositions/98765",
      reply: () => new Response(JSON.stringify({ message: "forbidden" }), { status: 403 }),
    }));
    await publishV1(impl);
    await expect(reconcile(ctxFor(impl))).rejects.toThrow(/403|forbidden/i);
  });

  it("STOPS on a 500 from the link", async () => {
    const { impl } = withLatestDraft(() => ({
      url: "https://sandbox.zenodo.org/api/deposit/depositions/98765",
      reply: () => new Response(JSON.stringify({ message: "boom" }), { status: 500 }),
    }));
    await publishV1(impl);
    await expect(reconcile(ctxFor(impl))).rejects.toThrow();
  });

  it("DOES adopt a genuine open revision draft", async () => {
    const { impl } = withLatestDraft(() => ({
      url: "https://sandbox.zenodo.org/api/deposit/depositions/777",
      reply: () => new Response(JSON.stringify({
        id: 777, conceptrecid: 99, state: "unsubmitted", submitted: false,
        metadata: { notes: bundleMarker(dir, "sandbox") },
        links: { bucket: "https://sandbox.zenodo.org/api/files/b777" },
      }), { status: 200 }),
    }));
    await publishV1(impl);
    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(777);
  });
});

// ===========================================================================
// B4 — the compromise goes through the REAL handle
// ===========================================================================

describe("the command lock's own assertHeld is exercised", () => {
  it("throws once proper-lockfile reports the lock compromised", async () => {
    // Drives the REAL handle built in bundle.ts: making `assertHeld` a no-op there
    // fails this test.
    let fire: ((err: Error) => void) | undefined;
    const acquire: LockAcquirer = async (_target, opts) => {
      fire = (opts as { onCompromised?: (e: Error) => void } | undefined)?.onCompromised;
      return async () => {};
    };
    let threw: unknown;
    await withCommandLock(dir, async (lock) => {
      lock.assertHeld(); // fine so far
      fire!(new Error("lock directory removed under us"));
      try { lock.assertHeld(); } catch (e) { threw = e; }
    }, acquire);
    expect(threw).toBeInstanceOf(CommandLockCompromisedError);
    expect((threw as Error).message).toMatch(/lock directory removed under us/);
    expect((threw as Error).message).toMatch(/re-run/i);
  });

  it("does not throw while the lock is held normally", async () => {
    const acquire: LockAcquirer = async () => async () => {};
    await expect(withCommandLock(dir, async (lock) => {
      lock.assertHeld();
      return "ok";
    }, acquire)).resolves.toBe("ok");
  });
});

describe("the emit lock's compromise is checked too", () => {
  it("stops before the publish POST when the emit lock reports it was lost", async () => {
    // Deleting the `assertBundleEmitLockHeld(...)` line from deposit.ts fails this.
    const emit = await import("../src/presentation/emit_lock.js");
    const original = emit.assertBundleEmitLockHeld;
    let armed = false;
    Object.defineProperty(emit, "assertBundleEmitLockHeld", {
      configurable: true,
      value: (bundleDir: string) => {
        if (armed) throw new emit.BundleEmitLockLostError(bundleDir, new Error("forced in test"));
        return original(bundleDir);
      },
    });
    try {
      const { impl } = fakeZenodo();
      await reserve(ctxFor(impl));
      await writeFile(path.join(dir, "paper.pdf"), minimalPdf("doi:10.5072/zenodo.99"));
      armed = true;
      calls.length = 0;
      await expect(publish(ctxFor(impl))).rejects.toThrow(/emit lock/i);
      expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
    } finally {
      Object.defineProperty(emit, "assertBundleEmitLockHeld", {
        configurable: true, value: original,
      });
    }
  }, 60_000);
});

// ===========================================================================
// B5 — the CLI really runs when invoked through a symlink
// ===========================================================================

describe("the CLI entry guard survives a symlinked invocation", () => {
  const CLI = path.resolve(fileURLToPath(import.meta.url), "../../bin/zenodo_deposit.ts");

  it("runs, rather than exiting 0 having done nothing", async () => {
    // Comparing raw paths instead of realpathSync makes this print nothing and exit 0.
    const linkDir = await mkdtemp(path.join(os.tmpdir(), "zenodo-link-"));
    const link = path.join(linkDir, "zenodo_deposit.ts");
    await symlink(CLI, link);
    const run = await execFileAsync(
      process.execPath,
      [path.resolve(fileURLToPath(import.meta.url), "../../node_modules/tsx/dist/cli.mjs"), link, "status", dir],
      { timeout: 120_000 },
    ).catch((e: { stdout?: string; stderr?: string; code?: number }) => e);
    const out = `${run.stdout ?? ""}${run.stderr ?? ""}`;
    expect(out).toMatch(/No sandbox deposit recorded|environment\s+sandbox/);
    expect(out).not.toBe("");
    await rm(linkDir, { recursive: true, force: true });
  }, 180_000);

  it("reports a bad flag through the symlink too, with a non-zero exit", async () => {
    const linkDir = await mkdtemp(path.join(os.tmpdir(), "zenodo-link-"));
    const link = path.join(linkDir, "zenodo_deposit.ts");
    await symlink(CLI, link);
    const run = await execFileAsync(
      process.execPath,
      [path.resolve(fileURLToPath(import.meta.url), "../../node_modules/tsx/dist/cli.mjs"), link, "reserve", dir, "--productoin"],
      { timeout: 120_000 },
    ).then(() => ({ code: 0, stdout: "", stderr: "" }))
      .catch((e: { stdout?: string; stderr?: string; code?: number }) => e);
    expect(run.code).not.toBe(0);
    expect(`${run.stdout ?? ""}${run.stderr ?? ""}`).toMatch(/Unknown flag '--productoin'/);
    await rm(linkDir, { recursive: true, force: true });
  }, 180_000);
});

describe("dry-run still leaves no lock artifact", () => {
  it("creates no sentinel", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, {
      client: new ZenodoClient({
        env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl,
        sleep: async () => {}, dryRun: true,
      }),
    }));
    await expect(readFile(path.join(dir, COMMAND_LOCK_FILE))).rejects.toThrow();
  });
});
