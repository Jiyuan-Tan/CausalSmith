// Regression tests for the FOURTH (whole-stack) audit.
//
// The mutation testing in that audit is the useful part: it showed that most guards
// really do fail the suite when removed, and named the ones that do NOT — a guard no
// test can kill is a guard that can be deleted by a future refactor without anyone
// noticing. Section 2 below exists purely to make those killable.
//
// The MAJOR is a different shape from earlier rounds. Nothing here is a wrong belief
// about the world; it is a recovery path that made things worse than the failure it was
// recovering from. A revision draft deleted by a request whose response was lost left
// the bundle in a state where every subsequent command refused, meta.json kept a dead
// version DOI, and the error message's advice — delete the sidecar entry — would have
// destroyed the only record that v1 existed and let the next reserve mint a second
// concept DOI for a published paper.

import { describe, it, expect, beforeEach } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { SANDBOX, ZenodoClient } from "../src/zenodo/client.js";
import {
  abandon, newVersion, publish, reconcile, reserve, status, type DepositContext,
} from "../src/zenodo/deposit.js";
import {
  bundleMarker, readSidecar, sidecarPath, CommandLockCompromisedError, type CommandLockHandle,
} from "../src/zenodo/bundle.js";
import { withBundleEmitLock } from "../src/presentation/emit_lock.js";
import { findDoi, stampShapePresent } from "../src/zenodo/pdf_text.js";
import { texToPlainText, texToHtml } from "../src/zenodo/metadata.js";
import { minimalPdf } from "./zenodo_fixtures.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";
const META = {
  qid: "stat_demo", spec: "spec", title: "A demo paper",
  abstract: "An abstract.", area: "Stat",
  created: "2026-07-21", version: 1, revised: "2026-07-21", score: 8,
};

let dir: string;
let calls: { method: string; url: string; body?: string }[];
let logs: string[];
let warns: string[];

beforeEach(async () => {
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-r4-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = []; logs = []; warns = [];
});

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));
const pdf = (text: string) => writeFile(path.join(dir, "paper.pdf"), minimalPdf(text));

function fakeZenodo(opts: {
  before?: (method: string, url: string) => Promise<Response | void>;
} = {}) {
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = 100;
  let creations = 0;
  let conceptrecid = 99;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;

  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url, body });
    if (opts.before) { const pre = await opts.before(method, url); if (pre) return pre; }
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
        links: { bucket: bucketOf(id) }, files: [],
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
    const nv = /\/deposit\/depositions\/(\d+)\/actions\/newversion$/.exec(u.pathname);
    if (method === "POST" && nv) {
      const parentId = Number(nv[1]);
      const parent = drafts.get(parentId)!;
      const id = nextId++;
      drafts.set(id, {
        id, conceptrecid: parent.conceptrecid, state: "unsubmitted", submitted: false,
        metadata: { ...(parent.metadata as object) }, links: { bucket: bucketOf(id) },
      });
      parent.links = { ...(parent.links as object), latest_draft: `https://sandbox.zenodo.org/api/deposit/depositions/${id}` };
      return json(201, { id: parentId, links: parent.links });
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
  over: Partial<DepositContext> & { dryRun?: boolean } = {},
): DepositContext {
  const { dryRun, ...rest } = over;
  return {
    bundleDir: dir,
    client: new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl,
      sleep: async () => {}, maxRetries: 1, dryRun,
    }),
    writeMeta: false, allowUnstamped: false,
    siteBaseUrl: "https://causalsmith.org",
    titlePrefix: "[TEST] ",
    log: (l) => logs.push(l), warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...rest,
  };
}

/** Publish v1, then open a revision draft, with the DOIs written into meta.json. */
async function publishThenRevise(impl: (u: string, i?: RequestInit) => Promise<Response>) {
  await reserve(ctxFor(impl, { writeMeta: true }));
  await pdf("doi:10.5072/zenodo.99");
  await publish(ctxFor(impl, { writeMeta: true }));
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
    ...META, version: 2, doi: "10.5072/zenodo.99", version_doi: "10.5072/zenodo.100",
  }, null, 2)}\n`);
  await newVersion(ctxFor(impl, { writeMeta: true }));
}

// ===========================================================================
// MAJOR — a vanished REVISION draft must not brick the bundle
// ===========================================================================

describe("MAJOR: a revision draft that vanished remotely is recoverable", () => {
  it("reconcile clears it instead of refusing, because v1 is still published", async () => {
    const { impl, drafts } = fakeZenodo();
    await publishThenRevise(impl);
    const draftId = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    drafts.delete(draftId); // the DELETE landed; the response never arrived

    await reconcile(ctxFor(impl, { writeMeta: true }));
    const s = await readSidecar(dir);
    expect(s.sandbox?.draft).toBeNull();
    expect(s.sandbox?.publishing).toBeNull();
    expect(s.sandbox?.published?.deposition_id).toBe(100);
    expect(s.sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("restores the published version DOI when meta.json held the dead draft DOI", async () => {
    const { impl, drafts } = fakeZenodo();
    await publishThenRevise(impl);
    const draftDoi = (await readSidecar(dir)).sandbox!.draft!.version_doi;
    expect((await meta()).version_doi).toBe(draftDoi);
    drafts.delete((await readSidecar(dir)).sandbox!.draft!.deposition_id);

    await reconcile(ctxFor(impl, { writeMeta: false }));
    expect((await meta()).version_doi).toBe("10.5072/zenodo.100");
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });

  it("refuses, naming the flag, when --no-write-meta forbids the repair", async () => {
    const { impl, drafts } = fakeZenodo();
    await publishThenRevise(impl);
    drafts.delete((await readSidecar(dir)).sandbox!.draft!.deposition_id);
    await expect(reconcile(ctxFor(impl, { metaWritesForbidden: true })))
      .rejects.toThrow(/--no-write-meta/);
  });

  it("leaves the bundle usable: a later command succeeds", async () => {
    const { impl, drafts } = fakeZenodo();
    await publishThenRevise(impl);
    drafts.delete((await readSidecar(dir)).sandbox!.draft!.deposition_id);
    await expect(status(ctxFor(impl), { repair: true })).resolves.toBeTruthy();
    // and new-version can open a fresh revision
    await expect(newVersion(ctxFor(impl))).resolves.toBeTruthy();
  });

  it("abandon survives its own DELETE being applied twice", async () => {
    // The first DELETE landed and its response was LOST, so the idempotent retry sees
    // 404. The GET a moment earlier already proved the draft existed and was ours.
    let dropped = false;
    const { impl: base, drafts } = fakeZenodo();
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      if ((init?.method ?? "GET") === "DELETE" && !dropped) {
        dropped = true;
        await base(url, init);              // it really is applied server-side
        throw new Error("ECONNRESET");      // …and the response never arrives
      }
      return base(url, init);
    };
    await publishThenRevise(impl);
    const draftId = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    expect(drafts.has(draftId)).toBe(true);

    await abandon(ctxFor(impl, { writeMeta: true }));
    // Run it again: there is nothing left to abandon, and the refusal must explain that
    // the remaining record is published rather than leaving the bundle looking broken.
    await expect(abandon(ctxFor(impl, { writeMeta: true }))).rejects.toThrow(/PUBLISHED/);
    const s = await readSidecar(dir);
    expect(s.sandbox?.published?.deposition_id).toBe(100);
    expect((await meta()).version_doi).toBe("10.5072/zenodo.100");
  });

  it("a DELETE that 404s is treated as success, not as a failure", async () => {
    const { impl, drafts } = fakeZenodo();
    await publishThenRevise(impl);
    const draftId = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    // Vanish it between the identity GET and the DELETE.
    const impl2 = async (url: string, init?: RequestInit): Promise<Response> => {
      const res = await impl(url, init);
      if ((init?.method ?? "GET") === "GET" && url.endsWith(`/${draftId}`)) drafts.delete(draftId);
      return res;
    };
    await expect(abandon(ctxFor(impl2, { writeMeta: true }))).resolves.toEqual({ deleted: true });
    expect((await readSidecar(dir)).sandbox?.draft).toBeNull();
    expect((await meta()).version_doi).toBe("10.5072/zenodo.100");
  });
});

describe("MAJOR: the refusal message never advises destroying a published record", () => {
  it("does not say 'delete the entry' when a version is published", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    drafts.clear(); // even the published record is unreachable
    const msg = await reconcile(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).not.toMatch(/delete the "?sandbox"? entry|delete the entry/i);
  });

  it("warns about the consequence even in the first-reservation case", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    drafts.clear();
    const msg = await reserve(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/second|different|new concept DOI/i);
    expect(msg).toMatch(/recompil|stamped/i);
  });
});

// ===========================================================================
// Tests that must be able to FAIL — the mutation-testing gaps
// ===========================================================================

describe("the compromised-lock abort is observable", () => {
  it("stops before the next request once the lock is lost", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");

    // A handle that is fine until the upload, then reports the lock as lost.
    let uploads = 0;
    const handle: CommandLockHandle = {
      assertHeld: () => {
        if (uploads > 0) throw new CommandLockCompromisedError(dir, "forced in test");
      },
    };
    const counting = async (url: string, init?: RequestInit): Promise<Response> => {
      if ((init?.method ?? "GET") === "PUT" && url.includes("/api/files/")) uploads += 1;
      return impl(url, init);
    };

    calls.length = 0;
    await expect(publish(ctxFor(counting, {
      lockRunner: (_d, action) => action(handle),
    }))).rejects.toBeInstanceOf(CommandLockCompromisedError);

    // The upload may have gone out; nothing after it may have.
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
    expect(calls.filter((c) => c.method === "PUT" && c.url.includes("/deposit/depositions/"))).toHaveLength(0);
  });

  it("stops a reserve before the creation POST", async () => {
    const { impl } = fakeZenodo();
    const handle: CommandLockHandle = {
      assertHeld: () => { throw new CommandLockCompromisedError(dir, "forced in test"); },
    };
    calls.length = 0;
    await expect(reserve(ctxFor(impl, { lockRunner: (_d, a) => a(handle) })))
      .rejects.toBeInstanceOf(CommandLockCompromisedError);
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
  });
});

describe("every mutating command refuses while an emit holds the bundle", () => {
  async function expectBusy(run: () => Promise<unknown>): Promise<void> {
    await withBundleEmitLock(dir, async () => {
      await expect(run()).rejects.toThrow(/emit of this bundle is in progress/i);
    }, { wait: false });
  }

  it("reserve", async () => {
    const { impl } = fakeZenodo();
    await expectBusy(() => reserve(ctxFor(impl)));
  }, 60_000);

  it("publish", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await expectBusy(() => publish(ctxFor(impl)));
  }, 60_000);

  it("new-version", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await expectBusy(() => newVersion(ctxFor(impl)));
  }, 60_000);

  it("abandon", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expectBusy(() => abandon(ctxFor(impl)));
  }, 60_000);

  it("status --repair", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expectBusy(() => status(ctxFor(impl), { repair: true }));
  }, 60_000);

  it("but status WITHOUT --repair is read-only and does not need the lock", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await withBundleEmitLock(dir, async () => {
      await expect(status(ctxFor(impl))).resolves.toBeTruthy();
    }, { wait: false });
  }, 60_000);
});

describe("a stale publishing journal does not fabricate a publication", () => {
  it("does not mark a still-unpublished draft as published", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    const s = await readSidecar(dir);
    // A journal left behind by an attempt that never actually published.
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      ...s,
      sandbox: {
        ...s.sandbox,
        publishing: {
          version: 1, paper_sha256: "b".repeat(64), meta_sha256: "c".repeat(64),
          started_at: "2026-09-21T11:00:00.000Z",
        },
      },
    }, null, 2)}\n`);

    await reconcile(ctxFor(impl, { writeMeta: true }));
    const after = await readSidecar(dir);
    expect(after.sandbox?.published).toBeNull();
    expect(after.sandbox?.draft).toBeTruthy();
    expect((await meta()).doi ?? null).toBeNull();
  });
});

// ===========================================================================
// Smaller items
// ===========================================================================

describe("new-version checks the live published parent's identity before posting", () => {
  it("refuses when the published record is not this bundle's", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    const pubId = (await readSidecar(dir)).sandbox!.published!.deposition_id;
    const d = drafts.get(pubId)!;
    drafts.set(pubId, { ...d, metadata: { ...(d.metadata as object), notes: "causalsmith-bundle-id:0000000000000000000000000000dead" } });
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);

    calls.length = 0;
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/marker|belong/i);
    expect(calls.some((c) => c.url.includes("/actions/newversion"))).toBe(false);
  });
});

describe("first-reservation abandon and reserve are atomic about the concept DOI", () => {
  it("leaves no lingering concept_doi after abandoning a first reservation", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { writeMeta: true }));
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await abandon(ctxFor(impl, { writeMeta: true }));
    const s = await readSidecar(dir);
    expect(s.sandbox).toBeUndefined();
    expect((await meta()).doi).toBeNull();
  });

  it("honours --no-write-meta on a first-reservation abandon too", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { writeMeta: true }));
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await expect(abandon(ctxFor(impl, { metaWritesForbidden: true })))
      .rejects.toThrow(/--no-write-meta/);
  });

  it("reserve refuses before creating when a concept DOI lingers with no draft", async () => {
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
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/concept DOI/i);
    expect(calls.filter((c) => c.method === "POST")).toHaveLength(0);
  });
});

describe("a sandbox run never overwrites a production DOI in meta.json", () => {
  it("refuses rather than replacing a 10.5281 doi with a sandbox one", async () => {
    const { impl } = fakeZenodo();
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, doi: "10.5281/zenodo.777", version_doi: "10.5281/zenodo.778",
    }, null, 2)}\n`);
    await expect(reserve(ctxFor(impl, { writeMeta: true })))
      .rejects.toThrow(/production|10\.5281|non-sandbox/i);
    expect((await meta()).doi).toBe("10.5281/zenodo.777");
  });
});

describe("request timeouts", () => {
  it("treats a POST timeout as ambiguous and a GET timeout as retryable", async () => {
    const hang = async (_u: string, init?: RequestInit): Promise<Response> => {
      await new Promise((_r, reject) => {
        init?.signal?.addEventListener("abort", () => reject(new Error("The operation was aborted")));
      });
      throw new Error("unreachable");
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: hang,
      sleep: async () => {}, maxRetries: 1, requestTimeoutMs: 20,
    });
    await expect(c.createDraft()).rejects.toThrow(/UNKNOWN outcome/);
    await expect(c.getDeposition(1)).rejects.toThrow(/timed out|aborted|before a response/i);
  }, 30_000);
});

describe("flag combinations", () => {
  it("rejects --write-meta together with --no-write-meta", async () => {
    const { parseStrict } = await import("../bin/zenodo_deposit.js");
    expect(() => parseStrict("reserve", ["/b", "--write-meta", "--no-write-meta"]))
      .toThrow(/--write-meta.*--no-write-meta|contradict|both/i);
  });
});

describe("TeX constructs that could silently change meaning", () => {
  it("renders \\| as the double vertical line", () => {
    expect(texToPlainText("\\(\\|x\\|\\)")).toBe("‖x‖");
  });

  it("parenthesises a multi-character fraction next to an adjacent atom", () => {
    expect(texToPlainText("\\(\\frac{1}{2}n\\)")).toBe("(1/2)n");
    expect(texToPlainText("\\(a/\\frac{b}{c}\\)")).toBe("a/(b/c)");
    expect(texToPlainText("\\(\\frac{a}{b}^2\\)")).toBe("(a/b)²");
  });

  it("parenthesises a multi-character root next to an adjacent atom", () => {
    expect(texToPlainText("\\(\\sqrt{2}n\\)")).toBe("(√2)n");
  });

  it("preserves an accent over a multi-atom argument", () => {
    expect(texToHtml("\\(\\overline{A\\cup B}\\)")).toContain("<code>");
    expect(texToHtml("\\(\\hat{x y}\\)")).toContain("<code>");
    // a single atom is still fine
    expect(texToPlainText("\\(\\hat{x}\\)")).toBe("x̂");
  });

  it("handles or preserves \\left. and \\right|", () => {
    const html = texToHtml("\\(\\left.\\frac{a}{b}\\right|_0\\)");
    expect(html).not.toContain("left");
    expect(html).not.toContain("right");
  });

  it("does not double-escape inside \\mathrm", () => {
    expect(texToHtml("\\(\\mathrm{A\\&B}\\)")).toContain("A&amp;B");
    expect(texToHtml("\\(\\mathrm{A\\&B}\\)")).not.toContain("&amp;amp;");
  });
});

describe("the real extraction shapes of the pipeline stamp", () => {
  // Measured by the pipeline agent on a real stamped 100-page PDF. Ghostscript's
  // txtwrite does not keep the rotated margin stamp together: it emits text in y-bands,
  // so the stamp arrives as three fragments with body text butted against the DOI.
  const GS_FRAGMENTS = [
    "           [Stat]               radius σ. The selector attaining",
    "           doi:10.5281/zenodo.17158230High-dimensional discrete adjustment creates",
    "           CSWP-2026-008v3",
  ].join("\n");
  // PyMuPDF returns it as one clean line.
  const PYMUPDF_LINE = "CSWP-2026-008v3 · doi:10.5281/zenodo.17158230 · [Stat] 27 Aug 2026";
  const DOI = "10.5281/zenodo.17158230";

  it("matches the gs-fragmented shape, where body text abuts the DOI", () => {
    expect(findDoi(GS_FRAGMENTS, DOI)).toBe(true);
  });

  it("matches the PyMuPDF single-line shape", () => {
    expect(findDoi(PYMUPDF_LINE, DOI)).toBe(true);
  });

  it("refuses when the abutting body text begins with a digit", () => {
    // The safe direction, and the reason PyMuPDF is preferred: under gs this is
    // indistinguishable from a longer DOI.
    const digitAbut = GS_FRAGMENTS.replace("High-dimensional", "2026 High-dimensional");
    expect(findDoi(digitAbut, DOI)).toBe(false);
  });

  it("recognises the stamp SHAPE only in the clean extraction", () => {
    expect(stampShapePresent(PYMUPDF_LINE, DOI)).toBe(true);
    expect(stampShapePresent(GS_FRAGMENTS, DOI)).toBe(false);
  });

  it("still rejects a longer DOI in either shape", () => {
    expect(findDoi(PYMUPDF_LINE.replace(DOI, `${DOI}9`), DOI)).toBe(false);
    expect(findDoi(GS_FRAGMENTS.replace(DOI, `${DOI}9`), DOI)).toBe(false);
  });

  it("names the extractor, and suggests PyMuPDF, when a stamped PDF is refused", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("a paper with no stamp at all");
    const msg = await publish(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/checked via /);
    expect(msg).toMatch(/PyMuPDF/);
  });
});

describe("the stamp matcher requires the record id's digits to be contiguous", () => {
  const D = "10.5072/zenodo.99";
  it("rejects a space inside the numeric suffix", () => {
    expect(findDoi("doi:10.5072/zenodo.9 9", D)).toBe(false);
  });
  it("still tolerates gaps in the prefix", () => {
    expect(findDoi("1 0 . 5 0 7 2 / z e n o d o . 99", D)).toBe(true);
  });
  it("still matches the contiguous form", () => {
    expect(findDoi("doi:10.5072/zenodo.99 · [Stat]", D)).toBe(true);
  });
});
