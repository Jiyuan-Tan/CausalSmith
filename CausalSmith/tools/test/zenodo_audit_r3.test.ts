// Regression tests for the THIRD audit of the Zenodo work package.
//
// Round 2's four mechanisms (one lock per command, reconcile-first, never replay a
// POST, exact identity) held — the auditor could not break any of them. What remained
// were places where those mechanisms were applied to the wrong evidence:
//
//   - "could not read the PDF" was read as "there is no PDF";
//   - "the search returned nothing" was read as "the create did nothing", although a
//     search index lags behind a write;
//   - "the sidecar is well-formed" was read as "the sidecar belongs to this bundle";
//   - "meta.version says 2" was read as "version 2 is what we published".
//
// Each is the same error: treating a weaker fact as a stronger one. The fixes narrow
// what each signal is allowed to prove.

import { describe, it, expect, beforeEach, vi } from "vitest";
import { chmod, mkdir, mkdtemp, readFile, rm, writeFile, stat } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { SANDBOX, PRODUCTION, ZenodoClient } from "../src/zenodo/client.js";
import {
  abandon, newVersion, publish, reconcile, reserve, status, type DepositContext,
} from "../src/zenodo/deposit.js";
import { bundleMarker, readSidecar, sidecarPath, COMMAND_LOCK_FILE } from "../src/zenodo/bundle.js";
import { extractPdfText, findDoi } from "../src/zenodo/pdf_text.js";
import { texToPlainText, texToHtml } from "../src/zenodo/metadata.js";
import { parseStrict, resolveEnvironment, SUBCOMMANDS } from "../bin/zenodo_deposit.js";
import { minimalPdf } from "./zenodo_fixtures.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";

const META = {
  qid: "stat_demo", spec: "spec", title: "A demo paper",
  abstract: "An abstract with \\(\\epsilon\\) in it.", area: "Stat",
  created: "2026-07-21", version: 1, revised: "2026-07-21", score: 8,
};

let dir: string;
let calls: { method: string; url: string; body?: string }[];
let logs: string[];
let warns: string[];

beforeEach(async () => {
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-r3-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = []; logs = []; warns = [];
});

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));
const pdf = (text: string) => writeFile(path.join(dir, "paper.pdf"), minimalPdf(text));
const posts = () => calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"));

function fakeZenodo(opts: {
  conceptrecid?: number;
  nextId?: number;
  /** Hide created drafts from the marker search, as a lagging index would. */
  hideFromSearch?: boolean;
  before?: (method: string, url: string) => Promise<Response | void>;
} = {}) {
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = opts.nextId ?? 100;
  const baseConcept = opts.conceptrecid ?? 99;
  let creations = 0;
  let conceptrecid = baseConcept;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;
  const marker = () => bundleMarker(dir, "sandbox");

  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url, body });
    if (opts.before) { const pre = await opts.before(method, url); if (pre) return pre; }
    const json = (status: number, value: unknown) => new Response(JSON.stringify(value), { status });
    const u = new URL(url);

    if (method === "GET" && u.pathname.endsWith("/deposit/depositions") && u.search) {
      if (opts.hideFromSearch) return json(200, []);
      const q = decodeURIComponent(u.searchParams.get("q") ?? "").replace(/^"|"$/g, "");
      return json(200, [...drafts.values()].filter(
        (d) => d.submitted === false &&
          String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "")
            .split("\n").some((l) => l.trim() === q),
      ));
    }
    if (method === "POST" && u.pathname.endsWith("/deposit/depositions")) {
      const id = nextId++;
      creations += 1;
      if (creations > 1) conceptrecid = baseConcept + 1000 * (creations - 1);
      const dep = {
        id, conceptrecid, state: "unsubmitted", submitted: false,
        metadata: { ...(JSON.parse(body ?? "{}").metadata ?? {}), prereserve_doi: { doi: `10.5281/zenodo.${id}`, recid: id } },
        links: { bucket: bucketOf(id), self: `https://sandbox.zenodo.org/api/deposit/depositions/${id}` },
        files: [],
      };
      drafts.set(id, dep);
      return json(201, dep);
    }
    const pub = /\/deposit\/depositions\/(\d+)\/actions\/publish$/.exec(u.pathname);
    if (method === "POST" && pub) {
      const id = Number(pub[1]);
      const dep = drafts.get(id)!;
      drafts.set(id, {
        ...dep, state: "done", submitted: true,
        conceptdoi: `10.5072/zenodo.${dep.conceptrecid}`, doi: `10.5072/zenodo.${id}`,
      });
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
        const next = { ...d, metadata: { ...(d.metadata as object), ...JSON.parse(body ?? "{}").metadata } };
        drafts.set(id, next);
        return json(200, next);
      }
      if (method === "DELETE") { drafts.delete(id); return new Response(null, { status: 204 }); }
    }
    if (method === "PUT" && u.pathname.includes("/api/files/")) {
      return json(201, { key: u.pathname.split("/").pop(), size: 10, checksum: "md5:fake" });
    }
    return json(500, { message: `unrouted ${method} ${u.pathname}` });
  };
  return { impl, drafts, marker };
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
    repoUrl: "https://github.com/Jiyuan-Tan/CausalSmith",
    titlePrefix: "[TEST] ",
    log: (l) => logs.push(l), warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...rest,
  };
}

// ===========================================================================
// BLOCKER 1 — only ENOENT means "there is no PDF"
// ===========================================================================

describe("BLOCKER: an unreadable PDF is not an absent PDF", () => {
  it("extractPdfText reports the errno so callers can tell the cases apart", async () => {
    const missing = await extractPdfText(path.join(dir, "nope.pdf"));
    expect(missing.text).toBeNull();
    expect((missing as { code?: string }).code).toBe("ENOENT");

    await pdf("hello");
    const ok = await extractPdfText(path.join(dir, "paper.pdf"));
    expect(ok.text).not.toBeNull();
    expect((ok as { code?: string }).code).toBeUndefined();
  });

  it("reports a non-ENOENT read failure with its own code", async () => {
    // A directory where a file is expected reads as EISDIR: a real read error that is
    // emphatically not "the file does not exist".
    await mkdir(path.join(dir, "paper.pdf"), { recursive: true });
    const res = await extractPdfText(path.join(dir, "paper.pdf"));
    expect(res.text).toBeNull();
    expect((res as { code?: string }).code).toBeDefined();
    expect((res as { code?: string }).code).not.toBe("ENOENT");
  });

  it("abandon refuses when paper.pdf exists but cannot be read", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await mkdir(path.join(dir, "paper.pdf"), { recursive: true }); // unreadable as a file
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1);
  });

  it("abandon proceeds only when the PDF is genuinely absent (ENOENT)", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await abandon(ctxFor(impl));
    expect(drafts.size).toBe(0);
  });

  it("abandon still refuses an unextractable but present PDF", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "paper.pdf"), Buffer.from("%PDF-1.4\ngarbage"));
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1);
  });
});

// ===========================================================================
// BLOCKER 2 — an empty search does not prove the create did nothing
// ===========================================================================

describe("BLOCKER: a pending reserve never silently creates a second draft", () => {
  /** Put the bundle in the state a lost create response leaves: pending, nothing recorded. */
  async function pendingOnly(marker: string): Promise<void> {
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      schema: 2,
      sandbox: {
        environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: null, concept_doi: null,
        marker, published: null, draft: null, publishing: null,
        pending_reserve: { marker, started_at: "2026-09-21T11:00:00.000Z" },
        updated_at: "2026-09-21T11:00:00.000Z",
      },
    }, null, 2)}\n`);
  }

  it("refuses, with zero POSTs, when the marker search comes back empty", async () => {
    const { impl, marker } = fakeZenodo({ hideFromSearch: true });
    await pendingOnly(marker());
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/--confirm-no-remote-draft/);
    expect(posts()).toHaveLength(0);
  });

  it("explains that the search index lags and says to check the account", async () => {
    const { impl, marker } = fakeZenodo({ hideFromSearch: true });
    await pendingOnly(marker());
    const msg = await reserve(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/may have succeeded|index/i);
    expect(msg).toMatch(/re-run/i);
  });

  it("creates exactly one draft when --confirm-no-remote-draft is given", async () => {
    const { impl, marker, drafts } = fakeZenodo({ hideFromSearch: true });
    await pendingOnly(marker());
    calls.length = 0;
    const res = await reserve(ctxFor(impl), { confirmNoRemoteDraft: true });
    expect(posts()).toHaveLength(1);
    expect(drafts.size).toBe(1);
    expect(res.record.pending_reserve).toBeNull();
  });

  it("adopts the orphan without the flag once the search can see it", async () => {
    const { impl, marker, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    await pendingOnly(marker());
    calls.length = 0;
    await reserve(ctxFor(impl));
    expect(posts()).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(id);
    expect(drafts.size).toBe(1);
  });

  it("a FIRST reserve with no journal still creates normally", async () => {
    const { impl } = fakeZenodo({ hideFromSearch: true });
    await reserve(ctxFor(impl));
    expect(posts()).toHaveLength(1);
  });
});

// ===========================================================================
// MAJOR — the sidecar and the live draft must belong to THIS bundle
// ===========================================================================

describe("MAJOR: identity is bound to the bundle, not merely well-formed", () => {
  it("refuses a sidecar whose marker belongs to another bundle", async () => {
    const other = createHash("sha256").update("some_other_bundle\nsandbox").digest("hex").slice(0, 32);
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      schema: 2,
      sandbox: {
        environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: 99,
        concept_doi: "10.5072/zenodo.99", marker: `causalsmith-bundle-id:${other}`,
        published: null, draft: null, publishing: null, pending_reserve: null,
        updated_at: "2026-09-21T11:00:00.000Z",
      },
    }, null, 2)}\n`);
    await expect(readSidecar(dir)).rejects.toThrow(/marker/i);
  });

  it("refuses to publish into a draft whose notes are not this bundle's", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    // The remote draft is re-tagged for a different paper.
    drafts.set(id, { ...d, metadata: { ...(d.metadata as object), notes: "causalsmith-bundle-id:0000000000000000000000000000dead" } });
    await pdf("doi:10.5072/zenodo.99");
    await expect(publish(ctxFor(impl))).rejects.toThrow(/marker|belong/i);
    expect(calls.some((c) => c.method === "PUT" && c.url.includes("/api/files/"))).toBe(false);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("refuses to delete a draft whose notes are not this bundle's", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, metadata: { ...(d.metadata as object), notes: "causalsmith-bundle-id:0000000000000000000000000000dead" } });
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/marker|belong/i);
    expect(drafts.size).toBe(1);
  });

  it("accepts a draft carrying the marker among other notes", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, metadata: { ...(d.metadata as object), notes: `prose\n\n${bundleMarker(dir, "sandbox")}` } });
    await pdf("doi:10.5072/zenodo.99");
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
  });
});

// ===========================================================================
// MAJOR — the published version comes from a journal, not from mutable meta
// ===========================================================================

describe("MAJOR: published_version is recovered from evidence, not from meta.version", () => {
  it("journals the version and input hashes before the publish POST", async () => {
    let journalAtPublish: Record<string, unknown> | null | undefined;
    const { impl } = fakeZenodo({
      before: async (method, url) => {
        if (method === "POST" && url.includes("/actions/publish")) {
          journalAtPublish = JSON.parse(await readFile(sidecarPath(dir), "utf8")).sandbox?.publishing;
        }
      },
    });
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));

    expect(journalAtPublish).toBeTruthy();
    expect(journalAtPublish!.version).toBe(1);
    const bytes = await readFile(path.join(dir, "paper.pdf"));
    expect(journalAtPublish!.paper_sha256).toBe(createHash("sha256").update(bytes).digest("hex"));
    expect(typeof journalAtPublish!.meta_sha256).toBe("string");
  });

  it("recovers published_version from the journal, not from a meta.version P4 has moved on", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;

    // v1 is published remotely; the response is lost, so local state still says draft.
    // Meanwhile P4 re-emits and meta.version becomes 2.
    const s = await readSidecar(dir);
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      ...s,
      sandbox: {
        ...s.sandbox,
        publishing: {
          version: 1,
          paper_sha256: createHash("sha256").update(await readFile(path.join(dir, "paper.pdf"))).digest("hex"),
          meta_sha256: "a".repeat(64),
          started_at: "2026-09-21T11:00:00.000Z",
        },
      },
    }, null, 2)}\n`);
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);

    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published?.published_version).toBe(1);
  });

  it("falls back to the live record's own metadata.version when no journal exists", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, {
      ...d, state: "done", submitted: true,
      conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}`,
      metadata: { ...(d.metadata as object), version: "v3" },
    });
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 7 }, null, 2)}\n`);
    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published?.published_version).toBe(3);
  });

  it("records null rather than guessing when there is neither journal nor version", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 9 }, null, 2)}\n`);
    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published?.published_version).toBeNull();
  });

  it("clears the publishing journal once the publish is recorded", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.publishing).toBeNull();
  });
});

// ===========================================================================
// MAJOR — abandoning a revision must never leave a dead version_doi
// ===========================================================================

describe("MAJOR: abandoning a revision repairs meta.version_doi unconditionally", () => {
  async function publishThenRevise(impl: (u: string, i?: RequestInit) => Promise<Response>) {
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl, { writeMeta: true }));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, version: 2, doi: "10.5072/zenodo.99", version_doi: "10.5072/zenodo.100",
    }, null, 2)}\n`);
    await newVersion(ctxFor(impl, { writeMeta: true }));
  }

  it("restores the published version DOI even when writeMeta is off", async () => {
    const { impl } = fakeZenodo();
    await publishThenRevise(impl);
    const draftDoi = (await readSidecar(dir)).sandbox!.draft!.version_doi;
    expect((await meta()).version_doi).toBe(draftDoi);

    // writeMeta off: the repair must still happen, because this tool wrote the value.
    await abandon(ctxFor(impl, { writeMeta: false }));
    const m = await meta();
    expect(m.version_doi).toBe("10.5072/zenodo.100"); // the published one
    expect(m.doi).toBe("10.5072/zenodo.99");
  });

  it("leaves meta.json alone when it does not hold the abandoned draft's DOI", async () => {
    const { impl } = fakeZenodo();
    await publishThenRevise(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, version: 2, doi: "10.5072/zenodo.99", version_doi: "10.5072/zenodo.100",
    }, null, 2)}\n`);
    await abandon(ctxFor(impl, { writeMeta: false }));
    expect((await meta()).version_doi).toBe("10.5072/zenodo.100");
  });

  it("never leaves the dead draft DOI behind", async () => {
    const { impl } = fakeZenodo();
    await publishThenRevise(impl);
    const draftDoi = (await readSidecar(dir)).sandbox!.draft!.version_doi;
    await abandon(ctxFor(impl, { writeMeta: false }));
    expect((await meta()).version_doi).not.toBe(draftDoi);
  });
});

// ===========================================================================
// MAJOR — variant symbols are distinct
// ===========================================================================

describe("MAJOR: variant Greek and \\mathnormal keep their distinctions", () => {
  it("renders \\phi and \\varphi as different characters", () => {
    expect(texToPlainText("\\(\\phi\\)")).toBe("ϕ");
    expect(texToPlainText("\\(\\varphi\\)")).toBe("φ");
    expect(texToPlainText("\\(\\phi\\ne\\varphi\\)")).not.toBe("φ ≠ φ");
  });

  it("renders \\epsilon and \\varepsilon as different characters", () => {
    expect(texToPlainText("\\(\\epsilon\\)")).toBe("ϵ");
    expect(texToPlainText("\\(\\varepsilon\\)")).toBe("ε");
  });

  it("keeps the other variant forms distinct from their base letters", () => {
    expect(texToPlainText("\\(\\theta\\vartheta\\)")).toBe("θϑ");
    expect(texToPlainText("\\(\\rho\\varrho\\)")).toBe("ρϱ");
    expect(texToPlainText("\\(\\sigma\\varsigma\\)")).toBe("σς");
    expect(texToPlainText("\\(\\pi\\varpi\\)")).toBe("πϖ");
    expect(texToPlainText("\\(\\kappa\\varkappa\\)")).toBe("κϰ");
  });

  it("maps \\mathnormal to the mathematical italic alphabet, not to upright text", () => {
    expect(texToPlainText("\\(\\mathnormal{x}\\)")).toBe("\u{1D465}");
    expect(texToPlainText("\\(\\mathnormal{x}\\)")).not.toBe(texToPlainText("\\(\\mathrm{x}\\)"));
  });

  it("preserves \\mathnormal when no exact code point exists", () => {
    expect(texToHtml("\\(\\mathnormal{+}\\)")).toContain("<code>");
  });
});

// ===========================================================================
// MINORs
// ===========================================================================

describe("MINOR: a 404 on the published deposition stops loudly", () => {
  it("does not treat it as 'no latest draft'", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    drafts.clear(); // the published record is no longer reachable
    await expect(reconcile(ctxFor(impl))).rejects.toThrow(/published/i);
  });
});

describe("MINOR: dry-run leaves no lock artifact", () => {
  it("creates no .zenodo.lock sentinel", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { dryRun: true }));
    await expect(stat(path.join(dir, COMMAND_LOCK_FILE))).rejects.toThrow();
  });

  it("a real command does create it", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expect(stat(path.join(dir, COMMAND_LOCK_FILE))).resolves.toBeTruthy();
  });
});

describe("MINOR: a compromised command lock aborts side effects in a controlled way", () => {
  it("surfaces an ambiguous-operation error instead of an uncaught throw", async () => {
    // Simulate the lock being compromised mid-command by removing the lock directory
    // while the command is between network calls.
    let compromised = false;
    const { impl } = fakeZenodo({
      before: async (method, url) => {
        if (!compromised && method === "PUT" && url.includes("/api/files/")) {
          compromised = true;
          await rm(path.join(dir, `${COMMAND_LOCK_FILE}.lock`), { recursive: true, force: true });
          // Give proper-lockfile's watcher a moment to notice.
          await new Promise((r) => setTimeout(r, 1200));
        }
      },
    });
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    const err = await publish(ctxFor(impl)).then(() => null, (e: Error) => e);
    // Either it completed before the watcher fired, or it failed in a controlled way —
    // what must NOT happen is an uncaught exception escaping the command.
    if (err) expect(err.message).toMatch(/lock|ambiguous|compromis/i);
  }, 30_000);
});

describe("MINOR: the strict parser and the production gate are unit-tested", () => {
  const B = "/some/bundle";

  it("rejects a mistyped production flag rather than silently using sandbox", () => {
    expect(() => parseStrict("reserve", [B, "--productoin", "--i-understand-this-is-permanent"]))
      .toThrow(/Unknown flag '--productoin'/);
  });

  it("requires BOTH production flags", () => {
    expect(resolveEnvironment(parseStrict("reserve", [B])).name).toBe("sandbox");
    expect(() => resolveEnvironment(parseStrict("reserve", [B, "--production"])))
      .toThrow(/--i-understand-this-is-permanent/);
    expect(resolveEnvironment(parseStrict("reserve", [B, "--production", "--i-understand-this-is-permanent"])).name)
      .toBe("production");
    expect(resolveEnvironment(parseStrict("reserve", [B])).apiBase).toBe(SANDBOX.apiBase);
    expect(resolveEnvironment(parseStrict("reserve", [B, "--production", "--i-understand-this-is-permanent"])).apiBase)
      .toBe(PRODUCTION.apiBase);
  });

  it("scopes subcommand-only flags to their subcommand", () => {
    // A flag may legitimately belong to more than one subcommand — `release` publishes, so it
    // takes the same --allow-unstamped escape hatch `publish` does — but every subcommand NOT
    // in the list must still refuse it rather than ignore it.
    const scoped: [string, string[]][] = [
      ["--allow-unstamped", ["publish", "release"]],
      ["--publish", ["release"]],
      ["--force", ["new-version"]],
      ["--repair", ["status"]],
      ["--discard-stamped-doi", ["abandon"]],
      ["--confirm-no-remote-draft", ["reserve"]],
    ];
    for (const [flag, owners] of scoped) {
      for (const owner of owners) expect(() => parseStrict(owner as never, [B, flag])).not.toThrow();
      for (const other of SUBCOMMANDS) {
        if (owners.includes(other)) continue;
        expect(() => parseStrict(other, [B, flag])).toThrow(/Unknown flag/);
      }
    }
  });

  it("rejects --flag=value, missing values, duplicates and surplus positionals", () => {
    expect(() => parseStrict("reserve", [B, "--license=cc-zero"])).toThrow(/--flag=value/);
    expect(() => parseStrict("reserve", [B, "--license"])).toThrow(/requires a value/);
    expect(() => parseStrict("reserve", [B, "--dry-run", "--dry-run"])).toThrow(/more than once/);
    expect(() => parseStrict("reserve", [B, "extra"])).toThrow(/exactly one bundle directory/);
    expect(() => parseStrict("reserve", [])).toThrow(/needs a bundle directory/);
  });

  it("parses a boolean flag placed before the bundle directory", () => {
    expect(parseStrict("reserve", ["--dry-run", B]).bundleDir).toBe(B);
  });

  it("allows --community to repeat and returns every value", () => {
    const a = parseStrict("reserve", [B, "--community", "one", "--community", "two"]);
    expect(a.values.get("--community")).toEqual(["one", "two"]);
  });
});

describe("MINOR: the real stamp layout matches", () => {
  // The pipeline stamp is being changed so the DOI is never the last token on its line.
  const LAYOUT = "CSWP-2026-008v3 · doi:10.5281/zenodo.99 · [Stat] 27 Aug 2026\n2026 continues here";

  it("matches the DOI in the production stamp layout", () => {
    expect(findDoi(LAYOUT, "10.5281/zenodo.99")).toBe(true);
  });

  it("still rejects a longer DOI in the same layout", () => {
    const longer = LAYOUT.replace("zenodo.99 ", "zenodo.999 ");
    expect(findDoi(longer, "10.5281/zenodo.99")).toBe(false);
    expect(findDoi(longer, "10.5281/zenodo.999")).toBe(true);
  });

  it("matches through a real PDF with that layout", async () => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, minimalPdf("CSWP-2026-008v3 · doi:10.5072/zenodo.99 · [Stat] 27 Aug 2026"));
    const { pdfContainsDoi } = await import("../src/zenodo/pdf_text.js");
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("present");
  });
});
