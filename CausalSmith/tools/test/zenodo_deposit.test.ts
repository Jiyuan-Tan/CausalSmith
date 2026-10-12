// The deposit rules that, if broken, cost something that cannot be undone.
//
//  1. RESERVE IS IDEMPOTENT. Every `POST /deposit/depositions` mints a new
//     `conceptrecid`, i.e. a new concept DOI, i.e. a new permanent identity for the
//     same paper. A reserve that silently opened a second draft would leave the PDF
//     stamped with one DOI and the record registered under another.
//  2. AN UNSTAMPED PDF IS NOT PUBLISHED. The published PDF is frozen; if the DOI
//     printed on page 1 is not the DOI it was registered under, the artefact is
//     permanently wrong and no later fix reaches the copies people downloaded.
//  3. A SANDBOX DOI NEVER REACHES meta.json. Prefix 10.5072 resolves to nothing, and
//     `meta.json` feeds the site's Cite panel, BibTeX and Highwire tags directly.
//  4. meta.json KEEPS EVERYTHING ELSE. It is shared with WP-B's P4 stage and the site;
//     a deposit must be a two-key diff, not a reserialization.
//
// Four mechanisms carry those rules, and most of this file is written against them:
//
//  - ONE LOCK PER COMMAND. Every mutating subcommand holds an exclusive per-bundle lock for
//    its whole duration, network included, and refuses while an emit holds the bundle.
//  - RECONCILE FIRST. Every mutating subcommand begins by asking Zenodo what is actually true
//    and repairing local state, so "the operation succeeded remotely but the local write
//    failed" is fixed by re-running any command.
//  - JOURNAL BEFORE A POST. A create or publish is recorded locally before the request
//    leaves, so a lost response is recoverable from evidence rather than from a guess.
//  - IDENTITY IS EXACT. Markers are hashed and compared as whole lines; DOIs are derived
//    locally and only ever asserted against responses; URLs are never persisted from a
//    response.
//
// A weaker fact is never read as a stronger one: "could not read the PDF" is not "there is no
// PDF", "the search returned nothing" is not "the create did nothing", "the sidecar is
// well-formed" is not "the sidecar belongs to this bundle", and "meta.version says 2" is not
// "version 2 is what we published".
//
// Everything runs against a fake `fetch` and a temp bundle — no network, no clock. Tests name
// the fake-Zenodo model they were written against (see FakeZenodoOptions).

import { describe, it, expect, beforeEach, vi } from "vitest";
import { createHash } from "node:crypto";
import { mkdir, readFile, rm, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import { SANDBOX, PRODUCTION } from "../src/zenodo/client.js";
import {
  abandon, newVersion, publish, reconcile, reserve, status,
} from "../src/zenodo/deposit.js";
import {
  bundleMarker, readSidecar, sidecarPath, withCommandLock,
  CommandLockCompromisedError, COMMAND_LOCK_FILE, type CommandLockHandle, type LockAcquirer,
} from "../src/zenodo/bundle.js";
import { withBundleEmitLock } from "../src/presentation/emit_lock.js";
import {
  DEMO_META, FAKE_DELETE_ALWAYS_204, FAKE_METADATA_REPLACED, FAKE_ONE_SHARED_CONCEPT,
  TEST_TOKEN, minimalPdf, multiPagePdf, unreadablePdf, zenodoTestBed,
  type FakeCall,
} from "./zenodo_fixtures.js";

const TOKEN = TEST_TOKEN;
const META = DEMO_META;

const { h, fakeZenodo, ctxFor } = zenodoTestBed();
let dir: string;
let calls: FakeCall[];
let logs: string[];
let warns: string[];
beforeEach(() => {
  ({ dir, calls, logs, warns } = h);
});

const readJson = async (p: string) => JSON.parse(await readFile(p, "utf8"));
/** The raw sidecar, unvalidated. */
const sidecar = () => readJson(path.join(dir, "zenodo.json"));
const meta = () => readJson(path.join(dir, "meta.json"));
const posts = () => calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"));

/** A real (tiny) PDF showing `text`. It must be a genuine PDF: plain text in a .pdf file is
 *  reported as `unavailable`, not `absent`, so a text stand-in would exercise the wrong
 *  branch entirely. */
const pdf = (text: string) => writeFile(path.join(dir, "paper.pdf"), minimalPdf(text));
const pdfBytes = (buf: Buffer) => writeFile(path.join(dir, "paper.pdf"), buf);

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

describe("reserve", () => {
  it("records the concept DOI derived from conceptrecid, not from prereserve_doi", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    const res = await reserve(ctxFor(impl));
    // prereserve_doi said 10.5281/zenodo.100; the sandbox actually mints 10.5072.
    expect(res.record.concept_doi).toBe("10.5072/zenodo.99");
    expect(res.record.draft?.version_doi).toBe("10.5072/zenodo.100");
    expect(res.record.draft?.deposition_id).toBe(100);
    expect(res.record.published).toBeNull();
    expect((await sidecar()).sandbox.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("is idempotent: a second reserve reuses the draft instead of minting a new DOI", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    const first = await reserve(ctxFor(impl));
    calls.length = 0;
    const second = await reserve(ctxFor(impl));
    expect(second.reused).toBe(true);
    expect(second.record.concept_doi).toBe(first.record.concept_doi);
    expect(second.record.draft?.deposition_id).toBe(first.record.draft?.deposition_id);
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
  });

  it("refuses to replace a concept DOI when the recorded draft vanished, creating nothing", async () => {
    // The draft is gone, so a NEW one would carry a different conceptrecid — a
    // different permanent identity for a paper that may already be stamped. Reconcile
    // stops BEFORE any creation; the earlier version created the replacement first and
    // only then discovered it was not allowed to, leaving an orphan on every retry.
    const { impl, drafts } = fakeZenodo(FAKE_METADATA_REPLACED);
    const first = await reserve(ctxFor(impl));
    drafts.delete(first.record.draft!.deposition_id);
    calls.length = 0;
    const refusal = reserve(ctxFor(impl));
    await expect(refusal).rejects.toThrow(/no longer exists|permanent|by hand/i);
    await expect(refusal).rejects.toThrow(/manual|permanent|refus/i);
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
    expect(drafts.size).toBe(0);
  });

  it("keeps the sandbox DOI out of meta.json by default", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    const m = await meta();
    expect(m.doi).toBeUndefined();
    expect(m.version_doi).toBeUndefined();
    expect(logs.join("\n")).toMatch(/SANDBOX DOI/);
  });

  it("writes the DOI into meta.json only when --write-meta is passed, and says so", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl, { writeMeta: true }));
    const m = await meta();
    expect(m.doi).toBe("10.5072/zenodo.99");
    expect(m.version_doi).toBe("10.5072/zenodo.100");
    expect(warns.join("\n")).toMatch(/WRITING A SANDBOX DOI/);
  });

  it("preserves every other meta.json key, 2-space indent and the trailing newline", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl, { writeMeta: true }));
    const raw = await readFile(path.join(dir, "meta.json"), "utf8");
    expect(raw.endsWith("}\n")).toBe(true);
    expect(raw).toContain('\n  "qid": "stat_demo"');
    const m = await meta();
    for (const [k, v] of Object.entries(META)) expect(m[k]).toEqual(v);
    expect(Object.keys(m).slice(0, Object.keys(META).length)).toEqual(Object.keys(META));
  });

  it("sends nothing and writes nothing under --dry-run", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl, { dryRun: true, writeMeta: true }));
    expect(calls).toHaveLength(0);
    expect((await meta()).doi).toBeUndefined();
    await expect(sidecar()).rejects.toThrow();
  });

  it("a first reserve with no journal creates normally, even when the search sees nothing", async () => {
    const { impl } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204, hideFromSearch: true });
    await reserve(ctxFor(impl));
    expect(posts()).toHaveLength(1);
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

// A crash between draft creation and the sidecar write leaves an orphan on Zenodo. It is
// adopted, never duplicated — and an empty search does not prove the create did nothing,
// because a search index lags behind a write.
describe("reserve — a lost create response never becomes a second draft", () => {
  it("adopts the orphaned draft instead of creating a second one", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    // Simulate the crash: the draft exists on Zenodo, the sidecar was never written.
    await reserve(ctxFor(impl));
    const before = await readSidecar(dir);
    const orphanId = before.sandbox!.draft!.deposition_id;
    await writeFile(path.join(dir, "zenodo.json"), "{}\n");

    calls.length = 0;
    const again = await reserve(ctxFor(impl));
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
    expect(again.record.draft?.deposition_id).toBe(orphanId);
    expect(drafts.size).toBe(1);
  });

  it("records the bundle marker, which is a hash rather than the readable id", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    const s = await readSidecar(dir);
    expect(s.sandbox?.marker).toBe(bundleMarker(dir, "sandbox"));
    expect(s.sandbox?.marker).not.toContain("stat_demo_spec");
  });

  it("tags the created draft with the bundle marker so it is findable", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    const created = [...drafts.values()][0];
    const notes = String((created.metadata as Record<string, unknown>).notes ?? "");
    expect(notes.split("\n").some((l) => l.trim() === bundleMarker(dir, "sandbox"))).toBe(true);
  });

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
    const { impl, marker } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204, hideFromSearch: true });
    await pendingOnly(marker());
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/--confirm-no-remote-draft/);
    expect(posts()).toHaveLength(0);
  });

  it("creates exactly one draft when --confirm-no-remote-draft is given", async () => {
    const { impl, marker, drafts } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204, hideFromSearch: true });
    await pendingOnly(marker());
    calls.length = 0;
    const res = await reserve(ctxFor(impl), { confirmNoRemoteDraft: true });
    expect(posts()).toHaveLength(1);
    expect(drafts.size).toBe(1);
    expect(res.record.pending_reserve).toBeNull();
  });

  it("adopts the orphan without the flag once the search can see it", async () => {
    const { impl, marker, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    await pendingOnly(marker());
    calls.length = 0;
    await reserve(ctxFor(impl));
    expect(posts()).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(id);
    expect(drafts.size).toBe(1);
  });
});

describe("reserve — the journal is durable before the create request is sent", () => {
  it("persists pending_reserve to disk before the creation POST leaves", async () => {
    let seenAtPostTime: unknown = "not-observed";
    const { impl } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204,
      before: async (method, url) => {
        if (method === "POST" && url.endsWith("/deposit/depositions")) {
          const raw = await readFile(sidecarPath(dir), "utf8").catch(() => null);
          seenAtPostTime = raw === null ? null : JSON.parse(raw).sandbox?.pending_reserve;
        }
      },
    });
    await reserve(ctxFor(impl));
    expect(seenAtPostTime).toBeTruthy();
    expect((seenAtPostTime as { marker: string }).marker).toBe(bundleMarker(dir, "sandbox"));
  });

  it("leaves the journal behind when the create fails, so a re-run can reconcile", async () => {
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      if ((init?.method ?? "GET") === "GET") return new Response("[]", { status: 200 });
      return new Response(JSON.stringify({ message: "boom" }), { status: 503 });
    };
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    const s = await readSidecar(dir);
    expect(s.sandbox?.pending_reserve).toBeTruthy();
    expect(s.sandbox?.draft).toBeNull();
  });

  it("journals before creating when the search itself is well-formed", async () => {
    let journalAtPost: unknown = "not-observed";
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      const method = init?.method ?? "GET";
      if (method === "GET") return new Response("[]", { status: 200 });
      journalAtPost = JSON.parse(await readFile(path.join(dir, "zenodo.json"), "utf8"))
        .sandbox?.pending_reserve;
      return new Response(JSON.stringify({ message: "boom" }), { status: 503 });
    };
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(journalAtPost).toBeTruthy();
  });

  it("never records a DOI built from a zero record id", async () => {
    // An unusable body now stops the run at the marker search, before anything is
    // journaled or created — a stricter outcome than the earlier "journal then fail".
    const impl = async (): Promise<Response> => new Response("", { status: 201 });
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(JSON.stringify(await readSidecar(dir))).not.toContain("zenodo.0");
  });
});

// A malformed search response must not read as 'no orphan'.
describe("reserve — the draft search fails closed", () => {
  it("refuses when the listing is not an array, rather than creating a deposit", async () => {
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      if ((init?.method ?? "GET") === "GET") {
        return new Response(JSON.stringify({ hits: { hits: [] } }), { status: 200 });
      }
      return new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: { bucket: "b" } }), { status: 201 });
    };
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/array|listing|unexpected/i);
    expect(posts()).toHaveLength(0);
  });

  it("refuses when a listing row is not a deposition object", async () => {
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      if ((init?.method ?? "GET") === "GET") return new Response(JSON.stringify(["nope"]), { status: 200 });
      return new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: { bucket: "b" } }), { status: 201 });
    };
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(posts()).toHaveLength(0);
  });
});

describe("identity — the bundle marker is exact and bound to this bundle", () => {
  it("is a hash of bundle id and environment, not the bare basename", () => {
    const m = bundleMarker(dir, "sandbox");
    expect(m).toMatch(/^causalsmith-bundle-id:[0-9a-f]{32}$/);
    expect(m).not.toContain("stat_demo_spec");
    const expected = createHash("sha256").update(`stat_demo_spec\nsandbox`).digest("hex").slice(0, 32);
    expect(m).toBe(`causalsmith-bundle-id:${expected}`);
  });

  it("differs between environments for the same bundle", () => {
    expect(bundleMarker(dir, "sandbox")).not.toBe(bundleMarker(dir, "production"));
  });

  it("does not adopt a draft whose marker merely CONTAINS ours", async () => {
    // The old substring rule let bundle `foo` adopt a draft belonging to `foobar`.
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    const ours = bundleMarker(dir, "sandbox");
    drafts.set(500, {
      id: 500, conceptrecid: 499, state: "unsubmitted", submitted: false,
      metadata: { notes: `${ours}extra` },
      links: { bucket: "https://sandbox.zenodo.org/api/files/b" },
    });
    await reserve(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).not.toBe(500);
  });

  it("adopts a draft whose notes carry the marker on its own line", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    const ours = bundleMarker(dir, "sandbox");
    drafts.set(500, {
      id: 500, conceptrecid: 499, state: "unsubmitted", submitted: false,
      metadata: { notes: `Some prose about the paper.\n\n${ours}` },
      links: { bucket: "https://sandbox.zenodo.org/api/files/b" },
    });
    calls.length = 0;
    await reserve(ctxFor(impl));
    expect(posts()).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(500);
  });

  it("refuses to publish into a draft whose notes are not this bundle's", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
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
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, metadata: { ...(d.metadata as object), notes: "causalsmith-bundle-id:0000000000000000000000000000dead" } });
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/marker|belong/i);
    expect(drafts.size).toBe(1);
  });

  it("accepts a draft carrying the marker among other notes", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, metadata: { ...(d.metadata as object), notes: `prose\n\n${bundleMarker(dir, "sandbox")}` } });
    await pdf("doi:10.5072/zenodo.99");
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
  });
});

describe("identity — DOIs and URLs are derived locally; responses are only checked against them", () => {
  it("fails and persists nothing when the API reports a different concept DOI", async () => {
    const { impl: base } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      const res = await base(url, init);
      if ((init?.method ?? "GET") === "POST" && url.includes("/actions/publish")) {
        const body = await res.json() as Record<string, unknown>;
        // A response claiming a production-prefixed concept DOI.
        return new Response(JSON.stringify({ ...body, conceptdoi: "10.5281/zenodo.424242" }), { status: 202 });
      }
      return res;
    };
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdfBytes(minimalPdf("doi:10.5072/zenodo.99"));
    await expect(publish(ctxFor(impl, { writeMeta: true }))).rejects.toThrow(/mismatch|concept/i);

    const s = await readSidecar(dir);
    expect(s.sandbox?.concept_doi).toBe("10.5072/zenodo.99");
    expect(JSON.stringify(s)).not.toContain("424242");
    expect(JSON.stringify(await meta())).not.toContain("424242");
  });

  it("fails when the API reports a different version DOI", async () => {
    const { impl: base } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      const res = await base(url, init);
      if ((init?.method ?? "GET") === "POST" && url.includes("/actions/publish")) {
        const body = await res.json() as Record<string, unknown>;
        return new Response(JSON.stringify({ ...body, doi: "10.5072/zenodo.777777" }), { status: 202 });
      }
      return res;
    };
    await reserve(ctxFor(impl));
    await pdfBytes(minimalPdf("doi:10.5072/zenodo.99"));
    await expect(publish(ctxFor(impl))).rejects.toThrow(/mismatch|doi/i);
    expect(JSON.stringify(await readSidecar(dir))).not.toContain("777777");
  });

  it("ignores a credential-bearing record_html from the response", async () => {
    const { impl: base } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      const res = await base(url, init);
      if ((init?.method ?? "GET") === "POST" && url.includes("/actions/publish")) {
        const body = await res.json() as Record<string, unknown>;
        return new Response(JSON.stringify({
          ...body,
          links: { record_html: `https://sandbox.zenodo.org/records/100?access_token=${TOKEN}` },
        }), { status: 202 });
      }
      return res;
    };
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    const res = await publish(ctxFor(impl));
    expect(res.record.published?.record_url).toBe("https://sandbox.zenodo.org/records/100");
    const raw = await readFile(sidecarPath(dir), "utf8");
    expect(raw).not.toContain(TOKEN);
    expect(raw).not.toContain("access_token");
    expect([...logs, ...warns].join("\n")).not.toContain(TOKEN);
  });

  it("refuses rather than replacing a 10.5281 doi with a sandbox one", async () => {
    const { impl } = fakeZenodo();
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, doi: "10.5281/zenodo.777", version_doi: "10.5281/zenodo.778",
    }, null, 2)}\n`);
    await expect(reserve(ctxFor(impl, { writeMeta: true })))
      .rejects.toThrow(/production|10\.5281|non-sandbox/i);
    expect((await meta()).doi).toBe("10.5281/zenodo.777");
  });

  it("keys the sidecar by environment so sandbox cannot clobber production", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    const s = await sidecar();
    s.production = {
      environment: "production", api_base: PRODUCTION.apiBase,
      conceptrecid: 554, concept_doi: "10.5281/zenodo.554",
      marker: bundleMarker(dir, "production"),
      published: {
        deposition_id: 555, version_doi: "10.5281/zenodo.555", published_version: 1,
        record_url: "https://zenodo.org/records/555", published_at: "2026-09-01T00:00:00.000Z",
      },
      draft: null, pending_reserve: null,
      updated_at: "2026-09-01T00:00:00.000Z",
    };
    await writeFile(path.join(dir, "zenodo.json"), `${JSON.stringify(s, null, 2)}\n`);
    await abandon(ctxFor(impl));
    const after = await sidecar();
    expect(after.sandbox).toBeUndefined();
    expect(after.production.concept_doi).toBe("10.5281/zenodo.554");
  });

  it("never leaks the token into any logged or warned line", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl, { writeMeta: true }));
    await status(ctxFor(impl));
    const all = [...logs, ...warns].join("\n");
    expect(all.length).toBeGreaterThan(0);
    expect(all).not.toContain(TOKEN);
    expect(JSON.stringify(await sidecar())).not.toContain(TOKEN);
    expect(JSON.stringify(await meta())).not.toContain(TOKEN);
  });
});

describe("the sidecar fails loudly rather than looking absent", () => {
  it.each<{ what: string; content: string; pattern?: RegExp }>([
    { what: "a JSON array", content: "[]\n", pattern: /object|schema|corrupt/i },
    { what: "malformed JSON", content: "{not json\n" },
    { what: "a schema-invalid environment record", content: `${JSON.stringify({ sandbox: { nonsense: true } })}\n` },
  ])("treats $what as corruption, not as 'no sidecar'", async ({ content, pattern }) => {
    await writeFile(path.join(dir, "zenodo.json"), content);
    if (pattern) await expect(readSidecar(dir)).rejects.toThrow(pattern);
    else await expect(readSidecar(dir)).rejects.toThrow();
  });

  it("returns {} only when the file does not exist", async () => {
    expect(await readSidecar(dir)).toEqual({});
  });

  it("does not create a duplicate deposit when the sidecar is corrupt", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "zenodo.json"), "[]\n");
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(calls.filter((c) => c.method === "POST")).toHaveLength(0);
  });
});

describe("the sidecar schema is recursive and environment-consistent", () => {
  const write = (v: unknown) => writeFile(sidecarPath(dir), `${JSON.stringify(v, null, 2)}\n`);
  const good = () => ({
    environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: 99,
    concept_doi: "10.5072/zenodo.99", marker: bundleMarker(dir, "sandbox"),
    published: null, draft: null, pending_reserve: null,
    updated_at: "2026-09-21T11:00:00.000Z",
  });

  it.each<{ what: string; patch: Record<string, unknown>; pattern: RegExp }>([
    { what: "whose environment does not match its key", patch: { environment: "production" }, pattern: /environment/i },
    { what: "whose api_base is not that environment's", patch: { api_base: "https://zenodo.org/api" }, pattern: /api_base/i },
    { what: "whose concept DOI prefix belongs to the other instance", patch: { concept_doi: "10.5281/zenodo.99" }, pattern: /prefix|10\.5072/i },
    { what: "whose nested draft record is malformed", patch: { draft: {} }, pattern: /draft/i },
    { what: "whose nested published record is malformed", patch: { published: { deposition_id: "x" } }, pattern: /published/i },
    { what: "whose concept DOI disagrees with conceptrecid", patch: { concept_doi: "10.5072/zenodo.12345" }, pattern: /conceptrecid|concept_doi/i },
  ])("refuses a record $what", async ({ patch, pattern }) => {
    await write({ schema: 2, sandbox: { ...good(), ...patch } });
    await expect(readSidecar(dir)).rejects.toThrow(pattern);
  });

  it("accepts a well-formed record", async () => {
    await write({ schema: 2, sandbox: good() });
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });

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
});

describe("publish", () => {
  it("refuses a PDF that does not carry the DOI it would be registered under", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("a paper with no DOI stamp at all");
    await expect(publish(ctxFor(impl))).rejects.toThrow(/does not contain the DOI/);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("publishes a PDF that does carry the DOI", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("page 1 ... doi:10.5072/zenodo.99 ... rest");
    const res = await publish(ctxFor(impl));
    expect(res.record.published?.version_doi).toBe("10.5072/zenodo.100");
    expect(res.record.published?.record_url).toBe("https://sandbox.zenodo.org/records/100");
    expect(res.record.draft).toBeNull();
    expect(logs.join("\n")).toMatch(/Stamp check: 10\.5072\/zenodo\.99 found/);
  });

  it("tolerates the spacing an extractor inserts into the stamped DOI", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    // A rotated margin stamp comes back one glyph group at a time; the record id's
    // digits still have to be contiguous.
    await pdf("d o i : 1 0 . 5 0 7 2 / z e n o d o . 99");
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
  });

  it("publishes an unstamped PDF only with --allow-unstamped, and warns", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("no stamp here");
    const res = await publish(ctxFor(impl, { allowUnstamped: true }));
    expect(res.record.published).toBeTruthy();
    expect(warns.join("\n")).toMatch(/UNSTAMPED PDF/);
  });

  it("uploads the PDF and sets metadata before publishing, in that order", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    calls.length = 0;
    await publish(ctxFor(impl));
    const seq = calls.map((c) => `${c.method} ${c.url.replace(/^https:\/\/sandbox\.zenodo\.org\/api/, "")}`);
    expect(seq).toEqual([
      // reconcile asks what is actually true before publish acts on local state
      "GET /deposit/depositions/100",
      "GET /deposit/depositions/100",
      "PUT /files/bucket-100/paper.pdf",
      "PUT /deposit/depositions/100",
      "POST /deposit/depositions/100/actions/publish",
    ]);
    const put = calls.find((c) => c.url.endsWith("/deposit/depositions/100") && c.method === "PUT");
    const sent = JSON.parse(put!.body!).metadata;
    expect(sent.title).toBe("[TEST] A demo paper");
    expect(sent.creators).toEqual([{ name: "CausalSmith" }]);
  });

  it("refuses to publish without a reservation", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await pdf("doi:10.5072/zenodo.99");
    await expect(publish(ctxFor(impl))).rejects.toThrow(/Run 'reserve' first/);
  });

  it("is a no-op when the deposition is already published", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    calls.length = 0;
    const again = await publish(ctxFor(impl));
    expect(again.alreadyPublished).toBe(true);
    // Reconcile still asks Zenodo, but nothing is published a second time.
    expect(calls.every((c) => c.method === "GET")).toBe(true);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("refuses, and persists nothing, when the reserved concept DOI no longer matches", async () => {
    // A warning is not enough: the whole point is that the LOCALLY DERIVED DOI is
    // authoritative, so a divergence must abort before anything is written.
    const { impl } = fakeZenodo({ ...FAKE_METADATA_REPLACED, conceptrecid: 99 });
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf("doi:10.5072/zenodo.99");
    const s = await sidecar();
    s.sandbox.concept_doi = "10.5072/zenodo.12345";
    s.sandbox.conceptrecid = 12345; // keep the sidecar itself schema-valid
    await writeFile(path.join(dir, "zenodo.json"), `${JSON.stringify(s, null, 2)}\n`);

    const metaBefore = JSON.stringify(await meta());
    await expect(publish(ctxFor(impl, { allowUnstamped: true, writeMeta: true })))
      .rejects.toThrow(/refusing to publish|MISMATCH|reserved/i);
    const after = await sidecar();
    expect(after.sandbox.published).toBeFalsy();
    expect(after.sandbox.concept_doi).toBe("10.5072/zenodo.12345");
    // Nothing at all was persisted by the failed publish.
    expect(JSON.stringify(await meta())).toBe(metaBefore);
  });

  it("publish writes the sidecar BEFORE meta.json", async () => {
    // If the order were reversed, a crash between them would leave meta.json claiming
    // a published DOI that no local record can locate or repair.
    const order: string[] = [];
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf("doi:10.5072/zenodo.99");
    const ctx = ctxFor(impl, { writeMeta: true });
    const orig = ctx.log;
    await publish({
      ...ctx,
      log: (l) => {
        if (/^Published:/.test(l)) order.push("sidecar");
        if (/^meta\.json updated/.test(l)) order.push("meta");
        orig(l);
      },
    });
    expect(order).toEqual(["sidecar", "meta"]);
  });
});

// The stamp is on page 1 and nowhere else, so that is the page the gate asks about; and a
// PDF that cannot be read is refused, not waved through with a warning.
describe("publish — the stamp gate refuses what it cannot verify, and looks at page 1", () => {
  const DOI = "10.5072/zenodo.99";

  it("refuses when extraction fails, rather than warning and publishing", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(unreadablePdf());
    await expect(publish(ctxFor(impl))).rejects.toThrow(/could not be (read|verified)|unreadable/i);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("uses a DIFFERENT message for unverifiable than for absent", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(unreadablePdf());
    const unreadable = await publish(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    await pdfBytes(minimalPdf("no stamp here"));
    const absent = await publish(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(unreadable).not.toBe(absent);
    expect(absent).toMatch(/does not contain/i);
  });

  it("still lets --allow-unstamped through for an unverifiable PDF", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(unreadablePdf());
    await expect(publish(ctxFor(impl, { allowUnstamped: true }))).resolves.toBeTruthy();
    expect(warns.join("\n")).toMatch(/!!/);
  });

  it("refuses a PDF whose only mention of the DOI is on page 5", async () => {
    // A related-work citation, an acknowledgement or a bibliography entry can perfectly well
    // name this concept DOI — it is the paper's own, and P5 or the author may cite the record.
    // Whole-document matching read that as a stamp and published a paper whose page 1 prints
    // nothing, which is precisely the permanently-wrong artefact this gate exists to prevent.
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(multiPagePdf(["Title page, unstamped.", "two", "three", "four", `See doi:${DOI}`]));
    await expect(publish(ctxFor(impl))).rejects.toThrow(/does not contain/i);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("accepts the same DOI when it IS on page 1", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(multiPagePdf([`Title page. doi:${DOI} [Stat]`, "two", "three", "four", "five"]));
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
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

describe("publish — published_version is recovered from the publishing journal, not from meta.version", () => {
  it("journals the version and input hashes before the publish POST", async () => {
    let journalAtPublish: Record<string, unknown> | null | undefined;
    const { impl } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204,
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
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
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
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
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
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 9 }, null, 2)}\n`);
    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published?.published_version).toBeNull();
  });

  it("clears the publishing journal once the publish is recorded", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.publishing).toBeNull();
  });

  it("a stale publishing journal does not mark a still-unpublished draft as published", async () => {
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

describe("new-version", () => {
  it("keeps the concept DOI and reserves a new version DOI", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2, revised: "2026-09-01" }, null, 2)}\n`);

    const res = await newVersion(ctxFor(impl));
    expect(res.record.concept_doi).toBe("10.5072/zenodo.99");
    expect(res.record.draft?.deposition_id).toBe(101);
    expect(res.record.draft?.version_doi).toBe("10.5072/zenodo.101");
    // v1 stays published and citable while v2 is drafted.
    expect(res.record.published?.deposition_id).toBe(100);
    expect(warns.join("\n")).not.toMatch(/MISMATCH/);
  });

  it("refuses when meta.version has not moved past the published version", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/nothing new to deposit/);
    await expect(newVersion(ctxFor(impl), { force: true })).resolves.toBeTruthy();
  });

  it("refuses to version an unpublished draft", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/Nothing is published/);
  });

  it("replaces the inherited paper.pdf in the new draft without deleting it first", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    calls.length = 0;
    await publish(ctxFor(impl));
    expect(calls.some((c) => c.method === "DELETE")).toBe(false);
    expect(calls.some((c) => c.method === "PUT" && c.url.endsWith("/files/bucket-101/paper.pdf"))).toBe(true);
  });

  it("refuses, before posting, when the live published record is not this bundle's", async () => {
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

describe("new-version — requires a demonstrated version advance", () => {
  async function publishV1(impl: (u: string, i?: RequestInit) => Promise<Response>, m: object = META) {
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(m, null, 2)}\n`);
    await reserve(ctxFor(impl));
    await pdfBytes(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl));
  }

  it("refuses when meta.version is missing", async () => {
    const { version: _v, ...noVersion } = META;
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl, noVersion);
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/version/i);
  });

  it("refuses when meta.version is not an integer", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: "2" }, null, 2)}\n`);
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/version/i);
  });

  it("refuses --force when there is no published record at all", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await expect(newVersion(ctxFor(impl), { force: true })).rejects.toThrow();
  });

  it("allows a genuine advance", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await expect(newVersion(ctxFor(impl))).resolves.toBeTruthy();
  });
});

describe("abandon", () => {
  it("deletes an unpublished draft and clears both the sidecar entry and meta.json", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl, { writeMeta: true }));
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
    await abandon(ctxFor(impl));
    expect(drafts.size).toBe(0);
    expect((await sidecar()).sandbox).toBeUndefined();
    const m = await meta();
    expect(m.doi).toBeNull();
    expect(m.version_doi).toBeNull();
    expect(m.tldr).toBe(META.tldr);
  });

  it("does not clear a meta.json DOI that belongs to a different deposit", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    // A production DOI already on the bundle must survive a sandbox abandon.
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, doi: "10.5281/zenodo.777" }, null, 2)}\n`);
    await abandon(ctxFor(impl));
    expect((await meta()).doi).toBe("10.5281/zenodo.777");
  });

  it("refuses to abandon when the only thing there is a published record", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/PUBLISHED/);
  });
});

describe("abandon — a revision draft goes, the published version and its DOIs stay", () => {
  async function publishV1(impl: (u: string, i?: RequestInit) => Promise<Response>) {
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdfBytes(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl, { writeMeta: true }));
  }

  it("keeps the published record and the concept DOI when a v2 draft is abandoned", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl, { writeMeta: true }));
    await abandon(ctxFor(impl, { writeMeta: true }));

    const s = await readSidecar(dir);
    expect(s.sandbox?.published).toBeTruthy();
    expect(s.sandbox?.published?.deposition_id).toBe(100);
    expect(s.sandbox?.concept_doi).toBe("10.5072/zenodo.99");
    expect(s.sandbox?.draft).toBeFalsy();
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });

  it("a reserve after abandoning a revision does NOT mint a second concept DOI", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    await abandon(ctxFor(impl));
    calls.length = 0;
    await reserve(ctxFor(impl));
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("never clears a concept DOI from meta.json while a version is published", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2, doi: "10.5072/zenodo.99" }, null, 2)}\n`);
    await newVersion(ctxFor(impl, { writeMeta: true }));
    await abandon(ctxFor(impl, { writeMeta: true }));
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });

  it("does not apply the stamped-DOI check when abandoning a REVISION draft", async () => {
    // v1 stays published, so its stamped concept DOI remains correct.
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    await abandon(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published).toBeTruthy();
    expect(drafts.size).toBe(1);
  });

  it("restores the published version DOI even when writeMeta is off", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
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
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await publishThenRevise(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({
      ...META, version: 2, doi: "10.5072/zenodo.99", version_doi: "10.5072/zenodo.100",
    }, null, 2)}\n`);
    await abandon(ctxFor(impl, { writeMeta: false }));
    expect((await meta()).version_doi).toBe("10.5072/zenodo.100");
  });

  it("never leaves the dead draft DOI behind", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await publishThenRevise(impl);
    const draftDoi = (await readSidecar(dir)).sandbox!.draft!.version_doi;
    await abandon(ctxFor(impl, { writeMeta: false }));
    expect((await meta()).version_doi).not.toBe(draftDoi);
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

// Only ENOENT means 'there is no PDF': a PDF that exists but cannot be read might carry the
// DOI, so absence cannot be established.
describe("abandon — refuses to orphan a DOI the local PDF may already print", () => {
  it("refuses when paper.pdf contains the reservation's concept DOI", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1); // the draft was NOT deleted
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("refuses when the PDF cannot be read, because absence cannot be established", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "paper.pdf"), Buffer.from("%PDF-1.4\ngarbage"));
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1);
  });

  it("proceeds, loudly, with --discard-stamped-doi", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await abandon(ctxFor(impl), { discardStampedDoi: true });
    expect(drafts.size).toBe(0);
    expect(warns.join("\n")).toMatch(/every compiled PDF|now wrong/i);
  });

  it("proceeds without the flag when the PDF does not carry the DOI", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("an unstamped paper");
    await abandon(ctxFor(impl));
    expect(drafts.size).toBe(0);
  });

  it("abandon refuses when paper.pdf exists but cannot be read", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await mkdir(path.join(dir, "paper.pdf"), { recursive: true }); // unreadable as a file
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1);
  });

  it("abandon proceeds only when the PDF is genuinely absent (ENOENT)", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await rm(path.join(dir, "paper.pdf"), { force: true });
    await abandon(ctxFor(impl));
    expect(drafts.size).toBe(0);
  });
});

// `abandon --discard-stamped-doi` is the remedy reconcile's own refusal names, so it has to
// work in exactly the state that refusal describes.
describe("abandon — a first reservation, including one whose draft is already gone remotely", () => {
/** The state a lost first reservation leaves: a recorded draft that is gone remotely. */
async function lostFirstReservation(impl: (u: string, i?: RequestInit) => Promise<Response>,
                                    drafts: Map<number, unknown>) {
  await reserve(ctxFor(impl, { writeMeta: true }));
  const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
  drafts.delete(id);
  return id;
}

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

  it("clears a lost first reservation whose draft is gone remotely", async () => {
    const { impl, drafts } = fakeZenodo();
    await lostFirstReservation(impl, drafts);
    // This is precisely what reconcile's refusal tells the operator to run.
    await abandon(ctxFor(impl, { writeMeta: true }), { discardStampedDoi: true });
    expect((await readSidecar(dir)).sandbox).toBeUndefined();
    expect((await meta()).doi).toBeNull();
    expect((await meta()).version_doi).toBeNull();
  });

  it("REFUSES a lost first reservation without the flag", async () => {
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

describe("reconcile repairs state that a lost response left behind", () => {
  it("adopts a recorded draft that Zenodo already published", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf("doi:10.5072/zenodo.99");
    // Publish remotely, then roll local state back to "still a draft", as a connection
    // reset between Zenodo's commit and our write would.
    const before = await readSidecar(dir);
    const id = before.sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, {
      ...d, state: "done", submitted: true,
      conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}`,
      links: { ...(d.links as object), record_html: `https://sandbox.zenodo.org/records/${id}` },
    });

    await reconcile(ctxFor(impl, { writeMeta: true }));
    const s = await readSidecar(dir);
    expect(s.sandbox?.published?.deposition_id).toBe(id);
    expect(s.sandbox?.published?.version_doi).toBe(`10.5072/zenodo.${id}`);
    expect(s.sandbox?.draft).toBeNull();
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });

  it("any re-run of publish repairs it, rather than treating a public record as editable", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });

    const res = await publish(ctxFor(impl));
    expect(res.alreadyPublished).toBe(true);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("adopts the latest_draft of a published record when the sidecar has none", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    // A new-version POST that succeeded remotely but whose response was lost.
    const pubId = (await readSidecar(dir)).sandbox!.published!.deposition_id;
    const parent = drafts.get(pubId)!;
    drafts.set(777, {
      id: 777, conceptrecid: parent.conceptrecid, state: "unsubmitted", submitted: false,
      metadata: { ...(parent.metadata as object) }, links: { bucket: "https://sandbox.zenodo.org/api/files/b777" },
    });
    parent.links = { ...(parent.links as object), latest_draft: "https://sandbox.zenodo.org/api/deposit/depositions/777" };

    await reconcile(ctxFor(impl));
    const s = await readSidecar(dir);
    expect(s.sandbox?.draft?.deposition_id).toBe(777);
    expect(s.sandbox?.published?.deposition_id).toBe(pubId);
  });

  it("new-version does not open a second draft when one is already open remotely", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    const pubId = (await readSidecar(dir)).sandbox!.published!.deposition_id;
    const parent = drafts.get(pubId)!;
    drafts.set(777, {
      id: 777, conceptrecid: parent.conceptrecid, state: "unsubmitted", submitted: false,
      metadata: { ...(parent.metadata as object) }, links: { bucket: "https://sandbox.zenodo.org/api/files/b777" },
    });
    parent.links = { ...(parent.links as object), latest_draft: "https://sandbox.zenodo.org/api/deposit/depositions/777" };

    calls.length = 0;
    await newVersion(ctxFor(impl));
    expect(calls.filter((c) => c.url.includes("/actions/newversion"))).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(777);
  });

  it("a pending journal with no recorded id is resolved by marker search", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    // Roll local state back to "pending, nothing recorded".
    const s = await readSidecar(dir);
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      schema: 2,
      sandbox: {
        ...s.sandbox, conceptrecid: null, concept_doi: null, draft: null,
        pending_reserve: { marker: s.sandbox!.marker, started_at: "2026-09-21T11:00:00.000Z" },
      },
    }, null, 2)}\n`);

    calls.length = 0;
    await reconcile(ctxFor(impl));
    expect(posts()).toHaveLength(0);
    expect((await readSidecar(dir)).sandbox?.draft?.deposition_id).toBe(id);
    expect(drafts.size).toBe(1);
  });

  it("a vanished draft with NO concept DOI is simply cleared", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await writeFile(sidecarPath(dir), `${JSON.stringify({
      schema: 2,
      sandbox: {
        environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: null, concept_doi: null,
        marker: bundleMarker(dir, "sandbox"),
        published: null,
        draft: { deposition_id: 4242, version_doi: "10.5072/zenodo.4242", opened_at: "2026-09-21T11:00:00.000Z" },
        pending_reserve: null, updated_at: "2026-09-21T11:00:00.000Z",
      },
    }, null, 2)}\n`);
    await reconcile(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.draft).toBeNull();
  });

  it("a 404 on the published deposition stops loudly, rather than reading as 'no latest draft'", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    drafts.clear(); // the published record is no longer reachable
    await expect(reconcile(ctxFor(impl))).rejects.toThrow(/published/i);
  });

  it("the refusal does not say 'delete the entry' when a version is published", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    drafts.clear(); // even the published record is unreachable
    const msg = await reconcile(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).not.toMatch(/delete the "?sandbox"? entry|delete the entry/i);
  });

  it("the refusal warns about a second concept DOI even in the first-reservation case", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    drafts.clear();
    const msg = await reserve(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/second|different|new concept DOI/i);
    expect(msg).toMatch(/recompil|stamped/i);
  });
});

describe("reconcile — a revision draft that vanished remotely is recoverable", () => {
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
});

describe("reconcile — links.latest_draft, in the shapes Zenodo actually returns", () => {
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

describe("status", () => {
  it("reports the recorded deposit alongside what Zenodo says", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    await reserve(ctxFor(impl));
    const res = await status(ctxFor(impl));
    expect(res.record?.concept_doi).toBe("10.5072/zenodo.99");
    expect(res.live?.state).toBe("unsubmitted");
    expect(res.meta.doi).toBeNull();
  });

  it("reports cleanly on a bundle with no deposit", async () => {
    const { impl } = fakeZenodo(FAKE_METADATA_REPLACED);
    const res = await status(ctxFor(impl));
    expect(res.record).toBeNull();
    expect(logs.join("\n")).toMatch(/No sandbox deposit recorded/);
  });

  it("reports both a published version and an open revision draft", async () => {
    const { impl } = fakeZenodo(FAKE_ONE_SHARED_CONCEPT);
    await reserve(ctxFor(impl));
    await pdfBytes(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    const s = await status(ctxFor(impl));
    expect(s.record?.published?.deposition_id).toBe(100);
    expect(s.record?.draft?.deposition_id).toBe(101);
    expect(s.record?.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("is read-only by default and does not repair", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await status(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published).toBeNull();
  });

  it("repairs with --repair", async () => {
    const { impl, drafts } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await status(ctxFor(impl), { repair: true });
    expect((await readSidecar(dir)).sandbox?.published?.deposition_id).toBe(id);
  });
});

describe("the per-bundle command lock serialises whole subcommands", () => {
  it("makes a concurrent reserve wait, then reuse rather than create", async () => {
    let releaseFirst: () => void = () => {};
    const gate = new Promise<void>((r) => { releaseFirst = r; });
    let firstInFlight = false;

    const { impl, drafts } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204,
      before: async (method, url) => {
        // Hold the FIRST create open until the second reserve has had time to block.
        if (method === "POST" && url.endsWith("/deposit/depositions") && !firstInFlight) {
          firstInFlight = true;
          await gate;
        }
      },
    });

    const a = reserve(ctxFor(impl));
    // Give A time to take the lock and reach the create.
    await vi.waitFor(() => expect(firstInFlight).toBe(true));
    const b = reserve(ctxFor(impl));
    releaseFirst();
    await Promise.all([a, b]);

    expect(posts()).toHaveLength(1);
    expect(drafts.size).toBe(1);
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  }, 60_000);

  it("creates the lock sentinel inside the bundle", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await expect(stat(path.join(dir, ".zenodo.lock"))).resolves.toBeTruthy();
  });

  it("releases the lock when the command throws", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl));
    await pdf("an unstamped paper");
    await expect(publish(ctxFor(impl))).rejects.toThrow();
    // A following command must not block.
    await expect(status(ctxFor(impl))).resolves.toBeTruthy();
  }, 30_000);

  it("a dry-run creates no .zenodo.lock sentinel", async () => {
    const { impl } = fakeZenodo(FAKE_DELETE_ALWAYS_204);
    await reserve(ctxFor(impl, { dryRun: true }));
    await expect(stat(path.join(dir, COMMAND_LOCK_FILE))).rejects.toThrow();
  });
});

describe("a compromised command lock aborts side effects in a controlled way", () => {
  it("surfaces an ambiguous-operation error instead of an uncaught throw", async () => {
    // Simulate the lock being compromised mid-command by removing the lock directory
    // while the command is between network calls.
    let compromised = false;
    const { impl } = fakeZenodo({ ...FAKE_DELETE_ALWAYS_204,
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
