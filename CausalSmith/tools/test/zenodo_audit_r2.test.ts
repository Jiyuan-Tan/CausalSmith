// Regression tests for the SECOND audit of the Zenodo work package.
//
// Round 1 closed 13 findings by adding guards. The auditor's verdict on that approach
// was that the attack surface had grown: each guard was correct and each gap between
// guards was a new finding. Round 2 is therefore structural. Four ideas replace most
// of the individual checks, and this file is written against those ideas rather than
// against their implementations:
//
//   1. ONE LOCK PER COMMAND. Every mutating subcommand holds an exclusive per-bundle
//      lock for its whole duration, network included. Concurrency is then not a thing
//      the deposit logic has to reason about at all.
//   2. RECONCILE FIRST. Every mutating subcommand begins by asking Zenodo what is
//      actually true and repairing local state. "The operation succeeded remotely but
//      the local write failed" stops being a special case: re-running any command
//      fixes it.
//   3. NEVER REPLAY A POST. Not on 5xx, not on a network error, and not on 429 — a
//      proxy can rate-limit a request an upstream already performed.
//   4. IDENTITY IS EXACT. Markers are hashed and compared as whole lines; DOIs are
//      derived locally and only ever asserted against responses; URLs are never
//      persisted from a response.

import { describe, it, expect, beforeEach, vi } from "vitest";
import { mkdir, mkdtemp, readFile, writeFile, stat } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { SANDBOX, ZenodoClient, ZenodoAmbiguousError } from "../src/zenodo/client.js";
import {
  abandon, newVersion, publish, reconcile, reserve, status, type DepositContext,
} from "../src/zenodo/deposit.js";
import { bundleMarker, readSidecar, sidecarPath } from "../src/zenodo/bundle.js";
import { findDoi } from "../src/zenodo/pdf_text.js";
import { texToHtml, texToPlainText } from "../src/zenodo/metadata.js";
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
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-r2-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = []; logs = []; warns = [];
});

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));
const pdf = (text: string) => writeFile(path.join(dir, "paper.pdf"), minimalPdf(text));
const posts = () => calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"));

/** A fake Zenodo with hooks for the interleavings this round is about. */
function fakeZenodo(opts: {
  conceptrecid?: number;
  nextId?: number;
  /** Called before each request; may throw or return a Response to pre-empt it. */
  before?: (method: string, url: string) => Promise<Response | void>;
} = {}) {
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = opts.nextId ?? 100;
  const baseConcept = opts.conceptrecid ?? 99;
  let creations = 0;
  let conceptrecid = baseConcept;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;

  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url, body });
    if (opts.before) {
      const pre = await opts.before(method, url);
      if (pre) return pre;
    }
    const json = (status: number, value: unknown) => new Response(JSON.stringify(value), { status });
    const u = new URL(url);

    if (method === "GET" && u.pathname.endsWith("/deposit/depositions") && u.search) {
      const marker = decodeURIComponent(u.searchParams.get("q") ?? "").replace(/^"|"$/g, "");
      return json(200, [...drafts.values()].filter(
        (d) => d.submitted === false &&
          String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "")
            .split("\n").some((l) => l.trim() === marker),
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
      const published = {
        ...dep, state: "done", submitted: true,
        conceptdoi: `10.5072/zenodo.${dep.conceptrecid}`, doi: `10.5072/zenodo.${id}`,
        links: { ...(dep.links as object), record_html: `https://sandbox.zenodo.org/records/${id}` },
      };
      drafts.set(id, published);
      return json(202, published);
    }
    const nv = /\/deposit\/depositions\/(\d+)\/actions\/newversion$/.exec(u.pathname);
    if (method === "POST" && nv) {
      const parentId = Number(nv[1]);
      const parent = drafts.get(parentId)!;
      const id = nextId++;
      drafts.set(id, {
        id, conceptrecid: parent.conceptrecid, state: "unsubmitted", submitted: false,
        metadata: { ...(parent.metadata as object) },
        links: { bucket: bucketOf(id) },
        files: [{ id: "inherited", filename: "paper.pdf" }],
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
    repoUrl: "https://github.com/Jiyuan-Tan/CausalSmith",
    titlePrefix: "[TEST] ",
    log: (l) => logs.push(l), warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...rest,
  };
}

// ===========================================================================
// BLOCKER — the stamp matcher must apply the digit boundary across line wraps
// ===========================================================================

describe("BLOCKER: a line-wrapped longer DOI must not satisfy the stamp guard", () => {
  const D = "10.5072/zenodo.99";

  it("rejects a newline between the DOI and the extra digit", () => {
    expect(findDoi("doi:10.5072/zenodo.99\n9 rest", D)).toBe(false);
  });

  it("rejects a hyphenated line break before the extra digit", () => {
    expect(findDoi("doi:10.5072/zenodo.99-\n9 rest", D)).toBe(false);
  });

  it("rejects a soft hyphen before the extra digit", () => {
    expect(findDoi("doi:10.5072/zenodo.99­9", D)).toBe(false);
  });

  it("rejects the extra digit after a plain space", () => {
    expect(findDoi("doi:10.5072/zenodo.99 9", D)).toBe(false);
  });

  it("rejects when the spaced-out pass would otherwise match a longer DOI", () => {
    expect(findDoi("1 0 . 5 0 7 2 / z e n o d o . 9 9\n9", D)).toBe(false);
  });

  it("still accepts the DOI followed by a non-digit", () => {
    expect(findDoi("doi:10.5072/zenodo.99 Page three", D)).toBe(true);
    expect(findDoi("doi:10.5072/zenodo.99.", D)).toBe(true);
    expect(findDoi("doi:10.5072/zenodo.99\nAbstract", D)).toBe(true);
  });

  it("accepts a glyph-spaced PREFIX but not a split record id", () => {
    // Gaps where a line wraps are tolerated; a gap inside the record id is not, because
    // `zenodo.9 9` is as likely to be `.9` followed by a stray digit as a spaced `.99`.
    expect(findDoi("1 0 . 5 0 7 2 / z e n o d o . 99", D)).toBe(true);
    expect(findDoi("1 0 . 5 0 7 2 / z e n o d o . 9 9", D)).toBe(false);
  });

  it("rejects a longer DOI in front", () => {
    expect(findDoi("110.5072/zenodo.99", D)).toBe(false);
    expect(findDoi("1\n10.5072/zenodo.99", D)).toBe(false);
  });
});

// ===========================================================================
// BLOCKER — abandoning a reservation whose DOI is already stamped into the PDF
// ===========================================================================

describe("BLOCKER: abandon refuses to orphan a DOI the local PDF already prints", () => {
  it("refuses when paper.pdf contains the reservation's concept DOI", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1); // the draft was NOT deleted
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("refuses when the PDF cannot be read, because absence cannot be established", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "paper.pdf"), Buffer.from("%PDF-1.4\ngarbage"));
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/--discard-stamped-doi/);
    expect(drafts.size).toBe(1);
  });

  it("proceeds, loudly, with --discard-stamped-doi", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await abandon(ctxFor(impl), { discardStampedDoi: true });
    expect(drafts.size).toBe(0);
    expect(warns.join("\n")).toMatch(/every compiled PDF|now wrong/i);
  });

  it("proceeds without the flag when the PDF does not carry the DOI", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("an unstamped paper");
    await abandon(ctxFor(impl));
    expect(drafts.size).toBe(0);
  });

  it("does not apply the check when abandoning a REVISION draft", async () => {
    // v1 stays published, so its stamped concept DOI remains correct.
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    await abandon(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published).toBeTruthy();
    expect(drafts.size).toBe(1);
  });
});

// ===========================================================================
// BLOCKER / MAJOR — reconcile-first
// ===========================================================================

describe("BLOCKER: reconcile repairs state that a lost response left behind", () => {
  it("(i) adopts a recorded draft that Zenodo already published", async () => {
    const { impl, drafts } = fakeZenodo();
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

  it("(i) any re-run of publish repairs it, rather than treating a public record as editable", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("doi:10.5072/zenodo.99");
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });

    const res = await publish(ctxFor(impl));
    expect(res.alreadyPublished).toBe(true);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("(ii) adopts the latest_draft of a published record when the sidecar has none", async () => {
    const { impl, drafts } = fakeZenodo();
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

  it("(ii) new-version therefore does not open a second draft", async () => {
    const { impl, drafts } = fakeZenodo();
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

  it("(iii) a pending journal with no recorded id is resolved by marker search", async () => {
    const { impl, drafts } = fakeZenodo();
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

  it("(iv) a vanished recorded draft with a concept DOI REFUSES, creating nothing", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    drafts.clear();
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/manual|permanent|refus/i);
    expect(posts()).toHaveLength(0);
    expect(drafts.size).toBe(0);
  });

  it("(iv) a vanished draft with NO concept DOI is simply cleared", async () => {
    const { impl } = fakeZenodo();
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

  it("publish writes the sidecar BEFORE meta.json", async () => {
    // If the order were reversed, a crash between them would leave meta.json claiming
    // a published DOI that no local record can locate or repair.
    const order: string[] = [];
    const { impl } = fakeZenodo();
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

// ===========================================================================
// MAJOR — a POST is never automatically replayed, 429 included
// ===========================================================================

describe("MAJOR: no automatic replay of a non-idempotent POST", () => {
  function status429(): (u: string, i?: RequestInit) => Promise<Response> {
    return async (url, init) => {
      calls.push({ method: init?.method ?? "GET", url });
      return new Response(JSON.stringify({ message: "rate limited" }), {
        status: 429, headers: { "retry-after": "1" },
      });
    };
  }

  it("does not replay createDraft after 429", async () => {
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: status429(),
      sleep: async () => {}, maxRetries: 4,
    });
    await expect(c.createDraft()).rejects.toBeInstanceOf(ZenodoAmbiguousError);
    expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
  });

  it("does not replay publish or newVersion after 429", async () => {
    for (const op of ["publish", "newVersion"] as const) {
      calls.length = 0;
      const c = new ZenodoClient({
        env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: status429(),
        sleep: async () => {}, maxRetries: 4,
      });
      await expect(c[op](1)).rejects.toBeInstanceOf(ZenodoAmbiguousError);
      expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
    }
  });

  it("tells the operator to re-run, since re-running reconciles", async () => {
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: status429(),
      sleep: async () => {}, maxRetries: 4,
    });
    const msg = await c.createDraft().then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/re-run/i);
  });

  it("still retries idempotent GET on 429", async () => {
    let n = 0;
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n === 1) return new Response("{}", { status: 429, headers: { "retry-after": "1" } });
      return new Response(JSON.stringify({ id: 5, conceptrecid: 4, links: {} }), { status: 200 });
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 3,
    });
    expect((await c.getDeposition(5)).id).toBe(5);
    expect(calls).toHaveLength(2);
  });
});

// ===========================================================================
// MAJOR — exact marker identity
// ===========================================================================

describe("MAJOR: the orphan marker is an exact, collision-free identity", () => {
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
    const { impl, drafts } = fakeZenodo();
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
    const { impl, drafts } = fakeZenodo();
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
});

// ===========================================================================
// MAJOR — a malformed search response must not read as "no orphan"
// ===========================================================================

describe("MAJOR: the draft search fails closed", () => {
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

// ===========================================================================
// MAJOR — sidecar schema is recursive and environment-consistent
// ===========================================================================

describe("MAJOR: the sidecar schema enforces environment consistency", () => {
  const write = (v: unknown) => writeFile(sidecarPath(dir), `${JSON.stringify(v, null, 2)}\n`);
  const good = () => ({
    environment: "sandbox", api_base: SANDBOX.apiBase, conceptrecid: 99,
    concept_doi: "10.5072/zenodo.99", marker: bundleMarker(dir, "sandbox"),
    published: null, draft: null, pending_reserve: null,
    updated_at: "2026-09-21T11:00:00.000Z",
  });

  it("refuses a record whose environment does not match its key", async () => {
    await write({ schema: 2, sandbox: { ...good(), environment: "production" } });
    await expect(readSidecar(dir)).rejects.toThrow(/environment/i);
  });

  it("refuses an api_base that is not that environment's", async () => {
    await write({ schema: 2, sandbox: { ...good(), api_base: "https://zenodo.org/api" } });
    await expect(readSidecar(dir)).rejects.toThrow(/api_base/i);
  });

  it("refuses a concept DOI whose prefix belongs to the other instance", async () => {
    await write({ schema: 2, sandbox: { ...good(), concept_doi: "10.5281/zenodo.99" } });
    await expect(readSidecar(dir)).rejects.toThrow(/prefix|10\.5072/i);
  });

  it("validates nested draft records", async () => {
    await write({ schema: 2, sandbox: { ...good(), draft: {} } });
    await expect(readSidecar(dir)).rejects.toThrow(/draft/i);
  });

  it("validates nested published records", async () => {
    await write({ schema: 2, sandbox: { ...good(), published: { deposition_id: "x" } } });
    await expect(readSidecar(dir)).rejects.toThrow(/published/i);
  });

  it("refuses a concept DOI that disagrees with conceptrecid", async () => {
    await write({ schema: 2, sandbox: { ...good(), concept_doi: "10.5072/zenodo.12345" } });
    await expect(readSidecar(dir)).rejects.toThrow(/conceptrecid|concept_doi/i);
  });

  it("accepts a well-formed record", async () => {
    await write({ schema: 2, sandbox: good() });
    expect((await readSidecar(dir)).sandbox?.concept_doi).toBe("10.5072/zenodo.99");
  });
});

// ===========================================================================
// MAJOR — URLs from responses are never persisted or printed
// ===========================================================================

describe("MAJOR: only locally derived URLs are stored", () => {
  it("ignores a credential-bearing record_html from the response", async () => {
    const { impl: base } = fakeZenodo();
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
});

// ===========================================================================
// MAJOR — error sanitisation covers cause and body reads
// ===========================================================================

describe("MAJOR: no credential escapes through an error cause or a body read", () => {
  it("does not retain an unsanitised cause", async () => {
    const impl = async (): Promise<Response> => {
      const err = new Error("connect failed");
      (err as Error & { cause?: unknown }).cause = new Error(`Bearer ${TOKEN} at https://u:${TOKEN}@h/x`);
      throw err;
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 0,
    });
    const err = await c.createDraft().then(() => null, (e: unknown) => e);
    expect(JSON.stringify(err, Object.getOwnPropertyNames(err))).not.toContain(TOKEN);
    expect((err as { cause?: unknown }).cause).toBeUndefined();
  });

  it("sanitises a failure while reading the response body", async () => {
    const impl = async (): Promise<Response> => ({
      ok: true, status: 200,
      headers: new Headers(),
      text: async () => { throw new Error(`stream aborted: Bearer ${TOKEN}`); },
    } as unknown as Response);
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 0,
    });
    const msg = await c.getDeposition(1).then(() => "", (e: Error) => e.message);
    expect(msg).not.toContain(TOKEN);
  });
});

// ===========================================================================
// MAJOR — font macros keep mathematical identity
// ===========================================================================

describe("MAJOR: font macros are mapped exactly or preserved", () => {
  it("maps blackboard-bold letters that have code points", () => {
    expect(texToPlainText("\\(\\mathbb{R}\\)")).toBe("ℝ");
    expect(texToPlainText("\\(\\mathbb{F}\\)")).toBe("𝔽");
  });

  it("no longer erases a bold/calligraphic distinction", () => {
    expect(texToPlainText("\\(\\mathbf{x}=x\\)")).not.toBe("x=x");
    expect(texToPlainText("\\(\\mathcal{F}=F\\)")).not.toBe("F=F");
  });

  it("maps calligraphic and fraktur exactly", () => {
    expect(texToPlainText("\\(\\mathcal{F}\\)")).toBe("ℱ");
    expect(texToPlainText("\\(\\mathfrak{g}\\)")).toBe("𝔤");
  });

  it("treats \\mathrm and \\operatorname as exact upright text", () => {
    expect(texToPlainText("\\(\\mathrm{Var}\\)")).toBe("Var");
    expect(texToPlainText("\\(\\operatorname{supp}\\)")).toBe("supp");
  });

  it("preserves a font macro whose argument has no exact mapping", () => {
    // No double-struck Greek exists.
    expect(texToHtml("\\(\\mathbb{\\alpha}\\)")).toContain("<code>");
    expect(texToHtml("\\(\\mathcal{+}\\)")).toContain("<code>");
  });
});

// ===========================================================================
// MINOR K — the three test-quality findings
// ===========================================================================

describe("MINOR: the journal is durable BEFORE the create request is sent", () => {
  it("persists pending_reserve to disk before the creation POST leaves", async () => {
    let seenAtPostTime: unknown = "not-observed";
    const { impl } = fakeZenodo({
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
});

// ===========================================================================
// The whole-command lock
// ===========================================================================

describe("the per-bundle command lock serialises whole subcommands", () => {
  it("makes a concurrent reserve wait, then reuse rather than create", async () => {
    let releaseFirst: () => void = () => {};
    const gate = new Promise<void>((r) => { releaseFirst = r; });
    let firstInFlight = false;

    const { impl, drafts } = fakeZenodo({
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
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expect(stat(path.join(dir, ".zenodo.lock"))).resolves.toBeTruthy();
  });

  it("releases the lock when the command throws", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf("an unstamped paper");
    await expect(publish(ctxFor(impl))).rejects.toThrow();
    // A following command must not block.
    await expect(status(ctxFor(impl))).resolves.toBeTruthy();
  }, 30_000);
});

// ===========================================================================
// status --repair
// ===========================================================================

describe("status", () => {
  it("is read-only by default and does not repair", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await status(ctxFor(impl));
    expect((await readSidecar(dir)).sandbox?.published).toBeNull();
  });

  it("repairs with --repair", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const d = drafts.get(id)!;
    drafts.set(id, { ...d, state: "done", submitted: true, conceptdoi: "10.5072/zenodo.99", doi: `10.5072/zenodo.${id}` });
    await status(ctxFor(impl), { repair: true });
    expect((await readSidecar(dir)).sandbox?.published?.deposition_id).toBe(id);
  });
});
