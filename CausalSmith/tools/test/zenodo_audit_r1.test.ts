// Regression tests for the round-1 audit of the Zenodo work package.
//
// Each block names the finding it pins. They are written against the BEHAVIOUR that
// must hold, not against the implementation that happened to be there, so they read
// as the specification of the guard rather than as a change detector.
//
// The audit's own summary of why this file exists: "the current `unavailable` bypass
// and the `.99` versus `.999` bug both survive all 73 passing tests". Every finding
// below was reproduced as a failing test before it was fixed.

import { describe, it, expect, beforeEach } from "vitest";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { SANDBOX, ZenodoClient, ZenodoError, ZenodoAmbiguousError } from "../src/zenodo/client.js";
import { abandon, newVersion, publish, reserve, status, type DepositContext } from "../src/zenodo/deposit.js";
import { bundleMarker, readSidecar } from "../src/zenodo/bundle.js";
import { pdfContainsDoi, pdfPage1ContainsDoi } from "../src/zenodo/pdf_text.js";
import { texToHtml, texToPlainText } from "../src/zenodo/metadata.js";
import { emptyPdf, minimalPdf, multiPagePdf, notAPdf, unreadablePdf } from "./zenodo_fixtures.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";

const META = {
  qid: "stat_demo",
  spec: "spec",
  title: "A demo paper",
  tldr: "a tldr that must survive untouched",
  abstract: "An abstract with \\(\\epsilon\\) in it.",
  area: "Stat",
  created: "2026-07-21",
  wp_number: "CSWP-2026-008",
  version: 1,
  revised: "2026-07-21",
  score: 8,
};

let dir: string;
let calls: { method: string; url: string; body?: string }[];
let logs: string[];
let warns: string[];

beforeEach(async () => {
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-audit-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = [];
  logs = [];
  warns = [];
});

// ---------------------------------------------------------------------------
// A fake Zenodo with the marker-search endpoint the adoption path needs.
// ---------------------------------------------------------------------------

function fakeZenodo(opts: { conceptrecid?: number; nextId?: number } = {}) {
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = opts.nextId ?? 100;
  const conceptrecid = opts.conceptrecid ?? 99;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;

  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url, body });
    const json = (status: number, value: unknown) => new Response(JSON.stringify(value), { status });
    const u = new URL(url);

    // The deposit listing: only ever consulted with status=draft + a marker query.
    if (method === "GET" && u.pathname.endsWith("/deposit/depositions") && u.search) {
      const q = u.searchParams.get("q") ?? "";
      const marker = q.replace(/^"|"$/g, "");
      const rows = [...drafts.values()].filter(
        (d) => d.submitted === false &&
          String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "").includes(marker),
      );
      return json(200, rows);
    }
    if (method === "POST" && u.pathname.endsWith("/deposit/depositions")) {
      const id = nextId++;
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
        conceptdoi: `10.5072/zenodo.${conceptrecid}`, doi: `10.5072/zenodo.${id}`,
        links: { ...(dep.links as object), record_html: `https://sandbox.zenodo.org/records/${id}` },
      };
      drafts.set(id, published);
      return json(202, published);
    }
    const nv = /\/deposit\/depositions\/(\d+)\/actions\/newversion$/.exec(u.pathname);
    if (method === "POST" && nv) {
      const id = nextId++;
      const parent = drafts.get(Number(nv[1]))!;
      drafts.set(id, {
        id, conceptrecid, conceptdoi: `10.5072/zenodo.${conceptrecid}`,
        state: "unsubmitted", submitted: false,
        metadata: { ...(parent.metadata as object) },
        links: { bucket: bucketOf(id) },
        files: [{ id: "inherited", filename: "paper.pdf" }],
      });
      return json(201, { id: Number(nv[1]), links: { latest_draft: `https://sandbox.zenodo.org/api/deposit/depositions/${id}` } });
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
      return json(201, { key: u.pathname.split("/").pop(), size: 10, checksum: "md5:fake", version_id: "v1" });
    }
    return json(500, { message: `unrouted ${method} ${u.pathname}` });
  };
  return { impl, drafts };
}

function ctxFor(
  impl: (url: string, init?: RequestInit) => Promise<Response>,
  over: Partial<DepositContext> & { dryRun?: boolean; clientOpts?: Record<string, unknown> } = {},
): DepositContext {
  const { dryRun, clientOpts, ...rest } = over;
  return {
    bundleDir: dir,
    client: new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl,
      sleep: async () => {}, maxRetries: 1, dryRun, ...clientOpts,
    }),
    writeMeta: false,
    allowUnstamped: false,
    siteBaseUrl: "https://causalsmith.org",
    repoUrl: "https://github.com/Jiyuan-Tan/CausalSmith",
    titlePrefix: "[TEST] ",
    log: (l) => logs.push(l),
    warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...rest,
  };
}

const meta = async () => JSON.parse(await readFile(path.join(dir, "meta.json"), "utf8"));
const pdf = (buf: Buffer) => writeFile(path.join(dir, "paper.pdf"), buf);

// ---------------------------------------------------------------------------
// BLOCKER 2 — pdf_text.ts: substring matching let a longer DOI satisfy the guard
// ---------------------------------------------------------------------------

describe("BLOCKER: DOI matching needs token boundaries", () => {
  let p: string;
  beforeEach(() => { p = path.join(dir, "paper.pdf"); });

  it("does not accept a LONGER DOI that merely starts with the expected one", async () => {
    await writeFile(p, minimalPdf("doi:10.5072/zenodo.999"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("absent");
  });

  it("does not accept a longer DOI whose extra digit was split off by the extractor", async () => {
    await writeFile(p, minimalPdf("doi:10.5072/zenodo.9 9 9"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("absent");
  });

  it("does not accept a DOI that is a suffix of a longer number", async () => {
    await writeFile(p, minimalPdf("doi:110.5072/zenodo.99"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("absent");
  });

  it("still accepts the exact DOI", async () => {
    await writeFile(p, minimalPdf("doi:10.5072/zenodo.99"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("present");
  });

  it("accepts the exact DOI followed by an unrelated number", async () => {
    await writeFile(p, minimalPdf("doi:10.5072/zenodo.99 Page 123"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("present");
  });

  it("accepts a DOI whose PREFIX the extractor spaced out glyph by glyph", async () => {
    // The record id's own digits must stay contiguous — see zenodo_audit_r4.
    await writeFile(p, minimalPdf("d o i : 1 0 . 5 0 7 2 / z e n o d o . 99"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("present");
  });

  it("accepts the longer DOI when the longer DOI is what we asked for", async () => {
    await writeFile(p, minimalPdf("doi:10.5072/zenodo.999"));
    expect((await pdfContainsDoi(p, "10.5072/zenodo.999")).outcome).toBe("present");
  });
});

describe("StampCheck reports every outcome distinctly", () => {
  it("reports `absent` for a readable PDF without the DOI", async () => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, minimalPdf("a paper with no stamp"));
    const r = await pdfContainsDoi(p, "10.5072/zenodo.99");
    expect(r.outcome).toBe("absent");
    expect(r).toHaveProperty("method");
  });

  it("reports `unavailable` for an empty file", async () => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, emptyPdf());
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("unavailable");
  });

  it("reports `unavailable` for a %PDF file with no readable text layer", async () => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, unreadablePdf());
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("unavailable");
  });

  it("reports `unavailable` for a file that is not a PDF, even if it contains the DOI", async () => {
    // A LaTeX failure can leave something else at paper.pdf. Text that happens to hold
    // the DOI must not be read as a stamped paper.
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, notAPdf());
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("unavailable");
  });

  it("reports `unavailable` for a missing file", async () => {
    expect((await pdfContainsDoi(path.join(dir, "nope.pdf"), "10.5072/zenodo.99")).outcome)
      .toBe("unavailable");
  });
});

// ---------------------------------------------------------------------------
// BLOCKER 1 — deposit.ts: `unavailable` must refuse, not warn and continue
// ---------------------------------------------------------------------------

describe("BLOCKER: publish refuses when the stamp cannot be verified", () => {
  it("refuses when extraction fails, rather than warning and publishing", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(unreadablePdf());
    await expect(publish(ctxFor(impl))).rejects.toThrow(/could not be (read|verified)|unreadable/i);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("uses a DIFFERENT message for unverifiable than for absent", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(unreadablePdf());
    const unreadable = await publish(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    await pdf(minimalPdf("no stamp here"));
    const absent = await publish(ctxFor(impl)).then(() => "", (e: Error) => e.message);
    expect(unreadable).not.toBe(absent);
    expect(absent).toMatch(/does not contain/i);
  });

  it("still lets --allow-unstamped through for an unverifiable PDF", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(unreadablePdf());
    await expect(publish(ctxFor(impl, { allowUnstamped: true }))).resolves.toBeTruthy();
    expect(warns.join("\n")).toMatch(/!!/);
  });
});

// ---------------------------------------------------------------------------
// The publish gate asks about PAGE 1, because that is the only page the stamp is on
// ---------------------------------------------------------------------------

describe("the stamp gate looks at page 1, not at the whole document", () => {
  const DOI = "10.5072/zenodo.99";

  it("refuses a PDF whose only mention of the DOI is on page 5", async () => {
    // A related-work citation, an acknowledgement or a bibliography entry can perfectly well
    // name this concept DOI — it is the paper's own, and P5 or the author may cite the record.
    // Whole-document matching read that as a stamp and published a paper whose page 1 prints
    // nothing, which is precisely the permanently-wrong artefact this gate exists to prevent.
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(multiPagePdf(["Title page, unstamped.", "two", "three", "four", `See doi:${DOI}`]));
    await expect(publish(ctxFor(impl))).rejects.toThrow(/does not contain/i);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("accepts the same DOI when it IS on page 1", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(multiPagePdf([`Title page. doi:${DOI} [Stat]`, "two", "three", "four", "five"]));
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
  });

  it("says so in `method` when it had to fall back to the whole document", async () => {
    // No page splitter can read this, so the check answers the weaker question rather than
    // refusing outright — and labels which question it answered.
    const p = path.join(dir, "not-a-real-pdf.pdf");
    await writeFile(p, notAPdf());
    const check = await pdfPage1ContainsDoi(p, DOI);
    expect(check.outcome).toBe("unavailable");
    const one = path.join(dir, "one-page.pdf");
    await writeFile(one, minimalPdf(`doi:${DOI} ·`));
    const good = await pdfPage1ContainsDoi(one, DOI);
    expect(good.outcome).toBe("present");
    if (good.outcome !== "present") return;
    expect(good.method).toMatch(/page 1|WHOLE DOCUMENT/);
  });
});

// ---------------------------------------------------------------------------
// BLOCKER 3 — abandon must not destroy the published record or the concept DOI
// ---------------------------------------------------------------------------

describe("BLOCKER: abandoning a revision preserves the published version", () => {
  async function publishV1(impl: (u: string, i?: RequestInit) => Promise<Response>) {
    await reserve(ctxFor(impl, { writeMeta: true }));
    await pdf(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl, { writeMeta: true }));
  }

  it("keeps the published record and the concept DOI when a v2 draft is abandoned", async () => {
    const { impl } = fakeZenodo();
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
    const { impl } = fakeZenodo();
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
    const { impl } = fakeZenodo();
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2, doi: "10.5072/zenodo.99" }, null, 2)}\n`);
    await newVersion(ctxFor(impl, { writeMeta: true }));
    await abandon(ctxFor(impl, { writeMeta: true }));
    expect((await meta()).doi).toBe("10.5072/zenodo.99");
  });
});

// ---------------------------------------------------------------------------
// MAJOR — non-idempotent requests are never blindly replayed
// ---------------------------------------------------------------------------

describe("MAJOR: POST is never blindly replayed", () => {
  function flaky(failures: number, status: number | "network") {
    let n = 0;
    return async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n <= failures) {
        if (status === "network") throw new Error("ECONNRESET");
        return new Response(JSON.stringify({ message: "upstream" }), { status });
      }
      return new Response(JSON.stringify({ id: 100, conceptrecid: 99, links: { bucket: "b" } }), { status: 201 });
    };
  }

  it("does not retry a draft creation after a network error", async () => {
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: flaky(1, "network"),
      sleep: async () => {}, maxRetries: 3,
    });
    await expect(c.createDraft()).rejects.toBeInstanceOf(ZenodoAmbiguousError);
    expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
  });

  it("does not retry a draft creation after a 5xx", async () => {
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: flaky(1, 503),
      sleep: async () => {}, maxRetries: 3,
    });
    await expect(c.createDraft()).rejects.toBeInstanceOf(ZenodoAmbiguousError);
    expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
  });

  it("does not retry publish or newversion after a 5xx", async () => {
    for (const op of ["publish", "newVersion"] as const) {
      calls.length = 0;
      const c = new ZenodoClient({
        env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: flaky(1, 503),
        sleep: async () => {}, maxRetries: 3,
      });
      await expect(c[op](1)).rejects.toBeInstanceOf(ZenodoAmbiguousError);
      expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
    }
  });

  it("DOES retry idempotent GET/PUT/DELETE", async () => {
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: flaky(1, 503),
      sleep: async () => {}, maxRetries: 3,
    });
    await expect(c.getDeposition(100)).resolves.toBeTruthy();
    expect(calls.filter((x) => x.method === "GET")).toHaveLength(2);
  });

  it("does not retry a POST on 429 either — see zenodo_audit_r2", async () => {
    // This test previously asserted the OPPOSITE, and so codified the very replay it
    // was meant to guard. A 429 says a rate limiter refused the request; it does not
    // say which layer refused it, and a proxy can rate-limit a call an upstream
    // already performed.
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      return new Response("{}", { status: 429, headers: { "retry-after": "1" } });
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 3,
    });
    await expect(c.createDraft()).rejects.toBeInstanceOf(ZenodoAmbiguousError);
    expect(calls).toHaveLength(1);
  });
});

// ---------------------------------------------------------------------------
// MAJOR — the reserve crash gap: adopt the orphan, never mint a second DOI
// ---------------------------------------------------------------------------

describe("MAJOR: a crash between draft creation and sidecar write is recoverable", () => {
  it("adopts the orphaned draft instead of creating a second one", async () => {
    const { impl, drafts } = fakeZenodo();
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
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    const s = await readSidecar(dir);
    expect(s.sandbox?.marker).toBe(bundleMarker(dir, "sandbox"));
    expect(s.sandbox?.marker).not.toContain("stat_demo_spec");
  });

  it("tags the created draft with the bundle marker so it is findable", async () => {
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const created = [...drafts.values()][0];
    const notes = String((created.metadata as Record<string, unknown>).notes ?? "");
    expect(notes.split("\n").some((l) => l.trim() === bundleMarker(dir, "sandbox"))).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// MAJOR — sidecar read failures must be loud
// ---------------------------------------------------------------------------

describe("MAJOR: the sidecar fails loudly rather than looking absent", () => {
  it("treats a JSON array as corruption, not as 'no sidecar'", async () => {
    await writeFile(path.join(dir, "zenodo.json"), "[]\n");
    await expect(readSidecar(dir)).rejects.toThrow(/object|schema|corrupt/i);
  });

  it("treats malformed JSON as corruption", async () => {
    await writeFile(path.join(dir, "zenodo.json"), "{not json\n");
    await expect(readSidecar(dir)).rejects.toThrow();
  });

  it("treats a schema-invalid environment record as corruption", async () => {
    await writeFile(path.join(dir, "zenodo.json"), `${JSON.stringify({ sandbox: { nonsense: true } })}\n`);
    await expect(readSidecar(dir)).rejects.toThrow();
  });

  it("returns {} only when the file does not exist", async () => {
    expect(await readSidecar(dir)).toEqual({});
  });

  it("does not create a duplicate deposit when the sidecar is corrupt", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writeFile(path.join(dir, "zenodo.json"), "[]\n");
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(calls.filter((c) => c.method === "POST")).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// MAJOR — redirects must not carry an authenticated request to production
// ---------------------------------------------------------------------------

describe("MAJOR: cross-instance redirects are refused", () => {
  it("does not follow a redirect to production", async () => {
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      expect(init?.redirect).toBe("manual");
      return new Response(null, { status: 302, headers: { location: "https://zenodo.org/api/deposit/depositions/1" } });
    };
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.getDeposition(1)).rejects.toThrow(/redirect|zenodo\.org/i);
    expect(calls).toHaveLength(1);
  });

  it("follows a same-origin redirect", async () => {
    let n = 0;
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n === 1) {
        return new Response(null, { status: 302, headers: { location: "https://sandbox.zenodo.org/api/deposit/depositions/2" } });
      }
      return new Response(JSON.stringify({ id: 2, conceptrecid: 1, links: {} }), { status: 200 });
    };
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    expect((await c.getDeposition(1)).id).toBe(2);
    expect(calls).toHaveLength(2);
  });
});

// ---------------------------------------------------------------------------
// MAJOR — logging must not carry credentials in a URL
// ---------------------------------------------------------------------------

describe("MAJOR: URLs are logged without credentials", () => {
  it("never logs a query string, even under an unrecognised parameter name", async () => {
    const log: string[] = [];
    const impl = async (): Promise<Response> =>
      new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: {} }), { status: 200 });
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, log: (l) => log.push(l),
    });
    await c.getByUrl(`https://sandbox.zenodo.org/api/deposit/depositions/1?token=${TOKEN}&secret=${TOKEN}`);
    const all = [...log, ...c.requestLog].join("\n");
    expect(all).not.toContain(TOKEN);
    expect(all).not.toContain("token=");
    expect(all).not.toContain("?");
  });

  it("never logs URL userinfo", async () => {
    const log: string[] = [];
    const impl = async (): Promise<Response> =>
      new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: {} }), { status: 200 });
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, log: (l) => log.push(l),
    });
    await c.getByUrl(`https://user:${TOKEN}@sandbox.zenodo.org/api/deposit/depositions/1`).catch(() => {});
    const all = [...log, ...c.requestLog].join("\n");
    expect(all).not.toContain(TOKEN);
    expect(all).not.toContain("@sandbox");
  });
});

// ---------------------------------------------------------------------------
// MAJOR — a 2xx with an unusable body is a hard error on a real mutation
// ---------------------------------------------------------------------------

describe("MAJOR: successful responses are validated, never stubbed", () => {
  it("rejects a 201 with an empty body instead of inventing record 0", async () => {
    const impl = async (): Promise<Response> => new Response("", { status: 201 });
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.createDraft()).rejects.toThrow(/empty|body|malformed|invalid/i);
  });

  it("rejects a 201 whose JSON lacks a numeric id", async () => {
    const impl = async (): Promise<Response> => new Response(JSON.stringify({ conceptrecid: 9 }), { status: 201 });
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.createDraft()).rejects.toThrow(/id/i);
  });

  it("rejects a draft with no conceptrecid rather than deriving 10.5072/zenodo.0", async () => {
    const impl = async (): Promise<Response> => new Response(JSON.stringify({ id: 5 }), { status: 201 });
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.createDraft()).rejects.toThrow(/conceptrecid/i);
  });

  it("never records a DOI built from a zero record id", async () => {
    // An unusable body now stops the run at the marker search, before anything is
    // journaled or created — a stricter outcome than the earlier "journal then fail".
    const impl = async (): Promise<Response> => new Response("", { status: 201 });
    await expect(reserve(ctxFor(impl))).rejects.toThrow();
    expect(JSON.stringify(await readSidecar(dir))).not.toContain("zenodo.0");
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
});

// ---------------------------------------------------------------------------
// MAJOR — DOIs are derived locally; API values are assertions only
// ---------------------------------------------------------------------------

describe("MAJOR: locally derived DOIs are authoritative", () => {
  it("fails and persists nothing when the API reports a different concept DOI", async () => {
    const { impl: base } = fakeZenodo();
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
    await pdf(minimalPdf("doi:10.5072/zenodo.99"));
    await expect(publish(ctxFor(impl, { writeMeta: true }))).rejects.toThrow(/mismatch|concept/i);

    const s = await readSidecar(dir);
    expect(s.sandbox?.concept_doi).toBe("10.5072/zenodo.99");
    expect(JSON.stringify(s)).not.toContain("424242");
    expect(JSON.stringify(await meta())).not.toContain("424242");
  });

  it("fails when the API reports a different version DOI", async () => {
    const { impl: base } = fakeZenodo();
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      const res = await base(url, init);
      if ((init?.method ?? "GET") === "POST" && url.includes("/actions/publish")) {
        const body = await res.json() as Record<string, unknown>;
        return new Response(JSON.stringify({ ...body, doi: "10.5072/zenodo.777777" }), { status: 202 });
      }
      return res;
    };
    await reserve(ctxFor(impl));
    await pdf(minimalPdf("doi:10.5072/zenodo.99"));
    await expect(publish(ctxFor(impl))).rejects.toThrow(/mismatch|doi/i);
    expect(JSON.stringify(await readSidecar(dir))).not.toContain("777777");
  });
});

// ---------------------------------------------------------------------------
// MAJOR — new-version requires demonstrated version advance
// ---------------------------------------------------------------------------

describe("MAJOR: new-version requires a real version advance", () => {
  async function publishV1(impl: (u: string, i?: RequestInit) => Promise<Response>, m: object = META) {
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(m, null, 2)}\n`);
    await reserve(ctxFor(impl));
    await pdf(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl));
  }

  it("refuses when meta.version is missing", async () => {
    const { version: _v, ...noVersion } = META;
    const { impl } = fakeZenodo();
    await publishV1(impl, noVersion);
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/version/i);
  });

  it("refuses when meta.version is not an integer", async () => {
    const { impl } = fakeZenodo();
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: "2" }, null, 2)}\n`);
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/version/i);
  });

  it("refuses --force when there is no published record at all", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expect(newVersion(ctxFor(impl), { force: true })).rejects.toThrow();
  });

  it("allows a genuine advance", async () => {
    const { impl } = fakeZenodo();
    await publishV1(impl);
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await expect(newVersion(ctxFor(impl))).resolves.toBeTruthy();
  });
});

// ---------------------------------------------------------------------------
// MAJOR — TeX conversion fails closed
// ---------------------------------------------------------------------------

describe("MAJOR: unsupported TeX is preserved visibly, never guessed", () => {
  it("preserves an unknown macro as its source rather than dropping the backslash", async () => {
    expect(texToHtml("\\(\\foo{y}\\)")).toContain("<code>\\foo{y}</code>");
    expect(texToPlainText("\\(\\foo{y}\\)")).toContain("\\foo{y}");
    expect(texToPlainText("\\(\\foo{y}\\)")).not.toBe("fooy");
  });

  it("preserves an optional argument rather than silently reinterpreting it", async () => {
    expect(texToHtml("\\(\\sqrt[3]{x}\\)")).toContain("<code>\\sqrt[3]{x}</code>");
    expect(texToHtml("\\(\\sqrt[3]{x}\\)")).not.toContain("√[3]");
  });

  it("parenthesizes a fraction whenever either side is more than one token", () => {
    expect(texToPlainText("\\(\\frac{ab}{cd}\\)")).toBe("(ab)/(cd)");
    expect(texToPlainText("\\(\\frac{a+b}{c}\\)")).toBe("(a+b)/c");
    expect(texToPlainText("\\(\\frac1n\\)")).toBe("1/n");
  });

  it("still converts everything it does support", () => {
    expect(texToPlainText("\\(\\epsilon\\in(0,1/2)\\)")).toBe("\u03f5 ∈ (0,1/2)");
    expect(texToPlainText("\\(\\sqrt{n}\\)")).toBe("√n");
  });

  it("treats a bracket after \\left as a delimiter, not an optional argument", () => {
    // `\left[x\right]` is ordinary mathematics; an earlier optional-argument check
    // preserved it as unreadable source across five of the real bundles.
    expect(texToPlainText("\\(\\left[x\\right]\\)")).toBe("[x]");
    expect(texToHtml("\\(\\left[x\\right]\\)")).not.toContain("<code>");
  });

  it("renders the infix \\over fraction, which divides its enclosing group", () => {
    expect(texToPlainText("\\({\\log n\\over n}\\)")).toBe("(log n)/n");
  });

  it("renders \\binom unambiguously", () => {
    expect(texToPlainText("\\(\\binom{n}{k}\\)")).toBe("C(n, k)");
  });

  it("preserves a whole environment, never just its \\begin token", () => {
    // Converting the BODY while preserving only the delimiters would flatten `&` and
    // `\\` into spaces and silently turn a piecewise definition into one expression.
    const html = texToHtml("\\(\\begin{cases} 0,&a=0,\\\\ 1,&a>0. \\end{cases}\\)");
    const codes = [...html.matchAll(/<code>([\s\S]*?)<\/code>/g)].map((m) => m[1]);
    expect(codes).toHaveLength(1);
    expect(codes[0]).toContain("\\begin{cases}");
    expect(codes[0]).toContain("\\end{cases}");
    expect(codes[0]).toContain("a=0");
  });

  it("maps font macros to their exact Unicode forms rather than erasing them", () => {
    // This previously expected "AB" — i.e. the distinction silently dropped.
    expect(texToPlainText("\\(\\mathsf{A}\\mathfrak{B}\\)")).toBe("\u{1D5A0}\u{1D505}");
    expect(texToPlainText("\\(\\mathbb{R}\\)")).toBe("ℝ");
  });
});

// ---------------------------------------------------------------------------
// MINOR — mismatch test must assert nothing wrong was persisted (covered above)
// and status keeps working across the new sidecar shape
// ---------------------------------------------------------------------------

describe("status reflects published and draft state separately", () => {
  it("reports both a published version and an open revision draft", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await pdf(minimalPdf("doi:10.5072/zenodo.99"));
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    const s = await status(ctxFor(impl));
    expect(s.record?.published?.deposition_id).toBe(100);
    expect(s.record?.draft?.deposition_id).toBe(101);
    expect(s.record?.concept_doi).toBe("10.5072/zenodo.99");
  });
});
