// Shared fixtures for the Zenodo suites: real (tiny) PDFs for the stamp guard, and one
// fake Zenodo + deposit context for every suite that drives the deposit logic.
//
// Real (tiny) PDF fixtures for the stamp guard.
//
// The first round of these tests wrote plain text into `paper.pdf`. That is not a PDF,
// so it exercised none of the real extraction path — and both the `unavailable`
// bypass and the `.99` matching `.999` bug survived a fully green suite. These build
// an actual, structurally valid PDF (correct xref offsets, uncompressed content
// stream) so `pdftotext`/`ghostscript`/the zlib fallback all have something genuine to
// read, whichever one the host happens to have.

import { beforeEach } from "vitest";
import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { SANDBOX, ZenodoClient, type ZenodoEnvironment } from "../src/zenodo/client.js";
import { bundleMarker } from "../src/zenodo/bundle.js";
import type { DepositContext } from "../src/zenodo/deposit.js";

/** A minimal one-page PDF whose page shows `text`, with a correct xref table.
 *
 *  The content stream is deliberately UNCOMPRESSED: it keeps the fixture readable in a
 *  hex dump when a test fails, and it means the dependency-free fallback extractor has
 *  the same text available as poppler would. */
export function minimalPdf(text: string): Buffer {
  const escaped = text.replace(/\\/g, "\\\\").replace(/\(/g, "\\(").replace(/\)/g, "\\)");
  const stream = `BT /F1 12 Tf 40 700 Td (${escaped}) Tj ET\n`;
  const objects = [
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R " +
      "/Resources << /Font << /F1 5 0 R >> >> >>",
    `<< /Length ${stream.length} >>\nstream\n${stream}endstream`,
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
  ];

  let body = "%PDF-1.4\n";
  const offsets: number[] = [];
  objects.forEach((obj, i) => {
    offsets.push(Buffer.byteLength(body, "latin1"));
    body += `${i + 1} 0 obj\n${obj}\nendobj\n`;
  });

  const xrefAt = Buffer.byteLength(body, "latin1");
  let xref = `xref\n0 ${objects.length + 1}\n0000000000 65535 f \n`;
  for (const off of offsets) xref += `${String(off).padStart(10, "0")} 00000 n \n`;
  const trailer =
    `trailer\n<< /Size ${objects.length + 1} /Root 1 0 R >>\nstartxref\n${xrefAt}\n%%EOF\n`;

  return Buffer.from(body + xref + trailer, "latin1");
}

/**
 * A multi-page PDF, one `pages[i]` string shown per page, with a correct xref table.
 *
 * The restamp verifier's whole job is a PER-PAGE comparison — page 1 gained the stamp, pages
 * 2..N are unchanged — so a one-page fixture cannot exercise it at all. `trailer` is appended
 * verbatim after `%%EOF`, which is how a test makes two compiles of the same document differ in
 * BYTES while being identical as text: exactly the situation the copy-back skip exists for.
 */
export function multiPagePdf(pages: readonly string[], trailer = ""): Buffer {
  const esc = (t: string) => t.replace(/\\/g, "\\\\").replace(/\(/g, "\\(").replace(/\)/g, "\\)");
  const streams = pages.map((t) => `BT /F1 12 Tf 40 700 Td (${esc(t)}) Tj ET\n`);
  // 1 catalog, 2 pages, 3 font, then per page: a /Page and its content stream.
  const firstPageObj = 4;
  const kids = pages.map((_, i) => `${firstPageObj + i * 2} 0 R`).join(" ");
  const objects = [
    "<< /Type /Catalog /Pages 2 0 R >>",
    `<< /Type /Pages /Kids [${kids}] /Count ${pages.length} >>`,
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
  ];
  streams.forEach((stream, i) => {
    objects.push(
      `<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents ${firstPageObj + i * 2 + 1} 0 R ` +
        "/Resources << /Font << /F1 3 0 R >> >> >>",
      `<< /Length ${stream.length} >>\nstream\n${stream}endstream`,
    );
  });

  let body = "%PDF-1.4\n";
  const offsets: number[] = [];
  objects.forEach((obj, i) => {
    offsets.push(Buffer.byteLength(body, "latin1"));
    body += `${i + 1} 0 obj\n${obj}\nendobj\n`;
  });
  const xrefAt = Buffer.byteLength(body, "latin1");
  let xref = `xref\n0 ${objects.length + 1}\n0000000000 65535 f \n`;
  for (const off of offsets) xref += `${String(off).padStart(10, "0")} 00000 n \n`;
  const tail =
    `trailer\n<< /Size ${objects.length + 1} /Root 1 0 R >>\nstartxref\n${xrefAt}\n%%EOF\n${trailer}`;
  return Buffer.from(body + xref + tail, "latin1");
}

/**
 * The per-page text of a {@link multiPagePdf} (or a {@link minimalPdf}), recovered from the
 * uncompressed text-showing operators in document order.
 *
 * A deliberate TEST DOUBLE for `extractPdfPages`: it reads real PDF bytes, so the fixture is
 * genuinely a PDF, while keeping the suite independent of whether PyMuPDF or ghostscript happens
 * to be installed on the host running it.
 */
export function pdfPageTexts(bytes: Buffer): string[] {
  const raw = bytes.toString("latin1");
  return [...raw.matchAll(/\(((?:[^()\\]|\\.)*)\)\s*Tj/g)].map((m) =>
    m[1].replace(/\\([\\()])/g, "$1"),
  );
}

/** A file that starts like a PDF but whose body is unreadable garbage — the
 *  "extraction genuinely failed" case, as distinct from "the DOI is not there". */
export function unreadablePdf(): Buffer {
  return Buffer.concat([
    Buffer.from("%PDF-1.4\n", "latin1"),
    Buffer.from(Array.from({ length: 512 }, (_, i) => (i * 37 + 11) % 256)),
  ]);
}

/** Zero bytes. */
export function emptyPdf(): Buffer {
  return Buffer.alloc(0);
}

/** Bytes that are not a PDF at all — e.g. a LaTeX error left a log file in place. */
export function notAPdf(): Buffer {
  return Buffer.from("This is not a PDF. doi:10.5072/zenodo.99\n", "utf8");
}

// ---------------------------------------------------------------------------
// A temp bundle, a fake Zenodo and a deposit context
// ---------------------------------------------------------------------------

/** A token-shaped string. Suites assert it never reaches a log line, an error or a file. */
export const TEST_TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";

/** The `meta.json` every temp bundle starts from. It carries keys a deposit must leave
 *  untouched (`tldr`, `authorship`, `score_rationale`) and TeX in the abstract. */
export const DEMO_META = {
  qid: "stat_demo",
  spec: "spec",
  title: "A demo paper",
  tldr: "a tldr that must survive untouched",
  abstract: "An abstract with \\(\\epsilon\\) in it.",
  area: "Stat",
  authorship: null,
  created: "2026-07-21",
  wp_number: "CSWP-2026-008",
  version: 1,
  revised: "2026-07-21",
  score: 8,
  score_rationale: "unchanged by a deposit",
};

/** A fresh temp bundle holding {@link DEMO_META}. The bundle DIRECTORY NAME is the site's
 *  paper id (and feeds the bundle marker), so it is named like a real one rather than being
 *  the mkdtemp root. */
export async function makeBundleDir(meta: object = DEMO_META): Promise<string> {
  const dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-bundle-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`, "utf8");
  return dir;
}

export interface FakeCall { method: string; url: string; body?: string }
export type FetchImpl = (url: string, init?: RequestInit) => Promise<Response>;

/** What one test sees: its bundle, every request the fake received, and what was logged. */
export interface ZenodoHarness {
  dir: string;
  calls: FakeCall[];
  logs: string[];
  warns: string[];
}

/**
 * How the fake Zenodo behaves. Every field below is a point where real Zenodo's behaviour is
 * either instance-dependent or was modelled in more than one way; the default is the model
 * closest to what was probed on the sandbox, and a test written against another model names it.
 */
export interface FakeZenodoOptions {
  /** Pre-seeded records. */
  drafts?: Map<number, Record<string, unknown>>;
  /** Id of the first created deposition (default 100). */
  nextId?: number;
  /** conceptrecid of the first created deposition (default 99). */
  conceptrecid?: number;
  /** Called after a request is recorded and before it is routed; may throw, or return a
   *  Response to pre-empt the route. */
  before?: (method: string, url: string) => Promise<Response | void>;
  /** The marker search always answers `[]`, as a lagging search index would. */
  hideFromSearch?: boolean;
  /** How the marker search matches `metadata.notes`: `"line"` (default) returns only drafts
   *  carrying the marker as a whole line; `"substring"` returns any draft whose notes contain
   *  it, leaving exactness entirely to the code under test. */
  search?: "line" | "substring";
  /** `"fresh"` (default): every created deposition gets its own conceptrecid, as real Zenodo
   *  does — which is exactly why a duplicate reserve is dangerous. `"shared"`: every creation
   *  reuses the first one. */
  conceptPerCreation?: "fresh" | "shared";
  /** Where publish and new-version take the concept from: `"record"` (default) reads it off
   *  the stored record; `"fake"` uses the fake's current creation counter. The two agree
   *  unless a second deposition was created in between. */
  conceptSource?: "record" | "fake";
  /** `"parent-linked"` (default): new-version records `links.latest_draft` on the published
   *  parent, so a later GET of the parent shows the open draft. `"response-only"`: the link
   *  appears in the new-version response alone, and the new draft carries a `conceptdoi`. */
  newVersion?: "parent-linked" | "response-only";
  /** Status of a DELETE for a draft that is not there: 404 (default, as probed) or 204. */
  deleteOfMissing?: 404 | 204;
  /** A metadata PUT merges into the stored metadata (default) or replaces it. */
  metadataPut?: "merge" | "replace";
}

/** DELETE is 204 whether or not the draft exists. */
export const FAKE_DELETE_ALWAYS_204 = { deleteOfMissing: 204 } as const satisfies FakeZenodoOptions;

/** The simplest model: one conceptrecid for every creation, a substring marker search, a
 *  new-version link that exists only in its own response, and a DELETE that is always 204. */
export const FAKE_ONE_SHARED_CONCEPT = {
  search: "substring", conceptPerCreation: "shared", conceptSource: "fake",
  newVersion: "response-only", deleteOfMissing: 204,
} as const satisfies FakeZenodoOptions;

/** A fresh conceptrecid per creation, with a substring marker search, a response-only
 *  new-version link, a DELETE that is always 204, and a metadata PUT that REPLACES. */
export const FAKE_METADATA_REPLACED = {
  search: "substring", conceptSource: "fake", newVersion: "response-only",
  deleteOfMissing: 204, metadataPut: "replace",
} as const satisfies FakeZenodoOptions;

/** A fake Zenodo: routes by method + URL shape and keeps the records it was asked to make,
 *  so one handler serves reserve, publish, new-version and abandon in a single test. */
export function makeFakeZenodo(h: ZenodoHarness, opts: FakeZenodoOptions = {}): {
  impl: FetchImpl;
  drafts: Map<number, Record<string, unknown>>;
  /** This bundle's sandbox marker. */
  marker: () => string;
} {
  const drafts = opts.drafts ?? new Map<number, Record<string, unknown>>();
  let nextId = opts.nextId ?? 100;
  const baseConcept = opts.conceptrecid ?? 99;
  let creations = 0;
  let conceptrecid = baseConcept;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;
  const draftUrl = (id: number) => `https://sandbox.zenodo.org/api/deposit/depositions/${id}`;
  const gone = { message: "The persistent identifier does not exist." };

  const impl: FetchImpl = async (url, init) => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    h.calls.push({ method, url, body });
    if (opts.before) {
      const pre = await opts.before(method, url);
      if (pre) return pre;
    }
    const json = (status: number, value: unknown) => new Response(JSON.stringify(value), { status });
    const u = new URL(url);

    // The marker search `reserve` uses to find an orphaned draft before creating one.
    if (method === "GET" && u.pathname.endsWith("/deposit/depositions") && u.search) {
      if (opts.hideFromSearch) return json(200, []);
      const q = decodeURIComponent(u.searchParams.get("q") ?? "").replace(/^"|"$/g, "");
      return json(200, [...drafts.values()].filter((d) => {
        if (d.submitted !== false) return false;
        const notes = String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "");
        return opts.search === "substring"
          ? notes.includes(q)
          : notes.split("\n").some((l) => l.trim() === q);
      }));
    }
    if (method === "POST" && u.pathname.endsWith("/deposit/depositions")) {
      const id = nextId++;
      creations += 1;
      if (creations > 1 && opts.conceptPerCreation !== "shared") {
        conceptrecid = baseConcept + 1000 * (creations - 1);
      }
      const dep = {
        id, conceptrecid, state: "unsubmitted", submitted: false,
        // The sandbox's prereserve_doi claims the production prefix; it is never to be trusted.
        metadata: { ...(JSON.parse(body ?? "{}").metadata ?? {}), prereserve_doi: { doi: `10.5281/zenodo.${id}`, recid: id } },
        links: { bucket: bucketOf(id), self: draftUrl(id) },
        files: [],
      };
      drafts.set(id, dep);
      return json(201, dep);
    }
    const pub = /\/deposit\/depositions\/(\d+)\/actions\/publish$/.exec(u.pathname);
    if (method === "POST" && pub) {
      const id = Number(pub[1]);
      const dep = drafts.get(id)!;
      const concept = opts.conceptSource === "fake" ? conceptrecid : dep.conceptrecid;
      const published = {
        ...dep, state: "done", submitted: true,
        conceptdoi: `10.5072/zenodo.${concept}`, doi: `10.5072/zenodo.${id}`,
        links: { ...(dep.links as object), record_html: `https://sandbox.zenodo.org/records/${id}` },
      };
      drafts.set(id, published);
      return json(202, published);
    }
    const nv = /\/deposit\/depositions\/(\d+)\/actions\/newversion$/.exec(u.pathname);
    if (method === "POST" && nv) {
      const parentId = Number(nv[1]);
      const id = nextId++;
      // Real Zenodo copies the parent's metadata into the new version, notes included —
      // which is how the bundle marker survives into a revision draft.
      const inherited = [{ id: "inherited", filename: "paper.pdf" }];
      if (opts.newVersion === "response-only") {
        const parent = drafts.get(parentId) ?? {};
        const concept = opts.conceptSource === "fake" ? conceptrecid : parent.conceptrecid;
        drafts.set(id, {
          id, conceptrecid: concept, conceptdoi: `10.5072/zenodo.${concept}`,
          state: "unsubmitted", submitted: false,
          metadata: { ...(parent.metadata as object) },
          links: { bucket: bucketOf(id) },
          files: inherited,
        });
        return json(201, { id: parentId, links: { latest_draft: draftUrl(id) } });
      }
      const parent = drafts.get(parentId)!;
      drafts.set(id, {
        id, conceptrecid: opts.conceptSource === "fake" ? conceptrecid : parent.conceptrecid,
        state: "unsubmitted", submitted: false,
        metadata: { ...(parent.metadata as object) },
        links: { bucket: bucketOf(id) },
        files: inherited,
      });
      parent.links = { ...(parent.links as object), latest_draft: draftUrl(id) };
      return json(201, { id: parentId, links: parent.links });
    }
    const one = /\/deposit\/depositions\/(\d+)$/.exec(u.pathname);
    if (one) {
      const id = Number(one[1]);
      if (method === "GET") {
        const d = drafts.get(id);
        return d ? json(200, d) : json(404, gone);
      }
      if (method === "PUT") {
        const d = drafts.get(id) ?? {};
        const sent = JSON.parse(body ?? "{}").metadata;
        const next = {
          ...d,
          metadata: opts.metadataPut === "replace" ? sent : { ...(d.metadata as object), ...sent },
        };
        drafts.set(id, next);
        return json(200, next);
      }
      if (method === "DELETE") {
        // A REPEATED delete is 404 on the real service, which is what makes the client's
        // `allow404` load bearing.
        if (!drafts.has(id) && opts.deleteOfMissing !== 204) return json(404, gone);
        drafts.delete(id);
        return new Response(null, { status: 204 });
      }
    }
    if (method === "PUT" && u.pathname.includes("/api/files/")) {
      return json(201, { key: u.pathname.split("/").pop(), size: 10, checksum: "md5:fake", version_id: "v1" });
    }
    return json(500, { message: `fake zenodo: unrouted ${method} ${u.pathname}` });
  };
  return { impl, drafts, marker: () => bundleMarker(h.dir, "sandbox") };
}

/** A deposit context over `impl`. `dryRun` and `env` are properties of the CLIENT, not of the
 *  context: the client is the only object that can send a request, so a second copy of either
 *  could disagree with it. Anything else in `over` overrides the context field of that name. */
export function makeDepositContext(
  h: ZenodoHarness,
  impl: FetchImpl,
  over: Partial<DepositContext> & { dryRun?: boolean; env?: ZenodoEnvironment } = {},
): DepositContext {
  const { dryRun, env, ...rest } = over;
  return {
    bundleDir: h.dir,
    client: new ZenodoClient({
      env: env ?? SANDBOX,
      tokenProvider: async () => TEST_TOKEN,
      fetchImpl: impl,
      sleep: async () => {},
      maxRetries: 1,
      dryRun,
    }),
    writeMeta: false,
    allowUnstamped: false,
    siteBaseUrl: "https://causalsmith.org",
    repoUrl: "https://github.com/Jiyuan-Tan/CausalSmith",
    titlePrefix: "[TEST] ",
    log: (l) => h.logs.push(l),
    warn: (l) => h.warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...rest,
  };
}

/**
 * Registers a `beforeEach` that gives every test a fresh bundle and empty call/log records,
 * and returns the harness together with a fake Zenodo and a context bound to it.
 *
 * The harness object is stable; its FIELDS are replaced before each test, so read them inside
 * a test (or copy them in a `beforeEach` registered after this call), never at module scope.
 */
export function zenodoTestBed(): {
  h: ZenodoHarness;
  fakeZenodo: (opts?: FakeZenodoOptions) => ReturnType<typeof makeFakeZenodo>;
  ctxFor: (impl: FetchImpl, over?: Parameters<typeof makeDepositContext>[2]) => DepositContext;
} {
  const h: ZenodoHarness = { dir: "", calls: [], logs: [], warns: [] };
  beforeEach(async () => {
    h.dir = await makeBundleDir();
    h.calls = [];
    h.logs = [];
    h.warns = [];
  });
  return {
    h,
    fakeZenodo: (opts = {}) => makeFakeZenodo(h, opts),
    ctxFor: (impl, over = {}) => makeDepositContext(h, impl, over),
  };
}
