// The four deposit rules that, if broken, cost something that cannot be undone.
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
// Everything runs against a fake `fetch` and a temp bundle — no network, no clock.

import { describe, it, expect, beforeEach } from "vitest";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import { minimalPdf } from "./zenodo_fixtures.js";
import os from "node:os";
import path from "node:path";
import { SANDBOX, PRODUCTION, ZenodoClient, type ZenodoEnvironment } from "../src/zenodo/client.js";
import { bundleMarker } from "../src/zenodo/bundle.js";
import { abandon, newVersion, publish, reserve, status, type DepositContext } from "../src/zenodo/deposit.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";

const META = {
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

let dir: string;
let calls: { method: string; url: string; body?: string }[];
let logs: string[];
let warns: string[];

beforeEach(async () => {
  // The bundle DIRECTORY NAME is the site's paper id, so the temp bundle must be named
  // like a real one rather than being the mkdtemp root.
  dir = path.join(await mkdtemp(path.join(os.tmpdir(), "zenodo-bundle-")), "stat_demo_spec");
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  calls = [];
  logs = [];
  warns = [];
});

/** A fake Zenodo: routes by method + URL shape and keeps a tiny bit of state, so the
 *  same handler serves reserve, publish and new-version in one test. */
function fakeZenodo(state: {
  drafts?: Map<number, Record<string, unknown>>;
  nextId?: number;
  conceptrecid?: number;
} = {}) {
  const drafts = state.drafts ?? new Map<number, Record<string, unknown>>();
  let nextId = state.nextId ?? 100;
  const baseConcept = state.conceptrecid ?? 99;
  // Real Zenodo mints a FRESH conceptrecid for every newly created deposition — that
  // is exactly why a duplicate `reserve` is dangerous. A fake that reuses one would
  // hide the bug this suite is here to catch.
  let creations = 0;
  let conceptrecid = baseConcept;
  const bucketOf = (id: number) => `https://sandbox.zenodo.org/api/files/bucket-${id}`;

  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url, body });
    const json = (status: number, value: unknown) =>
      new Response(JSON.stringify(value), { status });

    // The marker search `reserve` uses to find an orphaned draft before creating one.
    if (method === "GET" && url.includes("/deposit/depositions?")) {
      const marker = decodeURIComponent(new URL(url).searchParams.get("q") ?? "").replace(/^"|"$/g, "");
      return json(200, [...drafts.values()].filter(
        (d) => d.submitted === false &&
          String((d.metadata as Record<string, unknown> | undefined)?.notes ?? "").includes(marker),
      ));
    }
    if (method === "POST" && url.endsWith("/deposit/depositions")) {
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
    const pubM = /\/deposit\/depositions\/(\d+)\/actions\/publish$/.exec(url);
    if (method === "POST" && pubM) {
      const id = Number(pubM[1]);
      const dep = drafts.get(id) as Record<string, unknown>;
      const published = {
        ...dep, state: "done", submitted: true,
        conceptdoi: `10.5072/zenodo.${conceptrecid}`,
        doi: `10.5072/zenodo.${id}`,
        links: { ...(dep.links as object), record_html: `https://sandbox.zenodo.org/records/${id}` },
      };
      drafts.set(id, published);
      return json(202, published);
    }
    const nvM = /\/deposit\/depositions\/(\d+)\/actions\/newversion$/.exec(url);
    if (method === "POST" && nvM) {
      const id = nextId++;
      const parent = drafts.get(Number(nvM[1])) ?? {};
      drafts.set(id, {
        id, conceptrecid, conceptdoi: `10.5072/zenodo.${conceptrecid}`,
        state: "unsubmitted", submitted: false,
        // Real Zenodo copies the parent's metadata into the new version, notes included
        // — which is how the bundle marker survives into a revision draft.
        metadata: { ...(parent.metadata as object), prereserve_doi: { doi: `10.5281/zenodo.${id}`, recid: id } },
        links: { bucket: bucketOf(id) },
        files: [{ id: "inherited", filename: "paper.pdf" }],
      });
      return json(201, {
        id: Number(nvM[1]),
        links: { latest_draft: `https://sandbox.zenodo.org/api/deposit/depositions/${id}` },
      });
    }
    const depM = /\/deposit\/depositions\/(\d+)$/.exec(url);
    if (depM) {
      const id = Number(depM[1]);
      if (method === "GET") {
        const dep = drafts.get(id);
        return dep ? json(200, dep) : json(404, { message: "The persistent identifier does not exist." });
      }
      if (method === "PUT") {
        const dep = drafts.get(id) ?? {};
        const next = { ...dep, metadata: JSON.parse(body ?? "{}").metadata };
        drafts.set(id, next);
        return json(200, next);
      }
      if (method === "DELETE") {
        drafts.delete(id);
        return new Response(null, { status: 204 });
      }
    }
    if (method === "PUT" && url.includes("/api/files/")) {
      const key = url.split("/").pop() ?? "file";
      return json(201, { key, size: 10, checksum: "md5:fake", version_id: "v1" });
    }
    return json(500, { message: `fake zenodo: unrouted ${method} ${url}` });
  };
  return { impl, drafts };
}

function ctxFor(
  impl: (url: string, init?: RequestInit) => Promise<Response>,
  over: Partial<DepositContext> & { dryRun?: boolean } = {},
  env: ZenodoEnvironment = SANDBOX,
): DepositContext {
  const { dryRun, ...rest } = over;
  return {
    bundleDir: dir,
    // dry-run is a property of the CLIENT, not of the context: it is the only object
    // that can send a request, so a second copy of the flag could disagree with it.
    client: new ZenodoClient({
      env,
      tokenProvider: async () => TOKEN,
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
    log: (l) => logs.push(l),
    warn: (l) => warns.push(l),
    now: () => new Date("2026-09-20T12:00:00.000Z"),
    ...rest,
  };
}

const readJson = async (p: string) => JSON.parse(await readFile(p, "utf8"));
const sidecar = () => readJson(path.join(dir, "zenodo.json"));
const meta = () => readJson(path.join(dir, "meta.json"));

/** A real (tiny) PDF showing `contents`. It must be a genuine PDF: plain text in a
 *  .pdf file is now reported as `unavailable`, not `absent`, so a text stand-in would
 *  exercise the wrong branch entirely. */
async function writePdf(contents: string): Promise<void> {
  await writeFile(path.join(dir, "paper.pdf"), minimalPdf(contents));
}

describe("reserve", () => {
  it("records the concept DOI derived from conceptrecid, not from prereserve_doi", async () => {
    const { impl } = fakeZenodo();
    const res = await reserve(ctxFor(impl));
    // prereserve_doi said 10.5281/zenodo.100; the sandbox actually mints 10.5072.
    expect(res.record.concept_doi).toBe("10.5072/zenodo.99");
    expect(res.record.draft?.version_doi).toBe("10.5072/zenodo.100");
    expect(res.record.draft?.deposition_id).toBe(100);
    expect(res.record.published).toBeNull();
    expect((await sidecar()).sandbox.concept_doi).toBe("10.5072/zenodo.99");
  });

  it("is idempotent: a second reserve reuses the draft instead of minting a new DOI", async () => {
    const { impl } = fakeZenodo();
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
    const { impl, drafts } = fakeZenodo();
    const first = await reserve(ctxFor(impl));
    drafts.delete(first.record.draft!.deposition_id);
    calls.length = 0;
    await expect(reserve(ctxFor(impl))).rejects.toThrow(/no longer exists|permanent|by hand/i);
    expect(calls.filter((c) => c.method === "POST" && c.url.endsWith("/deposit/depositions"))).toHaveLength(0);
    expect(drafts.size).toBe(0);
  });

  it("keeps the sandbox DOI out of meta.json by default", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    const m = await meta();
    expect(m.doi).toBeUndefined();
    expect(m.version_doi).toBeUndefined();
    expect(logs.join("\n")).toMatch(/SANDBOX DOI/);
  });

  it("writes the DOI into meta.json only when --write-meta is passed, and says so", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { writeMeta: true }));
    const m = await meta();
    expect(m.doi).toBe("10.5072/zenodo.99");
    expect(m.version_doi).toBe("10.5072/zenodo.100");
    expect(warns.join("\n")).toMatch(/WRITING A SANDBOX DOI/);
  });

  it("preserves every other meta.json key, 2-space indent and the trailing newline", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { writeMeta: true }));
    const raw = await readFile(path.join(dir, "meta.json"), "utf8");
    expect(raw.endsWith("}\n")).toBe(true);
    expect(raw).toContain('\n  "qid": "stat_demo"');
    const m = await meta();
    for (const [k, v] of Object.entries(META)) expect(m[k]).toEqual(v);
    expect(Object.keys(m).slice(0, Object.keys(META).length)).toEqual(Object.keys(META));
  });

  it("sends nothing and writes nothing under --dry-run", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { dryRun: true, writeMeta: true }));
    expect(calls).toHaveLength(0);
    expect((await meta()).doi).toBeUndefined();
    await expect(sidecar()).rejects.toThrow();
  });
});

describe("publish", () => {
  it("refuses a PDF that does not carry the DOI it would be registered under", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("a paper with no DOI stamp at all");
    await expect(publish(ctxFor(impl))).rejects.toThrow(/does not contain the DOI/);
    expect(calls.some((c) => c.url.includes("/actions/publish"))).toBe(false);
  });

  it("publishes a PDF that does carry the DOI", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("page 1 ... doi:10.5072/zenodo.99 ... rest");
    const res = await publish(ctxFor(impl));
    expect(res.record.published?.version_doi).toBe("10.5072/zenodo.100");
    expect(res.record.published?.record_url).toBe("https://sandbox.zenodo.org/records/100");
    expect(res.record.draft).toBeNull();
    expect(logs.join("\n")).toMatch(/Stamp check: 10\.5072\/zenodo\.99 found/);
  });

  it("tolerates the spacing an extractor inserts into the stamped DOI", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    // A rotated margin stamp comes back one glyph group at a time; the record id's
    // digits still have to be contiguous.
    await writePdf("d o i : 1 0 . 5 0 7 2 / z e n o d o . 99");
    await expect(publish(ctxFor(impl))).resolves.toBeTruthy();
  });

  it("publishes an unstamped PDF only with --allow-unstamped, and warns", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("no stamp here");
    const res = await publish(ctxFor(impl, { allowUnstamped: true }));
    expect(res.record.published).toBeTruthy();
    expect(warns.join("\n")).toMatch(/UNSTAMPED PDF/);
  });

  it("uploads the PDF and sets metadata before publishing, in that order", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
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
    const { impl } = fakeZenodo();
    await writePdf("doi:10.5072/zenodo.99");
    await expect(publish(ctxFor(impl))).rejects.toThrow(/Run 'reserve' first/);
  });

  it("is a no-op when the deposition is already published", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
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
    const { impl } = fakeZenodo({ conceptrecid: 99 });
    await reserve(ctxFor(impl, { writeMeta: true }));
    await writePdf("doi:10.5072/zenodo.99");
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
});

describe("new-version", () => {
  it("keeps the concept DOI and reserves a new version DOI", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
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
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/nothing new to deposit/);
    await expect(newVersion(ctxFor(impl), { force: true })).resolves.toBeTruthy();
  });

  it("refuses to version an unpublished draft", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await expect(newVersion(ctxFor(impl))).rejects.toThrow(/Nothing is published/);
  });

  it("replaces the inherited paper.pdf in the new draft without deleting it first", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, version: 2 }, null, 2)}\n`);
    await newVersion(ctxFor(impl));
    calls.length = 0;
    await publish(ctxFor(impl));
    expect(calls.some((c) => c.method === "DELETE")).toBe(false);
    expect(calls.some((c) => c.method === "PUT" && c.url.endsWith("/files/bucket-101/paper.pdf"))).toBe(true);
  });
});

describe("status and abandon", () => {
  it("reports the recorded deposit alongside what Zenodo says", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    const res = await status(ctxFor(impl));
    expect(res.record?.concept_doi).toBe("10.5072/zenodo.99");
    expect(res.live?.state).toBe("unsubmitted");
    expect(res.meta.doi).toBeNull();
  });

  it("reports cleanly on a bundle with no deposit", async () => {
    const { impl } = fakeZenodo();
    const res = await status(ctxFor(impl));
    expect(res.record).toBeNull();
    expect(logs.join("\n")).toMatch(/No sandbox deposit recorded/);
  });

  it("deletes an unpublished draft and clears both the sidecar entry and meta.json", async () => {
    const { impl, drafts } = fakeZenodo();
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
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    // A production DOI already on the bundle must survive a sandbox abandon.
    await writeFile(path.join(dir, "meta.json"), `${JSON.stringify({ ...META, doi: "10.5281/zenodo.777" }, null, 2)}\n`);
    await abandon(ctxFor(impl));
    expect((await meta()).doi).toBe("10.5281/zenodo.777");
  });

  it("refuses to abandon when the only thing there is a published record", async () => {
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl));
    await writePdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl));
    await expect(abandon(ctxFor(impl))).rejects.toThrow(/PUBLISHED/);
  });
});

describe("environment separation", () => {
  it("keys the sidecar by environment so sandbox cannot clobber production", async () => {
    const { impl } = fakeZenodo();
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
    const { impl } = fakeZenodo();
    await reserve(ctxFor(impl, { writeMeta: true }));
    await writePdf("doi:10.5072/zenodo.99");
    await publish(ctxFor(impl, { writeMeta: true }));
    await status(ctxFor(impl));
    const all = [...logs, ...warns].join("\n");
    expect(all.length).toBeGreaterThan(0);
    expect(all).not.toContain(TOKEN);
    expect(JSON.stringify(await sidecar())).not.toContain(TOKEN);
    expect(JSON.stringify(await meta())).not.toContain(TOKEN);
  });
});
