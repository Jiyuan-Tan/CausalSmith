import { afterEach, describe, expect, it } from "vitest";
import process from "node:process";
import { mkdtemp, mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createHash } from "node:crypto";

import {
  formatWpNumber,
  nextWpNumber,
  parseWpNumber,
  parseWpRegistry,
  rankWpNumbers,
  readWpRegistry,
  resolveWpNumber,
  validateClaimedWpNumber,
  writeWpRegistry,
} from "../src/presentation/wp_registry.js";
import { assertCalendarIsoDate, isCalendarIsoDate, isoYear, utcToday } from "../src/presentation/iso_date.js";
import {
  ensurePaperIdentity,
  fileSha256,
  isProductionDoi,
  nextVersionState,
  paperSiteUrl,
  pinDateCommand,
  unpinDateCommand,
  renderStampTex,
  stampDate,
  titleDate,
} from "../src/presentation/paper_stamp.js";
import { wpRegistryPath } from "../src/presentation/paths.js";
import { withBundleMetaLock } from "../src/presentation/meta_store.js";
import {
  DEFAULT_PAPER_SERIES_PREFIX, assertPaperSeriesPrefix, paperSeriesPrefix, resolveSeriesPrefix,
} from "../src/local_config.js";
import { PaperMeta } from "../src/presentation/types.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function tempRepo(): Promise<string> {
  const root = await mkdtemp(join(tmpdir(), "wp-registry-"));
  dirs.push(root);
  await mkdir(join(root, "doc", "presentation"), { recursive: true });
  return root;
}

describe("working-paper registry", () => {
  it("ranks the initial assignment by (created, bundle id) within each created year", () => {
    expect(
      rankWpNumbers([
        { id: "b_later_same_day", created: "2026-07-02" },
        { id: "a_earliest", created: "2026-06-13" },
        { id: "a_later_same_day", created: "2026-07-02" },
        { id: "z_next_year", created: "2027-01-04" },
      ], "CSWP"),
    ).toEqual({
      a_earliest: "CSWP-2026-001",
      a_later_same_day: "CSWP-2026-002",
      b_later_same_day: "CSWP-2026-003",
      z_next_year: "CSWP-2027-001",
    });
  });

  it("gives a new paper max+1 for ITS year and never renumbers an existing entry", async () => {
    const root = await tempRepo();
    await writeWpRegistry(root, { old_a: "CSWP-2026-001", old_b: "CSWP-2026-007", other_year: "CSWP-2025-004" });
    expect(await resolveWpNumber(root, "fresh", "2026-09-20", null, "CSWP")).toBe("CSWP-2026-008");
    // an existing bundle keeps its number even if its created date would now rank elsewhere
    expect(await resolveWpNumber(root, "old_b", "2026-01-01", null, "CSWP")).toBe("CSWP-2026-007");
    // first paper of an unseen year starts at 001
    expect(await resolveWpNumber(root, "future", "2027-03-01", null, "CSWP")).toBe("CSWP-2027-001");
    const registry = await readWpRegistry(root, "CSWP");
    expect(registry).toEqual({
      old_a: "CSWP-2026-001",
      old_b: "CSWP-2026-007",
      other_year: "CSWP-2025-004",
      fresh: "CSWP-2026-008",
      future: "CSWP-2027-001",
    });
  });

  it("is idempotent and persists with sorted ids, 2-space JSON and a trailing newline", async () => {
    const root = await tempRepo();
    const first = await resolveWpNumber(root, "zz_bundle", "2026-05-05", null, "CSWP");
    const again = await resolveWpNumber(root, "zz_bundle", "2026-05-05", null, "CSWP");
    await resolveWpNumber(root, "aa_bundle", "2026-05-06", null, "CSWP");
    expect(again).toBe(first);
    const raw = await readFile(wpRegistryPath(root), "utf8");
    expect(raw).toBe('{\n  "aa_bundle": "CSWP-2026-002",\n  "zz_bundle": "CSWP-2026-001"\n}\n');
  });

  it("refuses a malformed number or a number used twice rather than guessing a repair", () => {
    expect(() => parseWpRegistry('{"a":"CSWP-26-1"}', "r.json", "CSWP")).toThrow("malformed");
    expect(() => parseWpRegistry('{"a":"CSWP-2026-001","b":"CSWP-2026-001"}', "r.json", "CSWP")).toThrow("assigned to both");
    expect(() => parseWpRegistry("[]", "r.json", "CSWP")).toThrow("expected a");
  });

  it("reads the year off the ISO string, so a 1 January paper cannot slip a year west of UTC", () => {
    expect(isoYear("2026-01-01")).toBe(2026);
    expect(() => isoYear("2026-1-1")).toThrow("invalid ISO date");
    expect(parseWpNumber("CSWP-2026-008", "CSWP")).toEqual({ year: 2026, seq: 8 });
    expect(parseWpNumber("nonsense", "CSWP")).toBeNull();
    expect(formatWpNumber(2026, 8, "CSWP")).toBe("CSWP-2026-008");
    expect(nextWpNumber({}, 2030, "CSWP")).toBe("CSWP-2030-001");
  });
});

describe("version history", () => {
  const created = "2026-07-21";
  const prior = {
    version: 2,
    revised: "2026-08-27",
    versions: [
      { v: 1, date: created, paper_sha256: null },
      { v: 2, date: "2026-08-27", paper_sha256: "aaa" },
    ],
  };

  it("does not invent a version when a re-emit recompiles the same manuscript", () => {
    expect(nextVersionState(prior, "aaa", "2026-09-20", created)).toEqual({
      version: 2,
      revised: "2026-08-27",
      versions: prior.versions,
    });
  });

  it("bumps and dates the new version at the emit date when paper.tex changed", () => {
    const next = nextVersionState(structuredClone(prior), "bbb", "2026-09-20", created);
    expect(next.version).toBe(3);
    expect(next.revised).toBe("2026-09-20");
    expect(next.versions.at(-1)).toEqual({ v: 3, date: "2026-09-20", paper_sha256: "bbb" });
  });

  it("treats a hash the manuscript is equivalent to as unchanged, and adopts the canonical one", () => {
    const next = nextVersionState(structuredClone(prior), "bbb", "2026-09-20", created, { equivalentShas: ["aaa"] });
    expect(next.version).toBe(2);
    expect(next.versions.at(-1)).toEqual({ v: 2, date: "2026-08-27", paper_sha256: "bbb" });
  });

  it("adopts the hash in place when the last entry has none, since unknown is not evidence of change", () => {
    const unhashed = { version: 1, revised: created, versions: [{ v: 1, date: created, paper_sha256: null }] };
    const next = nextVersionState(unhashed, "ccc", "2026-09-20", created);
    expect(next.version).toBe(1);
    expect(next.versions).toEqual([{ v: 1, date: created, paper_sha256: "ccc" }]);
  });

  it("dates a never-stamped bundle's v1 at its publication date, not at the emit", () => {
    expect(nextVersionState({}, "ddd", "2026-09-20", created)).toEqual({
      version: 1,
      revised: created,
      versions: [{ v: 1, date: created, paper_sha256: "ddd" }],
    });
  });
});

describe("stamp rendering", () => {
  it("formats dates from the ISO string, with no locale or timezone in the output", () => {
    expect(stampDate("2026-08-27")).toBe("27 Aug 2026");
    expect(titleDate("2026-08-27")).toBe("27 August 2026");
    expect(stampDate("2026-01-05")).toBe("5 Jan 2026");
    expect(utcToday(new Date("2026-12-31T23:59:59Z"))).toBe("2026-12-31");
    expect(() => stampDate("27/08/2026")).toThrow("invalid ISO date");
  });

  it("renews exactly the macros the template provides, and links a DOI to doi.org", () => {
    const tex = renderStampTex({
      wpNumber: "CSWP-2026-008",
      version: 3,
      area: "Stat",
      revised: "2026-08-27",
      doi: "10.5281/zenodo.123",
      siteUrl: "https://causalsmith.org/papers/x",
    });
    expect(tex).toContain("\\renewcommand*{\\csstampid}{CSWP-2026-008v3}");
    expect(tex).toContain("\\renewcommand*{\\csstamparea}{Stat}");
    expect(tex).toContain("\\renewcommand*{\\csstampdate}{27 Aug 2026}");
    expect(tex).toContain("\\renewcommand*{\\csstampdoi}{10.5281/zenodo.123}");
    expect(tex).toContain("\\renewcommand*{\\csstamplink}{https://doi.org/10.5281/zenodo.123}");
    expect(tex).toContain("\\renewcommand*{\\cspaperdate}{27 August 2026}");
    expect(tex.endsWith("\n")).toBe(true);
  });

  it("prints only a published production DOI — a sandbox one would be a dead citation on paper", () => {
    expect(isProductionDoi("10.5281/zenodo.17158230")).toBe(true);
    for (const rejected of ["10.5072/zenodo.17158230", "10.5281/zenodo.", "zenodo.123", "", null, undefined]) {
      expect(isProductionDoi(rejected)).toBe(false);
    }
    const sandbox = renderStampTex({
      wpNumber: "CSWP-2026-008", version: 3, area: "Stat", revised: "2026-08-27",
      doi: "10.5072/zenodo.99", siteUrl: "https://causalsmith.org/papers/x",
    });
    expect(sandbox).toContain("\\renewcommand*{\\csstampdoi}{}");
    expect(sandbox).toContain("\\renewcommand*{\\csstamplink}{https://causalsmith.org/papers/x}");
  });

  it("omits the DOI part and falls back to the paper's page when no DOI exists yet", () => {
    const tex = renderStampTex({
      wpNumber: "CSWP-2026-021",
      version: 1,
      area: "Partial ID",
      revised: "2026-09-13",
      doi: null,
      siteUrl: "https://causalsmith.org/papers/pid_x",
    });
    expect(tex).toContain("\\renewcommand*{\\csstampdoi}{}");
    expect(tex).toContain("\\renewcommand*{\\csstamplink}{https://causalsmith.org/papers/pid_x}");
  });

  it("stamps no link at all when there is neither a DOI nor a site origin", () => {
    const tex = renderStampTex({ wpNumber: "CSWP-2026-001", version: 1, area: "Stat", revised: "2026-06-13" });
    expect(tex).toContain("\\renewcommand*{\\csstamplink}{}");
    expect(paperSiteUrl("abc", { CAUSALSMITH_SITE_URL: "" })).toBe("");
    expect(paperSiteUrl("abc", {})).toBe("https://causalsmith.org/papers/abc");
    expect(paperSiteUrl("abc", { CAUSALSMITH_SITE_URL: "https://stage.example/" })).toBe("https://stage.example/papers/abc");
  });

  it("cannot inject TeX through an area or DOI value", () => {
    const tex = renderStampTex({ wpNumber: "CSWP-2026-001", version: 1, area: "A\\newpage{}B_C", revised: "2026-06-13" });
    expect(tex).toContain("\\renewcommand*{\\csstamparea}{AnewpageB\\_C}");
  });

  it("pins a legacy \\date{\\today} exactly once and leaves anything else alone", () => {
    const legacy = "\\title{X}\n\n\\date{\\today}\n\n\\begin{document}";
    const pinned = pinDateCommand(legacy);
    expect(pinned).toContain("\\date{\\cspaperdate}");
    expect(pinDateCommand(pinned)).toBe(pinned);
    expect(pinDateCommand("\\date{1 Jan 2026}")).toBe("\\date{1 Jan 2026}");
  });
});

describe("paper_macros.tex ↔ paper_stamp.tex contract", () => {
  it("provides a default for every macro the generated stamp file renews, and inputs it optionally", async () => {
    const template = await readFile(
      join(import.meta.dirname, "..", "src", "presentation", "templates", "paper_macros.tex"),
      "utf8",
    );
    const renewed = [...renderStampTex({ wpNumber: "CSWP-2026-001", version: 1, area: "Stat", revised: "2026-06-13" })
      .matchAll(/\\renewcommand\*\{\\(\w+)\}/g)].map((m) => m[1]);
    expect(renewed.length).toBeGreaterThan(0);
    for (const macro of renewed) expect(template).toContain(`\\providecommand*{\\${macro}}`);
    // `\IfFileExists` is what keeps every bundle shipped before the stamp existed compiling.
    expect(template).toContain("\\IfFileExists{paper_stamp.tex}{\\input{paper_stamp.tex}}{}");
    // The DOI must never be the LAST field: a text extractor would run it into whatever follows,
    // and the Zenodo stamp matcher reads this line. Order: number, doi, area, date.
    const line = template.slice(template.indexOf("\\newcommand{\\cs@stamptext}"));
    const at = (needle: string) => line.indexOf(needle);
    expect(at("\\csstampid")).toBeLessThan(at("doi:\\csstampdoi"));
    expect(at("doi:\\csstampdoi")).toBeLessThan(at("[\\csstamparea]"));
    expect(at("[\\csstamparea]")).toBeLessThan(at("\\csstampdate\\fi"));
    // Page 1 only, in the margin, bottom-to-top, and drawn only when there is a number.
    expect(template).toContain("\\AddToShipoutPictureBG*{");
    expect(template).toContain("\\rotatebox{90}");
    expect(template).toContain("\\ifx\\csstampid\\@empty\\else");
    // The packages the hook needs must be loaded by the template itself.
    for (const pkg of ["graphicx", "eso-pic", "xcolor"]) expect(template).toContain(`\\usepackage{${pkg}}`);
  });

  it("assembles a pinned \\date, so a recompile cannot move the printed date", async () => {
    const assembly = await readFile(
      join(import.meta.dirname, "..", "src", "presentation", "stages", "p2_draft.ts"),
      "utf8",
    );
    expect(assembly).toContain('"\\\\date{\\\\cspaperdate}"');
    expect(assembly).not.toContain('"\\\\date{\\\\today}"');
  });
});

describe("ensurePaperIdentity", () => {
  async function bundle(paper: string, prevMeta: Record<string, unknown> = {}) {
    const repoRoot = await tempRepo();
    const outDir = join(repoRoot, "doc", "presentation", "stat_demo_v1");
    await mkdir(outDir, { recursive: true });
    await writeFile(join(outDir, "paper.tex"), paper, "utf8");
    return { repoRoot, outDir, prevMeta };
  }

  it("pins the date, assigns a number, writes the stamp file, and records the compiled hash", async () => {
    const { repoRoot, outDir, prevMeta } = await bundle("\\date{\\today}\n\\begin{document}\\end{document}\n");
    const identity = await ensurePaperIdentity({
      outDir, repoRoot, bundleId: "stat_demo_v1", area: "Stat", created: "2026-07-21", prevMeta, seriesPrefix: "CSWP", today: "2026-09-20",
    });
    expect(identity).toEqual({
      wp_number: "CSWP-2026-001",
      version: 1,
      revised: "2026-07-21",
      versions: [{ v: 1, date: "2026-07-21", paper_sha256: expect.any(String) }],
      stampedDoi: null,
      // The pin equivalence, carried out so the callers that ADOPT this hash can re-point
      // p5_review.json's manuscript_sha256 at it — see adoptReviewManuscriptSha.
      manuscriptShas: { canonical: expect.any(String), equivalents: [expect.any(String), expect.any(String)] },
    });
    const paper = await readFile(join(outDir, "paper.tex"), "utf8");
    expect(paper).toContain("\\date{\\cspaperdate}");
    expect(identity.versions[0]!.paper_sha256).toBe(createHash("sha256").update(Buffer.from(paper, "utf8")).digest("hex"));
    expect(await readFile(join(outDir, "paper_stamp.tex"), "utf8")).toContain("\\renewcommand*{\\csstampid}{CSWP-2026-001v1}");
    expect(await readWpRegistry(repoRoot, "CSWP")).toEqual({ stat_demo_v1: "CSWP-2026-001" });
  });

  it("carries the WP-C DOIs and the assigned number through a re-emit without bumping the version", async () => {
    const { repoRoot, outDir } = await bundle("\\date{\\cspaperdate}\nbody\n");
    const first = await ensurePaperIdentity({
      outDir, repoRoot, bundleId: "stat_demo_v1", area: "Stat", created: "2026-07-21",
      prevMeta: {}, seriesPrefix: "CSWP", today: "2026-09-20",
    });
    const withDoi = { ...first, doi: "10.5281/zenodo.99", version_doi: "10.5281/zenodo.100", created: "2026-07-21" };
    const second = await ensurePaperIdentity({
      outDir, repoRoot, bundleId: "stat_demo_v1", area: "Stat", created: "2026-07-21",
      prevMeta: withDoi, seriesPrefix: "CSWP", today: "2026-09-21",
    });
    expect(second.version).toBe(1);
    expect(second.revised).toBe("2026-07-21");
    expect(second.wp_number).toBe("CSWP-2026-001");
    // P4 no longer WRITES the DOIs at all; it only reads the concept DOI to render the stamp.
    expect(second.stampedDoi).toBe("10.5281/zenodo.99");
    expect(second).not.toHaveProperty("version_doi");
    expect(await readFile(join(outDir, "paper_stamp.tex"), "utf8")).toContain("doi.org/10.5281/zenodo.99");
  });

  it("bumps the version, re-dates it to the emit, and restamps when paper.tex actually changed", async () => {
    const { repoRoot, outDir } = await bundle("\\date{\\cspaperdate}\nbody\n");
    const first = await ensurePaperIdentity({
      outDir, repoRoot, bundleId: "stat_demo_v1", area: "Stat", created: "2026-07-21", prevMeta: {}, seriesPrefix: "CSWP", today: "2026-09-20",
    });
    await writeFile(join(outDir, "paper.tex"), "\\date{\\cspaperdate}\nrevised body\n", "utf8");
    const second = await ensurePaperIdentity({
      outDir, repoRoot, bundleId: "stat_demo_v1", area: "Stat", created: "2026-07-21",
      prevMeta: { ...first, created: "2026-07-21" }, seriesPrefix: "CSWP", today: "2026-09-21",
    });
    expect(second.version).toBe(2);
    expect(second.revised).toBe("2026-09-21");
    expect(second.versions.map((v) => v.v)).toEqual([1, 2]);
    expect(await readFile(join(outDir, "paper_stamp.tex"), "utf8")).toContain("\\renewcommand*{\\csstampid}{CSWP-2026-001v2}");
  });
});

describe("meta.json schema compatibility", () => {
  it("still parses a meta.json written before the citation fields existed", () => {
    const legacy = {
      qid: "stat_x", spec: "v1", title: "T", tldr: "", abstract: "A", area: "Stat",
      authorship: null, created: "2026-06-13", wp_number: null, score: 6.8, score_rationale: "r",
    };
    const parsed = PaperMeta.parse(legacy);
    expect(parsed.version).toBe(1);
    expect(parsed.revised).toBeNull();
    expect(parsed.versions).toEqual([]);
    expect(parsed.doi).toBeNull();
    expect(parsed.version_doi).toBeNull();
  });

  it("emits the citation fields between wp_number and score, so a backfilled file keeps its key order", () => {
    const parsed = PaperMeta.parse({
      qid: "q", spec: "v1", title: "T", tldr: "", abstract: "A", area: "Stat", authorship: null,
      created: "2026-06-13", wp_number: "CSWP-2026-001", version: 2, revised: "2026-08-25",
      versions: [{ v: 1, date: "2026-06-13" }, { v: 2, date: "2026-08-25", paper_sha256: "ff" }],
      doi: null, version_doi: null, score: null, score_rationale: null,
    });
    expect(Object.keys(parsed)).toEqual([
      "qid", "spec", "title", "tldr", "abstract", "area", "authorship", "created",
      "wp_number", "version", "revised", "versions", "doi", "version_doi", "score", "score_rationale",
    ]);
    expect(parsed.versions[0]!.paper_sha256).toBeNull();
  });
});

describe("calendar dates (a published record cannot carry 31 February)", () => {
  it("accepts only dates that exist, in UTC", () => {
    for (const ok of ["2026-01-01", "2024-02-29", "2026-12-31"]) expect(isCalendarIsoDate(ok)).toBe(true);
    for (const bad of ["2026-02-31", "2026-13-01", "2025-1-01", "2026-00-10", "", "2026-02-30", null, 20260101]) {
      expect(isCalendarIsoDate(bad)).toBe(false);
    }
    expect(() => assertCalendarIsoDate("meta.json created", "2026-02-31")).toThrow("not a real calendar date");
    expect(() => stampDate("2026-02-31")).toThrow("not a real calendar date");
  });
});

describe("version history cannot move backwards", () => {
  it("rejects a recorded history dated before created, or out of order", () => {
    expect(() => nextVersionState(
      { versions: [{ v: 1, date: "2026-06-01", paper_sha256: "a" }] }, "a", "2026-09-20", "2026-07-01",
    )).toThrow("moves backwards");
    expect(() => nextVersionState(
      { versions: [{ v: 1, date: "2026-07-01", paper_sha256: "a" }, { v: 2, date: "2026-06-01", paper_sha256: "b" }] },
      "b", "2026-09-20", "2026-07-01",
    )).toThrow("moves backwards");
  });

  it("never dates a bump before created or before the version it revises", () => {
    // One day ahead of UTC is a timezone, not a fault: the bump takes the recorded date rather
    // than a date earlier than the version it revises (see the timezone group below).
    const oneDayAhead = nextVersionState(
      { versions: [{ v: 1, date: "2027-01-01", paper_sha256: "a" }] }, "changed", "2026-12-31", "2027-01-01",
    );
    expect(oneDayAhead.revised).toBe("2027-01-01");
    expect(oneDayAhead.versions.at(-1)!.date).toBe("2027-01-01");
    expect(oneDayAhead.revised >= "2027-01-01").toBe(true);
  });

  it("reports a malformed history entry instead of dropping it and renumbering the series", () => {
    expect(() => nextVersionState(
      { versions: [{ v: 1, date: "2026-07-01" }, { v: 0, date: "2026-08-01" }] }, "a", "2026-09-20", "2026-07-01",
    )).toThrow("versions[1].v is not a positive integer");
    expect(() => nextVersionState(
      { versions: [{ v: 1, date: "not-a-date" }] }, "a", "2026-09-20", "2026-07-01",
    )).toThrow("versions[0].date");
  });
});

describe("the registry is authoritative for wp_number", () => {
  it("returns the registry's number when meta agrees, and allocates when neither has one", async () => {
    const root = await tempRepo();
    expect(await resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP")).toBe("CSWP-2026-001");
    expect(await resolveWpNumber(root, "b1", "2026-05-05", "CSWP-2026-001", "CSWP")).toBe("CSWP-2026-001");
    expect(await resolveWpNumber(root, "b2", "2026-05-06", undefined, "CSWP")).toBe("CSWP-2026-002");
  });

  it("fails loudly, naming both values, when meta disagrees with the registry", async () => {
    const root = await tempRepo();
    await writeWpRegistry(root, { b1: "CSWP-2026-005" });
    await expect(resolveWpNumber(root, "b1", "2026-05-05", "CSWP-2026-006", "CSWP"))
      .rejects.toThrow(/CSWP-2026-005.*CSWP-2026-006|CSWP-2026-006.*CSWP-2026-005/s);
    // and the registry is left exactly as it was — no silent adoption either way
    expect(await readWpRegistry(root, "CSWP")).toEqual({ b1: "CSWP-2026-005" });
  });

  it("rejects a malformed meta number rather than adopting or overwriting it", async () => {
    const root = await tempRepo();
    for (const bad of ["CSWP-26-1", "cswp-2026-001", "CSWP-2026-001 ", " CSWP-2026-001", "1"]) {
      await expect(resolveWpNumber(root, "b1", "2026-05-05", bad, "CSWP")).rejects.toThrow("malformed working-paper number");
    }
    expect(await readWpRegistry(root, "CSWP")).toEqual({});
  });

  it("adopts an unregistered meta number only when no other bundle owns it", async () => {
    const root = await tempRepo();
    await writeWpRegistry(root, { other: "CSWP-2026-004" });
    expect(await resolveWpNumber(root, "b1", "2026-05-05", "CSWP-2026-009", "CSWP")).toBe("CSWP-2026-009");
    expect((await readWpRegistry(root, "CSWP")).b1).toBe("CSWP-2026-009");
    await expect(resolveWpNumber(root, "b2", "2026-05-05", "CSWP-2026-004", "CSWP"))
      .rejects.toThrow(/already assigned that number to other/);
  });

  it("hands two concurrent allocators distinct numbers", async () => {
    const root = await tempRepo();
    const ids = Array.from({ length: 6 }, (_, i) => `bundle_${i}`);
    const numbers = await Promise.all(ids.map((id) => resolveWpNumber(root, id, "2026-05-05", null, "CSWP")));
    expect(new Set(numbers).size).toBe(ids.length);
    const registry = await readWpRegistry(root, "CSWP");
    // every allocation survived: the lock serialises read-decide-write, so none was overwritten
    expect(Object.keys(registry).sort()).toEqual(ids.slice().sort());
    expect(new Set(Object.values(registry)).size).toBe(ids.length);
    expect(Object.values(registry).sort()).toEqual(
      ids.map((_, i) => `CSWP-2026-${String(i + 1).padStart(3, "0")}`),
    );
  });
});

describe("r2: only null/undefined mean 'this bundle has no number yet'", () => {
  it("reports every other non-conforming wp_number instead of treating it as absent", async () => {
    const root = await tempRepo();
    for (const corrupt of ["", 123, {}, [], true]) {
      await expect(resolveWpNumber(root, "b1", "2026-05-05", corrupt, "CSWP"))
        .rejects.toThrow(/malformed working-paper number/);
    }
    expect(await readWpRegistry(root, "CSWP")).toEqual({});
    // only a genuine absence allocates
    expect(await resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP")).toBe("CSWP-2026-001");
    expect(await resolveWpNumber(root, "b2", "2026-05-05", undefined, "CSWP")).toBe("CSWP-2026-002");
  });

  it("refuses to adopt a number whose year disagrees with created", async () => {
    const root = await tempRepo();
    await expect(resolveWpNumber(root, "b1", "2026-01-01", "CSWP-2025-009", "CSWP"))
      .rejects.toThrow(/series year 2025.*created date is 2026-01-01/s);
    expect(await readWpRegistry(root, "CSWP")).toEqual({});
    // the matching-year case still adopts
    expect(await resolveWpNumber(root, "b1", "2026-01-01", "CSWP-2026-009", "CSWP")).toBe("CSWP-2026-009");
  });
});

describe("r2: a timezone ahead of UTC must not fail a legitimate same-day revision", () => {
  const history = (date: string) => ({
    version: 1, revised: date, versions: [{ v: 1, date, paper_sha256: "old" }],
  });

  it("dates the bump at the recorded date when created/v1 is one day ahead of UTC today", () => {
    // UTC+14 operator: their local calendar day is already 2026-09-21 while UTC says 2026-09-20.
    const next = nextVersionState(history("2026-09-21"), "changed", "2026-09-20", "2026-09-21");
    expect(next.version).toBe(2);
    expect(next.revised).toBe("2026-09-21");
    expect(next.versions.at(-1)).toEqual({ v: 2, date: "2026-09-21", paper_sha256: "changed" });
  });

  it("still fails loudly when the recorded date is further ahead than any timezone explains", () => {
    expect(() => nextVersionState(history("2026-09-25"), "changed", "2026-09-20", "2026-09-25"))
      .toThrow(/clock|skew/i);
  });

  it("uses the emit date whenever it is the latest of the three", () => {
    expect(nextVersionState(history("2026-07-01"), "changed", "2026-09-20", "2026-06-01").revised)
      .toBe("2026-09-20");
  });
});

describe("r2: the recorded version history must be a complete, ordered series", () => {
  const base = { created: "2026-06-01" };
  const run = (versions: unknown[], top: Record<string, unknown> = {}) =>
    () => nextVersionState({ ...top, versions }, "x", "2026-09-20", base.created);

  it("rejects a gap, a duplicate, or a series that does not start at 1", () => {
    expect(run([{ v: 1, date: "2026-06-01" }, { v: 3, date: "2026-07-01" }])).toThrow(/contiguous|gap/i);
    expect(run([{ v: 1, date: "2026-06-01" }, { v: 1, date: "2026-07-01" }])).toThrow(/duplicate|contiguous/i);
    expect(run([{ v: 2, date: "2026-06-01" }])).toThrow(/start at 1|contiguous/i);
  });

  it("rejects top-level version/revised that disagree with the final history entry", () => {
    const versions = [{ v: 1, date: "2026-06-01" }, { v: 2, date: "2026-07-01" }];
    expect(run(versions, { version: 1, revised: "2026-07-01" })).toThrow(/version/);
    expect(run(versions, { version: 2, revised: "2026-06-01" })).toThrow(/revised/);
    // agreeing values are fine
    expect(run(versions, { version: 2, revised: "2026-07-01" })).not.toThrow();
  });
});

describe("r2: lock ordering is registry then meta, never the reverse", () => {
  it("refuses to take the registry lock while a bundle meta lock is held", async () => {
    const root = await tempRepo();
    await expect(
      withBundleMetaLock(root, () => resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP")),
    ).rejects.toThrow(/lock order/i);
  });

  it("allows the documented order", async () => {
    const root = await tempRepo();
    const number = await resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP");
    await withBundleMetaLock(root, async () => { expect(number).toBe("CSWP-2026-001"); });
  });
});

describe("r2: the tightened validator accepts every bundle already shipped", () => {
  it("re-validates all 22 published histories without rejecting or changing one", async () => {
    const root = join(import.meta.dirname, "..", "..", "doc", "presentation");
    const ids = (await readdir(root, { withFileTypes: true }))
      .filter((e) => e.isDirectory())
      .map((e) => e.name)
      .sort();
    expect(ids.length).toBeGreaterThanOrEqual(22);
    for (const id of ids) {
      const meta = JSON.parse(await readFile(join(root, id, "meta.json"), "utf8")) as Record<string, unknown>;
      const versions = meta.versions as Array<{ v: number; date: string; paper_sha256: string | null }>;
      const currentSha = versions.at(-1)!.paper_sha256!;
      // Same inputs a re-emit would present: unchanged manuscript, today's date.
      const state = nextVersionState(meta, currentSha, utcToday(), meta.created as string);
      expect(state.version, `${id} version`).toBe(meta.version);
      expect(state.revised, `${id} revised`).toBe(meta.revised);
      expect(state.versions, `${id} versions`).toEqual(versions);
      // and the contiguity/agreement rules hold as recorded
      expect(versions.map((v) => v.v)).toEqual(versions.map((_, i) => i + 1));
      expect(meta.version).toBe(versions.at(-1)!.v);
      expect(meta.revised).toBe(versions.at(-1)!.date);
    }
  });
});

describe("the working-paper series prefix is configurable", () => {
  const ENV = "CAUSALSMITH_PAPER_SERIES_PREFIX";
  afterEach(() => { delete process.env[ENV]; });

  it("defaults to CSWP, which is what the 22 shipped bundles and their registry use", async () => {
    expect(process.env[ENV]).toBeUndefined();
    expect(DEFAULT_PAPER_SERIES_PREFIX).toBe("CSWP");
    expect(paperSeriesPrefix()).toBe("CSWP");
    const shipped = join(import.meta.dirname, "..", "..", "doc", "presentation", "_wp_registry.json");
    const registry = parseWpRegistry(await readFile(shipped, "utf8"), shipped, DEFAULT_PAPER_SERIES_PREFIX); // must not throw
    expect(Object.keys(registry).length).toBeGreaterThanOrEqual(22);
    for (const number of Object.values(registry)) expect(number.startsWith("CSWP-")).toBe(true);
    expect(formatWpNumber(2026, 8, "CSWP")).toBe("CSWP-2026-008");
  });

  it("mints, validates and stamps a custom series end to end", async () => {
    process.env[ENV] = "AIWP7";
    const prefix = paperSeriesPrefix(); // resolved ONCE, exactly as an entry point does
    expect(prefix).toBe("AIWP7");
    const root = await tempRepo();
    expect(formatWpNumber(2026, 8, prefix)).toBe("AIWP7-2026-008");
    expect(await resolveWpNumber(root, "b1", "2026-05-05", null, prefix)).toBe("AIWP7-2026-001");
    expect(await resolveWpNumber(root, "b2", "2026-05-06", "AIWP7-2026-009", prefix)).toBe("AIWP7-2026-009");
    expect(nextWpNumber(await readWpRegistry(root, prefix), 2026, prefix)).toBe("AIWP7-2026-010");
    expect(rankWpNumbers([{ id: "x", created: "2026-01-01" }], prefix)).toEqual({ x: "AIWP7-2026-001" });
    // ...and the number reaches page 1 through the stamp unchanged
    expect(renderStampTex({ wpNumber: "AIWP7-2026-009", version: 2, area: "Stat", revised: "2026-05-06" }))
      .toContain("\\renewcommand*{\\csstampid}{AIWP7-2026-009v2}");
    // a number from the DEFAULT series is now foreign and must not be adopted
    await expect(resolveWpNumber(root, "b3", "2026-05-05", "CSWP-2026-003", prefix))
      .rejects.toThrow(/belongs to series CSWP, but this checkout publishes AIWP7/);
  });

  it("refuses a registry holding another series rather than mixing or renumbering", async () => {
    const root = await tempRepo();
    await writeWpRegistry(root, { b1: "CSWP-2026-001" });
    process.env[ENV] = "AIWP7";
    const prefix = paperSeriesPrefix();
    await expect(readWpRegistry(root, prefix)).rejects.toThrow(/belongs to series CSWP.*publishes AIWP7/s);
    await expect(resolveWpNumber(root, "b2", "2026-05-05", null, prefix)).rejects.toThrow(/series CSWP/);
  });

  it("rejects a prefix that could never read as a series tag", () => {
    for (const bad of ["", "C", "cswp", "CS WP", "C-SWP", "1CSWP", "TOOLONGPREFIX", 7, null]) {
      process.env[ENV] = bad === null ? "" : String(bad);
      expect(() => paperSeriesPrefix(), `${JSON.stringify(bad)}`).toThrow(/Invalid paperSeriesPrefix/);
      expect(() => assertPaperSeriesPrefix(bad)).toThrow(/Invalid paperSeriesPrefix/);
    }
    for (const ok of ["CSWP", "AB", "AIWP7", "A123456789"]) {
      expect(assertPaperSeriesPrefix(ok)).toBe(ok);
    }
  });
});

describe("r3: one operation carries one series", () => {
  const ENV = "CAUSALSMITH_PAPER_SERIES_PREFIX";
  afterEach(() => { delete process.env[ENV]; });

  it("uses the prefix it was GIVEN, so a mid-operation environment change cannot split a write", async () => {
    const root = await tempRepo();
    process.env[ENV] = "AAA";
    const captured = paperSeriesPrefix(); // the entry point resolves once...
    process.env[ENV] = "BBB";             // ...and the world changes underneath it
    expect(await resolveWpNumber(root, "b1", "2026-05-05", null, captured)).toBe("AAA-2026-001");
    // the registry it wrote is readable in the series it was written for, and only that one
    expect(await readWpRegistry(root, captured)).toEqual({ b1: "AAA-2026-001" });
    await expect(readWpRegistry(root, paperSeriesPrefix())).rejects.toThrow(/belongs to series AAA/);
  });

  it("validates a claimed number against the captured prefix and created year, verbatim", () => {
    expect(validateClaimedWpNumber("b", "2026-01-01", null, "CSWP")).toBeNull();
    expect(validateClaimedWpNumber("b", "2026-01-01", undefined, "CSWP")).toBeNull();
    expect(validateClaimedWpNumber("b", "2026-01-01", "CSWP-2026-004", "CSWP")).toBe("CSWP-2026-004");
    for (const bad of ["", 0, 123, {}, [], true, " CSWP-2026-004", "CSWP-2026-004 "]) {
      expect(() => validateClaimedWpNumber("b", "2026-01-01", bad, "CSWP")).toThrow(/malformed/);
    }
    expect(() => validateClaimedWpNumber("b", "2026-01-01", "AIWP7-2026-004", "CSWP"))
      .toThrow(/belongs to series AIWP7, but this checkout publishes CSWP/);
    expect(() => validateClaimedWpNumber("b", "2026-01-01", "CSWP-2025-004", "CSWP"))
      .toThrow(/series year 2025.*created date is 2026-01-01/s);
  });
});

describe("r3: the series never falls back to a guess", () => {
  it("fails closed when local.json exists but could not be parsed", () => {
    expect(() => resolveSeriesPrefix(undefined, undefined, "Unexpected token }"))
      .toThrow(/could not be parsed.*never guessed/s);
    expect(() => resolveSeriesPrefix(undefined, "AIWP7", "Unexpected token }")).toThrow(/could not be parsed/);
    // an operator stating the answer explicitly still wins over an unreadable file
    expect(resolveSeriesPrefix("AIWP7", undefined, "Unexpected token }")).toBe("AIWP7");
    // absent file (no parse error) keeps the default
    expect(resolveSeriesPrefix(undefined, undefined, null)).toBe(DEFAULT_PAPER_SERIES_PREFIX);
    expect(resolveSeriesPrefix(undefined, "AIWP7", null)).toBe("AIWP7");
    expect(() => resolveSeriesPrefix("bad-prefix", undefined, null)).toThrow(/Invalid paperSeriesPrefix/);
  });
});

describe("r3: an empty history cannot carry a version above 1", () => {
  it("rejects incomplete legacy state instead of synthesising the missing entries", () => {
    expect(() => nextVersionState(
      { version: 2, revised: "2026-08-01", versions: [] }, "x", "2026-09-20", "2026-06-01",
    )).toThrow(/incomplete legacy state/);
    // a genuine v1, and a bundle that has never been stamped, are both fine
    expect(nextVersionState({ version: 1, versions: [] }, "x", "2026-09-20", "2026-06-01").version).toBe(1);
    expect(nextVersionState({}, "x", "2026-09-20", "2026-06-01").version).toBe(1);
  });
});

describe("r3: the lock-order marker tracks the lock, not the async context", () => {
  it("lets work scheduled inside the lock take the registry lock after it is released", async () => {
    const root = await tempRepo();
    let detached!: Promise<string>;
    await withBundleMetaLock(root, async () => {
      // scheduled inside the critical section, resolved after it — a legal acquisition
      detached = new Promise<string>((res, rej) => setTimeout(
        () => resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP").then(res, rej), 20));
    });
    await expect(detached).resolves.toBe("CSWP-2026-001");
  });

  it("clears the marker even when the guarded action throws", async () => {
    const root = await tempRepo();
    await expect(withBundleMetaLock(root, async () => { throw new Error("boom"); })).rejects.toThrow("boom");
    // the lock is gone, so this legal acquisition must not be refused
    expect(await resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP")).toBe("CSWP-2026-001");
  });

  it("still refuses an acquisition while the lock is actually held", async () => {
    const root = await tempRepo();
    await expect(withBundleMetaLock(root, () => resolveWpNumber(root, "b1", "2026-05-05", null, "CSWP")))
      .rejects.toThrow(/lock order/i);
  });
});

describe("r6: the date pin is equivalent to the unpinned manuscript, in any run", () => {
  /** A bundle exactly as the backfill leaves it: paper.tex still carries `\date{\today}`, and the
   *  recorded hash is the hash of those UNPINNED bytes. All 22 shipped bundles are in this state. */
  async function backfilled() {
    const repoRoot = await tempRepo();
    const outDir = join(repoRoot, "doc", "presentation", "stat_demo_v1");
    await mkdir(outDir, { recursive: true });
    const unpinned = "\\documentclass{article}\n\\date{\\today}\n\\begin{document}\nBody.\n\\end{document}\n";
    await writeFile(join(outDir, "paper.tex"), unpinned, "utf8");
    const meta: Record<string, unknown> = {
      created: "2026-07-21", wp_number: "CSWP-2026-001", version: 1, revised: "2026-07-21",
      versions: [{ v: 1, date: "2026-07-21", paper_sha256: createHash("sha256").update(Buffer.from(unpinned, "utf8")).digest("hex") }],
    };
    return { repoRoot, outDir, meta, unpinned };
  }
  const emit = (a: { repoRoot: string; outDir: string }, prevMeta: Record<string, unknown>, today: string) =>
    ensurePaperIdentity({
      outDir: a.outDir, repoRoot: a.repoRoot, bundleId: "stat_demo_v1", area: "Stat",
      created: "2026-07-21", prevMeta, seriesPrefix: "CSWP", today,
    });

  it("does not bump when an earlier emit pinned the date but died before writing meta.json", async () => {
    const a = await backfilled();
    // Emit 1 pins paper.tex on disk...
    const first = await emit(a, a.meta, "2026-09-20");
    expect(first.version).toBe(1);
    expect(await readFile(join(a.outDir, "paper.tex"), "utf8")).toContain("\\date{\\cspaperdate}");
    // ...and then dies. meta.json still records the UNPINNED hash.
    // Emit 2 sees an already-pinned file it did not pin itself. Nothing about the paper changed.
    const second = await emit(a, a.meta, "2026-09-21");
    expect(second.version).toBe(1);
    expect(second.revised).toBe("2026-07-21");
    expect(second.versions).toHaveLength(1);
    // the pinned hash is adopted in place, so the third emit has nothing left to reconcile
    expect(second.versions[0]!.paper_sha256).toBe(await fileSha256(join(a.outDir, "paper.tex")));
    const third = await emit(a, { ...a.meta, versions: second.versions }, "2026-09-22");
    expect(third.version).toBe(1);
  });

  it("still bumps when the manuscript itself changed, pinned or not", async () => {
    const a = await backfilled();
    await emit(a, a.meta, "2026-09-20");
    const current = await readFile(join(a.outDir, "paper.tex"), "utf8");
    await writeFile(join(a.outDir, "paper.tex"), current.replace("Body.", "Revised body."), "utf8");
    const next = await emit(a, a.meta, "2026-09-21");
    expect(next.version).toBe(2);
    expect(next.revised).toBe("2026-09-21");
  });

  it("maps a pinned date back exactly, so the two directions cannot drift", () => {
    const unpinned = "x\n\\date{\\today}\ny\n";
    expect(unpinDateCommand(pinDateCommand(unpinned))).toBe(unpinned);
    expect(pinDateCommand(unpinDateCommand(pinDateCommand(unpinned)))).toBe(pinDateCommand(unpinned));
    // neither direction touches anything else
    expect(unpinDateCommand("\\date{1 Jan 2026}")).toBe("\\date{1 Jan 2026}");
    expect(unpinDateCommand(unpinned)).toBe(unpinned);
  });
});

describe("r7: the recorded hash is always the hash of the file's bytes", () => {
  async function bundleWith(bytes: Buffer) {
    const repoRoot = await tempRepo();
    const outDir = join(repoRoot, "doc", "presentation", "stat_demo_v1");
    await mkdir(outDir, { recursive: true });
    await writeFile(join(outDir, "paper.tex"), bytes);
    return { repoRoot, outDir };
  }
  const emit = (a: { repoRoot: string; outDir: string }, prevMeta: Record<string, unknown>, today: string) =>
    ensurePaperIdentity({
      outDir: a.outDir, repoRoot: a.repoRoot, bundleId: "stat_demo_v1", area: "Stat",
      created: "2026-07-21", prevMeta, seriesPrefix: "CSWP", today,
    });

  it("hashes raw bytes, so a manuscript that is not valid UTF-8 still agrees with P5 and the backfill", async () => {
    // A stray 0x80 continuation byte: `readFile(…, "utf8")` would turn it into U+FFFD, and a
    // string-derived digest would then match nothing else that records this file.
    const bytes = Buffer.concat([
      Buffer.from("\\documentclass{article}\n\\date{\\cspaperdate}\n% ", "utf8"),
      Buffer.from([0x80]),
      Buffer.from("\n\\begin{document}\\end{document}\n", "utf8"),
    ]);
    const a = await bundleWith(bytes);
    const onDisk = await fileSha256(join(a.outDir, "paper.tex"));
    expect(onDisk).toBe(createHash("sha256").update(bytes).digest("hex"));

    const first = await emit(a, {}, "2026-09-20");
    expect(first.versions[0]!.paper_sha256).toBe(onDisk); // == what P5/the backfill would record
    // nothing needed pinning, and the file is byte-identical afterwards
    expect(await readFile(join(a.outDir, "paper.tex"))).toEqual(bytes);
    // a second emit sees the same paper
    const second = await emit(a, { created: "2026-07-21", version: 1, revised: "2026-07-21", versions: first.versions }, "2026-09-21");
    expect(second.version).toBe(1);
    expect(second.versions[0]!.paper_sha256).toBe(onDisk);
  });

  it("does not bump a paper that literally contains BOTH date forms", async () => {
    // Undoing the pin cannot reproduce what was recorded here, because the pin rewrote one of two
    // occurrences; the pre-pin bytes are what identifies it.
    const both = "\\date{\\today}\n\\date{\\cspaperdate}\n";
    const a = await bundleWith(Buffer.from(both, "utf8"));
    const recorded = createHash("sha256").update(Buffer.from(both, "utf8")).digest("hex");
    const meta = { created: "2026-07-21", version: 1, revised: "2026-07-21",
      versions: [{ v: 1, date: "2026-07-21", paper_sha256: recorded }] };
    const out = await emit(a, meta, "2026-09-20");
    expect(out.version).toBe(1);
    expect(out.revised).toBe("2026-07-21");
    expect(out.versions[0]!.paper_sha256).toBe(await fileSha256(join(a.outDir, "paper.tex")));
  });
});
