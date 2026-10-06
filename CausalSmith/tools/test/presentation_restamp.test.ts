// What a restamp is allowed to do to a paper that is already published, and what it must
// refuse.
//
// The tool exists because a DOI arrives after the PDF was built and has to reach page 1 without
// a re-emit. Everything dangerous about it follows from that: it rewrites files inside a bundle
// whose manuscript is frozen, and a mistake ships a different document under an unchanged
// version number. So the rules under test are:
//
//  1. DRY RUN IS THE DEFAULT and writes nothing — the whole point of previewing 22 papers.
//  2. A FAILED COMPILE LEAVES THE BUNDLE ALONE. Everything happens in a scratch copy first.
//  3. A CHANGED DOCUMENT IS REFUSED. Same page count, same text on pages 2..N, stamp on page 1.
//  4. THE VERSION NEVER MOVES. A restamp recompiles an unchanged manuscript; a bump would
//     re-date a paper nobody edited and contradict a citation already in circulation.
//  5. THE COPY-BACK SET IS CLOSED. Four paper files plus tracked latexmk byproducts — never
//     sections/, proofs/ or the P2 assembly manifest.
//  6. IT IS IDEMPOTENT. latexmk embeds a timestamp, so byte-equality is not available; a second
//     run must still leave the bundle alone rather than churn a binary forever.
//  7. THE COPY-BACK IS ONE FLIP. Staged beside the destination, fsynced, renamed in — PDF last.
//     An interrupt leaves the bundle unchanged or consistently partway, never a truncated
//     `paper.pdf` that the next run then refuses to repair, and never any `*.restamp-tmp` debris.
//  8. P5'S REPORT KEEPS POINTING AT THE MANUSCRIPT IT READ. The pin adoption changes the hash
//     of a file whose content did not change; a review naming the pre-pin hash is re-pointed,
//     and one naming a genuinely different manuscript is not.
//
// `latexmk` and the PDF text extractor are injected. The PDFs are real (if tiny) files, built
// and read by the shared fixtures, so the page-splitting logic has genuine bytes to work on.

import { describe, it, expect, beforeEach } from "vitest";
import { createHash } from "node:crypto";
import { mkdir, mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { multiPagePdf, pdfPageTexts } from "./zenodo_fixtures.js";
import { LatexCompileError } from "../src/presentation/paper_compile.js";
import {
  RESTAMP_TMP_SUFFIX, copyBackCandidates, restampBundle, type RestampOptions,
} from "../src/presentation/restamp.js";

const BUNDLE_ID = "stat_demo_restamp_v1";
const WP_NUMBER = "CSWP-2026-007";
const BODY = ["page two body text", "page three body text"];

let repoRoot: string;
let bundleDir: string;
/** Bumped by the fake latexmk on every run so its PDF is never byte-identical twice. */
let compileNonce: number;

const sha = (buf: Buffer) => createHash("sha256").update(buf).digest("hex");
const readJson = async (p: string) => JSON.parse(await readFile(p, "utf8"));

const META = () => ({
  qid: "stat_demo", spec: "restamp_v1", title: "A demo paper", tldr: "t", abstract: "a",
  area: "Stat", authorship: null, created: "2026-07-21",
  wp_number: WP_NUMBER, version: 2, revised: "2026-08-03",
  versions: [
    { v: 1, date: "2026-07-21", paper_sha256: null },
    { v: 2, date: "2026-08-03", paper_sha256: null as string | null },
  ],
  doi: null as string | null, version_doi: null, score: 8, score_rationale: "kept",
});

/** The shipped paper.tex, unpinned exactly as every backfilled bundle's is. */
const PAPER_TEX = "\\documentclass{article}\n\\input{paper_macros}\n\\date{\\today}\n\\begin{document}x\\end{document}\n";

/** Page 1 as it shipped: no stamp yet. */
const shippedPage1 = "Title page.";

beforeEach(async () => {
  compileNonce = 0;
  repoRoot = path.join(await mkdtemp(path.join(os.tmpdir(), "restamp-repo-")), "CausalSmith");
  bundleDir = path.join(repoRoot, "doc", "presentation", BUNDLE_ID);
  await mkdir(path.join(bundleDir, "sections"), { recursive: true });
  await writeFile(path.join(bundleDir, "paper.tex"), PAPER_TEX, "utf8");
  await writeFile(path.join(bundleDir, "paper_macros.tex"), "% a stale template copy\n", "utf8");
  await writeFile(path.join(bundleDir, "sections", "01_intro.tex"), "intro\n", "utf8");
  await writeFile(path.join(bundleDir, "p2_assembly_manifest.json"), '{"digest":"keepme"}\n', "utf8");
  await writeFile(path.join(bundleDir, "paper.pdf"), multiPagePdf([shippedPage1, ...BODY]));
  // The backfill records the hash of the manuscript as it stands — unpinned. The pin equivalence
  // is what stops a restamp reading the pinned bytes as a new revision.
  const meta = META();
  meta.versions[1]!.paper_sha256 = sha(Buffer.from(PAPER_TEX, "utf8"));
  await writeFile(path.join(bundleDir, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`, "utf8");
  await writeFile(
    path.join(repoRoot, "doc", "presentation", "_wp_registry.json"),
    `${JSON.stringify({ [BUNDLE_ID]: WP_NUMBER }, null, 2)}\n`,
    "utf8",
  );
});

/** A latexmk that reads the generated stamp values and draws them on page 1, as the real
 *  template does. `pages` overrides the body so a test can provoke a reflow. */
function fakeLatexmk(opts: { body?: readonly string[]; page1?: (id: string, doi: string) => string } = {}) {
  return async (dir: string): Promise<void> => {
    const stamp = await readFile(path.join(dir, "paper_stamp.tex"), "utf8");
    const field = (name: string) =>
      new RegExp(`\\\\renewcommand\\*\\{\\\\${name}\\}\\{([^}]*)\\}`).exec(stamp)?.[1] ?? "";
    const id = field("csstampid");
    const doi = field("csstampdoi");
    const page1 = opts.page1
      ? opts.page1(id, doi)
      : `${shippedPage1} ${id}${doi ? ` doi:${doi} ` : " "}[Stat]`;
    compileNonce += 1;
    await writeFile(
      path.join(dir, "paper.pdf"),
      // The nonce makes two compiles of identical sources differ in bytes, as the real
      // latexmk's embedded creation timestamp does.
      multiPagePdf([page1, ...(opts.body ?? BODY)], `%nonce ${compileNonce}\n`),
    );
    await writeFile(path.join(dir, "paper.aux"), `aux ${compileNonce}\n`, "utf8");
    await writeFile(path.join(dir, "paper.log"), `log ${compileNonce}\n`, "utf8");
  };
}

const readPages = async (p: string) => ({ pages: pdfPageTexts(await readFile(p)), method: "fixture" });

function opts(over: Partial<RestampOptions> = {}): RestampOptions {
  return {
    repoRoot,
    seriesPrefix: "CSWP",
    today: "2026-09-21",
    compile: fakeLatexmk(),
    readPages,
    trackedFiles: async () => new Set(["paper.tex", "paper.pdf", "paper_macros.tex", "meta.json"]),
    ...over,
  };
}

/** Every file in the bundle with its hash — minus the lock sentinels, which are gitignored
 *  byproducts of taking the lock and are not part of "the bundle". */
async function snapshot(): Promise<Record<string, string>> {
  const out: Record<string, string> = {};
  for (const entry of await readdir(bundleDir, { recursive: true, withFileTypes: true })) {
    if (!entry.isFile()) continue;
    const rel = path.relative(bundleDir, path.join(entry.parentPath, entry.name));
    if (rel.startsWith(".emit.lock") || rel.startsWith(".meta.lock")) continue;
    out[rel] = sha(await readFile(path.join(bundleDir, rel)));
  }
  return out;
}

/** Staging files the copy-back should never leave behind. */
async function strayTmp(): Promise<string[]> {
  return (await readdir(bundleDir)).filter((n) => n.endsWith(RESTAMP_TMP_SUFFIX)).sort();
}

describe("restampBundle — dry run", () => {
  it("compiles, verifies and writes absolutely nothing", async () => {
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts());
    expect(result.verdict).toBe("would-write");
    expect(result.ok).toBe(true);
    expect(result.wpNumber).toBe(WP_NUMBER);
    expect(result.version).toBe(2);
    expect(result.pages).toBe(3);
    expect(result.written).toEqual([]);
    expect(await snapshot()).toEqual(before);
    // in particular: the stamp file is NOT created in the real bundle
    expect(before["paper_stamp.tex"]).toBeUndefined();
  });

  it("refuses a bundle whose working-paper number the registry has never recorded", async () => {
    await writeFile(path.join(repoRoot, "doc", "presentation", "_wp_registry.json"), "{}\n", "utf8");
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts());
    expect(result.verdict).toBe("blocked");
    expect(result.ok).toBe(false);
    expect(result.detail).toMatch(/would MINT one/);
    // The refusal is the point: a preview must not allocate a permanent number.
    expect(await readFile(path.join(repoRoot, "doc", "presentation", "_wp_registry.json"), "utf8")).toBe("{}\n");
    expect(await snapshot()).toEqual(before);
  });
});

describe("restampBundle — refusals", () => {
  it("leaves the bundle untouched when latexmk fails", async () => {
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts({
      write: true,
      compile: async (dir) => { throw new LatexCompileError(dir, "! Undefined control sequence.\nl.42 \\nope"); },
    }));
    expect(result.verdict).toBe("compile-failed");
    expect(result.ok).toBe(false);
    expect(result.detail).toMatch(/Undefined control sequence/);
    expect(await snapshot()).toEqual(before);
  });

  it("refuses when the recompile changed the page count", async () => {
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts({
      write: true,
      compile: fakeLatexmk({ body: [...BODY, "an extra page nobody asked for"] }),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/page count changed: the shipped paper.pdf has 3 page\(s\), the recompile has 4/);
    expect(await snapshot()).toEqual(before);
  });

  it("refuses when a later page's text moved, and names the first one", async () => {
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts({
      write: true,
      compile: fakeLatexmk({ body: [BODY[0]!, "page three body text REFLOWED"] }),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/^page 3 differs from the shipped PDF/);
    expect(await snapshot()).toEqual(before);
  });

  it("refuses when page 1 came back without the stamp", async () => {
    const result = await restampBundle(bundleDir, opts({
      write: true,
      compile: fakeLatexmk({ page1: () => shippedPage1 }),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/does not carry the stamp "CSWP-2026-007v2"/);
  });

  it("refuses when a published DOI is in meta.json but not on page 1", async () => {
    const meta = await readJson(path.join(bundleDir, "meta.json"));
    meta.doi = "10.5281/zenodo.17158230";
    await writeFile(path.join(bundleDir, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`, "utf8");
    const result = await restampBundle(bundleDir, opts({
      write: true,
      compile: fakeLatexmk({ page1: (id) => `${shippedPage1} ${id} [Stat]` }),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/does not carry the published DOI 10.5281\/zenodo.17158230/);
  });
});

describe("restampBundle — writing", () => {
  it("adopts the pinned hash without bumping the version of a backfilled bundle", async () => {
    const result = await restampBundle(bundleDir, opts({ write: true }));
    expect(result.verdict).toBe("written");
    const meta = await readJson(path.join(bundleDir, "meta.json"));
    // The manuscript did not change; only its date pin did. v2 stays v2, dated as before.
    expect(meta.version).toBe(2);
    expect(meta.revised).toBe("2026-08-03");
    expect(meta.versions).toHaveLength(2);
    // ...and the recorded hash now describes the file that is actually on disk.
    const pinned = await readFile(path.join(bundleDir, "paper.tex"));
    expect(pinned.toString("utf8")).toContain("\\date{\\cspaperdate}");
    expect(meta.versions[1].paper_sha256).toBe(sha(pinned));
    // Keys owned by other writers survive.
    expect(meta.score).toBe(8);
    expect(meta.doi).toBeNull();
  });

  it("stamps a published DOI onto page 1 and reports it", async () => {
    const meta = await readJson(path.join(bundleDir, "meta.json"));
    meta.doi = "10.5281/zenodo.17158230";
    await writeFile(path.join(bundleDir, "meta.json"), `${JSON.stringify(meta, null, 2)}\n`, "utf8");
    const result = await restampBundle(bundleDir, opts({ write: true }));
    expect(result.verdict).toBe("written");
    expect(result.doi).toBe("10.5281/zenodo.17158230");
    const pages = pdfPageTexts(await readFile(path.join(bundleDir, "paper.pdf")));
    expect(pages[0]).toContain("doi:10.5281/zenodo.17158230");
    expect(pages[0]).toContain("CSWP-2026-007v2");
  });

  it("copies back exactly the four paper files plus tracked byproducts, and nothing else", async () => {
    const before = await snapshot();
    const result = await restampBundle(bundleDir, opts({
      write: true,
      // paper.aux is tracked here, paper.log is not — the real bundles gitignore both.
      trackedFiles: async () => new Set(["paper.tex", "paper.pdf", "paper_macros.tex", "paper.aux"]),
      compile: async (dir) => {
        await fakeLatexmk()(dir);
        // A compile that also scribbled on files it does not own. None of these may travel.
        await writeFile(path.join(dir, "p2_assembly_manifest.json"), '{"digest":"TAMPERED"}\n', "utf8");
        await writeFile(path.join(dir, "sections", "01_intro.tex"), "TAMPERED\n", "utf8");
        await writeFile(path.join(dir, "zenodo.json"), '{"sandbox":"TAMPERED"}\n', "utf8");
      },
    }));
    expect(result.written).toEqual(["paper.pdf", "paper.tex", "paper_macros.tex", "paper_stamp.tex", "paper.aux"]);
    const after = await snapshot();
    expect(Object.keys(after).sort()).toEqual(
      [...Object.keys(before), "paper_stamp.tex", "paper.aux"].sort(),
    );
    expect(after["p2_assembly_manifest.json"]).toBe(before["p2_assembly_manifest.json"]);
    expect(after[path.join("sections", "01_intro.tex")]).toBe(before[path.join("sections", "01_intro.tex")]);
    expect(after["paper.log"]).toBeUndefined();
    expect(after["zenodo.json"]).toBeUndefined();
  });

  it("offers a closed candidate set that grows only with tracked byproducts", () => {
    expect(copyBackCandidates(new Set())).toEqual(["paper.pdf", "paper.tex", "paper_macros.tex", "paper_stamp.tex"]);
    expect(copyBackCandidates(new Set(["paper.bbl", "outline.md"]))).toEqual(
      ["paper.pdf", "paper.tex", "paper_macros.tex", "paper_stamp.tex", "paper.bbl"],
    );
  });

  it("is idempotent: the second run replaces nothing, timestamps and all", async () => {
    expect((await restampBundle(bundleDir, opts({ write: true }))).verdict).toBe("written");
    const after1 = await snapshot();
    const second = await restampBundle(bundleDir, opts({ write: true }));
    expect(second.verdict).toBe("unchanged");
    expect(second.ok).toBe(true);
    expect(second.written).toEqual([]);
    // The fake latexmk produced DIFFERENT BYTES on the second run (the nonce moved), and the
    // shipped PDF still was not touched — which is the behaviour that keeps a 2 MB binary out
    // of every future diff.
    expect(compileNonce).toBe(2);
    expect(await snapshot()).toEqual(after1);
  });

  it("dry-runs clean after a write, reporting nothing left to do", async () => {
    await restampBundle(bundleDir, opts({ write: true }));
    const before = await snapshot();
    const preview = await restampBundle(bundleDir, opts());
    expect(preview.verdict).toBe("unchanged");
    expect(await snapshot()).toEqual(before);
  });
});

describe("restampBundle — locking", () => {
  it("runs inside a lock the caller already holds instead of waiting for itself", async () => {
    const { withBundleEmitLock } = await import("../src/presentation/emit_lock.js");
    // The emit lock is NOT re-entrant: without either the explicit flag or the async-context
    // check, this would sit in the bounded retry loop waiting for a lock it is holding.
    const result = await withBundleEmitLock(
      bundleDir,
      () => restampBundle(bundleDir, opts({ write: true, emitLockHeld: true })),
      { wait: false },
    );
    expect(result.verdict).toBe("written");
    // ...and the same holds without the flag, from the async context alone.
    const again = await withBundleEmitLock(
      bundleDir,
      () => restampBundle(bundleDir, opts({ write: true })),
      { wait: false },
    );
    expect(again.verdict).toBe("unchanged");
  });
});

// ---------------------------------------------------------------------------
// The copy-back is one atomic flip (audit: MAJOR)
//
// `copyFile` TRUNCATES its destination and then streams into it. An interrupt, an ENOSPC or an
// NFS EIO in the middle therefore left a real, shipped `paper.pdf` truncated — unreadable, which
// makes the NEXT restamp's verification fail and refuse to repair it, and which in git looks like
// an ordinary restamp of a binary. So the flip is staged-and-renamed, PDF last.

describe("restampBundle — the copy-back is atomic", () => {
  it("leaves the bundle byte-identical when the flip dies before the first rename", async () => {
    const before = await snapshot();
    const outcome = await restampBundle(bundleDir, opts({
      write: true,
      onFlipStep: (step) => { if (step.phase === "staged") throw new Error("the node went down"); },
    })).then(() => null, (e: Error) => e);
    expect(outcome).toBeInstanceOf(Error);
    // Every byte of the shipped bundle survived — including the PDF, which `copyFile` would by
    // then have truncated to whatever had landed.
    expect(await snapshot()).toEqual(before);
    expect(await strayTmp()).toEqual([]);
  });

  it("never publishes a new PDF beside old sources, and heals on the next run", async () => {
    const before = await snapshot();
    let renames = 0;
    const outcome = await restampBundle(bundleDir, opts({
      write: true,
      onFlipStep: (step) => {
        if (step.phase === "rename" && renames++ === 1) throw new Error("EIO on the share");
      },
    })).then(() => null, (e: Error) => e);
    expect(outcome).toBeInstanceOf(Error);

    const halfway = await snapshot();
    // One source file made it across...
    expect(halfway["paper.tex"]).not.toBe(before["paper.tex"]);
    // ...and the PDF did NOT, because it is renamed last. A reader holding this bundle has the
    // document that shipped, intact, rather than a new page 1 the sources cannot reproduce.
    expect(halfway["paper.pdf"]).toBe(before["paper.pdf"]);
    expect(await strayTmp()).toEqual([]);

    // The recovery procedure is "run it again".
    const healed = await restampBundle(bundleDir, opts({ write: true }));
    expect(healed.verdict).toBe("written");
    expect(await strayTmp()).toEqual([]);
    const page1 = pdfPageTexts(await readFile(path.join(bundleDir, "paper.pdf")))[0]!;
    expect(page1).toContain("CSWP-2026-007v2");
    const meta = await readJson(path.join(bundleDir, "meta.json"));
    expect(meta.version).toBe(2);
    expect(meta.versions[1].paper_sha256).toBe(sha(await readFile(path.join(bundleDir, "paper.tex"))));
  });

  it("sweeps *.restamp-tmp debris at the START of a run — a dry run included", async () => {
    // What a run killed between staging and rename leaves behind. It never reached its own
    // `finally`, so only the next run can clear it — otherwise `git status` reports it forever.
    const debris = path.join(bundleDir, `paper.pdf.4242${RESTAMP_TMP_SUFFIX}`);
    await writeFile(debris, "the first 300 bytes of a PDF\n", "utf8");
    const result = await restampBundle(bundleDir, opts());
    expect(result.verdict).toBe("would-write");
    expect(await strayTmp()).toEqual([]);
  });
});

describe("restampBundle — an unreadable PDF is diagnosed, not just refused", () => {
  const truncated = "%PDF-1.4\nthe first kilobyte of a copy that never finished";

  it("names the git command that restores a corrupt SHIPPED paper.pdf", async () => {
    await writeFile(path.join(bundleDir, "paper.pdf"), truncated, "utf8");
    const result = await restampBundle(bundleDir, opts({
      write: true,
      headPaperPdf: async () => multiPagePdf([shippedPage1, ...BODY]),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.ok).toBe(false);
    expect(result.detail).toMatch(/SHIPPED paper\.pdf is corrupt/);
    expect(result.detail).toContain(`git checkout -- ${path.join(bundleDir, "paper.pdf")}`);
  });

  it("keeps the generic message when git holds no readable PDF either", async () => {
    await writeFile(path.join(bundleDir, "paper.pdf"), truncated, "utf8");
    const result = await restampBundle(bundleDir, opts({ write: true, headPaperPdf: async () => null }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/^shipped PDF: /);
    expect(result.detail).not.toMatch(/git checkout/);
  });

  it("gives a zero-page recompile a verdict rather than a TypeError", async () => {
    const result = await restampBundle(bundleDir, opts({
      write: true,
      // `extractPdfPages` reports a zero-page document as an EMPTY array, not as a failure.
      // Indexing page 1 of it handed `undefined` to the token check and threw out of the verifier.
      readPages: async (p) => (p.startsWith(bundleDir)
        ? { pages: pdfPageTexts(await readFile(p)), method: "fixture" }
        : { pages: [], method: "fixture" }),
    }));
    expect(result.verdict).toBe("verify-failed");
    expect(result.detail).toMatch(/recompiled PDF has 0 pages/);
  });
});

// ---------------------------------------------------------------------------
// P5's report and the pin adoption (audit: MAJOR)
//
// A backfilled bundle records the UNPINNED hash. The restamp pins `\date` and adopts the pinned
// hash into versions[-1].paper_sha256 — the same manuscript, a different hash. The site compares
// `p5_review.json`'s `manuscript_sha256` with that field by raw equality, so a report that read
// exactly this draft would be captioned "written for an earlier draft".

describe("restampBundle — p5_review.json follows the pin", () => {
  const REVIEW = (sha256: string) => ({
    score: 8,
    manuscript_sha256: sha256,
    reviewed_at: "2026-08-04",
    summary: "a critique that must survive verbatim",
  });
  const reviewPath = () => path.join(bundleDir, "p5_review.json");
  const unpinnedSha = () => sha(Buffer.from(PAPER_TEX, "utf8"));

  it("re-points a review that names the same manuscript under its pre-pin hash", async () => {
    await writeFile(reviewPath(), `${JSON.stringify(REVIEW(unpinnedSha()), null, 2)}\n`, "utf8");
    const result = await restampBundle(bundleDir, opts({ write: true }));
    expect(result.verdict).toBe("written");
    expect(result.written).toContain("p5_review.json");
    expect(result.detail).toMatch(/p5_review\.json manuscript_sha256 re-pointed/);

    const meta = await readJson(path.join(bundleDir, "meta.json"));
    const review = await readJson(reviewPath());
    // The two hashes now agree, which is what the site reads as "fresh".
    expect(review.manuscript_sha256).toBe(meta.versions[1].paper_sha256);
    expect(review.manuscript_sha256).toBe(sha(await readFile(path.join(bundleDir, "paper.tex"))));
    // ONLY that field moved — every other key, and the file's formatting, are as they were.
    expect(review.score).toBe(8);
    expect(review.reviewed_at).toBe("2026-08-04");
    expect(review.summary).toBe("a critique that must survive verbatim");
    const raw = await readFile(reviewPath(), "utf8");
    expect(raw.endsWith("}\n")).toBe(true);
    expect(raw).toContain('\n  "score": 8,');
  });

  it("announces it in the dry run without writing it", async () => {
    await writeFile(reviewPath(), `${JSON.stringify(REVIEW(unpinnedSha()), null, 2)}\n`, "utf8");
    const before = await snapshot();
    const preview = await restampBundle(bundleDir, opts());
    expect(preview.verdict).toBe("would-write");
    expect(preview.detail).toContain("p5_review.json");
    expect(await snapshot()).toEqual(before);
  });

  it("leaves a review of a genuinely DIFFERENT manuscript exactly as it is", async () => {
    const other = sha(Buffer.from("a manuscript this bundle never held", "utf8"));
    const body = `${JSON.stringify(REVIEW(other), null, 2)}\n`;
    await writeFile(reviewPath(), body, "utf8");
    const result = await restampBundle(bundleDir, opts({ write: true }));
    expect(result.verdict).toBe("written");
    expect(result.written).not.toContain("p5_review.json");
    // Saying "this report predates the current draft" is the field's whole job.
    expect(await readFile(reviewPath(), "utf8")).toBe(body);
  });

  it("never touches p5_review_history/", async () => {
    await writeFile(reviewPath(), `${JSON.stringify(REVIEW(unpinnedSha()), null, 2)}\n`, "utf8");
    const archive = path.join(bundleDir, "p5_review_history", "2026-08-04.json");
    await mkdir(path.dirname(archive), { recursive: true });
    const archived = `${JSON.stringify(REVIEW(unpinnedSha()), null, 2)}\n`;
    await writeFile(archive, archived, "utf8");
    await restampBundle(bundleDir, opts({ write: true }));
    // An archive is a record of what was written when it was written; re-pointing it would be a
    // falsification, not a repair.
    expect(await readFile(archive, "utf8")).toBe(archived);
  });
});
