// The stamp guard: is the DOI a paper was registered under really printed in its PDF?
//
// A published PDF is frozen. If the DOI on page 1 is not the DOI of the record, the artefact
// is permanently wrong, so the matcher is tested for what it must REFUSE as much as for what
// it must find:
//
//   - a LONGER DOI never satisfies a shorter one, whatever the extractor put between the
//     digits (a space, a line wrap, a hyphen, a soft hyphen);
//   - the record id's own digits must be contiguous, while the prefix may arrive glyph by
//     glyph, because that is how a rotated margin stamp is extracted;
//   - "the DOI is not there" (`absent`) and "the file could not be read" (`unavailable`) are
//     different answers, and only a genuine ENOENT means "there is no PDF".
//
// The PDFs are real ones (see zenodo_fixtures.ts): plain text in a `.pdf` file exercises none
// of the extraction path.

import { describe, it, expect, beforeEach } from "vitest";
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import {
  extractPdfText, findDoi, pdfContainsDoi, pdfPage1ContainsDoi, stampShapePresent,
} from "../src/zenodo/pdf_text.js";
import { emptyPdf, makeBundleDir, minimalPdf, notAPdf, unreadablePdf } from "./zenodo_fixtures.js";

let dir: string;

beforeEach(async () => {
  dir = await makeBundleDir();
});

const pdf = (text: string) => writeFile(path.join(dir, "paper.pdf"), minimalPdf(text));

describe("findDoi applies the digit boundary whatever the extractor put between the digits", () => {
  const D = "10.5072/zenodo.99";

  // Gaps where a line wraps are tolerated in the PREFIX; a gap inside the record id is not,
  // because `zenodo.9 9` is as likely to be `.9` followed by a stray digit as a spaced `.99`.
  it.each([
    { why: "rejects a newline between the DOI and an extra digit", text: "doi:10.5072/zenodo.99\n9 rest", found: false },
    { why: "rejects a hyphenated line break before an extra digit", text: "doi:10.5072/zenodo.99-\n9 rest", found: false },
    { why: "rejects a soft hyphen before an extra digit", text: "doi:10.5072/zenodo.99­9", found: false },
    { why: "rejects an extra digit after a plain space", text: "doi:10.5072/zenodo.99 9", found: false },
    { why: "rejects a glyph-spaced DOI whose extra digit wrapped onto the next line", text: "1 0 . 5 0 7 2 / z e n o d o . 9 9\n9", found: false },
    { why: "accepts the DOI followed by a space and a word", text: "doi:10.5072/zenodo.99 Page three", found: true },
    { why: "accepts the DOI followed by a full stop", text: "doi:10.5072/zenodo.99.", found: true },
    { why: "accepts the DOI followed by a newline and a word", text: "doi:10.5072/zenodo.99\nAbstract", found: true },
    { why: "accepts a glyph-spaced PREFIX with a contiguous record id", text: "1 0 . 5 0 7 2 / z e n o d o . 99", found: true },
    { why: "rejects a glyph-spaced prefix whose record id is split", text: "1 0 . 5 0 7 2 / z e n o d o . 9 9", found: false },
    { why: "rejects a longer DOI in front", text: "110.5072/zenodo.99", found: false },
    { why: "rejects a longer DOI in front across a line wrap", text: "1\n10.5072/zenodo.99", found: false },
    { why: "rejects a space inside the record id of an otherwise contiguous DOI", text: "doi:10.5072/zenodo.9 9", found: false },
    { why: "accepts the contiguous DOI inside a stamp line", text: "doi:10.5072/zenodo.99 · [Stat]", found: true },
  ])("$why", ({ text, found }) => {
    expect(findDoi(text, D)).toBe(found);
  });
});

describe("the stamp matcher on the extraction shapes of the pipeline stamp", () => {
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

  // The stamp keeps the DOI away from the end of its line, so a wrapped continuation cannot
  // be read as more of the record id.
  const LAYOUT = "CSWP-2026-008v3 · doi:10.5281/zenodo.99 · [Stat] 27 Aug 2026\n2026 continues here";
  const LAYOUT_LONGER = LAYOUT.replace("zenodo.99 ", "zenodo.999 ");
  // The safe direction, and the reason PyMuPDF is preferred: under gs a digit butted against
  // the DOI is indistinguishable from a longer DOI.
  const GS_DIGIT_ABUT = GS_FRAGMENTS.replace("High-dimensional", "2026 High-dimensional");

  it.each([
    { why: "matches the DOI in the production stamp layout", text: LAYOUT, doi: "10.5281/zenodo.99", found: true },
    { why: "rejects a longer DOI in the production stamp layout", text: LAYOUT_LONGER, doi: "10.5281/zenodo.99", found: false },
    { why: "matches the longer DOI when the longer DOI is the one asked for", text: LAYOUT_LONGER, doi: "10.5281/zenodo.999", found: true },
    { why: "matches the gs-fragmented shape, where body text abuts the DOI", text: GS_FRAGMENTS, doi: DOI, found: true },
    { why: "matches the PyMuPDF single-line shape", text: PYMUPDF_LINE, doi: DOI, found: true },
    { why: "refuses the gs shape when the abutting body text begins with a digit", text: GS_DIGIT_ABUT, doi: DOI, found: false },
    { why: "rejects a longer DOI in the PyMuPDF shape", text: PYMUPDF_LINE.replace(DOI, `${DOI}9`), doi: DOI, found: false },
    { why: "rejects a longer DOI in the gs-fragmented shape", text: GS_FRAGMENTS.replace(DOI, `${DOI}9`), doi: DOI, found: false },
  ])("findDoi $why", ({ text, doi, found }) => {
    expect(findDoi(text, doi)).toBe(found);
  });

  it.each([
    { shape: "the clean PyMuPDF line", text: PYMUPDF_LINE, present: true },
    { shape: "the gs fragments", text: GS_FRAGMENTS, present: false },
  ])("stampShapePresent is $present for $shape", ({ text, present }) => {
    expect(stampShapePresent(text, DOI)).toBe(present);
  });
});

describe("pdfContainsDoi through a real PDF", () => {
  it.each([
    { why: "does not accept a LONGER DOI that merely starts with the expected one", text: "doi:10.5072/zenodo.999", doi: "10.5072/zenodo.99", outcome: "absent" },
    { why: "does not accept a longer DOI whose extra digit was split off by the extractor", text: "doi:10.5072/zenodo.9 9 9", doi: "10.5072/zenodo.99", outcome: "absent" },
    { why: "does not accept a DOI that is a suffix of a longer number", text: "doi:110.5072/zenodo.99", doi: "10.5072/zenodo.99", outcome: "absent" },
    { why: "accepts the exact DOI", text: "doi:10.5072/zenodo.99", doi: "10.5072/zenodo.99", outcome: "present" },
    { why: "accepts the exact DOI followed by an unrelated number", text: "doi:10.5072/zenodo.99 Page 123", doi: "10.5072/zenodo.99", outcome: "present" },
    { why: "accepts a DOI whose PREFIX the extractor spaced out glyph by glyph", text: "d o i : 1 0 . 5 0 7 2 / z e n o d o . 99", doi: "10.5072/zenodo.99", outcome: "present" },
    { why: "accepts the longer DOI when the longer DOI is what was asked for", text: "doi:10.5072/zenodo.999", doi: "10.5072/zenodo.999", outcome: "present" },
    { why: "accepts the DOI in the production stamp layout", text: "CSWP-2026-008v3 · doi:10.5072/zenodo.99 · [Stat] 27 Aug 2026", doi: "10.5072/zenodo.99", outcome: "present" },
  ])("$why", async ({ text, doi, outcome }) => {
    await pdf(text);
    expect((await pdfContainsDoi(path.join(dir, "paper.pdf"), doi)).outcome).toBe(outcome);
  });

  it("reports `absent` for a readable PDF without the DOI", async () => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, minimalPdf("a paper with no stamp"));
    const r = await pdfContainsDoi(p, "10.5072/zenodo.99");
    expect(r.outcome).toBe("absent");
    expect(r).toHaveProperty("method");
  });

  // A LaTeX failure can leave something else at paper.pdf. Text that happens to hold the DOI
  // must not be read as a stamped paper.
  it.each([
    { what: "an empty file", bytes: emptyPdf },
    { what: "a %PDF file with no readable text layer", bytes: unreadablePdf },
    { what: "a file that is not a PDF, even if it contains the DOI", bytes: notAPdf },
  ])("reports `unavailable` for $what", async ({ bytes }) => {
    const p = path.join(dir, "paper.pdf");
    await writeFile(p, bytes());
    expect((await pdfContainsDoi(p, "10.5072/zenodo.99")).outcome).toBe("unavailable");
  });

  it("reports `unavailable` for a missing file", async () => {
    expect((await pdfContainsDoi(path.join(dir, "nope.pdf"), "10.5072/zenodo.99")).outcome)
      .toBe("unavailable");
  });
});

describe("pdfPage1ContainsDoi", () => {
  const DOI = "10.5072/zenodo.99";

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

describe("extractPdfText tells an unreadable PDF from an absent one", () => {
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
});
