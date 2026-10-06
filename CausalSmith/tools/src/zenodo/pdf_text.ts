/** Check that a compiled PDF really carries the DOI it is about to be published under.
 *
 * WHY THIS GUARD EXISTS. Plan decision 5 stamps the concept DOI onto page 1 of the PDF,
 * and decision 6 makes that DOI the one every citation of the paper uses. If the
 * stamped DOI and the registered DOI ever disagree, the artefact is permanently wrong:
 * the PDF is frozen at publish time and the printed DOI points somewhere else.
 *
 * TWO THINGS THE FIRST VERSION GOT WRONG, both found by audit:
 *
 *  1. It matched the DOI as a bare SUBSTRING, so a PDF stamped `10.5072/zenodo.999`
 *     satisfied a check for `10.5072/zenodo.99`. Record ids are consecutive integers,
 *     so "the DOI next door is a prefix of mine" is not a curiosity — it is the common
 *     case. Matching now requires digit boundaries; see {@link findDoi}.
 *  2. Its fallback extractor returned the file's raw bytes as "text", so extraction
 *     essentially never failed and `unavailable` was unreachable. A corrupt PDF then
 *     reported `absent` — a confident wrong answer. Extraction now reports success
 *     only when something actually produced a text layer.
 *
 * EXTRACTION IS BEST EFFORT, AND SAYS SO. Three strategies, in order of fidelity:
 *   1. `pdftotext` (poppler) — the reference implementation.
 *   2. `gs -sDEVICE=txtwrite` (ghostscript) — present on this cluster where poppler is
 *      not; verified against a real bundle PDF.
 *   3. A dependency-free fallback: inflate the PDF's Flate streams with `node:zlib` and
 *      scan them, plus the uncompressed text-showing operators and `/URI` link actions.
 *      The stamp is a hyperlink (decision 5) and link annotations are frequently
 *      uncompressed, so this finds the DOI more often than it has any right to.
 *
 * `unavailable` is never treated as "absent" by callers: publish refuses on both, but
 * with different messages, because "the DOI is not in the PDF" and "nobody could read
 * the PDF" call for different fixes.
 */

import { execFile } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";
import zlib from "node:zlib";
import { tryPythonCommand } from "../shared/python.js";

const execFileAsync = promisify(execFile);

/** Does page 1 carry the stamp in its intended SHAPE — `doi:<DOI> ·` — as opposed to
 *  merely containing the DOI somewhere? Only meaningful when the extractor preserved
 *  the line (PyMuPDF); a fragmenting extractor reports "unknown". */
export type StampShape = "matched" | "not-found" | "unknown";

export type StampCheck =
  | { readonly outcome: "present"; readonly method: string; readonly shape?: StampShape }
  | { readonly outcome: "absent"; readonly method: string; readonly shape?: StampShape }
  /** `code` is the filesystem errno when the file could not be READ at all. Only
   *  `ENOENT` means "there is no PDF"; every other code means "there is a PDF and we
   *  could not look inside it", which is a different, much weaker fact. */
  | { readonly outcome: "unavailable"; readonly reason: string; readonly code?: string };

/** Result of {@link extractPdfText}: text, or a reason plus the errno when the failure
 *  was a read error rather than an extraction one. */
export type PdfTextResult =
  | { readonly text: string; readonly method: string; readonly code?: undefined }
  | { readonly text: null; readonly reason: string; readonly code?: string };

/** Escape a literal for use inside a RegExp. */
function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/**
 * What a PDF text extractor can insert between two characters that were adjacent on
 * the page: any run of whitespace (a line wrap, a column break, kerning rendered as
 * spaces) optionally around a hyphen, which is how a line-broken token is printed.
 *
 * This is used BOTH to join the characters of the DOI (so a wrapped DOI still matches)
 * and, crucially, inside the boundary guards — because a gap that can hide part of the
 * DOI can equally hide the extra digit that makes it a DIFFERENT DOI.
 */
const GAP = "[\\s\\u00AD]*(?:-[\\s\\u00AD]*)?";
/** The same thing, length-bounded, for the lookbehind. */
const GAP_BOUNDED = "[\\s\\u00AD]{0,8}-?[\\s\\u00AD]{0,8}";

/**
 * Is `doi` present in `text` as a COMPLETE token?
 *
 * Two passes over the same boundary rule.
 *
 * **Boundary.** The DOI must not be preceded or followed by a digit, where "followed"
 * looks THROUGH whitespace, soft hyphens and a hyphenated line break — because a gap
 * that can hide part of the DOI can equally hide the extra digit that makes it a
 * different DOI. `…zenodo.99\n9` is `.999` to a reader and must not satisfy a check for
 * `.99`. The cost is a false negative when a DOI is genuinely followed by an unrelated
 * number on the next line; that refuses a publish a human can re-check, whereas a false
 * positive registers a paper under a DOI it does not print. (The pipeline stamp is laid
 * out so the DOI is never the last token on its line, which avoids the case entirely.)
 *
 * **Pass 1** matches the DOI exactly as written. **Pass 2** allows gaps between the
 * characters of the PREFIX only, for a DOI broken across a line or rendered glyph by
 * glyph — the record id's own digits must still be contiguous in both passes.
 */
export function findDoi(text: string, doi: string): boolean {
  const trimmed = doi.trim();
  if (!trimmed) return false;

  // The record id is the part that distinguishes one DOI from its neighbour, so its
  // digits must appear CONTIGUOUSLY. A gap there is not a line-wrap artifact worth
  // tolerating: `zenodo.9 9` is as likely to be `.9` followed by a stray `9` as it is a
  // spaced-out `.99`, and guessing wrong publishes a paper under a DOI it does not
  // print. Gaps elsewhere in the string are fine — that is where wrapping happens.
  const m = /^(.*?)(\d+)$/.exec(trimmed);
  const head = m ? m[1] : trimmed;
  const tail = m ? m[2] : "";

  const lead = `(?<![0-9])(?<![0-9]${GAP_BOUNDED})`;
  const trail = `(?!${GAP}[0-9])`;
  const headExact = [...head].map(escapeRe).join("");
  const headGappy = [...head].map(escapeRe).join(GAP);
  const tailExact = escapeRe(tail);

  if (new RegExp(`${lead}${headExact}${tailExact}${trail}`).test(text)) return true;
  // A gap is allowed between the prefix and the record id — that is a line wrap — but
  // never INSIDE the record id.
  return new RegExp(`${lead}${headGappy}${GAP}${tailExact}${trail}`).test(text);
}

/**
 * PyMuPDF, the PREFERRED extractor.
 *
 * WHY IT IS FIRST. The page-1 stamp is set rotated in the left margin, and ghostscript's
 * `txtwrite` does not keep it together: it emits text in y-bands, so the stamp arrives
 * as three fragments interleaved with body text —
 *
 *     [Stat]               radius σ. The selector attaining…
 *     doi:10.5281/zenodo.17158230High-dimensional discrete adjustment creates…
 *     CSWP-2026-008v3
 *
 * — with body text butted directly against the DOI. That is survivable (the matcher's
 * boundary rule only refuses when the following character is a DIGIT) but it is luck:
 * a sentence beginning with a number would refuse a correctly stamped paper. PyMuPDF
 * returns the stamp as one clean string, `CSWP-…v3 · doi:… · [Stat] 27 Aug 2026`, which
 * is both matchable and checkable for shape.
 *
 * Optional, like ghostscript: no package.json dependency, and absence just falls
 * through to the next extractor.
 */
async function viaPyMuPdf(pdfPath: string): Promise<string | null> {
  const py = tryPythonCommand();
  if (!py) return null;
  // `fitz` is the legacy module name and warns on modern builds; prefer `pymupdf`.
  const script =
    "import sys\n" +
    "try:\n" +
    "    import pymupdf\n" +
    "except Exception:\n" +
    "    try:\n" +
    "        import fitz as pymupdf\n" +
    "    except Exception:\n" +
    "        sys.exit(3)\n" +
    "doc = pymupdf.open(sys.argv[1])\n" +
    "sys.stdout.write('\\n'.join(p.get_text() for p in doc))\n";
  try {
    const { stdout } = await execFileAsync(py.bin, [...py.prefixArgs, "-c", script, pdfPath], {
      maxBuffer: 64 * 1024 * 1024,
      timeout: 300_000,
    });
    return stdout;
  } catch {
    return null;
  }
}

async function viaPdftotext(pdfPath: string): Promise<string | null> {
  try {
    const { stdout } = await execFileAsync("pdftotext", ["-q", "-layout", pdfPath, "-"], {
      maxBuffer: 64 * 1024 * 1024,
      timeout: 120_000,
    });
    return stdout;
  } catch {
    return null;
  }
}

async function viaGhostscript(pdfPath: string): Promise<string | null> {
  let dir: string | null = null;
  try {
    dir = await mkdtemp(path.join(os.tmpdir(), "zenodo-pdftext-"));
    const out = path.join(dir, "text.txt");
    await execFileAsync(
      "gs",
      ["-q", "-dNOPAUSE", "-dBATCH", "-dSAFER", "-sDEVICE=txtwrite", `-sOutputFile=${out}`, pdfPath],
      { maxBuffer: 64 * 1024 * 1024, timeout: 300_000 },
    );
    return await readFile(out, "utf8");
  } catch {
    return null;
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

/**
 * Last-resort extraction with no external tools.
 *
 * Returns null when the file yields NO evidence of a text layer. Returning the raw
 * bytes unconditionally — which is what this used to do — makes every corrupt file look
 * like a readable PDF that simply lacks the DOI.
 */
function viaInflate(bytes: Buffer): string | null {
  const raw = bytes.toString("latin1");
  const parts: string[] = [];

  // Uncompressed evidence: text-showing operators and link-annotation URIs.
  const showing = raw.match(/\((?:[^()\\]|\\.)*\)\s*T[Jj]/g);
  if (showing) parts.push(showing.join("\n"));
  const uris = raw.match(/\/URI\s*\((?:[^()\\]|\\.)*\)/g);
  if (uris) parts.push(uris.join("\n"));

  let inflatedAny = false;
  const marker = Buffer.from("stream");
  let from = 0;
  for (;;) {
    const at = bytes.indexOf(marker, from);
    if (at === -1) break;
    let start = at + marker.length;
    if (bytes[start] === 0x0d) start += 1;
    if (bytes[start] === 0x0a) start += 1;
    const end = bytes.indexOf(Buffer.from("endstream"), start);
    from = end === -1 ? start : end + 1;
    if (end === -1) break;
    const chunk = bytes.subarray(start, end);
    if (chunk.length === 0 || chunk.length > 32 * 1024 * 1024) continue;
    try {
      parts.push(zlib.inflateSync(chunk).toString("latin1"));
      inflatedAny = true;
    } catch {
      // Not a Flate stream (an image, a raw font, an object stream with a filter we do
      // not implement). Skipping is correct: the text layers are Flate.
    }
  }

  if (!inflatedAny && parts.length === 0) return null;
  const text = parts.join("\n");
  return text.trim() ? text : null;
}

/** Text of `pdfPath` by whichever strategy works, or null with the reason. */
export async function extractPdfText(pdfPath: string): Promise<PdfTextResult> {
  let bytes: Buffer;
  try {
    bytes = await readFile(pdfPath);
  } catch (err) {
    // The errno is carried out, not flattened into prose. A caller deciding whether a
    // DOI can safely be discarded must be able to tell ENOENT ("no such file, so
    // nothing can be stamped") from EACCES/EIO/EISDIR ("the file is there and we
    // cannot see inside it"), and a message string cannot be asked that question.
    const code = (err as NodeJS.ErrnoException).code ?? "EUNKNOWN";
    return { text: null, code, reason: `${pdfPath} could not be read (${code})` };
  }
  if (bytes.length === 0) return { text: null, reason: `${pdfPath} is empty (0 bytes)` };
  // A missing `%PDF` header means the compile left something else here — a log, an
  // error page, a truncated download. Reading text out of it and calling the result a
  // stamp check would be the worst kind of pass.
  if (!bytes.subarray(0, 1024).toString("latin1").includes("%PDF-")) {
    return { text: null, reason: `${pdfPath} is not a PDF (no %PDF- header)` };
  }

  const mupdf = await viaPyMuPdf(pdfPath);
  if (mupdf && mupdf.trim()) return { text: mupdf, method: "PyMuPDF" };
  const poppler = await viaPdftotext(pdfPath);
  if (poppler && poppler.trim()) return { text: poppler, method: "pdftotext" };
  const gs = await viaGhostscript(pdfPath);
  if (gs && gs.trim()) return { text: gs, method: "ghostscript (gs -sDEVICE=txtwrite)" };
  const fallback = viaInflate(bytes);
  if (fallback) return { text: fallback, method: "node:zlib stream scan (best effort)" };

  return {
    text: null,
    reason:
      `no text could be extracted from ${pdfPath}. None of PyMuPDF, pdftotext or ghostscript ` +
      `is available or able to read it, and it contains no readable text layer`,
  };
}

// ---------------------------------------------------------------------------
// per-PAGE text (the restamp verifier)

/** Page-by-page text, or a reason nobody could produce it. */
export type PdfPagesResult =
  | { readonly pages: readonly string[]; readonly method: string; readonly reason?: undefined }
  | { readonly pages: null; readonly method?: undefined; readonly reason: string };

/**
 * The text of each page, in order.
 *
 * {@link extractPdfText} deliberately flattens a document to one string — a DOI is a DOI wherever
 * it appears. The restamp verifier asks a strictly harder question: page 1 must have GAINED the
 * stamp while pages 2..N must be UNCHANGED, and answering that needs the page boundaries, so this
 * is a separate function rather than a flag on the other one.
 *
 * Only the two extractors that really delimit pages are used. PyMuPDF is asked for its own page
 * count first and then for the pages, so a zero-page document and a one-page document with no text
 * cannot be confused (both would otherwise arrive as one empty string). Ghostscript's `txtwrite`
 * writes a form feed after every page, which is enough; the dependency-free stream scan in
 * {@link extractPdfText} is NOT used here, because it cannot tell one page from the next and a
 * page-boundary check built on a guess is worse than an honest "cannot tell".
 */
export async function extractPdfPages(pdfPath: string): Promise<PdfPagesResult> {
  let bytes: Buffer;
  try {
    bytes = await readFile(pdfPath);
  } catch (err) {
    const code = (err as NodeJS.ErrnoException).code ?? "EUNKNOWN";
    return { pages: null, reason: `${pdfPath} could not be read (${code})` };
  }
  if (bytes.length === 0) return { pages: null, reason: `${pdfPath} is empty (0 bytes)` };
  if (!bytes.subarray(0, 1024).toString("latin1").includes("%PDF-")) {
    return { pages: null, reason: `${pdfPath} is not a PDF (no %PDF- header)` };
  }

  const py = tryPythonCommand();
  if (py) {
    // The count is emitted FIRST and the pages after it, all separated by form feeds, so the
    // reader never has to infer how many pages an empty join stood for.
    const script =
      "import sys\n" +
      "try:\n" +
      "    import pymupdf\n" +
      "except Exception:\n" +
      "    try:\n" +
      "        import fitz as pymupdf\n" +
      "    except Exception:\n" +
      "        sys.exit(3)\n" +
      "doc = pymupdf.open(sys.argv[1])\n" +
      "sys.stdout.write(str(doc.page_count))\n" +
      "for p in doc:\n" +
      "    sys.stdout.write('\\f')\n" +
      "    sys.stdout.write(p.get_text())\n";
    try {
      const { stdout } = await execFileAsync(py.bin, [...py.prefixArgs, "-c", script, pdfPath], {
        maxBuffer: 64 * 1024 * 1024,
        timeout: 300_000,
      });
      const parts = stdout.split("\f");
      const count = Number(parts[0]);
      if (Number.isInteger(count) && count === parts.length - 1) {
        return { pages: parts.slice(1), method: "PyMuPDF" };
      }
    } catch {
      // No PyMuPDF, or it could not open the file: fall through to ghostscript.
    }
  }

  let dir: string | null = null;
  try {
    dir = await mkdtemp(path.join(os.tmpdir(), "restamp-pdfpages-"));
    const out = path.join(dir, "text.txt");
    await execFileAsync(
      "gs",
      ["-q", "-dNOPAUSE", "-dBATCH", "-dSAFER", "-sDEVICE=txtwrite", `-sOutputFile=${out}`, pdfPath],
      { maxBuffer: 64 * 1024 * 1024, timeout: 300_000 },
    );
    const text = await readFile(out, "utf8");
    const parts = text.split("\f");
    // `txtwrite` terminates every page, so the split leaves one trailing empty chunk. Dropping
    // more than that would silently lose a genuinely blank final page.
    if (parts.length > 1 && parts[parts.length - 1] === "") parts.pop();
    return { pages: parts, method: "ghostscript (gs -sDEVICE=txtwrite)" };
  } catch {
    return {
      pages: null,
      reason:
        `page-by-page text could not be extracted from ${pdfPath}: neither PyMuPDF ` +
        `(pip install pymupdf) nor ghostscript is available or able to read it. Both keep page ` +
        `boundaries; the other extractors do not, so there is no safe fallback here`,
    };
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

/** Does `pdfPath` contain `doi`? See {@link StampCheck}: "no" and "cannot tell" are
 *  different answers and callers must treat them differently. */
export async function pdfContainsDoi(pdfPath: string, doi: string): Promise<StampCheck> {
  if (!doi.trim()) return { outcome: "unavailable", reason: `"${doi}" is not a DOI to look for` };
  const extracted = await extractPdfText(pdfPath);
  if (extracted.text === null) {
    return { outcome: "unavailable", reason: extracted.reason, code: extracted.code };
  }
  // The shape check is corroboration, never the decision: publish proceeds on the
  // strict DOI match. It is recorded so the operator can see whether the stamp line
  // itself was recognised or only the identifier inside it.
  const shape: StampShape = extracted.method === "PyMuPDF"
    ? (stampShapePresent(extracted.text, doi) ? "matched" : "not-found")
    : "unknown";
  return findDoi(extracted.text, doi)
    ? { outcome: "present", method: extracted.method, shape }
    : { outcome: "absent", method: extracted.method, shape };
}

/**
 * Does PAGE 1 of `pdfPath` carry `doi`? The gate the publish path uses.
 *
 * The stamp is drawn on page 1 and nowhere else, so page 1 is the only place a positive answer
 * means anything. {@link pdfContainsDoi} flattens the document, and a bibliography entry, an
 * acknowledgement or a related-work citation that happens to name the concept DOI therefore
 * satisfied it — the gate passed on a paper whose own page 1 was unstamped, which is exactly the
 * artefact it exists to prevent (a published record whose printed identifier is not the one it is
 * registered under).
 *
 * Per-page extraction needs PyMuPDF or ghostscript. When neither can read the file, the check
 * falls back to the whole document rather than refusing outright — the weaker answer is still
 * evidence — and SAYS SO in `method`, so the operator can see which question was actually asked.
 */
export async function pdfPage1ContainsDoi(pdfPath: string, doi: string): Promise<StampCheck> {
  if (!doi.trim()) return { outcome: "unavailable", reason: `"${doi}" is not a DOI to look for` };
  const pages = await extractPdfPages(pdfPath);
  if (pages.pages === null) {
    const whole = await pdfContainsDoi(pdfPath, doi);
    if (whole.outcome === "unavailable") return whole;
    return { ...whole, method: `${whole.method}, WHOLE DOCUMENT — per-page extraction unavailable (${pages.reason})` };
  }
  if (pages.pages.length === 0) {
    return { outcome: "unavailable", reason: `${pdfPath} has no pages, so nothing can be stamped` };
  }
  const page1 = pages.pages[0]!;
  const shape: StampShape = pages.method === "PyMuPDF"
    ? (stampShapePresent(page1, doi) ? "matched" : "not-found")
    : "unknown";
  const method = `${pages.method}, page 1`;
  return findDoi(page1, doi)
    ? { outcome: "present", method, shape }
    : { outcome: "absent", method, shape };
}

/**
 * `doi:<DOI>` followed by the stamp's separator — the shape the pipeline emits.
 *
 * The separator class is deliberately wide. The stamp is authored with U+00B7 MIDDLE
 * DOT, but what an extractor returns depends on the font's encoding: a Type1 face using
 * StandardEncoding maps that byte to U+2022 BULLET, so the same PDF yields `·` or `•`
 * depending on how the glyph was encoded. This is corroboration, not the decision, so
 * accepting any of the plausible separators costs nothing and avoids reporting
 * "not-found" for a perfectly good stamp.
 */
export function stampShapePresent(text: string, doi: string): boolean {
  const d = doi.trim();
  if (!d) return false;
  return new RegExp(`doi:${escapeRe(d)}(?![0-9])\\s*[\u00b7\u2022\u2219|\u2013\u2014-]`).test(text);
}
