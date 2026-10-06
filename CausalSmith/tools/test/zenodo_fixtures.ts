// Real (tiny) PDF fixtures for the stamp guard.
//
// The first round of these tests wrote plain text into `paper.pdf`. That is not a PDF,
// so it exercised none of the real extraction path — and both the `unavailable`
// bypass and the `.99` matching `.999` bug survived a fully green suite. These build
// an actual, structurally valid PDF (correct xref offsets, uncompressed content
// stream) so `pdftotext`/`ghostscript`/the zlib fallback all have something genuine to
// read, whichever one the host happens to have.

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
