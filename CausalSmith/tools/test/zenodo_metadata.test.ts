// Turning a bundle's `meta.json` into Zenodo metadata is mostly a TeX problem.
//
// Bundle titles and abstracts are LaTeX source, and Zenodo has no math renderer and
// accepts only a small sanitized HTML subset. So math is flattened to Unicode. The
// risk in doing that is silent MISTRANSLATION: an approximation that turns one symbol
// into a different symbol is worse than leaving the backslash in, because it reads as
// correct. That already happened once — `a_\epsilon` came out as `aᵨ` (subscript rho,
// a different constant) because the subscript table approximated a missing glyph — so
// the "no Greek subscripts" case is pinned below.

import { describe, it, expect } from "vitest";
import {
  CORPORATE_AUTHOR,
  DEFAULT_LICENSE,
  buildZenodoMetadata,
  paperUrl,
  texToHtml,
  texToPlainText,
  type BundleMeta,
} from "../src/zenodo/metadata.js";

const BASE_META: BundleMeta = {
  qid: "stat_demo",
  spec: "spec",
  title: "Sharp minimax rates under \\(\\epsilon\\)-overlap",
  abstract: "We study \\(\\epsilon\\in(0,1/2)\\) and show the rate is \\[\\frac1n+\\frac{d^2}{n^2(\\log n)^2}\\] up to constants.",
  area: "Stat",
  created: "2026-07-21",
  version: 3,
  revised: "2026-08-27",
  wp_number: "CSWP-2026-008",
};

const OPTS = { bundleId: "stat_demo_spec", siteBaseUrl: "https://causalsmith.org" };

describe("texToPlainText", () => {
  it("renders Greek, relations and fractions as readable Unicode", () => {
    expect(texToPlainText("\\(\\epsilon\\in(0,1/2)\\)")).toBe("\u03f5 ∈ (0,1/2)");
    expect(texToPlainText("\\(\\frac1n\\)")).toBe("1/n");
    expect(texToPlainText("\\(\\frac{d^2}{n^2(\\log n)^2}\\)")).toBe("d²/(n²(log n)²)");
  });

  it("keeps a space between a variable and an operator name", () => {
    // `n\log n` must not flatten to `nlogn`. Note `\rho n` IS `ρn`: in math mode TeX
    // ignores the space that merely terminates the control word.
    expect(texToPlainText("\\(\\rho n\\log n\\)")).toBe("ρn log n");
    expect(texToPlainText("\\(\\rho_\\epsilon n\\log n\\)")).toBe("ρ_\u03f5 n log n");
  });

  it("never substitutes a different letter for a missing subscript glyph", () => {
    // There is no subscript epsilon in Unicode; the fallback must be explicit.
    expect(texToPlainText("\\(a_\\epsilon\\)")).toBe("a_\u03f5");
    expect(texToPlainText("\\(a_\\epsilon\\)")).not.toContain("ᵨ");
    // Where a real glyph exists it is used.
    expect(texToPlainText("\\(a_n\\)")).toBe("aₙ");
    expect(texToPlainText("\\(x^2\\)")).toBe("x²");
  });

  it("keeps citation keys rather than leaving a dangling sentence", () => {
    expect(texToPlainText("Shown by \\citet{smith2020} and \\citep{a,b}."))
      .toBe("Shown by [smith2020] and [a, b].");
  });

  it("flattens cross-references to their bare label", () => {
    expect(texToPlainText("See \\cref{thm:main}.")).toBe("See main.");
  });

  it("unescapes TeX punctuation and text macros", () => {
    expect(texToPlainText("50\\% of \\emph{cases} in \\texttt{code}"))
      .toBe("50% of cases in code");
  });

  it("collapses a multi-line title to one line", () => {
    expect(texToPlainText("A title\n   spanning lines")).toBe("A title spanning lines");
  });
});

describe("texToHtml", () => {
  it("escapes HTML so a title cannot inject markup", () => {
    const html = texToHtml("A <script>alert(1)</script> & \"quote\"");
    expect(html).not.toContain("<script>");
    expect(html).toContain("&lt;script&gt;");
    expect(html).toContain("&amp;");
  });

  it("uses sub/sup tags where no Unicode glyph exists, and glyphs where one does", () => {
    expect(texToHtml("\\(a_\\epsilon\\)")).toBe("<p>a<sub>\u03f5</sub></p>");
    expect(texToHtml("\\(x^{n+\\epsilon}\\)")).toBe("<p>x<sup>n+\u03f5</sup></p>");
    // Every character of `n+1` has a superscript glyph, so no tag is needed.
    expect(texToHtml("\\(x^{n+1}\\)")).toBe("<p>xⁿ⁺¹</p>");
  });

  it("puts display math in its own paragraph and keeps inline math inline", () => {
    const html = texToHtml(BASE_META.abstract!);
    expect(html).toContain("<p>1/n+d²/(n²(log n)²)</p>");
    expect(html).toContain("\u03f5 ∈ (0,1/2)");
  });

  it("emits only tags Zenodo's sanitizer keeps", () => {
    const html = texToHtml("A \\textbf{bold} and \\emph{italic} and \\texttt{mono} line.");
    expect(html).toBe("<p>A <strong>bold</strong> and <em>italic</em> and <code>mono</code> line.</p>");
  });

  it("splits source paragraphs into separate <p> elements", () => {
    expect(texToHtml("One.\n\nTwo.")).toBe("<p>One.</p>\n<p>Two.</p>");
  });
});

describe("buildZenodoMetadata", () => {
  it("builds a working-paper deposit with the corporate author and no personal data", () => {
    const md = buildZenodoMetadata(BASE_META, OPTS);
    expect(md.upload_type).toBe("publication");
    expect(md.publication_type).toBe("workingpaper");
    expect(md.creators).toEqual([{ name: CORPORATE_AUTHOR }]);
    // No affiliation, no ORCID, no e-mail may ever appear.
    expect(Object.keys(md.creators[0])).toEqual(["name"]);
    expect(JSON.stringify(md)).not.toMatch(/@[\w.-]+\.\w+/);
  });

  it("dates the deposit by `revised`, falling back to `created`", () => {
    expect(buildZenodoMetadata(BASE_META, OPTS).publication_date).toBe("2026-08-27");
    const { revised: _drop, ...noRevised } = BASE_META;
    expect(buildZenodoMetadata(noRevised, OPTS).publication_date).toBe("2026-07-21");
  });

  it("refuses a non-ISO date rather than sending something Zenodo will mangle", () => {
    expect(() => buildZenodoMetadata({ ...BASE_META, revised: "27 Aug 2026", created: "" }, OPTS))
      .toThrow(/ISO yyyy-mm-dd/);
  });

  it("labels the version as vN and carries the area as a keyword", () => {
    const md = buildZenodoMetadata(BASE_META, OPTS);
    expect(md.version).toBe("v3");
    expect(md.keywords?.[0]).toBe("Stat");
  });

  it("omits `version` when meta.version is absent rather than inventing v1", () => {
    const { version: _drop, ...noVersion } = BASE_META;
    expect(buildZenodoMetadata(noVersion, OPTS).version).toBeUndefined();
  });

  it("links the site page as isIdenticalTo and the repo as isSupplementedBy", () => {
    const md = buildZenodoMetadata(BASE_META, { ...OPTS, repoUrl: "https://github.com/x/y/" });
    expect(md.related_identifiers).toEqual([
      {
        identifier: "https://causalsmith.org/papers/stat_demo_spec",
        relation: "isIdenticalTo",
        scheme: "url",
        resource_type: "publication-workingpaper",
      },
      {
        identifier: "https://github.com/x/y",
        relation: "isSupplementedBy",
        scheme: "url",
        resource_type: "software",
      },
    ]);
  });

  it("states in the notes that the paper is machine-generated and Lean-verified", () => {
    const notes = buildZenodoMetadata(BASE_META, OPTS).notes ?? "";
    expect(notes).toContain("CSWP-2026-008");
    expect(notes).toMatch(/machine-checked in Lean 4/);
    expect(notes).toMatch(/has not been peer reviewed/);
  });

  it("defaults to CC-BY-4.0 for the paper and honours an override", () => {
    expect(buildZenodoMetadata(BASE_META, OPTS).license).toBe(DEFAULT_LICENSE);
    expect(buildZenodoMetadata(BASE_META, { ...OPTS, license: "cc-zero" }).license).toBe("cc-zero");
  });

  it("applies a title prefix and adds communities only when asked", () => {
    const md = buildZenodoMetadata(BASE_META, { ...OPTS, titlePrefix: "[TEST] ", communities: ["causalsmith"] });
    expect(md.title.startsWith("[TEST] Sharp minimax rates under \u03f5-overlap")).toBe(true);
    expect(md.communities).toEqual([{ identifier: "causalsmith" }]);
    expect(buildZenodoMetadata(BASE_META, OPTS).communities).toBeUndefined();
  });

  it("refuses a bundle with no title or no abstract", () => {
    expect(() => buildZenodoMetadata({ ...BASE_META, title: "  " }, OPTS)).toThrow(/title/);
    expect(() => buildZenodoMetadata({ ...BASE_META, abstract: "" }, OPTS)).toThrow(/abstract/);
  });

  it("builds the site paper URL from the bundle directory name", () => {
    expect(paperUrl("https://causalsmith.org/", "abc_def")).toBe("https://causalsmith.org/papers/abc_def");
  });
});
