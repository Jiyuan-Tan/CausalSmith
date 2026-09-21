import { describe, it, expect } from "vitest";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import { join, resolve } from "node:path";
import { mathToText, renderReviewText, texToReadable } from "../src/lib/reviewText.js";
import { renderTexLine, TEX_SOURCED, titleCase } from "../src/lib/docmd.js";
import { parseReview, type Review } from "../src/lib/review.js";

/**
 * The referee quotes the manuscript, so its prose carries the manuscript's
 * LaTeX. The contract is absolute and the corpus sweep below is what enforces
 * it: NO TeX survives into the rendered output — no backslash command, no
 * escaped special, no unmatched math delimiter, no TeX dash, no stray brace.
 *
 * An earlier version of this test recognised only a handful of macros and
 * passed while `\mathbb`, `\kappa`, `\asymp` and `--` were being published
 * (audit, 2026-09-21). The assertion here is therefore stated as "nothing TeX
 * shaped", not as a list of macros to look for.
 */

const LABELS = {
  "thm:exact-ratio-decoder": "Theorem 3",
  "T-1": "Theorem 1",
  "P-2": "Assumption 1",
  "S-1": "Setup S-1",
};

/**
 * What a reader actually sees, EXCLUDING successfully rendered math.
 *
 * A KaTeX subtree is rendered typography, not source: it legitimately contains
 * brace and backslash GLYPHS (`\min\{1,d^2/n\}` draws braces). Anything KaTeX
 * could not parse never becomes a KaTeX subtree — it becomes a transliterated
 * `<code>` span, which this keeps and checks. So removing katex output narrows
 * the assertion to exactly the text that came through as prose.
 */
function visibleText(html: string): string {
  // `<code class="rv-tex">` is the FAIL-CLOSED path: a formula the renderer
  // could not draw is shown to the reader AS SOURCE, deliberately, because a
  // transliteration would read as different content. That is not a leak, so it
  // is excluded here — and counted separately by `sourceFallbacks` below, so a
  // regression that starts falling back everywhere is still visible.
  return stripKatex(html.replace(/<code class="rv-tex">[\s\S]*?<\/code>/g, ""))
    .replace(/<[^>]+>/g, "")
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'")
    .replace(/&nbsp;| /g, " ");
}

/**
 * Removes every `<span class="katex">…</span>` subtree, balanced.
 * (KaTeX nests spans, so a non-greedy regex would cut at the wrong `</span>`.)
 */
function stripKatex(html: string): string {
  let out = "";
  let i = 0;
  for (;;) {
    const start = html.indexOf('<span class="katex', i);
    if (start < 0) return out + html.slice(i);
    out += html.slice(i, start);
    let depth = 0;
    let j = start;
    for (; j < html.length; ) {
      if (html.startsWith("<span", j)) {
        depth++;
        j = html.indexOf(">", j) + 1;
      } else if (html.startsWith("</span>", j)) {
        depth--;
        j += 7;
        if (depth === 0) break;
      } else j++;
    }
    i = j;
  }
}

/**
 * Every way TeX could still be showing in prose. Returns the reasons it is.
 *
 * Braces are deliberately NOT listed: TeX grouping braces are consumed by the
 * scanner, so one that reaches prose is content the referee typed (set-builder
 * notation), and the earlier "drop every brace" rule corrupted those sentences.
 * An UNCONSUMED grouping brace always arrives next to the macro it belonged to,
 * which the backslash rules already catch.
 */
/**
 * KaTeX can degrade WITHOUT throwing: an unsupported or untrusted command is
 * drawn in its error colour with the arguments dropped, so `\href{…}{click}`
 * published a red "\href" instead of "click" (audit r2). That markup is inside
 * a katex subtree, so the stripper above hid it — this looks for it first.
 */
/** How many formulas were shown as source rather than rendered. */
export function sourceFallbacks(html: string): number {
  return (html.match(/<code class="rv-tex">/g) ?? []).length;
}

export function katexErrors(html: string): number {
  return (html.match(/katex-error|#cc0000/g) ?? []).length;
}

function texLeaks(text: string): string[] {
  const bad: string[] = [];
  const cmd = /\\[a-zA-Z@]+/.exec(text);
  if (cmd) bad.push(`backslash command ${cmd[0]}`);
  const escaped = /\\[%&_#$]/.exec(text);
  if (escaped) bad.push(`escaped special ${escaped[0]}`);
  if (/\\/.test(text)) bad.push("a bare backslash");
  if (/\$/.test(text)) bad.push("a $ delimiter");
  if (/--/.test(text)) bad.push("a TeX dash");
  const unmatched = /\\\(|\\\)|\\\[|\\\]/.exec(text);
  if (unmatched) bad.push(`an unmatched delimiter ${unmatched[0]}`);
  return bad;
}

describe("KaTeX degradation is never published", () => {
  // KaTeX renders these red, with the label dropped, and does not throw.
  it("renders a URL macro itself rather than handing it to KaTeX", () => {
    const http = renderReviewText("see \\href{https://example.test/a}{the note} for more");
    expect(katexErrors(http)).toBe(0);
    expect(http).toContain('<a href="https://example.test/a"');
    expect(http).toContain('rel="noopener nofollow"');
    expect(visibleText(http)).toBe("see the note for more");

    const url = renderReviewText("at \\url{https://example.test/a}");
    expect(katexErrors(url)).toBe(0);
    expect(visibleText(url)).toBe("at https://example.test/a");
  });

  // A non-http scheme is never a link, and never executable.
  it("renders a non-http href as text only", () => {
    const js = renderReviewText("\\href{javascript:alert(1)}{click}");
    expect(katexErrors(js)).toBe(0);
    expect(js).not.toContain("<a ");
    expect(js).not.toContain("javascript:");
    expect(visibleText(js)).toBe("click");
    expect(visibleText(renderReviewText("\\href{mailto:a@b.c}{write}"))).toBe("write");
  });

  it("discards any KaTeX output that came back as an error, and shows the source", () => {
    // `\color` is a command KaTeX draws in its error colour under our trust
    // policy rather than refusing outright.
    for (const src of [
      "\\href{javascript:alert(1)}{x}",
      "x \\htmlClass{a}{b} y",
      "`\\href{ftp://h/f}{g}`",
    ]) {
      const html = renderReviewText(src);
      expect(katexErrors(html), src).toBe(0);
    }
  });

  it("shows the source, escaped, when KaTeX cannot render a run at all", () => {
    const html = renderReviewText("a disabled \\iffalse proof block");
    expect(html).toContain('<code class="rv-tex">\\iffalse</code>');
    expect(sourceFallbacks(html)).toBe(1);
    expect(html).not.toContain("<iffalse");
    // The prose around it is untouched.
    expect(visibleText(html)).toBe("a disabled  proof block");
  });

  it("survives absurd nesting without throwing", () => {
    const deep = "\\emph{".repeat(5000) + "x" + "}".repeat(5000);
    expect(() => renderReviewText(deep)).not.toThrow();
    expect(renderReviewText(deep).length).toBeGreaterThan(0);
  });
});

// Both of these are real strings in the shipped corpus.
describe("cross-references in a sentence", () => {
  const L = { "thm:x": "Theorem 4", "oeq:feasible-upper": "Theorem 4", "thm:minimax-lower": "Theorem 3" };

  it("does not repeat a kind word the sentence already said", () => {
    expect(visibleText(renderReviewText("see Theorem~\\ref{thm:x} now", L))).toBe("see Theorem 4 now");
    expect(visibleText(renderReviewText("in Section~\\ref{thm:minimax-lower}.", L))).toBe("in Section 3.");
    // …and with no kind word in front, the full label stands.
    expect(visibleText(renderReviewText("Rewrite \\cref{thm:x}", L))).toBe("Rewrite Theorem 4");
  });

  // stat_policy_regret_margin_overlap_v1 and
  // stat_discrete_ate_heterogeneity_frontier_v1 both do this.
  it("shows a quoted reference as source instead of resolving it", () => {
    const html = renderReviewText('The sentence "Theorem~\\ref{oeq:feasible-upper}" is wrong.', L);
    expect(html).toContain('<code class="rv-tex">\\ref{oeq:feasible-upper}</code>');
    expect(visibleText(html)).not.toContain("Theorem 4");

    const lean = renderReviewText('artifacts such as "\\leanref{S-1}{a model}" appear', L);
    expect(lean).toContain('<code class="rv-tex">');
    expect(lean).toContain("leanref");

    // Outside the quotation it resolves as usual.
    expect(visibleText(renderReviewText('"quoted" then \\cref{thm:x}', L))).toContain("Theorem 4");
  });

  // A lone straight quote is an inch mark, a prime, a second — not the start
  // of a quotation that never ends. Treating it as an opener swallowed every
  // reference in the rest of the field (audit r5).
  it("opens a straight quotation only when the field closes it", () => {
    const inches = renderReviewText('The 5" margin is wrong. See Theorem~\\ref{thm:x}.', L);
    expect(visibleText(inches)).toBe('The 5" margin is wrong. See Theorem 4.');
    expect(sourceFallbacks(inches)).toBe(0);

    // …and a quotation that DOES close still shields what it quotes.
    const quoted = renderReviewText('It says "see Theorem~\\ref{thm:x}" there.', L);
    expect(quoted).toContain('<code class="rv-tex">\\ref{thm:x}</code>');
  });
});

/**
 * A referee writes "Theorems~\ref{a} and \ref{b}", and the crosswalk resolves
 * each label to "Theorem 3". Printing both labels gives "Theorems Theorem 3
 * and Theorem 4" — the doubled kind word the reader sees as a typo, or worse,
 * as a claim about a different object when the two kinds disagree.
 */
describe("a kind word the sentence already said, in every form", () => {
  const L = {
    "thm:a": "Theorem 3", "thm:b": "Theorem 4",
    "lem:x": "Lemma 1", "lem:y": "Lemma 2",
    "sec:a": "Section 2", "sec:b": "Section 5",
    "eq:a": "Equation 7", "eq:b": "Equation 8",
    "cor:a": "Corollary 1", "cor:b": "Corollary 2",
  };

  it("reads a PLURAL kind word, which then governs the whole list", () => {
    expect(visibleText(renderReviewText("See Theorems~\\ref{thm:a} and \\ref{thm:b}.", L)))
      .toBe("See Theorems 3 and 4.");
    expect(visibleText(renderReviewText("Lemmas \\ref{lem:x} and \\ref{lem:y} give it", L)))
      .toBe("Lemmas 1 and 2 give it");
    expect(visibleText(renderReviewText("Sections \\ref{sec:a}, \\ref{sec:b}", L)))
      .toBe("Sections 2, 5");
    expect(visibleText(renderReviewText("Equations \\ref{eq:a} through \\ref{eq:b}", L)))
      .toBe("Equations 7 through 8");
    expect(visibleText(renderReviewText("Corollaries \\ref{cor:a} and \\ref{cor:b}", L)))
      .toBe("Corollaries 1 and 2");
  });

  it("governs a comma list inside ONE macro the same way", () => {
    expect(visibleText(renderReviewText("Theorem \\ref{thm:a,thm:b}", L)))
      .toBe("Theorem 3 and 4");
    expect(visibleText(renderReviewText("see Theorems \\cref{thm:a,thm:b}", L)))
      .toBe("see Theorems 3 and 4");
    // With nothing naming the kind, each label stands in full.
    expect(visibleText(renderReviewText("\\cref{thm:a,thm:b}", L)))
      .toBe("Theorem 3 and Theorem 4");
  });

  it("emits the number alone when the label's kind DISAGREES", () => {
    expect(visibleText(renderReviewText("in Sections \\ref{thm:a} and \\ref{thm:b}", L)))
      .toBe("in Sections 3 and 4");
    expect(visibleText(renderReviewText("Lemmas \\ref{thm:a}, \\ref{lem:x}", L)))
      .toBe("Lemmas 3, 1");
  });

  it("stops governing where the coordinated list stops", () => {
    // Nothing named a kind, so nothing is dropped from either label.
    expect(visibleText(renderReviewText("Compare \\ref{thm:a} and \\ref{lem:x}", L)))
      .toBe("Compare Theorem 3 and Lemma 1");
    expect(visibleText(renderReviewText("Theorem \\ref{thm:a}, but also see \\ref{lem:x}", L)))
      .toBe("Theorem 3, but also see Lemma 1");
  });

  // `\label{…}` DECLARES a name; it never stands for a number, so resolving it
  // puts a number where the referee asked for a declaration.
  it("shows a \\label declaration as source rather than resolving it", () => {
    const html = renderReviewText("add \\label{thm:a} to the statement", L);
    expect(html).toContain('<code class="rv-tex">\\label{thm:a}</code>');
    expect(visibleText(html)).not.toContain("Theorem 3");
    expect(visibleText(html)).toBe("add  to the statement");
  });
});

describe("fail closed means the original source", () => {
  it("does not close a math span on an escaped dollar", () => {
    expect(visibleText(renderReviewText("Cost $5 versus \\$10"))).toBe("Cost $5 versus $10");
  });

  it("keeps a malformed macro's own source, not a transliteration", () => {
    expect(renderReviewText("a \\foo{ b")).toContain('<code class="rv-tex">\\foo{');
    expect(renderReviewText("a \\texttt{unclosed")).toContain("texttt");
    expect(renderReviewText("a \\texttt{unclosed")).toContain("\\texttt{");
  });

  // A URL that a browser would resolve elsewhere is not a URL we link.
  it("links only a URL that parses as http(s) and survives serialisation", () => {
    const evil = renderReviewText("\\href{https://trusted.test\n@evil.test/}{trusted}");
    expect(evil).not.toContain("<a ");
    expect(evil).not.toContain("evil.test\"");
    expect(visibleText(evil)).toContain("trusted");

    for (const bad of [
      "\\href{https://a.test\u0000/x}{l}",
      "\\href{ht!tp://a.test}{l}",
      "\\href{//a.test}{l}",
      "\\href{https://a.test\tb}{l}",
    ]) {
      expect(renderReviewText(bad), bad).not.toContain("<a ");
    }

    const ok = renderReviewText("\\href{https://example.test/a b}{l}");
    expect(ok).not.toContain("<a "); // a space is not a URL

    const good = renderReviewText("\\href{https://example.test/a}{label}");
    expect(good).toContain('href="https://example.test/a"');
  });

  it("skips TeX whitespace between a macro and its arguments", () => {
    const html = renderReviewText("\\href {https://example.test/a}{label}");
    expect(html).toContain('href="https://example.test/a"');
    expect(visibleText(html)).toBe("label");
    expect(visibleText(renderReviewText("\\url {https://example.test/b}")))
      .toBe("https://example.test/b");
  });
});

describe("literal characters that are not TeX", () => {
  it("keeps an unmatched dollar as the currency it is", () => {
    expect(visibleText(renderReviewText("price is $5 today"))).toBe("price is $5 today");
    // Two prices are not one formula (audit r4).
    expect(visibleText(renderReviewText("price $5 and $6 each"))).toBe("price $5 and $6 each");
    expect(visibleText(renderReviewText("a $ sign alone"))).toBe("a $ sign alone");
  });

  // …but the price rule must not eat mathematics. A span that carries a macro
  // or an operator is a formula whatever its first character is (audit r5).
  it("still reads a formula that opens on a digit as a formula", () => {
    const rate = renderReviewText("Take $1/n $ and $k$.");
    expect(sourceFallbacks(rate)).toBe(0);
    expect(rate).toContain("katex");
    expect(texLeaks(visibleText(rate)), visibleText(rate)).toEqual([]);

    const eps = renderReviewText("Assume $0 < \\epsilon < 1 $ throughout.");
    expect(eps).toContain("katex");
    expect(texLeaks(visibleText(eps)), visibleText(eps)).toEqual([]);
    expect(visibleText(eps)).toBe("Assume  throughout.");
  });

  it("does not apply TeX typography inside code, URLs or identifiers", () => {
    expect(renderReviewText("run \\texttt{--help} now")).toContain("<code>--help</code>");
    expect(visibleText(renderReviewText("see `--flag` please"))).toContain("--flag");
    expect(visibleText(renderReviewText("at https://x--y.test/a_b~c ok")))
      .toContain("https://x--y.test/a_b~c");
    expect(visibleText(renderReviewText("the decl Causalean.Graph.d_sep~x")))
      .toContain("Causalean.Graph.d_sep~x");
    // …while ordinary prose still gets its dashes.
    expect(visibleText(renderReviewText("pages 1--2 and a---b"))).toBe("pages 1\u20132 and a\u2014b");
  });
});

describe("renderReviewText: the rules", () => {
  it("resolves a cross-reference the paper's crosswalk knows", () => {
    expect(visibleText(renderReviewText("see \\cref{obj:thm:exact-ratio-decoder} now", LABELS)))
      .toBe("see Theorem 3 now");
  });

  it("resolves a comma list of references into a sentence", () => {
    expect(visibleText(renderReviewText("\\cref{obj:T-1,obj:P-2}", LABELS)))
      .toBe("Theorem 1 and Assumption 1");
    expect(visibleText(renderReviewText("\\Cref{T-1,P-2,S-1}", LABELS)))
      .toBe("Theorem 1, Assumption 1 and Setup S-1");
  });

  it("degrades an unresolvable reference to its label, never to source", () => {
    const out = visibleText(renderReviewText("Appendix~\\ref{sec:deferred-proofs} collects them"));
    expect(out).toBe("Appendix sec:deferred-proofs collects them");
  });

  // `\leanref{id}{display}` carries the reader's text in its SECOND argument.
  it("uses a two-argument leanref's display text", () => {
    // `\ensuremath{p}` is math, so it renders as math (and visibleText, which
    // drops rendered math, sees nothing left over).
    const math = renderReviewText("\\leanref{sym:p}{\\ensuremath{p}}");
    expect(math).toContain("katex");
    expect(texLeaks(visibleText(math))).toEqual([]);
    expect(visibleText(renderReviewText("\\leanref{S-1}{real-outcome model}"))).toBe(
      "real-outcome model",
    );
    expect(visibleText(renderReviewText("\\leanref{S-1}", LABELS))).toBe("Setup S-1");
  });

  it("keeps a citation's key and locator, and drops the macro", () => {
    expect(visibleText(renderReviewText("Use \\citet[Section 3, Theorems 1--2]{FuSamiiWang2026}.")))
      .toBe("Use FuSamiiWang2026 (Section 3, Theorems 1–2).");
    expect(visibleText(renderReviewText("\\citep{A2020,B2021}"))).toBe("A2020, B2021");
  });

  it("handles text macros with NESTED braces", () => {
    const html = renderReviewText("\\texttt{a {nested} b} and \\emph{x \\textbf{y} z}");
    // `\texttt` is CODE: its content is literal, braces and all.
    expect(html).toContain("<code>a {nested} b</code>");
    expect(html).toContain("<em>x <strong>y</strong> z</em>");
    expect(texLeaks(visibleText(html))).toEqual([]);
  });

  // The failure the audit found: macros loose in a sentence, outside any
  // delimiter, were passed straight through.
  it("renders bare math macros sitting in a sentence", () => {
    for (const src of [
      "notation such as \\mathbb C^{,m+1} and more",
      "we take F_{r,\\kappa} as given",
      "order comparability (AsympSeq/\\asymp), not convergence",
      "the chain R_{n,\\ell_1}^\\star \\le R_{n,\\infty}^\\star plus the bound",
      "a certificate object \\mathcal G_n and its grid",
      "define \\widehat\\kappa_n=n^{-1}\\sum_i w(X_i)^2 and write L_\\alpha\\sqrt{\\widehat\\kappa_n/n}.",
    ]) {
      expect(texLeaks(visibleText(renderReviewText(src))), src).toEqual([]);
    }
    // …and the surrounding prose is left alone.
    expect(visibleText(renderReviewText("a certificate object \\mathcal G_n and its grid")))
      .toContain(" and its grid");
  });

  it("renders a backtick span that is really a formula, as a formula", () => {
    const html = renderReviewText("the notation `\\ell_{n,d,\\sigma}` is used");
    expect(texLeaks(visibleText(html))).toEqual([]);
    expect(html).toContain("katex");
    // …and a span that is really an identifier stays code.
    expect(renderReviewText("commit `43ec493a` is stale")).toContain("<code>43ec493a</code>");
  });

  it("normalises TeX typography", () => {
    expect(visibleText(renderReviewText("a--b, c---d, ``q'' and x~y"))).toBe(
      "a–b, c—d, “q” and x y",
    );
  });

  it("unescapes an escaped special exactly once", () => {
    expect(visibleText(renderReviewText("50\\% of it \\& more, a\\_b, \\#1, \\$5"))).toBe(
      "50% of it & more, a_b, #1, $5",
    );
  });

  it("escapes HTML in the referee's prose", () => {
    const html = renderReviewText('a <script>x</script> & "quoted"');
    expect(html).not.toContain("<script>");
    expect(html).toContain("&lt;script&gt;");
  });

  it("never throws, whatever it is handed", () => {
    for (const bad of [
      "\\", "\\{", "{unbalanced", "unbalanced}", "\\(x", "`x",
      "\\cref{", "\\citet[", "\\texttt{a{b}", "\\begin{array}", "^_^",
    ]) {
      expect(() => renderReviewText(bad), JSON.stringify(bad)).not.toThrow();
      expect(texLeaks(visibleText(renderReviewText(bad))), JSON.stringify(bad)).toEqual([]);
    }
  });
});

/**
 * An ACCEPTED limitation, pinned so it stays a decision rather than drifting
 * into a bug report: bare text mathematics is shown as the referee typed it.
 */
describe("mathematics typed without TeX", () => {
  it("is shown as written, not guessed at", () => {
    for (const src of ["a rate of n^{-4/3} here", "the class Omega_{n,M} is", "x_1 + y_2 = z"]) {
      expect(visibleText(renderReviewText(src)), src).toBe(src);
    }
  });
});

describe("texToReadable", () => {
  it("is nesting aware and maps common macros to Unicode", () => {
    expect(texToReadable("\\emph{A {nested} B}")).toBe("A nested B");
    expect(texToReadable("rates at \\epsilon \\le 1/2")).toBe("rates at ε ≤ 1/2");
    expect(texToReadable("\\mathbb{R}^d")).toBe("R^d");
  });

  // `{}` is TeX's empty group: a separator, never something to put brackets
  // round. `T{}^2` is "T squared", not "T() squared".
  it("does not make a parenthesised base out of an empty group", () => {
    expect(mathToText("T{}^2")).toBe("T²");
    expect(mathToText("{x+y}^2")).toBe("(x+y)²"); // a real group still is one
  });

  it("keeps an unknown command's name for prose, drops it for citations", () => {
    expect(texToReadable("a \\iffalse block")).toBe("a iffalse block");
    expect(texToReadable("a \\iffalse block", true)).toBe("a block");
    expect(texToReadable("\\unknownmacro{kept text}", true)).toBe("kept text");
  });
});

// ── the whole corpus, strictly ───────────────────────────────────────────

const PRESENTATION = resolve(import.meta.dirname, "..", "..", "doc", "presentation");

/** Every report and every history round in the tree. */
function reports(): { name: string; file: string; raw: unknown; labels: Record<string, string> }[] {
  if (!existsSync(PRESENTATION)) return [];
  const out: { name: string; file: string; raw: unknown; labels: Record<string, string> }[] = [];
  for (const name of readdirSync(PRESENTATION)) {
    const dir = join(PRESENTATION, name);
    const main = join(dir, "p5_review.json");
    if (!existsSync(main)) continue;
    const labels: Record<string, string> = {};
    try {
      const cw = JSON.parse(readFileSync(join(dir, "presentation_crosswalk.json"), "utf8")) as {
        entries: { obj_id: string; paper_label: string }[];
      };
      for (const e of cw.entries) labels[e.obj_id] = e.paper_label;
    } catch {
      /* a bundle without a crosswalk simply resolves no labels */
    }
    const files = [main];
    const hist = join(dir, "p5_review_history");
    if (existsSync(hist)) {
      for (const r of readdirSync(hist)) {
        if (/^round_\d+\.json$/.test(r)) files.push(join(hist, r));
      }
    }
    for (const file of files) {
      try {
        out.push({ name, file, raw: JSON.parse(readFileSync(file, "utf8")), labels });
      } catch {
        /* unreadable: the loader's own tests cover that path */
      }
    }
  }
  return out;
}


/**
 * A corpus sweep that finds no corpus proves nothing. Missing bundles are a
 * broken checkout, not a pass — opt out explicitly if you really mean it.
 */
function requireCorpus(found: number): void {
  if (found === 0 && process.env.SITE_ALLOW_NO_CORPUS !== "1") {
    throw new Error(
      "No bundles under doc/presentation: this sweep would pass vacuously. " +
        "Set SITE_ALLOW_NO_CORPUS=1 to allow it.",
    );
  }
}

const ALL = reports();

function strings(r: Review): string[] {
  return [
    r.summary ?? "",
    r.rationale ?? "",
    ...r.strengths,
    ...r.questions,
    ...r.findings.flatMap((f) => [f.issue, f.fix ?? "", f.section ?? ""]),
  ].filter(Boolean);
}

describe("every shipped referee report renders without TeX", () => {
  it("covers the whole corpus, history included", () => {
    requireCorpus(ALL.length);
    expect(new Set(ALL.map((r) => r.name)).size).toBeGreaterThanOrEqual(20);
    expect(ALL.length).toBeGreaterThan(20);
  });

  // Falling back is correct when a formula cannot be drawn, but it should stay
  // rare: a jump here means the renderer stopped understanding the corpus.
  it("shows source instead of rendering for only a handful of formulas", () => {
    let fallbacks = 0;
    let total = 0;
    for (const { raw, labels } of ALL) {
      const review = parseReview(raw);
      if (!review) continue;
      for (const s of strings(review)) {
        total += 1;
        fallbacks += sourceFallbacks(renderReviewText(s, labels));
      }
    }
    expect(total).toBeGreaterThan(1000);
    expect(fallbacks / total).toBeLessThan(0.02);
  });

  for (const { name, file, raw, labels } of ALL) {
    it(`${name}/${file.split("/").slice(-2).join("/")}`, () => {
      const review = parseReview(raw);
      if (!review) return;
      for (const s of strings(review)) {
        const text = visibleText(renderReviewText(s, labels));
        const leaks = texLeaks(text);
        expect(leaks, `${leaks.join("; ")} in:\n${s.slice(0, 200)}\n→ ${text.slice(0, 200)}`)
          .toEqual([]);
      }
    });
  }
});

/**
 * Paper titles and tldrs are .tex-sourced too, and they are rendered by
 * `docmd`, not by the review renderer. "Margin--Overlap" was reaching the
 * landing page, the paper page and the review page verbatim.
 */
describe("every shipped title renders without TeX", () => {
  const metas = [...new Set(ALL.map((r) => r.name))].map((name) => ({
    name,
    meta: JSON.parse(
      readFileSync(join(PRESENTATION, name, "meta.json"), "utf8"),
    ) as { title: string; tldr?: string | null; abstract: string },
  }));

  it("covers the corpus", () => {
    requireCorpus(metas.length);
    expect(metas.length).toBeGreaterThanOrEqual(20);
  });

  for (const { name, meta } of metas) {
    it(`${name}`, () => {
      for (const [what, src] of [
        ["title", meta.title],
        ["titleCase(title)", titleCase(meta.title)],
        ["tldr", meta.tldr ?? ""],
        ["abstract", meta.abstract],
      ] as [string, string][]) {
        if (!src) continue;
        // These fields come out of the paper's .tex, so they opt in to
        // TeX typography; a Lean docstring never does (audit r4).
        const text = visibleText(renderTexLine(src, TEX_SOURCED));
        expect(texLeaks(text), `${name} ${what}: ${text.slice(0, 160)}`).toEqual([]);
      }
    });
  }
});
