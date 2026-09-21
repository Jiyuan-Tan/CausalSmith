import { describe, it, expect } from "vitest";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import { join, resolve } from "node:path";
import {
  bibtex,
  bibtexTitle,
  citationAuthor,
  citationKey,
  conceptDoi,
  doiUrl,
  formatDate,
  paperUrl,
  validDate,
  validText,
  validVersion,
  plainCitation,
  seriesLabel,
  texToPlain,
  yearOf,
  type CitationMeta,
} from "../src/lib/citation.js";

const CTX = { site: "https://causalsmith.org/", base: "" };

/** A fully-stamped paper: number, version, revision date, DOI. */
const FULL: CitationMeta = {
  id: "stat_discrete_ate_minimax_loggap_polynomial_upper_match",
  title: "Sharp Minimax Rates for Average Treatment Effects with Discrete Confounding",
  wpNumber: "CSWP-2026-008",
  created: "2026-07-21",
  version: 3,
  revised: "2026-08-27",
  doi: "10.5281/zenodo.0000008",
  commit: "ff99e4bdeadbeef",
};

/** What every bundle in the repository looks like TODAY: no number, no
 *  version, no DOI. The citation must still be correct and complete. */
const BARE: CitationMeta = {
  id: "demo_paper_v1",
  title: "A Demonstration Bound for the Average Treatment Effect",
  created: "2026-06-10",
  commit: "e591f16demo",
};

describe("dates", () => {
  it("formats an ISO date without a timezone round-trip", () => {
    expect(formatDate("2026-08-27")).toBe("27 Aug 2026");
    expect(formatDate("2026-01-01")).toBe("1 Jan 2026");
    expect(yearOf("2026-08-27")).toBe("2026");
  });

  // meta.json is DATA. A field that is not a real date must read as absent,
  // never reach the reader raw (audit r4).
  it("treats anything that is not a real calendar date as absent", () => {
    for (const bad of ["August 2026", "2026-13-01", "2026-13-45", "2026-02-31", "", "2026-1-1"]) {
      expect(formatDate(bad), bad).toBe("");
      expect(validDate(bad), bad).toBeNull();
    }
    expect(formatDate(null)).toBe("");
    expect(validDate(20260827 as unknown as string)).toBeNull();
    expect(validDate("2028-02-29")).toBe("2028-02-29"); // a leap day IS a day
  });

  it("guards the other interpolated fields too", () => {
    expect(validText(42 as unknown as string)).toBeNull();
    expect(validText("  ")).toBeNull();
    expect(validText(" CSWP-2026-008 ")).toBe("CSWP-2026-008");
    expect(validVersion(0)).toBeNull();
    expect(validVersion(1.5)).toBeNull();
    expect(validVersion("3" as unknown as number)).toBeNull();
    expect(validVersion(3)).toBe(3);
  });

  // A whole entry built from junk must still parse, and print none of it.
  it("never prints an invalid field, and never throws on one", () => {
    const junk = {
      ...FULL,
      wpNumber: 7 as unknown as string,
      revised: "2026-13-45",
      version: "three" as unknown as number,
      doi: { nope: true } as unknown as string,
    };
    const entry = bibtex(junk, CTX);
    expect(() => bibtex(junk, CTX)).not.toThrow();
    expect(bibProblems(entry)).toEqual([]);
    for (const raw of ["2026-13-45", "three", "nope", "number      = {7}"]) {
      expect(entry, raw).not.toContain(raw);
    }
    expect(plainCitation(junk, CTX)).not.toContain("2026-13-45");
  });
});

describe("urls", () => {
  it("builds the paper URL from the configured site, not a hardcoded domain", () => {
    expect(paperUrl(FULL, CTX)).toBe(`https://causalsmith.org/papers/${FULL.id}/`);
    expect(paperUrl(FULL, { site: "https://org.github.io/repo/", base: "/repo" })).toBe(
      `https://org.github.io/repo/papers/${FULL.id}/`,
    );
  });

  it("omits the URL when the build has no site configured", () => {
    expect(paperUrl(FULL, { site: null })).toBeNull();
  });

  it("normalizes a DOI to the resolver form", () => {
    expect(doiUrl("10.5281/zenodo.8")).toBe("https://doi.org/10.5281/zenodo.8");
    expect(doiUrl("https://doi.org/10.5281/zenodo.8")).toBe("https://doi.org/10.5281/zenodo.8");
    expect(doiUrl(null)).toBeNull();
  });
});

// A DOI that does not resolve is worse than no DOI: the reader cannot see that
// it is dead. The sandbox prefix 10.5072 is the case that actually occurs — a
// deposit run against Zenodo's sandbox writes one into meta.json.
describe("DOI validation", () => {
  it("accepts a published Zenodo concept DOI", () => {
    expect(conceptDoi("10.5281/zenodo.8")).toBe("10.5281/zenodo.8");
    expect(conceptDoi("10.5281/zenodo.0000008")).toBe("10.5281/zenodo.0000008");
    expect(conceptDoi(" https://doi.org/10.5281/zenodo.8 ")).toBe("10.5281/zenodo.8");
  });

  it("treats a sandbox or malformed DOI as absent", () => {
    for (const bad of [
      "10.5072/zenodo.8", // Zenodo SANDBOX — resolves to nothing
      "10.5281/zenodo.",
      "10.5281/zenodo.abc",
      "10.5281/foo.8",
      "10.1234/other.8",
      "zenodo.8",
      "",
      null,
      undefined,
    ]) {
      expect(conceptDoi(bad as string | null | undefined), String(bad)).toBeNull();
      expect(doiUrl(bad as string | null | undefined), String(bad)).toBeNull();
    }
  });

  it("omits it from both citation forms rather than failing", () => {
    const sandbox = { ...FULL, doi: "10.5072/zenodo.9999" };
    expect(bibtex(sandbox, CTX)).not.toContain("10.5072");
    expect(bibtex(sandbox, CTX)).not.toContain("doi ");
    // With no printable DOI the plain form falls back to the page URL.
    expect(plainCitation(sandbox, CTX)).toBe(
      "CausalSmith (2026). “Sharp Minimax Rates for Average Treatment Effects with " +
        "Discrete Confounding.” CausalSmith Working Paper CSWP-2026-008, version 3 " +
        `(27 Aug 2026). https://causalsmith.org/papers/${FULL.id}/`,
    );
  });

  // Between reserve and publish a per-version DOI does not resolve, so the
  // series cites the concept DOI only — the version is carried by `vN`.
  it("never cites the per-version DOI, even when the bundle carries one", () => {
    const withVersionDoi = { ...FULL, version_doi: "10.5281/zenodo.0000009" } as CitationMeta;
    expect(bibtex(withVersionDoi, CTX)).not.toContain("0000009");
    expect(plainCitation(withVersionDoi, CTX)).not.toContain("0000009");
    expect(bibtex(withVersionDoi, CTX)).toContain("10.5281/zenodo.0000008");
  });
});

/**
 * A tiny BibTeX field validator — enough to catch the failure mode the audit
 * found, which is an entry whose `title = {…}` never closes. Deliberately not
 * a dependency: the property under test is "the braces balance and every field
 * terminates", and that is ten lines.
 */
function bibProblems(entry: string): string[] {
  const bad: string[] = [];
  if (!/^@techreport\{[^,{}\s]+,\n/.test(entry)) bad.push("no @techreport header");
  if (!entry.trimEnd().endsWith("\n}")) bad.push("entry does not close");

  // Walk the body, tracking brace depth with backslash escapes honoured.
  const body = entry.slice(entry.indexOf("\n") + 1, entry.lastIndexOf("}"));
  let depth = 0;
  let dollars = 0;
  for (let i = 0; i < body.length; i++) {
    if (body[i] === "\\") {
      i++;
      continue;
    }
    if (body[i] === "{") depth++;
    else if (body[i] === "}") {
      depth--;
      if (depth < 0) bad.push(`field closed early at ${i}`);
    } else if (body[i] === "$" && depth > 0) dollars++;
  }
  if (depth !== 0) bad.push(`unbalanced braces (${depth})`);
  if (dollars % 2 !== 0) bad.push("odd number of math delimiters");
  // Every line inside the entry must be `  key = value` or a continuation.
  for (const line of body.split("\n")) {
    if (line.trim() && !/^\s{2}[a-z]+\s*=\s/.test(line) && !/^\s/.test(line)) {
      bad.push(`stray line: ${line}`);
    }
  }
  return bad;
}

describe("bibtex titles", () => {
  // A style file lowercases an unprotected title. These are the words that
  // would be damaged: proper names, acronyms, and mixed-case tokens.
  it("brace-protects capitals a style file would eat", () => {
    const out = bibtexTitle("Chebyshev Rollout Schedules for POMDPs and CR2");
    expect(out).toBe("Chebyshev {Rollout} {Schedules} for {POMDPs} and {CR2}");
  });

  it("leaves the first word alone, since every style capitalizes it anyway", () => {
    expect(bibtexTitle("Forbidden comparisons in poisson models")).toBe(
      "Forbidden comparisons in poisson models",
    );
  });

  it("protects a hyphenated compound as one word, punctuation outside the braces", () => {
    expect(bibtexTitle("A lower-bound calibration for Margin--Overlap decay:")).toContain(
      "{Margin--Overlap}",
    );
    expect(bibtexTitle("one two Three: four")).toContain("{Three}:");
  });

  it("converts TeX math to BibTeX math and never braces inside a formula", () => {
    const out = bibtexTitle("Rates at \\(\\epsilon \\in (0, 1/2)\\) for Discrete X");
    expect(out).toContain("$\\epsilon \\in (0, 1/2)$");
    expect(out).not.toContain("{\\epsilon");
    expect(out).toContain("{Discrete}");
  });

  it("escapes the characters that are syntax in a .bib file", () => {
    expect(bibtexTitle("cost & benefit, 50% of it")).toBe("cost \\& benefit, 50\\% of it");
  });

  // The audit's adversarial set: each of these produced an entry that a .bib
  // parser could not read.
  it("never leaves the field unbalanced, however malformed the title", () => {
    const cases: [string, string][] = [
      ["M{alformed title", "an unmatched open brace"],
      ["M}alformed title", "an unmatched close brace"],
      ["Unbalanced $x title", "an unmatched math delimiter"],
      ["Already \\% escaped", "an already-escaped special"],
      ["Trailing backslash \\", "a trailing backslash"],
      ["Nested {a {b} c} braces", "balanced prose braces"],
      ["\\emph{a {b} c} macro", "a macro with a nested argument"],
      ["Mixed \\(x_1\\) and $y$ math", "two math forms"],
      ["100% & #1 _under_ {it}", "every special at once"],
      ["Cost $5 versus \\$10", "an escaped dollar after a currency one"],
      ["Cost \\$5 only", "an escaped dollar alone"],
      ["Half $x$ math and $ a stray", "math then a stray dollar"],
    ];
    for (const [title, why] of cases) {
      const t = bibtexTitle(title);
      let depth = 0;
      for (let i = 0; i < t.length; i++) {
        if (t[i] === "\\") {
          i++;
          continue;
        }
        if (t[i] === "{") depth++;
        else if (t[i] === "}") depth--;
        expect(depth, `${why}: closed early — ${t}`).toBeGreaterThanOrEqual(0);
      }
      expect(depth, `${why}: unbalanced — ${t}`).toBe(0);
      // …and the whole entry parses.
      expect(bibProblems(bibtex({ ...BARE, title }, CTX)), `${why}: ${t}`).toEqual([]);
    }
  });

  // The closing delimiter has to be an UNESCAPED one.
  it("treats a currency dollar as prose, not as a math delimiter", () => {
    expect(bibtexTitle("Cost $5 versus \\$10")).toBe("Cost \\$5 versus \\$10");
    expect(bibtexTitle("Half $x$ math")).toContain("$x$");
  });

  it("escapes an already-escaped special exactly once", () => {
    expect(bibtexTitle("Already \\% escaped")).toContain("\\%");
    expect(bibtexTitle("Already \\% escaped")).not.toContain("\\\\%");
  });

  // The site Title Cases titles for display. Feeding THAT to BibTeX would
  // brace-protect capitals the author never wrote — a display convention baked
  // into every reader's .bib. Callers pass `meta.title` as authored, and the
  // sentence-case corpus then braces only the words that need it.
  it("braces only the capitals the author wrote", () => {
    expect(
      bibtexTitle("Chebyshev rollout schedules for polynomial extrapolation under interference"),
    ).toBe("Chebyshev rollout schedules for polynomial extrapolation under interference");
  });
});

describe("bibtex entry", () => {
  const entry = bibtex(FULL, CTX);

  it("is a @techreport keyed off the immutable bundle id", () => {
    expect(citationKey(FULL)).toBe(`causalsmith_${FULL.id.slice(0, 40)}_${citationKey(FULL).split("_").pop()}`);
    expect(citationKey(FULL)).toMatch(/^causalsmith_[A-Za-z0-9_-]+$/);
    expect(entry.startsWith(`@techreport{${citationKey(FULL)},`)).toBe(true);
    expect(entry.trimEnd().endsWith("}")).toBe(true);
    expect(bibProblems(entry)).toEqual([]);
  });

  // A reader's .bib is keyed on this. It cannot move when the paper is
  // numbered or deposited (audit, 2026-09-21).
  it("does not change when the number or the DOI arrives", () => {
    const before = citationKey({ ...FULL, wpNumber: null, doi: null });
    expect(citationKey(FULL)).toBe(before);
    expect(citationKey({ ...FULL, wpNumber: "CSWP-2026-999", doi: "10.5281/zenodo.1" }))
      .toBe(before);
  });

  it("caps a very long bundle id deterministically, without collisions", () => {
    const long = "x".repeat(80);
    const a = citationKey({ ...FULL, id: `${long}a` });
    const b = citationKey({ ...FULL, id: `${long}b` });
    expect(a.length).toBeLessThanOrEqual(60);
    expect(a).toBe(citationKey({ ...FULL, id: `${long}a` })); // deterministic
    expect(a).not.toBe(b);
  });

  it("carries the corporate author double-braced", () => {
    expect(entry).toContain("author      = {{CausalSmith}}");
  });

  // `meta.authorship` is the paper's own byline. A citation that printed "CausalSmith"
  // instead would credit the series for a person's work.
  it("names the bundle's author when it records one", () => {
    const mine: CitationMeta = { ...FULL, authorship: "Jiyuan Tan" };
    // SINGLE braces: `{{Jiyuan Tan}}` tells BibTeX the name is one indivisible corporate
    // unit, so an abbreviating style prints "Jiyuan Tan" where it should print "Tan, J."
    // and files it under J. Double braces are for the corporate default and nothing else.
    expect(bibtex(mine, CTX)).toContain("author      = {Jiyuan Tan}");
    expect(bibtex(mine, CTX)).not.toContain("{{Jiyuan Tan}}");
    expect(bibtex(FULL, CTX)).toContain("author      = {{CausalSmith}}");
    // ...and the plain-text form and the resolver agree with it.
    expect(plainCitation(mine, CTX)).toMatch(/^Jiyuan Tan \(2026\)\./);
    expect(citationAuthor(mine, CTX)).toBe("Jiyuan Tan");
  });

  it("falls back to the corporate author for every shape of absent authorship", () => {
    for (const absent of [null, undefined, "", "   "]) {
      const meta = { ...FULL, authorship: absent as string | null | undefined };
      expect(citationAuthor(meta, CTX), JSON.stringify(absent)).toBe("CausalSmith");
      expect(bibtex(meta, CTX)).toContain("author      = {{CausalSmith}}");
    }
    expect(citationAuthor(BARE, CTX)).toBe("CausalSmith");
    // A build-level override still works, and a bundle's own byline outranks it.
    expect(citationAuthor(BARE, { ...CTX, author: "Someone Else" })).toBe("Someone Else");
    expect(citationAuthor({ ...FULL, authorship: "Jiyuan Tan" }, { ...CTX, author: "Someone Else" }))
      .toBe("Jiyuan Tan");
  });

  // "revised" is a claim about history; a v1 paper has none (audit r4).
  it("says revised only when there is a revision", () => {
    expect(bibtex({ ...FULL, version: 1, revised: FULL.created }, CTX))
      .toContain("Version 1, 21 Jul 2026.");
    expect(bibtex({ ...FULL, version: 1, revised: FULL.created }, CTX))
      .not.toContain("revised");
    expect(bibtex(FULL, CTX)).toContain("Version 3, revised 27 Aug 2026.");
  });

  // A .bib file keeps the accent macro; a style file would eat "Hölder".
  it("keeps a TeX accent verbatim, braced", () => {
    expect(bibtexTitle('A H{\\"o}lder bound')).toContain('{\\"o}');
    expect(bibtexTitle('A H\\"older bound')).toContain('{\\"o}');
    expect(bibProblems(bibtex({ ...BARE, title: 'A H\\"older bound' }, CTX))).toEqual([]);
    // …and the reading form gives the letter.
    expect(texToPlain('A H\\"older bound')).toBe('A H\u00f6lder bound');
    expect(texToPlain("Erd\\H{o}s and Kurkov\\'a")).toBe('Erd\u0151s and Kurkov\u00e1');
  });

  it("carries institution, number, doi, url and the Lean pin in the note", () => {
    expect(entry).toContain("institution = {CausalSmith Working Papers}");
    expect(entry).toContain("number      = {CSWP-2026-008}");
    expect(entry).toContain("doi         = {10.5281/zenodo.0000008}");
    expect(entry).toContain(`url         = {https://causalsmith.org/papers/${FULL.id}/}`);
    expect(entry).toContain("Version 3, revised 27 Aug 2026.");
    expect(entry).toContain("formal statements verified in Lean 4 at commit ff99e4b");
    expect(entry).toContain("month       = jul");
  });

  // This is the shape of every bundle in the repository today.
  it("works with no number, no version and no DOI", () => {
    const bare = bibtex(BARE, CTX);
    expect(citationKey(BARE)).toBe("causalsmith_demo_paper_v1");
    expect(bare).toContain("@techreport{causalsmith_demo_paper_v1,");
    expect(bibProblems(bare)).toEqual([]);
    expect(bare).not.toContain("number");
    expect(bare).not.toContain("doi ");
    expect(bare).toContain("institution = {CausalSmith Working Papers}");
    expect(bare).toContain("url         = {https://causalsmith.org/papers/demo_paper_v1/}");
    expect(bare).toContain("verified in Lean 4 at commit e591f16");
  });

  it("drops the url too when there is no configured site", () => {
    expect(bibtex(BARE, { site: null })).not.toContain("url");
  });
});

describe("plain-text citation", () => {
  it("names the numbered working paper, its version, and its DOI", () => {
    expect(plainCitation(FULL, CTX)).toBe(
      "CausalSmith (2026). “Sharp Minimax Rates for Average Treatment Effects with " +
        "Discrete Confounding.” CausalSmith Working Paper CSWP-2026-008, version 3 " +
        "(27 Aug 2026). https://doi.org/10.5281/zenodo.0000008",
    );
  });

  it("falls back to the series name and the page URL when unnumbered", () => {
    expect(plainCitation(BARE, CTX)).toBe(
      "CausalSmith (2026). “A Demonstration Bound for the Average Treatment Effect.” " +
        "CausalSmith Working Papers. https://causalsmith.org/papers/demo_paper_v1/",
    );
    expect(seriesLabel(BARE, CTX)).toBe("CausalSmith Working Papers");
  });

  // The audit found "Rates at \(\epsilon\)" published as "Rates at \epsilon".
  it("reads a TeX-bearing title as words, with math as Unicode", () => {
    const withMath = { ...FULL, title: "Rates at \\(\\epsilon\\) with \\texttt{clip}" };
    const out = plainCitation(withMath, CTX);
    expect(out).toContain("Rates at ε with clip");
    expect(out).not.toMatch(/\\[a-zA-Z]/);
    expect(texToPlain("a--b and c---d")).toBe("a–b and c—d");
  });

  it("is nesting aware and keeps a text wrapper's words", () => {
    expect(texToPlain("\\emph{A {nested} B}")).toBe("A nested B");
    expect(texToPlain("bounds at \\(\\epsilon \\le 1/2\\)")).toBe("bounds at ε ≤ 1/2");
  });

  /**
   * The transliterator used to drop an operator and run its arguments
   * together, so a citation said "12" where the title said one half (audit
   * r2). Operators now have structured forms, and one the table does not know
   * makes the span print as its own TeX — honest, rather than wrong.
   */
  describe("mathematics in a title", () => {
    const plain = (t: string) => texToPlain(t);

    it("gives a fraction a division, with parentheses only where needed", () => {
      expect(plain("Rates of \\(\\frac{1}{2}\\)")).toBe("Rates of 1/2");
      expect(plain("\\(\\frac{a+b}{2}\\)")).toBe("(a+b)/2");
      expect(plain("\\(\\frac{1}{n \\log n}\\)")).toBe("1/(n log n)");
    });

    it("names a binomial", () => {
      expect(plain("\\(\\binom{n}{2}\\)")).toBe("C(n, 2)");
      expect(plain("\\(\\binom{n}{k-1}\\)")).toBe("C(n, k-1)");
    });

    // The audit's list: a script must not swallow the grouping around it, and
    // anything this is unsure of becomes verbatim source rather than a guess.
    it("reads a symbol's script, and refuses a base it cannot identify", () => {
      expect(plain("\\(\\sigma^2\\)")).toBe("\u03c3\u00b2");
      expect(plain("\\(\\beta_0^2\\)")).toBe("\u03b2_0\u00b2");
      expect(plain("\\(\\log_2 n\\)")).toBe("log_2 n");
      // Sets, bars and big operators: source, not a guess.
      expect(plain("\\(\\{-1,1\\}^n\\)")).toBe("\\(\\{-1,1\\}^n\\)");
      expect(plain("\\(|N_i|^2\\)")).toBe("\\(|N_i|^2\\)");
      expect(plain("\\(\\sum_{i=1}^n x_i\\)")).toBe("\\(\\sum_{i=1}^n x_i\\)");
      // …and a set with no script still reads as a set.
      expect(plain("\\(\\{1,2\\}\\)")).toBe("{1,2}");
    });

    it("keeps a root, and only uses an index it can write exactly", () => {
      expect(plain("\\(\\sqrt{n}\\)")).toBe("√(n)");
      expect(plain("\\(\\sqrt[3]{n}\\)")).toBe("³√(n)");
      expect(plain("\\(\\sqrt[k]{n}\\)")).toBe("\\(\\sqrt[k]{n}\\)"); // no exact index
    });

    it("keeps a script's marker when there is no exact Unicode for it", () => {
      expect(plain("\\(\\log_2 n\\)")).toBe("log_2 n");
      expect(plain("\\(x^{2}\\)")).toBe("x²");
      expect(plain("\\(n^{-1/2}\\)")).toBe("n^(-1/2)");
      expect(plain("\\(n^{-1}\\)")).toBe("n⁻¹");
    });

    it("flattens an operator name", () => {
      expect(plain("\\(\\operatorname{Var}(X)\\)")).toBe("Var(X)");
      expect(plain("\\(\\mathrm{MSE}\\)")).toBe("MSE");
    });

    // A script binds to an ATOM. Dropping the grouping changed the meaning:
    // `{x+y}^2` was published as "x+y²" (audit r3).
    it("keeps the grouping a script applies to", () => {
      expect(plain("\\({x+y}^2\\)")).toBe("(x+y)\u00b2");
      expect(plain("\\(\\frac{1}{2}^{-1}\\)")).toBe("(1/2)\u207b\u00b9");
      expect(plain("\\({a+b}_{i}\\)")).toBe("(a+b)_i");
      // An atom needs no parentheses.
      expect(plain("\\(x^2\\)")).toBe("x\u00b2");
      expect(plain("\\(x_1^2\\)")).toBe("x_1\u00b2");
      // A closing bracket is NOT a base this can read, so the span is shown
      // as source rather than guessed at (audit r4).
      expect(plain("\\((x+y)^2\\)")).toBe("\\((x+y)^2\\)");
    });

    // The closing delimiter must be an UNESCAPED one here too.
    it("does not close a math span on an escaped dollar", () => {
      expect(plain("Cost $5 versus \\$10")).toBe("Cost $5 versus $10");
      expect(plain("Half $x$ and \\$3")).toBe("Half x and $3");
    });

    // Typography is prose's business: a verbatim span keeps its own `--`.
    it("does not retypeset a span it is preserving as source", () => {
      expect(plain("A \\(\\foo{a--b}\\) title")).toBe("A \\(\\foo{a--b}\\) title");
      expect(plain("A \\foo{x--y} title")).toBe("A \\foo{x--y} title");
      // …while the prose around it is still typeset.
      expect(plain("Pages 1--2 with \\(\\foo{a--b}\\)")).toBe(
        "Pages 1\u20132 with \\(\\foo{a--b}\\)",
      );
    });

    // FAIL CLOSED: the ORIGINAL source, all of it.
    it("preserves every argument of a macro it cannot read", () => {
      expect(plain("A \\frac{1}{2} title")).toBe("A \\frac{1}{2} title");
      expect(plain("A \\foo{a}{b}{c} title")).toBe("A \\foo{a}{b}{c} title");
      expect(plain("A \\foo{ title")).toBe("A \\foo{ title");
    });

    it("prints the TeX of a span it cannot read faithfully", () => {
      expect(plain("A \\(\\foo{a}{b}\\) bound")).toBe("A \\(\\foo{a}{b}\\) bound");
      expect(plain("Before \\(\\foo{x}{y}\\) after")).toContain("Before ");
      expect(plain("Before \\(\\foo{x}{y}\\) after")).toContain(" after");
    });
  });
});

/**
 * The plain-text form of every real title.
 *
 * The audit's failure was a transliterator that ran arguments together, so the
 * property asserted here is that nothing the SOURCE separated comes out joined.
 * None of the 22 shipped titles carries math today — that is asserted, not
 * assumed, so the day one does, the expectation below has to be written down
 * by hand rather than silently generated.
 */
describe("the shipped corpus reads as plain text", () => {
  const dir = resolve(import.meta.dirname, "..", "..", "doc", "presentation");
  const titles = existsSync(dir)
    ? readdirSync(dir)
        .filter((n) => existsSync(join(dir, n, "meta.json")))
        .map((n) => ({
          id: n,
          title: (JSON.parse(readFileSync(join(dir, n, "meta.json"), "utf8")) as { title: string })
            .title,
        }))
    : [];

  it.runIf(titles.length > 0)("covers every bundle", () => {
    expect(titles.length).toBeGreaterThanOrEqual(20);
  });

  // If this ever fails, add the bundle to EXPECTED below with a hand-checked
  // reading of its mathematics.
  it.runIf(titles.length > 0)("finds no title carrying TeX", () => {
    const mathy = titles.filter((t) => /\\[a-zA-Z(\[]|\$/.test(t.title)).map((t) => t.id);
    expect(mathy).toEqual([]);
  });

  /** Hand-checked plain-text readings for titles that DO carry mathematics. */
  const EXPECTED: Record<string, string> = {
    // (none today — see the test above)
  };

  for (const { id, title } of titles) {
    it(`${id}`, () => {
      const plain = texToPlain(title);
      if (EXPECTED[id]) {
        expect(plain).toBe(EXPECTED[id]);
        return;
      }
      // No mathematics: the reading is the title, with TeX dashes resolved and
      // nothing run together that the source kept apart.
      expect(plain).toBe(title.replace(/---/g, "\u2014").replace(/--/g, "\u2013"));
      const sourceWords = title.replace(/[-\u2013\u2014]+/g, " ").split(/\s+/).filter(Boolean);
      const plainWords = plain.replace(/[-\u2013\u2014]+/g, " ").split(/\s+/).filter(Boolean);
      expect(plainWords.length, "words were run together").toBe(sourceWords.length);
    });
  }
});

// Every real title, through the real entry builder.
describe("the shipped corpus produces valid BibTeX", () => {
  const dir = resolve(import.meta.dirname, "..", "..", "doc", "presentation");
  const metas = existsSync(dir)
    ? readdirSync(dir)
        .filter((n) => existsSync(join(dir, n, "meta.json")))
        .map((n) => ({
          id: n,
          meta: JSON.parse(readFileSync(join(dir, n, "meta.json"), "utf8")) as {
            title: string;
            created: string;
            wp_number: string | null;
            doi?: string | null;
            version?: number | null;
            revised?: string | null;
          },
        }))
    : [];

  it.runIf(metas.length > 0)("covers every bundle", () => {
    expect(metas.length).toBeGreaterThanOrEqual(20);
  });

  for (const { id, meta } of metas) {
    it(`${id}`, () => {
      const entry = bibtex(
        {
          id,
          title: meta.title,
          wpNumber: meta.wp_number,
          created: meta.created,
          version: meta.version,
          revised: meta.revised,
          doi: meta.doi,
          commit: "0123456789ab",
        },
        CTX,
      );
      expect(bibProblems(entry), entry).toEqual([]);
    });
  }
});
