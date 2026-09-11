import { describe, it, expect, vi, afterEach } from "vitest";
import {
  parseBib,
  citedKeys,
  verifyEntry,
  defaultLookup,
  UNREACHABLE,
  canonicalizeBibEntry,
  type BibEntry,
} from "../src/presentation/citations.js";

const BIB = `@article{robins1994,
  title = {Estimation of Regression Coefficients When Some Regressors Are Not Always Observed},
  author = {Robins, James M. and Rotnitzky, Andrea and Zhao, Lue Ping},
  journal = {JASA}, year = {1994}, doi = {10.1080/01621459.1994.10476818}
}
@misc{fake2025, title = {A Paper That Does Not Exist}, author = {Nobody, A.}, year = {2025}
}`;

describe("citations", () => {
  it("parses bib entries", () => {
    const entries = parseBib(BIB);
    expect(entries.map((e) => e.key)).toEqual(["robins1994", "fake2025"]);
    expect(entries[0].fields.year).toBe("1994");
    expect(entries[0].fields.author).toContain("Robins");
  });

  it("parses one-line entries and quoted fields", () => {
    const entries = parseBib(`@article{k, title = "X", author = {Robins}, year = {1994}}`);
    expect(entries).toEqual([
      {
        key: "k",
        type: "article",
        fields: { title: "X", author: "Robins", year: "1994" },
      },
    ]);
  });

  it("finds cited keys in tex including strays", () => {
    const tex = "as shown by \\citet{robins1994} and \\citep[see][]{robins1994, missing2020}";
    expect([...citedKeys(tex)].sort()).toEqual(["missing2020", "robins1994"]);
  });

  it("verifies via injected lookup: exact / minor / major", async () => {
    const lookup = async (e: BibEntry) =>
      e.key === "robins1994"
        ? {
            title: "Estimation of regression coefficients when some regressors are not always observed",
            authorFamily: "Robins",
            year: 1994,
          }
        : null;
    const entries = parseBib(BIB);
    expect((await verifyEntry(entries[0], lookup)).verdict).toBe("exact");
    expect((await verifyEntry(entries[1], lookup)).verdict).toBe("major");
    // Title + author identify the work; a year gap is a caveat that names the record's year.
    const wrongYear = async () => ({ title: entries[0].fields.title, authorFamily: "Robins", year: 2001 });
    const gap = await verifyEntry(entries[0], wrongYear);
    expect(gap.verdict).toBe("minor");
    expect(gap.detail).toContain("year 1994 vs record 2001");
  });

  it("accepts a registry family that is the trailing word of a particle name, in any author position", async () => {
    const entry: BibEntry = {
      key: "vanerven2015",
      type: "article",
      fields: { title: "Fast Rates in Statistical and Online Learning", author: "van Erven, Tim and Grünwald, Peter", year: "2015" },
    };
    const lastWord = async () => ({ title: entry.fields.title, authorFamily: "Erven", year: 2015 });
    expect((await verifyEntry(entry, lastWord)).verdict).toBe("exact");
    const secondAuthorFirst = async () => ({ title: entry.fields.title, authorFamily: "Grünwald", year: 2015 });
    expect((await verifyEntry(entry, secondAuthorFirst)).verdict).toBe("exact");
    const unparsableYear: BibEntry = { ...entry, fields: { ...entry.fields, year: "forthcoming" } };
    const v = await verifyEntry(unparsableYear, lastWord);
    expect(v.verdict).toBe("minor");
    expect(v.detail).toContain("year forthcoming vs record 2015");
  });

  it("same title, different identity is major and names both records for adjudication", async () => {
    const entry: BibEntry = {
      key: "lindsay1995",
      type: "book",
      fields: { title: "Mixture Models: Theory, Geometry and Applications", author: "Lindsay, Bruce G.", year: "1995" },
    };
    const review = async () => ({ title: entry.fields.title, authorFamily: "Jensen", year: 1997 });
    const v = await verifyEntry(entry, review);
    expect(v.verdict).toBe("major");
    expect(v.detail).toBe("title matches but author or year does not (record: Jensen 1997; entry: lindsay 1995)");
  });

  it("a title-query record under a book's short title with author and year agreeing is a caveat, not a drop", async () => {
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: { title: "Causal Inference for Statistics, Social, and Biomedical Sciences: An Introduction", author: "Imbens, Guido W. and Rubin, Donald B.", year: "2015" },
    };
    const shortTitle = async () => ({ title: "Causal Inference for Statistics, Social, and Biomedical Sciences", authorFamily: "Imbens", year: 2015 });
    const v = await verifyEntry(book, shortTitle);
    expect(v.verdict).toBe("minor");
    expect(v.detail).toContain("check the subtitle");
    const review = async () => ({ title: book.fields.title, authorFamily: "Blumberg", year: 2016 });
    expect((await verifyEntry(book, review)).verdict).toBe("major");
  });

  it("a record with no author cannot contradict: title and year agreeing is a caveat, never exact", async () => {
    const entry: BibEntry = {
      key: "kasahara2009",
      type: "article",
      fields: { title: "Nonparametric Identification of Finite Mixture Models of Dynamic Discrete Choices", author: "Kasahara, Hiroyuki and Shimotsu, Katsumi", year: "2009", doi: "10.3982/ECTA6763" },
    };
    const noAuthor = async () => ({ title: entry.fields.title, authorFamily: "", year: 2009, authoritative: true });
    const v = await verifyEntry(entry, noAuthor);
    expect(v.verdict).toBe("minor");
    expect(v.detail).toContain("lists no author");
    const noAuthorWrongYear = async () => ({ title: entry.fields.title, authorFamily: "", year: 2014 });
    expect((await verifyEntry(entry, noAuthorWrongYear)).verdict).toBe("major");
  });

  it("a generic author-less record never confirms an entry, whether whole or as a short title", async () => {
    const fabricated: BibEntry = { key: "x", type: "article", fields: { title: "Introduction", author: "Nobody, A.", year: "2019" } };
    expect((await verifyEntry(fabricated, async () => ({ title: "Introduction", authorFamily: "", year: 2019 }))).verdict).toBe("major");
    const discussion: BibEntry = { key: "y", type: "article", fields: { title: "Comment: Performance of Double-Robust Estimators", author: "Nobody, A.", year: "2011" } };
    expect((await verifyEntry(discussion, async () => ({ title: "Comment", authorFamily: "", year: 2011 }))).verdict).toBe("major");
    // A title-query record sharing only the core with a different subtitle is a different work.
    const other: BibEntry = { key: "z", type: "article", fields: { title: "Causal Inference: A Primer", author: "Imbens, Guido W.", year: "2015" } };
    expect((await verifyEntry(other, async () => ({ title: "Causal Inference: The Mixtape", authorFamily: "Imbens", year: 2015 }))).verdict).toBe("major");
  });

  it("ignores publisher formula markup in a registry title and a whole name in the family slot", async () => {
    const { stripRegistryMarkup } = await import("../src/presentation/citations.js");
    expect(stripRegistryMarkup("Minimax Estimation of the <inline-formula><tex-math>$L_{1}$</tex-math></inline-formula> Distance")).toBe("Minimax Estimation of the $L_{1}$ Distance");
    const entry: BibEntry = {
      key: "jiao2018",
      type: "article",
      fields: { title: "Minimax Estimation of the $L_1$ Distance", author: "Jiao, Jiantao and Han, Yanjun and Weissman, Tsachy", year: "2018" },
    };
    const marked = async () => ({ title: "Minimax Estimation of the <inline-formula><tex-math>$L_{1}$</tex-math></inline-formula> Distance", authorFamily: "Jiao", year: 2018, authoritative: true });
    expect((await verifyEntry(entry, marked)).verdict).toBe("exact");
    const wholeName = async () => ({ title: entry.fields.title, authorFamily: "Jiantao Jiao", year: 2018, authoritative: true });
    expect((await verifyEntry(entry, wholeName)).verdict).toBe("exact");
  });

  it("matches diacritics and LaTeX accents, leading articles, and question-mark subtitles", async () => {
    const savje: BibEntry = { key: "savje2021", type: "article", fields: { title: "Average Treatment Effects in the Presence of Unknown Interference", author: "S\\\"avje, Fredrik and Aronow, Peter M. and Hudgens, Michael G.", year: "2021" } };
    expect((await verifyEntry(savje, async () => ({ title: savje.fields.title, authorFamily: "Sävje", year: 2021 }))).verdict).toBe("exact");
    const erdos: BibEntry = { key: "gm2016", type: "book", fields: { title: "Erd\\H{o}s--Ko--Rado Theorems: Algebraic Approaches", author: "Godsil, Chris and Meagher, Karen", year: "2016" } };
    expect((await verifyEntry(erdos, async () => ({ title: "Erdős–Ko–Rado Theorems: Algebraic Approaches", authorFamily: "Godsil", year: 2016 }))).verdict).toBe("exact");
    const article: BibEntry = { key: "filmus", type: "article", fields: { title: "An Orthogonal Basis for Functions over a Slice of the Boolean Hypercube", author: "Filmus, Yuval", year: "2016" } };
    expect((await verifyEntry(article, async () => ({ title: "Orthogonal basis for functions over a slice of the Boolean hypercube", authorFamily: "Filmus", year: 2016 }))).verdict).toBe("exact");
    const question: BibEntry = { key: "sobel", type: "article", fields: { title: "What Do Randomized Studies of Housing Mobility Demonstrate? Causal Inference in the Face of Interference", author: "Sobel, Michael E.", year: "2006" } };
    expect((await verifyEntry(question, async () => ({ title: "What Do Randomized Studies of Housing Mobility Demonstrate?", authorFamily: "Sobel", year: 2006, authoritative: true }))).verdict).toBe("minor");
  });

  it("matches letters without a Unicode decomposition, such as the dotless i in Turkish names", async () => {
    const entry: BibEntry = { key: "varici2025", type: "article", fields: { title: "Score-Based Causal Representation Learning", author: "Var{\\i}c{\\i}, Burak and Acarturk, Emre", year: "2025" } };
    expect((await verifyEntry(entry, async () => ({ title: entry.fields.title, authorFamily: "Varıcı", year: 2024 }))).verdict).toBe("exact");
    const thorn: BibEntry = { key: "thor2020", type: "article", fields: { title: "Icelandic Cohort Effects", author: "{\\TH}{\\'o}rarinsson, Einar and {\\AE}gisson, Jon", year: "2020" } };
    expect((await verifyEntry(thorn, async () => ({ title: thorn.fields.title, authorFamily: "Þórarinsson", year: 2020 }))).verdict).toBe("exact");
    expect((await verifyEntry(thorn, async () => ({ title: thorn.fields.title, authorFamily: "Ægisson", year: 2020 }))).verdict).toBe("exact");
  });

  it("never mistakes an ordinary macro for an accent", async () => {
    for (const [tex, plain] of [["$\\beta$-mixing rates", "β-mixing rates"], ["\\textit{Weak} limits", "Weak limits"], ["Bounds \\dots\\ here", "Bounds here"], ["The \\rho and \\tau scales", "The ρ and τ scales"], ["A \\vec{x} lemma", "A x lemma"], ["\\kappa-cover results", "κ-cover results"]] as const) {
      const entry: BibEntry = { key: "m", type: "article", fields: { title: tex, author: "Doe, Jane", year: "2020" } };
      const registryTitle = plain.replace(/[βρτκ]/g, (c) => ({ "β": "beta", "ρ": "rho", "τ": "tau", "κ": "kappa" })[c]!);
      // The registry spells the Greek letter out (as Crossref does for a plain-text title): the LaTeX side must reduce to the same word, not to a truncated one.
      const wrongTruncation = registryTitle.replace(/\b(beta|rho|tau|kappa|Weak|Bounds|A x)\b/, (w) => w.slice(1));
      expect((await verifyEntry(entry, async () => ({ title: wrongTruncation, authorFamily: "Doe", year: 2020 }))).verdict).not.toBe("exact");
    }
  });

  it("title identity ignores a registry's spacing typo", async () => {
    const entry: BibEntry = {
      key: "sidiropoulos2000",
      type: "article",
      fields: { title: "On the uniqueness of multilinear decomposition of N-way arrays", author: "Sidiropoulos, Nicholas D. and Bro, Rasmus", year: "2000" },
    };
    const typo = async () => ({ title: "On the uniqueness of multilinear decomposition ofN-way arrays", authorFamily: "Sidiropoulos", year: 2000, authoritative: true });
    expect((await verifyEntry(entry, typo)).verdict).toBe("exact");
  });

  it("a hand-verified entry is kept on its recorded authority without consulting the registry", async () => {
    const entry: BibEntry = {
      key: "lindsay1995",
      type: "book",
      fields: { title: "Mixture Models", author: "Lindsay, Bruce G.", year: "1995", verifiedby: "ISBN 9780940600324" },
    };
    const lookup = vi.fn(async () => null);
    expect(await verifyEntry(entry, lookup)).toEqual({ key: "lindsay1995", verdict: "minor", detail: "hand-verified (ISBN 9780940600324)" });
    expect(lookup).not.toHaveBeenCalled();
  });

  it("does not confuse substring-related author families", async () => {
    const entry: BibEntry = {
      key: "lin2020",
      type: "article",
      fields: { title: "A Generic Result", author: "Lin, Alice", year: "2020" },
    };
    const wrongAuthor = async () => ({ title: entry.fields.title, authorFamily: "Li", year: 2020 });
    expect((await verifyEntry(entry, wrongAuthor)).verdict).toBe("major");
  });

  it("id-authoritative record: a title mismatch is a field fix (minor), not a wrong-source drop", async () => {
    // Books store only the short title in Crossref, so the DOI-fetched record's title differs
    // from the entry's full title-with-subtitle. As long as the author corroborates, the DOI
    // confirms the source — keep it (minor), never drop it (major).
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: {
        title: "Causal Inference for Statistics, Social, and Biomedical Sciences: An Introduction",
        author: "Imbens, Guido W. and Rubin, Donald B.",
        year: "2015",
        doi: "10.1017/CBO9781139025751",
      },
    };
    const shortTitleByDoi = async () => ({
      title: "Causal Inference for Statistics, Social, and Biomedical Sciences",
      authorFamily: "Imbens",
      year: 2015,
      authoritative: true,
    });
    expect((await verifyEntry(book, shortTitleByDoi)).verdict).toBe("minor");
  });

  it("id-authoritative but author also mismatches stays major (guards a stray DOI hitting another work)", async () => {
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: { title: "Causal Inference ...", author: "Imbens, Guido W.", year: "2015", doi: "10.x/y" },
    };
    const otherPaperByDoi = async () => ({
      title: "A completely different paper",
      authorFamily: "Smith",
      year: 2015,
      authoritative: true,
    });
    expect((await verifyEntry(book, otherPaperByDoi)).verdict).toBe("major");
  });

  it("authoritative id needs two corroborating identity dimensions for a field repair", async () => {
    const entry: BibEntry = {
      key: "smith2020",
      type: "article",
      fields: { title: "A Generic Result", author: "Smith, Alice", year: "2020", doi: "10.x/y" },
    };
    const sameTitleWrongIdentity = async () => ({
      title: entry.fields.title,
      authorFamily: "Jones",
      year: 1990,
      authoritative: true,
    });
    const sameAuthorWrongIdentity = async () => ({
      title: "A Different Result",
      authorFamily: "Smith",
      year: 1990,
      authoritative: true,
    });
    const sameAuthorYearDifferentWork = async () => ({
      title: "An Entirely Different Paper",
      authorFamily: "Smith",
      year: 2020,
      authoritative: true,
    });
    expect((await verifyEntry(entry, sameTitleWrongIdentity)).verdict).toBe("major");
    expect((await verifyEntry(entry, sameAuthorWrongIdentity)).verdict).toBe("major");
    expect((await verifyEntry(entry, sameAuthorYearDifferentWork)).verdict).toBe("major");

    const titledEntry: BibEntry = {
      ...entry,
      fields: { ...entry.fields, title: "Inference: Randomized Experiments" },
    };
    const sharedCoreDifferentSubtitle = async () => ({
      title: "Inference: Observational Studies",
      authorFamily: "Smith",
      year: 2020,
      authoritative: true,
    });
    expect((await verifyEntry(titledEntry, sharedCoreDifferentSubtitle)).verdict).toBe("major");
  });

  it("UNREACHABLE registry is non-blocking (minor), not a hallucination rejection", async () => {
    const entry: BibEntry = {
      key: "fan2025",
      type: "misc",
      fields: { title: "Some Real Paper", author: "Fan, X.", year: "2025", eprint: "2502.06008" },
    };
    const v = await verifyEntry(entry, async () => UNREACHABLE);
    expect(v.verdict).toBe("minor");
    expect(v.detail).toMatch(/unreachable/i);
  });

  it("normalizes fields only from an authoritative id record", () => {
    const rec = { title: "Canonical Title", authorFamily: "Robins", author: "Robins, James", year: 1995, authoritative: true };
    const fixed = canonicalizeBibEntry(BIB, "robins1994", rec)!;
    const entry = parseBib(fixed)[0];
    expect(entry.fields.title).toBe("Canonical Title");
    expect(entry.fields.author).toBe("Robins, James");
    expect(entry.fields.year).toBe("1995");
    expect(entry.fields.doi).toBe("10.1080/01621459.1994.10476818");
    expect(canonicalizeBibEntry(BIB, "robins1994", { ...rec, authoritative: false })).toBeNull();
  });

  it("decodes and TeX-escapes ampersands in authoritative metadata", () => {
    const rec = { title: "Patents-R &amp; D Relationship", authorFamily: "Hausman", year: 1984, authoritative: true };
    const fixed = canonicalizeBibEntry(BIB, "robins1994", rec)!;
    expect(fixed).toContain("Patents-R \\& D Relationship");
    expect(fixed).not.toContain("&amp;");
  });
});

describe("defaultLookup: transient-unreachable vs definitively-absent", () => {
  const realFetch = globalThis.fetch;
  afterEach(() => {
    globalThis.fetch = realFetch;
    vi.useRealTimers();
  });

  // A wrong Crossref title-query hit — the record the OLD fallback would have laundered into a "major".
  const wrongCrossrefHit = {
    ok: true,
    status: 200,
    json: async () => ({
      message: { items: [{ title: ["A Completely Different Paper"], author: [{ family: "Other" }], issued: { "date-parts": [[2024]] } }] },
    }),
    text: async () => "",
  };
  const arxivEmptyFeed = {
    ok: true,
    status: 200,
    json: async () => ({}),
    text: async () => "<feed><title>ArXiv Query</title></feed>", // no entry <title> → no record
  };

  const runLookup = async (entry: BibEntry) => {
    vi.useFakeTimers();
    const p = defaultLookup(entry);
    await vi.runAllTimersAsync(); // drive politeFetch's throttle + backoff sleeps
    return p;
  };

  it("arXiv id unreachable (429) → UNREACHABLE, never falls back to the wrong title hit", async () => {
    const crossref = vi.fn(async () => wrongCrossrefHit);
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("export.arxiv.org")) return { ok: false, status: 429 } as unknown as Response;
      if (u.includes("api.crossref.org")) return crossref() as unknown as Promise<Response>;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "fan2025",
      type: "misc",
      fields: { title: "Causal Inference under Interference", author: "Fan, X.", year: "2025", eprint: "2502.06008" },
    };
    const rec = await runLookup(entry);
    expect(rec).toBe(UNREACHABLE); // NOT the wrong Crossref paper
    expect(crossref).not.toHaveBeenCalled(); // the laundering title-query never ran
  });

  it("arXiv id definitively absent (reachable, empty feed) → still title-checked → fabricated id caught (major)", async () => {
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.crossref.org")) return wrongCrossrefHit as unknown as Response;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "fake2030",
      type: "misc",
      fields: { title: "A Paper That Does Not Exist", author: "Nobody, A.", year: "2030", eprint: "9999.99999" },
    };
    vi.useFakeTimers();
    const p = verifyEntry(entry, defaultLookup);
    await vi.runAllTimersAsync();
    expect((await p).verdict).toBe("major"); // reachable-but-absent id is not laundered to non-blocking
  });

  it("stops at a Crossref identity hit and prefers the same work at another year over an unrelated top hit", async () => {
    const entry: BibEntry = {
      key: "lee2009",
      type: "article",
      fields: { title: "Training, Wages, and Sample Selection", author: "Lee, David S.", year: "2009" },
    };
    const item = (title: string, family: string, year: number) =>
      ({ title: [title], author: [{ family }], issued: { "date-parts": [[year]] } });
    const fetchMock = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("api.crossref.org")) {
        return { ok: true, status: 200, json: async () => ({ message: { items: [
          item("Training, Wages, and Sample Selection", "Other", 2004),
          item("Training, Wages, and Sample Selection", "Lee", 2009),
        ] } }), text: async () => "" } as unknown as Response;
      }
      throw new Error(`unexpected fetch ${u}`);
    });
    globalThis.fetch = fetchMock as unknown as typeof fetch;
    const rec = await runLookup(entry);
    expect(rec && rec !== UNREACHABLE ? rec.authorFamily : null).toBe("Lee");
    expect(fetchMock).toHaveBeenCalledTimes(1);

    // Crossref lists a book's reviews under the full title and the book itself under its short title.
    const book: BibEntry = {
      key: "imbens2015",
      type: "book",
      fields: { title: "Causal Inference for Statistics, Social, and Biomedical Sciences: An Introduction", author: "Imbens, Guido W. and Rubin, Donald B.", year: "2015" },
    };
    const bookFetch = vi.fn(async (url: string | URL) => {
      if (!String(url).includes("api.crossref.org")) throw new Error(`unexpected fetch ${String(url)}`);
      return { ok: true, status: 200, json: async () => ({ message: { items: [
        item(book.fields.title!, "Blumberg", 2016),
        item("Causal Inference for Statistics, Social, and Biomedical Sciences", "Imbens", 2015),
      ] } }), text: async () => "" } as unknown as Response;
    });
    globalThis.fetch = bookFetch as unknown as typeof fetch;
    const bookRec = await runLookup(book);
    expect(bookRec && bookRec !== UNREACHABLE ? [bookRec.authorFamily, bookRec.year] : null).toEqual(["Imbens", 2015]);
    expect(bookFetch).toHaveBeenCalledTimes(1);

    // An author-less registry record of the work outranks an unrelated top hit, once nothing
    // author-confirmed exists anywhere.
    const authorless: BibEntry = { key: "stewart1990", type: "book", fields: { title: "Matrix Perturbation Theory", author: "Stewart, G. W. and Sun, Ji-guang", year: "1990" } };
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("api.crossref.org")) {
        return { ok: true, status: 200, json: async () => ({ message: { items: [
          item("Matrix Perturbation Theory", "Li", 2006),
          { title: ["Matrix perturbation theory"], issued: { "date-parts": [[1991]] } },
        ] } }), text: async () => "" } as unknown as Response;
      }
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.openalex.org")) return { ok: true, status: 200, json: async () => ({ results: [] }), text: async () => "" } as unknown as Response;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;
    const authorlessRec = await runLookup(authorless);
    expect(authorlessRec && authorlessRec !== UNREACHABLE ? [authorlessRec.authorFamily, authorlessRec.year] : null).toEqual(["", 1991]);

    // No identity hit anywhere: the same work at another year still beats the unrelated top hit.
    const calls: string[] = [];
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      calls.push(u);
      if (u.includes("api.crossref.org")) {
        return { ok: true, status: 200, json: async () => ({ message: { items: [
          item("Training, Wages, and Sample Selection", "Other", 2004),
          item("Training, Wages, and Sample Selection", "Lee", 2005),
        ] } }), text: async () => "" } as unknown as Response;
      }
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.openalex.org")) {
        expect(u).toContain("filter=title.search:Training%20Wages%20and%20Sample%20Selection&");
        return { ok: true, status: 200, json: async () => ({ results: [] }), text: async () => "" } as unknown as Response;
      }
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;
    const other = await runLookup(entry);
    expect(other && other !== UNREACHABLE ? [other.authorFamily, other.year] : null).toEqual(["Lee", 2005]);
    expect(calls.some((u) => u.includes("api.openalex.org"))).toBe(true);
  });

  it("an id-less entry whose title search hit an unreachable registry is transient, not a rejection", async () => {
    const entry: BibEntry = {
      key: "manski1990",
      type: "article",
      fields: { title: "Nonparametric Bounds on Treatment Effects", author: "Manski, Charles F.", year: "1990" },
    };
    const fetchFor = (openAlexStatus: number) => vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("api.crossref.org")) return wrongCrossrefHit as unknown as Response;
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.openalex.org")) {
        return openAlexStatus === 200
          ? { ok: true, status: 200, json: async () => ({ results: [] }), text: async () => "" } as unknown as Response
          : { ok: false, status: openAlexStatus } as unknown as Response;
      }
      return { ok: false, status: 404 } as unknown as Response;
    });
    globalThis.fetch = fetchFor(429) as unknown as typeof fetch;
    expect(await runLookup(entry)).toBe(UNREACHABLE);
    globalThis.fetch = fetchFor(200) as unknown as typeof fetch;
    const rec = await runLookup(entry);
    expect(rec && rec !== UNREACHABLE ? rec.title : null).toBe("A Completely Different Paper"); // every registry answered: a real mismatch
  });

  it("uses an exact OpenAlex title match when Crossref's top title-search hit is unrelated", async () => {
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("api.crossref.org")) return wrongCrossrefHit as unknown as Response;
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.openalex.org")) {
        return {
          ok: true,
          status: 200,
          json: async () => ({
            results: [{
              title: "Conservative variance estimation for sampling designs with zero pairwise inclusion probabilities",
              publication_year: 2012,
              authorships: [
                { author: { display_name: "Peter M. Aronow" } },
                { author: { display_name: "Cyrus Samii" } },
              ],
            }],
          }),
          text: async () => "",
        } as unknown as Response;
      }
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "AronowSamii2013",
      type: "article",
      fields: {
        title: "Conservative Variance Estimation for Sampling Designs with Zero Pairwise Inclusion Probabilities",
        author: "Aronow, Peter M. and Samii, Cyrus",
        year: "2013",
      },
    };
    const rec = await runLookup(entry);
    expect(rec).toMatchObject({
      title: "Conservative variance estimation for sampling designs with zero pairwise inclusion probabilities",
      authorFamily: "Aronow",
      year: 2012,
    });
    expect((await verifyEntry(entry, async () => rec)).verdict).toBe("exact");
  });

  it("continues past an exact-title Crossref hit with the wrong author to the matching OpenAlex work", async () => {
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u.includes("api.crossref.org")) {
        return {
          ...wrongCrossrefHit,
          json: async () => ({
            message: { items: [{
              title: ["A Generic Result"],
              author: [{ family: "Li" }],
              issued: { "date-parts": [[2020]] },
            }] },
          }),
        } as unknown as Response;
      }
      if (u.includes("export.arxiv.org")) return arxivEmptyFeed as unknown as Response;
      if (u.includes("api.openalex.org")) {
        return {
          ok: true,
          status: 200,
          json: async () => ({
            results: [{
              title: "A Generic Result",
              publication_year: 2020,
              authorships: [{ author: { display_name: "Alice Lin" } }],
            }],
          }),
          text: async () => "",
        } as unknown as Response;
      }
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "lin2020",
      type: "article",
      fields: { title: "A Generic Result", author: "Lin, Alice", year: "2020" },
    };
    const rec = await runLookup(entry);
    expect(rec).toMatchObject({ authorFamily: "Lin", year: 2020 });
    expect((await verifyEntry(entry, async () => rec)).verdict).toBe("exact");
  });

  it("uses a canonical JMLR article URL instead of a wrong title-search hit", async () => {
    const crossref = vi.fn(async () => wrongCrossrefHit);
    globalThis.fetch = vi.fn(async (url: string | URL) => {
      const u = String(url);
      if (u === "https://www.jmlr.org/papers/v7/shimizu06a.html") {
        return {
          ok: true,
          status: 200,
          text: async () => `<html><head>
            <meta content="A Linear Non-Gaussian Acyclic Model for Causal Discovery" name="citation_title">
            <meta name="citation_author" content="Shohei Shimizu">
            <meta name="citation_author" content="Aapo Hyv&amp;#228;rinen">
            <meta name="citation_publication_date" content="2006">
          </head></html>`,
          json: async () => ({}),
        } as unknown as Response;
      }
      if (u.includes("api.crossref.org")) return crossref() as unknown as Promise<Response>;
      return { ok: false, status: 404 } as unknown as Response;
    }) as unknown as typeof fetch;

    const entry: BibEntry = {
      key: "shimizu2006",
      type: "article",
      fields: {
        title: "A Linear Non-Gaussian Acyclic Model for Causal Discovery",
        author: "Shimizu, Shohei and Hyvarinen, Aapo",
        year: "2006",
        url: "https://www.jmlr.org/papers/v7/shimizu06a.html",
      },
    };
    const rec = await runLookup(entry);
    expect(rec).toMatchObject({
      title: entry.fields.title,
      authorFamily: "Shimizu",
      author: "Shohei Shimizu and Aapo Hyvärinen",
      year: 2006,
      authoritative: true,
    });
    expect(crossref).not.toHaveBeenCalled();
    expect((await verifyEntry(entry, async () => rec)).verdict).toBe("exact");
  });
});
