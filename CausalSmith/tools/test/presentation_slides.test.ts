import { describe, expect, it } from "vitest";
import { lintSlides, parseSlidesMd } from "../src/presentation/slides.js";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { bibSummary, extractDeckMarkdown, extractDsl, SLIDES_READER_PASSES, stageP6 } from "../src/presentation/stages/p6_slides.js";
import { freshPaperState } from "../src/presentation/state.js";
import { hashEnvBody } from "../src/presentation/tex_anchors.js";
import type { PaperDeps, StageIO } from "../src/presentation/pipeline.js";
import { parseFigureDsl, renderFigureSvg } from "../src/presentation/figure_layout.js";

const BLOCKS = [
  { obj_id: "ass:design", kind: "assumption" },
  { obj_id: "thm:main", kind: "theorem" },
  { obj_id: "thm:lower", kind: "theorem" },
];

const filler = Array.from({ length: 6 }, (_, i) => `## Filler ${i + 1}\n- a point`).join("\n\n---\n\n");

const appendix = "\n\n---\n\n## Appendix: main theorem\nThe exact statement.\n@formal thm:main";

function deck(body: string, backup = appendix): string {
  return `# A Talk\nOne-line pitch.\n\n---\n\n${body}\n\n---\n\n${filler}${backup}`;
}

describe("parseSlidesMd", () => {
  it("splits slides and types directive blocks", () => {
    const doc = parseSlidesMd(deck(
      "## Main result\n@informal thm:main: Plain headline.\nSome prose.\n@formal obj:thm:lower",
    ));
    expect(doc.talkTitle).toBe("A Talk");
    const main = doc.slides[1];
    expect(main.title).toBe("Main result");
    expect(main.blocks).toEqual([
      { kind: "informal", objId: "thm:main", text: "Plain headline." },
      { kind: "prose", md: "Some prose." },
      { kind: "formal", objId: "thm:lower" }, // obj: prefix normalized away
    ]);
  });

  it("rejects a deck without a title slide and slides without headings", () => {
    expect(() => parseSlidesMd("## no title\nx")).toThrow(/# <talk title>/);
    expect(() => parseSlidesMd("# T\n\n---\n\nno heading here")).toThrow(/slide 2/);
  });
});

describe("lintSlides", () => {
  it("passes a well-formed deck", () => {
    const doc = parseSlidesMd(deck("## Results\n@formal thm:main\n@informal thm:lower: Lower bound in words."));
    expect(lintSlides(doc, BLOCKS)).toEqual([]);
  });

  it("flags unknown obj_ids, a theorem-free deck, non-verbatim displays, and empty headlines", () => {
    const doc = parseSlidesMd(deck(
      "## Results\n@formal thm:nope\n@informal ass:design:\nAnd \\[x=1\\] inline-displayed.",
      "",
    ));
    const gates = lintSlides(doc, BLOCKS).map((p) => p.gate).sort();
    expect(gates).toEqual([
      "slides-display-not-verbatim", // \[x=1\] is not copied from the paper
      "slides-empty-informal",
      "slides-no-formal-theorem",
      "slides-no-theorem", // no theorem block on any slide
      "slides-unknown-obj",
    ]);
  });

  it("allows a \\[…\\] display only when copied verbatim from the corpus", () => {
    const doc = parseSlidesMd(deck(
      "## Results\n@informal thm:main: Words.\n@informal thm:lower: Words.\nThe rate is \\[ n^{-1} \\log d \\] here.",
    ));
    expect(lintSlides(doc, BLOCKS, "we show risk \\(n^{-1}\\log d\\) for…").map((p) => p.gate)).toEqual([]);
    expect(lintSlides(doc, BLOCKS, "unrelated text").map((p) => p.gate)).toEqual(["slides-display-not-verbatim"]);
    const composed = parseSlidesMd(deck("## Results\n@informal thm:main: W.\n@informal thm:lower: W.\n$$x$$"));
    expect(lintSlides(composed, BLOCKS, "$$x$$").map((p) => p.gate)).toEqual(["slides-displayed-math"]);
    // Substring laundering: a prose fragment inside \[…\] is not a formula even
    // when the corpus contains it, and an unmatched \[ is malformed.
    const laundered = parseSlidesMd(deck(
      "## Results\n@informal thm:main: W.\n@informal thm:lower: W.\nSo \\[the\\] rate.",
    ));
    expect(lintSlides(laundered, BLOCKS, "we show the rate").map((p) => p.gate)).toEqual([
      "slides-display-not-verbatim",
    ]);
    // A TeX row break with spacing inside a display is not a second opener.
    const rowBreak = parseSlidesMd(deck(
      "## Results\n@informal thm:main: W.\n@informal thm:lower: W.\n\\[ a=1,\\\\[3mm] b=2 \\]",
    ));
    expect(lintSlides(rowBreak, BLOCKS, "a=1,\\\\[3mm]b=2").map((p) => p.gate)).toEqual([]);
    // A real opener right after a row break is still an opener, and `aligned` inside a display is legal.
    const afterBreak = parseSlidesMd(deck("## Results\n@informal thm:main: W.\nx \\\\\\[ y=2 \\]"));
    expect(lintSlides(afterBreak, BLOCKS, "unrelated").map((p) => p.gate)).toEqual(["slides-display-not-verbatim"]);
    const aligned = parseSlidesMd(deck("## Results\n@informal thm:main: W.\n\\[\\begin{aligned} a&=1 \\end{aligned}\\]"));
    expect(lintSlides(aligned, BLOCKS, "\\begin{aligned} a&=1 \\end{aligned}").map((p) => p.gate)).toEqual([]);
    const unmatched = parseSlidesMd(deck(
      "## Results\n@informal thm:main: W.\n@informal thm:lower: W.\nSo \\[ x=1 dangling.",
    ));
    expect(lintSlides(unmatched, BLOCKS, "x=1").map((p) => p.gate)).toEqual(["slides-displayed-math"]);
  });

  it("flags a bare @formal slide and third-person 'the paper' voice", () => {
    const bare = parseSlidesMd(deck("## Main result\n@formal thm:main\n\n---\n\n## B\n@informal thm:lower: W."));
    expect(lintSlides(bare, BLOCKS).map((p) => p.gate)).toEqual(["slides-bare-formal"]);
    const voiced = parseSlidesMd(deck(
      "## Main result\nThe paper establishes a bound.\n@formal thm:main\n@informal thm:lower: W.",
    ));
    expect(lintSlides(voiced, BLOCKS).map((p) => p.gate)).toEqual(["slides-voice"]);
  });

  it("keeps slides readable: no oversized or doubled @formal, at most six bullets", () => {
    const blocks = [{ obj_id: "thm:main", kind: "theorem", bodyChars: 4000 }, { obj_id: "ass:design", kind: "assumption", bodyChars: 100 }];
    const long = parseSlidesMd(deck("## Main result\nIn words.\n@formal thm:main"));
    expect(lintSlides(long, blocks).map((p) => p.gate)).toEqual(["slides-formal-too-long"]);
    const informal = parseSlidesMd(deck("## Main result\n@informal thm:main: In words.\n@formal ass:design"));
    expect(lintSlides(informal, blocks)).toEqual([]);
    const doubled = parseSlidesMd(deck("## Main result\n@informal thm:main: W.\n@formal ass:design\n@formal ass:design"));
    expect(lintSlides(doubled, blocks).map((p) => p.gate)).toEqual(["slides-density"]);
    const bullets = Array.from({ length: 7 }, (_, i) => `- point ${i}`).join("\n");
    const dense = parseSlidesMd(deck(`## Main result\n@informal thm:main: W.\n${bullets}`));
    expect(lintSlides(dense, blocks).map((p) => p.gate)).toEqual(["slides-density"]);
    // Sub-items and display-math continuation lines are not bullets.
    const nested = parseSlidesMd(deck(
      "## Main result\n@informal thm:main: W.\n- a\n  - a1\n  - a2\n- b\n  - b1\n- c\n\\[\nx=1\n- b\n- c\n- d\n\\]",
    ));
    expect(lintSlides(nested, blocks, "x=1-b-c-d").map((p) => p.gate)).toEqual([]);
  });

  it("requires the exact theorem somewhere, and backup slides only after the talk", () => {
    const informalOnly = parseSlidesMd(deck("## Main result\n@informal thm:main: W.", ""));
    expect(lintSlides(informalOnly, BLOCKS).map((p) => p.gate)).toEqual(["slides-no-formal-theorem"]);
    const long = [{ obj_id: "thm:main", kind: "theorem", bodyChars: 4000 }];
    expect(lintSlides(parseSlidesMd(deck("## Main result\n@informal thm:main: W.")), long)).toEqual([]);
    const misplaced = parseSlidesMd(`# T\npitch${appendix}\n\n---\n\n## Main result\n@informal thm:main: W.\n\n---\n\n${filler}\n\n---\n\n${filler}`);
    expect(lintSlides(misplaced, long).map((p) => p.gate)).toContain("slides-backup");
  });

  it("flags a deck too short for a 15–20 minute talk", () => {
    const doc = parseSlidesMd("# T\npitch\n\n---\n\n## Only\nWords.\n@formal thm:main");
    expect(lintSlides(doc, BLOCKS).map((p) => p.gate)).toContain("slides-deck-shape");
  });
});

describe("figures", () => {
  it("parses @figure and lints name/caption/count", () => {
    const doc = parseSlidesMd(deck(
      "## Results\nIn words.\n@formal thm:main\n@informal thm:lower: W.\n@figure regime-map: Which term dominates where.",
    ));
    expect(doc.slides[1].blocks).toContainEqual({
      kind: "figure",
      name: "regime-map",
      caption: "Which term dominates where.",
    });
    expect(lintSlides(doc, BLOCKS)).toEqual([]);
    const bad = parseSlidesMd(deck(
      "## Results\n@formal thm:main\n@informal thm:lower: W.\n@figure Bad_Name:\n@figure a: x\n@figure b: x\n@figure c: x",
    ));
    const gates = lintSlides(bad, BLOCKS).map((p) => p.gate);
    expect(gates).toContain("slides-figure-name");
    expect(gates).toContain("slides-figure-caption");
    expect(gates).toContain("slides-figure-count");
  });

  it("extractDsl keeps only node/edge lines and rejects DSL-free output", () => {
    const out = extractDsl("Here you go:\n```\nnode a | Title A\nnode b | Title B | detail\nedge a -> b\n```\ndone");
    expect(out).toBe("node a | Title A\nnode b | Title B | detail\nedge a -> b");
    expect(() => extractDsl("no dsl at all")).toThrow(/no `node`\/`edge`/);
  });

  it("parseFigureDsl validates ids, titles, and edge endpoints", () => {
    expect(() => parseFigureDsl("edge a -> b")).toThrow(/no nodes/);
    expect(() => parseFigureDsl("node a | T\nedge a -> ghost")).toThrow(/undeclared node "ghost"/);
    expect(() => parseFigureDsl("node a | T\nnode a | T2")).toThrow(/duplicate/);
    expect(() => parseFigureDsl("node a | T\nedge a -> a")).toThrow(/self-loop/);
  });

  it("renderFigureSvg lays out deterministically: every box fits its text, every edge is drawn", () => {
    const spec = parseFigureDsl(
      [
        "node data | Observed data",
        "node poly | Heavy-light polynomial | plug-in on heavy | Chebyshev on light",
        "node coll | Occupancy collision | crossed cells only",
        "node zero | Zero branch",
        "node sel | Known-radius selector | compares scales via σ",
        "edge data -> poly",
        "edge data -> coll",
        "edge data -> zero",
        "edge poly -> sel",
        "edge coll -> sel",
        "edge zero -> sel",
      ].join("\n"),
    );
    const svg = renderFigureSvg(spec);
    expect(svg).toContain("viewBox");
    expect((svg.match(/marker-end/g) ?? []).length).toBe(6); // all six edges drawn
    expect((svg.match(/<rect /g) ?? []).length).toBe(5);
    expect(svg).not.toMatch(/<text(?![^>]*stroke="none")/); // text never stroked
    // Box width always exceeds its widest measured line: rect widths ≥ text estimate.
    const widest = "Heavy-light polynomial".length * 17 * 0.62 * 1.08;
    const polyRect = /<rect [^>]*width="([\d.]+)" height/g;
    const widths = [...svg.matchAll(polyRect)].map((m) => Number(m[1]));
    expect(Math.max(...widths)).toBeGreaterThan(widest);
  });
});

describe("extractDeckMarkdown", () => {
  it("strips fences and pre-heading chatter", () => {
    const out = extractDeckMarkdown("Here is the deck:\n```markdown\n# T\nbody\n```");
    expect(out).toBe("# T\nbody\n");
    expect(() => extractDeckMarkdown("no heading at all")).toThrow(/# <talk title>/);
  });
});

describe("bibSummary", () => {
  it("renders one Author (Year) line per entry from references.bib", () => {
    const bib = `@article{Robinson1988,
  author = {Robinson, P. M.},
  title = {Root-{N}-consistent semiparametric regression},
  journal = {Econometrica},
  year = {1988}
}
@inproceedings{MackeySyrgkanisZadik2018,
  author = {Mackey, Lester and Syrgkanis, Vasilis and Zadik, Ilias},
  title = {Orthogonal Machine Learning},
  booktitle = {Proceedings of ICML},
  year = {2018}
}`;
    const out = bibSummary(bib);
    expect(out).toContain("- Robinson1988: Robinson (1988). Root-N-consistent semiparametric regression. Econometrica.");
    expect(out).toContain("- MackeySyrgkanisZadik2018: Mackey, Syrgkanis, Zadik (2018). Orthogonal Machine Learning. Proceedings of ICML.");
    expect(bibSummary("")).toBe("");
  });
});

describe("stageP6 clarity loop", () => {
  const read = (severity: "lost" | "rough" | null, understood = severity === "lost" ? "partly" : "yes") =>
    JSON.stringify({
      understood,
      question: "q", result: "r", mechanism: "m", why_true: "w", example: "e",
      findings: severity ? [{ slide: 2, severity, problem: "undefined term", fix: "define it" }] : [],
    });
  async function run(
    readerReplies: string[],
    existingDeck?: string,
    reenter: boolean | string[] = false,
    reportOnFile?: string,
    sectionFiles: Record<string, string> = {},
    staleInputs = false,
  ) {
    const dir = await mkdtemp(join(tmpdir(), "p6-loop-"));
    await mkdir(join(dir, "sections"));
    for (const [name, text] of Object.entries(sectionFiles)) await writeFile(join(dir, "sections", name), text);
    if (existingDeck !== undefined) await writeFile(join(dir, "slides.md"), existingDeck);
    if (reportOnFile !== undefined) {
      await writeFile(
        join(dir, "slides_review.json"),
        JSON.stringify({ ...JSON.parse(reportOnFile), passed: false, deck_hash: hashEnvBody(existingDeck!) }),
      );
      if (staleInputs) await writeFile(join(dir, "slides_cache.json"), JSON.stringify({ key: "other-inputs" }));
    }
    await writeFile(join(dir, "meta.json"), JSON.stringify({ title: "T", abstract: "A." }));
    await writeFile(join(dir, "outline.md"), "outline\n");
    await writeFile(
      join(dir, "formal_layer.json"),
      JSON.stringify({ blocks: [{ obj_id: "thm:main", alias: "Theorem 1", kind: "theorem", title: "Main", body: "x".repeat(2000) }] }),
    );
    let drafts = 0;
    const briefs: string[] = [];
    const deps: PaperDeps = {
      runClaude: async () => "",
      runCodex: async (args) => {
        if (args.prompt.startsWith("=== PROMPT: p6_reader")) {
          expect(args.prompt).not.toContain("x".repeat(2000)); // the reader never sees backup slides
          const reply = readerReplies.shift();
          if (reply === undefined) throw new Error("test: reader called with no reply queued");
          if (reply === "THROW") throw new Error("quota");
          return { stdout: reply, stderr: "" };
        }
        briefs.push(args.prompt);
        drafts += 1;
        return { stdout: deck(`## Main result\n@informal thm:main: Draft ${drafts}.`), stderr: "" };
      },
      dryRun: false,
    };
    const io = {
      ctx: { repoRoot: dir, qid: "q", spec: "v1", deps, outDir: dir },
      state: freshPaperState("q", "v1"),
      bank: {} as StageIO["bank"],
      outDir: dir,
    } as StageIO;
    await stageP6(io);
    const first = {
      md: await readFile(join(dir, "slides.md"), "utf8"),
      review: JSON.parse(await readFile(join(dir, "slides_review.json"), "utf8")),
      note: io.state.notes.at(-1)!,
      briefs: [...briefs],
    };
    let second: typeof first | null = null;
    if (reenter === true) {
      await stageP6(io); // a no-op: no writer call (briefs unchanged) and no read (the queue is empty)
      expect(briefs.length).toBe(first.briefs.length);
      expect(io.state.notes.at(-1)).toContain("up to date");
    } else if (reenter) {
      readerReplies.push(...reenter);
      await stageP6(io);
      second = {
        md: await readFile(join(dir, "slides.md"), "utf8"),
        review: JSON.parse(await readFile(join(dir, "slides_review.json"), "utf8")),
        note: io.state.notes.at(-1)!,
        briefs: briefs.slice(first.briefs.length),
      };
    }
    await rm(dir, { recursive: true });
    return { ...first, second };
  }
  it("revises from the reader's findings until the reader follows the deck", async () => {
    const out = await run([read("lost"), read(null)]);
    expect(out.md).toContain("Draft 2.");
    expect(out.briefs[1]).toContain("undefined term");
    expect(out.review).toMatchObject({ passed: true, reader_passes: 2 });
  });

  it("works in a first read's rough findings once, then stops", async () => {
    const out = await run([read("rough"), read("rough")]);
    expect(out.md).toContain("Draft 2.");
    expect(out.review).toMatchObject({ passed: true, reader_passes: 2 });
  });

  it("keeps the best-understood deck when a revision reads worse", async () => {
    const out = await run([read("rough"), read("lost"), ...Array.from({ length: SLIDES_READER_PASSES - 2 }, () => read("lost", "no"))]);
    expect(out.md).toContain("Draft 1.");
    expect(out.review).toMatchObject({ passed: true, understood: "yes", reader_passes: SLIDES_READER_PASSES });
    expect(out.note).not.toContain("failed");
  });

  it("keeps the finished deck when a cold read fails", async () => {
    const first = await run(["THROW"]);
    expect(first.md).toContain("Draft 1.");
    expect(first.review).toMatchObject({ passed: false, reader_passes: 0 });
    expect(first.note).toContain("NOT REVIEWED");
    const later = await run([read("lost"), "THROW"]);
    expect(later.md).toContain("Draft 1.");
    expect(later.review).toMatchObject({ passed: false, reader_passes: 1 });
  });

  it("revises a deck that is already there instead of drafting a new one", async () => {
    const mine = deck("## Main result\n@informal thm:main: My own wording.");
    const out = await run([read("lost"), read(null)], mine);
    expect(out.briefs).toHaveLength(1);
    expect(out.briefs[0]).toContain("My own wording."); // the one writer call is a revision of the deck on disk
    expect(out.md).toContain("Draft 1.");
    expect(out.note).toContain("revised");
  });

  it("re-entering a deck that did not pass revises it from the report on file, with no read first", async () => {
    const out = await run(Array.from({ length: SLIDES_READER_PASSES }, () => read("lost")), undefined, [read(null)]);
    expect(out.review).toMatchObject({ passed: false });
    expect(out.second!.briefs).toHaveLength(1); // one revision, driven by the saved findings
    expect(out.second!.briefs[0]).toContain("undefined term");
    expect(out.second!.review).toMatchObject({ passed: true, reader_passes: 1 });
    expect(out.second!.note).toContain("revised");
  });

  it("reads again, ignoring the report on file, when the paper inputs changed", async () => {
    const mine = deck("## Main result\n@informal thm:main: My own wording.") + "\n";
    const out = await run([read(null)], mine, false, read("lost"), {}, true);
    expect(out.briefs).toHaveLength(0); // the fresh read passes the deck: nothing is revised
    expect(out.md).toBe(mine);
    expect(out.review).toMatchObject({ passed: true, reader_passes: 1 });
  });

  it("keeps an existing deck the reader already understands, and re-entry is then a no-op", async () => {
    const mine = deck("## Main result\n@informal thm:main: My own wording.");
    const out = await run([read("rough")], mine, true);
    expect(out.briefs).toHaveLength(0);
    expect(out.md).toBe(mine + "\n");
    expect(out.review).toMatchObject({ passed: true, reader_passes: 1 });
    expect(out.note).toContain("kept");
  });

  it("gives the writer the main text and points it at the appendix files", async () => {
    const out = await run([read(null)], undefined, false, undefined, {
      "01_setup.tex": "MAIN-TEXT-BODY",
      "08_appendix_a_proofs.tex": "APPENDIX-PROOF-BODY",
    });
    expect(out.briefs[0]).toContain("MAIN-TEXT-BODY");
    expect(out.briefs[0]).not.toContain("APPENDIX-PROOF-BODY");
    expect(out.briefs[0]).toMatch(/sections\/08_appendix_a_proofs\.tex/);
  });

  it("stops at the pass cap with the last deck that was read, marked not passed", async () => {
    const out = await run(Array.from({ length: SLIDES_READER_PASSES }, () => read("lost")));
    expect(out.md).toContain(`Draft ${SLIDES_READER_PASSES}.`);
    expect(out.review).toMatchObject({ passed: false, reader_passes: SLIDES_READER_PASSES });
    expect(out.note).toContain("NOT PASSED");
  });
});
