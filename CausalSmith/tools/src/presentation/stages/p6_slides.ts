import { mkdir, readdir, readFile, rename, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join } from "node:path";
import { parseJsonLoose } from "../gates.js";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt } from "../prompt_io.js";
import { hashEnvBody, type LintProblem } from "../tex_anchors.js";
import { SLIDES_READER_REPLY } from "../reply_schemas.js";
import { FORMAL_SLIDE_MAX_CHARS, isBackupSlide, lintSlides, parseSlidesMd, type FormalBlockRef, type SlidesDoc } from "../slides.js";
import { parseFigureDsl, renderFigureSvg } from "../figure_layout.js";

/** Deck-generation standard — opaque version token for the cache key.
  * Bump to any new literal only when the standard tightens (a cached verdict under the old
  * standard would be wrong); prompt wording and code changes never bump it. */
export const SLIDES_STANDARD = "story-first-cold-reader-v2";

/**
 * P6 — seminar slides. Terminal, optional, and strictly post-P5: a pitch talk
 * re-told from the FINISHED paper. A writer call emits `slides.md`; a cold
 * reader who sees only the rendered deck reports where a listener is lost, and
 * the writer revises until the reader follows it (at most
 * `SLIDES_READER_PASSES` reads; `slides_review.json` is the report on the deck kept).
 * Formal statements are injected from the frozen layer at render time, so no
 * equivalence/proof re-audit runs here. Entering P6 with no `slides.md` builds
 * the deck from scratch; entering with one REVISES it — the reader reads the deck
 * on disk (hand edits included) and the writer revises from that report. Delete
 * `slides.md` to rebuild. The orchestrator confirms the deck and its review at
 * the checkpoint.
 */
export async function stageP6(io: StageIO): Promise<void> {
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p6.stub"), "dry-run\n");
    return;
  }
  const meta = JSON.parse(await readFile(join(io.outDir, "meta.json"), "utf8")) as {
    title: string;
    tldr?: string;
    abstract: string;
  };
  const layer = JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")) as {
    blocks: { obj_id: string; alias?: string | null; kind: string; title: string; body: string }[];
  };
  const outline = await readFile(join(io.outDir, "outline.md"), "utf8");
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  // The paper's verified bibliography (P-stage citation audit) is the ONLY
  // citable set — the deck attributes prior work as Author (Year) from it.
  const references = bibSummary(
    await readFile(join(io.outDir, "references.bib"), "utf8").catch(() => ""),
  );
  if (!references) {
    io.state.notes.push(
      "P6: references.bib missing or unparsable — deck generated with NO citable bibliography (prior work described without attribution).",
    );
  }
  // Existing figure assets are never overwritten, so a caption reusing a name
  // must describe THAT diagram — show the model what each kept asset draws.
  const assetDir = join(io.outDir, "slides_assets");
  const existingFigures = (
    await Promise.all(
      (
        await readdir(assetDir).catch((e: NodeJS.ErrnoException) => {
          if (e.code !== "ENOENT") throw e; // only a truly absent dir means "no assets"
          return [] as string[];
        })
      )
        .filter((n) => n.endsWith(".dsl"))
        .sort()
        .map(async (n) => `- ${n.replace(/\.dsl$/, "")}:\n${await readFile(join(assetDir, n), "utf8")}`),
    )
  ).join("\n");
  // The main text goes into the prompt. The appendices — where the constructions
  // and rate-producing steps behind the mechanism slides live — stay on disk: the
  // writer is given their paths and opens the one a step needs, so the prompt
  // carries the paper's argument without every proof. A flat tail-truncation of
  // an over-budget main text would deterministically cut whatever is numbered
  // last, so every section is clipped proportionally instead.
  const sectionFiles = (await readdir(join(io.outDir, "sections")).catch(() => []))
    .filter((n) => n.endsWith(".tex"))
    .sort()
    .map((n) => join(io.outDir, "sections", n));
  const isAppendix = (p: string) => /appendix/i.test(basename(p));
  const mainFiles = sectionFiles.filter((p) => !isAppendix(p));
  // The per-statement proofs are the fullest source: `appendix_proofs.tex` need not carry every one.
  const proofFiles = (await readdir(join(io.outDir, "proofs")).catch(() => []))
    .filter((n) => n.endsWith(".tex"))
    .sort()
    .map((n) => join(io.outDir, "proofs", n));
  const appendixFiles = [
    ...sectionFiles.filter(isAppendix),
    join(io.outDir, "appendix_proofs.tex"),
    ...proofFiles,
  ].filter(existsSync);
  const read = (paths: string[]) => Promise.all(paths.map((p) => readFile(p, "utf8")));
  const [mainSections, appendixSections] = await Promise.all([read(mainFiles), read(appendixFiles)]);
  // Everything the deck may quote: the verbatim-display check covers the appendices too.
  const rawSections = [...mainSections, ...appendixSections];
  const SECTIONS_BUDGET = 200_000;
  const sectionsTotal = mainSections.reduce((s, t) => s + t.length, 0);
  let sections: string;
  if (sectionsTotal <= SECTIONS_BUDGET) {
    sections = mainSections.join("\n\n");
  } else {
    sections = mainSections
      .map((t) => t.slice(0, Math.floor((t.length / sectionsTotal) * SECTIONS_BUDGET)))
      .join("\n\n");
    io.state.notes.push(
      `P6: main-text sections exceed the prompt budget (${sectionsTotal} > ${SECTIONS_BUDGET} chars) — each section clipped proportionally.`,
    );
  }
  const mainText = sections; // the cache key hashes content, never the checkout path
  if (appendixFiles.length > 0) {
    sections +=
      "\n\nAPPENDIX AND PROOF FILES (not included above; on disk). They hold the proofs: the constructions and the steps that produce the rates; a file under `proofs/` is the proof of the statement it is named after. Before writing or revising a mechanism slide whose step the main text only asserts, open the file that proves it and take the construction and its formula from there:\n" +
      appendixFiles.map((p, i) => `- ${p} (${Math.round(appendixSections[i].length / 1000)}k chars)`).join("\n");
  }

  const key = hashEnvBody(
    [
      SLIDES_STANDARD,
      meta.title,
      meta.tldr ?? "",
      meta.abstract,
      outline,
      brief,
      references,
      existingFigures,
      rawSections.join("\n"), // full text: the lint's verbatim corpus, beyond the clipped prompt view
      mainText,
      ...layer.blocks.map((b) => `${b.obj_id}§${b.body}`),
    ].join("§§"),
  );
  const cachePath = join(io.outDir, "slides_cache.json");
  const slidesPath = join(io.outDir, "slides.md");
  const reviewPath = join(io.outDir, "slides_review.json");
  const cache = await readFile(cachePath, "utf8")
    .then((raw) => JSON.parse(raw) as { key?: string })
    .catch(() => null);
  const savedReview = await readFile(reviewPath, "utf8")
    .then((raw) => JSON.parse(raw) as Partial<SlidesReaderReview> & { passed?: boolean; deck_hash?: string })
    .catch(() => null);
  const existing = await readFile(slidesPath, "utf8").catch(() => null);
  // Paper-labeled blocks first (stable order); a null alias marks an internal
  // helper — flag it explicitly so the "never reference helpers" rule is followable.
  const formalCatalog = [...layer.blocks]
    .sort((a, b) => Number(b.alias != null) - Number(a.alias != null))
    .map(
      (b) =>
        `- ${b.obj_id} | ${b.kind} | ${b.alias ?? "(internal helper — never reference on a slide)"} | ${b.title} | ${
          b.alias == null
            ? "not for slides"
            : b.body.length <= FORMAL_SLIDE_MAX_CHARS
              ? "slide-size: @formal allowed"
              : "too long for a talk slide: @informal in the talk, @formal on a backup slide only"
        }\n${b.body}`,
    )
    .join("\n\n");
  const formalRefs: FormalBlockRef[] = layer.blocks.map((b) => ({
    obj_id: b.obj_id,
    kind: b.kind,
    bodyChars: b.body.length,
  }));
  const vars = {
    title: meta.title,
    tldr: meta.tldr ?? "",
    abstract: meta.abstract,
    outline,
    related_work_brief: brief,
    references,
    existing_figures: existingFigures || "(none)",
    formal_catalog: formalCatalog,
    sections,
    revision_notes: "",
  };
  // A `\[…\]` display in authored prose must be a verbatim copy from the paper —
  // the corpus is the FULL material (unclipped sections), not the prompt view.
  const verbatimCorpus = [...layer.blocks.map((b) => b.body), ...rawSections].join("\n");

  // Nothing to do: the deck on disk is the one a reader passed, written from these inputs.
  if (
    existing !== null &&
    savedReview?.passed === true &&
    savedReview.deck_hash === hashEnvBody(existing) &&
    cache?.key === key &&
    lintDeck(existing, formalRefs, verbatimCorpus).length === 0
  ) {
    // A prior run may have died mid-figure-authoring.
    const authored = await authorMissingFigures(io, parseSlidesMd(existing), meta.abstract, layer.blocks);
    io.state.notes.push(
      `P6: slides.md up to date — a reader passed this deck${authored > 0 ? `; ${authored} figure(s) authored` : ""}.`,
    );
    return;
  }

  /** One authoring call, then one lint-informed minimal repair. `notes` is the
   *  revision brief (empty for the first draft). Returns the deck and whatever
   *  lint problems survive the repair. */
  const authorLinted = async (notes: string): Promise<{ md: string; problems: LintProblem[] }> => {
    let md = await generate(io, { ...vars, revision_notes: notes });
    let problems = lintDeck(md, formalRefs, verbatimCorpus);
    if (problems.length > 0) {
      // Minimal-repair retry: a fresh re-roll can regress on dimensions the lint
      // does not check (drop a figure, rename a coined term, break a cross-slide
      // reference) — so the retry patches the previous deck instead.
      md = await generate(io, { ...vars, revision_notes: lintRepairBrief(problems, md) });
      problems = lintDeck(md, formalRefs, verbatimCorpus);
    }
    return { md, problems };
  };

  // The starting deck: a fresh draft when none exists, otherwise the deck on disk
  // (brought within the mechanical limits first, by a minimal repair, if it is not).
  const fresh = existing === null;
  const existingProblems = fresh ? [] : lintDeck(existing, formalRefs, verbatimCorpus);
  const draft = fresh
    ? await authorLinted("")
    : existingProblems.length > 0
      ? await authorLinted(lintRepairBrief(existingProblems, existing))
      : { md: existing, problems: [] };
  if (draft.problems.length > 0) {
    throw new Error(
      `P6: ${fresh ? "slides" : "the existing slides.md"} failed the mechanical lint after ${fresh ? "one retry" : "repair"}${
        fresh ? "" : " — fix it by hand, or delete slides.md to rebuild"
      }:\n- ${draft.problems.map((p) => `[${p.gate}] ${p.detail}`).join("\n- ")}`,
    );
  }

  // Clarity loop. A reader who sees ONLY the rendered deck says whether they
  // understood the paper's main result and mechanism and where a listener struggles; the writer revises
  // from that report; a fresh reader reads the revision. The deck saved is the
  // best-understood one a reader actually read (latest on a tie), so
  // `slides_review.json` describes exactly the `slides.md` beside it. The paper
  // is frozen — a deck that does not pass within the cap goes to the checkpoint
  // marked as such, never back to an earlier stage.
  const rank = (r: SlidesReaderReview): number => ["no", "partly", "yes"].indexOf(r.understood);
  let best: { md: string; review: SlidesReaderReview } | null = null;
  let md = draft.md;
  let passes = 0;
  let loopNote = "";
  // The report on file is the first review when it describes exactly the deck on
  // disk, written from these same paper inputs: the revision starts from the
  // feedback that deck already received. After a paper change the reader reads again.
  let onFile: SlidesReaderReview | null =
    existing !== null &&
    md === existing &&
    cache?.key === key &&
    savedReview?.deck_hash === hashEnvBody(existing) &&
    isReview(savedReview)
      ? savedReview
      : null;
  for (;;) {
    let review: SlidesReaderReview;
    try {
      review = onFile ?? (await readCold(io, md));
    } catch (err) {
      // A failed read never costs a finished deck: keep the best one read so far,
      // or the lint-clean draft when no read completed.
      loopNote = ` A cold-reader call failed (${err instanceof Error ? err.message.split("\n")[0] : String(err)}).`;
      break;
    }
    if (onFile === null) passes += 1;
    onFile = null;
    if (best === null || rank(review) >= rank(best.review)) best = { md, review };
    // A fresh draft's first-read findings are always worked in — a reader who
    // understood still names what a listener would struggle with. Otherwise a
    // revision runs only while the reader does not pass the deck, so an existing
    // deck that reads clearly is kept exactly as it is.
    const revise = !readerPasses(review) || (fresh && passes === 1 && review.findings.length > 0);
    if (!revise || passes >= SLIDES_READER_PASSES) break;
    const revised = await authorLinted(revisionBrief(review, md));
    if (revised.problems.length > 0) {
      loopNote = ` A revision failed the mechanical lint (${revised.problems.map((p) => p.gate).join(", ")}) and was discarded.`;
      break;
    }
    md = revised.md;
  }
  const kept = best?.md ?? draft.md;
  const review = best?.review ?? null;
  const passed = review !== null && readerPasses(review);

  // Atomic (tmp+rename) writes, so NFS readers never see torn files. Review, then
  // deck, then the input key: a crash part-way leaves a review that matches no deck
  // or a key that matches no inputs, and the next entry reads the deck again.
  const finalMd = kept.endsWith("\n") ? kept : kept + "\n";
  await writeAtomic(
    reviewPath,
    JSON.stringify({ ...(review ?? {}), passed, reader_passes: passes, deck_hash: hashEnvBody(finalMd) }, null, 2) + "\n",
  );
  await writeAtomic(slidesPath, finalMd);
  await writeAtomic(cachePath, JSON.stringify({ key }, null, 2) + "\n");
  const deck = parseSlidesMd(kept);
  const authored = await authorMissingFigures(io, deck, meta.abstract, layer.blocks);
  io.state.notes.push(
    `P6: ${fresh ? "wrote" : kept === existing ? "kept" : "revised"} slides.md (${deck.slides.filter((s) => !isBackupSlide(s)).length} talk slides${authored > 0 ? `, ${authored} figure(s) authored` : ""}); ` +
      (review === null
        ? "NOT REVIEWED — no cold read completed; rerun P6 or judge the deck by hand."
        : passed
          ? `a reader of the slides alone understood the result and mechanism (${passes} read(s); ${review.findings.length} remaining finding(s) in slides_review.json).`
          : `NOT PASSED — after ${passes} cold-reader pass(es) the result and mechanism are understood "${review.understood}"; fix the deck by hand from slides_review.json.`) +
      loopNote,
  );
}

/** Brief for a minimal repair of a deck that breaks mechanical limits. */
function lintRepairBrief(problems: LintProblem[], md: string): string {
  // Minimal repair: a fresh re-roll can regress on dimensions the lint does not
  // check (drop a figure, rename a coined term, break a cross-slide reference).
  return (
    "\nThe deck below fails these mechanical checks — fix ALL of them:\n" +
    problems.map((p) => `- [${p.gate}] ${p.detail}`).join("\n") +
    "\nRepair MINIMALLY: reproduce the deck below unchanged except where a listed defect requires an edit — do not drop, rename, or rewrite slides, figures, or terms that are not implicated. Exception: a slides-deck-shape finding implicates the whole deck — fix an over-long deck by MERGING the most closely related slides, and an over-short one by splitting.\n\nDeck:\n" +
    md + "\n"
  );
}

/** Reader passes per deck (first read + reads of revisions). */
export const SLIDES_READER_PASSES = 5;

/** One cold read: whether the reader got the main result and mechanism from the slides alone,
 *  their takeaway, and where the talk failed them. */
export interface SlidesReaderReview {
  understood: "yes" | "partly" | "no";
  question: string;
  result: string;
  mechanism: string;
  why_true: string;
  example: string;
  findings: { slide: number; severity: "lost" | "rough"; problem: string; fix: string }[];
}

function isReview(r: unknown): r is SlidesReaderReview {
  const v = r as Partial<SlidesReaderReview> | null;
  return !!v && ["yes", "partly", "no"].includes(v.understood as string) && Array.isArray(v.findings);
}

/** The deck passes when a reader of the slides alone clearly understands the paper's main result and mechanism. */
export function readerPasses(review: SlidesReaderReview): boolean {
  return review.understood === "yes";
}

/** The deck as an audience sees it: numbered slides, `@formal` bodies injected,
 *  `@informal` headlines and figure captions labeled. No paper text, no obj_ids,
 *  and no backup slides — a listener never sees those. */
export function renderDeckForReader(
  doc: SlidesDoc,
  bodyOf: ReadonlyMap<string, { kind: string; body: string }>,
): string {
  return doc.slides
    .filter((slide) => !isBackupSlide(slide))
    .map((slide, i) => {
      const blocks = slide.blocks.map((b) => {
        if (b.kind === "prose") return b.md;
        if (b.kind === "informal") return `[Informal statement] ${b.text}`;
        if (b.kind === "figure") return `[Figure — boxes and arrows] ${b.caption}`;
        const fb = bodyOf.get(b.objId);
        return `[Formal ${fb?.kind ?? "statement"}]\n${fb?.body ?? ""}`;
      });
      return `=== Slide ${i + 1}: ${slide.title} ===\n${blocks.join("\n\n")}`;
    })
    .join("\n\n");
}

/** One cold read: a fresh model call that sees ONLY the rendered deck — it runs
 *  outside the repository with web search off, so the paper is out of reach. */
async function readCold(io: StageIO, md: string): Promise<SlidesReaderReview> {
  const layer = JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")) as {
    blocks: { obj_id: string; kind: string; body: string }[];
  };
  const prompt = await presentationPrompt("p6_reader", {
    deck: renderDeckForReader(parseSlidesMd(md), new Map(layer.blocks.map((b) => [b.obj_id, b]))),
  });
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: tmpdir(),
    reasoningEffort: "high",
    leanLsp: false,
    webSearch: false,
    sandboxMode: "read-only",
    outputSchema: SLIDES_READER_REPLY,
  });
  const review = parseJsonLoose(stdout);
  if (!isReview(review)) throw new Error("P6: cold-reader reply does not match its schema");
  return review;
}

/** Revision brief: what the reader understood, where they were lost, and the deck to revise. */
function revisionBrief(review: SlidesReaderReview, md: string): string {
  return (
    `\nREVISION. An econometrician outside the subfield read the deck below with no access to the paper. Asked whether they clearly understood the paper's main result and its mechanism, they answered "${review.understood}". What they took away:\n` +
    `- the question: ${review.question}\n- the result: ${review.result}\n- the mechanism: ${review.mechanism}\n- why it is true: ${review.why_true}\n- the example: ${review.example}\n` +
    "Where that differs from the story you intend, the deck failed to convey it. Their findings:\n" +
    review.findings.map((f) => `- [${f.severity}] slide ${f.slide}: ${f.problem} — ${f.fix}`).join("\n") +
    "\nRewrite the deck so this reader would understand it: resolve every finding, restructuring, merging, or cutting slides where that is what it takes. Everything above still applies; a fix uses only the paper's material, and a finding the paper cannot answer is left alone. The reader was not shown the backup slides: keep them.\n\nDeck they read:\n" +
    md + "\n"
  );
}

/** One codex call per @figure whose `slides_assets/<name>.svg` does not exist yet.
 *  Existing assets (including hand-drawn replacements) are never overwritten —
 *  delete a file to re-author it. Figures are schematics labeled "illustrative";
 *  the orchestrator judges them at the clarity checkpoint like everything else. */
async function authorMissingFigures(
  io: StageIO,
  deck: ReturnType<typeof parseSlidesMd>,
  abstract: string,
  blocks: { obj_id: string; kind: string; body: string }[],
): Promise<number> {
  const bodyOf = new Map(blocks.map((b) => [b.obj_id, b]));
  const wanted: {
    name: string;
    caption: string;
    slideTitle: string;
    slideContent: string;
    formalContext: string;
  }[] = [];
  for (const slide of deck.slides) {
    for (const block of slide.blocks) {
      if (block.kind !== "figure") continue;
      const slideContent = slide.blocks
        .map((b) => (b.kind === "prose" ? b.md : b.kind === "informal" ? b.text : ""))
        .filter(Boolean)
        .join("\n");
      // The figure model must see the audited definitions its arrows depict —
      // caption + prose alone produced dependency-wrong diagrams (audit 2026-08-27).
      const formalContext = slide.blocks
        .flatMap((b) => (b.kind === "formal" || b.kind === "informal" ? [b.objId] : []))
        .flatMap((id) => {
          const fb = bodyOf.get(id);
          return fb ? [`${fb.obj_id} (${fb.kind}):\n${fb.body}`] : [];
        })
        .join("\n\n");
      wanted.push({ name: block.name, caption: block.caption, slideTitle: slide.title, slideContent, formalContext });
    }
  }
  if (wanted.length === 0) return 0;
  const assetsDir = join(io.outDir, "slides_assets");
  await mkdir(assetsDir, { recursive: true });
  let authored = 0;
  for (const fig of wanted) {
    const path = join(assetsDir, `${fig.name}.svg`);
    if (existsSync(path)) continue;
    const vars = {
      name: fig.name,
      caption: fig.caption,
      slide_title: fig.slideTitle,
      slide_content: fig.slideContent,
      formal_context: fig.formalContext || "(none referenced on this slide)",
      abstract,
      dsl_findings: "",
    };
    // Content from the model, geometry from figure_layout — one DSL-informed retry.
    let dsl = "";
    let svg: string;
    try {
      dsl = extractDsl(await runFigureCall(io, vars));
      svg = renderFigureSvg(parseFigureDsl(dsl));
    } catch (err) {
      const detail = err instanceof Error ? err.message : String(err);
      dsl = extractDsl(
        await runFigureCall(io, {
          ...vars,
          dsl_findings: `\nA previous attempt failed: ${detail}\n${dsl ? `Its DSL was:\n${dsl}\n` : ""}Emit ONLY valid DSL lines this time.\n`,
        }),
      );
      svg = renderFigureSvg(parseFigureDsl(dsl));
    }
    await writeAtomic(path, svg);
    // The DSL is the figure's SOURCE: kept beside the SVG so a layouter improvement
    // (or a content hand-fix) can re-render without a model call.
    await writeAtomic(join(assetsDir, `${fig.name}.dsl`), dsl + "\n");
    authored += 1;
  }
  return authored;
}

async function runFigureCall(io: StageIO, vars: Record<string, string>): Promise<string> {
  const prompt = await presentationPrompt("p6_figure", vars);
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "medium",
    leanLsp: false,
  });
  return stdout;
}

/** tmp+rename so concurrent readers (and a crash mid-write) never see a torn file. */
async function writeAtomic(path: string, content: string): Promise<void> {
  const tmp = `${path}.tmp-${process.pid}`;
  await writeFile(tmp, content, "utf8");
  await rename(tmp, path);
}

/** Keep only DSL statements — models sometimes wrap output in fences or preamble. */
export function extractDsl(stdout: string): string {
  const lines = stdout
    .replace(/```[a-z]*\n?/g, "")
    .split("\n")
    .map((l) => l.trim())
    .filter((l) => /^(node|edge)\s/.test(l));
  if (lines.length === 0) throw new Error("model output contains no `node`/`edge` DSL lines");
  return lines.join("\n");
}

async function generate(io: StageIO, vars: Record<string, string>): Promise<string> {
  const prompt = await presentationPrompt("p6_slides", vars);
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "high",
    leanLsp: false,
    sandboxMode: "read-only", // the writer reads appendix files; the deck comes back on stdout
  });
  return extractDeckMarkdown(stdout);
}

/** Strip codex chatter/fences: the deck starts at the first `# ` heading line. */
export function extractDeckMarkdown(stdout: string): string {
  let text = stdout.trim();
  // Strip a fence only when it CLOSES AT THE END of the output (leading chatter
  // before the opener is fine). A fully line-anchored (/m) match would pair an
  // internal fence mid-deck and truncate the deck to that block's interior.
  const fence = /(?:^|\n)```(?:markdown|md)?\n([\s\S]*?)\n```\s*$/.exec(text);
  if (fence) text = fence[1].trim();
  const start = text.search(/^# /m);
  if (start < 0) throw new Error("P6: model output contains no `# <talk title>` heading");
  return text.slice(start).trim() + "\n";
}

function lintDeck(md: string, formalRefs: FormalBlockRef[], verbatimCorpus: string) {
  try {
    return lintSlides(parseSlidesMd(md), formalRefs, verbatimCorpus);
  } catch (err) {
    return [{ gate: "slides-structure", detail: err instanceof Error ? err.message : String(err) }];
  }
}

/** Compact one-line-per-entry view of the paper's verified references.bib:
 *  `- key: Surname, Surname (year). Title. Venue.` — enough for the deck to cite
 *  Author (Year) without seeing (or inventing beyond) the bibliography. */
export function bibSummary(bib: string): string {
  const lines: string[] = [];
  for (const entry of bib.split(/^\s*@/m).slice(1)) {
    const key = /^\w+\s*\{\s*([^,\s]+)\s*,/.exec(entry)?.[1];
    if (!key) continue;
    const field = (name: string): string => {
      const m =
        new RegExp(`\\b${name}\\s*=\\s*\\{((?:[^{}]|\\{[^{}]*\\})*)\\}`, "i").exec(entry) ??
        new RegExp(`\\b${name}\\s*=\\s*"((?:\\\\.|[^"\\\\])*)"`, "i").exec(entry) ??
        new RegExp(`\\b${name}\\s*=\\s*(\\d+)`, "i").exec(entry);
      return (
        m?.[1]
          ?.replace(/<[^>]+>/g, "") // publisher-exported bibs can carry MathML/HTML in titles
          .replace(/[{}]/g, "")
          .replace(/\s+/g, " ")
          .trim() ?? ""
      );
    };
    const surnames = field("author")
      .split(/\s+and\s+/)
      .map((a) => (a.includes(",") ? a.split(",")[0] : a.split(/\s+/).pop() ?? "").trim())
      .filter(Boolean);
    const venue = field("journal") || field("booktitle") || field("publisher");
    if (surnames.length === 0 && !field("year")) continue; // unparsable entry: no junk line
    lines.push(
      `- ${key}: ${surnames.join(", ")} (${field("year")}). ${field("title")}.${venue ? ` ${venue}.` : ""}`,
    );
  }
  return lines.join("\n");
}
