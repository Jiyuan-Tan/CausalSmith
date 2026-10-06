import { type LintProblem } from "./tex_anchors.js";

/**
 * P6 slides — parser and mechanical lint for `slides.md`, the authored seminar-deck
 * source.
 *
 * Format contract (kept deliberately tiny so a single model call can honor it and an
 * operator can hand-edit the file):
 *   - `---` on its own line separates slides;
 *   - the first slide opens with `# <talk title>`, every later slide with `## <slide title>`;
 *   - `@formal <obj_id>` on its own line marks where the frozen formal-layer body is
 *     injected verbatim at render time — in the talk only a body short enough to read
 *     on a slide (`FORMAL_SLIDE_MAX_CHARS`); any length on an `Appendix…` backup slide;
 *   - `@informal <obj_id>: <one-line headline>` is a labeled plain-language restatement,
 *     rendered with an "informal" chip linking to the audited paper environment;
 *   - `@figure <kebab-name>: <caption>` shows `slides_assets/<name>.svg` — a SCHEMATIC
 *     illustration (DAG, regime diagram, pipeline sketch; never a data plot), rendered
 *     with an "illustrative" label; the stage authors a missing asset with one codex
 *     call, and existing assets (incl. hand-drawn) are never overwritten;
 *   - everything else is ordinary markdown prose/bullets (inline `\(…\)`/`$…$` allowed).
 *
 * The site has a mirroring renderer in `site/src/lib/slides.ts` — keep the two in sync.
 */

export type SlideBlock =
  | { kind: "prose"; md: string }
  | { kind: "formal"; objId: string }
  | { kind: "informal"; objId: string; text: string }
  | { kind: "figure"; name: string; caption: string };

export interface Slide {
  title: string;
  blocks: SlideBlock[];
}

export interface SlidesDoc {
  talkTitle: string;
  slides: Slide[];
}

/** Minimal view of a formal-layer source block that the lint needs. */
export interface FormalBlockRef {
  obj_id: string;
  kind: string;
  /** TeX-source length of the audited body; absent = size unknown, not checked. */
  bodyChars?: number;
}

/** Longest audited body (TeX-source chars) `@formal` may inject: beyond this the
 *  block cannot be read in the minute a slide gets. */
export const FORMAL_SLIDE_MAX_CHARS = 900;
/** Fewest and most slides the talk may have (backup slides not counted). */
export const TALK_SLIDES_MIN = 8;
export const TALK_SLIDES_MAX = 25;
/** Most backup slides a deck may carry after the talk. */
export const BACKUP_SLIDES_MAX = 4;
/** A backup slide — titled `Appendix…`, placed after the talk — carries a full
 *  audited statement for the expert reader; the size cap does not apply to it. */
export function isBackupSlide(slide: Slide): boolean {
  return /^appendix\b/i.test(slide.title);
}
/** Most bullets one slide may carry. */
export const SLIDE_MAX_BULLETS = 6;

const FORMAL_RE = /^@formal\s+(\S+)\s*$/;
const INFORMAL_RE = /^@informal\s+(\S+)\s*:\s*(.*)$/;
const FIGURE_RE = /^@figure\s+([A-Za-z0-9_-]+)\s*:\s*(.*)$/;

/** Split `slides.md` into slides and typed blocks. Throws on structural defects the
 *  renderer could not survive (no title, a slide with no `##` heading). */
export function parseSlidesMd(md: string): SlidesDoc {
  const chunks = md
    .split(/\n---[ \t]*\n/)
    .map((c) => c.trim())
    .filter((c) => c.length > 0);
  if (chunks.length === 0) throw new Error("slides.md is empty");
  const first = chunks[0];
  const titleMatch = /^#\s+(.+)$/m.exec(first);
  if (!titleMatch || !first.trimStart().startsWith("# ")) {
    throw new Error("slides.md must open with a `# <talk title>` title slide");
  }
  const talkTitle = titleMatch[1].trim();
  const slides: Slide[] = [];
  for (const [i, chunk] of chunks.entries()) {
    const lines = chunk.split("\n");
    let title: string;
    if (i === 0) {
      title = talkTitle;
      lines.shift();
    } else {
      const m = /^##\s+(.+)$/.exec(lines[0] ?? "");
      if (!m) throw new Error(`slide ${i + 1} does not open with a \`## <title>\` heading`);
      title = m[1].trim();
      lines.shift();
    }
    const blocks: SlideBlock[] = [];
    let prose: string[] = [];
    const flush = () => {
      const md = prose.join("\n").trim();
      if (md) blocks.push({ kind: "prose", md });
      prose = [];
    };
    for (const line of lines) {
      const f = FORMAL_RE.exec(line);
      const inf = INFORMAL_RE.exec(line);
      const fig = FIGURE_RE.exec(line);
      if (f) {
        flush();
        blocks.push({ kind: "formal", objId: normalizeObjId(f[1]) });
      } else if (inf) {
        flush();
        blocks.push({ kind: "informal", objId: normalizeObjId(inf[1]), text: inf[2].trim() });
      } else if (fig) {
        flush();
        blocks.push({ kind: "figure", name: fig[1], caption: fig[2].trim() });
      } else {
        prose.push(line);
      }
    }
    flush();
    slides.push({ title, blocks });
  }
  return { talkTitle, slides };
}

/** Models sometimes emit the paper-body form `obj:thm:x`; the formal layer keys on `thm:x`. */
function normalizeObjId(raw: string): string {
  return raw.replace(/^obj:/, "");
}

/**
 * Mechanical quality gate (no model calls). Checks:
 *   - every directive resolves to a formal-layer block;
 *   - some theorem block appears on a slide (formal or informal) — which results the
 *     story needs is the writer's and the cold reader's judgment, not the lint's;
 *   - readable slides: in the talk, `@formal` only for a body within
 *     `FORMAL_SLIDE_MAX_CHARS`; at most one per slide; at most `SLIDE_MAX_BULLETS`
 *     bullets per slide;
 *   - the exact statement is available: some theorem appears via `@formal`, in the
 *     talk or on a backup slide (`isBackupSlide`, at most `BACKUP_SLIDES_MAX`, all
 *     after the talk);
 *   - no model-COMPOSED displayed math: `$$`/`\begin{align…}` are always rejected, and
 *     a `\[…\]` display in prose must be a VERBATIM copy (whitespace-insensitive) from
 *     `verbatimCorpus` (formal bodies + paper sections) — captions and @informal
 *     headlines stay inline-only;
 *   - no bare-@formal slide: a formal block needs at least one framing prose/@informal
 *     line on its slide;
 *   - authors' voice: prose never says "the paper" (write "we");
 *   - `@informal` headlines are non-empty and at most 280 characters;
 *   - deck shape: `TALK_SLIDES_MIN`–`TALK_SLIDES_MAX` talk slides, at most 2 figures.
 */
export function lintSlides(
  doc: SlidesDoc,
  formalBlocks: FormalBlockRef[],
  verbatimCorpus = "",
): LintProblem[] {
  const problems: LintProblem[] = [];
  const known = new Set(formalBlocks.map((b) => b.obj_id));
  const bodyChars = new Map(formalBlocks.map((b) => [b.obj_id, b.bodyChars]));
  const referenced = new Set<string>();
  const formalShown = new Set<string>();
  let figures = 0;
  const composedMath = (s: string): boolean =>
    /\$\$|\\begin\{(align|equation|gather|multline|flalign|eqnarray|displaymath)\*?\}/.test(s);
  const displayedMath = (s: string): boolean => composedMath(s) || /(?<=(?<!\\)(?:\\\\)*)\\\[/.test(s);
  const squash = (s: string): string => s.replace(/\s+/g, "");
  const corpus = squash(verbatimCorpus);
  for (const [i, slide] of doc.slides.entries()) {
    const where = `slide ${i + 1} ("${slide.title}")`;
    for (const block of slide.blocks) {
      if (block.kind === "prose") {
        if (composedMath(block.md)) {
          problems.push({
            gate: "slides-displayed-math",
            detail: `${where}: $$…$$/align displayed math in authored prose — use \\[…\\] copied verbatim from the paper, or @formal <obj_id>`,
          });
        }
        // An opener is `\[` after an even run of backslashes: a TeX row break with
        // spacing (`\\[3mm]`) is not one.
        const displayPairs = [...block.md.matchAll(/(?<=(?<!\\)(?:\\\\)*)\\\[([\s\S]*?)\\\]/g)];
        if ((block.md.match(/(?<=(?<!\\)(?:\\\\)*)\\\[/g) ?? []).length !== displayPairs.length) {
          problems.push({
            gate: "slides-displayed-math",
            detail: `${where}: unmatched \\[ in prose — every display must be a complete \\[…\\] pair`,
          });
        }
        for (const m of displayPairs) {
          // Substring laundering guard: a display must be a real formula (some
          // math structure, non-trivial length), not a prose fragment that
          // happens to occur in the corpus — and then a verbatim corpus copy.
          const content = squash(m[1]);
          const formulaLike = content.length >= 3 && /[\\=<>^_]|\d/.test(content);
          // Boundary-aware match: some corpus occurrence must not continue into
          // an alphanumeric on either side, so \[x=1\] cannot launder off x=10.
          const isBoundary = (ch: string | undefined) => ch === undefined || !/[0-9a-zA-Z]/.test(ch);
          let verbatim = false;
          // Guarded by formulaLike: indexOf("") clamps at corpus.length and
          // would spin forever on an empty display.
          if (formulaLike) {
            for (let i = corpus.indexOf(content); i >= 0; i = corpus.indexOf(content, i + 1)) {
              if (isBoundary(corpus[i - 1]) && isBoundary(corpus[i + content.length])) {
                verbatim = true;
                break;
              }
            }
          }
          if (!formulaLike || !verbatim) {
            problems.push({
              gate: "slides-display-not-verbatim",
              detail: `${where}: the display equation \\[${m[1].trim().slice(0, 60)}…\\] is not a verbatim copy of a formal-catalog body or paper-section formula — copy a real formula exactly, or, where the paper has no such display, write it inline as \\(…\\) or in words`,
            });
          }
        }
        if (/^@(formal|informal|figure)\b/m.test(block.md)) {
          problems.push({
            gate: "slides-directive-malformed",
            detail: `${where}: a line starts with @formal/@informal/@figure but does not parse (expected \`@formal <obj_id>\`, \`@informal <obj_id>: <headline>\`, or \`@figure <kebab-name>: <caption>\`)`,
          });
        }
      } else if (block.kind === "figure") {
        figures += 1;
        if (displayedMath(block.caption)) {
          problems.push({
            gate: "slides-displayed-math",
            detail: `${where}: displayed math in the @figure caption — use inline \\(…\\) only`,
          });
        }
        if (!/^[a-z][a-z0-9-]*$/.test(block.name)) {
          problems.push({
            gate: "slides-figure-name",
            detail: `${where}: figure name "${block.name}" must be lowercase kebab-case (it becomes slides_assets/<name>.svg)`,
          });
        }
        if (!block.caption) {
          problems.push({
            gate: "slides-figure-caption",
            detail: `${where}: @figure ${block.name} has an empty caption`,
          });
        }
      } else {
        referenced.add(block.objId);
        if (!known.has(block.objId)) {
          problems.push({
            gate: "slides-unknown-obj",
            detail: `${where}: @${block.kind} references "${block.objId}", which is not a formal-layer block`,
            objId: block.objId,
          });
        }
        const chars = bodyChars.get(block.objId);
        if (block.kind === "formal") formalShown.add(block.objId);
        if (block.kind === "formal" && !isBackupSlide(slide) && chars !== undefined && chars > FORMAL_SLIDE_MAX_CHARS) {
          problems.push({
            gate: "slides-formal-too-long",
            detail: `${where}: @formal ${block.objId} injects a ${chars}-char statement (limit ${FORMAL_SLIDE_MAX_CHARS}) — in the talk use @informal ${block.objId}: <headline> with the verbatim \\[…\\] display that carries it; the full statement goes on an "Appendix: …" backup slide`,
            objId: block.objId,
          });
        }
        if (block.kind === "informal") {
          if (displayedMath(block.text)) {
            problems.push({
              gate: "slides-displayed-math",
              detail: `${where}: displayed math in an @informal headline — use inline \\(…\\) only`,
            });
          }
          // A long multi-clause headline defeats the labeled-restatement register
          // and smuggles extra claims past the checkpoint read.
          if (block.text.length > 280) {
            problems.push({
              gate: "slides-informal-headline",
              detail: `${where}: @informal ${block.objId} headline is ${block.text.length} chars (limit 280) — one short sentence`,
              objId: block.objId,
            });
          }
          if (!block.text) {
            problems.push({
              gate: "slides-empty-informal",
              detail: `${where}: @informal ${block.objId} has an empty headline`,
              objId: block.objId,
            });
          }
        }
      }
    }
    // A verbatim theorem dump with no framing reads as a wall: every @formal
    // needs at least one plain-language line (prose or @informal) on its slide.
    if (
      slide.blocks.some((b) => b.kind === "formal") &&
      !slide.blocks.some((b) => b.kind === "prose" || b.kind === "informal")
    ) {
      problems.push({
        gate: "slides-bare-formal",
        detail: `${where}: a @formal block stands alone — add at least one plain-language line saying what the statement delivers`,
      });
    }
    if (slide.blocks.filter((b) => b.kind === "formal").length > 1) {
      problems.push({
        gate: "slides-density",
        detail: `${where}: more than one @formal block — show one statement per slide`,
      });
    }
    // Top-level list items only: display-math lines and indented sub-items are not bullets.
    const bullets = slide.blocks
      .flatMap((b) => (b.kind === "prose" ? b.md.replace(/(?<=(?<!\\)(?:\\\\)*)\\\[[\s\S]*?\\\]/g, "").split("\n") : []))
      .filter((l) => /^([-*+]|\d+\.)\s/.test(l)).length;
    if (bullets > SLIDE_MAX_BULLETS) {
      problems.push({
        gate: "slides-density",
        detail: `${where}: ${bullets} bullets (limit ${SLIDE_MAX_BULLETS}) — cut to the slide's one point or split it`,
      });
    }
    // Speaker voice: a deck narrated as "the paper does X" reads as a book
    // report about someone else's work; the authors say "we".
    const spoken = [
      slide.title,
      ...slide.blocks.map((b) =>
        b.kind === "prose" ? b.md : b.kind === "informal" ? b.text : b.kind === "figure" ? b.caption : "",
      ),
    ].join("\n");
    if (/\bthe paper('s)?\b/i.test(spoken)) {
      problems.push({
        gate: "slides-voice",
        detail: `${where}: says "the paper" — write in the authors' voice (we/us/our)`,
      });
    }
  }
  const theorems = formalBlocks.filter((b) => b.kind === "theorem");
  if (theorems.length > 0 && !theorems.some((b) => referenced.has(b.obj_id))) {
    problems.push({
      gate: "slides-no-theorem",
      detail: "no theorem appears on any slide — state the main result via @informal or @formal",
    });
  }
  if (theorems.length > 0 && !theorems.some((b) => formalShown.has(b.obj_id))) {
    problems.push({
      gate: "slides-no-formal-theorem",
      detail: 'the main theorem\'s exact statement is nowhere in the deck — add an "Appendix: …" backup slide after the talk with one framing line and @formal <obj_id>',
    });
  }
  const backup = doc.slides.map(isBackupSlide);
  const talkSlides = backup.includes(true) ? backup.indexOf(true) : doc.slides.length;
  if (backup.slice(talkSlides).includes(false) || doc.slides.length - talkSlides > BACKUP_SLIDES_MAX) {
    problems.push({
      gate: "slides-backup",
      detail: `backup ("Appendix: …") slides come after the whole talk, at most ${BACKUP_SLIDES_MAX}`,
    });
  }
  if (figures > 2) {
    problems.push({
      gate: "slides-figure-count",
      detail: `deck declares ${figures} figures; at most 2`,
    });
  }
  if (talkSlides < TALK_SLIDES_MIN || talkSlides > TALK_SLIDES_MAX) {
    problems.push({
      gate: "slides-deck-shape",
      detail: `the talk has ${talkSlides} slides before any backup slide; a 20-minute talk needs ${TALK_SLIDES_MIN}–${TALK_SLIDES_MAX}`,
    });
  }
  return problems;
}
