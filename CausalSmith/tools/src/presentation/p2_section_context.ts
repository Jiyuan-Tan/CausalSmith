import type { Outline } from "./stage_util.js";
import { extractBalancedEnv, stripTexComments } from "../shared/tex_text.js";

export interface PriorSectionContext {
  name: string;
  objs: readonly string[];
  path: string;
  tex: string;
}

/** Ordering and reference inventory only. The current section receives its own brief,
 * environments and notation separately; prior prose remains available in its source file. */
export function compactSectionOutline(outline: Outline): string {
  return [`Title: ${outline.title}`, ...outline.sections.map((s) =>
    `Section: ${s.name}\nObjects: ${s.objs.join(", ") || "(none)"}`)].join("\n\n");
}

/** A continuity cue, never a partial paragraph or a fragment of a formula. Remove
 * environment bodies and displays before selecting complete recent prose paragraphs. */
export function sectionContinuityExcerpt(tex: string, maxChars = 2000): string {
  let prose = stripTexComments(tex);
  // Drop whole balanced environments, including frozen statements and display math.
  // An incomplete environment makes the remainder unsuitable as an excerpt.
  for (let m; (m = /\\begin\{([A-Za-z][A-Za-z0-9*]*)\}/.exec(prose)); ) {
    const body = extractBalancedEnv(prose.slice(m.index), m[1]);
    if (body === null) { prose = prose.slice(0, m.index); break; }
    const end = m.index + body.length;
    prose = `${prose.slice(0, m.index)}\n\n${prose.slice(end)}`;
  }
  prose = prose.replace(/\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$/g, "\n\n");
  const selected: string[] = [];
  let used = 0;
  for (const paragraph of prose.split(/\n\s*\n/).map((p) => p.trim()).reverse()) {
    if (!paragraph || /\\(?:section|subsection|subsubsection|chapter|end)\b/.test(paragraph) ||
        !balancedProse(paragraph) || paragraph.length + used + (selected.length ? 2 : 0) > maxChars) continue;
    selected.unshift(paragraph);
    used += paragraph.length + (selected.length > 1 ? 2 : 0);
  }
  return selected.join("\n\n");
}

// TeX paragraphs with unfinished groups or math delimiters are unsuitable cues.
function balancedProse(text: string): boolean {
  let braces = 0, math: string | null = null;
  for (const token of text.match(/\\[()[\]]|\\.|[{}$]/g) ?? []) {
    if (token === "{") braces++;
    else if (token === "}" && --braces < 0) return false;
    else if (token === "$" || token === "\\(" || token === "\\[") {
      if (math === null) math = token;
      else if (math === "$" && token === "$") math = null;
      else return false;
    } else if (token === "\\)" || token === "\\]") {
      if (math !== (token === "\\)" ? "\\(" : "\\[")) return false;
      math = null;
    }
  }
  return braces === 0 && math === null;
}

/** Small deterministic continuity context. The complete link ledger survives excerpt
 * selection so a later section cannot repeat an earlier first-mention symbol link. */
export function priorSectionContext(prior: readonly PriorSectionContext[]): string {
  if (prior.length === 0) return "(this is the first section; no prior links)";
  const linked = new Set<string>();
  for (const s of prior) {
    for (const m of stripTexComments(s.tex).matchAll(/\\leanref\s*\{([^{}]+)\}/g)) linked.add(m[1].trim());
  }
  const previous = prior[prior.length - 1];
  const excerpt = sectionContinuityExcerpt(previous.tex);
  return [
    "Earlier sections (read the named file only when exact earlier wording is needed):",
    ...prior.map((s) => `- ${s.name}\n  Objects: ${s.objs.join(", ") || "(none)"}\n  File: ${s.path}`),
    "Already linked leanref targets (do not link these again):",
    [...linked].sort().join(", ") || "(none)",
    `Recent prose from ${previous.name} (excerpt only; omitted content remains in its file):`,
    excerpt || "(no short complete prose paragraphs)",
  ].join("\n");
}
