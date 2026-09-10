/**
 * Deterministic one-hop Lean context for the judges. A judge that must "open the tagged helper"
 * or "read the file around the declaration" spends a dozen shell turns per call, each re-sending
 * its whole context. The facts it goes looking for are computable: the declarations a Lean proof
 * names, and the section variables in scope at a declaration. Supplying them in the prompt turns
 * those turns into text; a file read remains the fallback for anything not supplied.
 */
import { resolveLibraryDeclaration } from "./declaration_resolver.js";
import { extractFullDeclSource } from "./lean_extract.js";
import type { ModuleDecl } from "./components.js";

const LEAN_KEYWORDS = new Set([
  "theorem", "lemma", "def", "abbrev", "structure", "class", "instance", "inductive", "where", "with",
  "fun", "have", "show", "from", "by", "at", "in", "let", "if", "then", "else", "match", "do", "return",
  "calc", "exact", "apply", "refine", "intro", "intros", "rcases", "obtain", "cases", "induction", "simp",
  "simpa", "rw", "rwa", "omega", "linarith", "nlinarith", "positivity", "norm_num", "ring", "field_simp",
  "constructor", "use", "exists", "ext", "funext", "congr", "trivial", "rfl", "sorry", "set", "unfold",
  "open", "namespace", "section", "end", "variable", "import", "private", "protected", "noncomputable",
  "true", "false", "True", "False", "Type", "Prop", "Sort", "this", "not", "and", "or", "iff", "fun",
  "filter_upwards", "gcongr", "aesop", "decide", "norm_cast", "push_cast", "exact_mod_cast", "first",
  "all_goals", "any_goals", "try", "repeat", "focus", "case", "next", "rename_i", "subst", "specialize",
  "generalize", "clear", "revert", "change", "suffices", "exfalso", "contrapose", "by_contra", "by_cases",
  "left", "right", "symm", "trans", "assumption", "contradiction", "tauto", "push_neg", "nth_rewrite",
  "conv", "lhs", "rhs", "enter", "arg", "mul_comm", "add_comm",
]);

/** Lean with comments removed: `--` to end of line and `/- … -/` blocks (nesting flattened). */
export function stripLeanComments(source: string): string {
  let out = "";
  let i = 0;
  let depth = 0;
  while (i < source.length) {
    if (depth === 0 && source.startsWith("--", i)) {
      const nl = source.indexOf("\n", i);
      i = nl < 0 ? source.length : nl;
      continue;
    }
    if (source.startsWith("/-", i)) { depth++; i += 2; continue; }
    if (depth > 0 && source.startsWith("-/", i)) { depth--; i += 2; continue; }
    if (depth === 0) out += source[i];
    i++;
  }
  return out;
}

/** Identifiers a Lean text names, in first-occurrence order, keywords and tactic names removed. */
export function leanIdentifiers(text: string): string[] {
  const seen = new Set<string>();
  const out: string[] = [];
  for (const m of stripLeanComments(text).matchAll(/(?<![\p{L}\p{N}_.'])[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*/gu)) {
    const id = m[0].replace(/[!?]+$/, "");
    if (!id || LEAN_KEYWORDS.has(id) || seen.has(id)) continue;
    seen.add(id);
    out.push(id);
  }
  return out;
}

/** The `variable`, `open`, and `namespace` lines still in scope at 1-indexed `line`: frames opened
 *  by `section`/`namespace` and not yet closed by `end` contribute their lines; closed frames do not. */
export function sectionContextBefore(source: string, line: number): string {
  const lines = stripLeanComments(source).split("\n").slice(0, Math.max(0, line - 1));
  const frames: string[][] = [[]];
  let continuing = false; // inside a multi-line `variable` block: indented continuation lines belong to it
  for (const raw of lines) {
    const l = raw.trim();
    if (continuing && l && /^\s/.test(raw) && !/^(end|section|namespace|variable|open|theorem|lemma|def|abbrev|structure|class|instance|inductive)\b/.test(l)) {
      const frame = frames[frames.length - 1];
      frame[frame.length - 1] += `\n${raw.trimEnd()}`;
      continue;
    }
    continuing = false;
    if (/^(noncomputable\s+)?section\b/.test(l) || /^namespace\b/.test(l)) {
      frames.push(/^namespace\b/.test(l) ? [l] : []);
    } else if (/^end\b/.test(l)) {
      if (frames.length > 1) frames.pop();
    } else if (/^(variable|open|set_option|local notation|notation|scoped notation)\b/.test(l)) {
      frames[frames.length - 1].push(l);
      continuing = /^variable\b/.test(l);
    }
  }
  return frames.flat().join("\n");
}

const PER_HELPER_CHARS = 6000;
const TOTAL_CHARS = 80000;
const MAX_HELPERS = 24;

/**
 * Every run or library declaration a Lean proof names, as labelled source blocks: run helpers in
 * full (statement and proof — a judge must see whether a helper is bookkeeping or a real step),
 * library declarations by their statement snippet. Bounded; a helper beyond the cap is listed by
 * name so the judge knows it exists and may read it.
 */
export async function helperDeclarationsFor(args: {
  proofSource: string;
  targetDecl: string;
  runIndex: ReadonlyMap<string, ModuleDecl>;
  readRunFile: (relFile: string) => Promise<string>;
  repoRoot: string;
  libraryMemo?: Map<string, string | null>;
}): Promise<string> {
  const memo = args.libraryMemo ?? new Map<string, string | null>();
  const blocks: string[] = [];
  const named: string[] = [];
  const seenDecl = new Set<string>([args.targetDecl]);
  let chars = 0;
  for (const id of leanIdentifiers(args.proofSource)) {
    let block: string | null = null;
    let decl = id;
    const run = args.runIndex.get(id);
    if (run) {
      decl = run.decl ?? id;
      if (seenDecl.has(decl)) continue;
      try {
        const body = extractFullDeclSource(await args.readRunFile(run.file), decl, run.line);
        block = `-- ${decl}  (${run.file})\n${truncate(body)}`;
      } catch { block = null; }
    } else if (id.includes(".")) {
      if (!memo.has(id)) {
        const hit = await resolveLibraryDeclaration(args.repoRoot, id, { mathlib: false }).catch(() => null);
        memo.set(id, hit ? `-- ${hit.decl}  (${hit.file})\n${truncate(hit.snippet)}` : null);
      }
      block = memo.get(id) ?? null;
      if (block) decl = block.slice(3, block.indexOf("  (")); // the resolved full name, so aliases dedupe
      if (seenDecl.has(decl)) continue;
    }
    if (!block) continue;
    seenDecl.add(decl);
    if (blocks.length >= MAX_HELPERS || chars + block.length > TOTAL_CHARS) { named.push(decl); continue; }
    chars += block.length;
    blocks.push(block);
  }
  if (blocks.length === 0 && named.length === 0) return "(the Lean proof names no run or library declaration beyond Mathlib)";
  const tail = named.length > 0 ? `\n\n-- also named, not supplied (read from source if needed): ${named.join(", ")}` : "";
  return blocks.join("\n\n") + tail;
}

function truncate(body: string): string {
  return body.length <= PER_HELPER_CHARS ? body : `${body.slice(0, PER_HELPER_CHARS)}\n-- … [truncated; read the file for the rest]`;
}
