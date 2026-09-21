// F5 bank-soundness gate: text-based (no LSP) scan of a banked artifact subdir plus
// its reachable CausalSmith/Mathlib closure for real `sorry` tokens and cheat tokens.
// Extracted from the retired stage3.ts (F3) so the kept F5 bank keeps its mechanical
// soundness check. Pure scanning — no Lean elaboration.

import { readFileSync } from "node:fs";
import path from "node:path";
import { stripLeanComments } from "../graph/extractor.js";
import { listLeanFiles } from "../pipeline_support.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { LEAN_IMPORT_RE_GM, parseLeanImport } from "../shared/lean_syntax.js";

/**
 * Comment-aware "does this file contain a REAL (uncommented) `sorry` token?".
 * NEVER false-negatives a genuine `sorry`; a false positive is merely a wasted check, not a
 * correctness loss. Uses the char-accurate `stripLeanComments` (nesting-, string- and
 * char-literal-aware) — the previous line-granular scanner skipped an ENTIRE line that merely
 * STARTED inside a block comment, so code after a mid-line `-/` close escaped the scan.
 */
export function textHasRealSorry(text: string): boolean {
  return /\bsorry\b/.test(stripLeanComments(text));
}

/** repoRoot-relative (forward-slash) form of a path. */
function relOf(file: string, repoRoot: string): string {
  const r = path.isAbsolute(file) ? path.relative(repoRoot, file) : file;
  return r.split(path.sep).join("/");
}

/** Artifact files plus the transitive closure of every `CausalSmith.*` file they import. */
function reachableFileClosure(researchFiles: string[], repoRoot: string): string[] {
  const seen = new Set<string>();
  const all: string[] = [];
  const queue = [...researchFiles];
  while (queue.length) {
    const f = queue.shift()!;
    const abs = path.isAbsolute(f) ? f : path.join(repoRoot, f);
    if (seen.has(abs)) continue;
    seen.add(abs);
    all.push(abs);
    let src: string;
    try {
      src = readFileSync(abs, "utf8");
    } catch {
      continue;
    }
    for (const m of maskLeanCommentsAndStrings(src).matchAll(LEAN_IMPORT_RE_GM)) {
      const imported = parseLeanImport(m[0]);
      if (imported && /^CausalSmith\./u.test(imported.module)) {
        // A component written `«Foo Bar»` resolves to the file `Foo Bar.lean`: Lean's module path
        // uses the raw name, so the guillemets are escaping, not part of the path.
        const modulePath = imported.module
          .split(".")
          .map((c) => c.replace(/^«(.*)»$/u, "$1"))
          .join("/");
        queue.push(path.join(repoRoot, modulePath + ".lean"));
      }
    }
  }
  return all;
}

/** Scan the artifact + its reachable closure for cheat tokens (axiom/opaque/unsafe/admit/sorry).
 *  `native_decide` was removed from this list on 2026-09-04 (operator call) — do not re-add;
 *  keep aligned with `scanResearchCheatTokens` in `proof_review_loop.ts`. */
async function scanCheatTokens(
  researchFiles: string[],
  repoRoot: string,
): Promise<Array<{ file: string; line: number; token: string }>> {
  const all = reachableFileClosure(researchFiles, repoRoot);
  // Reject admitted proof tokens here too, so closure banking cannot launder them as non-cheats.
  const TOKEN = /\b(axiom|opaque|unsafe|admit|sorry|sorryAx)\b/;
  const found: Array<{ file: string; line: number; token: string }> = [];
  for (const abs of all) {
    let text: string;
    try {
      text = readFileSync(abs, "utf8");
    } catch {
      continue;
    }
    // stripLeanComments preserves newlines, so line numbers stay accurate; unlike the old
    // line-granular scan it also sees code AFTER a mid-line block-comment close.
    const lines = stripLeanComments(text).split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const m = TOKEN.exec(lines[i]);
      if (m) found.push({ file: relOf(abs, repoRoot), line: i + 1, token: m[1] });
    }
  }
  return found;
}

/**
 * F5 bank-soundness gate: scan the artifact subdir plus its reachable
 * CausalSmith closure for real `sorry` tokens and cheat tokens. Returns
 * human-readable issue strings; empty = bankable.
 */
export async function bankSoundnessIssues(leanDir: string, repoRoot: string): Promise<string[]> {
  const research = await listLeanFiles(leanDir);
  const issues: string[] = [];
  for (const abs of reachableFileClosure(research, repoRoot)) {
    try {
      if (textHasRealSorry(readFileSync(abs, "utf8"))) {
        issues.push(`sorry in ${relOf(abs, repoRoot)}`);
      }
    } catch {
      issues.push(`unreadable file ${relOf(abs, repoRoot)}`);
    }
  }
  for (const c of await scanCheatTokens(research, repoRoot)) {
    issues.push(`${c.token} in ${c.file}:${c.line}`);
  }
  return issues;
}
