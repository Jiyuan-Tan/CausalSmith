import { readFile } from "node:fs/promises";
import { parseTypedCore } from "../discovery/core/core_io.js";
import type { Core } from "../discovery/core/schema.js";

/** Remove fields that F1.5/F2 never need while preserving the typed structure. */
export function formalizationCoreContextValue(core: Core): Record<string, unknown> {
  const projected = structuredClone(core) as unknown as Record<string, unknown>;
  for (const key of [
    "tldr",
    "project_justification",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "statement_notes",
    "comparator_promise_table",
    "bibliography",
  ]) delete projected[key];
  if (Array.isArray(projected.statements)) {
    projected.statements = projected.statements.map((value) => {
      const statement = { ...(value as Record<string, unknown>) };
      delete statement.proof_tex;
      delete statement.justification;
      delete statement.gap;
      delete statement.consumer;
      return statement;
    });
  }
  return projected;
}

/** The F1 planner's core view on a re-plan: the slim view plus the bibliography entries a node
 *  cites (F1 mints the plan's `citations[]` from them); the rest of the bibliography is positioning. */
export function plannerCoreContextValue(core: Core): Record<string, unknown> {
  const cited = new Set<string>();
  for (const s of core.statements) if (s.source?.cite) cited.add(s.source.cite);
  for (const a of core.assumptions) if (a.standard?.cite) cited.add(a.standard.cite);
  const bibliography = (core.bibliography ?? []).filter((b) => cited.has(b.key));
  const projected = formalizationCoreContextValue(core);
  return bibliography.length > 0 ? { ...projected, bibliography } : projected;
}

/**
 * The view cut down to the nodes in `ids`, with the symbols those nodes use: the ones their
 * `free_symbols` declare and the symbols those are defined from (`refs`); every symbol when a
 * kept node declares none (an absent declaration may use any). Settings and the bibliography
 * stay on disk.
 */
export function restrictCoreContextValue(view: Record<string, unknown>, ids: ReadonlySet<string>): Record<string, unknown> {
  type Node = { id?: unknown; free_symbols?: unknown };
  type Sym = { name: string; refs?: string[] };
  const keep = (list: unknown): Node[] =>
    Array.isArray(list) ? (list as Node[]).filter((n) => ids.has(String(n.id))) : [];
  const assumptions = keep(view.assumptions);
  const definitions = keep(view.definitions);
  const statements = keep(view.statements);
  const all = Array.isArray(view.symbols) ? (view.symbols as Sym[]) : [];
  const kept = [...assumptions, ...definitions, ...statements];
  let symbols = all;
  if (kept.every((n) => Array.isArray(n.free_symbols))) {
    const used = new Set(kept.flatMap((n) => n.free_symbols as string[]));
    for (let grew = true; grew; ) {
      grew = false;
      for (const s of all) {
        if (!used.has(s.name)) continue;
        for (const r of s.refs ?? []) if (!used.has(r)) { used.add(r); grew = true; }
      }
    }
    symbols = all.filter((s) => used.has(s.name));
  }
  return { qid: view.qid, symbols, assumptions, definitions, statements };
}

/** Structural core view for F1.5 reuse-fit and F2 scaffolding. These stages
 * need exact declarations and dependency metadata, not the completed paper's
 * proof bodies, positioning prose (per-statement justification/gap/consumer,
 * the comparator table), or bibliography (F2's cited-gate docstrings come from
 * the plan's `citations[]`, which F1 mints from the raw core). Parse first so
 * projection never hides a malformed/missing core. PROMPT-ONLY: this string is
 * never persisted; later stages read core.json itself. Serialized compact —
 * indentation was ~11% of the F2/F1.5 prompt bytes. */
export async function readFormalizationCoreContext(
  corePath: string,
  label: string,
): Promise<string> {
  let raw: string;
  try {
    raw = await readFile(corePath, "utf8");
  } catch (err) {
    throw new Error(`${label}: required typed core is unreadable at ${corePath}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const core = parseTypedCore(raw, `${label}: typed core ${corePath}`);
  return JSON.stringify(formalizationCoreContextValue(core));
}
