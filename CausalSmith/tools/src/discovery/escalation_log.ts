// The D0 escalation journal: the orchestrator's directives to the solver.
//
// Append-only JSONL under `discovery/d0_escalation_log.jsonl`. An entry is a
// directive (free text), optionally scoped to `required_core_targets` (statement
// ids the next round must dispatch even if proved) and optionally
// `provenance_only` (recorded, never dispatched). The consumption cursor lives in
// `state.flags.d0_directives_consumed`: entries below it have been shown to a
// solver round; entries at or above it are pending and pull a resume back to D0.
//
// Legacy rows (applied-change receipts, mandates, cancellations) are read
// tolerantly and rendered as history; nothing in them is actionable any more —
// an exact edit is now a direct commit on the graph, not a mandate.
import { existsSync } from "node:fs";
import { appendFile, mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StateJson } from "../types.js";
import { artifactPath } from "../paths.js";
import { repairLatexStringsDeep } from "./core/latex_serialization.js";

export interface EscalationLogEntry {
  round: number;
  note?: string;
  directive?: string;
  required_core_targets?: string[];
  provenance_only?: boolean;
  /** Legacy applied-change receipt rows. Rendered as history only. */
  changed?: Array<{ id: string; kind: string; from: string; to: string; reason: string }>;
  /** Idempotency key of a legacy apply transaction. */
  transaction_id?: string;
  [legacy: string]: unknown;
}

export function escalationLogPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "d0_escalation_log.jsonl", [`${ctx.qid}_d0_escalation_log.jsonl`]);
}

export async function appendEscalationLog(ctx: PipelineContext, entry: EscalationLogEntry): Promise<void> {
  const p = escalationLogPath(ctx);
  await mkdir(path.dirname(p), { recursive: true });
  await appendFile(p, `${JSON.stringify(entry)}\n`, "utf8");
}

export async function readEscalationLog(ctx: PipelineContext): Promise<EscalationLogEntry[]> {
  const p = escalationLogPath(ctx);
  if (!existsSync(p)) return [];
  const entries: EscalationLogEntry[] = [];
  (await readFile(p, "utf8")).split("\n").forEach((line, i) => {
    if (line.trim().length === 0) return;
    try {
      const entry = JSON.parse(line) as EscalationLogEntry;
      repairLatexStringsDeep(entry, new Set(["source_fingerprint", "from", "to", "required_core_edit_mandates"]));
      entries.push(entry);
    } catch (err) {
      throw new Error(
        `D0 escalation journal is corrupt at ${p}:${i + 1}: ${err instanceof Error ? err.message : String(err)}. ` +
          "If it is the last line and truncated mid-write, delete that line and resume; otherwise reconstruct the " +
          "lost decision from decision_log.jsonl before resuming.",
      );
    }
  });
  return entries;
}

/** How many journal entries the solver has already been shown. */
export function directivesConsumed(state: StateJson): number {
  const n = (state.flags as { d0_directives_consumed?: unknown }).d0_directives_consumed;
  return typeof n === "number" && Number.isFinite(n) && n >= 0 ? n : 0;
}

export function isActionable(entry: EscalationLogEntry): boolean {
  return entry.provenance_only !== true && typeof entry.directive === "string" && entry.directive.trim().length > 0;
}

export function pendingDirectives(entries: EscalationLogEntry[], consumed: number): EscalationLogEntry[] {
  return entries.slice(Math.min(consumed, entries.length)).filter(isActionable);
}

/** The block a solver unit sees: every pending directive verbatim, plus the last
 *  few already-dispatched ones as history (their targets no longer bind). */
export function formatDirectiveContext(entries: EscalationLogEntry[], consumed: number, historyDepth = 3): string {
  const cut = Math.min(consumed, entries.length);
  const pending = entries.slice(cut).filter(isActionable);
  const history = entries.slice(0, cut).filter(isActionable).slice(-historyDepth);
  if (pending.length === 0 && history.length === 0) return "";
  const lines: string[] = ["=== ORCHESTRATOR DIRECTIVES ==="];
  if (pending.length > 0) {
    lines.push("Act on every ACTIVE directive below, for its required targets when it names any.");
    for (const e of pending) {
      const targets = (e.required_core_targets ?? []).length > 0 ? ` [REQUIRED TARGETS: ${e.required_core_targets!.join(", ")}]` : "";
      lines.push(`  [round ${e.round}] ACTIVE DIRECTIVE${targets}: ${e.directive}${e.note ? ` — ${e.note}` : ""}`);
    }
  }
  if (history.length > 0) {
    lines.push("Earlier directives (already dispatched; context only, they grant no emission authority):");
    for (const e of history) lines.push(`  [round ${e.round}] ${e.directive}`);
  }
  return lines.join("\n");
}
