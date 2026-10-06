// THE single authority for "what is the current, complete paper".
//
// Why this module exists
// ----------------------
// D0 keeps the paper's content in several stores, and each reviewer used to
// assemble its own view from a different subset:
//
//   D0.5.1/D0.5.2  rendered core.json                      (in-memory)
//   D0.5.G         read writeup.tex                        (from disk)
//   D0.R           edited raw core.json                    (in-memory)
//   D0 adjudicator read proto_core.json + proposed_*.json  (from disk)
//
// Those views disagree. The most expensive disagreement: when a round proposes a
// structural change, `stage0_solve` deliberately withholds that round's fresh
// proofs from core.json and banks them in proposed_proofs.json. A reviewer
// assembling from core.json alone therefore reads STALE proof text and reports
// the result as "merely asserted" / "incomplete" — a plumbing artifact delivered
// as a mathematical defect. That drove an eight-round REJECT loop on the
// 2026-07-18 stat_cot_observational_efficiency run.
//
// Fixing that per-reviewer is what created the drift in the first place. So the
// rule is: NOBODY assembles the paper themselves. Every consumer calls
// `loadPaperView` and reads `view.core` / `view.tex`. A new reviewer added later
// is correct by construction rather than by remembering to overlay.
import { existsSync } from "node:fs";
import type { PipelineContext } from "../../types.js";
import { type Core } from "./schema.js";
import { renderCoreTex } from "./render_tex.js";
import { coreJsonPath } from "../stages/d0_core.js";
import { readTypedCore } from "./core_io.js";

/** A same-round proof payload banked in `proposed_proofs.json` while a structural
 *  proposal is pending. */
export interface PaperView {
  /** The core with this round's provisional proofs overlaid. Use this for review,
   *  for rendering, and as the edit base — never the raw core.json. */
  core: Core;
  /** Deterministic render of `core`. Identical bytes for every consumer. */
  tex: string;
  /** Always empty since the graph store: kept for the consumers' log line. */
  overlaid: string[];
  unmatchedProofs: string[];
  /** Provenance, for the one-line log every consumer emits. */
  provenance: { corePath: string; provisionalPath: string | null; statements: number; texChars: number };
}

/** Assemble the canonical paper view. Fail-closed: a missing or empty core is a
 *  plumbing failure, never something to hand a referee and let it render a verdict on. */
export async function loadPaperView(ctx: PipelineContext, opts?: { corePath?: string }): Promise<PaperView> {
  const corePath = opts?.corePath ?? coreJsonPath(ctx);
  if (!existsSync(corePath)) {
    throw new Error(`Cannot assemble the paper view: core is absent at ${corePath}. This is a plumbing failure.`);
  }
  const core = await readTypedCore(corePath);
  const tex = renderCoreTex(core);
  if (tex.trim().length === 0) {
    throw new Error(`Assembled paper view is EMPTY (core ${corePath} rendered to 0 chars). Refusing to review nothing.`);
  }
  return {
    core,
    tex,
    overlaid: [],
    unmatchedProofs: [],
    provenance: { corePath, provisionalPath: null, statements: core.statements.length, texChars: tex.length },
  };
}

/** One-line provenance log. Every consumer emits this, so a paper-assembly problem is
 *  visible in the transcript rather than inferred from a downstream verdict. The whole
 *  prompt's char count cannot reveal it — the static rubric dominates that number. */
export function logPaperView(view: PaperView, consumer: string): void {
  console.error(
    `[${consumer}] paper view: ${view.provenance.statements} statement(s), ${view.provenance.texChars} tex chars, ` +
      `${view.overlaid.length} provisional proof(s) overlaid` +
      (view.overlaid.length > 0 ? ` (${view.overlaid.join(", ")})` : "") +
      ` from ${view.provenance.corePath}`,
  );
  if (view.unmatchedProofs.length > 0) {
    console.error(
      `[${consumer}] PLUMBING FAULT: ${view.unmatchedProofs.length} provisional proof(s) name no core statement ` +
        `and are NOT in the reviewed paper: ${view.unmatchedProofs.join(", ")}.`,
    );
  }
}
