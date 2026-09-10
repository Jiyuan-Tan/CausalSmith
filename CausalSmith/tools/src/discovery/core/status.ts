// One rule for "what status does a node with a proof carry?".
//
// Used only by the legacy render (`core/assemble.ts`) that the graph-store converter
// runs once per migrated run; the live stage derives status in `vcs/validity.ts`. `cited` must survive: a node whose result is imported from the literature is
// not something this paper proved, and overwriting its status to `proved` is a
// provenance claim the run cannot support.

import type { CoreStatement } from "./schema.js";

/**
 * The status a node takes once a proof has been attached to it.
 *
 * `cited` is preserved; everything else becomes `proved`.
 *
 * WARNING PATH: callers can reach this with an EMPTY proof, which would publish
 * `status: "proved"` over nothing. That has never been observed in a real run, so this
 * preserves the long-standing behaviour rather than silently changing it — but it says
 * so, because the alternative is an unearned `proved` in a rendered paper. The recovery
 * tool independently chose the stricter rule (keep the prior status when the proof is
 * empty); if this warning ever fires, that is the rule to adopt.
 */
export function solvedStatus(
  s: { status?: CoreStatement["status"]; id?: string; proof_tex?: string },
): CoreStatement["status"] {
  if (s.status === "cited") return "cited";
  if (s.proof_tex !== undefined && s.proof_tex.trim().length === 0) {
    console.warn(
      `[D0] status: marking '${s.id ?? "<unknown>"}' proved with an EMPTY proof — ` +
        "the node will render as established with nothing behind it. Inspect before trusting this round.",
    );
  }
  return "proved";
}
