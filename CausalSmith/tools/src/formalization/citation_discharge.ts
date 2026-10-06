import type { Plan } from "./plan/schema.js";

export type PlanNode = Plan["nodes"][string];

export function externalCitationReuse(node: PlanNode): string | null {
  if (
    node.disposition !== "reuse" ||
    typeof node.reuse !== "string" ||
    node.reuse.trim().length === 0 ||
    !node.reuse.includes(".") ||
    node.reuse !== node.lean_name
  ) return null;
  return node.reuse;
}

export function isDischargedCitation(node: PlanNode): boolean {
  if (
    node.citation_discharged !== true ||
    node.gate ||
    node.gate_class !== undefined ||
    (node.lean_kind !== "lemma" && node.lean_kind !== "theorem")
  ) return false;
  return node.disposition !== "reuse" || externalCitationReuse(node) !== null;
}
