/**
 * Strict JSON Schemas for every model reply the presentation pipeline parses. Passed to the
 * runners (`outputSchema` for codex, `jsonSchema` for claude) so the API constrains decoding:
 * the reply is valid JSON of this shape by construction, and the parsers only extract and
 * validate content. Strict-mode rules: every property required, `additionalProperties: false`,
 * no dynamic-key records, optional fields as empty lists / `false` / `null` (folded by the site).
 */
type Schema = Record<string, unknown>;
const obj = (properties: Record<string, Schema>): Schema => ({
  type: "object", properties, required: Object.keys(properties), additionalProperties: false,
});
const arr = (items: Schema): Schema => ({ type: "array", items });
const str: Schema = { type: "string" };
const num: Schema = { type: "number" };
const int: Schema = { type: "integer" };
const bool: Schema = { type: "boolean" };
const strs = arr(str);
const oneOf = (...values: string[]): Schema => ({ type: "string", enum: values });

/** P1 statement-equivalence judge, one statement. */
export const EQUIVALENCE_REPLY = obj({ obj_id: str, verdict: oneOf("faithful", "drift", "missing-coverage"), detail: str });
/** P1 statement-equivalence judge, batched. */
export const EQUIVALENCE_BATCH_REPLY = obj({ results: arr(EQUIVALENCE_REPLY) });
/** P2 proof judge. */
export const PROOF_AUDIT_REPLY = obj({ theorem: str, verdict: oneOf("faithful", "unfaithful", "incomplete"), issues: strs });
/** P2 proof repair and P3 prose reviser: ordered exact replacements. */
export const REPLACEMENTS_REPLY = obj({ replacements: arr(obj({ before: str, after: str })) });
/** P4 component discovery: which Lean pieces formalize an environment. */
export const COMPONENTS_REPLY = obj({
  components: arr({ anyOf: [
    obj({ type: oneOf("decl"), decl: str }),
    obj({ type: oneOf("hypotheses"), theorem: str, binders: strs }),
  ] }),
});
/** P5 referee. */
export const REFEREE_REPLY = obj({
  recommendation: oneOf("accept", "minor_revision", "major_revision", "reject"),
  score: num,
  score_rationale: str,
  summary: str,
  strengths: strs,
  findings: arr(obj({
    severity: oneOf("major", "minor", "nit"),
    section: str,
    issue: str,
    fix: str,
    kind: oneOf("prose", "structure", "statement", "citation", "other"),
    finding_id: str,
    remedy: oneOf("rewrite", "citation_research", "new_theorem", "simulation", "implementation", "source_change", "adjudication"),
  })),
  questions_for_authors: strs,
});
/** P3 overclaim auditor. */
export const OVERCLAIM_REPLY = obj({ flags: arr(obj({ id: int, sentence: str, class: oneOf("overclaim"), fix: str })), clean: bool });
/** P3 citation-support auditor, batched. */
export const CITATION_SUPPORT_REPLY = obj({ results: arr(obj({ id: int, verdict: oneOf("supported", "unsupported", "unverifiable"), reason: str })) });
/** P3 rubric reviewers (both the claude and the codex reviewer). */
export const RUBRIC_REPLY = obj({
  scores: obj({ claims_vs_assumptions: num, positioning: num, assumption_discussion: num, writing: num }),
  weaknesses: strs,
  defects: strs,
});
/** P1 notation reviewer. */
export const NOTATION_REPLY = obj({
  clean: bool,
  problems: arr(obj({ symbol: str, used_in: strs, case: oneOf("undefined", "wrong-ref", "mismatch", "rendering"), fix: str })),
});
/** P4 nl-links verifier: every field present; the site folds empty lists and false away. */
export const NL_LINKS_VERIFY_REPLY = obj({
  verdicts: arr(obj({ obj_id: str, claim: str, ok: bool, segments: strs, unstated: bool, decls: strs, presentationOnly: bool })),
});
