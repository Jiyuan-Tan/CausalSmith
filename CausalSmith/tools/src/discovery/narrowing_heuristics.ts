// Heuristics that flag a proposed statement narrowing for careful review: an
// assume-the-crux rewrite (the open obligation promoted into a hypothesis) and a
// result-class degradation (a minimax / lower-bound / equivalence construct
// dropped to a surviving fragment). Conservative: a hit annotates the approval
// item; it never decides anything on its own.
import { maskNonBoundaryPeriods } from "../shared/tex_text.js";

export interface NarrowingChange {
  current?: string;
  proposed: string;
}

/** Heuristic: does a proposed statement REWRITE convert the node's own load-bearing
 *  claim into an ASSUMED hypothesis of itself — "X holds" → "Suppose X (or the hard
 *  property that delivers X). Then [a now-trivial reduction]"? That is an assume-the-crux
 *  narrowing (a laundering-adjacent move): it promotes the open proof obligation into a
 *  premise instead of restricting scope/regime. Detected by a new leading conditional
 *  premise ("Suppose/Assume … such that / with …", or a new leading Assume/Suppose clause)
 *  that the prior statement did not have. Conservative — false positives route to review. */
export function isAssumeTheCruxNarrowing(c: NarrowingChange): boolean {
  // Every `[^.]*` below runs on PERIOD-MASKED text: an abbreviation or decimal
  // ("… are i.i.d. across …", "\(\alpha \le 0.05\)") otherwise ends the clause
  // scan mid-premise — truncating `addedPremise` inside a TeX group, blinding
  // the crux-word test, and making the i.i.d. whitelist entry unreachable.
  const mask = (s: string | undefined) => maskNonBoundaryPeriods(s ?? "");
  const prem = /\b(suppose|assume)\b[^.]*\b(such that|with|so that)\b/i;
  const leadingPrem = /^\s*(suppose|assume)\b[^.]*\./i;
  const leadingClause = (s: string | undefined) => mask(s).match(/^\s*(?:suppose|assume)\b[^.]*\./i)?.[0] ?? "";
  const addedPremise = leadingClause(c.proposed).trim();
  const currentText = mask(c.current);
  const cruxProofObject = /\b(chi[-\s]?square|χ²|least[-\s]?favo[u]?rable|separation|le\s*cam|fano|two[-\s]?point|packing|testing|witness|construction|family)\b/i;
  // `i[.․]i[.․]d[.․]?` — the masked spelling of `i.i.d.` (mask sentinel ․) must
  // stay whitelisted alongside the plain `iid`.
  const REGIME_WORDS =
    /\b(regime|setting|case|class|model|iid|i[.․]i[.․]d[.․]?|independent|compact|finite|measurable|overlap|positivity|regularity|smooth|margin|sparsity|sub-?gaussian|well-specified|realizable|bounded|support|moment|integrable|dominated|tail|continuous|differentiable)\b/i;
  const regimeWhitelist = new RegExp(String.raw`^\s*(suppose|assume)\b[^.]*${REGIME_WORDS.source}[^.]*\.`, "i");
  const hadPremise = c.current !== undefined && prem.test(mask(c.current));
  const hasPremise = prem.test(mask(c.proposed));
  const hadLeadingPremise = c.current !== undefined && leadingPrem.test(mask(c.current));
  const hasLeadingPremise = leadingPrem.test(mask(c.proposed));
  const addedCruxPremise = addedPremise.length > 0 && !currentText.includes(addedPremise) && cruxProofObject.test(addedPremise);
  if (addedCruxPremise) return true; // why: generic words like bounded/family cannot whitelist proof-object premises that buy the crux.
  // AUDIT-B: whitelist only obvious regime restrictions; uncertain leading assumptions gate for review.
  // The whitelist is consulted on BOTH branches for the mid-text case: masking
  // widened `prem`'s reach across decimals/abbreviations (its purpose), which
  // otherwise flipped previously whitelisted regime narrowings ("overlap at
  // level 0.05 with margin …") into gated findings via the un-whitelisted
  // `hasPremise` branch. Suppression is deliberately narrow — EVERY
  // suppose/assume clause must read as a pure regime restriction, and a crux
  // word ANYWHERE in a clause vetoes it ("least-favorable family with bounded
  // variance" is a crux premise even though "bounded" is a regime word; a crux
  // in a SECOND premise must not hide behind a regime-only first one). False
  // positives route to review; false negatives launder the crux.
  const premiseClauses = [...mask(c.proposed).matchAll(/\b(?:suppose|assume)\b[^.]*/gi)].map((m) => m[0]);
  const allPremisesPureRegime =
    premiseClauses.length > 0 &&
    premiseClauses.every((clause) => REGIME_WORDS.test(clause) && !cruxProofObject.test(clause));
  return (
    (hasPremise && !hadPremise && !allPremisesPureRegime) ||
    (hasLeadingPremise && !hadLeadingPremise && !regimeWhitelist.test(mask(c.proposed)))
  );
}

/** The DUAL of assume-the-crux: a narrowing that DROPS the node's load-bearing RESULT
 *  (a minimax/lower-bound risk assertion, an equivalence, or an iff) — keeping only an
 *  easy surviving fragment — and would then be marked "proved". This degrades the result
 *  class (the anti-laundering case in the open-kernel re-tiering rule) and must be gated:
 *  the result belongs in the node (open if unproven), not silently removed to discharge.
 *  Detects a load-bearing construct present in `current` but absent in `proposed`. */
export function isResultClassDegradation(c: NarrowingChange): boolean {
  if (c.current === undefined) return false;
  // load-bearing result constructs (minimax risk bound, equivalence, iff).
  // `[\s\S]` (not `.`): these assertions are routinely typeset across lines in
  // an `aligned` block, and a `.`-based scan missed every multi-line instance.
  // `\ge`/`\geq` are the TeX spellings of the lower-bound comparator — the
  // ASCII `>=` never occurs in real TeX, which made that construct a dead guard.
  const constructs: RegExp[] = [
    /inf[_{\s][\s\S]*sup[_{\s][\s\S]*\bE_?P?\b/i, // inf_hat sup_P E|...|  (a minimax-risk assertion)
    /(?:>=|\\geq?\b)\s*c[_0-9]*\s*R_?n?\^?\*/i, //  >= c R_n^*  (a lower-bound on the rate)
    /\bequivalent\b[\s\S]*\bR_?n?\^?\*/i, // "equivalent ... to R_n^*"
    // ONE alternation for every equivalence spelling: with `\iff` matched only
    // via the English-word branch (backslash is a \b boundary), a pure notation
    // swap `\iff` → `\Leftrightarrow` read as "construct dropped" and falsely
    // gated a meaning-preserving rewrite.
    /\bif and only if\b|(?<!\\)\biff\b|\\iff\b|\\Longleftrightarrow\b|\\Leftrightarrow\b|\\equiv\b/i,
  ];
  for (const re of constructs) {
    if (re.test(c.current) && !re.test(c.proposed)) return true;
  }
  return false;
}


/** Every review annotation the heuristics attach to a claim change. */
export function narrowingWarnings(current: string, proposed: string): string[] {
  const c = { current, proposed };
  const out: string[] = [];
  if (isAssumeTheCruxNarrowing(c)) out.push("REVIEW: assume-the-crux narrowing — a new assume/suppose premise may promote the open obligation into a hypothesis (state the result and leave the construction an open obligation instead)");
  if (isResultClassDegradation(c)) out.push("REVIEW: result-class degradation — the load-bearing construct (minimax / lower bound / equivalence / iff) is dropped to a surviving fragment (keep the result, mark it open if unproven)");
  return out;
}
