---
qid: eid_mobius_null_compliance
spec: v1
topic: "Möbius-null compliance envelope for three-factor perfect-complier effects. Fix randomized full-support assignment Z over all subsets of {A,B,C}, one-sided received bundle D=g(Z) subseteq Z, outcome exclusion Y=Y(D), and independence of Z from the WARP-rational response map g and all bundle outcomes. Let g*(z)=z have positive mass and sigma_t(g)=sum_{z superseteq t}(-1)^{|z|-|t|}1{g(z)=t}. Prove that the unique inclusion-maximal WARP class containing all eight coordinate-separable maps and outcome-nonrestrictively identifying all eight perfect-complier means is E3={g*} union {g:sigma_t(g)=0 for every t}; classify its exactly 29 maps, including 21 interactive maps, by a symbolic Möbius/choice argument. Identify each mean by the signed probability and outcome-moment transforms and all seven factorial effects by Walsh contrasts. For every rational h outside E3, construct two finite Bernoulli outcome/type laws with identical observed (Z,D,Y) law and a different target mean. Add joint influence functions and simultaneous Wald inference when the perfect-complier share is bounded below, plus Bonferroni-Fieller inversion for weak denominators, without claiming uniform vanishing-share adaptation. Consumer: factiv::iv_factorial and Blackwell–Pashley's New Haven perfect-complier factorial analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact enumeration of all 4096 one-sided response maps found 244 WARP-rational maps and confirmed a 29-map envelope with 21 interactive additions; a symbolic 28=1+9+18 classification and finite Bernoulli observational-equivalence construction cover all 215 excluded additions. An outside-envelope mixture can pass all eight probability diagnostics, so outcome-moment isolation and the full converse are essential. Current Goff, Blackwell–Pashley, Kormos–Lieli–Huber, and 2025–2026 citing work did not contain the classification; separate JASA supplement C was unavailable. UNRESOLVED BOTTLENECK: Prove symbolically that the full-offer-pair branch permits exactly four maps with the remaining factor unresponsive and two with it responsive, completing the behavioral classification independently of enumeration. EARLY KILL TEST: Retrieve JASA supplement C and test whether it already permits the six null types with no irrelevant coordinate and states the same maximal perfect-complier support class; an equivalent result kills novelty. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_mobius_null_compliance.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The exact fixed-K=3 one-sided WARP result is sound, but lacks a broader-factor/model frontier or substantive empirical/software demonstration needed to clear the field floor."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves the advertised 29-map classification, signed identification formulas, and both directions of maximality within the explicitly stated one-sided three-factor WARP ambient class; no open conjecture remains in that headline."
  - "Its contribution is nevertheless confined to three factors, requires retention of the eight-map separable baseline, and provides no applied reanalysis or software evidence showing that the 21 added types materially change an empirical conclusion."
  - "The Fieller coverage proof uses positive variance only at u=mu_t^star; requiring it for every real u is materially stronger."
  - "The attested quotation does not establish the lemma's claimed joint cell influence representation, exact primitive hypotheses, Fieller studentization, or seven-dimensional Wald conclusion."
  - "Not salvageable within scope — bank downgraded, or re-anchor the proposal (rewind D-1.2)."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_symbolic_classification.json
  - discovery/solve_thm_classification.json
  - discovery/solve_thm_envelope_iff.json
  - discovery/solve_tex/solve_oeq_symbolic_classification.tex
  - discovery/solve_tex/solve_thm_classification.tex
  - discovery/solve_tex/solve_thm_envelope_iff.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery completed the symbolic 28-null-map classification, the exact 29-map
  envelope, signed identification formulas, and the all-excluded-type converse.
  The mathematics remained sound, but the independent referee capped the fixed
  three-factor one-sided result at incremental novelty; field status would require
  a broader-factor/model frontier or a substantive application/software result.
  The archived inference rung also retains nonminimal-assumption and source-match
  caveats and was never formalized in Lean.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 10622420
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 10622420
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_mobius_null_compliance / v1 — Downgraded

**Topic.** Möbius-null compliance envelope for three-factor perfect-complier effects. Fix randomized full-support assignment Z over all subsets of {A,B,C}, one-sided received bundle D=g(Z) subseteq Z, outcome exclusion Y=Y(D), and independence of Z from the WARP-rational response map g and all bundle outcomes. Let g*(z)=z have positive mass and sigma_t(g)=sum_{z superseteq t}(-1)^{|z|-|t|}1{g(z)=t}. Prove that the unique inclusion-maximal WARP class containing all eight coordinate-separable maps and outcome-nonrestrictively identifying all eight perfect-complier means is E3={g*} union {g:sigma_t(g)=0 for every t}; classify its exactly 29 maps, including 21 interactive maps, by a symbolic Möbius/choice argument. Identify each mean by the signed probability and outcome-moment transforms and all seven factorial effects by Walsh contrasts. For every rational h outside E3, construct two finite Bernoulli outcome/type laws with identical observed (Z,D,Y) law and a different target mean. Add joint influence functions and simultaneous Wald inference when the perfect-complier share is bounded below, plus Bonferroni-Fieller inversion for weak denominators, without claiming uniform vanishing-share adaptation. Consumer: factiv::iv_factorial and Blackwell–Pashley's New Haven perfect-complier factorial analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact enumeration of all 4096 one-sided response maps found 244 WARP-rational maps and confirmed a 29-map envelope with 21 interactive additions; a symbolic 28=1+9+18 classification and finite Bernoulli observational-equivalence construction cover all 215 excluded additions. An outside-envelope mixture can pass all eight probability diagnostics, so outcome-moment isolation and the full converse are essential. Current Goff, Blackwell–Pashley, Kormos–Lieli–Huber, and 2025–2026 citing work did not contain the classification; separate JASA supplement C was unavailable. UNRESOLVED BOTTLENECK: Prove symbolically that the full-offer-pair branch permits exactly four maps with the remaining factor unresponsive and two with it responsive, completing the behavioral classification independently of enumeration. EARLY KILL TEST: Retrieve JASA supplement C and test whether it already permits the six null types with no irrelevant coordinate and states the same maximal perfect-complier support class; an equivalent result kills novelty. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_mobius_null_compliance.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Not salvageable within scope — bank downgraded, or re-anchor the proposal.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The validity gate confirmed `terminal:below-floor`, not a correctness failure.
Future re-raises should lift the archived symbolic classification and converse,
while independently rebuilding the inference claims and completing the missing
Supplement-C novelty audit.
