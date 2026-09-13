---
qid: pid_coarsened_iv_facet_envelope
spec: v1
topic: "Sharp single-bin facet envelope for arbitrary finite coarsened-exposure IV bounds. Observe iid (Z,X,Y) with randomized binary Z, binary Y, finite X={a,b,c_1,...,c_m}, and a declared trusted set T containing a,b whose category interventions are well defined and satisfy exclusion and consistency; untrusted categories impose no cross-Z outcome restriction. For theta_ab=E[Y(b)-Y(a)], prove the identified interval is sharp and its lower/upper endpoints are the eight binary-exposure Balke-Pearl affine pieces plus exactly two pieces per trusted nuisance category. Derive a complete two-diagonal transport reduction, explicit endpoint-attaining finite response laws, the exact strict-improvement criterion for adding trust, and invariance to splitting or merging wholly untrusted bins. Give an O(|X|) endpoint/active-face evaluator and finite-sample simultaneous whole-set inference valid at ties and zero cells. Consumer: Du Toit et al.'s LEAP adherence analysis, where the theorem determines whether separately justified intermediate exposure categories can change the assumption-free low-versus-high consumption interval. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Coupling the two instrument-arm factual responses on a complete bipartite graph minus a partial matching reduces the lower endpoint to maximizing mass on two target diagonals. After reserving those masses, feasibility has two individual caps and one total cap per trusted nuisance outcome cell; exact maximization yields the claimed affine envelope, and a finite augmenting-path completion constructs attaining laws. Checks passed 840 response-LP cases for 2-8 exposure categories and all trust cardinalities, 32 saturated-response cases, and 9,648 exact rational endpoint constructions; maximum LP discrepancy was 7.78e-16. LEAP arm denominators 305 and 312 reproduce the low-minus-high interval [-5073/31720,10/61]. UNRESOLVED BOTTLENECK: Independently formalize and verify the transport domination and endpoint-completion argument; the optional moment-selected Gaussian multiplier procedure still needs a uniform local-tie/vanishing-variance proof, while finite-sample Hoeffding whole-set coverage is already derived. EARLY KILL TEST: Enumerate legal denominator-three four-category tables under every trust subset containing a,b and reconstruct both reserved-diagonal endpoint laws exactly; stop if any residual flow, margin, or objective equality fails. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_coarsened_iv_facet_envelope.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The title's word \"facet\" exceeds the delivered geometric statement: the proof establishes a complete affine evaluation list but expressly does not establish irredundancy or that every listed function supports a facet."
  - "The claimed LEAP relevance is not developed into a reproducible worked application or trust-sensitivity analysis in the stitched note, limiting the demonstrated practical significance at a leading econometrics journal."
  - "The result is a genuine field contribution but remains too specialized, and its sharper inference rung too incomplete, for flagship status."
  - "D0.5.G projected paper-score gate: paper_score_ceiling 7.2 < 7.4, so the graded tier 'field' is capped at 'subfield'."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_strict_regime_separation.json
  - discovery/solve_prop_untrusted_refinement_invariance.json
  - discovery/solve_thm_finite_sample_whole_set.json
  - discovery/solve_prop_published_reductions.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the arbitrary-cardinality affine endpoint envelope, finite endpoint-attaining
  response laws, trust nesting and strict separation, untrusted-refinement invariance, linear-time
  evaluation, and finite-sample Hoeffding whole-set coverage; the final math review passed with no
  findings and all cited leaves were source-attested. The package missed the field score floor because
  facet irredundancy was not proved, the LEAP calculation was not developed into a reproducible worked
  trust-sensitivity application, and the uniform Gaussian/local-tie inference rung remained open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24553301
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24553301
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_coarsened_iv_facet_envelope / v1 — Downgraded

**Topic.** Sharp single-bin facet envelope for arbitrary finite coarsened-exposure IV bounds. Observe iid (Z,X,Y) with randomized binary Z, binary Y, finite X={a,b,c_1,...,c_m}, and a declared trusted set T containing a,b whose category interventions are well defined and satisfy exclusion and consistency; untrusted categories impose no cross-Z outcome restriction. For theta_ab=E[Y(b)-Y(a)], prove the identified interval is sharp and its lower/upper endpoints are the eight binary-exposure Balke-Pearl affine pieces plus exactly two pieces per trusted nuisance category. Derive a complete two-diagonal transport reduction, explicit endpoint-attaining finite response laws, the exact strict-improvement criterion for adding trust, and invariance to splitting or merging wholly untrusted bins. Give an O(|X|) endpoint/active-face evaluator and finite-sample simultaneous whole-set inference valid at ties and zero cells. Consumer: Du Toit et al.'s LEAP adherence analysis, where the theorem determines whether separately justified intermediate exposure categories can change the assumption-free low-versus-high consumption interval. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Coupling the two instrument-arm factual responses on a complete bipartite graph minus a partial matching reduces the lower endpoint to maximizing mass on two target diagonals. After reserving those masses, feasibility has two individual caps and one total cap per trusted nuisance outcome cell; exact maximization yields the claimed affine envelope, and a finite augmenting-path completion constructs attaining laws. Checks passed 840 response-LP cases for 2-8 exposure categories and all trust cardinalities, 32 saturated-response cases, and 9,648 exact rational endpoint constructions; maximum LP discrepancy was 7.78e-16. LEAP arm denominators 305 and 312 reproduce the low-minus-high interval [-5073/31720,10/61]. UNRESOLVED BOTTLENECK: Independently formalize and verify the transport domination and endpoint-completion argument; the optional moment-selected Gaussian multiplier procedure still needs a uniform local-tie/vanishing-variance proof, while finite-sample Hoeffding whole-set coverage is already derived. EARLY KILL TEST: Enumerate legal denominator-three four-category tables under every trust subset containing a,b and reconstruct both reserved-diagonal endpoint laws exactly; stop if any residual flow, margin, or objective equality fails. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_coarsened_iv_facet_envelope.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 BELOW NOVELTY FLOOR: paper_score_ceiling 7.2 is below the 7.4 field gate; the math is sound, but facet irredundancy, a reproducible LEAP trust-sensitivity application, and uniform Gaussian inference were not delivered.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The validity-gate consult identified a bounded re-raise path: retitle the result as a sharp
linear-size affine envelope and add the already-presolved LEAP calculation (arm denominators 305 and
312, interval `[-5073/31720, 10/61]`) together with the no-change-under-middle-category-trust
sensitivity result. The mill's standing field-floor rule required banking this run without that rescore.
