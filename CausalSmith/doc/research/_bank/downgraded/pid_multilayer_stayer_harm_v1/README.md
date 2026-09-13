---
qid: pid_multilayer_stayer_harm
spec: v1
topic: "Closed-form sharp harm bounds for stayers under ordered multilayer selection. Fix any finite L>=2, randomized Z, D_z in {0,...,L} with D_1>=D_0, binary Y observed when D>0, unrestricted potential-outcome dependence, and an observable positive lower bound on total positive-layer stayer mass. Characterize the exact joint region of layer-stayer masses s_d and harm masses h_d; prove the stayer diagonal is the Cartesian box ell_d=max(0,C_d-R_{d-1})<=s_d<=u_d=min(r_d,c_d), derive jointly attainable hinge bounds (s_d-a_d)_+<=h_d<=min(s_d,b_d), and obtain O(L) closed-form sharp endpoints for the fraction harmed among D_0=D_1>0 plus the iff certificate q_0d-q_1d>R_d-C_d for unavoidable harm. Give exact confidence-region projection and directional numerical-delta inference at ties and structural zero cells. Consumer: KMV's Job Corps/WorkAdvance multilayer Lee analyses and Lee-bounds software. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived the Cartesian diagonal projection by strict-triangular residual transport, the simultaneous binary-outcome completion, and closed-form endpoint ratios. Exact L=2 bounds are [8/25,10/11]; an all-positive L=3 example gives [1/9,10/11]. A 31-arc missing-outcome network has a valid decoder, and 180 independent programs for L=2 through 7, including zero cells, matched the formulas below 1.5e-15. Checked KMV, Possebom--Riva, Kallus, Khandamiryan--Semenova, and generic transport precedents; none supplied the all-layer joint box and contraction. UNRESOLVED BOTTLENECK: Prove conditional bounded-Lipschitz validity of the joint endpoint numerical-delta bootstrap at every fixed observable law, including simultaneous hinge equalities and structural zero cells, using the ambient formula extension and a defined fallback outside the positive-denominator neighborhood. EARLY KILL TEST: Independently enumerate small rational L=3 margins with zero masses and compare both closed-form endpoints against the full 31-arc expanded-state ratio program; any mismatch in the Cartesian projection or simultaneous outcome completion stops the paper. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_multilayer_stayer_harm.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "No proved numerical-delta validity theorem at simultaneous hinge ties and structural-zero multinomial cells; the note only invokes Hong--Li conditional on unverified premises."
  - "No empirical/software demonstration beyond a two-layer witness."
  - "The authoritative D0.5 checkpoint assessed subfield below the field floor, with projected paper_score_ceiling 6.5 < 7.4, and 'Not salvageable within scope'."
reusable_artifacts:
  - "discovery/core.json — proved theorem graph for the general finite linear-response-type fractional-flow programs and exact decoder"
  - "discovery/solve_thm_diagonal_box.json — ordered Strong-Monotonicity Cartesian diagonal projection"
  - "discovery/solve_thm_closed_form_harm_interval.json — sharp O(|X|L) endpoint contraction and unavoidable-harm certificate"
  - "discovery/writeup.tex — complete derivation note, literature positioning, and exact two-layer witness"
seeds_burned:
  - index: 0
    one_liner: "seed:joint-stayer-harm-box"
    reason: "The selected stayer-harm seed produced sound subfield-tier identification results but did not reach the fixed field floor without a new inference and implementation workstream."
proof_attempt_summary: |
  D0 proved sharp harmed-stayer programs with an exact decoder for arbitrary finite linear response-type restrictions, then proved the Cartesian prism, O(|X|L) endpoints, and iff harm certificate under KMV Strong Monotonicity. The identification mathematics survived maximality and correctness review, but the promised numerical-delta validity result at hinge ties and structural zeros was not proved. Reaching field tier would require that new inference theorem plus meaningful implementation or empirical validation, so the sound result was banked at subfield tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37850264
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 37850264
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_multilayer_stayer_harm / v1 — Downgraded

**Topic.** Closed-form sharp harm bounds for stayers under ordered multilayer selection. Fix any finite L>=2, randomized Z, D_z in {0,...,L} with D_1>=D_0, binary Y observed when D>0, unrestricted potential-outcome dependence, and an observable positive lower bound on total positive-layer stayer mass. Characterize the exact joint region of layer-stayer masses s_d and harm masses h_d; prove the stayer diagonal is the Cartesian box ell_d=max(0,C_d-R_{d-1})<=s_d<=u_d=min(r_d,c_d), derive jointly attainable hinge bounds (s_d-a_d)_+<=h_d<=min(s_d,b_d), and obtain O(L) closed-form sharp endpoints for the fraction harmed among D_0=D_1>0 plus the iff certificate q_0d-q_1d>R_d-C_d for unavoidable harm. Give exact confidence-region projection and directional numerical-delta inference at ties and structural zero cells. Consumer: KMV's Job Corps/WorkAdvance multilayer Lee analyses and Lee-bounds software. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived the Cartesian diagonal projection by strict-triangular residual transport, the simultaneous binary-outcome completion, and closed-form endpoint ratios. Exact L=2 bounds are [8/25,10/11]; an all-positive L=3 example gives [1/9,10/11]. A 31-arc missing-outcome network has a valid decoder, and 180 independent programs for L=2 through 7, including zero cells, matched the formulas below 1.5e-15. Checked KMV, Possebom--Riva, Kallus, Khandamiryan--Semenova, and generic transport precedents; none supplied the all-layer joint box and contraction. UNRESOLVED BOTTLENECK: Prove conditional bounded-Lipschitz validity of the joint endpoint numerical-delta bootstrap at every fixed observable law, including simultaneous hinge equalities and structural zero cells, using the ambient formula extension and a defined fallback outside the positive-denominator neighborhood. EARLY KILL TEST: Independently enumerate small rational L=3 margins with zero masses and compare both closed-form endpoints against the full 31-arc expanded-state ratio program; any mismatch in the Cartesian projection or simultaneous outcome completion stops the paper. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_multilayer_stayer_harm.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: projected paper_score_ceiling 6.5 < 7.4 and not salvageable within scope; the sound identification kernel lacks the promised boundary-valid inference theorem and meaningful implementation or empirical evidence.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
