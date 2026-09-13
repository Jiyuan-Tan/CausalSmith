---
qid: scm_selected_pag_conditional_hedge
spec: v1
topic: "Denominator-locked completeness for conditional causal effects in selected COPAGs. Fix a finite input-free COPAG over binary observed variables representing Chen--Mooij's positive discrete SCM class with arbitrary latent and selection variables, disjoint Y,X,C, and positive selected conditioning strata. Define Branch-sCIDP to enumerate every reachable role state using the source algorithm's current bucket intersections and valid Rule-2 exchanges, run sIDP on each terminal joint P(Y,Cbar | do(Xbar),S=1), and normalize any successful functional. Prove Branch-sCIDP succeeds iff P(Y | do(X),C,S=1) is identified; otherwise construct a denominator-locked selected conditional hedge: a represented MAG/sADMG and terminal-joint forest plus explicit positive rational binary SCMs with the same full selected observational law and the same positive conditioning denominator but different joint numerators. Give a shared-cache O(3^n poly(n)+output) formula-or-certificate algorithm and verification polynomial in graph plus expanded rational certificate size. Consumer: extend PAGId from no-selection conditional identification to formula-or-checkable-failure output for selected-cohort FCI/PAG analyses. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Varying one rational interior mechanism makes all fixed-regime masses affine; equality of the normalized selected observational law and conditioning denominator becomes a homogeneous rational system Av=0, while numerator disagreement is a row b outside row(A), so a locked witness exists exactly when rank([A;b]) exceeds rank(A). Exact enumeration produced a selected binary bow with identical observational laws, denominator 1/2, numerators 9/25 versus 7/23, and conditional effects 18/25 versus 14/23. It also verified both four-cycle graph realizations and exact cancellation of their conditional ratios. Checks corrected whole-bucket moves to role intersections, separated the independent-root cancellation model from the actual hedge realization, tested positivity and boundary cases, and found no current primary-source collision. These are derived special cases, not the complete converse. UNRESOLVED BOTTLENECK: Prove that failure at every reachable terminal state forces a represented residual forest from which one can construct positive rational binary mechanisms sharing the selected observational law and conditioning denominator while separating the numerator, with the advertised output-sensitive synthesis bound. EARLY KILL TEST: Exhaustively enumerate input-free COPAGs on at most four observed vertices and their exact Rule-2 role-state graphs; any graph-valid identifying formula for an all-branches-fail conditional target refutes completeness, while a proof that all compatible rational binary pairs at a failing graph violate denominator locking refutes the certificate coordinate. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_selected_pag_conditional_hedge.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The advertised iff formula-or-certificate theorem requires proving that every all-branches-fail role graph yields a represented denominator-locked rational tangent/certificate pair with the claimed output-sensitive synthesis bound; the delivered affine compiler handles only supplied families and traces."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "AllFail is explicitly given no nonidentification implication, and the graph-to-lock step remains open."
  - "The affine compiler only converts a supplied represented family, legal trace, forest pair, and successful rank condition into a certificate; it does not show that any of these inputs exist after Branch-sCIDP fails."
  - "The selection-equalizer lift and connected binary example establish exact locked witnesses on specially constructed graphs, not certificates for arbitrary failing input COPAGs or the fixed target under analysis."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_affine_lock_compiler.json
  - discovery/solve_tex/solve_thm_affine_lock_compiler.tex
  - discovery/solve_lem_selection_equalizer_lift.json
  - discovery/solve_tex/solve_lem_selection_equalizer_lift.tex
  - discovery/solve_prop_informative_lock_witness.json
  - discovery/solve_tex/solve_prop_informative_lock_witness.tex
  - discovery/solve_thm_branch_soundness.json
  - discovery/solve_tex/solve_thm_branch_soundness.tex
seeds_burned: []
proof_attempt_summary: |
  The run exhaustively developed Branch-sCIDP soundness, a source-faithful
  no-selection reduction, a selection-equalizer lift, an informative rational
  witness, and a reachability-qualified affine rank compiler. The compiler is
  sound for a supplied represented affine family and legal role trace, but the
  attempted completeness argument never derived those inputs from an arbitrary
  all-branches-fail COPAG. The remaining graph-to-lock implication and its
  output-sensitive synthesis bound are the unproved research barrier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 50362239
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 50362239
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# scm_selected_pag_conditional_hedge / v1 — Downgraded

**Topic.** Denominator-locked completeness for conditional causal effects in selected COPAGs. Fix a finite input-free COPAG over binary observed variables representing Chen--Mooij's positive discrete SCM class with arbitrary latent and selection variables, disjoint Y,X,C, and positive selected conditioning strata. Define Branch-sCIDP to enumerate every reachable role state using the source algorithm's current bucket intersections and valid Rule-2 exchanges, run sIDP on each terminal joint P(Y,Cbar | do(Xbar),S=1), and normalize any successful functional. Prove Branch-sCIDP succeeds iff P(Y | do(X),C,S=1) is identified; otherwise construct a denominator-locked selected conditional hedge: a represented MAG/sADMG and terminal-joint forest plus explicit positive rational binary SCMs with the same full selected observational law and the same positive conditioning denominator but different joint numerators. Give a shared-cache O(3^n poly(n)+output) formula-or-certificate algorithm and verification polynomial in graph plus expanded rational certificate size. Consumer: extend PAGId from no-selection conditional identification to formula-or-checkable-failure output for selected-cohort FCI/PAG analyses. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Varying one rational interior mechanism makes all fixed-regime masses affine; equality of the normalized selected observational law and conditioning denominator becomes a homogeneous rational system Av=0, while numerator disagreement is a row b outside row(A), so a locked witness exists exactly when rank([A;b]) exceeds rank(A). Exact enumeration produced a selected binary bow with identical observational laws, denominator 1/2, numerators 9/25 versus 7/23, and conditional effects 18/25 versus 14/23. It also verified both four-cycle graph realizations and exact cancellation of their conditional ratios. Checks corrected whole-bucket moves to role intersections, separated the independent-root cancellation model from the actual hedge realization, tested positivity and boundary cases, and found no current primary-source collision. These are derived special cases, not the complete converse. UNRESOLVED BOTTLENECK: Prove that failure at every reachable terminal state forces a represented residual forest from which one can construct positive rational binary mechanisms sharing the selected observational law and conditioning denominator while separating the numerator, with the advertised output-sensitive synthesis bound. EARLY KILL TEST: Exhaustively enumerate input-free COPAGs on at most four observed vertices and their exact Rule-2 role-state graphs; any graph-valid identifying formula for an all-branches-fail conditional target refutes completeness, while a proof that all compatible rational binary pairs at a failing graph violate denominator locking refutes the certificate coordinate. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_selected_pag_conditional_hedge.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Graded incremental at ceiling 5.4 below the field gate 7.4 after all bounded repairs; arbitrary AllFail-to-denominator-lock synthesis remains open.

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
