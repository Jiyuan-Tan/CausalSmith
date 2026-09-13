---
qid: panel_closegroup_weaksep_honest_frontier
spec: v1
topic: "Weak-separation honest-inference frontier for exact close-comparison panels. With finitely many treated stacks and candidate donors, iid within-group micro-panels, and a joint asymptotically linear pre-equality-score/post-mean vector, define the nonempty close set by exact zero score and require every close donor to imply the same ATT. Construct simultaneous joint donor-label/ATT Gaussian inversion with within-label outcome uncertainty. Prove uniform coverage, oracle root-n diameter under fixed separation, and a matching positive local-minimax expected-diameter frontier over root-n-separated triangular arrays, including multiple-close-donor faces and shared-control covariance. Reanalyse the CMS State Innovation Models comparison-state claims workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Profiling each joint Wald ellipsoid yields an explicit labelwise interval centered at the post-effect estimate corrected by its score regression; a Gaussian maximum critical value makes the hull cover every true label simultaneously. On the unscaled weak-risk scale, post-mean noise vanishes and the problem reduces to a finite Gaussian label-confidence experiment on a union of coordinate hyperplanes. For two donors with identity score covariance, switches h=(0,c) and h=(c,0), effect gap Delta, and total-variation distance 2 Phi(c/sqrt(2))-1 force honest expected diameter at least Delta times [1-2 alpha-TV]_+; c=1, Delta=0.4, alpha=0.05 gives about 0.1518. Fixed separation eliminates false labels and restores the oracle root-n hull. UNRESOLVED BOTTLENECK: Prove uniform Le Cam minimax equivalence for the nonclosed triangular union and show that covariance-estimated simultaneous inversion attains the finite-Gaussian worst expected-diameter functional, including multiple-zero-label faces. EARLY KILL TEST: Solve the two-donor identity-covariance Gaussian decision problem over 0<c<=H analytically or by a fine-grid linear program and compare its exact minimax diameter with the proposed maximum-critical hull; a persistent sharpness gap not repairable within joint inversion should pivot or stop the run."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "A faithful result would require a new sqrt(n)-scaled noisy local experiment, changing the risk scale, parameter space, least-favorable witnesses, attaining rule, and exact constant."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The exact value solves a bounded-spread score-only experiment with b observed noiselessly, not the proposal's matching local-minimax expected-diameter frontier for panel triangular arrays; the stated transfer node expressly leaves that loss and coverage transfer open."
  - "The advertised weak-separation panel frontier is not proved over the panel triangular-array experiment: the exact minimax value concerns a repaired experiment that observes b without noise and imposes a bounded effect spread."
  - "Hence on the advertised root-n-local score class, all effect contrasts satisfy max_k|b_{k,n}-tau_n|=O(n^(-1/2)). They cannot converge to the fixed, unequally spaced b* grid used by the lower bound of thm:score-face-general-minimax-exact."
reusable_artifacts:
  - "discovery/core.json — sound transport, covariance-clipping, pilot-adaptive coverage, and two-face Gaussian components remain useful after separating them from the failed frontier claim."
  - "discovery/writeup.tex — contains the score-only experiment and the exact point where the noiseless-b replacement departs from the panel experiment."
  - "orchestrator/decision_log.jsonl — preserves the D0 maximality consults, repair directives, and terminal validity receipts."
seeds_burned: []
proof_attempt_summary: |
  D0 proved a totalized simultaneous hull, a pilot-screened oracle construction,
  and exact two-face Gaussian bounds, then repaired the finite frontier by observing
  b noiselessly. D0.5 and the independent validity gate showed that this repair
  launders the advertised panel problem: additive transport and bounded covariance
  make every effect contrast O(n^(-1/2)) under root-n-local score separation, so the
  fixed positive-spread least-favorable grid is inadmissible. A future topic may study
  the genuinely noisy sqrt(n)-scaled local experiment, but it needs a new proposal.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 41290839
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# panel_closegroup_weaksep_honest_frontier / v1 — Failed

**Topic.** Weak-separation honest-inference frontier for exact close-comparison panels. With finitely many treated stacks and candidate donors, iid within-group micro-panels, and a joint asymptotically linear pre-equality-score/post-mean vector, define the nonempty close set by exact zero score and require every close donor to imply the same ATT. Construct simultaneous joint donor-label/ATT Gaussian inversion with within-label outcome uncertainty. Prove uniform coverage, oracle root-n diameter under fixed separation, and a matching positive local-minimax expected-diameter frontier over root-n-separated triangular arrays, including multiple-close-donor faces and shared-control covariance. Reanalyse the CMS State Innovation Models comparison-state claims workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Profiling each joint Wald ellipsoid yields an explicit labelwise interval centered at the post-effect estimate corrected by its score regression; a Gaussian maximum critical value makes the hull cover every true label simultaneously. On the unscaled weak-risk scale, post-mean noise vanishes and the problem reduces to a finite Gaussian label-confidence experiment on a union of coordinate hyperplanes. For two donors with identity score covariance, switches h=(0,c) and h=(c,0), effect gap Delta, and total-variation distance 2 Phi(c/sqrt(2))-1 force honest expected diameter at least Delta times [1-2 alpha-TV]_+; c=1, Delta=0.4, alpha=0.05 gives about 0.1518. Fixed separation eliminates false labels and restores the oracle root-n hull. UNRESOLVED BOTTLENECK: Prove uniform Le Cam minimax equivalence for the nonclosed triangular union and show that covariance-estimated simultaneous inversion attains the finite-Gaussian worst expected-diameter functional, including multiple-zero-label faces. EARLY KILL TEST: Solve the two-donor identity-covariance Gaussian decision problem over 0<c<=H analytically or by a fine-grid linear program and compare its exact minimax diameter with the proposed maximum-critical hull; a persistent sharpness gap not repairable within joint inversion should pivot or stop the run.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The advertised weak-separation panel frontier is not proved: its exact value uses a repaired score-only experiment with b observed noiselessly, while admissible panel effect contrasts vanish at O(n^-1/2).

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The reusable positive results should be lifted only after restating the target on
the noisy sqrt(n)-scaled local experiment. They do not establish a positive
unscaled expected-diameter frontier for the original panel triangular arrays.
