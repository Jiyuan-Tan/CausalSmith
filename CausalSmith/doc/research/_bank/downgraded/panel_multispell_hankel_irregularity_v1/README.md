---
qid: panel_multispell_hankel_irregularity
spec: v1
topic: "Hankel-history irregularity frontier for heterogeneous carryover effects in continuous reversible fixed-T panels. Under the time-invariant random-coefficient distributed-lag model, a fixed stayer-plus-full-dimensional-mover class, and explicitly bounded density, moment, eligibility and frontier-compatible semialgebraic tube constants, derive each lag's target-active pseudo-inverse leverage tail from the complete joint stratification of Hankel rank loss, maximal-minor contact and target-kernel alignment. Prove the induced regular, critical and irregular matched minimax squared-risk and shortest uniformly honest expected-confidence-length regimes; construct a feasible joint-Gamma trimmed/debiased estimator with geometry-estimated cutoff attaining the upper bound and prove a matching lower bound. Recover finite-support/root-G and scalar slow-mover cases. Use the Gentzkow-Shapiro-Sinkinson/dist_lag_het consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At full column rank the presolve derived H_k^2=e_k'(M'M)^-1e_k, and near a smooth rank-(p-1) target-active point H_k is comparable to target alignment divided by the smallest singular value. It derived generic Hankel-locus codimension T-2K-1; for K=1,T=4 it computed H_0=sqrt(x1^2+x2^2)/|x2^2-x1*x3| and H_1=sqrt(x2^2+x3^2)/|x2^2-x1*x3|, so coarea gives tail exponent one. A tentative truncation-risk balance was also obtained. Checks covered target-inactive rank loss, support separated from singularity, finite treatment support, stayer ineligibility, boundary tangencies, higher-rank intersections, joint alignment vanishing, and Sasaki-Ura/Graham-Powell collisions; none refuted the spine. UNRESOLVED BOTTLENECK: Prove a uniform two-sided tail expansion over the complete boundary-compatible stratification, including logarithmic multiplicities and multi-rank or target-inactive frontiers, and carry its resolved exponent through the matched lower bound and honest-length theorem. EARLY KILL TEST: For K=1,T=5 near history (1,-1,1,-1), prove and numerically verify for both target coordinates that u^2 P(H_k>u) approaches a finite positive constant; a slower frontier contribution or failure of convergence stops the program."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The note does not deliver the advertised matched minimax and honest-confidence-length frontier: thm:matched-frontier proves only an upper bound at the augmented quantity R^dagger and a separate deterministic upper envelope R^star, with no comparison between them and no converse."
  - "The note also proves that its frozen class can have zero minimax risk and confidence length while R^star>0, demonstrating that the current assumptions cannot support the desired lower bounds."
  - "The proposed geometry-estimated cutoff is only a named Goldenshluger--Lepski handle, with no comparison statistic, threshold, or interval critical value; the core itself says no unique map or adaptation/coverage theorem is delivered."
  - "The selector-distance bound is not reproduced: the normal-link certificate does not make a ray from every deep-tail point reach the retained anchor set with the required displacement control."
reusable_artifacts:
  - "discovery/core.json — resolution-invariant target-specific Hankel/local-zeta tail atlas and fixed-signature class."
  - "discovery/writeup.tex — full derivation note, source bridge, scalar reduction, and K=1,T=5 critical witness."
  - "discovery/solve_lem_published_reduced_form_scope.json — audited bridge to the published reduced-form experiment."
  - "orchestrator/d0_round1_fitting_literature_codex.txt — literature audit motivating the minimax-linear/Riesz correction and documenting the missing occupancy/transport theorem."
  - "orchestrator/d05_terminal_below_floor_codex.txt — terminal novelty/maximality adjudication with the non-laundering boundary."
seeds_burned:
  - index: 0
    one_liner: "seed:hankel-tail-atlas"
    reason: "The sole same-topic angle converged to a specialized subfield tail-atlas result; restoring field-tier matched minimax and honest inference requires a new rich-subclass theorem program, not a bounded repair."
proof_attempt_summary: |
  The run derived a resolution-invariant pseudo-inverse/local-zeta tail atlas, repaired the scalar and critical Hankel benchmarks, and constructed a total minimax-linear estimator attaining an exposed augmented R^dagger risk bound on a strict fixed-signature reduced-form subclass. The field-tier program collapsed because no lawful argument compared the empirical extrapolation modulus to the deterministic R^star phase, no same-signature converse or class-wide honest interval was proved, and the named adaptive cutoff remained unspecified. A future re-raise would require a separately scoped primitive rich subclass together with explicit transport, estimator, interval, and multiscale lower-bound theorems; assuming those properties would encode the missing crux.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 75011611
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-02"
---

# panel_multispell_hankel_irregularity / v1 — Downgraded

**Topic.** Hankel-history irregularity frontier for heterogeneous carryover effects in continuous reversible fixed-T panels. Under the time-invariant random-coefficient distributed-lag model, a fixed stayer-plus-full-dimensional-mover class, and explicitly bounded density, moment, eligibility and frontier-compatible semialgebraic tube constants, derive each lag's target-active pseudo-inverse leverage tail from the complete joint stratification of Hankel rank loss, maximal-minor contact and target-kernel alignment. Prove the induced regular, critical and irregular matched minimax squared-risk and shortest uniformly honest expected-confidence-length regimes; construct a feasible joint-Gamma trimmed/debiased estimator with geometry-estimated cutoff attaining the upper bound and prove a matching lower bound. Recover finite-support/root-G and scalar slow-mover cases. Use the Gentzkow-Shapiro-Sinkinson/dist_lag_het consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: At full column rank the presolve derived H_k^2=e_k'(M'M)^-1e_k, and near a smooth rank-(p-1) target-active point H_k is comparable to target alignment divided by the smallest singular value. It derived generic Hankel-locus codimension T-2K-1; for K=1,T=4 it computed H_0=sqrt(x1^2+x2^2)/|x2^2-x1*x3| and H_1=sqrt(x2^2+x3^2)/|x2^2-x1*x3|, so coarea gives tail exponent one. A tentative truncation-risk balance was also obtained. Checks covered target-inactive rank loss, support separated from singularity, finite treatment support, stayer ineligibility, boundary tangencies, higher-rank intersections, joint alignment vanishing, and Sasaki-Ura/Graham-Powell collisions; none refuted the spine. UNRESOLVED BOTTLENECK: Prove a uniform two-sided tail expansion over the complete boundary-compatible stratification, including logarithmic multiplicities and multi-rank or target-inactive frontiers, and carry its resolved exponent through the matched lower bound and honest-length theorem. EARLY KILL TEST: For K=1,T=5 near history (1,-1,1,-1), prove and numerically verify for both target coordinates that u^2 P(H_k>u) approaches a finite positive constant; a slower frontier contribution or failure of convergence stops the program.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The delivered result is a nontrivial but specialized pseudo-inverse/local-zeta tail characterization and augmented-modulus upper bound, not the advertised matched minimax and honest-confidence-length frontier.

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
