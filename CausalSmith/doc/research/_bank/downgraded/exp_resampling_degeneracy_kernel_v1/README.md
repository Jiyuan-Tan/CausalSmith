---
qid: exp_resampling_degeneracy_kernel
spec: v1
topic: "Universal resampling-degeneracy certificates and power-optimal exact kernels for network exposure-effect quantiles. For a finite positive design law π on Ω and a directed legal-support relation L, let K be a row-stochastic kernel supported on L and define d_K(A) as the minimum over orderings σ of nonempty A of the maximum prefix mass K(σ_j,{σ_1,…,σ_j}). Prove that upper-tail p-values from K are super-uniform for every real score vector iff d_K(A)≥π(A) for every nonempty A; derive the peeling/core equivalence, O(|Ω|2^|Ω|) recursion and violated-subset certificate, exact union-of-polyhedra description, and a certified mixed-integer optimizer for power against a prespecified alternative catalogue. Within predeclared imputable network-exposure fibers, compute worst-case p-values over sharp schedules having at most r direct effects above c and invert the nested family into exact simultaneous lower bounds for exposure-specific effect quantiles. Credit Caughey–Dafoe–Li–Miratrix for bounded-null quantile RI, Owusu and Hoshino for network conditional tests, Zhang–Zhao for partition-sufficient conditional randomization, and Ramdas et al. for arbitrary-permutation constructions; use Owusu's Cai–de Janvry–Sadoulet weather-insurance reanalysis as the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the universal-validity iff by ordering rejection sets and constructing a strict score order from every violating subset; it derived d_K(A)=min_i max{K(i,A),d_K(A\\{i})}, the equivalent nonempty-core certificate, exact O(m2^m) separation, and a finite disjunctive MILP. It solved the uniform three-state cyclic nonpartition kernel and proved composite bounded-null validity using the supremum over null-consistent sharp schedules. Threshold equality, ties, zero-mass states, missing self-loops, outcome adaptation, tiny fibers, naive Monte Carlo, generic disjunctive collapse, and Ramdas et al. were checked; no collision was found. UNRESOLVED BOTTLENECK: For a fixed network rank statistic and legal exposure fiber, prove a terminating exact weak-order, LP, or MILP reduction of the worst-case composite-null p-value over schedules with at most r effects above c, including the simultaneous quantile-projection identity. EARLY KILL TEST: On one actual Cai/Owusu exposure fiber at α=0.05, compare the globally optimized kernel with every partition kernel and compute one bounded-null quantile p-value exactly; stop or pivot if legal support forces partitions, no strict certified power gain exists, or exact worst-case computation changes the target. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_resampling_degeneracy_kernel.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The universal-validity iff and exact finite recursion are sound, but the promised field-level network application and strict comparator gain do not reach the field novelty threshold; one redundant unconsumed wrapper remains ballast."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The “power-optimal” theorem proves optimality only for a prespecified finite score catalogue and level, not for effect-quantile inference generally or for an actual Cai–Owusu exposure fiber."
  - "Strict power improvement is demonstrated only by constructed supports—most notably the three-cycle at level 2/3 and the asymmetric-isolate construction at alpha equal to one state’s mass—so the note supplies no evidence of useful gains at conventional levels."
  - "The network result delivers an exact but exponentially large weak-order enumeration and algebraic inversion, without the promised empirical fiber computation needed to establish practical relevance or reproducibility."
  - "DELETE this unconsumed wrapper theorem: it merely restates thm:exact-network-schedule-reduction and prop:no-interference-reduction, so the headline can be carried by those substantive nodes (and prose) without a second numbered claim."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_universal_validity_iff.tex
  - discovery/solve_thm_catalogue_power_optimizer.tex
  - discovery/solve_thm_partition_strict_inclusion.tex
  - discovery/solve_thm_composite_null_validity.tex
  - discovery/solve_oeq_network_schedule_reduction.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the finite universal-validity characterization, its subset recursion and certificates, catalogue-level power optimization, and an exact finite network schedule reduction; the D0.5 math referee passed after both citation leaves were verified and the requested evaluation-map and related-work repairs landed. The field-tier promise collapsed because power improvement was shown only on constructed supports and no conventional-level Cai–Owusu exposure-fiber computation established practical gain; the contribution panel therefore capped the paper at subfield (6.6 versus the 7.4 field threshold). A future re-raise should reuse the listed theorem graph and solver artifacts, delete the redundant wrapper theorem, and supply the prespecified real-fiber computation with reproducible strict partition-kernel power-gap certificates.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 23561696
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 23561696
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_resampling_degeneracy_kernel / v1 — Downgraded

**Topic.** Universal resampling-degeneracy certificates and power-optimal exact kernels for network exposure-effect quantiles. For a finite positive design law π on Ω and a directed legal-support relation L, let K be a row-stochastic kernel supported on L and define d_K(A) as the minimum over orderings σ of nonempty A of the maximum prefix mass K(σ_j,{σ_1,…,σ_j}). Prove that upper-tail p-values from K are super-uniform for every real score vector iff d_K(A)≥π(A) for every nonempty A; derive the peeling/core equivalence, O(|Ω|2^|Ω|) recursion and violated-subset certificate, exact union-of-polyhedra description, and a certified mixed-integer optimizer for power against a prespecified alternative catalogue. Within predeclared imputable network-exposure fibers, compute worst-case p-values over sharp schedules having at most r direct effects above c and invert the nested family into exact simultaneous lower bounds for exposure-specific effect quantiles. Credit Caughey–Dafoe–Li–Miratrix for bounded-null quantile RI, Owusu and Hoshino for network conditional tests, Zhang–Zhao for partition-sufficient conditional randomization, and Ramdas et al. for arbitrary-permutation constructions; use Owusu's Cai–de Janvry–Sadoulet weather-insurance reanalysis as the consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the universal-validity iff by ordering rejection sets and constructing a strict score order from every violating subset; it derived d_K(A)=min_i max{K(i,A),d_K(A\{i})}, the equivalent nonempty-core certificate, exact O(m2^m) separation, and a finite disjunctive MILP. It solved the uniform three-state cyclic nonpartition kernel and proved composite bounded-null validity using the supremum over null-consistent sharp schedules. Threshold equality, ties, zero-mass states, missing self-loops, outcome adaptation, tiny fibers, naive Monte Carlo, generic disjunctive collapse, and Ramdas et al. were checked; no collision was found. UNRESOLVED BOTTLENECK: For a fixed network rank statistic and legal exposure fiber, prove a terminating exact weak-order, LP, or MILP reduction of the worst-case composite-null p-value over schedules with at most r effects above c, including the simultaneous quantile-projection identity. EARLY KILL TEST: On one actual Cai/Owusu exposure fiber at α=0.05, compare the globally optimized kernel with every partition kernel and compute one bounded-null quantile p-value exactly; stop or pivot if legal support forces partitions, no strict certified power gain exists, or exact worst-case computation changes the target. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_resampling_degeneracy_kernel.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 math referee passed with verified citations and both mandated repairs, but the contribution panel assessed paper_score_ceiling 6.6 below the field threshold 7.4.

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
