---
qid: eid_stable_orbit_counting
spec: v1
topic: "Stable-orbit counting complexity for cyclic linear non-Gaussian mechanisms. For square fully observed cyclic LiNG SEMs identified up to normalized ICA row assignments, let N_stab(W) count every admissible normalized row assignment whose induced coefficient matrix is Schur stable. Prove that for every simple n-vertex graph G an explicit rational 3n-variable construction W_G, with epsilon_n=1/[2^40(n+1)^4], has its complete stable assignment orbit in bijection with the independent sets of G; derive #P-completeness under polynomial-time Turing reductions and no FPRAS unless RP=NP on the stated bounded-degree images, contrasted with the permanent FPRAS for unfiltered assignments. Prove exact SCC factorization and an output-sensitive local enumeration algorithm. Add pointwise orbit-honest count inference by inverting a symmetrized FOBI confidence region, without uniform graph-support claims. Consumer: the matching-frequency sampler and adaptive intervention choice of Sharifian, Salehkaleybar, and Kiyavash must condition on stability when equilibrium stability is imposed. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact elimination gives an analytic critical-root coordinate with perturbation bounded by 4gn^2; explicit radial margins separate independent from non-independent switch sets, while resolvent contours exclude root-third-coordinate swaps and root-only cycles. Complete rational enumeration at the committed epsilon rule matched independent-set counts for K2, P5, C5, K1,4, and K5, with stable counts 3, 13, 11, 17, and 6 and no extra or missing assignment. Counting/AP conventions, polynomial bit length, error-law closure, SCC factorization, and the consumer mapping survived destructive checks. UNRESOLVED BOTTLENECK: Independently verify the graph-uniform analytic determinant homotopy, especially multiplicity preservation and absence of poles after the Schur complement and local inverse map. EARLY KILL TEST: Audit the exact pencil, inverse-coordinate equations, 4gn^2 bound, and negative-mode homotopy, then rerun all five exact complete-orbit checks; any sign error, hidden pole, lost polynomial-bit margin, or unintended stable permutation kills the realization. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_stable_orbit_counting.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The sharp bounded-degree phase diagram is proved only for fixed-labelled matrices manufactured by the reduction, not for a natural bounded-degree class of cyclic LiNG mechanisms, so it does not establish a general sparsity frontier."
  - "The consumer claim is correspondingly limited: the results show worst-case difficulty of stability-conditioned matching counts, but do not analyze the distribution of instances produced by the cited intervention method or provide a usable approximation scheme for its stable frequencies."
  - "The FOBI confidence image supplies pointwise coverage but is not accompanied by a finite computational procedure for evaluating the image over its continuum of matrices and may be highly noninformative near stability boundaries, which limits its practical evidentiary value and the projected journal score."
reusable_artifacts:
  - path: discovery/core.json
    kind: witness
    one_line: "Complete rational 3n stable-orbit realization, sharp gadget-image complexity elbows, and one-SCC hardness package."
  - path: discovery/solve_thm_scc_factorization_real.tex
    kind: operator
    one_line: "Exact admissible/stable SCC product factorization for arbitrary real equation matrices."
  - path: discovery/solve_thm_pointwise_count_inference.tex
    kind: other
    one_line: "Pointwise signed-orbit FOBI confidence-image construction and coverage argument."
seeds_burned: []
proof_attempt_summary: |
  Discovery completed a coherent mathematical derivation of the rational 3n reduction, spectral homotopy certificate, exact and approximate counting separations, SCC factorization, exact rational enumeration, and pointwise FOBI inference. The result missed the field floor because its sharp positive frontier is confined to fixed-labelled gadget images, its consumer relevance is worst-case, and its confidence-image inversion lacks a computationally useful evaluation theorem. Formalization was not attempted because the operator's D→F freeze was active; a future re-raise needs a new natural-class, consumer-linked average-case, or computational-inference kernel rather than panel-only cleanup.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 30133155
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 30133155
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_stable_orbit_counting / v1 — Downgraded

**Topic.** Stable-orbit counting complexity for cyclic linear non-Gaussian mechanisms. For square fully observed cyclic LiNG SEMs identified up to normalized ICA row assignments, let N_stab(W) count every admissible normalized row assignment whose induced coefficient matrix is Schur stable. Prove that for every simple n-vertex graph G an explicit rational 3n-variable construction W_G, with epsilon_n=1/[2^40(n+1)^4], has its complete stable assignment orbit in bijection with the independent sets of G; derive #P-completeness under polynomial-time Turing reductions and no FPRAS unless RP=NP on the stated bounded-degree images, contrasted with the permanent FPRAS for unfiltered assignments. Prove exact SCC factorization and an output-sensitive local enumeration algorithm. Add pointwise orbit-honest count inference by inverting a symmetrized FOBI confidence region, without uniform graph-support claims. Consumer: the matching-frequency sampler and adaptive intervention choice of Sharifian, Salehkaleybar, and Kiyavash must condition on stability when equilibrium stability is imposed. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact elimination gives an analytic critical-root coordinate with perturbation bounded by 4gn^2; explicit radial margins separate independent from non-independent switch sets, while resolvent contours exclude root-third-coordinate swaps and root-only cycles. Complete rational enumeration at the committed epsilon rule matched independent-set counts for K2, P5, C5, K1,4, and K5, with stable counts 3, 13, 11, 17, and 6 and no extra or missing assignment. Counting/AP conventions, polynomial bit length, error-law closure, SCC factorization, and the consumer mapping survived destructive checks. UNRESOLVED BOTTLENECK: Independently verify the graph-uniform analytic determinant homotopy, especially multiplicity preservation and absence of poles after the Schur complement and local inverse map. EARLY KILL TEST: Audit the exact pencil, inverse-coordinate equations, 4gn^2 bound, and negative-mode homotopy, then rerun all five exact complete-orbit checks; any sign error, hidden pole, lost polynomial-bit margin, or unintended stable permutation kills the realization. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_stable_orbit_counting.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=subfield < floor=field and NOT salvageable in scope; the four panel findings are repairable as hygiene, but repairing them does not change the 7.2 novelty ceiling.

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
