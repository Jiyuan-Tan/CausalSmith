---
qid: scm_arbitrarycluster_global_id
spec: v1
topic: "Global sound-and-complete macro-effect identification under arbitrary variable clustering. Input a finite feasible arbitrary cluster causal diagram H with known cluster memberships and finite micro alphabets, together with disjoint macro intervention and outcome sets. Over all recursive semi-Markovian finite SCMs whose acyclic micro ADMG coarsens exactly to H and whose observational law is strictly positive, construct Global-CID: a terminating graph-native algorithm that returns either one guarded arithmetic circuit F(P(V)) for the full P(C_Y | do(C_X=c_x)), valid simultaneously for every compatible law, SCM, and intervention value, or a bounded-cardinality collision certificate containing compatible micro refinements and two strictly positive finite SCMs with the same complete observed law but different target distributions. Prove soundness, completeness, termination, and an explicit elementary complexity/output bound in the finite encoded input. The decisive kernel is a constructive overlap normal-form theorem that either compiles refinement-specific identifying formulas into one circuit on all common-law overlaps or extracts an actual common-law separating pair; generic real quantifier elimination may verify a returned certificate but is not the identification algorithm. After a formula return, derive empirical-multinomial plug-in influence inference on fixed positive-support strata and simultaneous-region propagation across guarded boundaries. Treat Anand-Hripcsak's ALARM medical C-DAG effect analysis and the cyclic lisinopril-stroke grouping as consumers. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A semantic finite-union theorem reduces uniform identification exactly to identification within every compatible micro-refinement plus agreement of refinement-specific answers on common observable-law overlaps. A bounded-support construction preserves the observational law, every intervention distribution, and active graph while using at most 2^n∏d_i+4n²+1 states per latent root. Finite macro-calculus proof skeletons transfer through the three-representative reduction. Exact enumeration verified all 84 refinements of the published positive cyclic example, the bow collision, and a new reversible-chain collision in which both refinements identify individually but disagree at one common strictly positive observational law. The binary unconfounded two-cluster (2,1) family was completely classified. Positivity, singleton-cycle feasibility, active dependencies, cyclic unions, and recent atomic/global completeness claims were checked; no literature collision was found. UNRESOLVED BOTTLENECK: Prove a constructive overlap normal-form theorem that compiles locally identified formulas into one guarded uniform circuit or extracts a common-law separating pair using only finitely bounded graph and symbolic operations. EARLY KILL TEST: Exhaust binary micro-ADMGs with n≤4 and partitions (2,1,1) or (2,2); any uniformly identified input absent from the proposed normal form, unsupported rejection, or need for unrestricted real elimination forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_arbitrarycluster_global_id.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "Uniform identification is defined as one map on the union, and the displayed iff is exactly the set-theoretic gluing of restrictions agreeing on overlaps; make it a definition or retain only a nontrivial constructive consequence."
  - "phi_G is typed as Omega_G to Delta(A_Y), but the target and terminal circuit are indexed by every intervention value c_x; the local-map type must be Delta(A_Y)^(A_X), or c_x must be explicit throughout."
  - "Its consumer says only that it ‘supplies the bounded negative-output subroutine,’ with no named published problem, paper, or applied domain establishing why the support theorem matters independently."
reusable_artifacts:
  - discovery/proto_core.json
  - reviews/angle0_v7.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Seven proposal revisions tried to isolate a constructive overlap-normal-form theorem,
  retain an explicit positive same-law collision, and make the inference supplement total.
  The collision arithmetic survived review, but semantic gluing remained definitional,
  the local functional retained a type mismatch, and comparator/contribution positioning
  failed to converge after the final provenance-safe repair. A future run may reuse the
  collision as a narrower seed, but must rebuild the contribution spine independently.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 32534548
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-06"
---

# scm_arbitrarycluster_global_id / v1 — Failed

**Topic.** Global sound-and-complete macro-effect identification under arbitrary variable clustering. Input a finite feasible arbitrary cluster causal diagram H with known cluster memberships and finite micro alphabets, together with disjoint macro intervention and outcome sets. Over all recursive semi-Markovian finite SCMs whose acyclic micro ADMG coarsens exactly to H and whose observational law is strictly positive, construct Global-CID: a terminating graph-native algorithm that returns either one guarded arithmetic circuit F(P(V)) for the full P(C_Y | do(C_X=c_x)), valid simultaneously for every compatible law, SCM, and intervention value, or a bounded-cardinality collision certificate containing compatible micro refinements and two strictly positive finite SCMs with the same complete observed law but different target distributions. Prove soundness, completeness, termination, and an explicit elementary complexity/output bound in the finite encoded input. The decisive kernel is a constructive overlap normal-form theorem that either compiles refinement-specific identifying formulas into one circuit on all common-law overlaps or extracts an actual common-law separating pair; generic real quantifier elimination may verify a returned certificate but is not the identification algorithm. After a formula return, derive empirical-multinomial plug-in influence inference on fixed positive-support strata and simultaneous-region propagation across guarded boundaries. Treat Anand-Hripcsak's ALARM medical C-DAG effect analysis and the cyclic lisinopril-stroke grouping as consumers. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A semantic finite-union theorem reduces uniform identification exactly to identification within every compatible micro-refinement plus agreement of refinement-specific answers on common observable-law overlaps. A bounded-support construction preserves the observational law, every intervention distribution, and active graph while using at most 2^n∏d_i+4n²+1 states per latent root. Finite macro-calculus proof skeletons transfer through the three-representative reduction. Exact enumeration verified all 84 refinements of the published positive cyclic example, the bow collision, and a new reversible-chain collision in which both refinements identify individually but disagree at one common strictly positive observational law. The binary unconfounded two-cluster (2,1) family was completely classified. Positivity, singleton-cycle feasibility, active dependencies, cyclic unions, and recent atomic/global completeness claims were checked; no literature collision was found. UNRESOLVED BOTTLENECK: Prove a constructive overlap normal-form theorem that compiles locally identified formulas into one guarded uniform circuit or extracts a common-law separating pair using only finitely bounded graph and symbolic operations. EARLY KILL TEST: Exhaust binary micro-ADMGs with n≤4 and partitions (2,1,1) or (2,2); any uniformly identified input absent from the proposed normal form, unsupported rejection, or need for unrestricted real elimination forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_arbitrarycluster_global_id.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 revision-cap exhaustion with recurring definitional/comparator defects and newly exposed contribution/type incoherence after the final authorized root repair.

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
