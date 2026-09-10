---
qid: pid_commonentropy_benefit_harm_contact
spec: v1
topic: "Exact common-entropy sensitivity for the joint benefit-harm plane with binary treatment and outcome. Define the sharp set Theta_kappa(P) of B=P(Y0=0,Y1=1) and H=P(Y0=1,Y1=0) over factual-compatible latent-factor SCMs satisfying H(U)<=kappa. Prove constructive sufficiency and the exact three-state latent reduction, including an explicit law showing that three states are sometimes necessary for the full image; prove (0,0) is feasible iff G(A;Y)<=kappa and that this origin face admits a two-state entropy minimizer, while I(A;Y)<=kappa is only a necessary relaxation; derive, under treatment positivity where arm risks are used, the zero-budget Frechet segment, the high-budget rectangle, and star-shapedness/connectedness at every intermediate budget. Prove conservative whole-set coverage by exact multinomial inversion. Retain as explicit open strengthening questions a rank-free terminating BH-CERT with nested inner/outer Hausdorff-certified complexes, exact included-cell SCM witness sections, and checkable excluded-cell separation certificates, together with regular-versus-entropy-contact Hausdorff inference; use causaloptim only as a computational comparator, not as a claimed extension. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the balanced .9/.1 observed channel, I(A;Y)=.368064 while G(A;Y)=h(4/9)=.686962, so kappa=.5 creates a strict estimand-level false inclusion of no individual effect. Under treatment positivity, at kappa=0 the set is the Frechet line B-H=mu1-mu0; for kappa>=H(A) it is the unrestricted factual rectangle. Replacing each response distribution by a common convex mixture toward one no-confounding response law preserves factual cells and entropy, giving a star-shaped exact set. UNRESOLVED BOTTLENECK: Prove BH-CERT terminates with two-sided Hausdorff enclosures and exact causal witnesses at singular feasible factors with zero latent weights or active entropy equality, without an interval-Newton rank assumption. EARLY KILL TEST: On the balanced .9/.1 law, require one support-at-most-three certified run that finitely separates the origin below G(A;Y) and produces convergent inner/outer complexes exactly at kappa=G(A;Y); pivot if zero-weight/contact boxes cannot be closed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The framing correctly leaves BH-CERT and contact inference open, but the delivered ‘exact joint set’ is an exact representation rather than an operational solution for intermediate entropy budgets."
  - "Replace the non-effective compactness argument with the claimed finite certification procedure, first closing the balanced contact instance and then extending the construction uniformly over the three-state program. The proof must handle zero latent masses and active entropy equality without a local rank assumption."
  - "The requested uniformly terminating exact algorithm quantifies over arbitrary real inputs without an input/oracle model, certificate language, exact-witness representation, or singular equality decision semantics."
reusable_artifacts:
  - discovery/core.json
  - discovery/d0_working.json
  - discovery/writeup.tex
  - discovery/proof_archive/index.jsonl
  - reviews/review_math.json
  - reviews/review_rubric.json
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The D stage established a positivity-free exact three-state representation, a sharp
  three-state necessity witness, a two-state no-effect face, the exact common-entropy
  origin threshold, strict insufficiency of its observed-MI relaxation, and conservative
  whole-set coverage. Math and decision reviews passed, but the field-tier general review
  required a rank-free terminating BH-CERT at zero weights and entropy contact. That
  effective-certification theorem remains open because the demanded algorithm did not
  specify finite inputs, certificate semantics, or exact witness representation.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 62074903
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# pid_commonentropy_benefit_harm_contact / v1 — Downgraded

**Topic.** Exact common-entropy sensitivity for the joint benefit-harm plane with binary treatment and outcome. Define the sharp set Theta_kappa(P) of B=P(Y0=0,Y1=1) and H=P(Y0=1,Y1=0) over factual-compatible latent-factor SCMs satisfying H(U)<=kappa. Prove constructive sufficiency and the exact three-state latent reduction, including an explicit law showing that three states are sometimes necessary for the full image; prove (0,0) is feasible iff G(A;Y)<=kappa and that this origin face admits a two-state entropy minimizer, while I(A;Y)<=kappa is only a necessary relaxation; derive, under treatment positivity where arm risks are used, the zero-budget Frechet segment, the high-budget rectangle, and star-shapedness/connectedness at every intermediate budget. Prove conservative whole-set coverage by exact multinomial inversion. Retain as explicit open strengthening questions a rank-free terminating BH-CERT with nested inner/outer Hausdorff-certified complexes, exact included-cell SCM witness sections, and checkable excluded-cell separation certificates, together with regular-versus-entropy-contact Hausdorff inference; use causaloptim only as a computational comparator, not as a claimed extension. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For the balanced .9/.1 observed channel, I(A;Y)=.368064 while G(A;Y)=h(4/9)=.686962, so kappa=.5 creates a strict estimand-level false inclusion of no individual effect. Under treatment positivity, at kappa=0 the set is the Frechet line B-H=mu1-mu0; for kappa>=H(A) it is the unrestricted factual rectangle. Replacing each response distribution by a common convex mixture toward one no-confounding response law preserves factual cells and entropy, giving a star-shaped exact set. UNRESOLVED BOTTLENECK: Prove BH-CERT terminates with two-sided Hausdorff enclosures and exact causal witnesses at singular feasible factors with zero latent weights or active entropy equality, without an interval-Newton rank assumption. EARLY KILL TEST: On the balanced .9/.1 law, require one support-at-most-three certified run that finitely separates the origin below G(A;Y) and produces convergent inner/outer complexes exactly at kappa=G(A;Y); pivot if zero-weight/contact boxes cannot be closed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** General referee: the delivered exact joint set is an exact representation rather than an operational solution for intermediate entropy budgets; the only field lift is the still-open, underspecified rank-free BH-CERT theorem.

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
