---
qid: scm_partialdiff_uniform_singledoor
spec: v1
topic: "Boundary-honest SCM partial identification and inference for environment-specific direct effects from an LDiffPC equality/sepset ledger. For two positive diff-faithful linear-Gaussian acyclic SCMs with baseline-parent modular interventions, invariant innovation variances, and a common order, define the exact compatible-completion effect fiber Ψ(s); prove its finite semialgebraic branch representation and exact finite-sample coverage of the fixed direct-effect triple by projecting a paired Wishart covariance region through Ψ. Derive Fell boundary random-set limits using tangent-cone regularity and derived rational-branch smoothness, an exact p=3 collider singleton audit, and every-p≥3 same-law noncontraction and infinite global worst-case expected-diameter converses, with converse-only transfer to the full Bystrova–Devijver anchor class and finite attainment of each bounded Gaussian tangent minimax problem. On a separately declared coefficient/covariance-bounded Gaussian subclass, establish exact projected-Wishart coverage and explicit finite-sample constant-factor minimax expected-diameter bounds without separation or beta-min assumptions. Make no componentwise uniform-single-door iff, fixed-treewidth algorithm, rejection-certificate, non-Gaussian exact positive-inference, or exact minimax-optimality claim."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The requested axiom-free API depends on foundational real algebraic geometry absent from both Mathlib and Causalean: real-closed-field quantifier elimination, semialgebraic cell decomposition and dimension theory, finite Whitney/Nash stratification, and semialgebraic Sard."
  - "The paper-specific residual is the complete LDiffPC algorithm plus its Definition 2–4 diff-separation semantics and Theorem 1 skeleton/orientation proof. Further work is therefore an implementation of the cited 2026 paper, not a small bridge."
  - "Closing only downstream consequences cannot remove their foundational dependency."
reusable_artifacts:
  - "discovery/core.json — final 26-node field-tier dependency core"
  - "discovery/writeup.tex — discharged mathematical derivation"
  - "discovery/d05_acceptance_receipt.json — clean field-tier PASS receipt"
  - "discovery/proto_core_angle0_rejected.json — preserved record of the rejected universal-iff angle"
  - "discovery/certificates/a4_common_fiber_v4.json — negative evidence showing why Angle 0 was retired"
  - "formalization/plan.json — formalization dependency and overflow map"
seeds_burned:
  - index: 0
    one_liner: "Componentwise generic direct-effect identification iff the LDiffPC ledger forces zero or admits a completion-uniform single-door set."
    reason: "Angle 0's claimed exhaustive p=4 certificate contained only one explicit row and one intensional protocol record, so the angle was retired without supporting its universal necessity theorem."
proof_attempt_summary: |
  Discovery completed and passed at field tier with the paired-Wishart covariance-fiber coverage theorem, boundary random-set law, bounded constant-factor minimax bracket, and global converse. Formalization planning then showed that the headline theorem depends on both a complete local formalization of LDiffPC and foundational real-semialgebraic projection, dimension, Whitney/Nash, and Sard infrastructure; the side study produced only sorry-bearing scaffolds and correctly escalated as unbuildable. Retry after those foundations exist axiom-free, or after a reviewed specialization removes them without weakening the stated theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 120220222
  pipeline_claude_tokens: 5122717
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# scm_partialdiff_uniform_singledoor / v1 — Downgraded

**Topic.** Boundary-honest SCM partial identification and inference for environment-specific direct effects from an LDiffPC equality/sepset ledger. For two positive diff-faithful linear-Gaussian acyclic SCMs with baseline-parent modular interventions, invariant innovation variances, and a common order, define the exact compatible-completion effect fiber Ψ(s); prove its finite semialgebraic branch representation and exact finite-sample coverage of the fixed direct-effect triple by projecting a paired Wishart covariance region through Ψ. Derive Fell boundary random-set limits using tangent-cone regularity and derived rational-branch smoothness, an exact p=3 collider singleton audit, and every-p≥3 same-law noncontraction and infinite global worst-case expected-diameter converses, with converse-only transfer to the full Bystrova–Devijver anchor class and finite attainment of each bounded Gaussian tangent minimax problem. On a separately declared coefficient/covariance-bounded Gaussian subclass, establish exact projected-Wishart coverage and explicit finite-sample constant-factor minimax expected-diameter bounds without separation or beta-min assumptions. Make no componentwise uniform-single-door iff, fixed-treewidth algorithm, rejection-certificate, non-Gaussian exact positive-inference, or exact minimax-optimality claim.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Substrate unbuildable: field-tier mathematics passed discovery, but faithful axiom-free Lean formalization requires missing real-semialgebraic foundations and a local LDiffPC soundness development.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The associated study is `CausalSmith/doc/study/semialgebraic_stratification_sard/`. Its four staging modules compile only with twelve `sorry`s; they were not promoted, are not imported by the result, and must not be treated as proved reusable substrate.
