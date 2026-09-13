---
qid: scm_ctf_protocol_cost_frontier
spec: v1
topic: "Cost-optimal physical acquisition certificates for counterfactual identification. For a finite discrete ADMG G with explicit physical action expansion G+, domains of size at most d, and a priced catalogue of SELECT/RAND/CTF-RAND/READ actions with endpoints, affected child sets, allowed values, precedence, and conflicts, optimize total acquisition cost over legal protocol/slice collections making the full, correctly typed unconditional CTFIDU+ procedure accept an unnested L2.5 joint Q. A protocol is a subset bit-vector in canonical topological order with exactly one fresh-iid SELECT and each mechanism used at most once. Action costs are nonnegative binary rationals paid anew per distinct acquired protocol; slices from that protocol share its cost. Output one optimal protocol collection, polynomial assignment labels, and for each of k structural target factors a chosen input regime and finite uniform value-matching ancestor/district restriction transcript. Prove the <=k source-slice sparsification, fixed-factor connected-ancestor obstruction iff theorem, and cost-preserving legality/obstruction compilation on V⊔A⊔LIT⊔FAC with Dir/Bidir/Source/Affects/Precedes/Conflicts/Owns/HasValue/InFactor/RequestedBy, yielding exact f(k,d,w)poly(input) optimization for full Gaifman incidence treewidth w. Retain ordinary legal-subclass hardness and H_k approximation only on the explicit one-action/no-synergy factor-cover subclass. Preserve positive-law and measured-ancestry source typing. No scalar identifying-functional output, evaluation, or compactness theorem is claimed; general lower certificates may be exponential. Do not claim conditional or arbitrary partial-read completeness, mediator-depth FPT, or global action-cover approximation. Consumer: Park-Lee counterfactual structural causal bandits (ICLR 2026), whose reward-distribution queries can use cheaper certified acquisition protocols. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For a fixed labelled source factor T and target C, IDENTIFY+ fails exactly when some C⊊F⊆T is bidirected connected and every vertex of F reaches C in its value-matching dependency graph. The obstruction survives each ancestor and district restriction; terminal failure supplies a witness. Independent exhaustive checks through four vertices covered 28,751 cases with zero mismatches. Two binary SCMs agree under all 27 ordinary intervention regimes but differ on P(Y_0=1,Z_1=1). Independent response noise ε=0.1 preserves positive laws and yields 1/4 versus 41/100. A cost-1 counterfactual protocol identifies the joint from its natural-X=1 slice, compared with the direct cost-2 protocol. The output contract avoids the exponential scalar-functional objection; positivity and measured ancestral closure remain explicit source-typing requirements. UNRESOLVED BOTTLENECK: Prove full CTFIDU+ acceptance equivalent to at most k uniform source-slice certificates and a cost-preserving local relational compilation whose width includes every action, conflict, precedence, and value request. EARLY KILL TEST: Exhaustively compare full acceptance and uniform certificates on binary instances with at most four mechanism vertices, four intervention actions, and two factors, including equal-value cases and omitted READs; unrecorded assignment-dependent switching or more than k required slices forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_ctf_protocol_cost_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised cost-preserving full-incidence compiler and exact bounded-width optimizer cannot be delivered without changing the oracle model, input representation, or theorem target."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The delivered optimization result is weighted set cover only after an exponentially large branch incidence relation has been constructed, so it does not deliver the advertised structural cost frontier or the promised f(k,d,w)poly(input) tractability."
  - "The key implication from complete CTFIDU+ nonfailure to forall alpha exists a successful source tuple (and its converse) is not derivable from the declared dependencies: CTFIDU+ is only an opaque algorithm symbol/acceptance call, with no theorem specifying its branch-search decomposition; the proof assumes exactly the unresolved crux."
  - "The core replaces the proposed full-incidence-Gaifman-treewidth compilation and f(k,d,w)poly(input) optimizer with exhaustive protocol/branch enumeration; it explicitly disclaims the promised bounded-treewidth compiler, so the delivered theorem is a weaker kernel than the headline frontier."
reusable_artifacts:
  - path: discovery/core.json
    kind: other
    one_line: "Versioned theorem graph for branch-indexed switching certificates, exact weighted-cover reduction, oracle lower bound, and positive physical-separation witness."
  - path: discovery/writeup.tex
    kind: witness
    one_line: "Incremental derivation note containing the explicit branch-incidence formulation and binary physical-acquisition separation construction."
seeds_burned: []
proof_attempt_summary: |
  The run replaced a false uniform-source normal form with branch-indexed switching certificates and derived an exact weighted-set-cover formulation after explicit enumeration of the protocol-to-branch incidence relation. The promised field-tier cost-preserving bounded-treewidth compiler and exact f(k,d,w)poly(input) optimizer collapsed because the input exposes an arbitrary black-box oracle over protocol masks, which forces exponentially many queries even for fixed k, d, and constant structural width. The resulting incremental kernel retains useful separation and restricted-cover artifacts, but six mathematical/source-fidelity findings remain unresolved.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 61476468
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 61476468
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# scm_ctf_protocol_cost_frontier / v1 — Downgraded

**Topic.** Cost-optimal physical acquisition certificates for counterfactual identification. For a finite discrete ADMG G with explicit physical action expansion G+, domains of size at most d, and a priced catalogue of SELECT/RAND/CTF-RAND/READ actions with endpoints, affected child sets, allowed values, precedence, and conflicts, optimize total acquisition cost over legal protocol/slice collections making the full, correctly typed unconditional CTFIDU+ procedure accept an unnested L2.5 joint Q. A protocol is a subset bit-vector in canonical topological order with exactly one fresh-iid SELECT and each mechanism used at most once. Action costs are nonnegative binary rationals paid anew per distinct acquired protocol; slices from that protocol share its cost. Output one optimal protocol collection, polynomial assignment labels, and for each of k structural target factors a chosen input regime and finite uniform value-matching ancestor/district restriction transcript. Prove the <=k source-slice sparsification, fixed-factor connected-ancestor obstruction iff theorem, and cost-preserving legality/obstruction compilation on V⊔A⊔LIT⊔FAC with Dir/Bidir/Source/Affects/Precedes/Conflicts/Owns/HasValue/InFactor/RequestedBy, yielding exact f(k,d,w)poly(input) optimization for full Gaifman incidence treewidth w. Retain ordinary legal-subclass hardness and H_k approximation only on the explicit one-action/no-synergy factor-cover subclass. Preserve positive-law and measured-ancestry source typing. No scalar identifying-functional output, evaluation, or compactness theorem is claimed; general lower certificates may be exponential. Do not claim conditional or arbitrary partial-read completeness, mediator-depth FPT, or global action-cover approximation. Consumer: Park-Lee counterfactual structural causal bandits (ICLR 2026), whose reward-distribution queries can use cheaper certified acquisition protocols. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For a fixed labelled source factor T and target C, IDENTIFY+ fails exactly when some C⊊F⊆T is bidirected connected and every vertex of F reaches C in its value-matching dependency graph. The obstruction survives each ancestor and district restriction; terminal failure supplies a witness. Independent exhaustive checks through four vertices covered 28,751 cases with zero mismatches. Two binary SCMs agree under all 27 ordinary intervention regimes but differ on P(Y_0=1,Z_1=1). Independent response noise ε=0.1 preserves positive laws and yields 1/4 versus 41/100. A cost-1 counterfactual protocol identifies the joint from its natural-X=1 slice, compared with the direct cost-2 protocol. The output contract avoids the exponential scalar-functional objection; positivity and measured ancestral closure remain explicit source-typing requirements. UNRESOLVED BOTTLENECK: Prove full CTFIDU+ acceptance equivalent to at most k uniform source-slice certificates and a cost-preserving local relational compilation whose width includes every action, conflict, precedence, and value request. EARLY KILL TEST: Exhaustively compare full acceptance and uniform certificates on binary instances with at most four mechanism vertices, four intervention actions, and two factors, including equal-value cases and omitted READs; unrecorded assignment-dependent switching or more than k required slices forces a pivot. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_ctf_protocol_cost_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The exact f(k,d,w)poly(input) optimizer is impossible for the stated arbitrary mask oracle, so the normalized incremental ceiling 5.6 remains below the field floor 7.2.

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
