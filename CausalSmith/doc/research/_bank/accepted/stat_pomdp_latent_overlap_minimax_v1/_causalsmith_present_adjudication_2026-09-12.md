# Presentation adjudication — 2026-09-12

## `lem:signed-depth-membership`

The frozen presentation body said that signed-depth membership held at `T = 0`, but the current Lean model carrier `ModelIndex` has a load-bearing `horizon_pos : 1 ≤ T` field and the theorem `signedDepth_membership` consumes that hypothesis. The paper statement was narrowed from `T ≥ 0` to `T ≥ 1`; the mathematical construction, stationary-law formulas, domination bound, and target-value formula were unchanged.

This is a frozen-layer correction to match the accepted Lean theorem, authorized by the supervisor's resolved presentation instruction to narrow claims to what the formalization carries.

## P5 hand-revision round — time indexing and the minimax supremum

The referee found the paper's time conventions internally inconsistent (a trajectory displayed with
states `0..T` and action/reward pairs `0..T-1`, against assumptions written over `t = 1,…,T`), and
found `1 ≤ T` displayed inside the supremum of the minimax risk. The operator resolved both: the
paper is zero-based, because the Lean epoch index is `Fin T` (`∀ t : Fin T` in every assumption
predicate, `stateAt 0` in `StationaryStart`, `phiwRaw` summing over `k ≤ t`), and `1 ≤ T` is
`ModelIndex.horizon_pos`, a field of the model carrier the supremum ranges over, not a side
condition on the supremum.

Amended `nl.frozen_body` on these bank nodes (a `.bak` of `graph.json` is beside it):

- `ass:pomdp-kernel`, `ass:sequential-ignorability`, `ass:stationary-start`, `ass:bounded-reward` —
  epoch range `t = 1,…,T` → `t = 0,…,T-1`, conditioning prefixes `X_{1:t},…` → `X_{0:t},…`, and the
  stationary start `S_1 ∼ d_b` → `S_0 ∼ d_b`.
- `def:phiw-estimator` — the average `∑_{t=k+1}^{T}` → `∑_{t=k}^{T-1}`, matching `phiwRaw`'s
  `Finset.univ.filter (fun t : Fin T ↦ k ≤ t.val)`. The one-based form also contradicted the
  Lean-rendered lemma bodies, which already displayed `∑_{t=k}^{T-1}`.
- `def:filter-quantities` — `σ(A_1,Y_1,…,A_{t-1},Y_{t-1})` → `σ(A_0,Y_0,…,A_{t-1},Y_{t-1})` and
  `ℓ_t := min{Q,t-1}` → `min{Q,t}`, matching `prefixLen t := min Q t.val` with `t : Fin T` and the
  `ObsPrefix t.val` prefix length.
- `def:minimax-risk` — `1 ≤ T` removed from the supremum subscript, the lead-in restricted to
  `T ≥ 1`, and one sentence added recording that the positive-horizon condition is part of model-class
  membership rather than a restriction on the supremum.
- `def:radius-adaptive-history-depth` — `nl.frozen_title` "Radius-adaptive history depth" →
  "Radius-calibrated history depth" (the object id is unchanged). The estimator takes `C` as an
  input; "adaptive" wrongly suggested selection of an unknown radius.

No mathematical content was weakened, no hypothesis was added or dropped, and no theorem or lemma
statement was touched. The P1 Lean-equivalence judge re-audited every amended body (the audit key
includes the body text) and returned all envs faithful.

The presentation-synthesized definitions carrying the same indexing (`synth_10`, `synth_11`,
`synth_12`, `synth_13`, `synth_15`, `synth_16`, `synth_17`) were re-indexed the same way in the
bundle's `p1_cache.json`, where synthesized bodies live; `synth_13` additionally lost the
forty-object `\cref` preamble the referee flagged, in favour of a direct definition.

Residual, deliberately not changed: appendix lemma statements that enumerate a generic length-`k`
observation prefix as `(A_1,R_1),…,(A_k,R_k)` keep that local one-based enumeration, because they are
Lean-rendered theorem statements and re-indexing them is not a presentation repair.
