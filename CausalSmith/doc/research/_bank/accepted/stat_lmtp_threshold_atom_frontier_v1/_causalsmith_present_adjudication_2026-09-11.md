# Presentation adjudications — 2026-09-11 hand-revision round

## Bank edit: `graph.json` — `def:local-design-notation` supporting decls

P1 halted with `lean-coverage`: the clauses defining `U_i`, `v_ell`, `N_x`, `G_x`,
`M_{ell,kappa,rho}`, `lambda_star`, `Omega_x` and the inverse-Gram intercept-weight formula
were certified by declarations that were not in the node's Lean mapping (only
`interceptWeight` was mapped).

Resolution (skill: "map the missing certifying declarations in the bank node's
`lean.supporting_decls`, keep the authored body"): added
`scaledDose`, `monomialVec`, `localCount`, `localGram`, `localGram_apply`,
`refMomentMatrix`, `lambdaStar`, `GoodGramEvent`, `interceptWeight_eq_mulVec`
(all `CausalSmith.Stat.LmtpThresholdAtomFrontier.*`, all present in
`Helpers/Design.lean`) to `lean.supporting_decls`. The authored frozen body was not
weakened or changed. `graph.json.bak` holds the pre-edit file. P1 converged afterwards.

## Frozen-layer edits (presentation-synthesized envs only, no Lean-backed body touched)

`synth_11`, `synth_14`, `synth_18`, `synth_20` were re-rendered this round with a
preamble citing every object in the paper (`\cref{obj:...}` x ~74). That preamble is pure
packaging; it also drove the P1 order solver to hoist nearly every definition into the
first two sections. Replaced the enumerations with "the objects introduced earlier in the
paper" (and, for `synth_20`, "the notation, model conditions, and constructions introduced
earlier in the paper") in `formal_layer.json`, `formal_layer.tex` and the section copies.
No Lean-backed environment was modified.

## Round 2 (2026-09-11) — frozen-body amendments NOT applied; correct channel recorded

Two referee statement-fidelity findings require amending Lean-backed frozen bodies. I first
amended them in the bundle's `formal_layer.json`; the next `--from P1` re-render silently
reverted both, because the authoritative text is `nl.frozen_body` on THIS `graph.json`, which
enters the layer verbatim. No bank edit was made, so bundle and bank remain consistent.

To apply (then sync the env copy in `sections/04_main_statistical_results.tex` and re-enter
`--from P1`):

1. `thm:minimax-risk` — `nl.frozen_body` writes the upper comparison as
   `\sup_{P\in\mathcal M} \mathbb E_P\!\left[ ... \right]`. The Lean criterion
   (`observedMinimaxRisk`, `estimatorRisk`) integrates under `iidProduct P n`, so the body
   should read `\mathbb E_{P^{\otimes n}}\!\left[ ... \right]`. One occurrence.
2. `thm:phase-diagram` — `nl.frozen_body` says the zero-threshold stabilized risk and length are
   "both asymptotic to \(n^{-1/2}\)". The Lean conclusion is `AsympSeq` (order equivalence), not
   ratio convergence to one, so the body should read "both of order \(n^{-1/2}\)". One occurrence.

Separately, `synth_3` (presentation-synthesized, editable in the bundle) was amended to state the
`[0,1]` range restriction that `observedMinimaxRisk` imposes on estimators; that edit survived.

## Round 2 — synthesized-environment removals

`synth_15` (a verbatim restatement of `def:clamp-functional`) and `synth_14` (a restatement of the
Lean-backed `def:exact-modulus-handle`, and the env whose symbol `\mathfrak R_{n,x}` P1 could not
define) were removed from the outline, the frozen layer, and the P1 synthesis cache: neither
carried a notation anchor and no environment referenced them. `synth_18` was trimmed to define
only the continuity-only class, with the Hölder class left to `def:def:model-class`. `synth_21`
(`W_{n,B_n}`, the symbol `oeq:sharp-constant` actually uses) was kept.
