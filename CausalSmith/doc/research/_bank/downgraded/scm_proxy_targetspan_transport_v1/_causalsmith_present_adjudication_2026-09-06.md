# Presentation adjudication — 2026-09-06

Bundle: `scm_proxy_targetspan_transport/v1`

## P1 notation homes

The P1 notation reviewer initially found Lean-backed symbols without reader-facing homes. The presentation outline now assigns those symbols to the earliest existing environment that can display their defining content. The main assignments are:

- model and sampling primitives to the factorization and sampling assumptions;
- conditional, unconditional, and empirical moments to their first consuming setup environments;
- row laws and the two-sample product space to the triangular source-sampling environment;
- the target estimand and latent factorization quantities to the observable-factorization environment;
- Wald functional, variance, and quantile notation to their regular-inference environments;
- finite witness carriers to the rank-deficient witness definition.

These are presentation-only ownership decisions. No Lean declaration, crosswalk mapping, theorem statement, or proof was edited manually.

## Halt: post-audit notation regression

The ordinary P1 notation loop converged cleanly. The subsequent Lean statement-equivalence audit rewrote and persisted several bodies, after which the mandatory post-audit notation review reported that previously resolved defining displays were again missing or ordered after first use. Representative recurrences were `H_x`, `z_{x,y}`, `b`, `B_x`, and `r`; the synthesized covariance environment was also placed before the quantities it uses.

Per the `causalsmith-present` stop rule, the bundle is halted as a pipeline bug. The failing re-entry was:

`cd CausalSmith/tools && source scripts/node_env.sh && npx tsx bin/causalsmith.ts present scm_proxy_targetspan_transport v1 --from P1`

Durable log:

`<workspace>/_orch_logs/present_scm_proxy_targetspan_transport_v1_p1order_20260906T064355Z.log`

