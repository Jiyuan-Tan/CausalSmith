---
qid: pid_binaryu_commonodds_tipping
spec: v1
topic: "Sharp common-binary-confounder ATE bounds and tipping frontiers for the Rosenbaum–Rubin odds model. For finite categorical X and binary A,Y,U, assume consistency and (Y(0),Y(1)) independent of A conditional on (X,U). In each stratum bound OR(A,U) in [1/Gamma_A,Gamma_A] and OR(Y(a),U) in [1/Gamma_a,Gamma_a], with interior observed p=P(A=1|X) and r_a=P(Y=1|A=a,X). Let w_a=P(U=1|A=a,X), pi=p w_1+(1-p)w_0, and D_A be the compact cross-product-odds region. For fixed r,w,pi and theta=OR(Y(a),U), derive the unique feasible root of (1-w)(theta-1)mu_0^2+[1+(w-r)(theta-1)]mu_0-r=0, set mu_1=theta mu_0/[1+(theta-1)mu_0], and use q-r=(pi-w)(mu_1-mu_0) to prove outcome extrema occur at theta in {Gamma,1/Gamma}. Prove the exact stratum ATE interval is min/max of h_1 minus h_0 over the SAME (w_0,w_1), construct endpoint-attaining conditional Bernoulli potential outcomes, and sum over X. Give a complete semialgebraic algorithm enumerating the two exposure-odds boundary arcs and endpoints, analytic outcome-sign branches, and generic interior stationary candidates by resultants, with separate treatment of Gamma=1, constant-U corners, denominator artifacts, and stationary continua. Prove an open-set strict tightening versus the separate-posterior-pair relaxation and characterize the piecewise-algebraic zero-tipping surface. State Manski recovery only as the all-budget limit under vanishing positivity. Certify the rational witness p=1/2,w_1=4/5,w_0=1/5,Gamma_A=16; outcome risks for Y(1)=(13/20,1/20) and Y(0)=(4/5,1/10), with Gamma_0=Gamma_1=36, observed r_1=53/100,r_0=6/25 and causal ATE=-1/10 versus unconfounded ATE=29/100. PRESOLVE EVIDENCE REQUIRING VERIFICATION: coarse global optimization produced common-U bounds about [-0.1075,0.5395] versus separate-pair bounds about [-0.1104,0.5588]; exact interval arithmetic must certify the gap. At Gamma_A=1 or Gamma_0=Gamma_1=1 the adjusted contrast is point identified; near deterministic U=A recovers Manski in the infinite-budget limit. Credit Rosenbaum–Rubin's fixed-parameter model, VanderWeele–Arah bias decomposition, Ding–VanderWeele arbitrary-U bias factor, Dorn–Guo–Kallus marginal sensitivity bounds, and Nabi et al.'s tilt model. UNRESOLVED BOTTLENECK: rule out missed/spurious resultant roots and verify that Rosenbaum–Rubin Sections 2–4 do not already state an equivalent sharp bounded-parameter envelope. EARLY KILL TEST: use exact rational branch formulas and interval Newton checks on the displayed witness, compare against a direct nonlinear feasibility program and the historical Rosenbaum–Rubin envelope, and stop if any endpoint is missed, the strict gap vanishes, or the novelty collision is exact."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No proved translation to an established sensitivity model, no demonstrated CERT implementation, and only pointwise regular-branch inference; additionally, the terminal draft retains undeclared dependencies, incomplete related-work comparisons, and an unconsumed ballast node."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "Delivered tier incremental < floor field; not salvageable within scope."
  - "The semialgebraic certificate and atlas are mathematical termination results rather than a reproducible implementation with demonstrated computational behavior."
  - "The advertised inference contribution is only pointwise on a unique smooth active branch; uniform inference at the branch switches and degeneracies emphasized by the tipping atlas remains open."
  - "The exhaustive canonical-arc reduction and compact continuity argument explicitly invoke thm:one-arc-endpoint-reduction and prop:closed-chart-extension, neither of which is declared in depends_on."
  - "The witness proof silently uses thm:one-arc-endpoint-reduction and lem:outcome-budget-extrema, but neither node is in depends_on."
  - "The bibliography includes Zhao--Small--Bhattacharya, Dorn--Guo--Kallus, Franks--D'Amour--Feller, Gabriel--Sachs--Jensen, Huang et al., and Fan--Park without a relevance sentence or a precise comparison."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/solve_thm_complete_semialgebraic_certificate.json
  - discovery/solve_thm_sharp_common_u_envelope.json
  - reviews/angle0_v3.json
seeds_burned: []
proof_attempt_summary: |
  Discovery derived an exact common-U ATE envelope, a one-arc endpoint reduction,
  an exact rational strict-tightening witness, and a regular-branch tipping-frontier
  limit. The cold D0.5 referee nevertheless graded the package incremental because
  it lacked a proved bridge to an established sensitivity model, a demonstrated
  certificate implementation, and uniform inference on singular frontier strata.
  The terminal math review also remained REVISE due to undeclared proof dependencies,
  incomplete comparison prose, and an unconsumed coordinate-equivalence node; this
  bank entry therefore records an unapproved draft, not an established sound theorem.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31239937
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31239937
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# pid_binaryu_commonodds_tipping / v1 — Downgraded

**Topic.** Sharp common-binary-confounder ATE bounds and tipping frontiers for the Rosenbaum–Rubin odds model. For finite categorical X and binary A,Y,U, assume consistency and (Y(0),Y(1)) independent of A conditional on (X,U). In each stratum bound OR(A,U) in [1/Gamma_A,Gamma_A] and OR(Y(a),U) in [1/Gamma_a,Gamma_a], with interior observed p=P(A=1|X) and r_a=P(Y=1|A=a,X). Let w_a=P(U=1|A=a,X), pi=p w_1+(1-p)w_0, and D_A be the compact cross-product-odds region. For fixed r,w,pi and theta=OR(Y(a),U), derive the unique feasible root of (1-w)(theta-1)mu_0^2+[1+(w-r)(theta-1)]mu_0-r=0, set mu_1=theta mu_0/[1+(theta-1)mu_0], and use q-r=(pi-w)(mu_1-mu_0) to prove outcome extrema occur at theta in {Gamma,1/Gamma}. Prove the exact stratum ATE interval is min/max of h_1 minus h_0 over the SAME (w_0,w_1), construct endpoint-attaining conditional Bernoulli potential outcomes, and sum over X. Give a complete semialgebraic algorithm enumerating the two exposure-odds boundary arcs and endpoints, analytic outcome-sign branches, and generic interior stationary candidates by resultants, with separate treatment of Gamma=1, constant-U corners, denominator artifacts, and stationary continua. Prove an open-set strict tightening versus the separate-posterior-pair relaxation and characterize the piecewise-algebraic zero-tipping surface. State Manski recovery only as the all-budget limit under vanishing positivity. Certify the rational witness p=1/2,w_1=4/5,w_0=1/5,Gamma_A=16; outcome risks for Y(1)=(13/20,1/20) and Y(0)=(4/5,1/10), with Gamma_0=Gamma_1=36, observed r_1=53/100,r_0=6/25 and causal ATE=-1/10 versus unconfounded ATE=29/100. PRESOLVE EVIDENCE REQUIRING VERIFICATION: coarse global optimization produced common-U bounds about [-0.1075,0.5395] versus separate-pair bounds about [-0.1104,0.5588]; exact interval arithmetic must certify the gap. At Gamma_A=1 or Gamma_0=Gamma_1=1 the adjusted contrast is point identified; near deterministic U=A recovers Manski in the infinite-budget limit. Credit Rosenbaum–Rubin's fixed-parameter model, VanderWeele–Arah bias decomposition, Ding–VanderWeele arbitrary-U bias factor, Dorn–Guo–Kallus marginal sensitivity bounds, and Nabi et al.'s tilt model. UNRESOLVED BOTTLENECK: rule out missed/spurious resultant roots and verify that Rosenbaum–Rubin Sections 2–4 do not already state an equivalent sharp bounded-parameter envelope. EARLY KILL TEST: use exact rational branch formulas and interval Newton checks on the displayed witness, compare against a direct nonlinear feasibility program and the historical Rosenbaum–Rubin envelope, and stop if any endpoint is missed, the strict gap vanishes, or the novelty collision is exact.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: delivered tier incremental below field, paper-score ceiling 6.4 < 7.2, salvageable=false; math panel remained REVISE, so soundness is not established.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The operator's mill policy requires `terminal:below-floor` runs to be banked at
their achieved tier. This entry must not be cited as soundness-approved: the
final math panel returned REVISE and the independent validity gate agreed that
the bounded dependency/prose/ballast repairs would need a fresh D0.5 soundness
pass before reuse as a theorem package.
