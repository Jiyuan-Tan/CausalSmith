---
qid: scm_robust_jointdo_qbf
spec: v1
topic: "Robust joint-intervention design on locally switched causal stars. Fix binary observed variables with arrows w→T for every proxy w and T→Y, and let independent two-mode local switches choose bidirected edges, with equality/complement copies only. Before switch modes are revealed, choose one unit-cost proxy set J and acquire the complete single joint source P(V\\J | do(J=j)) for every j, plus P(V). Prove P_t(Y) is identifiable on a completion iff T and Y are disconnected after deleting J; give the explicit adjustment functional and strictly positive binary same-source countermodels when a path survives. Prove deciding whether some |J|≤B works for every completion is Σ₂ᴾ-complete using occurrence-copy pairs, budget-saturating pair tests, consistency paths, and selector-isolated clause chains, with singleton T,Y, constant-size switches, and nonterminal bidirected degree at most eight; return J and per-completion gID certificates or, for a fixed failing J, a completion and hedge. Compare explicitly with Akbari et al. 2023/2025, Elahi et al. 2024, Jaber et al. 2022, and switched robust-cut literature. The consumer is a dosearch pre-data design mode for one multiplex intervention under local graph uncertainty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact causal-star disconnect criterion, adjustment formula, and full-support binary indistinguishability construction. It built a quantified reduction whose rounding argument prevents auxiliary interventions and whose selector chains prevent inactive-module bypasses. Exact checks matched hedge and path criteria in 8,192 graph/intervention cases, exhausted all budget-feasible cuts in four compiled quantified examples, and verified dyadic countermodel tables for one-to-four internal proxies. Greatest-completion families collapse to ordinary cut; bounded possible terminal neighborhoods and PAG scope are excluded, and terminal degrees remain unbounded. UNRESOLVED BOTTLENECK: Independently audit the uniform occurrence/equality/selector compiler and resolve priority against switched-cut and forbidden-pair-path literature; do not broaden from the proved causal-star criterion to unrestricted strictly-binary gID without a separate semantic completeness proof. EARLY KILL TEST: Regenerate every two-clause formula over one existential and one universal variable, exhaust all auxiliary-inclusive budget cuts and switch assignments, and stop if quantified truth ever differs from residual T–Y disconnection. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_robust_jointdo_qbf.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Sound restricted fixed-completion causal-star identification and complexity results, but not the promised field-level local-switch result: constant-fanout locality and bounded terminal degree were not delivered, and practical/priority evidence remained insufficient."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The hardness theorem permits a switch coordinate to guard O(L) edge copies and leaves terminal degree unbounded, so it does not establish hardness for genuinely constant-fanout local switches."
  - "The causal significance also rests on an unusually strong protocol in which exact configuration metadata reveals the realized latent-confounding graph, while no implementation or substantive design example demonstrates that this information structure occurs in practice."
  - "These scope and evidence limitations, together with only cursory theorem-level comparison to the closest switched-separation literature, constrain the leading-econometrics paper score despite the field-level theoretical result."
  - "Panel findings left unrepaired: wrong-moment-display@lem:path-countermodels, ballast@thm:bounded-terminal-frontier-complete, related_work_gap@ass:semi-markovian."
reusable_artifacts:
  - "discovery/core.json — proved causal-star source criterion, adjustment functional, countermodels, quantified compiler audit, and bounded-terminal classification."
  - "discovery/solve_thm_robust_design_complexity.tex — proof attempt and compiler construction for the robust-design complexity theorem."
  - "discovery/solve_lem_qbf_compiler_audit.tex — audited occurrence/equality/selector compiler argument."
  - "state.json — literature_map and accepted protocol-scope caveats for future re-anchoring."
seeds_burned:
  - index: 0
    one_liner: "Quantified robust joint-proxy design on locally switched causal stars"
    reason: "The selected robust causal-star angle was exhausted at D0.5: exact released-graph metadata, unrestricted switch-copy fanout and terminal degree, absent implementation/application evidence, and cursory closest-work comparison cap it below field; lifting the floor requires D-1.2 re-anchoring."
proof_attempt_summary: |
  The run proved an exact residual T--Y disconnection criterion for the restricted positive-binary causal-star source model, explicit adjustment and countermodel constructions, and a Sigma_2^P classification for its encoded robust-design language. The field-level framing collapsed at D0.5 because the proof did not retain constant switch-copy fanout or bounded terminal degree and depended on exact revealed graph metadata without implementation or substantive application evidence. A future re-raise should preserve the sound core but re-anchor at D-1.2 around a genuinely local restriction or a stronger practical protocol, while repairing the moment-display typo and expanding the closest-work comparison.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 23069954
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 23069954
  total_tokens_consumed: null
banked_on: "2026-09-16"
---

# scm_robust_jointdo_qbf / v1 — Downgraded

**Topic.** Robust joint-intervention design on locally switched causal stars. Fix binary observed variables with arrows w→T for every proxy w and T→Y, and let independent two-mode local switches choose bidirected edges, with equality/complement copies only. Before switch modes are revealed, choose one unit-cost proxy set J and acquire the complete single joint source P(V\J | do(J=j)) for every j, plus P(V). Prove P_t(Y) is identifiable on a completion iff T and Y are disconnected after deleting J; give the explicit adjustment functional and strictly positive binary same-source countermodels when a path survives. Prove deciding whether some |J|≤B works for every completion is Σ₂ᴾ-complete using occurrence-copy pairs, budget-saturating pair tests, consistency paths, and selector-isolated clause chains, with singleton T,Y, constant-size switches, and nonterminal bidirected degree at most eight; return J and per-completion gID certificates or, for a fixed failing J, a completion and hedge. Compare explicitly with Akbari et al. 2023/2025, Elahi et al. 2024, Jaber et al. 2022, and switched robust-cut literature. The consumer is a dosearch pre-data design mode for one multiplex intervention under local graph uncertainty. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact causal-star disconnect criterion, adjustment formula, and full-support binary indistinguishability construction. It built a quantified reduction whose rounding argument prevents auxiliary interventions and whose selector chains prevent inactive-module bypasses. Exact checks matched hedge and path criteria in 8,192 graph/intervention cases, exhausted all budget-feasible cuts in four compiled quantified examples, and verified dyadic countermodel tables for one-to-four internal proxies. Greatest-completion families collapse to ordinary cut; bounded possible terminal neighborhoods and PAG scope are excluded, and terminal degrees remain unbounded. UNRESOLVED BOTTLENECK: Independently audit the uniform occurrence/equality/selector compiler and resolve priority against switched-cut and forbidden-pair-path literature; do not broaden from the proved causal-star criterion to unrestricted strictly-binary gID without a separate semantic completeness proof. EARLY KILL TEST: Regenerate every two-clause formula over one existential and one universal variable, exhaust all auxiliary-inclusive budget cuts and switch assignments, and stop if quantified truth ever differs from residual T–Y disconnection. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_robust_jointdo_qbf.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: achieved incremental below required field floor; paper_score_ceiling=6.1 < 7.4; salvageable=false within the current scope.

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
