# Presentation orchestrator review

## P1 checkpoint

- Moved `def:signed-depth-family` into the setup because the fixed-radius theorem uses the construction in its statement.
- Added the missing Lean coverage mappings for the model class, target value, minimax risk, and signed-depth construction without changing any statement.
- Excised `def:local-frontier-handle` because it is an unused proof-planning device, not a delivered result.
- Excised synthesized `synth_10` because it has no visible consumer.
- Acknowledged the `lem:phiw-upper` cross-reference advisory: the lemma is an appendix risk bound whose displayed domain and notation are already defined by the surrounding setup; inserting a model-class citation into its frozen Lean-backed statement would add no mathematical information.
- Retained and acknowledged the four principal results and the finite-insulin construction as delivered headline or benchmark content.

## P2 first audit and promotion review

- Reviewed the five promoted nodes (`lem:phiw-raw-variance`, `lem:phiw-score-stationary-mean`, `lem:refined-terminal-posterior`, `lem:finite-signed-depth-kl`, and `lem:insulin-bias-certificate`): each maps to a named existing Lean declaration with a complete proof and zero sorries.
- Granted the second promotion round because six residual findings identify genuinely absent citable derivation steps.
- Adjudicated `thm:uniform-overlap-frontier` as faithful: all three cached “issues” explicitly say the prose matches Lean and the final issue states that no substantive mismatch exists.
- Requested fresh rendering for the four rendering-only residuals: `prop:unit-overlap-boundary`, `thm:fixed-c-minimax`, `lem:radius-sensitive-phiw`, and `lem:uniform-parametric-floor`.

## P2 second promotion and cap

- The authorized second promotion added eleven complete, zero-sorry Lean-backed helper environments covering the insulin certificate, PHIW covariance decomposition, and signed-depth stationary/bootstrap calculations.
- After the final allowed retry, 22 of 27 proof audits were faithful. Five remained unfaithful: `lem:phiw-upper`, `lem:signed-depth-membership`, `lem:observed-path-kl`, `lem:insulin-bias-certificate`, and `lem:phiw-separated-window-covariance`.
- Three residual proofs still require citable mathematical steps, so the promotion/referee cap is exhausted and the run stops as `cap-block` under the skill contract.

## P2 resumed promotion review

- Re-entered under the operator-authorized resume exception and granted two additional promotion
  rounds only for genuinely citable gaps. The rounds added the certified stationary-reward
  enclosure, signed-depth terminal-sign invariant, separated-window peeling,
  behavior-support operator congruence, and signed-depth conditional-reward-mean environments.
- Checked that every promoted environment has a named Lean declaration, appears in both `objs:` and
  `home_objs:` in the existing outline, and passed the P1 equivalence judge before being frozen.
- Reviewed the 36 remaining P1 advisories. They are `xref-missing` notices on Lean-backed statement
  bodies whose dependencies are supplied by the surrounding setup or cited in their proofs; adding
  proof-route citations to frozen theorem statements would not clarify the mathematical claims.
- Archived each rejected proof candidate before re-rendering. After the helper layer was complete,
  hand-repaired the three remaining rendering-only proofs: removed reader-facing Lean comments,
  made the separated-window indexing and ratio bound explicit, and stated the finite-grid kernel and
  certificate conversions needed by the insulin calculation. No frozen statement or Lean source was
  changed in these repairs.

## P2 reproduced repair defect — lease return

- Verbatim terminal line: `causalsmith: P2 proof audit: rendering defects remain (3 proof(s) still
  unfaithful after repair — adjudicate, or delete the proof file for <id> under proofs/ (its colon is
  spelled --) to re-render from scratch)`.
- Minimal replay: start from the snapshotted hand repairs in
  `logs/snapshots/pre_p2_hand_repair_20260912T1335/`, run
  `present stat_pomdp_latent_overlap_minimax v1 --from P2 --auto`, and inspect the three resulting
  proof files and `proof_audit_cache.json`.
- Wrong input: the proof-repair worker's exact-replacement response for
  `lem:insulin-bias-certificate` reintroduced reader-visible `% lean:` comments and invented a
  transition enclosure that the subsequent judge found non-stochastic; the same repair cycle also
  left the separated-window endpoint/carrier mismatch unresolved.
- Trust site: `src/presentation/stages/p2_draft.ts` passes the replacement response through
  `parseProofRepair`, and `src/presentation/audit.ts` persists the parsed replacement before the next
  judge call. The post-repair judge correctly catches the defects, but the stage has no deterministic
  route that preserves an orchestrator-authored correction from another lossy repair pass.
- This is the second reproduced three-proof rendering halt after both fresh regeneration and a
  source-grounded hand repair. Per the presentation skill's stop rule, no further cache deletion,
  promotion, or proof rewrite is authorized in this lease.

## P2 operator-fixed resume and promotion round 5

- Confirmed that the three operator-restored proof files are byte-identical to
  `logs/snapshots/pre_p2_hand_repair_20260912T1335/proofs/` and contain no hand-placed `% lean:`
  tags, then resumed exactly from P2 in auto mode.
- The repaired audit persistence path cleared `lem:phiw-separated-window-covariance`; the complete
  P2 pass halted with eight unfaithful proofs, five explicitly tagged as missing derivations that a
  promoted lemma can supply.
- Granted promotion round 5 under the operator's standing rule. The comparison baseline for this
  round is eight unfaithful proofs; a further round is allowed only if this round lowers that count.
- Promotion round 5 added eleven Lean-backed helper environments; all eleven passed the P1
  equivalence judge. The P2 recount fell from eight to six unfaithful proofs, so the round made
  progress. Every surviving issue is tagged `[rendering]` or `[citation]`, with no missing derivation;
  promotion cannot address these residuals, so the six proof candidates are archived and removed
  for fresh writer rendering as prescribed by the P2 halt receipt.
- Fresh rendering reduced the residual count from six to one. The only survivor,
  `lem:terminal-posterior-initial-window`, still has a wrong-direction explanation for the bound on
  `w_Q`; it is rendering-only. Archived the regenerated candidate and authorized the single
  sanctioned fresh-render workaround. Recurrence of the same defect after this retry is a
  pipeline-bug under the stop rule.
- The second fresh render cleared the final P2 proof audit and P3 completed without hard failures.
- P4's full Lean build twice terminated at the hard-coded 30-minute `execFile` timeout with only
  `Command failed: lake ... build ...` and no Lean diagnostic. On the second termination, three
  Lean compiler children were still healthy and compiling certificate parts at high CPU. Authorized
  the single sanctioned workaround: pre-warm the exact P4 module target list outside the capped
  call, capture the full build output, then re-enter P4 once.
