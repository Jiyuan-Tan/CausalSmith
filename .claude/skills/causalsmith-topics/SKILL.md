---
name: causalsmith-topics
description: Generate search-grounded, human-aligned topic anchors for CausalSmith research. Use when the user asks for promising CausalSmith topics, a research slate, a niche in an area, or an apply (application-domain) / diagnose (practice-audit) / bridge (cross-field) candidate. Return a ready-to-run `causalsmith research --propose` command but do not launch it or edit prompts.
---

# /causalsmith-topics — search-grounded topic generator

Produce candidate `--propose <topic>` anchors matching the user's taste. A "topic" is the anchor string
in `causalsmith research --propose "<topic>" <qid> <spec>`; D-1.1 turns it into `gaps.json`. Deliverable:
a small slate the user picks from, then a ready-to-run command. The 17 principles below are the rubric —
apply every one.

## Runtime

Three steps spawn helpers: the deep-read pass (step 3 / A3), the adversarial gate, and the presolve.
- **Claude Code:** deep reads via the Agent tool (`general-purpose`, one batch per message). The gate
  shells out to codex (cross-model adversary): `codex exec --sandbox read-only -C <cwd>
  --skip-git-repo-check -c windows.sandbox=unelevated -c model=gpt-5.6-sol -c model_reasoning_effort=high`,
  prompt on stdin, `timeout 1200`, run FOREGROUND in one call. Presolve the same way with `gpt-6-astra`,
  `xhigh`.
- **Codex:** spawn review/presolve agents natively (never `codex exec` yourself); instruct the reviewer
  to actively refute to recover independence. Presolver: `gpt-6-astra`, `xhigh`.

**When dispatched as a subagent:** you own selection end-to-end — the capped gate loop and the presolve
run autonomously, blocking on each verdict in your turn. Never start an explicit `run_in_background`
task and end your turn, and never detach manually (`nohup`/`&`); if a child is long, foreground-poll it.
Return to the coordinator only at the bounce point (terminal no-accept after the capped re-propose) or
when blocked, handing back `{slate, verbatim gate verdicts, verbatim presolve verdicts, ranked options +
recommendation}` tagged `ESCALATION` / `BLOCKED` / `DONE`. On `ESCALATION` also hand back a ranked list
of UNTRIED levers (fresh cluster / sub-area / mode, one-line headroom each) plus your best tier-honest
fallback; an empty list signals structural exhaustion. The coordinator re-steers ≤4 rounds and never
re-runs your deep reads/gate/presolve.

## Generation procedure


1. **Scope.** Take the user's area/seed, else span clusters (panel / exactid / partialid / stat /
   experimentation / scm; no cluster preference, #11). Read the flagship rubric
   (`CausalSmith/tools/src/discovery/prompts/_shared/stage_flagship_rubric.txt`) and the motif library
   (`.../prompts/D-1/stage_neg1_2_motif_library.txt`) so each candidate maps to an axis (a)–(i) and a
   motif (M1–M20); the library defines each cluster's admissible shapes — never narrow a cluster to its
   default shape. **Choose a stance:** *exploit* (extend a banked result or a cluster with a high
   accepted-to-attempted ratio in `_bank/`) or *explore* (a cluster/area with few acceptances); state it
   in one line. The stance steers drafting only, not ranking or the gate.
2. **Search FIRST** (#8, #2). Websearch each area for work from the last 1–5 years; select 1–2
   theorem-bearing anchor papers, preferring highly-cited authors with a strong track record (search
   steer only; never enters ranking). For each anchor inspect the theorem's scope/proof boundary and
   what its load-bearing method could do for another target, model, or setting. Scan accepted-bank
   READMEs in the same pass. Read the follow-up wave, not the date: thin-but-growing = open; thick =
   worked (routes to step 5, not a higher score).
3. **Deep-read pass (parallel subagents, mandatory).** Every candidate rests on a theorem actually read.
   Each digest (≤400 words): (a) central theorems and load-bearing proof steps; (b) 1–2 unresolved
   questions at the scope/proof boundary, naming the blocking step; (c) 1–2 technique-derived
   directions for another target/model/setting, naming the first changed proof step; (d) follow-up
   searches for each. Tag occupied directions `closed-by:<cite>`. For a bank anchor read its
   `README.md` + `discovery/writeup.tex` and run the same external search.
4. **Draft ~4 candidates** (#12) from both opportunity kinds. Rank by
   evidence, mathematical depth, novelty, feasibility, and consumer value. Each carries a named focal object, a computation method if
   it is a bound (#3), the estimation rung for ID/partial-ID (#9), and the tier-justifying hard theorem
   in the kernel (#15). For an open characterization problem make the kernel problem-closed and
   answer-open: fix model, information regime, target, criterion, deliverable, consumer, scope; leave
   the exact rate/formula/threshold open unless derived; record a conjectured answer as presolve
   evidence.
5. **Per-candidate confirm** (#2). Focused search on the exact question or target–method pair; state in
   one line how it differs from the closest recent paper. Search citing/follow-up work on the anchor,
   not just destination keywords.
6. **Saturation check.** Cross-check `CausalSmith/doc/research/active/<qid>/` and `_bank/`. Drop a
   collision with an in-flight run. For a `_bank/` collision branch on the README `reraise_status`:
   `true-negative` → drop; `re-raise` → keep, re-anchored at the corrected tier; `retry` → keep, same
   framing. Never branch on `reusable`. If `reraise_status` is `unknown`/absent/`TODO`, skim the
   entry's `*_reviews.jsonl`.
7. **17-principle gate.** Drop or repair failures; #13 is a hard gate.
8. **Present the slate** with an adversarial self-ranking and each candidate's most-likely D0.5 death.
9. **Gate, presolve, emit.** Run the adversarial gate; after accept, run the presolve; only a `launch`
   verdict produces the command: `causalsmith research --propose "<anchor>" <qid> <spec> --novelty
   <target>` with the presolve capsule embedded in `<anchor>`. `--novelty` is required and maps the
   accepted Target tier directly (`flagship | field | subfield | incremental`). Do not launch it.

## Venue reference (orientation, not a filter)

- Theory/method: Econometrica, QJE, AER, ReStud, JPE, J. Econometrics, Econometrics J., Econometric
  Theory; Ann. Statist., JASA, Biometrika, JRSS-B, JMLR; NeurIPS / ICML / UAI.
- Applied practice (DG1 scan, #17 consumers): AER, AEJ:Applied, AEJ:Policy, JHR, JPubE, ReStat,
  Management Science, Marketing Science.

arXiv preprints are fully eligible; a listed venue is never evidence a direction is open.

## Bank-sourced leads

Accepted bank entries are inspiration sources: an **unresolved-question lead** (a question at the
entry's scope/proof boundary; identify the blocking step, search subsequent work) or a
**technique-derived lead** (the entry's method on another target/model/setting; identify the first
non-verbatim proof step, search prior art; for a new application domain also apply gate A4). The bank
grounds the MATH only — the formalized-substrate advantage may be noted but never ranks. A lead does
not collide with its own parent but must differ from the parent's banked theorem. Bank leads compete on
the same slate with no bonus.

## Apply mode (--apply)

Apply mode is the subset of technique-derived directions whose destination is a NEW external
application domain. Steps A1–A4 replace steps 1–3; steps 4–9 run unchanged.

- **A1 — Domain scan.** Websearch applied venues (OR, RL, LLM evaluation, ML systems, A/B platforms,
  recommenders, queueing/service ops, …) for settings where causal questions are debated without the
  formal machinery or causal tools are visibly misapplied. Pick 2–3 domains.
- **A2 — Donor matching.** Name the donor framework at cluster granularity (the cluster classifies the
  kernel's mathematical type, not the domain). The donor may be a bank entry.
- **A3 — Deep-read pass.** As step 3, but two reads per candidate: the domain paper (formal structure —
  data regime, estimand, dependence) and the donor's anchor theorem.
- **A4 — Non-verbatim witness gate (HARD).** Show the classical theorem is NOT a verbatim instance, at
  one of: (1) a load-bearing assumption fails for a setting-native reason; (2) the domain estimand is a
  different functional with no classical counterpart; (3) the data regime breaks the classical proof;
  (4) the correspondence itself requires a theorem (with a counterexample outside its conditions). Name
  the break point and the concrete witness. "Every step transfers verbatim" → drop.

Extra slate lines:
```
Donor framework: <cluster / anchor theorem>
New setting: <domain + data regime>
Non-verbatim witness: <break point 1-4 + concrete witness>
```
The emitted anchor encodes setting + donor + witness.

## Diagnose mode (--diagnose)

Audit APPLIED PRACTICE for a load-bearing unproven belief. The headline kernel is always a positive
characterization theorem (axis (e); (d) as fallback) — a bare counterexample is not a paper. Steps
DG1–DG4 replace steps 1–3.

- **DG1 — Practice scan.** Websearch applied sources (top-journal empirical papers, practitioner
  guides, software defaults) for a widespread practice P resting on an unproven belief B, or one proven
  only in a narrower special case.
- **DG2 — Belief formalization + strawman guard (HARD).** State B precisely over a named class. B must
  be genuinely held: ≥2 published applications or one software default rely on it, else drop.
- **DG3 — Numeric reconnaissance.** Test B on small legal instances first; for a software default,
  exercise the actual package. B false → diagnose candidate (the instance is the sanity witness); B
  robustly true → "first proof that P is valid on class C" (axes (c)/(f)). Kill "true and already
  proven" and "true with only an efficiency gap" (no Δ = 0-iff characterization → no diagnose kernel).
- **DG4 — Kernel shape (all three).** (i) the characterization IS the kernel: estimand delivered by P =
  target + Δ with Δ = 0 iff C, stated as a precise conjecture; (ii) the verified counterexample is the
  sanity witness, not the headline; (iii) the corrected estimand/estimator is the #9 rung.

Extra slate lines:
```
Practice: <P + ≥2 citing applications or software default>
Belief + recon: <B stated precisely; instance tested + outcome>
Remedy: <corrected object / estimator>
```

## Bridge mode (--bridge)

Find a SAME-OBJECT bridge between a causal-inference framework and another field (OT, OR, control,
information theory, risk, another statistics subfield). Steps BR1–BR3 replace steps 1–3.

- **BR1 — Pair scan.** Websearch for framework pairs answering the same inferential question about the
  same object (exemplar: MSM ≡ CVaR/DRO dual).
- **BR2 — Same-object gate (HARD).** State the shared object formally on both sides; the correspondence
  must itself require a theorem (coincidence conditions + a counterexample outside them). A renaming
  dictionary → drop. Numerically hand-check the coincidence equality on a minimal instance — a one-way
  relation dressed as an equivalence is the dominant bridge failure.
- **BR3 — Two-sided deep-read.** Two reads per candidate; each digest reports which proof step the
  coincidence conditions touch.

Kernel: the equivalence / sharp inequality / mutual characterization with the coincidence conditions as
hypotheses; witness = a worked instance where the bridge computes something one side alone could not.

Extra slate lines:
```
Sides: <F1 anchor / F2 anchor>
Shared object + coincidence: <formal statement on both sides; conditions + outside counterexample>
Bridge payoff: <what the bridge computes that one side alone could not>
```

## The 17-principle rubric (apply ALL)

1. **Infra-agnostic.** Judge math only, never Causalean infrastructure.
2. **Live prior-art search is mandatory.** State how the topic differs from the closest paper.
3. **A bound needs a concrete computation method.** Prefer closed form over an LP/inf-sup framing;
   the closed-form reduction of a published abstract bound is a creditable niche. Tie-break, not a
   filter.
4. **No sensitivity model on a non-identified parameter.**
5. **Prefer estimation-nontrivial framing; reject trivial-iff extensions.**
6. **No superficial cross-field bridges** — a same-object bridge is welcome; a new application domain
   is welcome iff it carries a non-verbatim witness (A4).
7. **Require a nontrivial mathematical change** — a new object, regime, target, or setting that changes
   a load-bearing proof step.
8. **Generate at the live-opportunity altitude.** Search first; never re-propose an occupied headline;
   rank by the step-4 criteria, not opportunity origin.
9. **ID/partial-ID topics carry the estimation rung in the kernel.**
10. **Default to positive constructive results.** A necessity/impossibility result only when surprising
    or quantitatively sharp.
11. **No cluster preference; crowdedness never disqualifies.** Neither collision density nor a missing
    anchor is a drop reason — deep-read the anchor instead.
12. **Slate of ~5, pick the best.**
13. **Well-posed under its own assumptions.** Reject a framing that mislabels its difficulty
    (disclaiming the regularity the target needs; calling an estimation problem identification, e.g.
    "partial ID of ATE under weak overlap" — point-identified whenever `0<e(X)<1` a.e.). Self-test: is
    the focal object a function of P alone, and does the advertised difficulty actually bite? Repair by
    reframing to the difficulty that bites, or drop.
14. **Tier honesty.** Ladder `flagship > field > subfield > incremental`: flagship = a first sharp
    boundary, a new estimand-defining object, or a method carried into a setting where it changes what
    can be learned; field = a genuinely new scalar/regime/threshold nontrivially extending named prior
    art; subfield = generic machinery on a new instance, or a single counterexample/reduction;
    incremental = reparametrization. Each candidate carries `Target tier` and `Est. achievable tier`;
    achievable < target fails — strengthen the kernel or re-pitch honestly. The emitted command sets
    `--novelty <target>`.
15. **Put the hard theorem in the KERNEL** as a precise conjecture. If the stated kernel reduces to a
    routine step (a continuous-mapping image of a known limit, a known optimization, a verbatim
    transfer) while the depth sits in an unstated follow-on, the gate grades the routine kernel
    subfield. Promote the hard object (nuisance-robust inference theorem, characterization / optimal
    value, sharp converse, completeness proof) to be the kernel; the routine half becomes a lemma.
16. **Specify the OBJECT; delegate the MECHANICS.** Under-specifying the object (target, model, domain,
    quantifiers, comparison class, finite-sample scope) → `kernel_is_precise_conjecture:false`.
    Over-specifying mechanics (normalizations, constants, splitting schemes, class margins) → free
    refutation targets. Pin the object and any frontier/criterion; mark mechanics as delegated; never
    commit an algebraic form or instance you have not checked. Every remaining universally-quantified
    clause carries its own checked instance or is explicitly delegated; every term is defined on its
    clause's full domain. `refutation_found` + `derivation_step` + `tier_if_true >= target` on rotating
    slips means the drafting is the bottleneck: strip back to object + verified instance + tier argument
    and re-gate; if that still fails, it is a launch decision, not another gate round.
17. **Name the consumer.** ≥1 specific published applied work, software default, or named empirical
    literature whose conclusions or practice would CHANGE if the kernel is true, plus what changes.
    "The theory literature on X" is not a consumer. Consumer strength weighs equally with tier.

## Slate row format

```
<anchor phrase>  ·  cluster  ·  axis (a)-(i)  ·  motif (M1-M20)
Live opportunity: <unresolved question | technique-derived direction, and the occupied result it avoids>
Grounding: <anchor paper> Thm <n> — <the proof-structure fact the niche rests on>
Closest recent work: <bibkey/arXiv> — differs by: <one line> (#2)
Focal object: <named object>          Computation: <closed form | algorithm | finite instance>  (#3)
Estimation rung: <estimator + inference over the set>  (#9)
Consumer: <who (≥1 citation or software default) + what changes in their practice>  (#17)
Target tier: <…>   Est. achievable tier: <…> — ceiling reason: <the strongest honest result a full D0 solve yields, and why>  (#14)
Likely D0.5 death: <where it would collapse>
```

Then the adversarial ranking with one-line reasons, and the emitted command for the winner.

## Adversarial quality gate (post-selection)

Build the reviewer prompt from `reviewer-prompt-template.md` (this directory) — fill its `{{SLOTS}}`
and change nothing else; it carries the stance, tier ladder, rubric, decision rule
(`worthy = kernel_is_precise_conjecture && !refutation_found && tier_if_true >= target_tier && consumer_is_real`),
output schema, and consistency requirements. Send the whole prompt every round; on re-gates use a
factual slot-level changelog, never an argument.

**A gate accept (`worthy:true`) is required before acting.** `worthy:false` is a repair-or-replace
signal; you drive the gate to an accept yourself (repair, runner-up, re-propose) without handing the
choice to the user, who is only the backstop after the capped loop.

**Reading the verdict.** `topic_death_or_derivation` routes the loop. `tier_if_true` drives the
shortfall branch (`estimated_tier` does not). `consumer_is_real:false` is a `derivation_step` (name a
real consumer or re-anchor) unless no consumer can exist. `expert_prior` / `contradicts_expert_prior`
are advisory — log, never act. If the decision rule holds, the verdict is an accept even with a
volunteered `derivation_step` note — do not grind a sound kernel through repairs.

**Tier shortfall (`clears_target_tier:false`).** (a) the `reframe_suggestion` is a real available
strengthening → repair and re-gate the same candidate; (b) no strengthening reaches the target →
`topic_death`. Never auto-downgrade `target_tier`.

**Loop.** On a genuine `worthy:false`: `derivation_step` → repair (fully specify the model / state the
missing theorem) and re-gate the SAME candidate, up to 3 re-gates; a #15 kernel-pivot is a NEW candidate
with its own budget. After 3 failed re-gates: one #15 pivot if the gate named an adjacent hard kernel,
else the candidate is subfield-terminal (hold as the tier-honest fallback). `topic_death` → drop and
advance. Never surface a mid-loop `worthy:false` to the user.

**Kernel-pivot (#15).** A `derivation_step` verdict with `is_relabeling:false`, direction OPEN, and a
named hard theorem as the missing content, yet `repairable_by_reframing:false`, means the field object
is an ADJACENT kernel: promote that theorem to be the kernel as a fresh candidate and gate it before
accepting a subfield ceiling. A pivot or estimand re-anchor invalidates the consumer line — re-verify
#17. A direction is subfield-terminal only when no adjacent hard kernel exists or it is vacuous /
ill-posed / already proven (verify which).

- **Round 1 — top pick.** Accept → emit. `derivation_step` → repair loop. `topic_death` → Round 2.
- **Round 2 — runner-up.** Gate rank #2 yourself. Accept → emit. Both dead → double rejection.
- **Double rejection.** Do not try #3–#5 as-is. Re-run steps 1–9 with the rejected anchors and their
  failure modes as anti-constraints; select and gate the best of the new slate yourself. Capped at one
  re-propose; only then does control return to the user with the full picture.

## Bounded presolve (post-acceptance)

Dispatch ONE fresh presolver (`gpt-6-astra`, `xhigh`) with the accepted candidate, primary sources, and
follow-up-search receipts; withhold the preliminary score. Aim at the paper, not a feasibility memo.
Three passes in one call:

1. **Constructive attempt.** State the theorem spine; derive the central reduction or attack the
   hardest lemma; solve a representative special case. Separate derivation from heuristics; name the
   exact remaining bottleneck.
2. **Destructive check.** Counterexamples and omitted boundary regimes; current and citing literature
   for a collision; collapse to generic machinery; comparison with accepted-paper tier anchors.
3. **Strongest-form draft.** The strongest supported result, paper-shaped: theorem statement(s) at full
   precision, proof architecture, each load-bearing step in checkable detail. Routine steps may be
   compressed to a named claim and hard steps left open, but every compression or gap is listed. Persist
   the draft as a file and return its path.

Require exactly:

```json
{
  "verdict": "launch | pivot | drop",
  "reason": "<2-4 sentences>",
  "constructive_traction": "<nontrivial reduction, lemma, or solved special case; derivation vs heuristic>",
  "remaining_bottleneck": "<one exact unresolved theorem step>",
  "failed_regimes_checked": "<counterexamples, boundaries, and collisions tested>",
  "early_kill_test": "<one bounded first test whose failure should pivot or stop>",
  "launch_revision": "<material correction required before launch; empty when none>",
  "strongest_form_headline": "<the strongest supported theorem statement, <=120 words>",
  "strongest_form_path": "<absolute path to the paper-shaped draft>",
  "strongest_form_gaps": "<every compressed or unproved step in that draft>"
}
```

**Verdicts.** `launch` — nontrivial derived traction OR a credible spine with a precise bottleneck,
novelty survives, `launch_revision` empty, every destructive finding has a resolution path;
hard-but-likely-correct qualifies. On an answer-open topic a corrected answer is not a pivot while the
problem coordinates (model, regime, target, criterion, deliverable, consumer, scope, tier) are unchanged.
`pivot` — the area is live but a coordinate or the achievable tier needs a material change. `drop` —
affirmative evidence only: collision, generic reduction, counterexample, contradiction, vacuity, or an
obstruction to every route in the spine.

**Routing.** `launch` → emit. `pivot`/`drop` → `ESCALATION` with the verbatim receipt as the
coordinator's anti-constraint. One presolve per gate-accepted winner per round.

On `launch`, append a 150–250 word capsule to the anchor with only:

```text
PRESOLVE EVIDENCE REQUIRING VERIFICATION: <derived reduction/special case and failed checks>.
UNRESOLVED BOTTLENECK: <exact remaining step>.
EARLY KILL TEST: <bounded first test whose failure should pivot or stop the run>.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <absolute path>.
```

The draft stays in the file; D-1/D0 reads it from the path and must independently verify every listed
gap. Preserve the candidate's original assumptions; theorem status is reserved for D-1/D0 verification.


## What this skill does NOT do

- Launch CausalSmith research (emit the command; the user runs it).
- Filter on Causalean infra availability (#1).
