# Proof automation in Causalean

What the library provides beyond Mathlib's stock tactics, when to reach for it, and what
must never be fed into it. Kept deliberately short — if a rule here needs a paragraph of
caveats, it is wrong.

## Discharging side conditions: `fun_prop`

The library's side-condition layer (measurability, integrability of its own constructions:
`factualS`, `condExpGiven`, `propScore`, indicator/nuisance compositions, …) is registered
with Mathlib's `fun_prop` tactic. **For a goal whose head is `Measurable`, `AEMeasurable`,
`StronglyMeasurable` (including σ-explicit `Measurable[m]`), `Integrable`, or `Continuous`,
try bare `fun_prop` first** — before searching for lemma names.

- Use **bare** `fun_prop`. Do not use `fun_prop (disch := measurability)` file-wide: it buys
  almost nothing here and has caused deterministic heartbeat-timeout cascades. If a side
  goal (e.g. `MeasurableSet {x}`) blocks a composition, look for — or add — a
  side-condition-free corollary (`[MeasurableSingletonClass]`-style) instead.
- If the goal is behind a conjunction or a bundle hypothesis, destructure first
  (`obtain ⟨hmeas, -⟩ := hU`); `fun_prop` uses hypotheses only by `assumption`.
- `MemLp` goals are **not** covered (not a registered fun_prop property; `@[fun_prop]` on a
  MemLp lemma hard-errors). Neither are `IntegrableOn`/`IntervalIntegrable`. Cite lemmas by
  name there.
- What `fun_prop` will rightly NOT close: analytic content — a.e.-bounded products
  (`Integrable.bdd_mul` shapes), Cauchy–Schwarz/Hölder products, Fubini slices,
  assumption-gated integrability (`hA.integrable_Y`, overlap-dependent bounds). Those steps
  are mathematics, not plumbing; state them.
- `MeasurableSet` goals: use `measurability` (that is its remaining real domain; on
  function-property goals the `@[measurability]` attribute is just a deprecated alias for
  `@[fun_prop]`).

## Tagging discipline (write-time, like headline curation)

New side-condition lemmas are tagged **at birth**:

- Conclusion `Measurable/AEMeasurable/StronglyMeasurable/Integrable/Continuous` applied to a
  project construction, hypotheses at most function-properties/instances → `@[fun_prop]`.
- Structure fields with such statements tag directly:
  `attribute [fun_prop] MyStruct.field_lemma` — **provided the statement mentions the
  bundle** (`S.foo`). Fields/lemmas about structure *parameters* are rejected loudly
  (`DepGraph.meas`) or, for ∀-quantified fields, need a one-line projection lemma
  (`IIDSample.meas` pattern).
- σ-explicit families: every `MeasurableSpace.comap`-generated σ-algebra should ship its
  generator lemmas (`Measurable[S.sigmaX] S.factualX`, `measurable_jointValue_sigma`
  pattern) — these carry most of the automation in conditioning-heavy files.
- Assumption-bundle fields (e.g. `Assumptions.integrable_Y`-style) ARE tagged when files
  always hold the bundle in context (identification files do).

**Never tag:**

1. **Generic heads** — conclusions like `Integrable (fun p => p.1 * p.2) π` or bare
   projections: tried on every matching goal library-wide.
2. **Self-headed hypotheses** — a lemma whose hypotheses share its own conclusion head makes
   `fun_prop` loop: deterministic heartbeat-timeout with whole-file blast radius.
3. **MemLp / unregistered predicates** — hard error (self-enforcing).
4. **Transition shapes** — conclusion about a bare variable obtained from a non-fun_prop
   hypothesis (`IsUpperEnvZ S U → Measurable U`): silently accepted, never fires. This is
   the one *silent* failure mode; when in doubt, verify the tag closes a real goal
   ("fires in anger") before shipping it.
5. **Data-valued bundle fields** (`Integrable S.Y μ` where `Y` is data): unrecoverable by
   unification; leave name-called.

A tag is proof-layer metadata: adding one must never change any statement.

## Fin-literal spelling

In new code, write concrete `Fin n` indices as bare numeric literals (`S.factualS 0`), not
`⟨0, by decide⟩` — they are definitionally equal (OfNat), including under pattern matching.
Existing sites convert opportunistically, site by site; never by blanket rewrite (proofs that
pattern-match on the constructor form break).

## Deprecations

Renames and superseded helpers use `@[deprecated <replacement> (since := "YYYY-MM-DD")]`,
never silent removal. Migrate call sites in the same change where feasible. If a deprecated
lemma is in a `headline_theorems` sidecar, move the sidecar entry to the replacement.

## Simp sets (registered in `Causalean/Tactic/Attr.lean`)

Each set is one documented normal form; use `simp only [<set>, …]` (or `simp [<set>]` to
combine with the global simp set). All are loop-checked: idempotent on normal forms,
confluent with Mathlib's global simps.

- **`causal_defs_simps`** — unfold project definitions to their defining equations,
  replacing `unfold` chains (`propScore`, `condExpGiven`-adjacent constants, `P_Z`, CATE,
  …). Direction: away from the constant toward its body. Deliberately opaque: `obsKernel`
  (carries the `IsMarkovKernel` instance), `obsCondKernel`, `dgpSCM`.
- **`condexp_simps`** — unwrap the conditioning wrappers (`POVar`/`POCFBundle`
  `condExpGiven`, `condExpRatio`, `eventCondExp`) to Mathlib `condExp`/restricted
  integrals so the Mathlib API applies. Wrapper unfolding ONLY — condExp *linearity* is
  `=ᵐ[μ]`-valued and out of simp's reach; use the named `condExp_add/sub/…` lemmas.
- **`indicator_simps`** — carry indicator expressions to a single `Set.indicator` head and
  eliminate an indicator once the context decides its membership test; never introduces
  `ite` (an `ite` normal form strands goals on `Decidable`-instance mismatches). Honest
  scope note: Mathlib's global simps plus `by_cases h <;> simp [h]` already close most
  indicator goals — this set's value is the uniform idiom, especially for
  `POVar.indicator`'s call sites; it is a deletion candidate if adoption stays low.
- **`sum_algebra_simps`** — DISTRIBUTE normal form for finite-sum algebra: products and
  differences pushed through `∑` (so `Finset.sum_congr rfl … ring` sees `∑` at the head).
  Does not normalize inside a summand, and a domain fact `∑ f = c` must be collected back
  out by hand.

## Integral linearity: `integral_linearity`

**Normal form: `+`, `−`, negation, `•`, a factor that does not depend on the integration
variable, and finite sums all sit OUTSIDE the `∫`; integrability side conditions are
discharged from the context, then by `fun_prop`.** This is "by linearity of expectation" in
one word. Reach for it wherever a proof currently writes `rw [integral_sub h₁ h₂]` with
hand-named integrability witnesses.

It is a normalizer, not a finisher: follow it with `ring`, a domain `rw`, or `linarith` when
more than linearity is needed. It fails loudly (naming the normal form) if it can rewrite
nothing, so `first | integral_linearity | …` is safe.

What it deliberately leaves: `integral_congr_ae` and every `=ᵐ[μ]` step (that is
mathematics — prove the a.e. equality, `rw`, then normalize); `integral_const` (evaluation,
not distribution — it would drag `μ.real univ` into the goal, so apply it yourself, and with
`simp only` rather than `rw`, since normalizing can leave several constant integrals); the
merging (`←`) direction; set integrals, `lintegral` and `intervalIntegral`. Two situations
where it will not fire, both correct: the integrability witness is only reachable by
`Integrable.congr` from a `ring`-rearranged function (state the `have`), and the goal's other
side deliberately keeps an *un*-distributed integral behind a `let`/abbreviation (normalizing
overshoots it — keep the named lemma there).

## Conditional-expectation linearity: `condexp_linearity`

**Normal form: it is the goal's *other* side that fixes the answer — `condexp_linearity`
takes that side's `+`, `−`, unary `−` and `•` structure apart and pushes `condExp` inside to
match it, gluing the steps with `Filter.EventuallyEq.trans` and discharging the integrability
side conditions from the context, then by `fun_prop`.** Reach for it at any
`have h : μ[… ± … | m] =ᵐ[μ] μ[…|m] ± μ[…|m]` — the shape that today costs one `have` per
operator plus a chain of `Integrable.add`/`Integrable.sub` bookkeeping. Wrapper goals
(`POVar.condExpGiven`, `POCFBundle.condExpGiven`) are in scope: `condexp_simps` unwraps them
first. Either orientation of the goal works, and a `calc` step whose two sides are both
written out is a goal like any other.

Because a.e. equality is not a rewrite rule, this is a proof-building tactic, not a
normalizer: it closes the goal or fails. When it fails it names the blocking subterm and
leaves the goal untouched — there is never a partial rewrite to clean up.

An integrability witness that is only reachable as a *term* — a bundle field or an applied
∀-hypothesis (`As.integrable_Y d`, `hindD_integrable true`) — is invisible to both
`assumption` and `fun_prop`; hand it over in brackets, `filter_upwards`-style:
`condexp_linearity [As.integrable_Y d, As.integrable_Y z]`. This is the single most common
reason a call fails.

What it deliberately leaves: pull-out (`condExp_mul_of_stronglyMeasurable_*` — that carries a
measurability side condition and real analytic content), `condExp_congr_ae` (mathematics),
finite sums (use `condExp_finsetSum'`), and any goal stated as a plain `=` rather than
`=ᵐ[μ]` (`condExp_const`'s own shape — call it by name). A scalar multiple is recognised only
where the goal writes `•`; spelled `fun ω => c * g ω`, the product is treated as a leaf.

**Integrability-free linearity lemmas.** Where the *statement* is not written out — a
`have hsub := condExp_sub …` whose type is inferred — the tactic has nothing to follow, but
the integrability arguments can still be dropped: `condExp_add'`, `condExp_sub'`,
`condExp_finsetSum'` (`Causalean/Mathlib/MeasureTheory/CondExpLinearity.lean`) and the
wrapper analogues `POVar.condExpGiven_{add',sub',neg,const,finsetSum'}` /
`POCFBundle.condExpGiven_{add,sub,add',sub',smul,neg,const,finsetSum'}` take them as
`autoParam`s discharged by `fun_prop`. Same caveat as above: a witness that is a term rather
than a hypothesis is out of `fun_prop`'s reach, and there the unprimed lemma stays.

## Monotonicity: `gcongr`

For `≤`/`<` goals over integrals, sums, and products, try `gcongr` before hunting for
`mul_le_mul_of_nonneg_left`-style lemma names (the library has ~3,000 such hand-cited
steps). `gcongr` may return `Integrable`/positivity side goals — the blessed invocation is
`gcongr <;> first | fun_prop | assumption | positivity`.

## Planned (not yet available — do not reference in proofs)

Remaining items (`integral_linearity` and `condexp_linearity` have landed — see above; `dsep_decide` and the
positivity/gcongr extensions skipped). This section is replaced as they land.
