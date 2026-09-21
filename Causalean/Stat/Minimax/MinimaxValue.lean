/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The minimax value of a statistical decision problem

This module provides two sibling families for `inf over estimators of sup over the model
class of the risk`. Use `minimaxValueENNReal` for an `ℝ≥0∞` risk when empty or unbounded
problems must retain complete-lattice values, and use `minimaxValueReal` when rates and
bounds are stated in `ℝ`. The conversion `minimaxValueENNRealOfReal` lets a real-valued
pointwise risk use the `ℝ≥0∞` family, while its `toReal` lemmas recover the real family
under nonnegativity and finiteness assumptions.

An empty model class has worst-case risk zero, while an empty estimator class has minimax
value infinity. These are exactly the bottom and top conventions of the complete lattice
`ℝ≥0∞`.
-/

@[expose] public section

open scoped ENNReal

namespace Causalean.Stat

variable {E E' Θ Θ' : Sort*}

section ENNRealAPI

/-- Given an [estimator class](hyp:E), a [model class](hyp:Θ), a [nonnegative extended risk
for each estimator-model pair](hyp:risk), and an [estimator](hyp:e), the
[worst-case risk](goal) is the supremum of that estimator's risks over the model class. -/
noncomputable def worstCaseRiskENNReal (risk : E → Θ → ℝ≥0∞) (e : E) : ℝ≥0∞ :=
  ⨆ θ : Θ, risk e θ

/-- Use the [extended-nonnegative minimax value](goal) for an [estimator class](hyp:E), a
[model class](hyp:Θ), and an [extended risk](hyp:risk) when empty or unbounded problems
must retain their complete-lattice values. -/
noncomputable def minimaxValueENNReal (risk : E → Θ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ e : E, worstCaseRiskENNReal risk e

/-- Given a [real-valued risk](hyp:risk) and an [estimator](hyp:e), the [lifted worst-case
risk](goal) first sends every pointwise risk to its nonnegative extended value and then
takes the supremum over the model class. -/
noncomputable def worstCaseRiskOfReal (risk : E → Θ → ℝ) (e : E) : ℝ≥0∞ :=
  worstCaseRiskENNReal (fun e θ => ENNReal.ofReal (risk e θ)) e

/-- Use the [extended-nonnegative minimax value converted from a real risk](goal) for an
[estimator class](hyp:E), a [model class](hyp:Θ), and a [real risk](hyp:risk) when the
pointwise risk is real but complete-lattice minimax semantics are wanted. -/
noncomputable def minimaxValueENNRealOfReal (risk : E → Θ → ℝ) : ℝ≥0∞ :=
  minimaxValueENNReal (fun e θ => ENNReal.ofReal (risk e θ))

/-- For an [empty model class](hyp:Θ), every [extended risk](hyp:risk) has [zero worst-case
value](goal). -/
@[simp]
theorem worstCaseRiskENNReal_of_isEmpty_class [IsEmpty Θ]
    (risk : E → Θ → ℝ≥0∞) (e : E) :
    worstCaseRiskENNReal risk e = 0 := by
  simp [worstCaseRiskENNReal]

/-- For an [empty estimator class](hyp:E), every [extended risk](hyp:risk) has [infinite minimax
value](goal). -/
@[simp]
theorem minimaxValueENNReal_of_isEmpty_estimators [IsEmpty E]
    (risk : E → Θ → ℝ≥0∞) :
    minimaxValueENNReal risk = ∞ := by
  simp [minimaxValueENNReal]

/-- When the [model class has a unique element](hyp:Θ), the [worst-case extended risk is
the risk at that element](goal) for the given [risk](hyp:risk) and [estimator](hyp:e). -/
theorem worstCaseRiskENNReal_of_unique [Unique Θ]
    (risk : E → Θ → ℝ≥0∞) (e : E) :
    worstCaseRiskENNReal risk e = risk e default := by
  simp [worstCaseRiskENNReal]

/-- For a [nonnegative extended risk](hyp:risk), an [estimator](hyp:e), and a
[model](hyp:θ), the [model-specific risk is at most the worst-case risk](goal). -/
theorem le_worstCaseRiskENNReal {risk : E → Θ → ℝ≥0∞} (e : E) (θ : Θ) :
    risk e θ ≤ worstCaseRiskENNReal risk e :=
  le_iSup (risk e) θ

/-- If a [constant](hyp:c) bounds a fixed [estimator's](hyp:e) [risk](hyp:risk) at every
model as witnessed by [the uniform bound](hyp:h), then it [bounds the worst-case risk](goal). -/
theorem worstCaseRiskENNReal_le {risk : E → Θ → ℝ≥0∞} {e : E} {c : ℝ≥0∞}
    (h : ∀ θ, risk e θ ≤ c) :
    worstCaseRiskENNReal risk e ≤ c :=
  iSup_le h

/-- **Any admissible estimator is an upper bound.** For a [risk](hyp:risk) and an
[estimator](hyp:e), the [minimax value is at most that estimator's worst-case risk](goal). -/
theorem minimaxValueENNReal_le_worstCaseRisk {risk : E → Θ → ℝ≥0∞} (e : E) :
    minimaxValueENNReal risk ≤ worstCaseRiskENNReal risk e :=
  iInf_le _ e

/-- **A uniform estimator-wise bound is a lower bound.** If [every estimator's worst-case
risk is at least a constant](hyp:h), then [that constant is at most the minimax value](goal)
for the given [risk](hyp:risk) and [constant](hyp:c). -/
theorem le_minimaxValueENNReal {risk : E → Θ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ e, c ≤ worstCaseRiskENNReal risk e) :
    c ≤ minimaxValueENNReal risk :=
  le_iInf h

/-- **Two-point reduction to the minimax value.** For a [risk](hyp:risk), a
[candidate lower bound](hyp:c), and [two models](hyp:θ₀,θ₁), if [every estimator has at
least that much risk at one of the two models](hyp:htwo), then [the minimax value is at
least the candidate bound](goal). -/
theorem le_minimaxValueENNReal_of_two_point {risk : E → Θ → ℝ≥0∞} {c : ℝ≥0∞}
    (θ₀ θ₁ : Θ) (htwo : ∀ e, c ≤ max (risk e θ₀) (risk e θ₁)) :
    c ≤ minimaxValueENNReal risk := by
  apply le_minimaxValueENNReal
  intro e
  exact (htwo e).trans
    (max_le (le_worstCaseRiskENNReal e θ₀) (le_worstCaseRiskENNReal e θ₁))

/-- If a [map between model classes](hyp:φ) sends every [risk](hyp:risk) to no larger than
the corresponding [comparison risk](hyp:risk') as witnessed by [pointwise domination](hyp:hle),
then a fixed [estimator's](hyp:e) [worst-case risk is no larger](goal). -/
theorem worstCaseRiskENNReal_mono_class {risk : E → Θ → ℝ≥0∞}
    {risk' : E → Θ' → ℝ≥0∞} {e : E} (φ : Θ → Θ')
    (hle : ∀ θ, risk e θ ≤ risk' e (φ θ)) :
    worstCaseRiskENNReal risk e ≤ worstCaseRiskENNReal risk' e := by
  apply iSup_le
  intro θ
  exact (hle θ).trans (le_iSup (risk' e) (φ θ))

/-- **Comparison of two minimax problems.** If [every estimator in the second problem is
matched by one in the first with no larger worst-case risk](hyp:h), then the [first minimax
value is at most the second](goal) for the two [risks](hyp:risk,risk'). -/
theorem minimaxValueENNReal_le_minimaxValue {risk : E → Θ → ℝ≥0∞}
    {risk' : E' → Θ' → ℝ≥0∞}
    (h : ∀ e' : E', ∃ e : E,
      worstCaseRiskENNReal risk e ≤ worstCaseRiskENNReal risk' e') :
    minimaxValueENNReal risk ≤ minimaxValueENNReal risk' := by
  apply le_minimaxValueENNReal
  intro e'
  obtain ⟨e, he⟩ := h e'
  exact (minimaxValueENNReal_le_worstCaseRisk e).trans he

/-- **Restricting the model class cannot raise minimax risk.** If a [map between model
classes](hyp:φ) makes the first [risk](hyp:risk) no larger than the second [risk](hyp:risk')
under [pointwise domination](hyp:hle), then the [first minimax value is no larger](goal). -/
theorem minimaxValueENNReal_mono_class {risk : E → Θ → ℝ≥0∞}
    {risk' : E → Θ' → ℝ≥0∞} (φ : Θ → Θ')
    (hle : ∀ e θ, risk e θ ≤ risk' e (φ θ)) :
    minimaxValueENNReal risk ≤ minimaxValueENNReal risk' :=
  minimaxValueENNReal_le_minimaxValue fun e =>
    ⟨e, worstCaseRiskENNReal_mono_class φ (hle e)⟩

/-- The [worst-case extended risk](goal) for a given [risk](hyp:risk) and
[estimator](hyp:e) is the supremum of the set of attained risks. -/
theorem worstCaseRiskENNReal_eq_sSup_range (risk : E → Θ → ℝ≥0∞) (e : E) :
    worstCaseRiskENNReal risk e = sSup (Set.range (risk e)) :=
  rfl

/-- The [extended minimax value](goal) for a [risk](hyp:risk) is the infimum of the set of
attained worst-case risks. -/
theorem minimaxValueENNReal_eq_sInf_range (risk : E → Θ → ℝ≥0∞) :
    minimaxValueENNReal risk = sInf (Set.range (worstCaseRiskENNReal risk)) :=
  rfl

variable {A B : Type*}

/-- For an [admissibility predicate](hyp:Adm) and [extended risk](hyp:risk), the [minimax
value over the admissible subtype is the set infimum of its worst-case risks](goal). -/
theorem minimaxValueENNReal_subtype_eq_sInf_worstCaseRisk
    {Adm : A → Prop} (risk : A → Θ → ℝ≥0∞) :
    minimaxValueENNReal (fun (e : Subtype Adm) => risk e.1) =
      sInf {r : ℝ≥0∞ | ∃ e, Adm e ∧ r = worstCaseRiskENNReal risk e} := by
  rw [minimaxValueENNReal_eq_sInf_range]
  congr 1
  ext r
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

/-- For a [model-class predicate](hyp:Cls), an [extended risk](hyp:risk), and an
[estimator](hyp:e), the [worst-case risk over the subtype is the set supremum of its
attained risks](goal). -/
theorem worstCaseRiskENNReal_subtype_eq_sSup_setOf
    {Cls : B → Prop} (risk : A → B → ℝ≥0∞) (e : A) :
    worstCaseRiskENNReal (fun (a : A) (θ : Subtype Cls) => risk a θ.1) e =
      sSup {q : ℝ≥0∞ | ∃ θ, Cls θ ∧ q = risk e θ} := by
  change (⨆ θ : Subtype Cls, risk e θ.1) = _
  rw [iSup]
  congr 1
  ext q
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩

/-- For an [admissibility predicate](hyp:Adm), a [model-class predicate](hyp:Cls), and an
[extended risk](hyp:risk), the [subtype minimax value equals its nested set-infimum and
set-supremum spelling](goal). -/
theorem minimaxValueENNReal_subtype_eq_sInf_setOf (Adm : A → Prop) (Cls : B → Prop)
    (risk : A → B → ℝ≥0∞) :
    minimaxValueENNReal (fun (e : Subtype Adm) (θ : Subtype Cls) => risk e.1 θ.1) =
      sInf {r : ℝ≥0∞ | ∃ e, Adm e ∧
        r = sSup {q : ℝ≥0∞ | ∃ θ, Cls θ ∧ q = risk e θ}} := by
  rw [minimaxValueENNReal_subtype_eq_sInf_worstCaseRisk
    (risk := fun (a : A) (θ : Subtype Cls) => risk a θ.1)]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, worstCaseRiskENNReal_subtype_eq_sSup_setOf]

/-- If a fixed [estimator's](hyp:e) [worst-case extended risk](hyp:risk) is
[finite](hyp:hfinite), its [real value is the real supremum of the pointwise risks](goal). -/
theorem worstCaseRiskENNReal_toReal {risk : E → Θ → ℝ≥0∞} {e : E}
    (hfinite : worstCaseRiskENNReal risk e ≠ ∞) :
    (worstCaseRiskENNReal risk e).toReal = ⨆ θ, (risk e θ).toReal := by
  rw [worstCaseRiskENNReal, ENNReal.toReal_iSup]
  intro θ htop
  apply hfinite
  exact top_unique (htop ▸ le_iSup (risk e) θ)

/-- If [every estimator's worst-case extended risk is finite](hyp:hfinite), then the
[real value of the minimax risk is the real infimum of their real worst-case risks](goal)
for the given [risk](hyp:risk). -/
theorem minimaxValueENNReal_toReal {risk : E → Θ → ℝ≥0∞}
    (hfinite : ∀ e, worstCaseRiskENNReal risk e ≠ ∞) :
    (minimaxValueENNReal risk).toReal =
      ⨅ e, (worstCaseRiskENNReal risk e).toReal := by
  exact ENNReal.toReal_iInf hfinite

end ENNRealAPI

section RealAPI

/-- Given an [estimator class](hyp:E), a [model class](hyp:Θ), a [real-valued risk for each
estimator-model pair](hyp:risk), and an [estimator](hyp:e), the [worst-case risk](goal) is the
supremum, over all models in the class, of that estimator's risk.

If the class is empty, or if the estimator's risk is unbounded over the class, this is zero
by the real-supremum convention; `le_worstCaseRisk` therefore asks for an explicit bound. -/
noncomputable def worstCaseRiskReal (risk : E → Θ → ℝ) (e : E) : ℝ :=
  ⨆ θ : Θ, risk e θ

/-- Use the [real minimax value](goal) for an [estimator class](hyp:E), a
[model class](hyp:Θ), and a [real-valued risk](hyp:risk) when rates are stated in `ℝ` and
the required boundedness and nonemptiness side conditions are available.

Admissibility is expressed by the choice of the estimator index type, so instantiating it at a
subtype restricts the infimum to the estimators satisfying that subtype's condition.

If there are no admissible estimators this is zero by the real-infimum convention. -/
noncomputable def minimaxValueReal (risk : E → Θ → ℝ) : ℝ :=
  ⨅ e : E, worstCaseRiskReal risk e

/-- If a [real-valued risk](hyp:risk) is [nonnegative](hyp:hr) and its lifted
[worst-case risk for an estimator](hyp:e) is [finite](hyp:hfinite), then [taking the real
value of the standard extended worst-case risk recovers the real supremum](goal). -/
theorem worstCaseRiskENNReal_ofReal_toReal {risk : E → Θ → ℝ} {e : E}
    (hr : ∀ θ, 0 ≤ risk e θ)
    (hfinite : worstCaseRiskOfReal risk e ≠ ∞) :
    (worstCaseRiskOfReal risk e).toReal =
      worstCaseRiskReal risk e := by
  rw [worstCaseRiskOfReal, worstCaseRiskENNReal_toReal hfinite]
  simp_rw [ENNReal.toReal_ofReal (hr _)]
  rfl

/-- If a [real-valued risk](hyp:risk) is [nonnegative](hyp:hr) and [every lifted
worst-case risk is finite](hyp:hfinite), then [taking the real value of the standard
extended minimax risk recovers the real minimax infimum](goal). -/
theorem minimaxValueENNRealOfReal_toReal {risk : E → Θ → ℝ}
    (hr : ∀ e θ, 0 ≤ risk e θ)
    (hfinite : ∀ e, worstCaseRiskOfReal risk e ≠ ∞) :
    (minimaxValueENNRealOfReal risk).toReal =
      minimaxValueReal risk := by
  unfold minimaxValueENNRealOfReal
  rw [minimaxValueENNReal_toReal (fun e => by
    simpa [worstCaseRiskOfReal] using hfinite e)]
  unfold minimaxValueReal
  congr 1
  funext e
  change (worstCaseRiskOfReal risk e).toReal = worstCaseRiskReal risk e
  exact worstCaseRiskENNReal_ofReal_toReal (hr e) (hfinite e)

/-- If a fixed [estimator's real-valued risk is bounded above](hyp:hbdd), then its
[lifted worst-case risk is finite](goal) for the given [risk](hyp:risk) and
[estimator](hyp:e). -/
theorem worstCaseRiskOfReal_ne_top_of_bddAbove {risk : E → Θ → ℝ} {e : E}
    (hbdd : BddAbove (Set.range (risk e))) :
    worstCaseRiskOfReal risk e ≠ ∞ := by
  obtain ⟨c, hc⟩ := hbdd
  apply ne_of_lt
  exact (worstCaseRiskENNReal_le fun θ =>
    ENNReal.ofReal_le_ofReal (hc ⟨θ, rfl⟩)).trans_lt ENNReal.ofReal_lt_top

/-- If a [real-valued risk is nonnegative](hyp:hr) and [bounded above for every
estimator](hyp:hbdd), then [the real value of its lifted minimax risk equals the legacy real
infimum-supremum expression](goal) for the given [risk](hyp:risk). -/
theorem minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove {risk : E → Θ → ℝ}
    (hr : ∀ e θ, 0 ≤ risk e θ)
    (hbdd : ∀ e, BddAbove (Set.range (risk e))) :
    (minimaxValueENNRealOfReal risk).toReal = minimaxValueReal risk :=
  minimaxValueENNRealOfReal_toReal hr fun e =>
    worstCaseRiskOfReal_ne_top_of_bddAbove (hbdd e)

/-- Use `worstCaseRiskReal` instead of this [legacy real worst-case risk](goal) for an
[estimator class](hyp:E), a [model class](hyp:Θ), a [real-valued risk](hyp:risk), and an
[estimator](hyp:e) because this name is retained only for compatibility. -/
@[deprecated worstCaseRiskReal (since := "2026-09-17")]
noncomputable def worstCaseRisk (risk : E → Θ → ℝ) (e : E) : ℝ :=
  ⨆ θ : Θ, risk e θ

/-- Use `minimaxValueReal` instead of this [legacy real minimax value](goal) for an
[estimator class](hyp:E), a [model class](hyp:Θ), and a [real-valued risk](hyp:risk)
because this name is retained only for compatibility. -/
@[deprecated minimaxValueReal (since := "2026-09-17")]
noncomputable def minimaxValueRealLegacy (risk : E → Θ → ℝ) : ℝ :=
  ⨅ e : E, worstCaseRiskReal risk e

section Degenerate

/-- Over an empty model class the worst-case risk of every estimator is zero. -/
@[simp]
theorem worstCaseRisk_of_isEmpty_class [IsEmpty Θ] (risk : E → Θ → ℝ) (e : E) :
    worstCaseRiskReal risk e = 0 :=
  Real.iSup_of_isEmpty _

/-- When no estimator is admissible the minimax value is zero, so no positive lower bound on
the minimax value can hold vacuously. -/
@[simp]
theorem minimaxValue_of_isEmpty_estimators [IsEmpty E] (risk : E → Θ → ℝ) :
    minimaxValueReal risk = 0 :=
  Real.iInf_of_isEmpty _

/-- When the model class consists of a single law, the worst-case risk is just the risk at
that law. This covers decision problems that minimise a functional of the estimator alone,
with no adversarial choice of model. -/
theorem worstCaseRisk_of_unique [Unique Θ] (risk : E → Θ → ℝ) (e : E) :
    worstCaseRiskReal risk e = risk e default :=
  ciSup_unique

end Degenerate

section Nonneg

/-- A worst-case risk is nonnegative as soon as the risk is, with no boundedness or
nonemptiness caveat: an empty class or an unbounded risk both give the value zero. -/
theorem worstCaseRisk_nonneg {risk : E → Θ → ℝ} {e : E} (hr : ∀ θ, 0 ≤ risk e θ) :
    0 ≤ worstCaseRiskReal risk e :=
  Real.iSup_nonneg hr

/-- The minimax value of a nonnegative-risk problem is nonnegative, with no boundedness or
nonemptiness caveat. Squared-error, absolute-error and regret losses all qualify. -/
theorem minimaxValue_nonneg {risk : E → Θ → ℝ} (hr : ∀ e θ, 0 ≤ risk e θ) :
    0 ≤ minimaxValueReal risk :=
  Real.iInf_nonneg fun e => worstCaseRisk_nonneg (hr e)

/-- For a nonnegative risk the worst-case risks are bounded below by zero, which is the
side condition the infimum over estimators needs. -/
theorem bddBelow_range_worstCaseRisk {risk : E → Θ → ℝ} (hr : ∀ e θ, 0 ≤ risk e θ) :
    BddBelow (Set.range (worstCaseRiskReal risk)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact worstCaseRisk_nonneg (hr e)

end Nonneg

section Bounds

/-- The risk at any single model in the class is at most the estimator's worst-case risk,
provided that estimator's risk is bounded over the class. -/
theorem le_worstCaseRisk {risk : E → Θ → ℝ} {e : E}
    (hbdd : BddAbove (Set.range (risk e))) (θ : Θ) :
    risk e θ ≤ worstCaseRiskReal risk e :=
  le_ciSup hbdd θ

/-- A bound holding at every model in a nonempty class bounds the worst-case risk. -/
theorem worstCaseRisk_le [Nonempty Θ] {risk : E → Θ → ℝ} {e : E} {c : ℝ}
    (h : ∀ θ, risk e θ ≤ c) :
    worstCaseRiskReal risk e ≤ c :=
  ciSup_le h

/-- **Any admissible estimator is an upper bound.** Exhibiting one estimator and bounding
its worst-case risk bounds the minimax value, which is how achievability half of a minimax
rate is certified. The hypothesis rules out a worst-case risk that decreases without bound
across the estimator family. -/
theorem minimaxValue_le_worstCaseRisk {risk : E → Θ → ℝ}
    (hbdd : BddBelow (Set.range (worstCaseRiskReal risk))) (e : E) :
    minimaxValueReal risk ≤ worstCaseRiskReal risk e :=
  ciInf_le hbdd e

/-- For a nonnegative risk, any admissible estimator is an upper bound on the minimax value
with no further side condition, since zero already bounds the worst-case risks below. -/
theorem minimaxValue_le_worstCaseRisk_of_nonneg {risk : E → Θ → ℝ}
    (hr : ∀ e θ, 0 ≤ risk e θ) (e : E) :
    minimaxValueReal risk ≤ worstCaseRiskReal risk e :=
  minimaxValue_le_worstCaseRisk (bddBelow_range_worstCaseRisk hr) e

/-- **A bound uniform over admissible estimators is a lower bound.** If every admissible
estimator has worst-case risk at least `c`, the minimax value is at least `c`. This is the
converse half of a minimax rate; it needs at least one admissible estimator to exist,
since otherwise the minimax value is zero by convention. -/
theorem le_minimaxValue [Nonempty E] {risk : E → Θ → ℝ} {c : ℝ}
    (h : ∀ e, c ≤ worstCaseRiskReal risk e) :
    c ≤ minimaxValueReal risk :=
  le_ciInf h

/-- **Two-point reduction to the minimax value.** Fix two models `θ₀` and `θ₁` from the
parameter class. If [every estimator's risk is bounded above across the parameter
class](hyp:hbdd) and [for each estimator, the larger of its risks at the two fixed models
is at least `c`](hyp:htwo), then [the minimax value of the problem is at least `c`](goal).

This is the step that turns a Le Cam or divergence-based testing bound, which produces
exactly such a two-model statement, into a statement about the minimax value. Each
estimator's risk must be bounded over the class for its supremum to be meaningful. -/
theorem le_minimaxValue_of_two_point [Nonempty E] {risk : E → Θ → ℝ} {c : ℝ} (θ₀ θ₁ : Θ)
    (hbdd : ∀ e, BddAbove (Set.range (risk e)))
    (htwo : ∀ e, c ≤ max (risk e θ₀) (risk e θ₁)) :
    c ≤ minimaxValueReal risk :=
  le_minimaxValue fun e =>
    (htwo e).trans (max_le (le_worstCaseRisk (hbdd e) θ₀) (le_worstCaseRisk (hbdd e) θ₁))

end Bounds

section Restriction

/-- Comparing two model classes at a fixed estimator: if every model of the first class is
matched, through the map, by a model of the second class whose risk is at least as large,
the worst-case risk over the first class is at most that over the second. The second class
must bound the estimator's risk, and the first must be nonempty; see
`worstCaseRisk_mono_class_of_nonneg` for the version that drops the nonemptiness. -/
theorem worstCaseRisk_mono_class [Nonempty Θ] {risk : E → Θ → ℝ} {risk' : E → Θ' → ℝ}
    {e : E} (φ : Θ → Θ')
    (hbdd : BddAbove (Set.range (risk' e)))
    (hle : ∀ θ, risk e θ ≤ risk' e (φ θ)) :
    worstCaseRiskReal risk e ≤ worstCaseRiskReal risk' e :=
  worstCaseRisk_le fun θ => (hle θ).trans (le_worstCaseRisk hbdd (φ θ))

/-- Version of `worstCaseRisk_mono_class` for a nonnegative larger risk: no nonemptiness
assumption on the smaller class is needed, because an empty class contributes worst-case
risk zero, which the larger nonnegative worst-case risk already dominates. -/
theorem worstCaseRisk_mono_class_of_nonneg {risk : E → Θ → ℝ} {risk' : E → Θ' → ℝ}
    {e : E} (φ : Θ → Θ')
    (hbdd : BddAbove (Set.range (risk' e))) (hr' : ∀ θ', 0 ≤ risk' e θ')
    (hle : ∀ θ, risk e θ ≤ risk' e (φ θ)) :
    worstCaseRiskReal risk e ≤ worstCaseRiskReal risk' e := by
  cases isEmpty_or_nonempty Θ with
  | inl _ => simpa using worstCaseRisk_nonneg hr'
  | inr _ => exact worstCaseRisk_mono_class φ hbdd hle

/-- **Comparison of two minimax problems.** If every admissible estimator of the second
problem is matched by an estimator of the first whose worst-case risk is no larger, the
first minimax value is at most the second. Both restricting the model class and enlarging
the estimator family are instances; the boundedness hypothesis is on the first problem's
worst-case risks, and the second problem must have at least one estimator. -/
theorem minimaxValue_le_minimaxValue [Nonempty E'] {risk : E → Θ → ℝ} {risk' : E' → Θ' → ℝ}
    (hbdd : BddBelow (Set.range (worstCaseRiskReal risk)))
    (h : ∀ e' : E', ∃ e : E, worstCaseRiskReal risk e ≤ worstCaseRiskReal risk' e') :
    minimaxValueReal risk ≤ minimaxValueReal risk' := by
  refine le_minimaxValue fun e' => ?_
  obtain ⟨e, he⟩ := h e'
  exact (minimaxValue_le_worstCaseRisk hbdd e).trans he

/-- **Restricting the model class cannot raise the minimax value.** If each model of the
smaller class sits, through the map, inside the larger class with no larger risk, then the
minimax value over the smaller class is at most the minimax value over the larger one — the
same estimators face a weaker adversary. This is the standard step that transfers a
published converse proved on a convenient subclass to the full class. -/
theorem minimaxValue_mono_class [Nonempty E] [Nonempty Θ] {risk : E → Θ → ℝ}
    {risk' : E → Θ' → ℝ} (φ : Θ → Θ')
    (hbddBelow : BddBelow (Set.range (worstCaseRiskReal risk)))
    (hbdd : ∀ e, BddAbove (Set.range (risk' e)))
    (hle : ∀ e θ, risk e θ ≤ risk' e (φ θ)) :
    minimaxValueReal risk ≤ minimaxValueReal risk' :=
  minimaxValue_le_minimaxValue hbddBelow
    fun e => ⟨e, worstCaseRisk_mono_class φ (hbdd e) (hle e)⟩

/-- For a map `φ` from the parameter class of the first problem to that of the
second, if [the first problem's risk is nonnegative](hyp:hr), [the second problem's risk is
nonnegative](hyp:hr'), [each estimator's risk is bounded above across the second parameter
class](hyp:hbdd), and [the first risk at any model is dominated by the second risk at that
model's image under `φ`](hyp:hle), then [the minimax value of the first problem is at most
that of the second](goal).

Version of `minimaxValue_mono_class` for nonnegative risks. Nonnegativity supplies both
the lower bound on the smaller problem's worst-case risks and the empty-class case, so the
only remaining side condition is that each estimator's risk be bounded over the larger
class. Squared-error and absolute-error losses meet the nonnegativity hypotheses by
inspection. -/
theorem minimaxValue_mono_class_of_nonneg [Nonempty E] {risk : E → Θ → ℝ}
    {risk' : E → Θ' → ℝ} (φ : Θ → Θ')
    (hr : ∀ e θ, 0 ≤ risk e θ) (hr' : ∀ e θ', 0 ≤ risk' e θ')
    (hbdd : ∀ e, BddAbove (Set.range (risk' e)))
    (hle : ∀ e θ, risk e θ ≤ risk' e (φ θ)) :
    minimaxValueReal risk ≤ minimaxValueReal risk' :=
  minimaxValue_le_minimaxValue (bddBelow_range_worstCaseRisk hr)
    fun e => ⟨e, worstCaseRisk_mono_class_of_nonneg φ (hbdd e) (hr' e) (hle e)⟩

end Restriction

section SetSpelling

/-- The worst-case risk is the supremum of the set of risks the estimator attains across the
class. Rewriting handle for arguments phrased on the set of attained risks. -/
theorem worstCaseRisk_eq_sSup_range (risk : E → Θ → ℝ) (e : E) :
    worstCaseRiskReal risk e = sSup (Set.range (risk e)) :=
  rfl

/-- The minimax value is the infimum of the set of worst-case risks the admissible
estimators attain. Rewriting handle for arguments phrased on that set. -/
theorem minimaxValue_eq_sInf_range (risk : E → Θ → ℝ) :
    minimaxValueReal risk = sInf (Set.range (worstCaseRiskReal risk)) :=
  rfl

variable {A B : Type*}

/-- The minimax value over the estimators satisfying an admissibility condition, written as
the infimum of the set of worst-case risks the admissible estimators attain. This is the
bridge for developments that state admissibility by a predicate rather than by a subtype
while leaving the inner supremum as it stands. -/
theorem minimaxValue_subtype_eq_sInf_worstCaseRisk {Adm : A → Prop} (risk : A → Θ → ℝ) :
    minimaxValueReal (fun (e : Subtype Adm) => risk e.1)
      = sInf {r : ℝ | ∃ e, Adm e ∧ r = worstCaseRiskReal risk e} := by
  rw [minimaxValue_eq_sInf_range]
  congr 1
  ext r
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

/-- The worst-case risk over a class carved out by a membership condition, written as the
supremum of the set of risks attained on the class. This is the bridge to the spelling that
states the class by a predicate rather than by a subtype. -/
theorem worstCaseRisk_subtype_eq_sSup_setOf {Cls : B → Prop} (risk : A → B → ℝ) (e : A) :
    worstCaseRiskReal (fun (a : A) (θ : Subtype Cls) => risk a θ.1) e
      = sSup {q : ℝ | ∃ θ, Cls θ ∧ q = risk e θ} := by
  change (⨆ θ : Subtype Cls, risk e θ.1) = _
  rw [iSup]
  congr 1
  ext q
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩

/-- The minimax value over an admissible-estimator condition and a model-class condition,
written with set comprehensions instead of subtypes: the infimum of the set of worst-case
risks attained by admissible estimators, each of which is the supremum of the set of risks
attained on the class. Runs that spell their minimax risk this way rewrite with this lemma
and then use the rest of this file. -/
theorem minimaxValue_subtype_eq_sInf_setOf (Adm : A → Prop) (Cls : B → Prop)
    (risk : A → B → ℝ) :
    minimaxValueReal (fun (e : Subtype Adm) (θ : Subtype Cls) => risk e.1 θ.1)
      = sInf {r : ℝ | ∃ e, Adm e ∧ r = sSup {q : ℝ | ∃ θ, Cls θ ∧ q = risk e θ}} := by
  rw [minimaxValue_subtype_eq_sInf_worstCaseRisk
    (risk := fun (a : A) (θ : Subtype Cls) => risk a θ.1)]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, worstCaseRisk_subtype_eq_sSup_setOf]

end SetSpelling

end RealAPI

end Causalean.Stat
