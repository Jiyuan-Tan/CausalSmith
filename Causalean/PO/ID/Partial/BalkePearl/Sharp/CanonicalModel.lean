/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: sharpness construction

This file builds the canonical PO model that realises an arbitrary
feasible latent table π for a Balke-Pearl IV system.

Given `(P, S)` and a feasible π, we construct `(P', S')` such that
* `S'.cellProb = S.cellProb`,
* `S'.ATE = BPObjective π`,
* `S'.BaseAssumptions` holds.

The model has
* `V' := Fin 3` (0=Z, 1=D, 2=Y)
* `X' v := Bool` for each v
* `Ω' := Bool × (Bool × Bool × Bool × Bool)` — `(z, d0, d1, y0, y1)`
* `μ' := μ_Z ⊗ π_meas`
* `eval r ω` cascades through `Z → D → Y`, using interventions when their
  target variables are assigned and otherwise reading the latent response type.
-/

module
public import Causalean.PO.ID.Partial.BalkePearl.LatentTable
public import Causalean.PO.ID.Partial.BalkePearl.Main

/-! # Canonical Balke-Pearl model

This part defines the finite canonical response-type model, its probability measure and
potential-outcome system, and verifies consistency of its intervention evaluator. -/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBalkePearlSharp

/-! ### Canonical sample space -/

/-- The [canonical sample space](goal) consists of one observed binary instrument value together with four binary latent response values: treatment under each instrument value and outcome under each treatment value. -/
abbrev SOmega : Type := Bool × (Bool × Bool × Bool × Bool)

/-- The [canonical variable-index set](goal) has exactly three elements, representing respectively the instrument, treatment, and outcome. -/
abbrev SV : Type := Fin 3

/-- The [canonical measurement-scale assignment](goal) assigns the binary scale to each of the three canonical variables. -/
abbrev SX : SV → Type := fun _ => Bool

/-! ### Canonical eval map -/

/-- For [a binary instrument value](hyp:z) and [a canonical sample-space point](hyp:ω), the [latent treatment response](goal) is that point's treatment response under the specified instrument value. -/
def dArmω (z : Bool) (ω : SOmega) : Bool :=
  if z then ω.2.2.1 else ω.2.1

/-- For [a binary treatment value](hyp:d) and [a canonical sample-space point](hyp:ω), the [latent outcome response](goal) is that point's outcome response under the specified treatment value. -/
def yArmω (d : Bool) (ω : SOmega) : Bool :=
  if d then ω.2.2.2.2 else ω.2.2.2.1

/-- For [an intervention regime on the canonical instrument, treatment, and outcome variables](hyp:r), [a canonical sample-space point](hyp:ω), and [one of those variables](hyp:v), the [canonical evaluator](goal) returns the variable's assigned value when the regime intervenes on it; otherwise it returns the point's instrument value, its treatment response to the resulting instrument value, or its outcome response to the resulting treatment value, respectively. [For an intervened variable](step:1), the assigned value is used; for the instrument, the observed coordinate is used; for the treatment, the treatment response is used; and for the outcome, the outcome response is used. -/
noncomputable def eval (r : Regime SV SX) (ω : SOmega) : ∀ v : SV, SX v := by
  classical
  intro v
  exact
    if hv : v ∈ r.target then r.assign v hv
    else
      match v with
      | ⟨0, _⟩ => ω.1
      | ⟨1, _⟩ =>
          let zEff : Bool :=
            if h0 : (⟨0, by decide⟩ : SV) ∈ r.target
              then r.assign _ h0 else ω.1
          dArmω zEff ω
      | ⟨2, _⟩ =>
          let zEff : Bool :=
            if h0 : (⟨0, by decide⟩ : SV) ∈ r.target
              then r.assign _ h0 else ω.1
          let dEff : Bool :=
            if h1 : (⟨1, by decide⟩ : SV) ∈ r.target
              then r.assign _ h1 else dArmω zEff ω
          yArmω dEff ω

/-- The canonical evaluator is measurable under every intervention regime. -/
@[fun_prop]
lemma measurable_eval (r : Regime SV SX) : Measurable (eval r) := by
  exact measurable_of_finite _

/-- The Z-coordinate `eval r ω 0`: assignment if intervened on, else `ω.1`. -/
lemma eval_zero (r : Regime SV SX) (ω : SOmega) :
    eval r ω ⟨0, by decide⟩ =
      (if h : (⟨0, by decide⟩ : SV) ∈ r.target then r.assign _ h else ω.1) := rfl

/-- The D-coordinate (raw). -/
lemma eval_one_raw (r : Regime SV SX) (ω : SOmega) :
    eval r ω ⟨1, by decide⟩ =
      (if h : (⟨1, by decide⟩ : SV) ∈ r.target then r.assign _ h
        else dArmω (if h0 : (⟨0, by decide⟩ : SV) ∈ r.target
                      then r.assign _ h0 else ω.1) ω) := rfl

/-- The Y-coordinate (raw). -/
lemma eval_two_raw (r : Regime SV SX) (ω : SOmega) :
    eval r ω ⟨2, by decide⟩ =
      (if h : (⟨2, by decide⟩ : SV) ∈ r.target then r.assign _ h
        else
          yArmω (if h1 : (⟨1, by decide⟩ : SV) ∈ r.target
                   then r.assign _ h1
                   else dArmω (if h0 : (⟨0, by decide⟩ : SV) ∈ r.target
                                 then r.assign _ h0 else ω.1) ω) ω) := rfl

/-- The D-coordinate folded via `eval_zero`. -/
lemma eval_one (r : Regime SV SX) (ω : SOmega) :
    eval r ω ⟨1, by decide⟩ =
      (if h : (⟨1, by decide⟩ : SV) ∈ r.target then r.assign _ h
        else dArmω (eval r ω ⟨0, by decide⟩) ω) := by
  rw [eval_one_raw]; rfl

/-- The Y-coordinate folded via `eval_one`. -/
lemma eval_two (r : Regime SV SX) (ω : SOmega) :
    eval r ω ⟨2, by decide⟩ =
      (if h : (⟨2, by decide⟩ : SV) ∈ r.target then r.assign _ h
        else yArmω (eval r ω ⟨1, by decide⟩) ω) := by
  rw [eval_two_raw]; rfl

private lemma eval_zero_of_mem (r : Regime SV SX) (ω : SOmega)
    (h : (⟨0, by decide⟩ : SV) ∈ r.target) :
    eval r ω ⟨0, by decide⟩ = r.assign _ h := by
  exact (eval_zero r ω).trans (dif_pos h)

private lemma eval_zero_of_not_mem (r : Regime SV SX) (ω : SOmega)
    (h : (⟨0, by decide⟩ : SV) ∉ r.target) :
    eval r ω ⟨0, by decide⟩ = ω.1 := by
  exact (eval_zero r ω).trans (dif_neg h)

/-- Given [a regime and canonical state](hyp:r,ω), if [the first variable is intervened on](hyp:h),
then [the canonical evaluator returns that variable's assigned intervention value](goal). -/
lemma eval_one_of_mem (r : Regime SV SX) (ω : SOmega)
    (h : (⟨1, by decide⟩ : SV) ∈ r.target) :
    eval r ω ⟨1, by decide⟩ = r.assign _ h := by
  exact (eval_one r ω).trans (dif_pos h)

private lemma eval_one_of_not_mem (r : Regime SV SX) (ω : SOmega)
    (h : (⟨1, by decide⟩ : SV) ∉ r.target) :
    eval r ω ⟨1, by decide⟩ = dArmω (eval r ω ⟨0, by decide⟩) ω := by
  exact (eval_one r ω).trans (dif_neg h)

/-- Given [a regime and canonical state](hyp:r,ω), if [the second variable is not intervened on](hyp:h),
then [the canonical evaluator returns the state's outcome arm indexed by the evaluated first variable](goal). -/
lemma eval_two_of_not_mem (r : Regime SV SX) (ω : SOmega)
    (h : (⟨2, by decide⟩ : SV) ∉ r.target) :
    eval r ω ⟨2, by decide⟩ = yArmω (eval r ω ⟨1, by decide⟩) ω := by
  exact (eval_two r ω).trans (dif_neg h)

/-! ### Canonical measures

We work with `S` and `π` from the surrounding context. -/

variable {P : POSystem} (S : POBalkePearlSystem P)

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system on it](hyp:S), the [canonical instrument marginal measure](goal) assigns to each binary instrument value the probability of that system's corresponding factual instrument event. -/
noncomputable def zMeasure : Measure Bool :=
  ∑ z : Bool, P.μ (S.zEvent z) • Measure.dirac z

/-- For [a table of real weights indexed by the four binary latent response values](hyp:π), the [latent-table measure](goal) is the discrete measure that places at each response type the nonnegative extended-real part of its table weight. -/
noncomputable def piMeasure (π : Bool → Bool → Bool → Bool → ℝ) :
    Measure (Bool × Bool × Bool × Bool) :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    ENNReal.ofReal (π d0 d1 y0 y1) • Measure.dirac (d0, d1, y0, y1)

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), and [a table of real weights indexed by the four binary latent response values](hyp:π), the [canonical product measure](goal) is the product of the system's instrument marginal measure and the latent-table measure. -/
noncomputable def canonicalMeasure (π : Bool → Bool → Bool → Bool → ℝ) :
    Measure SOmega :=
  (zMeasure S).prod (piMeasure π)

/-! ### Probability instance for canonicalMeasure -/

/-- `zMeasure S` has total mass 1. -/
lemma zMeasure_univ : (zMeasure S) Set.univ = 1 := by
  unfold zMeasure
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, mul_one]
  have hpart : (S.zEvent false) ∪ (S.zEvent true) = Set.univ := by
    ext ω
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    cases h : S.zVar.factual ω
    · exact Or.inl h
    · exact Or.inr h
  have hdisj : Disjoint (S.zEvent false) (S.zEvent true) := by
    rw [Set.disjoint_left]; intro ω h1 h2
    have h1' : S.zVar.factual ω = false := h1
    have h2' : S.zVar.factual ω = true := h2
    rw [h1'] at h2'; exact Bool.false_ne_true h2'
  have hmeas_t : MeasurableSet (S.zEvent true) := S.measurableSet_zEvent _
  have hadd : P.μ (S.zEvent false) + P.μ (S.zEvent true) = P.μ Set.univ := by
    rw [← measure_union hdisj hmeas_t, hpart]
  rw [Fintype.sum_bool, add_comm, hadd, measure_univ]

/-- For [a potential-outcomes system](hyp:P) and [a binary Balke--Pearl system
on that system](hyp:S), [the canonical marginal distribution of the binary
instrument](goal) is a probability measure.

The original instrument marginal is a probability measure. -/
instance instIsProbZMeasure : IsProbabilityMeasure (zMeasure S) :=
  ⟨zMeasure_univ S⟩

/-- `piMeasure π` has total mass 1 when π has nonneg entries summing to 1. -/
lemma piMeasure_univ_of_feasible {π : Bool → Bool → Bool → Bool → ℝ}
    (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        π d0 d1 y0 y1 = 1) :
    (piMeasure π) Set.univ = 1 := by
  unfold piMeasure
  -- Reduce iterated sum measure applied to univ to iterated sum of weights.
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, mul_one]
  -- Now goal: ∑ d0 ∑ d1 ∑ y0 ∑ y1, ENNReal.ofReal (π d0 d1 y0 y1) = 1
  have h1 : ∀ d0 d1 y0,
      ∑ y1 : Bool, ENNReal.ofReal (π d0 d1 y0 y1)
        = ENNReal.ofReal (∑ y1 : Bool, π d0 d1 y0 y1) := by
    intros d0 d1 y0
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro y1 _; exact hπ_nn _ _ _ _
  have h2 : ∀ d0 d1,
      ∑ y0 : Bool, ∑ y1 : Bool, ENNReal.ofReal (π d0 d1 y0 y1)
        = ENNReal.ofReal (∑ y0 : Bool, ∑ y1 : Bool, π d0 d1 y0 y1) := by
    intros d0 d1
    simp_rw [h1]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro y0 _; exact Finset.sum_nonneg fun y1 _ => hπ_nn _ _ _ _
  have h3 : ∀ d0,
      ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, ENNReal.ofReal (π d0 d1 y0 y1)
        = ENNReal.ofReal (∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, π d0 d1 y0 y1) := by
    intros d0
    simp_rw [h2]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro d1 _
    exact Finset.sum_nonneg fun y0 _ =>
      Finset.sum_nonneg fun y1 _ => hπ_nn _ _ _ _
  have h4 : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        ENNReal.ofReal (π d0 d1 y0 y1)
      = ENNReal.ofReal (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
          π d0 d1 y0 y1) := by
    simp_rw [h3]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro d0 _
    exact Finset.sum_nonneg fun d1 _ =>
      Finset.sum_nonneg fun y0 _ =>
        Finset.sum_nonneg fun y1 _ => hπ_nn _ _ _ _
  rw [h4, hπ_sum]
  simp

/-- A nonnegative latent table that sums to one induces a probability measure. -/
lemma instIsProbPiMeasure {π : Bool → Bool → Bool → Bool → ℝ}
    (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        π d0 d1 y0 y1 = 1) :
    IsProbabilityMeasure (piMeasure π) :=
  ⟨piMeasure_univ_of_feasible hπ_nn hπ_sum⟩

/-! ### Canonical POSystem -/

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on
that system](hyp:S), and [a table of real weights indexed by the four binary
latent response values](hyp:π), if the probability measure induced by that
latent table is a probability measure, then [the canonical product
measure combining the instrument marginal and latent-table measure](goal) is a
probability measure.

The product of the instrument marginal and latent-table measure is a probability
measure. -/
instance instIsProbCanonicalMeasure {π : Bool → Bool → Bool → Bool → ℝ}
    [IsProbabilityMeasure (piMeasure π)] :
    IsProbabilityMeasure (canonicalMeasure S π) := by
  unfold canonicalMeasure; infer_instance

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), [a table of real weights indexed by the four binary latent response values](hyp:π), [the condition that every table entry is nonnegative](hyp:hπ_nn), and [the condition that all table entries sum to one](hyp:hπ_sum), the [canonical potential-outcomes system](goal) has the canonical variables, binary measurement scales, canonical sample space, canonical product probability measure, and canonical evaluator. [Its probability-measure property](step:1) follows from the two conditions on the latent table. -/
noncomputable def canonicalPOSystem (π : Bool → Bool → Bool → Bool → ℝ)
    (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        π d0 d1 y0 y1 = 1) :
    POSystem :=
  letI : IsProbabilityMeasure (piMeasure π) :=
    instIsProbPiMeasure hπ_nn hπ_sum
  { V := SV
    X := SX
    Ω := SOmega
    μ := canonicalMeasure S π
    eval := eval
    measurable_eval := measurable_eval }

/-! ### Canonical POBalkePearlSystem -/

/-- For [a potential-outcomes system](hyp:P), [a binary Balke--Pearl system on it](hyp:S), [a table of real weights indexed by the four binary latent response values](hyp:π), [the condition that every table entry is nonnegative](hyp:hπ_nn), and [the condition that all table entries sum to one](hyp:hπ_sum), the [canonical Balke--Pearl system](goal) designates the first, second, and third canonical variables as instrument, treatment, and outcome, respectively. -/
noncomputable def canonicalBP (π : Bool → Bool → Bool → Bool → ℝ)
    (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        π d0 d1 y0 y1 = 1) :
    POBalkePearlSystem (canonicalPOSystem S π hπ_nn hπ_sum) where
  Z := ⟨0, by decide⟩
  D := ⟨1, by decide⟩
  Y := ⟨2, by decide⟩
  hZbool := MeasurableEquiv.refl Bool
  hDbool := MeasurableEquiv.refl Bool
  hYbool := MeasurableEquiv.refl Bool
  hZD := by intro h; exact absurd (Fin.mk.inj_iff.mp h) (by decide)
  hZY := by intro h; exact absurd (Fin.mk.inj_iff.mp h) (by decide)
  hDY := by intro h; exact absurd (Fin.mk.inj_iff.mp h) (by decide)

/-! ### Verifying BaseAssumptions on the canonical system

We work with abbreviations for the canonical PO system and BP system. -/

section BaseAssumptions

variable (π : Bool → Bool → Bool → Bool → ℝ)
  (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
  (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      π d0 d1 y0 y1 = 1)

/-- The canonical potential-outcomes system is the model built from the given nonnegative latent
response-type probabilities that sum to one. It is the constructed system used to realize a
feasible Balke--Pearl table. -/
noncomputable abbrev P' := canonicalPOSystem S π hπ_nn hπ_sum
/-- The canonical Balke--Pearl system equips the constructed potential-outcomes system with its
instrument, treatment, and outcome roles. It is used to verify that every feasible latent
response-type table is realized by a Balke--Pearl model. -/
noncomputable abbrev S' := canonicalBP S π hπ_nn hπ_sum

/-- The sqcup assignment formula. -/
private lemma sqcup_assign_left {V : Type*} [DecidableEq V]
    {X : V → Type*} [∀ v, MeasurableSpace (X v)]
    (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂) (v : V) (hin : v ∈ r₁.target)
    (hsq : v ∈ (r₁.sqcup r₂ h).target) :
    (r₁.sqcup r₂ h).assign v hsq = r₁.assign v hin := by
  exact Regime.sqcup_assign_pos r₁ r₂ h v hin

/-- Given [two disjoint regimes over a family of variable spaces](hyp:V,X,r₁,r₂,h), for [a
variable outside the first regime](hyp:v,hnin) but [inside the second](hyp:hin), and [a proof that it
lies in their union](hyp:hsq), [the union regime assigns the second regime's value](goal). -/
lemma sqcup_assign_right {V : Type*} [DecidableEq V]
    {X : V → Type*} [∀ v, MeasurableSpace (X v)]
    (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂) (v : V) (hnin : v ∉ r₁.target)
    (hin : v ∈ r₂.target) (hsq : v ∈ (r₁.sqcup r₂ h).target) :
    (r₁.sqcup r₂ h).assign v hsq = r₂.assign v hin := by
  exact Regime.sqcup_assign_neg r₁ r₂ h v hnin hin

/-- For [a potential-outcome system](hyp:P), [a binary Balke–Pearl system](hyp:S), [a canonical
latent response-type table](hyp:π), [nonnegativity of every table entry](hyp:hπ_nn), and [unit
total table mass](hyp:hπ_sum), [the canonical potential-outcome construction satisfies factual
consistency](goal). -/
lemma canonical_consistency : (P' S π hπ_nn hπ_sum).Consistency := by
  refine ⟨?_⟩
  · -- Factual consistency.
    intro r Y hYr ω hFA
    funext v
    -- v : {x // x ∈ Y}
    have hv_notr : v.val ∉ r.target := fun hvr =>
      Finset.disjoint_left.mp hYr v.property hvr
    -- Show eval r ω v = eval Regime.empty ω v.
    change eval r ω v.val = eval Regime.empty ω v.val
    -- Case-split on v.val : Fin 3.
    -- We'll use eval_zero/eval_one/eval_two and Regime.empty_target.
    rcases v with ⟨v, hvY⟩
    -- v : Fin 3.  Match on Fin 3 with three cases.
    have hne_empty0 : (⟨0, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
      rw [Regime.empty_target]; exact Finset.notMem_empty _
    have hne_empty1 : (⟨1, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
      rw [Regime.empty_target]; exact Finset.notMem_empty _
    have hne_empty2 : (⟨2, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
      rw [Regime.empty_target]; exact Finset.notMem_empty _
    fin_cases v
    · -- v = ⟨0, _⟩
      have hv0_notr : (⟨0, by decide⟩ : SV) ∉ r.target := hv_notr
      rw [eval_zero_of_not_mem r ω hv0_notr,
        eval_zero_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty0]
    · -- v = ⟨1, _⟩
      have hv1_notr : (⟨1, by decide⟩ : SV) ∉ r.target := hv_notr
      rw [eval_one_of_not_mem r ω hv1_notr,
        eval_one_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty1]
      have hzEq : eval r ω ⟨0, by decide⟩ = eval Regime.empty ω ⟨0, by decide⟩ := by
        by_cases h0 : (⟨0, by decide⟩ : SV) ∈ r.target
        · exact (eval_zero_of_mem r ω h0).trans (hFA _ h0).symm
        · rw [eval_zero_of_not_mem r ω h0,
            eval_zero_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty0]
      exact congrArg (fun z => dArmω z ω) hzEq
    · -- v = ⟨2, _⟩
      have hv2_notr : (⟨2, by decide⟩ : SV) ∉ r.target := hv_notr
      rw [eval_two_of_not_mem r ω hv2_notr,
        eval_two_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty2]
      have hzEq : eval r ω ⟨0, by decide⟩ = eval Regime.empty ω ⟨0, by decide⟩ := by
        by_cases h0 : (⟨0, by decide⟩ : SV) ∈ r.target
        · exact (eval_zero_of_mem r ω h0).trans (hFA _ h0).symm
        · rw [eval_zero_of_not_mem r ω h0,
            eval_zero_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty0]
      have hdEq : eval r ω ⟨1, by decide⟩ = eval Regime.empty ω ⟨1, by decide⟩ := by
        by_cases h1 : (⟨1, by decide⟩ : SV) ∈ r.target
        · exact (eval_one_of_mem r ω h1).trans (hFA _ h1).symm
        · rw [eval_one_of_not_mem r ω h1,
            eval_one_of_not_mem (Regime.empty : Regime SV SX) ω hne_empty1]
          exact congrArg (fun z => dArmω z ω) hzEq
      exact congrArg (fun d => yArmω d ω) hdEq
/-- For [a potential-outcome system](hyp:P), [a binary Balke–Pearl system](hyp:S), [a canonical
latent response-type table](hyp:π), [nonnegativity of every table entry](hyp:hπ_nn), and [unit
total table mass](hyp:hπ_sum), [the canonical potential-outcome construction satisfies
composition consistency](goal). -/
lemma canonical_compositionConsistency :
    (P' S π hπ_nn hπ_sum).CompositionConsistency := by
  refine ⟨?_⟩
  intro r₁ r₂ hd Y hY ω hIA
    -- Helper: agreement of `eval (r₁⊔r₂) ω` with `eval r₁ ω` at the Z-coord.
  have hzEq : eval (r₁.sqcup r₂ hd) ω ⟨0, by decide⟩ = eval r₁ ω ⟨0, by decide⟩ := by
      by_cases h01 : (⟨0, by decide⟩ : SV) ∈ r₁.target
      · have h0sq : (⟨0, by decide⟩ : SV) ∈ (r₁.sqcup r₂ hd).target :=
          Finset.mem_union_left _ h01
        exact (eval_zero_of_mem (r₁.sqcup r₂ hd) ω h0sq).trans
          ((sqcup_assign_left r₁ r₂ hd _ h01 h0sq).trans
            (eval_zero_of_mem r₁ ω h01).symm)
      · by_cases h02 : (⟨0, by decide⟩ : SV) ∈ r₂.target
        · have h0sq : (⟨0, by decide⟩ : SV) ∈ (r₁.sqcup r₂ hd).target :=
            Finset.mem_union_right _ h02
          exact (eval_zero_of_mem (r₁.sqcup r₂ hd) ω h0sq).trans
            ((sqcup_assign_right r₁ r₂ hd _ h01 h02 h0sq).trans
              (hIA _ h02).symm)
        · have h0sq : (⟨0, by decide⟩ : SV) ∉ (r₁.sqcup r₂ hd).target := by
            rw [Regime.sqcup_target]; intro h
            rcases Finset.mem_union.mp h with h | h
            · exact h01 h
            · exact h02 h
          rw [eval_zero_of_not_mem (r₁.sqcup r₂ hd) ω h0sq,
            eval_zero_of_not_mem r₁ ω h01]
    -- Helper: agreement at the D-coord.
  have hdEq : eval (r₁.sqcup r₂ hd) ω ⟨1, by decide⟩ = eval r₁ ω ⟨1, by decide⟩ := by
      by_cases h11 : (⟨1, by decide⟩ : SV) ∈ r₁.target
      · have h1sq : (⟨1, by decide⟩ : SV) ∈ (r₁.sqcup r₂ hd).target :=
          Finset.mem_union_left _ h11
        exact (eval_one_of_mem (r₁.sqcup r₂ hd) ω h1sq).trans
          ((sqcup_assign_left r₁ r₂ hd _ h11 h1sq).trans
            (eval_one_of_mem r₁ ω h11).symm)
      · by_cases h12 : (⟨1, by decide⟩ : SV) ∈ r₂.target
        · have h1sq : (⟨1, by decide⟩ : SV) ∈ (r₁.sqcup r₂ hd).target :=
            Finset.mem_union_right _ h12
          exact (eval_one_of_mem (r₁.sqcup r₂ hd) ω h1sq).trans
            ((sqcup_assign_right r₁ r₂ hd _ h11 h12 h1sq).trans
              (hIA _ h12).symm)
        · have h1sq : (⟨1, by decide⟩ : SV) ∉ (r₁.sqcup r₂ hd).target := by
            rw [Regime.sqcup_target]; intro h
            rcases Finset.mem_union.mp h with h | h
            · exact h11 h
            · exact h12 h
          rw [eval_one_of_not_mem (r₁.sqcup r₂ hd) ω h1sq,
            eval_one_of_not_mem r₁ ω h11]
          exact congrArg (fun z => dArmω z ω) hzEq
  funext v
  rcases v with ⟨v, hvY⟩
  have hv_notr : v ∉ r₁.target ∪ r₂.target :=
      Finset.disjoint_left.mp hY hvY
  have hv_notr1 : v ∉ r₁.target := fun h => hv_notr (Finset.mem_union_left _ h)
  have hv_not_sqcup : v ∉ (r₁.sqcup r₂ hd).target := by
      rw [Regime.sqcup_target]; exact hv_notr
  change eval (r₁.sqcup r₂ hd) ω v = eval r₁ ω v
  fin_cases v
  · exact hzEq
  · have hv1_not_sqcup : (⟨1, by decide⟩ : SV) ∉ (r₁.sqcup r₂ hd).target :=
      hv_not_sqcup
    have hv1_notr1 : (⟨1, by decide⟩ : SV) ∉ r₁.target := hv_notr1
    rw [eval_one_of_not_mem (r₁.sqcup r₂ hd) ω hv1_not_sqcup,
      eval_one_of_not_mem r₁ ω hv1_notr1]
    exact congrArg (fun z => dArmω z ω) hzEq
  · have hv2_not_sqcup : (⟨2, by decide⟩ : SV) ∉ (r₁.sqcup r₂ hd).target :=
      hv_not_sqcup
    have hv2_notr1 : (⟨2, by decide⟩ : SV) ∉ r₁.target := hv_notr1
    rw [eval_two_of_not_mem (r₁.sqcup r₂ hd) ω hv2_not_sqcup,
      eval_two_of_not_mem r₁ ω hv2_notr1]
    exact congrArg (fun d => yArmω d ω) hdEq


end BaseAssumptions
end POBalkePearlSharp
end PO
end Causalean
