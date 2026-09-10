import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Estimator
import Causalean.Stat.Inference.HadamardDeriv
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Directional calculus for the fixed-support endpoint -/

open scoped BigOperators
open Filter Topology
open Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ}

/-- Coordinatewise positive-part projection of raw mass-vector capacities. -/
noncomputable def projectedMassCapacity
    (v : ObservedDatum 𝒳 K → ℝ) : Capacities 𝒳 K where
  lower x i := max ((capacitiesFromMassVector v).lower x i) 0
  upper x i := max ((capacitiesFromMassVector v).upper x i) 0

/-- Cell survivor mass as a functional of the finite atom vector. -/
noncomputable def survivorMassFromMassVector
    (v : ObservedDatum 𝒳 K → ℝ) (x : 𝒳) : ℝ :=
  massVectorSum v (fun o => decide (o.cell = x)) *
    (projectedMassCapacity v).mass x

/-- The finite-coordinate survivor score is Borel measurable. [the stated conclusion follows](goal). -/
theorem measurable_survivorMassFromMassVector {K : ℕ} [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] (x : 𝒳) :
    Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
      survivorMassFromMassVector v x) := by
  have hsum (E : ObservedDatum 𝒳 K → Bool) :
      Measurable (fun v : ObservedDatum 𝒳 K → ℝ => massVectorSum v E) := by
    unfold massVectorSum
    fun_prop
  have hcond (A B : ObservedDatum 𝒳 K → Bool) :
      Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
        empiricalConditional (massVectorSum v A) (massVectorSum v B)) := by
    unfold empiricalConditional
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (hsum B)
    · exact (hsum A).div (hsum B)
    · exact measurable_const
  have hlower (i : Fin K) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ =>
        (projectedMassCapacity v).lower x i) := by
    unfold projectedMassCapacity capacitiesFromMassVector
    exact ((hcond _ _).sub (hcond _ _)).max measurable_const
  have hupper (i : Fin K) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ =>
        (projectedMassCapacity v).upper x i) := by
    unfold projectedMassCapacity capacitiesFromMassVector
    exact ((hcond _ _).sub (hcond _ _)).max measurable_const
  unfold survivorMassFromMassVector Capacities.mass Capacities.q0 Capacities.q1
  exact (hsum _).mul
    ((Finset.measurable_sum _ fun i _ => hlower i).min
      (Finset.measurable_sum _ fun i _ => hupper i))

/-- [the benefit lower nonneg property holds](goal). -/
theorem benefitLower_nonneg (c : Capacities 𝒳 K) (x : 𝒳) :
    0 ≤ c.benefitLower x := by
  unfold Capacities.benefitLower
  exact Finset.le_sup' (f := fun t : Option (Fin K) => match t with
    | none => 0
    | some k => c.lowerLe x k - c.upperLe x k + min (c.gap x) 0)
    (by simp : none ∈ (Finset.univ : Finset (Option (Fin K))))

/-- Given [the stated hypotheses](hyp:hc), [the benefit upper nonneg property holds](goal). -/
theorem benefitUpper_nonneg (c : Capacities 𝒳 K) (hc : ValidCapacities c)
    (x : 𝒳) : 0 ≤ c.benefitUpper x := by
  unfold Capacities.benefitUpper
  rw [Finset.le_inf'_iff]
  intro t ht
  cases t with
  | none =>
      exact le_min (Finset.sum_nonneg fun i _ => hc.1 x i)
        (Finset.sum_nonneg fun i _ => hc.2 x i)
  | some k =>
      exact add_nonneg (Finset.sum_nonneg fun i _ => hc.1 x i)
        (Finset.sum_nonneg fun i _ => hc.2 x i)

/-- [the benefit upper is at most mass property holds](goal). -/
theorem benefitUpper_le_mass (c : Capacities 𝒳 K) (x : 𝒳) :
    c.benefitUpper x ≤ c.mass x := by
  unfold Capacities.benefitUpper
  exact Finset.inf'_le (f := fun t : Option (Fin K) => match t with
    | none => c.mass x
    | some k => c.lowerLt x k + c.upperGt x k)
    (by simp : none ∈ (Finset.univ : Finset (Option (Fin K))))

/-- Given [the stated hypotheses](hyp:hc), [the benefit lower is at most mass property holds](goal). -/
theorem benefitLower_le_mass (c : Capacities 𝒳 K) (hc : ValidCapacities c)
    (x : 𝒳) : c.benefitLower x ≤ c.mass x := by
  unfold Capacities.benefitLower
  rw [Finset.sup'_le_iff]
  intro t ht
  cases t with
  | none =>
      exact le_min (Finset.sum_nonneg fun i _ => hc.1 x i)
        (Finset.sum_nonneg fun i _ => hc.2 x i)
  | some k =>
      change c.lowerLe x k - c.upperLe x k + min (c.gap x) 0 ≤ c.mass x
      have hprefix : c.lowerLe x k ≤ c.q0 x := by
        unfold Capacities.lowerLe Capacities.q0
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun i hi hj => hc.1 x i)
      have hu : 0 ≤ c.upperLe x k := Finset.sum_nonneg fun i _ => hc.2 x i
      by_cases hq : c.q0 x ≤ c.q1 x
      · rw [Capacities.mass, min_eq_left hq]
        nlinarith [min_le_right (c.gap x) 0]
      · have hq' : c.q1 x ≤ c.q0 x := le_of_not_ge hq
        rw [Capacities.mass, min_eq_right hq']
        have hgap : c.gap x ≤ 0 := by
          unfold Capacities.gap
          linarith
        rw [min_eq_left hgap]
        unfold Capacities.gap
        linarith

set_option maxHeartbeats 500000 in
/-- [the projected components map is measurable](goal). -/
theorem measurable_projected_components {K : ℕ} [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] :
    (∀ x, Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
      (projectedMassCapacity v).mass x)) ∧
    (∀ x, Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
      (projectedMassCapacity v).benefitLower x)) ∧
    (∀ x, Measurable (fun v : ObservedDatum 𝒳 K → ℝ =>
      (projectedMassCapacity v).benefitUpper x)) := by
  have hsum (E : ObservedDatum 𝒳 K → Bool) :
      Measurable (fun v : ObservedDatum 𝒳 K → ℝ => massVectorSum v E) := by
    unfold massVectorSum
    fun_prop
  have hcond (A B : ObservedDatum 𝒳 K → Bool) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ =>
        empiricalConditional (massVectorSum v A) (massVectorSum v B)) := by
    unfold empiricalConditional
    exact Measurable.ite (measurableSet_lt measurable_const (hsum B))
      ((hsum A).div (hsum B)) measurable_const
  have hl (x : 𝒳) (i : Fin K) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ => (projectedMassCapacity v).lower x i) := by
    unfold projectedMassCapacity capacitiesFromMassVector
    exact ((hcond _ _).sub (hcond _ _)).max measurable_const
  have hu (x : 𝒳) (i : Fin K) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ => (projectedMassCapacity v).upper x i) := by
    unfold projectedMassCapacity capacitiesFromMassVector
    exact ((hcond _ _).sub (hcond _ _)).max measurable_const
  have hq0 (x : 𝒳) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ => (projectedMassCapacity v).q0 x) := by
    unfold Capacities.q0
    exact Finset.measurable_sum _ fun i _ => hl x i
  have hq1 (x : 𝒳) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ => (projectedMassCapacity v).q1 x) := by
    unfold Capacities.q1
    exact Finset.measurable_sum _ fun i _ => hu x i
  have hm (x : 𝒳) : Measurable
      (fun v : ObservedDatum 𝒳 K → ℝ => (projectedMassCapacity v).mass x) := by
    unfold Capacities.mass
    exact (hq0 x).min (hq1 x)
  refine ⟨hm, ?_, ?_⟩
  · intro x
    let fL : Option (Fin K) → (ObservedDatum 𝒳 K → ℝ) → ℝ := fun t v =>
      match t with
      | none => 0
      | some k => (projectedMassCapacity v).lowerLe x k -
        (projectedMassCapacity v).upperLe x k +
        min ((projectedMassCapacity v).gap x) 0
    rw [show (fun v : ObservedDatum 𝒳 K → ℝ =>
      (projectedMassCapacity v).benefitLower x) = fun v =>
        Finset.univ.sup' Finset.univ_nonempty (fun t => fL t v) by
      funext v; exact benefitLower_eq_sup_explicit _ _]
    have hh : Measurable (Finset.univ.sup' Finset.univ_nonempty
        fL) := by
      apply Finset.measurable_sup' Finset.univ_nonempty
      intro t ht
      cases t with
      | none => exact measurable_const
      | some k =>
          dsimp [fL]
          unfold Capacities.lowerLe Capacities.upperLe Capacities.gap
          fun_prop
    convert hh using 1
    funext v
    exact (Finset.sup'_apply
      (s := (Finset.univ : Finset (Option (Fin K))))
      (C := fun _ : (ObservedDatum 𝒳 K → ℝ) => ℝ)
      Finset.univ_nonempty fL v).symm
  · intro x
    let fU : Option (Fin K) → (ObservedDatum 𝒳 K → ℝ) → ℝ := fun t v =>
      match t with
      | none => (projectedMassCapacity v).mass x
      | some k => (projectedMassCapacity v).lowerLt x k +
        (projectedMassCapacity v).upperGt x k
    rw [show (fun v : ObservedDatum 𝒳 K → ℝ =>
      (projectedMassCapacity v).benefitUpper x) = fun v =>
        Finset.univ.inf' Finset.univ_nonempty (fun t => fU t v) by
      funext v; exact benefitUpper_eq_inf_explicit _ _]
    have hh : Measurable (Finset.univ.inf' Finset.univ_nonempty
        fU) := by
      apply Finset.inf'_induction
      · intro f hf g hg
        exact hf.min hg
      · intro t ht
        cases t with
        | none => simpa [fU] using hm x
        | some k =>
            dsimp [fU]
            unfold Capacities.lowerLt Capacities.upperGt
            fun_prop
    convert hh using 1
    funext v
    exact (Finset.inf'_apply
      (s := (Finset.univ : Finset (Option (Fin K))))
      (C := fun _ : (ObservedDatum 𝒳 K → ℝ) => ℝ)
      Finset.univ_nonempty fU v).symm

private lemma massSum_chd (θ : ObservedDatum 𝒳 K → ℝ)
    (E : ObservedDatum 𝒳 K → Bool) :
    HasContinuousHadamardDirDerivAt (fun v => massVectorSum v E) θ := by
  apply HasContinuousHadamardDirDerivAt.of_differentiableAt
  unfold massVectorSum
  fun_prop

private lemma conditional_chd (θ : ObservedDatum 𝒳 K → ℝ)
    (A B : ObservedDatum 𝒳 K → Bool) (hB : 0 < massVectorSum θ B) :
    HasContinuousHadamardDirDerivAt
      (fun v => empiricalConditional (massVectorSum v A) (massVectorSum v B)) θ := by
  have hBc : Continuous (fun v => massVectorSum v B) := by
    unfold massVectorSum
    fun_prop
  have hev : ∀ᶠ v in 𝓝 θ, 0 < massVectorSum v B :=
    hBc.continuousAt.eventually (eventually_gt_nhds hB)
  apply HasContinuousHadamardDirDerivAt.congr_of_eventuallyEq
    (g := fun v => massVectorSum v A / massVectorSum v B)
  · filter_upwards [hev] with v hv
    simp only [empiricalConditional, if_pos hv]
  · exact (massSum_chd θ A).div hB.ne' (massSum_chd θ B)

private lemma projected_lower_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳) (i : Fin K)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).lower x i) θ := by
  have hzero : HasContinuousHadamardDirDerivAt
      (fun _ : ObservedDatum 𝒳 K → ℝ => (0 : ℝ)) θ :=
    .of_differentiableAt (differentiableAt_const (c := (0 : ℝ)))
  apply HasContinuousHadamardDirDerivAt.max _ hzero
  apply HasContinuousHadamardDirDerivAt.sub
  · exact conditional_chd θ _ _ (hArm false)
  · exact conditional_chd θ _ _ (hArm true)

private lemma projected_upper_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳) (i : Fin K)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).upper x i) θ := by
  have hzero : HasContinuousHadamardDirDerivAt
      (fun _ : ObservedDatum 𝒳 K → ℝ => (0 : ℝ)) θ :=
    .of_differentiableAt (differentiableAt_const (c := (0 : ℝ)))
  apply HasContinuousHadamardDirDerivAt.max _ hzero
  apply HasContinuousHadamardDirDerivAt.sub
  · exact conditional_chd θ _ _ (hArm true)
  · exact conditional_chd θ _ _ (hArm false)

private lemma projected_q0_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).q0 x) θ := by
  unfold Capacities.q0
  exact HasContinuousHadamardDirDerivAt.finset_sum Finset.univ
    (fun i _ => projected_lower_chd θ x i hArm)

private lemma projected_q1_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).q1 x) θ := by
  unfold Capacities.q1
  exact HasContinuousHadamardDirDerivAt.finset_sum Finset.univ
    (fun i _ => projected_upper_chd θ x i hArm)

private lemma projected_mass_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).mass x) θ := by
  unfold Capacities.mass
  exact (projected_q0_chd θ x hArm).min (projected_q1_chd θ x hArm)

/-- Directional differentiability of one screened cell score. Given [the stated hypotheses](hyp:hArm), [the stated conclusion follows](goal). -/
theorem survivorMassFromMassVector_chd
    (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt (fun v => survivorMassFromMassVector v x) θ := by
  exact (massSum_chd θ _).mul (projected_mass_chd θ x hArm)

/-- [the projected mass capacity empirical probability vector property holds](goal). -/
theorem projectedMassCapacity_empiricalProbabilityVector
    {Ω : Type*} (O : ℕ → Ω → ObservedDatum 𝒳 K) (n : ℕ) (ω : Ω) :
    projectedMassCapacity (empiricalProbabilityVector O n ω) =
      projectedCapacities O n ω := by
  unfold projectedMassCapacity projectedCapacities
  rw [Capacities.mk.injEq]
  constructor <;> funext x i <;>
    simp only [rawCapacities, capacitiesFromMassVector,
      massVectorSum_empiricalProbabilityVector] <;> rfl

/-- [the survivor mass from mass vector empirical probability vector property holds](goal). -/
theorem survivorMassFromMassVector_empiricalProbabilityVector
    {Ω : Type*} (O : ℕ → Ω → ObservedDatum 𝒳 K) (n : ℕ) (ω : Ω) (x : 𝒳) :
    survivorMassFromMassVector (empiricalProbabilityVector O n ω) x =
      empiricalCellMass O n ω x * (projectedCapacities O n ω).mass x := by
  unfold survivorMassFromMassVector empiricalCellMass
  rw [massVectorSum_empiricalProbabilityVector,
    projectedMassCapacity_empiricalProbabilityVector]

/-- On a nonempty recovered support, the guarded implementation agrees with the fixed-support mass-vector functional. Given [the stated hypotheses](hyp:hη,hsupport,hs), [the stated conclusion follows](goal). -/
theorem plugInEndpoints_eq_endpointFromMassVectorOn_of_screenedSupport_eq
    {Ω : Type*} (O : ℕ → Ω → ObservedDatum 𝒳 K) (η : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (support : Finset 𝒳)
    (hη : 0 < η n) (hsupport : support.Nonempty)
    (hs : screenedSupport O η n ω = support) :
    plugInEndpoints O η n ω =
      endpointFromMassVectorOn support (empiricalProbabilityVector O n ω) := by
  classical
  have hscreenNonempty : (screenedSupport O η n ω).Nonempty := by
    rw [hs]
    exact hsupport
  have hscore : ∀ x ∈ screenedSupport O η n ω,
      0 < empiricalCellMass O n ω x * (projectedCapacities O n ω).mass x := by
    intro x hx
    have hx' : screenedCell O η n ω x := by
      simpa [screenedSupport] using hx
    exact hη.trans hx'
  have hM : 0 < ∑ x ∈ screenedSupport O η n ω,
      empiricalCellMass O n ω x * (projectedCapacities O n ω).mass x :=
    Finset.sum_pos hscore hscreenNonempty
  have hsum (f : 𝒳 → ℝ) :
      (∑ x, (if screenedCell O η n ω x then (1 : ℝ) else 0) * f x) =
        ∑ x ∈ screenedSupport O η n ω, f x := by
    simp only [screenedSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : screenedCell O η n ω x <;> simp [h]
  have hsum3 (f g : 𝒳 → ℝ) :
      (∑ x, (if screenedCell O η n ω x then (1 : ℝ) else 0) * f x * g x) =
        ∑ x ∈ screenedSupport O η n ω, f x * g x := by
    calc
      _ = ∑ x, (if screenedCell O η n ω x then (1 : ℝ) else 0) *
          (f x * g x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = _ := hsum (fun x => f x * g x)
  rw [← hs]
  unfold plugInEndpoints endpointFromMassVectorOn
  dsimp only
  rw [hsum3, hsum3, hsum3, if_pos hM]
  rw [← projectedMassCapacity_empiricalProbabilityVector]
  simp_rw [massVectorSum_empiricalProbabilityVector]
  rfl

set_option maxHeartbeats 500000 in
-- The explicit finite envelope creates a large elaboration term.
private lemma projected_benefitLower_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).benefitLower x) θ := by
  have hlowerLe (t : Fin K) : HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).lowerLe x t) θ := by
    unfold Capacities.lowerLe
    exact HasContinuousHadamardDirDerivAt.finset_sum _
      (fun i _ => projected_lower_chd θ x i hArm)
  have hupperLe (t : Fin K) : HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).upperLe x t) θ := by
    unfold Capacities.upperLe
    exact HasContinuousHadamardDirDerivAt.finset_sum _
      (fun i _ => projected_upper_chd θ x i hArm)
  have hgap : HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).gap x) θ := by
    unfold Capacities.gap
    exact (projected_q1_chd θ x hArm).sub (projected_q0_chd θ x hArm)
  have hzero : HasContinuousHadamardDirDerivAt
      (fun _ : ObservedDatum 𝒳 K → ℝ => (0 : ℝ)) θ :=
    .of_differentiableAt (differentiableAt_const (c := (0 : ℝ)))
  apply HasContinuousHadamardDirDerivAt.congr_of_eventuallyEq
    (g := fun v => Finset.univ.sup' Finset.univ_nonempty
      (fun t : Option (Fin K) => match t with
        | none => 0
        | some k => (projectedMassCapacity v).lowerLe x k -
            (projectedMassCapacity v).upperLe x k +
            min ((projectedMassCapacity v).gap x) 0))
  · filter_upwards [] with v
    exact benefitLower_eq_sup_explicit (projectedMassCapacity v) x
  · apply HasContinuousHadamardDirDerivAt.finset_sup'
    intro t _
    cases t with
    | none => exact hzero
    | some k => exact ((hlowerLe k).sub (hupperLe k)).add (hgap.min hzero)

set_option maxHeartbeats 500000 in
-- The explicit finite envelope creates a large elaboration term.
private lemma projected_benefitUpper_chd (θ : ObservedDatum 𝒳 K → ℝ) (x : 𝒳)
    (hArm : ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z))) :
    HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).benefitUpper x) θ := by
  have hlowerLt (t : Fin K) : HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).lowerLt x t) θ := by
    unfold Capacities.lowerLt
    exact HasContinuousHadamardDirDerivAt.finset_sum _
      (fun i _ => projected_lower_chd θ x i hArm)
  have hupperGt (t : Fin K) : HasContinuousHadamardDirDerivAt
      (fun v => (projectedMassCapacity v).upperGt x t) θ := by
    unfold Capacities.upperGt
    exact HasContinuousHadamardDirDerivAt.finset_sum _
      (fun i _ => projected_upper_chd θ x i hArm)
  apply HasContinuousHadamardDirDerivAt.congr_of_eventuallyEq
    (g := fun v => Finset.univ.inf' Finset.univ_nonempty
      (fun t : Option (Fin K) => match t with
        | none => (projectedMassCapacity v).mass x
        | some k => (projectedMassCapacity v).lowerLt x k +
            (projectedMassCapacity v).upperGt x k))
  · filter_upwards [] with v
    exact benefitUpper_eq_inf_explicit (projectedMassCapacity v) x
  · apply HasContinuousHadamardDirDerivAt.finset_inf'
    intro t _
    cases t with
    | none => exact projected_mass_chd θ x hArm
    | some k => exact (hlowerLt k).add (hupperGt k)

set_option maxHeartbeats 800000 in
-- The final composite contains both finite envelopes and their common quotient.
/-- Directional differentiability of the reduced-support endpoint, including all projection, mass-minimum, and finite threshold-tie faces. Given [the stated hypotheses](hyp:hArm,hMass), [the stated conclusion follows](goal). -/
theorem endpointFromMassVectorOn_chd
    (θ : ObservedDatum 𝒳 K → ℝ) (support : Finset 𝒳)
    (hArm : ∀ x ∈ support, ∀ z, 0 < massVectorSum θ
      (fun o => decide (o.cell = x ∧ o.instrument = z)))
    (hMass : 0 < ∑ x ∈ support,
      massVectorSum θ (fun o => decide (o.cell = x)) *
        (projectedMassCapacity θ).mass x) :
    HasContinuousHadamardDirDerivAt (endpointFromMassVectorOn support) θ := by
  have hp (x : 𝒳) := massSum_chd θ (fun o => decide (o.cell = x))
  have hd : HasContinuousHadamardDirDerivAt
      (fun v => ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).mass x) θ :=
    HasContinuousHadamardDirDerivAt.finset_sum support fun x hx =>
      (hp x).mul (projected_mass_chd θ x (hArm x hx))
  have hnL : HasContinuousHadamardDirDerivAt
      (fun v => ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).benefitLower x) θ :=
    HasContinuousHadamardDirDerivAt.finset_sum support fun x hx =>
      (hp x).mul (projected_benefitLower_chd θ x (hArm x hx))
  have hnU : HasContinuousHadamardDirDerivAt
      (fun v => ∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).benefitUpper x) θ :=
    HasContinuousHadamardDirDerivAt.finset_sum support fun x hx =>
      (hp x).mul (projected_benefitUpper_chd θ x (hArm x hx))
  change HasContinuousHadamardDirDerivAt
    (fun v => ((∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
          (projectedMassCapacity v).benefitLower x) /
        (∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
          (projectedMassCapacity v).mass x),
      (∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
          (projectedMassCapacity v).benefitUpper x) /
        (∑ x ∈ support, massVectorSum v (fun o => decide (o.cell = x)) *
          (projectedMassCapacity v).mass x))) θ
  have hratioL := HasContinuousHadamardDirDerivAt.div
    (f := fun v => ∑ x ∈ support,
      massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).benefitLower x)
    (g := fun v => ∑ x ∈ support,
      massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).mass x)
    (x := θ) hMass.ne' hnL hd
  have hratioU := HasContinuousHadamardDirDerivAt.div
    (f := fun v => ∑ x ∈ support,
      massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).benefitUpper x)
    (g := fun v => ∑ x ∈ support,
      massVectorSum v (fun o => decide (o.cell = x)) *
        (projectedMassCapacity v).mass x)
    (x := θ) hMass.ne' hnU hd
  exact hratioL.prod hratioU

end CausalSmith.PartialID.SlateBenefitPartialTransport
