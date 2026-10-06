module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Basic
public import Causalean.Stat.Minimax.ChiSquaredFinite

/-!
# Complete-arrival one-cell submodel

This module gives the explicit Bernoulli submodel used for the parametric
point-risk and honest-interval floors.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The full-data atom generated from a fair treatment bit and one treated-potential bit. -/
@[no_expose]
def parametricAtom {d : ℕ} (x : Fin d) (a y : Bool) : FullAtom d :=
  ⟨⟨x, false, false, false, y⟩, a, false, (if a then y else false), true⟩

/-- Bernoulli PMF written with real-valued success probability. -/
@[no_expose]
noncomputable def parametricBoolPMF (p : ℝ) (hp : p ∈ Set.Icc 0 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then p else 1 - p)) (by
    have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
    rw [← ENNReal.ofReal_add hp.1 hp']
    norm_num)

/-- Complete-arrival one-cell Bernoulli law with treated mean `p`. -/
@[no_expose]
noncomputable def parametricFullLaw {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) : FullLaw d :=
  ⟨(parametricBoolPMF (1 / 2) (by norm_num)).bind fun a =>
    (parametricBoolPMF p hp).map (parametricAtom x a)⟩

/-- For [a probability in the unit interval](hyp:hp) and [a binary outcome](hyp:b), [the Bernoulli point mass equals its usual real-valued probability](goal). -/
lemma parametricBernoulli_toReal (p : ℝ) (hp : p ∈ Set.Icc 0 1) (b : Bool) :
    (parametricBoolPMF p hp b).toReal =
      if b then p else 1 - p := by
  cases b <;> simp [parametricBoolPMF, hp.1, sub_nonneg.mpr hp.2]

/-- For [a valid treated success probability](hyp:hp) and [a full-data atom](hyp:w), [the one-cell law's atom mass is the sum of its fair-treatment and outcome weights over generating pairs](goal). -/
lemma parametricFullLaw_fullMass {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (w : FullAtom d) :
    fullMass (parametricFullLaw x p hp) w =
      ∑ a : Bool, ∑ y : Bool,
        if w = parametricAtom x a y then
          (1 / 2 : ℝ) * (if y then p else 1 - p)
        else 0 := by
  simp only [fullMass, parametricFullLaw, PMF.bind_apply, PMF.map_apply,
    tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : w = parametricAtom x a y
      · subst w
        simp only [if_true]
        rw [parametricBernoulli_toReal (1 / 2) (by norm_num) a,
          parametricBernoulli_toReal p hp y]
        cases a <;> cases y <;> norm_num
      · simp [h]
    · intro y _
      split
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
  · intro a _
    apply ENNReal.mul_ne_top
    · exact PMF.apply_ne_top _ _
    · rw [ENNReal.sum_ne_top]
      intro y _
      split
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top

/-- For [a valid treated success probability](hyp:hp) and [a decidable event](hyp:E), [the one-cell event probability reduces to the four generating treatment-outcome pairs](goal). -/
lemma parametricFullLaw_massOf {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (E : FullAtom d → Prop) [DecidablePred E] :
    massOf (parametricFullLaw x p hp) E =
      ∑ a : Bool, ∑ y : Bool,
        if E (parametricAtom x a y) then
          (1 / 2 : ℝ) * (if y then p else 1 - p)
        else 0 := by
  classical
  unfold massOf
  simp_rw [parametricFullLaw_fullMass]
  calc
    _ = ∑ w : FullAtom d, ∑ a : Bool, ∑ y : Bool,
        if E w ∧ w = parametricAtom x a y then
          (1 / 2 : ℝ) * (if y then p else 1 - p)
        else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hE : E w <;> simp [hE]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_eq_single (parametricAtom x a y)]
      · simp
      · intro w _ hw
        by_cases hc : E w ∧ w = parametricAtom x a y
        · exact (hw hc.2).elim
        · simp [hc]
      · simp

/-- For [a valid treated success probability](hyp:hp) and [an outcome function](hyp:f), [the one-cell expectation reduces to the four generating treatment-outcome pairs](goal). -/
lemma parametricFullLaw_sum {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (f : FullAtom d → ℝ) :
    (∑ w : FullAtom d, fullMass (parametricFullLaw x p hp) w * f w) =
      ∑ a : Bool, ∑ y : Bool,
        ((1 / 2 : ℝ) * (if y then p else 1 - p)) * f (parametricAtom x a y) := by
  classical
  simp_rw [parametricFullLaw_fullMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp

/-- For [a valid treated success probability](hyp:hp), if [a full-data atom is not one of the generated treatment-outcome atoms](hyp:h), [the one-cell law assigns it zero mass](goal). -/
lemma parametricFullLaw_mass_zero_of_not_generated {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (w : FullAtom d)
    (h : ∀ a y : Bool, w ≠ parametricAtom x a y) :
    fullMass (parametricFullLaw x p hp) w = 0 := by
  rw [parametricFullLaw_fullMass]
  simp [h]

-- @node: parametricFullLaw_complete
/-- The one-cell family has deterministic outcome arrival. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the specified input `w`](hyp:w), [the specified input `hR`](hyp:hR), [the stated mathematical conclusion holds](goal). -/
lemma parametricFullLaw_complete {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (w : FullAtom d) (hR : w.R = false) :
    fullMass (parametricFullLaw x p hp) w = 0 := by
  apply parametricFullLaw_mass_zero_of_not_generated x p hp w
  intro a y h
  subst w
  simp [parametricAtom] at hR

-- @node: parametricFullLaw_consistency
/-- The one-cell family obeys consistency. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametricFullLaw_consistency {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    Consistency (parametricFullLaw x p hp) := by
  intro w hw
  apply parametricFullLaw_mass_zero_of_not_generated x p hp w
  intro a y h
  subst w
  cases a <;> cases y <;> simp [parametricAtom] at hw

-- @node: parametricFullLaw_balanced
/-- The one-cell family is balanced. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametricFullLaw_balanced {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    BalancedRandomization (parametricFullLaw x p hp) := by
  unfold BalancedRandomization armMass
  rw [parametricFullLaw_massOf]
  simp [parametricAtom]
  ring

-- @node: parametricFullLaw_randomized
/-- Treatment is independent of the fixed baseline and potential vector. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametricFullLaw_randomized {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    RandomizedIndependence (parametricFullLaw x p hp) := by
  intro a x' s0 s1 y0 y1
  unfold armMass
  rw [parametricFullLaw_massOf, parametricFullLaw_massOf,
    parametricFullLaw_massOf]
  fin_cases a <;> fin_cases s0 <;> fin_cases s1 <;> fin_cases y0 <;>
    fin_cases y1
  all_goals
    by_cases hx : x' = x
    · subst x'
      simp [parametricAtom]
      all_goals exact Or.inl (by ring)
    · have hxx : x ≠ x' := Ne.symm hx
      simp [parametricAtom, hx, hxx]

-- @node: parametricFullLaw_tau
/-- The target of the one-cell family is its treated success probability. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametricFullLaw_tau {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    tau (parametricFullLaw x p hp) = p := by
  unfold tau
  rw [parametricFullLaw_sum]
  simp [parametricAtom]

/-- For [a valid treated success probability](hyp:hp) and [an observed atom](hyp:o), [the one-cell law's observed point mass has the displayed explicit form](goal). -/
lemma parametric_observed_mass {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (o : Obs d) :
    obsMass (observedLaw (parametricFullLaw x p hp)) o =
      if o.X = x ∧ o.S = false ∧ o.R = true then
        if o.A then (1 / 2 : ℝ) * (if o.RY then p else 1 - p)
        else if o.RY then 0 else 1 / 2
      else 0 := by
  have h := obsMass_sum_event (parametricFullLaw x p hp) (fun z => z = o)
  have hsingle :
      (∑ z : Obs d, if z = o then obsMass (observedLaw (parametricFullLaw x p hp)) z else 0) =
        obsMass (observedLaw (parametricFullLaw x p hp)) o := by simp
  rw [hsingle, parametricFullLaw_massOf] at h
  rw [h]
  rcases o with ⟨X, A, S, R, RY⟩
  by_cases hx : X = x
  · subst X
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [observe, parametricAtom] <;> ring
  · have hxx : x ≠ X := Ne.symm hx
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [observe, parametricAtom, hx, hxx]

-- @node: parametric_observed_ac
/-- Every one-cell observed law is dominated by the central one. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametric_observed_ac {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (observedLaw (parametricFullLaw x p hp)).toMeasure ≪
      (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))).toMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  let μ := (observedLaw (parametricFullLaw x p hp)).toMeasure
  let ν := (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))).toMeasure
  let sf : Finset (Obs d) := (Set.toFinite s).toFinset
  have hsf : (sf : Set (Obs d)) = s := by simp [sf]
  have hsumν : (∑ o ∈ sf, ν {o}) = ν s := by
    rw [sum_measure_singleton, hsf]
  have hpointν : ∀ o ∈ sf, ν {o} = 0 := by
    intro o ho
    have hzsum : ∑ z ∈ sf, ν {z} = 0 := by rw [hsumν]; exact hzero
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => bot_le)).mp hzsum o ho
  have hpointμ : ∀ o ∈ sf, μ {o} = 0 := by
    intro o ho
    have hrealν : ν.real {o} = 0 := by rw [measureReal_eq_zero_iff]; exact hpointν o ho
    have hrealμ : μ.real {o} = 0 := by
      dsimp [μ, ν] at hrealν ⊢
      rw [show (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))).toMeasure.real {o} =
          obsMass (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))) o by
            simp [measureReal_def, obsMass]] at hrealν
      rw [show (observedLaw (parametricFullLaw x p hp)).toMeasure.real {o} =
          obsMass (observedLaw (parametricFullLaw x p hp)) o by
            simp [measureReal_def, obsMass]]
      rw [parametric_observed_mass] at hrealν
      rw [parametric_observed_mass]
      rcases o with ⟨X, A, S, R, RY⟩
      by_cases hx : X = x <;> cases A <;> cases S <;> cases R <;> cases RY <;>
        simp [hx] at hrealν ⊢
      all_goals norm_num at hrealν
    rw [measureReal_eq_zero_iff] at hrealμ
    exact hrealμ
  rw [← hsf, ← sum_measure_singleton]
  exact Finset.sum_eq_zero hpointμ

-- @node: parametric_observed_chisq
/-- The central one-record chi-square divergence of the one-cell family. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the stated mathematical conclusion holds](goal). -/
lemma parametric_observed_chisq {d : ℕ} (x : Fin d) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    Causalean.Stat.chiSqDiv
      (observedLaw (parametricFullLaw x p hp)).toMeasure
      (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))).toMeasure =
        2 * (p - 1 / 2) ^ 2 := by
  let μ := (observedLaw (parametricFullLaw x p hp)).toMeasure
  let ν := (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))).toMeasure
  have hac : μ ≪ ν := parametric_observed_ac x p hp
  have h := Causalean.Stat.finite_one_add_chiSqDiv μ ν hac
  let f : Obs d → ℝ := fun o => (μ.real {o}) ^ 2 / ν.real {o}
  have hmassμ (o : Obs d) : μ.real {o} =
      obsMass (observedLaw (parametricFullLaw x p hp)) o := by
    simp [μ, measureReal_def, obsMass]
  have hmassν (o : Obs d) : ν.real {o} =
      obsMass (observedLaw (parametricFullLaw x (1 / 2) (by norm_num))) o := by
    simp [ν, measureReal_def, obsMass]
  let c : Obs d := ⟨x, false, false, true, false⟩
  let e₀ : Obs d := ⟨x, true, false, true, false⟩
  let e₁ : Obs d := ⟨x, true, false, true, true⟩
  have hsum : (∑ o : Obs d, f o) = ∑ o ∈ ({c, e₀, e₁} : Finset (Obs d)), f o := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro o _ ho
    rcases o with ⟨X, A, S, R, RY⟩
    by_cases hx : X = x
    · subst X
      cases A <;> cases S <;> cases R <;> cases RY <;>
        simp [f, hmassμ, hmassν, c, e₀, e₁, parametric_observed_mass] at ho ⊢
    · simp [f, hmassμ, hmassν, parametric_observed_mass, hx]
  have hvalue : (∑ o : Obs d, f o) = 1 + 2 * (p - 1 / 2) ^ 2 := by
    rw [hsum]
    simp [f, hmassμ, hmassν, c, e₀, e₁, parametric_observed_mass]
    ring
  change 1 + Causalean.Stat.chiSqDiv μ ν = ∑ o : Obs d, f o at h
  linarith

end CausalSmith.Stat.MarNearcompleteFrontier
