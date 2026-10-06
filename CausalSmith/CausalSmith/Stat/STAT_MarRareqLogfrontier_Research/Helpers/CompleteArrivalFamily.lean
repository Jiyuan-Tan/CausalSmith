module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Causalean.Stat.Minimax.ChiSquaredFinite

/-! A normalized one-cell complete-arrival Bernoulli family. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: completeRecord
/-- For [the specified inputs and assumptions](hyp:d,x,a,y), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def completeRecord {d : ℕ} (x : Fin d) (a y : Bool) : FullRecord d :=
  ⟨x, a, false, false, false, y, true⟩

-- @node: completeBernWeight
/-- For [the specified inputs and assumptions](hyp:p,b), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def completeBernWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

-- @node: completeMeasure
/-- For [the specified inputs and assumptions](hyp:d,x,u), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def completeMeasure {d : ℕ} (x : Fin d) (u : ℝ) : Measure (FullRecord d) :=
  ∑ a : Bool, ∑ y : Bool,
    ENNReal.ofReal (completeBernWeight (1/2) a * completeBernWeight u y) •
      Measure.dirac (completeRecord x a y)

-- @node: completeMeasure_univ
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeMeasure_univ {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) : completeMeasure x u Set.univ = 1 := by
  simp [completeMeasure, completeBernWeight]
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  norm_num at ⊢
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hhalf]
  calc
    _ = (2⁻¹ + 2⁻¹ : ℝ≥0∞) *
        (ENNReal.ofReal u + ENNReal.ofReal (1 - u)) := by ring
    _ = 1 := by rw [← ENNReal.ofReal_add hu.1 hu', ENNReal.inv_two_add_inv_two]; norm_num

-- @node: completeFamilyLaw
/-- For [the specified inputs and assumptions](hyp:d,x,u,hu), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def completeFamilyLaw {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) : FullLaw d :=
  ⟨completeMeasure x u, ⟨completeMeasure_univ x u hu⟩⟩

-- @node: completeFamilyLaw_ate
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_ate {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) : ate (completeFamilyLaw x u hu) = u := by
  let f : FullRecord d → ℝ := fun r =>
    (if r.Y1 then 1 else 0) - (if r.Y0 then 1 else 0)
  have hInt (a y : Bool) : Integrable f
      (ENNReal.ofReal (completeBernWeight (1/2) a * completeBernWeight u y) •
        Measure.dirac (completeRecord x a y)) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold ate completeFamilyLaw completeMeasure
  change (∫ r, f r ∂(∑ a : Bool, ∑ y : Bool,
    ENNReal.ofReal (completeBernWeight (1/2) a * completeBernWeight u y) •
      Measure.dirac (completeRecord x a y))) = u
  have hinner (a : Bool) :
      (∫ r, f r ∂(∑ y : Bool,
        ENNReal.ofReal (completeBernWeight (1/2) a * completeBernWeight u y) •
          Measure.dirac (completeRecord x a y))) =
      ∑ y : Bool, ∫ r, f r ∂(ENNReal.ofReal
        (completeBernWeight (1/2) a * completeBernWeight u y) •
          Measure.dirac (completeRecord x a y)) := by
    exact integral_finsetSum_measure (by intro y hy; exact hInt a y)
  have hOuter : ∀ a : Bool, Integrable f (∑ y : Bool,
      ENNReal.ofReal (completeBernWeight (1/2) a * completeBernWeight u y) •
        Measure.dirac (completeRecord x a y)) := by
    intro a
    apply (integrable_finsetSum_measure).2
    intro y hy
    exact hInt a y
  rw [integral_finsetSum_measure (by intro a ha; exact hOuter a)]
  simp_rw [hinner]
  simp [completeRecord, completeBernWeight, integral_smul_measure, integral_dirac]
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hu2 : 0 ≤ (1 - 2⁻¹ : ℝ) * u := mul_nonneg (by norm_num) hu.1
  simp [f, ENNReal.toReal_ofReal hu.1, ENNReal.toReal_ofReal hu']
  rw [ENNReal.toReal_ofReal hu2]
  ring

-- @node: completeFamilyLaw_obs_ac
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_obs_ac {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) :
    ((completeFamilyLaw x u hu).1.map obs) ≪
      ((completeFamilyLaw x (1 / 2) (by norm_num :
        (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1)).1.map obs) := by
  intro s hs
  rw [Measure.map_apply (by fun_prop) (by simp)] at hs ⊢
  simp [completeFamilyLaw, completeMeasure, completeBernWeight,
    completeRecord] at hs ⊢
  norm_num at hs
  tauto

-- @node: completeFamilyLaw_obs_atom
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu,o), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_obs_atom {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (o : ObsRecord d) :
    ((completeFamilyLaw x u hu).1.map obs).real {o} =
      if o.X = x ∧ o.S = false ∧ o.R = true then
        (1 / 2 : ℝ) *
          (if o.A then completeBernWeight u o.RY else if o.RY then 0 else 1)
      else 0 := by
  have h1 : 0 ≤ u * (1 / 2 : ℝ) := mul_nonneg hu.1 (by norm_num)
  have h2 : 0 ≤ (1 / 2 : ℝ) + u * (-1 / 2) := by nlinarith [hu.2]
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by simp)]
  rcases o with ⟨X, A, S, R, RY⟩
  by_cases hx : X = x
  · subst X
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [completeFamilyLaw, completeMeasure, completeBernWeight, completeRecord,
        obs, FullRecord.Y, FullRecord.S, Set.indicator, hu.1, sub_nonneg.mpr hu.2,
        ENNReal.toReal_add, ENNReal.toReal_ofReal, h1, h2] <;>
      try ring
    rw [ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    ring
  · have hneq : x ≠ X := Ne.symm hx
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [completeFamilyLaw, completeMeasure, completeBernWeight, completeRecord,
        obs, FullRecord.Y, FullRecord.S, Set.indicator, hx, hneq]

-- @node: completeFamilyLaw_obs_chi
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_obs_chi {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) :
    Causalean.Stat.chiSqDiv ((completeFamilyLaw x u hu).1.map obs)
      ((completeFamilyLaw x (1 / 2) (by norm_num)).1.map obs) =
      2 * (u - 1 / 2) ^ 2 := by
  let P₁ := completeFamilyLaw x u hu
  let P₀ := completeFamilyLaw x (1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1)
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  let μ := P₁.1.map obs
  let ν := P₀.1.map obs
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hac := completeFamilyLaw_obs_ac x u hu
  have h := Causalean.Stat.finite_one_add_chiSqDiv μ ν hac
  dsimp [μ, ν, P₁, P₀] at h
  simp_rw [completeFamilyLaw_obs_atom x u hu,
    completeFamilyLaw_obs_atom x (1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1)] at h
  let a : ObsRecord d := ⟨x, false, false, true, false⟩
  let b : ObsRecord d := ⟨x, true, false, true, false⟩
  let c : ObsRecord d := ⟨x, true, false, true, true⟩
  let f : ObsRecord d → ℝ := fun o =>
    (if o.X = x ∧ o.S = false ∧ o.R = true then
      (1 / 2 : ℝ) * (if o.A then completeBernWeight u o.RY else if o.RY then 0 else 1)
      else 0) ^ 2 /
    (if o.X = x ∧ o.S = false ∧ o.R = true then
      (1 / 2 : ℝ) *
        (if o.A then completeBernWeight (1 / 2) o.RY else if o.RY then 0 else 1)
      else 0)
  have hsum : (∑ o : ObsRecord d, f o) =
      ∑ o ∈ ({a, b, c} : Finset (ObsRecord d)), f o := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro o ho hn
    rcases o with ⟨X, A, S, R, RY⟩
    by_cases hx : X = x
    · subst X
      cases A <;> cases S <;> cases R <;> cases RY <;>
        simp [f, a, b, c] at hn ⊢
    · simp [f, hx]
  have hvalue : (∑ o : ObsRecord d, f o) =
      1 + 2 * (u - 1 / 2) ^ 2 := by
    rw [hsum]
    simp [f, a, b, c, completeBernWeight]
    ring
  change 1 + Causalean.Stat.chiSqDiv
      ((completeFamilyLaw x u hu).1.map obs)
      ((completeFamilyLaw x (1 / 2) (by norm_num)).1.map obs) =
        ∑ o : ObsRecord d, f o at h
  linarith [hvalue]

-- @node: completeFamilyLaw_balanced
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_balanced {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) :
    BalancedRandomization (completeFamilyLaw x u hu) := by
  rw [BalancedRandomization, Measure.real]
  simp [completeFamilyLaw, completeMeasure, completeBernWeight, completeRecord]
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hw : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  rw [← mul_add, hw]
  norm_num

-- @node: completeFamilyLaw_consistency
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_consistency {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) :
    SurrogateConsistency (completeFamilyLaw x u hu) ∧
      OutcomeConsistency (completeFamilyLaw x u hu) := by
  constructor
  · filter_upwards [] with r
    rfl
  · filter_upwards [] with r
    rfl

-- @node: completeFamilyLaw_arrivedCell
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu,j), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_arrivedCell {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (j : Cell d) :
    arrivedCell (completeFamilyLaw x u hu) j =
      cellProb (completeFamilyLaw x u hu) j := by
  simp [arrivedCell, cellProb, Measure.real, completeFamilyLaw, completeMeasure,
    completeBernWeight, completeRecord, inCell, Set.indicator]

-- @node: completeFamilyLaw_mar
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_mar {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) : ArrivalMAR (completeFamilyLaw x u hu) := by
  intro j y r
  cases r <;>
    simp [Measure.real, completeFamilyLaw, completeMeasure,
      completeBernWeight, completeRecord, cellProb, inCell, Set.indicator] <;> ring

-- @node: completeFamilyLaw_randomized
/-- Given [the specified inputs and assumptions](hyp:d,x,u,hu), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_randomized {d : ℕ} (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) :
    RandomizedIndependence (completeFamilyLaw x u hu) := by
  rw [RandomizedIndependence, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hw (v : ℝ) (hv : 0 ≤ v) :
      ENNReal.ofReal ((1 - 2⁻¹ : ℝ) * v) = (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal v := by
    norm_num [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [ENNReal.ofReal_div_of_pos]
  have hsum : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  have htwo : (2⁻¹ : ℝ≥0∞) * 2 = 1 := by
    rw [mul_two]
    exact ENNReal.inv_two_add_inv_two
  simp [completeFamilyLaw, completeMeasure, completeRecord, completeBernWeight,
    Set.indicator, hw u hu.1, hw (1-u) hu']
  by_cases hsT : true ∈ s <;> by_cases hsF : false ∈ s <;>
    by_cases htT : (x, false, false, false, true) ∈ t <;>
    by_cases htF : (x, false, false, false, false) ∈ t <;>
    simp [hsT, hsF, htT, htF, Set.mem_inter_iff] <;>
      simp only [← mul_add, hsum, mul_one] <;>
      simp only [← two_mul, ← mul_assoc, htwo, one_mul] <;>
      rw [mul_comm (2 : ℝ≥0∞) (2⁻¹ : ℝ≥0∞), htwo] <;>
      simp <;> simpa only [mul_comm] using htwo.symm

-- @node: completeFamilyLaw_in_unrestricted_class_of_randomized
/-- Given [the specified inputs and assumptions](hyp:n,d,hn,hd,x,u,hu,hR), [the stated mathematical conclusion holds](goal). -/
lemma completeFamilyLaw_in_unrestricted_class_of_randomized {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (x : Fin d) (u : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1)
    (hR : RandomizedIndependence (completeFamilyLaw x u hu)) :
    UnrestrictedArrivalModelClass n d 1 (completeFamilyLaw x u hu) := by
  refine ⟨hn, hd, by norm_num, by norm_num, hR,
    completeFamilyLaw_balanced x u hu,
    (completeFamilyLaw_consistency x u hu).1,
    (completeFamilyLaw_consistency x u hu).2,
    completeFamilyLaw_mar x u hu, ?_⟩
  intro j hj
  rw [completeFamilyLaw_arrivedCell]
  simp

end CausalSmith.Stat.MarRareqLogfrontier
