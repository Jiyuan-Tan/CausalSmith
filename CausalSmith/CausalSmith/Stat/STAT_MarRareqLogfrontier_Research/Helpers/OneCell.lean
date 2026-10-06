module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.CompleteArrivalFamily
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.CompleteArrivalTesting
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticKernel

/-! One-cell testing lower bounds inside the original rare-arrival model. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: oneCellRecord
/-- For [the specified inputs and assumptions](hyp:d,x,a,y,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def oneCellRecord {d : ℕ} (x : Fin d) (a y r : Bool) : FullRecord d :=
  ⟨x, a, false, false, false, y, r⟩

-- @node: oneCellMeasure
/-- For [the specified inputs and assumptions](hyp:d,x,u,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def oneCellMeasure {d : ℕ} (x : Fin d) (u q : ℝ) :
    Measure (FullRecord d) :=
  ∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
    ENNReal.ofReal (completeBernWeight (1 / 2) a *
      completeBernWeight u y * completeBernWeight q r) •
      Measure.dirac (oneCellRecord x a y r)

-- @node: oneCellMeasure_univ
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellMeasure_univ {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    oneCellMeasure x u q Set.univ = 1 := by
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hq' : 0 ≤ 1 - q := by linarith [hq.2]
  simp [oneCellMeasure, completeBernWeight]
  norm_num at ⊢
  rw [ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * u)
      (mul_nonneg (by norm_num) hu.1),
    ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * u)
      (mul_nonneg (by norm_num) hu.1),
    ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * (1 - u))
      (mul_nonneg (by norm_num) hu'),
    ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * (1 - u))
      (mul_nonneg (by norm_num) hu')]
  simp only [ENNReal.ofReal_mul (p := (1 / 2 : ℝ)) (by norm_num)]
  have hu_sum : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  have hq_sum : ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq.1 hq']
    norm_num
  calc
    _ = (ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ)) *
        (ENNReal.ofReal u + ENNReal.ofReal (1 - u)) *
        (ENNReal.ofReal q + ENNReal.ofReal (1 - q)) := by ring
    _ = 1 := by
      rw [hu_sum, hq_sum]
      simp only [mul_one]
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

-- @node: oneCellFamilyLaw
/-- For [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def oneCellFamilyLaw {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) : FullLaw d :=
  ⟨oneCellMeasure x u q, ⟨oneCellMeasure_univ x u q hu hq⟩⟩

-- @node: oneCellFamilyLaw_ate
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_ate {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ate (oneCellFamilyLaw x u q hu hq) = u := by
  let f : FullRecord d → ℝ := fun r =>
    (if r.Y1 then 1 else 0) - (if r.Y0 then 1 else 0)
  have hInt (a y r : Bool) : Integrable f
      (ENNReal.ofReal (completeBernWeight (1 / 2) a *
        completeBernWeight u y * completeBernWeight q r) •
        Measure.dirac (oneCellRecord x a y r)) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold ate oneCellFamilyLaw oneCellMeasure
  change (∫ w, f w ∂(∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
    ENNReal.ofReal (completeBernWeight (1 / 2) a *
      completeBernWeight u y * completeBernWeight q r) •
      Measure.dirac (oneCellRecord x a y r))) = u
  have hr (a y : Bool) :
      (∫ w, f w ∂(∑ r : Bool,
        ENNReal.ofReal (completeBernWeight (1 / 2) a *
          completeBernWeight u y * completeBernWeight q r) •
          Measure.dirac (oneCellRecord x a y r))) =
        ∑ r : Bool, ∫ w, f w ∂(ENNReal.ofReal
          (completeBernWeight (1 / 2) a * completeBernWeight u y *
            completeBernWeight q r) • Measure.dirac (oneCellRecord x a y r)) := by
    exact integral_finsetSum_measure (by intro r _; exact hInt a y r)
  have hy (a : Bool) :
      (∫ w, f w ∂(∑ y : Bool, ∑ r : Bool,
        ENNReal.ofReal (completeBernWeight (1 / 2) a *
          completeBernWeight u y * completeBernWeight q r) •
          Measure.dirac (oneCellRecord x a y r))) =
        ∑ y : Bool, ∫ w, f w ∂(∑ r : Bool,
          ENNReal.ofReal (completeBernWeight (1 / 2) a *
            completeBernWeight u y * completeBernWeight q r) •
            Measure.dirac (oneCellRecord x a y r)) := by
    exact integral_finsetSum_measure (by
      intro y _
      apply (integrable_finsetSum_measure).2
      intro r _
      exact hInt a y r)
  rw [integral_finsetSum_measure]
  · simp_rw [hy, hr]
    simp [f, oneCellRecord, completeBernWeight, integral_smul_measure,
      integral_dirac]
    have hu' : 0 ≤ 1 - u := by linarith [hu.2]
    have hq' : 0 ≤ 1 - q := by linarith [hq.2]
    norm_num [ENNReal.toReal_ofReal, hu.1, hu', hq.1, hq']
    ring
  · intro a ha
    apply (integrable_finsetSum_measure).2
    intro y hy
    apply (integrable_finsetSum_measure).2
    intro r hr
    exact hInt a y r

-- @node: oneCellFamilyLaw_consistency
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_consistency {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    SurrogateConsistency (oneCellFamilyLaw x u q hu hq) ∧
      OutcomeConsistency (oneCellFamilyLaw x u q hu hq) := by
  constructor
  · filter_upwards [] with r
    rfl
  · filter_upwards [] with r
    rfl

-- @node: oneCellFamilyLaw_support
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_support {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ᵐ w : FullRecord d ∂((oneCellFamilyLaw x u q hu hq).1),
      w.X = x ∧ w.S0 = false ∧ w.S1 = false ∧ w.Y0 = false := by
  simp [oneCellFamilyLaw, oneCellMeasure, oneCellRecord, Measure.ae_smul_measure]

-- @node: oneCellFamilyLaw_iid
/-- Given [the specified inputs and assumptions](hyp:n,d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_iid {n d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    IIDSampling n (sampleLaw n (oneCellFamilyLaw x u q hu hq))
      (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i)
      (oneCellFamilyLaw x u q hu hq) :=
  sampleLaw_iid n _

-- @node: oneCellFamilyLaw_balanced
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_balanced {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    BalancedRandomization (oneCellFamilyLaw x u q hu hq) := by
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hq' : 0 ≤ 1 - q := by linarith [hq.2]
  simp [BalancedRandomization, Measure.real, oneCellFamilyLaw, oneCellMeasure,
    oneCellRecord, completeBernWeight, hu.1, hu']
  have hu_sum : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  have hq_sum : ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq.1 hq']
    norm_num
  rw [show (2⁻¹ * ENNReal.ofReal u * ENNReal.ofReal q +
      2⁻¹ * ENNReal.ofReal u * ENNReal.ofReal (1 - q) +
      (2⁻¹ * ENNReal.ofReal (1 - u) * ENNReal.ofReal q +
      2⁻¹ * ENNReal.ofReal (1 - u) * ENNReal.ofReal (1 - q))) =
      (2⁻¹ : ℝ≥0∞) *
        (ENNReal.ofReal u + ENNReal.ofReal (1 - u)) *
        (ENNReal.ofReal q + ENNReal.ofReal (1 - q)) by ring,
    hu_sum, hq_sum]
  norm_num

-- @node: oneCellFamilyLaw_arrival_mass
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_arrival_mass {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    (oneCellFamilyLaw x u q hu hq).1.real {r | r.R = true} = q := by
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  simp [Measure.real, oneCellFamilyLaw, oneCellMeasure, oneCellRecord,
    completeBernWeight, hu.1, hu']
  have hu_sum : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  norm_num only [ENNReal.ofReal_mul, hu.1, hu', hq.1] at ⊢
  rw [ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * u) (mul_nonneg (by norm_num) hu.1),
    ENNReal.ofReal_mul (p := (1 / 2 : ℝ) * (1 - u)) (mul_nonneg (by norm_num) hu'),
    ENNReal.ofReal_mul (p := (1 / 2 : ℝ)) (by norm_num)]
  rw [hhalf]
  rw [ENNReal.ofReal_mul (p := (1 / 2 : ℝ)) (by norm_num), hhalf]
  calc
    _ = (((2 : ℝ≥0∞)⁻¹ + 2⁻¹) *
        (ENNReal.ofReal u + ENNReal.ofReal (1 - u)) * ENNReal.ofReal q).toReal := by
      congr 1
      ring
    _ = q := by rw [hu_sum, ENNReal.inv_two_add_inv_two]; simp [hq.1]

-- @node: oneCellFamilyLaw_randomized
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_randomized {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    RandomizedIndependence (oneCellFamilyLaw x u q hu hq) := by
  rw [RandomizedIndependence, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have hu' : 0 ≤ 1 - u := by linarith [hu.2]
  have hq' : 0 ≤ 1 - q := by linarith [hq.2]
  have hsum_u : ENNReal.ofReal u + ENNReal.ofReal (1 - u) = 1 := by
    rw [← ENNReal.ofReal_add hu.1 hu']
    norm_num
  have hsum_q : ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq.1 hq']
    norm_num
  have hhalf : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num
  have hfactor (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ENNReal.ofReal (2⁻¹ * a * b) =
        (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal a * ENNReal.ofReal b := by
    rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) ha),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    norm_num [ENNReal.ofReal_div_of_pos]
  have htwo : (2⁻¹ : ℝ≥0∞) * 2 = 1 := by
    rw [mul_two]
    exact ENNReal.inv_two_add_inv_two
  have hdouble (z : ℝ≥0∞) : (2⁻¹ : ℝ≥0∞) * (z + z) = z := by
    rw [← two_mul, ← mul_assoc, htwo]
    simp
  simp [oneCellFamilyLaw, oneCellMeasure, oneCellRecord, completeBernWeight,
    Set.indicator]
  rw [hhalf]
  simp only [hfactor u q hu.1 hq.1, hfactor u (1-q) hu.1 hq',
    hfactor (1-u) q hu' hq.1, hfactor (1-u) (1-q) hu' hq']
  by_cases hsT : true ∈ s <;> by_cases hsF : false ∈ s <;>
    by_cases htT : (x, false, false, false, true) ∈ t <;>
    by_cases htF : (x, false, false, false, false) ∈ t <;>
    simp [hsT, hsF, htT, htF, Set.mem_inter_iff, ← mul_add, hsum_u, hsum_q] <;>
    norm_num [ENNReal.inv_two_add_inv_two] <;>
    simp [pow_two, mul_assoc, mul_comm, mul_left_comm, htwo, hdouble]
  all_goals
    calc
      _ = (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal u := by ring
      _ = (2⁻¹ : ℝ≥0∞) * (2⁻¹ * (ENNReal.ofReal u + ENNReal.ofReal u)) := by
        rw [hdouble]
      _ = _ := by ring

-- @node: oneCellFamilyLaw_mar
set_option maxHeartbeats 800000 in
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_mar {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ArrivalMAR (oneCellFamilyLaw x u q hu hq) := by
  have hu' : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  have h₀ : 0 ≤ u * (1 / 2) + u * q * (-1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq']
  have h₁ : 0 ≤ 1 / 2 + u * (-1 / 2) + u * q * (1 / 2) + q * (-1 / 2) := by
    nlinarith [mul_nonneg hu' hq']
  have h₂ : 0 ≤ u * q * (1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq.1]
  have h₃ : 0 ≤ u * q * (-1 / 2) + q * (1 / 2) := by
    nlinarith [mul_nonneg hu' hq.1]
  have h₄ : 0 ≤ (1 / 2 : ℝ) * u * q :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) hq.1
  have h₅ : 0 ≤ (1 / 2 : ℝ) * u * (1 - q) :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) hq'
  have h₆ : 0 ≤ (1 / 2 : ℝ) * (1 - u) * q :=
    mul_nonneg (mul_nonneg (by norm_num) hu') hq.1
  have h₇ : 0 ≤ (1 / 2 : ℝ) * (1 - u) * (1 - q) :=
    mul_nonneg (mul_nonneg (by norm_num) hu') hq'
  intro j y r
  cases j with
  | mk a xs =>
    cases xs with
    | mk x' s =>
      cases a <;> cases s <;> cases y <;> cases r <;>
        by_cases hx : x = x'
      all_goals simp [Measure.real, oneCellFamilyLaw, oneCellMeasure,
        completeBernWeight, oneCellRecord, FullRecord.Y, FullRecord.S, cellProb,
        inCell, Set.indicator, hx, hu.1, hu', hq.1, hq', h₀, h₁, h₂, h₃,
        h₄, h₅, h₆, h₇, ENNReal.toReal_add, ENNReal.toReal_ofReal,
        ENNReal.toReal_mul]
      all_goals
        repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        try simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hu.1, hu', hq.1, hq']
        ring
-- @node: oneCellFamilyLaw_arrivedCell
set_option maxHeartbeats 800000 in
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq,j), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_arrivedCell {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (j : Cell d) :
    arrivedCell (oneCellFamilyLaw x u q hu hq) j =
      q * cellProb (oneCellFamilyLaw x u q hu hq) j := by
  have hu' : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  have h₀ : 0 ≤ u * (1 / 2) + u * q * (-1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq']
  have h₁ : 0 ≤ 1 / 2 + u * (-1 / 2) + u * q * (1 / 2) + q * (-1 / 2) := by
    nlinarith [mul_nonneg hu' hq']
  have h₂ : 0 ≤ u * q * (1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq.1]
  have h₃ : 0 ≤ u * q * (-1 / 2) + q * (1 / 2) := by
    nlinarith [mul_nonneg hu' hq.1]
  have h₄ : 0 ≤ (1 / 2 : ℝ) * u * q :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) hq.1
  have h₅ : 0 ≤ (1 / 2 : ℝ) * u * (1 - q) :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) hq'
  have h₆ : 0 ≤ (1 / 2 : ℝ) * (1 - u) * q :=
    mul_nonneg (mul_nonneg (by norm_num) hu') hq.1
  have h₇ : 0 ≤ (1 / 2 : ℝ) * (1 - u) * (1 - q) :=
    mul_nonneg (mul_nonneg (by norm_num) hu') hq'
  cases j with
  | mk a xs =>
    cases xs with
    | mk x' s =>
      cases a <;> cases s <;>
        by_cases hx : x = x'
      all_goals simp [arrivedCell, cellProb, Measure.real,
        oneCellFamilyLaw, oneCellMeasure, completeBernWeight, oneCellRecord,
        FullRecord.Y, FullRecord.S, inCell, Set.indicator, hx, hu.1, hu', hq.1,
        hq', h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, ENNReal.toReal_add,
        ENNReal.toReal_ofReal, ENNReal.toReal_mul]
      all_goals try rw [ENNReal.toReal_ofReal h₂]
      all_goals try rw [ENNReal.toReal_ofReal h₃]
      all_goals try rw [ENNReal.toReal_ofReal h₀]
      all_goals try rw [ENNReal.toReal_ofReal h₁]
      all_goals try ring
      all_goals
        repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        try simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hu.1, hu', hq.1, hq']
        ring
      all_goals
        rw [ENNReal.toReal_ofReal h₂, ENNReal.toReal_ofReal h₃,
          ENNReal.toReal_ofReal h₀, ENNReal.toReal_ofReal h₁]
        ring

-- @node: oneCellFamilyLaw_model
/-- Given [the specified inputs and assumptions](hyp:n,d,x,u,q,hn,hd,hu,hq,hq1,hslice), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_model {n d : ℕ} (x : Fin d) (u q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hu : 0 ≤ u ∧ u ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hslice : RareArrivalSlice n q) :
    RareArrivalModelClass n d q (oneCellFamilyLaw x u q hu ⟨hq.le, hq1⟩) := by
  refine ⟨oneCellFamilyLaw_iid (n := n) x u q hu ⟨hq.le, hq1⟩,
    oneCellFamilyLaw_randomized x u q hu ⟨hq.le, hq1⟩,
    oneCellFamilyLaw_balanced x u q hu ⟨hq.le, hq1⟩,
    (oneCellFamilyLaw_consistency x u q hu ⟨hq.le, hq1⟩).1,
    (oneCellFamilyLaw_consistency x u q hu ⟨hq.le, hq1⟩).2,
    oneCellFamilyLaw_mar x u q hu ⟨hq.le, hq1⟩, ?_, hslice,
    hn, hd, hq, hq1⟩
  intro j hj
  rw [oneCellFamilyLaw_arrivedCell]

-- @node: oneCellFamilyLaw_obs_ac
set_option maxHeartbeats 800000 in
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_obs_ac {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ((oneCellFamilyLaw x u q hu hq).1.map obs) ≪
      ((oneCellFamilyLaw x (1 / 2) q (by norm_num) hq).1.map obs) := by
  apply Measure.AbsolutelyContinuous.map
  · let μ : Bool × Bool × Bool → Measure (FullRecord d) := fun t =>
      ENNReal.ofReal (completeBernWeight (1 / 2) t.1 *
        completeBernWeight u t.2.1 * completeBernWeight q t.2.2) •
        Measure.dirac (oneCellRecord x t.1 t.2.1 t.2.2)
    let ν : Bool × Bool × Bool → Measure (FullRecord d) := fun t =>
      ENNReal.ofReal (completeBernWeight (1 / 2) t.1 *
        completeBernWeight (1 / 2) t.2.1 * completeBernWeight q t.2.2) •
        Measure.dirac (oneCellRecord x t.1 t.2.1 t.2.2)
    have hatom (t : Bool × Bool × Bool) : μ t ≪ ν t := by
      rcases t with ⟨a, y, r⟩
      by_cases hν : ENNReal.ofReal (completeBernWeight (1 / 2) a *
          completeBernWeight (1 / 2) y * completeBernWeight q r) = 0
      · have hμ : ENNReal.ofReal (completeBernWeight (1 / 2) a *
            completeBernWeight u y * completeBernWeight q r) = 0 := by
          cases a <;> cases y <;> cases r <;>
            simp [completeBernWeight, ENNReal.ofReal_eq_zero, hq.1, hq.2] at hν ⊢ <;>
            nlinarith
        change (ENNReal.ofReal (completeBernWeight (1 / 2) a *
            completeBernWeight u y * completeBernWeight q r) •
              Measure.dirac (oneCellRecord x a y r)) ≪
          ENNReal.ofReal (completeBernWeight (1 / 2) a *
            completeBernWeight (1 / 2) y * completeBernWeight q r) •
              Measure.dirac (oneCellRecord x a y r)
        rw [hμ, hν]
      · exact Measure.smul_absolutelyContinuous.trans
          (Measure.AbsolutelyContinuous.rfl.smul_right hν)
    have hfin (s : Finset (Bool × Bool × Bool)) :
        (∑ t ∈ s, μ t) ≪ ∑ t ∈ s, ν t := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert t s ht ih =>
          simp only [Finset.sum_insert ht]
          exact (hatom t).add ih
    have hsum : (∑ t, μ t) ≪ ∑ t, ν t := by
      simpa using hfin Finset.univ
    simpa [oneCellFamilyLaw, oneCellMeasure, μ, ν, Fintype.sum_prod_type] using hsum
  · fun_prop

-- @node: oneCellFamilyLaw_obs_atom
set_option maxHeartbeats 800000 in
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq,o), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_obs_atom {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (o : ObsRecord d) :
    ((oneCellFamilyLaw x u q hu hq).1.map obs).real {o} =
      if o.X = x ∧ o.S = false then
        if o.R then
          (1 / 2 : ℝ) * q *
            (if o.A then completeBernWeight u o.RY else if o.RY then 0 else 1)
        else if o.RY then 0 else (1 / 2 : ℝ) * (1 - q)
      else 0 := by
  have hu' : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  have h₀ : 0 ≤ u * (1 / 2) + u * q * (-1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq']
  have h₁ : 0 ≤ 1 / 2 + u * (-1 / 2) + u * q * (1 / 2) + q * (-1 / 2) := by
    nlinarith [mul_nonneg hu' hq']
  have h₂ : 0 ≤ u * q * (1 / 2) := by
    nlinarith [mul_nonneg hu.1 hq.1]
  have h₃ : 0 ≤ u * q * (-1 / 2) + q * (1 / 2) := by
    nlinarith [mul_nonneg hu' hq.1]
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by simp)]
  rcases o with ⟨X, A, S, R, RY⟩
  by_cases hx : X = x
  · subst X
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [oneCellFamilyLaw, oneCellMeasure, completeBernWeight, oneCellRecord,
        obs, FullRecord.Y, FullRecord.S, Set.indicator, hu.1, hu', hq.1, hq',
        ENNReal.toReal_add, ENNReal.toReal_ofReal, h₀, h₁, h₂, h₃,
        ENNReal.toReal_mul] <;>
      try ring
    all_goals try { rw [ENNReal.toReal_ofReal h₀, ENNReal.toReal_ofReal h₁]; ring }
    all_goals try { rw [ENNReal.toReal_ofReal h₂, ENNReal.toReal_ofReal h₃]; ring }
    all_goals
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_mul]
      simp [ENNReal.toReal_ofReal, hu.1, hu', hq']
      ring
  · have hneq : x ≠ X := Ne.symm hx
    cases A <;> cases S <;> cases R <;> cases RY <;>
      simp [oneCellFamilyLaw, oneCellMeasure, completeBernWeight, oneCellRecord,
        obs, FullRecord.Y, FullRecord.S, Set.indicator, hx, hneq]

-- @node: oneCellFamilyLaw_obs_chi
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_obs_chi {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    Causalean.Stat.chiSqDiv ((oneCellFamilyLaw x u q hu hq).1.map obs)
      ((oneCellFamilyLaw x (1 / 2) q (by norm_num) hq).1.map obs) =
      2 * q * (u - 1 / 2) ^ 2 := by
  let P₁ := oneCellFamilyLaw x u q hu hq
  let P₀ := oneCellFamilyLaw x (1 / 2) q
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1) hq
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  let μ := P₁.1.map obs
  let ν := P₀.1.map obs
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hac := oneCellFamilyLaw_obs_ac x u q hu hq
  have h := Causalean.Stat.finite_one_add_chiSqDiv μ ν hac
  dsimp [μ, ν, P₁, P₀] at h
  simp_rw [oneCellFamilyLaw_obs_atom x u q hu hq,
    oneCellFamilyLaw_obs_atom x (1 / 2) q
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1) hq] at h
  let f : ObsRecord d → ℝ := fun o =>
    (if o.X = x ∧ o.S = false then
      if o.R then
        (1 / 2 : ℝ) * q *
          (if o.A then completeBernWeight u o.RY else if o.RY then 0 else 1)
      else if o.RY then 0 else (1 / 2 : ℝ) * (1 - q)
    else 0) ^ 2 /
    (if o.X = x ∧ o.S = false then
      if o.R then
        (1 / 2 : ℝ) * q *
          (if o.A then completeBernWeight (1 / 2) o.RY else if o.RY then 0 else 1)
      else if o.RY then 0 else (1 / 2 : ℝ) * (1 - q)
    else 0)
  let a : ObsRecord d := ⟨x, false, false, false, false⟩
  let b : ObsRecord d := ⟨x, true, false, false, false⟩
  let c : ObsRecord d := ⟨x, false, false, true, false⟩
  let e₀ : ObsRecord d := ⟨x, true, false, true, false⟩
  let e₁ : ObsRecord d := ⟨x, true, false, true, true⟩
  have hsum : (∑ o : ObsRecord d, f o) =
      ∑ o ∈ ({a, b, c, e₀, e₁} : Finset (ObsRecord d)), f o := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro o ho hn
    rcases o with ⟨X, A, S, R, RY⟩
    by_cases hx : X = x
    · subst X
      cases A <;> cases S <;> cases R <;> cases RY <;>
        simp [f, a, b, c, e₀, e₁] at hn ⊢
    · simp [f, hx]
  have hvalue : (∑ o : ObsRecord d, f o) =
      1 + 2 * q * (u - 1 / 2) ^ 2 := by
    classical
    rw [hsum]
    rcases eq_or_ne q 0 with rfl | hqne
    · norm_num [f, a, b, c, e₀, e₁]
    · rcases eq_or_ne (1 - q) 0 with hqone | hqone
      · have hqeq : q = 1 := by linarith
        subst q
        norm_num [f, a, b, c, e₀, e₁, completeBernWeight]
        field_simp
        ring
      · simp [f, a, b, c, e₀, e₁, completeBernWeight, hqne, hqone]
        field_simp
        ring
  change 1 + Causalean.Stat.chiSqDiv
      ((oneCellFamilyLaw x u q hu hq).1.map obs)
      ((oneCellFamilyLaw x (1 / 2) q (by norm_num) hq).1.map obs) =
        ∑ o : ObsRecord d, f o at h
  linarith [hvalue]

/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def oneCellStep (n : ℕ) (q : ℝ) : ℝ :=
  min (1 / 4) (1 / (4 * Real.sqrt (effectiveSize n q)))

/-- Given [the specified inputs and assumptions](hyp:n,q,hn,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellStep_pos (n : ℕ) (q : ℝ) (hn : 1 ≤ n) (hq : 0 < q) :
    0 < oneCellStep n q := by
  have hN : 0 < effectiveSize n q := by
    unfold effectiveSize
    positivity
  unfold oneCellStep
  exact lt_min (by norm_num) (by positivity)

/-- Given [the specified inputs and assumptions](hyp:n,q), [the stated mathematical conclusion holds](goal). -/
lemma oneCellStep_le_quarter (n : ℕ) (q : ℝ) :
    oneCellStep n q ≤ 1 / 4 := by
  exact min_le_left _ _

/-- Given [the specified inputs and assumptions](hyp:n,q,hn,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellStep_mem (n : ℕ) (q : ℝ) (hn : 1 ≤ n) (hq : 0 < q) :
    0 ≤ 1 / 2 + oneCellStep n q ∧ 1 / 2 + oneCellStep n q ≤ 1 := by
  have hp := oneCellStep_pos n q hn hq
  have hle := oneCellStep_le_quarter n q
  constructor <;> linarith

-- @node: oneCellFamilyLaw_obs_chi_step
/-- Given [the specified inputs and assumptions](hyp:d,x,n,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_obs_chi_step {d : ℕ} (x : Fin d) (n : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    Causalean.Stat.chiSqDiv
        ((oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
          (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩).1.map obs)
        ((oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩).1.map obs) ≤
      (1 / 8 : ℝ) / n := by
  rw [oneCellFamilyLaw_obs_chi]
  have hN : 0 < effectiveSize n q := by
    unfold effectiveSize
    positivity
  have hsqrt : 0 < Real.sqrt (effectiveSize n q) := Real.sqrt_pos.2 hN
  have hle : oneCellStep n q ≤ 1 / (4 * Real.sqrt (effectiveSize n q)) :=
    min_le_right _ _
  have hp := oneCellStep_pos n q hn hq
  have hsquare : (oneCellStep n q) ^ 2 ≤
      (1 / (4 * Real.sqrt (effectiveSize n q))) ^ 2 := by
    nlinarith
  have hsqrt_sq : (Real.sqrt (effectiveSize n q)) ^ 2 = effectiveSize n q :=
    Real.sq_sqrt hN.le
  have hbudget : 16 * effectiveSize n q * (oneCellStep n q) ^ 2 ≤ 1 := by
    rw [div_pow] at hsquare
    field_simp [hsqrt.ne'] at hsquare
    nlinarith
  have hnR : (0 : ℝ) < n := by positivity
  have heq : (1 / 2 + oneCellStep n q - 1 / 2) ^ 2 =
      (oneCellStep n q) ^ 2 := by ring
  rw [heq, le_div_iff₀ hnR]
  unfold effectiveSize at hbudget
  nlinarith

-- @node: oneCell_product_testing_half
/-- Given [the specified inputs and assumptions](hyp:d,x,n,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_product_testing_half {d : ℕ} (x : Fin d) (n : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ A : Set (Fin n → ObsRecord d), MeasurableSet A →
      (sampleLaw n (oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
        (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩)).real Aᶜ +
      (sampleLaw n (oneCellFamilyLaw x (1 / 2) q (by norm_num)
        ⟨hq.le, hq1⟩)).real A ≥ 1 / 2 := by
  let L₁ := oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
    (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩
  let L₀ := oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  letI : IsProbabilityMeasure L₁.1 := L₁.2
  letI : IsProbabilityMeasure L₀.1 := L₀.2
  let P₁ := L₁.1.map obs
  let P₀ := L₀.1.map obs
  letI : IsProbabilityMeasure P₁ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure P₀ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hac : P₁ ≪ P₀ := oneCellFamilyLaw_obs_ac x
    (1 / 2 + oneCellStep n q) q (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩
  have hint : Integrable (fun z => ((P₁.rnDeriv P₀ z).toReal - 1) ^ 2) P₀ :=
    Integrable.of_finite
  have hchi : Causalean.Stat.chiSqDiv P₁ P₀ ≤ (1 / 8 : ℝ) / n :=
    oneCellFamilyLaw_obs_chi_step x n q hn hq hq1
  simpa [sampleLaw, P₁, P₀, L₁, L₀] using
    (complete_arrival_product_testing_half n hn P₁ P₀ hac hint hchi)

-- @node: oneCellStep_sq_lower
/-- Given [the specified inputs and assumptions](hyp:n,q,hn,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellStep_sq_lower (n : ℕ) (q : ℝ) (hn : 1 ≤ n) (hq : 0 < q) :
    (1 / 16 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤ (oneCellStep n q) ^ 2 := by
  have hN : 0 < effectiveSize n q := by
    unfold effectiveSize
    positivity
  have hsqrt : 0 < Real.sqrt (effectiveSize n q) := Real.sqrt_pos.2 hN
  have hsqrt_sq : (Real.sqrt (effectiveSize n q)) ^ 2 = effectiveSize n q :=
    Real.sq_sqrt hN.le
  unfold oneCellStep
  by_cases h : (1 / 4 : ℝ) ≤ 1 / (4 * Real.sqrt (effectiveSize n q))
  · rw [min_eq_left h]
    have hmin : min 1 (effectiveSize n q)⁻¹ ≤ 1 := min_le_left _ _
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)]
    have hmin : min 1 (effectiveSize n q)⁻¹ ≤ (effectiveSize n q)⁻¹ :=
      min_le_right _ _
    have heq : (1 / (4 * Real.sqrt (effectiveSize n q))) ^ 2 =
        (1 / 16 : ℝ) * (effectiveSize n q)⁻¹ := by
      rw [div_pow, mul_pow, hsqrt_sq]
      field_simp
      norm_num
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmin (by norm_num)

-- @node: oneCell_symmetric_testing_pair
/-- Given [the specified inputs and assumptions](hyp:δ,hδ,hδle), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_symmetric_testing_pair (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 2) :
    ∃ u₀ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
      ∃ u₁ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
        u₀ ≠ u₁ ∧ u₁ - u₀ = δ := by
  refine ⟨1 / 2 - δ / 2, ?_, 1 / 2 + δ / 2, ?_, ?_, ?_⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · linarith
  · ring


-- @node: oneCell_linear_grid
/-- Given [the specified inputs and assumptions](hyp:M,hM,w,hw,hwle), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_linear_grid (M : ℕ) (hM : 0 < M) (w : ℝ)
    (hw : 0 < w) (hwle : w ≤ 1 / 2) :
    ∃ grid : Fin (M + 1) → ℝ,
      Function.Injective grid ∧
      (∀ i, grid i ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun i => 1 / 2 - w / 2 + w * (i : ℝ) / M, ?_, ?_⟩
  · intro i j hij
    have hcast : (i : ℝ) = (j : ℝ) := by
      have hdiv : w * (i : ℝ) / M = w * (j : ℝ) / M := by linarith
      have hmul : w * (i : ℝ) = w * (j : ℝ) :=
        (div_left_inj' (ne_of_gt hMr)).mp hdiv
      exact mul_left_cancel₀ (ne_of_gt hw) hmul
    exact Fin.ext (by exact_mod_cast hcast)
  · intro i
    have hi : (i : ℝ) ≤ M := by
      exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
    have hit : 0 ≤ w * (i : ℝ) / M := by positivity
    have hit' : w * (i : ℝ) / M ≤ w := by
      apply (div_le_iff₀ hMr).2
      exact mul_le_mul_of_nonneg_left hi hw.le
    constructor <;> dsimp <;> linarith

-- @node: oneCellFamilyLaw_noSurrogate
/-- Given [the specified inputs and assumptions](hyp:d,x,u,q,hu,hq), [the stated mathematical conclusion holds](goal). -/
lemma oneCellFamilyLaw_noSurrogate {d : ℕ} (x : Fin d) (u q : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ᵐ r : FullRecord d ∂((oneCellFamilyLaw x u q hu hq).1),
      r.S0 = false ∧ r.S1 = false := by
  filter_upwards [oneCellFamilyLaw_support x u q hu hq] with r hr
  exact ⟨hr.2.1, hr.2.2.1⟩

/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def noSurrogateRisk (n d : ℕ) (q : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := Estimator n d)
    (Θ := {P : FullLaw d // RareArrivalModelClass n d q P ∧
      ∀ᵐ r : FullRecord d ∂(P.1), r.S0 = false ∧ r.S1 = false})
    (fun T P => squaredRisk T P.1)

end CausalSmith.Stat.MarRareqLogfrontier
