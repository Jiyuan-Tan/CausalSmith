module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.MemberLaw

/-! The comparison member with independent treated outcome and arrival draws.
This is the law P_* in equations (3) and (5) of the large-alphabet roadmap. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:q,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparison_parameters
lemma largeAlphabetComparison_parameters (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    q / (1 + q) ∈ Icc (0 : ℝ) 1 ∧
    q ≤ (1 + q) / 2 ∧ (1 + q) / 2 ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 < 1 + q := by linarith
  refine ⟨⟨by positivity, (div_le_iff₀ hp).mpr (by linarith)⟩,
    by linarith, by constructor <;> linarith⟩

/-- For [the specified inputs and assumptions](hyp:q,a), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetComparisonArrival
noncomputable def largeAlphabetComparisonArrival (q : ℝ) (a : Bool) : ℝ :=
  if a then (1 + q) / 2 else 1

-- @node: largeAlphabetComparisonArrival_bounds
/-- Given [the specified inputs and assumptions](hyp:q,hq,hq1,a), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonArrival_bounds (q : ℝ) (hq : 0 < q)
    (hq1 : q ≤ 1) (a : Bool) :
    q ≤ largeAlphabetComparisonArrival q a ∧
      largeAlphabetComparisonArrival q a ∈ Icc (0 : ℝ) 1 := by
  have hp := largeAlphabetComparison_parameters q hq hq1
  cases a
  · simp only [largeAlphabetComparisonArrival, Bool.false_eq_true, if_false]
    exact ⟨hq1, by norm_num⟩
  · exact ⟨hp.2.1, hp.2.2⟩

/-- For [the specified inputs and assumptions](hyp:d,q,a,y,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetComparisonWeight
noncomputable def largeAlphabetComparisonWeight (d : ℕ) (q : ℝ) (a y r : Bool) : ℝ :=
  (1 / (2 * (d : ℝ))) * completeBernWeight (q / (1 + q)) y *
    completeBernWeight (largeAlphabetComparisonArrival q a) r

-- @node: largeAlphabetComparisonWeight_nonneg
/-- Given [the specified inputs and assumptions](hyp:d,q,hq,hq1,a,y,r), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonWeight_nonneg (d : ℕ) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (a y r : Bool) :
    0 ≤ largeAlphabetComparisonWeight d q a y r := by
  have hy := (largeAlphabetComparison_parameters q hq hq1).1
  have hr := (largeAlphabetComparisonArrival_bounds q hq hq1 a).2
  have hb (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (b : Bool) :
      0 ≤ completeBernWeight p b := by
    cases b <;> simp [completeBernWeight] <;> linarith [hp.1, hp.2]
  exact mul_nonneg (mul_nonneg (by positivity) (hb _ hy y)) (hb _ hr r)

-- @node: largeAlphabetComparisonMeasure
/-- For [the specified inputs and assumptions](hyp:d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def largeAlphabetComparisonMeasure (d : ℕ) (q : ℝ) :
    Measure (FullRecord d) :=
  ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
    ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) •
      Measure.dirac (⟨x, a, false, false, false, y, r⟩ : FullRecord d)

-- @node: largeAlphabetComparisonWeight_sum_arrival
/-- Given [the specified inputs and assumptions](hyp:d,q,hq,hq1,a,y), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonWeight_sum_arrival (d : ℕ) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (a y : Bool) :
    (∑ r : Bool, ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r)) =
      ENNReal.ofReal ((1 / (2 * (d : ℝ))) * completeBernWeight (q / (1 + q)) y) := by
  rw [Fintype.sum_bool, ← ENNReal.ofReal_add
    (largeAlphabetComparisonWeight_nonneg d q hq hq1 a y true)
    (largeAlphabetComparisonWeight_nonneg d q hq hq1 a y false)]
  congr 1
  simp only [largeAlphabetComparisonWeight, completeBernWeight, if_true,
    Bool.false_eq_true, if_false]
  ring

-- @node: largeAlphabetComparisonMeasure_univ
/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonMeasure_univ (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    largeAlphabetComparisonMeasure d q univ = 1 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp := (largeAlphabetComparison_parameters q hq hq1).1
  have hsum : (∑ y : Bool,
      ENNReal.ofReal ((1 / (2 * (d : ℝ))) * completeBernWeight (q / (1 + q)) y)) =
        ENNReal.ofReal (1 / (2 * (d : ℝ))) := by
    simp only [Fintype.sum_bool, completeBernWeight, if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) hp.1)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hp.2))]
    congr 1
    ring
  simp only [largeAlphabetComparisonMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one,
    largeAlphabetComparisonWeight_sum_arrival d q hq hq1, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have heq : (d : ℝ) * (2 * (1 / (2 * (d : ℝ)))) = 1 := by field_simp
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [heq]
  norm_num

/-- For [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetComparisonLaw
noncomputable def largeAlphabetComparisonLaw (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) : FullLaw d :=
  ⟨largeAlphabetComparisonMeasure d q,
    ⟨largeAlphabetComparisonMeasure_univ d q hd hq hq1⟩⟩

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,E), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_real_event
lemma largeAlphabetComparisonLaw_real_event (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (E : Set (FullRecord d)) :
    (largeAlphabetComparisonLaw d q hd hq hq1).1.real E = by
      classical
      exact ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
        if (⟨x, a, false, false, false, y, r⟩ : FullRecord d) ∈ E then
          largeAlphabetComparisonWeight d q a y r else 0 := by
  classical
  simp only [largeAlphabetComparisonLaw, largeAlphabetComparisonMeasure, Measure.real,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
  have hfinite (x : Fin d) (a y r : Bool) :
      (if (⟨x, a, false, false, false, y, r⟩ : FullRecord d) ∈ E then
        ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) else 0) ≠ ⊤ := by
    split_ifs <;> simp
  rw [ENNReal.toReal_sum (by simp only [ENNReal.sum_ne_top]; intros; apply hfinite)]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.toReal_sum (by simp only [ENNReal.sum_ne_top]; intros; apply hfinite)]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_sum (by simp only [ENNReal.sum_ne_top]; intros; apply hfinite)]
  apply Finset.sum_congr rfl
  intro y _
  rw [ENNReal.toReal_sum (by intros; apply hfinite)]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · exact ENNReal.toReal_ofReal (largeAlphabetComparisonWeight_nonneg d q hq hq1 a y r)
  · rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,f), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_integral
lemma largeAlphabetComparisonLaw_integral (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (f : FullRecord d → ℝ) :
    (∫ w, f w ∂(largeAlphabetComparisonLaw d q hd hq hq1).1) =
      ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
        largeAlphabetComparisonWeight d q a y r *
          f ⟨x, a, false, false, false, y, r⟩ := by
  have hi (x : Fin d) (a y r : Bool) : Integrable f
      (ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) •
        Measure.dirac (⟨x, a, false, false, false, y, r⟩ : FullRecord d)) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hir (x : Fin d) (a y : Bool) : Integrable f
      (∑ r : Bool, ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) •
        Measure.dirac (⟨x, a, false, false, false, y, r⟩ : FullRecord d)) := by
    apply integrable_finsetSum_measure.mpr
    intro r _
    exact hi x a y r
  have hiy (x : Fin d) (a : Bool) : Integrable f
      (∑ y : Bool, ∑ r : Bool, ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) •
        Measure.dirac (⟨x, a, false, false, false, y, r⟩ : FullRecord d)) := by
    apply integrable_finsetSum_measure.mpr
    intro y _
    exact hir x a y
  have hia (x : Fin d) : Integrable f
      (∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
        ENNReal.ofReal (largeAlphabetComparisonWeight d q a y r) •
        Measure.dirac (⟨x, a, false, false, false, y, r⟩ : FullRecord d)) := by
    apply integrable_finsetSum_measure.mpr
    intro a _
    exact hiy x a
  change (∫ w, f w ∂largeAlphabetComparisonMeasure d q) = _
  rw [largeAlphabetComparisonMeasure, integral_finsetSum_measure (by intro x _; exact hia x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum_measure (by intro a _; exact hiy x a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum_measure (by intro y _; exact hir x a y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_finsetSum_measure (by intro r _; exact hi x a y r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (largeAlphabetComparisonWeight_nonneg d q hq hq1 a y r)]
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_ate
lemma largeAlphabetComparisonLaw_ate (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    ate (largeAlphabetComparisonLaw d q hd hq hq1) = q / (1 + q) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [ate, largeAlphabetComparisonLaw_integral]
  simp [largeAlphabetComparisonWeight, completeBernWeight, largeAlphabetComparisonArrival]
  field_simp
  <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,o), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_observed_atom
lemma largeAlphabetComparisonLaw_observed_atom (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (o : ObsRecord d) :
    ((largeAlphabetComparisonLaw d q hd hq hq1).1.map obs).real {o} =
      if o.S = false then (1 / (2 * (d : ℝ))) *
        (if o.A then
          if o.R then (if o.RY then q / 2 else 1 / 2)
          else (if o.RY then 0 else (1 - q) / 2)
        else if o.R = true ∧ o.RY = false then 1 else 0)
      else 0 := by
  classical
  have hp : 1 + q ≠ 0 := by linarith
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by simp)]
  change (largeAlphabetComparisonLaw d q hd hq hq1).1.real (obs ⁻¹' {o}) = _
  rw [largeAlphabetComparisonLaw_real_event]
  rcases o with ⟨x, a, s, r, ry⟩
  cases a <;> cases s <;> cases r <;> cases ry <;>
    simp [obs, FullRecord.S, FullRecord.Y, largeAlphabetComparisonWeight,
      completeBernWeight, largeAlphabetComparisonArrival, ite_and,
      Finset.sum_ite_irrel, Finset.sum_ite_eq'] <;>
    field_simp <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,a,x,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_cellProb
lemma largeAlphabetComparisonLaw_cellProb (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (a : Bool) (x : Fin d) (s : Bool) :
    cellProb (largeAlphabetComparisonLaw d q hd hq hq1) (a, x, s) =
      if s then 0 else 1 / (2 * (d : ℝ)) := by
  classical
  rw [cellProb, largeAlphabetComparisonLaw_real_event]
  cases a <;> cases s <;>
    simp [inCell, FullRecord.S, largeAlphabetComparisonWeight,
      completeBernWeight, largeAlphabetComparisonArrival,
      Finset.sum_ite_irrel, Finset.sum_ite_eq'] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,a,x,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_arrivedCell
lemma largeAlphabetComparisonLaw_arrivedCell (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (a : Bool) (x : Fin d) (s : Bool) :
    arrivedCell (largeAlphabetComparisonLaw d q hd hq hq1) (a, x, s) =
      largeAlphabetComparisonArrival q a *
        cellProb (largeAlphabetComparisonLaw d q hd hq hq1) (a, x, s) := by
  classical
  rw [arrivedCell, largeAlphabetComparisonLaw_real_event, largeAlphabetComparisonLaw_cellProb]
  cases a <;> cases s <;>
    simp [inCell, FullRecord.S, largeAlphabetComparisonWeight,
      completeBernWeight, largeAlphabetComparisonArrival,
      Finset.sum_ite_irrel, Finset.sum_ite_eq'] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_mar
lemma largeAlphabetComparisonLaw_mar (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    ArrivalMAR (largeAlphabetComparisonLaw d q hd hq hq1) := by
  classical
  intro j y r
  rcases j with ⟨a, x, s⟩
  rw [largeAlphabetComparisonLaw_cellProb]
  simp_rw [largeAlphabetComparisonLaw_real_event]
  cases a <;> cases s <;> cases y <;> cases r <;>
    simp [inCell, FullRecord.S, FullRecord.Y, largeAlphabetComparisonWeight,
      completeBernWeight, largeAlphabetComparisonArrival, ite_and,
      Finset.sum_ite_irrel, Finset.sum_ite_eq']
  all_goals first | (left; ring) | ring

-- @node: largeAlphabetComparisonLaw_occupiedCellArrival
/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonLaw_occupiedCellArrival (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    OccupiedCellArrival q (largeAlphabetComparisonLaw d q hd hq hq1) := by
  intro j hj
  rcases j with ⟨a, x, s⟩
  rw [largeAlphabetComparisonLaw_arrivedCell]
  exact mul_le_mul_of_nonneg_right
    (largeAlphabetComparisonArrival_bounds q hq hq1 a).1 hj.le

-- @node: largeAlphabetComparisonLaw_balanced
/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonLaw_balanced (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    BalancedRandomization (largeAlphabetComparisonLaw d q hd hq hq1) := by
  classical
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [BalancedRandomization, largeAlphabetComparisonLaw_real_event]
  calc
    _ = ∑ _x : Fin d, 1 / (2 * (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [largeAlphabetComparisonWeight, completeBernWeight, largeAlphabetComparisonArrival]
      ring
    _ = 1 / 2 := by simp; field_simp

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,s,t), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_arm_event_factor
lemma largeAlphabetComparisonLaw_arm_event_factor (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Set Bool)
    (t : Set (Fin d × Bool × Bool × Bool × Bool)) :
    (largeAlphabetComparisonLaw d q hd hq hq1).1.real
      {w | w.A ∈ s ∧ (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) *
      (largeAlphabetComparisonLaw d q hd hq hq1).1.real
        {w | (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} := by
  classical
  rw [largeAlphabetComparisonLaw_real_event, largeAlphabetComparisonLaw_real_event,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hsT : true ∈ s <;> by_cases hsF : false ∈ s <;>
    by_cases htT : (x, false, false, false, true) ∈ t <;>
    by_cases htF : (x, false, false, false, false) ∈ t <;>
    simp [largeAlphabetComparisonWeight, completeBernWeight,
      largeAlphabetComparisonArrival, hsT, hsF, htT, htF] <;> ring

-- @node: largeAlphabetComparisonLaw_arm_mass
/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,s), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonLaw_arm_mass (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Set Bool) :
    (largeAlphabetComparisonLaw d q hd hq hq1).1.real {w | w.A ∈ s} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) := by
  let := (largeAlphabetComparisonLaw d q hd hq hq1).2
  simpa using largeAlphabetComparisonLaw_arm_event_factor d q hd hq hq1 s univ

-- @node: largeAlphabetComparisonLaw_randomized
/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetComparisonLaw_randomized (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    RandomizedIndependence (largeAlphabetComparisonLaw d q hd hq hq1) := by
  let := (largeAlphabetComparisonLaw d q hd hq hq1).2
  rw [RandomizedIndependence, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (largeAlphabetComparisonLaw d q hd hq hq1).1.real
      {w | w.A ∈ s ∧ (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} =
    (largeAlphabetComparisonLaw d q hd hq hq1).1.real {w | w.A ∈ s} *
      (largeAlphabetComparisonLaw d q hd hq hq1).1.real
        {w | (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t}
  rw [largeAlphabetComparisonLaw_arm_event_factor, largeAlphabetComparisonLaw_arm_mass]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_model
lemma largeAlphabetComparisonLaw_model (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    UnrestrictedArrivalModelClass n d q (largeAlphabetComparisonLaw d q hd hq hq1) := by
  refine ⟨hn, hd, hq, hq1, largeAlphabetComparisonLaw_randomized d q hd hq hq1,
    largeAlphabetComparisonLaw_balanced d q hd hq hq1, ?_, ?_,
    largeAlphabetComparisonLaw_mar d q hd hq hq1,
    largeAlphabetComparisonLaw_occupiedCellArrival d q hd hq hq1⟩
  all_goals filter_upwards [] with w; rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,o), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_one_visit_matching
lemma largeAlphabet_one_visit_matching (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (o : ObsRecord d) :
    (∫ b : Bool,
      ((largeAlphabetLaw q (fun _ : Fin d => b) hd hq hq1).1.map obs).real {o}
      ∂((1 / 2 : ℝ≥0∞) • Measure.dirac false +
        (1 / 2 : ℝ≥0∞) • Measure.dirac true)) =
      ((largeAlphabetComparisonLaw d q hd hq hq1).1.map obs).real {o} := by
  rw [fairBinary_integral]
  simp_rw [largeAlphabetLaw_observed_atom, largeAlphabetComparisonLaw_observed_atom]
  rcases o with ⟨x, a, s, r, ry⟩
  cases a <;> cases s <;> cases r <;> cases ry <;>
    simp [largeAlphabetArrival, completeBernWeight] <;> ring

end CausalSmith.Stat.MarRareqLogfrontier
