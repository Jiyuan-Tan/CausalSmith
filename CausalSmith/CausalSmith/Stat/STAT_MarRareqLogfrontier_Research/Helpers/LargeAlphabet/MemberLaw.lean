module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.FuzzyPrior
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.CompleteArrivalFamily

/-! The deterministic binary-cell members of the large-alphabet lower-bound experiment. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:d,ξ,x,a,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetRecord
def largeAlphabetRecord {d : ℕ} (ξ : Fin d → Bool) (x : Fin d) (a r : Bool) :
    FullRecord d := ⟨x, a, false, false, false, ξ x, r⟩

/-- For [the specified inputs and assumptions](hyp:d,q,ξ,x,a), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetArrival
def largeAlphabetArrival {d : ℕ} (q : ℝ) (ξ : Fin d → Bool) (x : Fin d)
    (a : Bool) : ℝ := if a && ξ x then q else 1

/-- For [the specified inputs and assumptions](hyp:d,q,ξ), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetMeasure
noncomputable def largeAlphabetMeasure {d : ℕ} (q : ℝ) (ξ : Fin d → Bool) :
    Measure (FullRecord d) :=
  ∑ x : Fin d, ∑ a : Bool, ∑ r : Bool,
    ENNReal.ofReal ((1 / (2 * (d : ℝ))) *
      completeBernWeight (largeAlphabetArrival q ξ x a) r) •
        Measure.dirac (largeAlphabetRecord ξ x a r)

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hq,hq1,x,a), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetArrival_bounds
lemma largeAlphabetArrival_bounds {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hq : 0 < q) (hq1 : q ≤ 1) (x : Fin d) (a : Bool) :
    q ≤ largeAlphabetArrival q ξ x a ∧
      largeAlphabetArrival q ξ x a ∈ Icc (0 : ℝ) 1 := by
  unfold largeAlphabetArrival
  split_ifs <;> refine ⟨by linarith, ?_, ?_⟩ <;> linarith

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hq,hq1,x,a,r), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_weight_nonneg
lemma largeAlphabet_weight_nonneg {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hq : 0 < q) (hq1 : q ≤ 1) (x : Fin d) (a r : Bool) :
    0 ≤ (1 / (2 * (d : ℝ))) * completeBernWeight (largeAlphabetArrival q ξ x a) r := by
  have hb := (largeAlphabetArrival_bounds q ξ hq hq1 x a).2
  apply mul_nonneg (by positivity)
  cases r <;> simp only [completeBernWeight, Bool.false_eq_true, if_false, if_true]
  · linarith [hb.2]
  · exact hb.1

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetMeasure_univ
lemma largeAlphabetMeasure_univ {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    largeAlphabetMeasure q ξ univ = 1 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsum (x : Fin d) (a : Bool) :
      (∑ r : Bool, ENNReal.ofReal ((1 / (2 * (d : ℝ))) *
        completeBernWeight (largeAlphabetArrival q ξ x a) r)) =
          ENNReal.ofReal (1 / (2 * (d : ℝ))) := by
    simp only [Fintype.sum_bool, completeBernWeight, if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add
      (by simpa [completeBernWeight] using largeAlphabet_weight_nonneg q ξ hq hq1 x a true)
      (by simpa [completeBernWeight] using largeAlphabet_weight_nonneg q ξ hq hq1 x a false)]
    congr 1
    ring
  simp only [largeAlphabetMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have heq : (d : ℝ) * (2 * (1 / (2 * (d : ℝ)))) = 1 := by field_simp
  norm_num only [Nat.cast_ofNat] at ⊢
  rw [heq]
  norm_num

/-- For [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetLaw
noncomputable def largeAlphabetLaw {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) : FullLaw d :=
  ⟨largeAlphabetMeasure q ξ, ⟨largeAlphabetMeasure_univ q ξ hd hq hq1⟩⟩

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,E), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_real_event
lemma largeAlphabetLaw_real_event {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (E : Set (FullRecord d)) :
    (largeAlphabetLaw q ξ hd hq hq1).1.real E = by
      classical
      exact ∑ x : Fin d, ∑ a : Bool, ∑ r : Bool,
        if largeAlphabetRecord ξ x a r ∈ E then
          (1 / (2 * (d : ℝ))) * completeBernWeight (largeAlphabetArrival q ξ x a) r
        else 0 := by
  classical
  simp only [largeAlphabetLaw, largeAlphabetMeasure, Measure.real,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [ENNReal.toReal_sum (by
    simp only [ENNReal.sum_ne_top]
    intros
    split_ifs <;> simp only [ENNReal.ofReal_ne_top, ne_eq, ENNReal.zero_ne_top, not_false_eq_true])]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.toReal_sum (by
    simp only [ENNReal.sum_ne_top]
    intros
    split_ifs <;> simp only [ENNReal.ofReal_ne_top, ne_eq, ENNReal.zero_ne_top, not_false_eq_true])]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_sum (by
    intros
    split_ifs <;> simp only [ENNReal.ofReal_ne_top, ne_eq, ENNReal.zero_ne_top, not_false_eq_true])]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · exact ENNReal.toReal_ofReal (largeAlphabet_weight_nonneg q ξ hq hq1 x a r)
  · rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,a,x,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_cellProb
lemma largeAlphabetLaw_cellProb {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (a : Bool) (x : Fin d) (s : Bool) :
    cellProb (largeAlphabetLaw q ξ hd hq hq1) (a, x, s) =
      if s then 0 else 1 / (2 * (d : ℝ)) := by
  classical
  rw [cellProb, largeAlphabetLaw_real_event]
  cases a <;> cases s <;>
    simp [inCell, largeAlphabetRecord, FullRecord.S, completeBernWeight,
      Finset.sum_ite_irrel, Finset.sum_ite_eq'] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,a,x,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_arrivedCell
lemma largeAlphabetLaw_arrivedCell {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (a : Bool) (x : Fin d) (s : Bool) :
    arrivedCell (largeAlphabetLaw q ξ hd hq hq1) (a, x, s) =
      largeAlphabetArrival q ξ x a * cellProb (largeAlphabetLaw q ξ hd hq hq1) (a, x, s) := by
  classical
  rw [arrivedCell, largeAlphabetLaw_real_event, largeAlphabetLaw_cellProb]
  cases a <;> cases s <;>
    simp [inCell, largeAlphabetRecord, FullRecord.S, completeBernWeight,
      Finset.sum_ite_irrel, Finset.sum_ite_eq'] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_mar
lemma largeAlphabetLaw_mar {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    ArrivalMAR (largeAlphabetLaw q ξ hd hq hq1) := by
  classical
  intro j y r
  rcases j with ⟨a, x, s⟩
  rw [largeAlphabetLaw_cellProb]
  simp_rw [largeAlphabetLaw_real_event]
  cases a <;> cases s <;> cases y <;> cases r <;>
    simp [inCell, largeAlphabetRecord, FullRecord.S, FullRecord.Y, completeBernWeight,
      Finset.sum_ite_irrel, Finset.sum_ite_eq', ite_and]
  all_goals first | (left; ring) | (split_ifs <;> ring) | ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_occupiedCellArrival
lemma largeAlphabetLaw_occupiedCellArrival {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    OccupiedCellArrival q (largeAlphabetLaw q ξ hd hq hq1) := by
  intro j hj
  rcases j with ⟨a, x, s⟩
  rw [largeAlphabetLaw_arrivedCell]
  exact mul_le_mul_of_nonneg_right
    (largeAlphabetArrival_bounds q ξ hq hq1 x a).1 hj.le

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_balanced
lemma largeAlphabetLaw_balanced {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    BalancedRandomization (largeAlphabetLaw q ξ hd hq hq1) := by
  classical
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [BalancedRandomization, largeAlphabetLaw_real_event]
  calc
    _ = ∑ _x : Fin d, 1 / (2 * (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [largeAlphabetRecord, completeBernWeight]
      ring
    _ = 1 / 2 := by simp; field_simp

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,s,t), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_arm_event_factor
lemma largeAlphabetLaw_arm_event_factor {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Set Bool)
    (t : Set (Fin d × Bool × Bool × Bool × Bool)) :
    (largeAlphabetLaw q ξ hd hq hq1).1.real
      {w | w.A ∈ s ∧ (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) *
      (largeAlphabetLaw q ξ hd hq hq1).1.real
        {w | (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} := by
  classical
  rw [largeAlphabetLaw_real_event, largeAlphabetLaw_real_event, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hsT : true ∈ s <;> by_cases hsF : false ∈ s <;>
    by_cases ht : (x, false, false, false, ξ x) ∈ t <;>
    simp [largeAlphabetRecord, completeBernWeight, hsT, hsF, ht] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_arm_mass
lemma largeAlphabetLaw_arm_mass {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Set Bool) :
    (largeAlphabetLaw q ξ hd hq hq1).1.real {w | w.A ∈ s} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) := by
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  simpa using largeAlphabetLaw_arm_event_factor q ξ hd hq hq1 s univ

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_randomized
lemma largeAlphabetLaw_randomized {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    RandomizedIndependence (largeAlphabetLaw q ξ hd hq hq1) := by
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  rw [RandomizedIndependence, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (largeAlphabetLaw q ξ hd hq hq1).1.real
      {w | w.A ∈ s ∧ (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t} =
    (largeAlphabetLaw q ξ hd hq hq1).1.real {w | w.A ∈ s} *
      (largeAlphabetLaw q ξ hd hq hq1).1.real
        {w | (w.X, w.S0, w.S1, w.Y0, w.Y1) ∈ t}
  rw [largeAlphabetLaw_arm_event_factor, largeAlphabetLaw_arm_mass]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,ξ,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_model
lemma largeAlphabetLaw_model {n d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    UnrestrictedArrivalModelClass n d q (largeAlphabetLaw q ξ hd hq hq1) := by
  refine ⟨hn, hd, hq, hq1, largeAlphabetLaw_randomized q ξ hd hq hq1,
    largeAlphabetLaw_balanced q ξ hd hq hq1, ?_, ?_,
    largeAlphabetLaw_mar q ξ hd hq hq1,
    largeAlphabetLaw_occupiedCellArrival q ξ hd hq hq1⟩
  all_goals filter_upwards [] with w; rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,f), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_integral
lemma largeAlphabetLaw_integral {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (f : FullRecord d → ℝ) :
    (∫ w, f w ∂(largeAlphabetLaw q ξ hd hq hq1).1) =
      ∑ x : Fin d, ∑ a : Bool, ∑ r : Bool,
        (1 / (2 * (d : ℝ))) * completeBernWeight (largeAlphabetArrival q ξ x a) r *
          f (largeAlphabetRecord ξ x a r) := by
  have hi (x : Fin d) (a r : Bool) : Integrable f
      (ENNReal.ofReal ((1 / (2 * (d : ℝ))) *
        completeBernWeight (largeAlphabetArrival q ξ x a) r) •
          Measure.dirac (largeAlphabetRecord ξ x a r)) := by
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hir (x : Fin d) (a : Bool) : Integrable f
      (∑ r : Bool, ENNReal.ofReal ((1 / (2 * (d : ℝ))) *
        completeBernWeight (largeAlphabetArrival q ξ x a) r) •
          Measure.dirac (largeAlphabetRecord ξ x a r)) := by
    apply integrable_finsetSum_measure.mpr
    intro r _
    exact hi x a r
  have hia (x : Fin d) : Integrable f
      (∑ a : Bool, ∑ r : Bool, ENNReal.ofReal ((1 / (2 * (d : ℝ))) *
        completeBernWeight (largeAlphabetArrival q ξ x a) r) •
          Measure.dirac (largeAlphabetRecord ξ x a r)) := by
    apply integrable_finsetSum_measure.mpr
    intro a _
    exact hir x a
  change (∫ w, f w ∂largeAlphabetMeasure q ξ) = _
  rw [largeAlphabetMeasure, integral_finsetSum_measure (by intro x _; exact hia x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum_measure (by intro a _; exact hir x a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum_measure (by intro r _; exact hi x a r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_smul_measure, integral_dirac]
  rw [ENNReal.toReal_ofReal (largeAlphabet_weight_nonneg q ξ hq hq1 x a r)]
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_ate
lemma largeAlphabetLaw_ate {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    ate (largeAlphabetLaw q ξ hd hq hq1) = cellPriorTarget ξ := by
  rw [ate, largeAlphabetLaw_integral]
  unfold cellPriorTarget
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : ξ x <;>
    simp [largeAlphabetRecord, completeBernWeight, largeAlphabetArrival, hx] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,o), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_observed_atom
lemma largeAlphabetLaw_observed_atom {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (o : ObsRecord d) :
    ((largeAlphabetLaw q ξ hd hq hq1).1.map obs).real {o} =
      if o.S = false ∧ o.RY = (o.R && (o.A && ξ o.X)) then
        (1 / (2 * (d : ℝ))) * completeBernWeight (largeAlphabetArrival q ξ o.X o.A) o.R
      else 0 := by
  classical
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by simp)]
  change (largeAlphabetLaw q ξ hd hq hq1).1.real (obs ⁻¹' {o}) = _
  rw [largeAlphabetLaw_real_event]
  rcases o with ⟨x, a, s, r, ry⟩
  cases a <;> cases s <;> cases r <;> cases ry <;>
    simp [obs, largeAlphabetRecord, FullRecord.S, FullRecord.Y, completeBernWeight,
      ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq']

end CausalSmith.Stat.MarRareqLogfrontier
