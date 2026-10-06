module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationPriorTarget
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticKernel

/-! Cell probabilities and MAR factorization for the activated full-data laws.
These construction identities supply the model obligations used when averaging
coverage over the finite reciprocal priors. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

variable (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ)
  (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
  (hslice : RareArrivalSlice n q)
  (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))

/-- Given [the event](hyp:E), [the stated activated-law mass identity holds](goal). -/
-- @node: activatedFullLaw_real_event
lemma activatedFullLaw_real_event (E : Set (FullRecord d)) :
    (activatedFullLaw η n d q z hd hb hq hslice hz).1.real E = by
      classical
      exact ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool, ∑ r : Bool,
        if lowerFullRecord x a y r ∈ E then
          baselineMass η n d q x / 2 *
            bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y *
            bernWeight (q * lowerCellZ η n d q z x) r else 0 := by
  classical
  simp only [activatedFullLaw, activatedLaw, Measure.real, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [ENNReal.toReal_sum (by simp [ENNReal.sum_ne_top, ite_eq_iff])]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.toReal_sum (by simp [ENNReal.sum_ne_top, ite_eq_iff])]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_sum (by simp [ENNReal.sum_ne_top, ite_eq_iff])]
  apply Finset.sum_congr rfl
  intro y _
  rw [ENNReal.toReal_sum (by simp [ENNReal.sum_ne_top, ite_eq_iff])]
  apply Finset.sum_congr rfl
  intro r _
  by_cases he : lowerFullRecord x a y r ∈ E
  · simp only [if_pos he]
    exact ENNReal.toReal_ofReal
      (activatedLaw_weight_nonneg η n d q z hb hq hslice hz x y r)
  · simp only [if_neg he, ENNReal.toReal_zero]

/-- Given [an arm, cell, and surrogate value](hyp:a,x,s), [the activated cell probability has the displayed form](goal). -/
-- @node: activatedFullLaw_cellProb
lemma activatedFullLaw_cellProb (a : Bool) (x : Fin d) (s : Bool) :
    cellProb (activatedFullLaw η n d q z hd hb hq hslice hz) (a, x, s) =
      if s then 0 else baselineMass η n d q x / 2 := by
  classical
  rw [cellProb, activatedFullLaw_real_event η n d q z hd hb hq hslice hz]
  cases a <;> cases s <;>
    simp [inCell, lowerFullRecord, FullRecord.S, bernWeight,
      Finset.sum_ite_irrel, Finset.sum_ite_eq']
  all_goals split_ifs <;> ring

/-- Given [an arm, cell, and surrogate value](hyp:a,x,s), [the activated arrived-cell mass has the displayed form](goal). -/
-- @node: activatedFullLaw_arrivedCell
lemma activatedFullLaw_arrivedCell (a : Bool) (x : Fin d) (s : Bool) :
    arrivedCell (activatedFullLaw η n d q z hd hb hq hslice hz) (a, x, s) =
      q * lowerCellZ η n d q z x *
        cellProb (activatedFullLaw η n d q z hd hb hq hslice hz) (a, x, s) := by
  classical
  rw [arrivedCell, activatedFullLaw_real_event η n d q z hd hb hq hslice hz,
    activatedFullLaw_cellProb η n d q z hd hb hq hslice hz]
  cases a <;> cases s <;>
    simp [inCell, lowerFullRecord, FullRecord.S, bernWeight,
      Finset.sum_ite_irrel, Finset.sum_ite_eq']
  all_goals split_ifs <;> ring

/-- The activated law [satisfies occupied-cell arrival](goal). -/
-- @node: activatedFullLaw_occupiedCellArrival
lemma activatedFullLaw_occupiedCellArrival :
    OccupiedCellArrival q (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  intro j hj
  rcases j with ⟨a, x, s⟩
  rw [activatedFullLaw_arrivedCell η n d q z hd hb hq hslice hz]
  have hcell : 1 ≤ lowerCellZ η n d q z x := by
    unfold lowerCellZ
    split_ifs
    · exact (hz x).1
    · exact lowerEndpoint_one_le n q hq.le
  have hfactor : q ≤ q * lowerCellZ η n d q z x := by nlinarith
  exact mul_le_mul_of_nonneg_right hfactor hj.le

/-- The activated law [satisfies arrival MAR](goal). -/
-- @node: activatedFullLaw_mar
lemma activatedFullLaw_mar :
    ArrivalMAR (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  classical
  intro j y r
  rcases j with ⟨a, x, s⟩
  rw [activatedFullLaw_cellProb η n d q z hd hb hq hslice hz]
  simp_rw [activatedFullLaw_real_event η n d q z hd hb hq hslice hz]
  cases a <;> cases s <;> cases y <;> cases r <;>
    simp [inCell, lowerFullRecord, FullRecord.S, FullRecord.Y, bernWeight, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, Finset.sum_ite_eq']
  all_goals split_ifs <;> ring
  all_goals simp only [true_or]

/-- The activated law [satisfies surrogate and outcome consistency](goal). -/
-- @node: activatedFullLaw_consistency
lemma activatedFullLaw_consistency :
    SurrogateConsistency (activatedFullLaw η n d q z hd hb hq hslice hz) ∧
      OutcomeConsistency (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  constructor <;> filter_upwards [] with r <;> rfl

/-- The activated law [has balanced treatment assignment](goal). -/
-- @node: activatedFullLaw_balanced
lemma activatedFullLaw_balanced :
    BalancedRandomization (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  classical
  rw [BalancedRandomization, activatedFullLaw_real_event η n d q z hd hb hq hslice hz]
  calc
    _ = ∑ x : Fin d, baselineMass η n d q x / 2 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hr : x.val < rareCount η n d q <;>
        simp [lowerFullRecord, bernWeight, hr] <;> ring
    _ = 1 / 2 := by rw [← Finset.sum_div, baselineMass_sum η n d q hd]

/-- For [arm and latent events](hyp:s,t), [the activated-law joint mass factors](goal). -/
-- @node: activatedFullLaw_arm_event_factor
lemma activatedFullLaw_arm_event_factor (s : Set Bool)
    (t : Set (Fin d × Bool × Bool × Bool × Bool)) :
    (activatedFullLaw η n d q z hd hb hq hslice hz).1.real
      {r | r.A ∈ s ∧ (r.X, r.S0, r.S1, r.Y0, r.Y1) ∈ t} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) *
      (activatedFullLaw η n d q z hd hb hq hslice hz).1.real
        {r | (r.X, r.S0, r.S1, r.Y0, r.Y1) ∈ t} := by
  classical
  rw [activatedFullLaw_real_event η n d q z hd hb hq hslice hz,
    activatedFullLaw_real_event η n d q z hd hb hq hslice hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hsT : true ∈ s <;> by_cases hsF : false ∈ s <;>
    by_cases htT : (x, false, false, false, true) ∈ t <;>
    by_cases htF : (x, false, false, false, false) ∈ t <;>
    simp [lowerFullRecord, bernWeight, hsT, hsF, htT, htF]
  all_goals split_ifs <;> ring

/-- For [an arm event](hyp:s), [the activated-law arm mass has the displayed value](goal). -/
-- @node: activatedFullLaw_arm_mass
lemma activatedFullLaw_arm_mass (s : Set Bool) :
    (activatedFullLaw η n d q z hd hb hq hslice hz).1.real {r | r.A ∈ s} =
      (by classical exact ((if true ∈ s then (1 : ℝ) else 0) +
        (if false ∈ s then (1 : ℝ) else 0)) / 2) := by
  let := (activatedFullLaw η n d q z hd hb hq hslice hz).2
  simpa using activatedFullLaw_arm_event_factor η n d q z hd hb hq hslice hz s univ

/-- The activated law [has randomized treatment independent of latent variables](goal). -/
-- @node: activatedFullLaw_randomized
lemma activatedFullLaw_randomized :
    RandomizedIndependence (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  let := (activatedFullLaw η n d q z hd hb hq hslice hz).2
  rw [RandomizedIndependence, indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  change (activatedFullLaw η n d q z hd hb hq hslice hz).1.real
      {r | r.A ∈ s ∧ (r.X, r.S0, r.S1, r.Y0, r.Y1) ∈ t} =
    (activatedFullLaw η n d q z hd hb hq hslice hz).1.real {r | r.A ∈ s} *
      (activatedFullLaw η n d q z hd hb hq hslice hz).1.real
        {r | (r.X, r.S0, r.S1, r.Y0, r.Y1) ∈ t}
  rw [activatedFullLaw_arm_event_factor η n d q z hd hb hq hslice hz,
    activatedFullLaw_arm_mass η n d q z hd hb hq hslice hz]

/-- Given [a positive sample size](hyp:hn), [the activated law belongs to the rare-arrival model](goal). -/
-- @node: activatedFullLaw_model
lemma activatedFullLaw_model (hn : 1 ≤ n) :
    RareArrivalModelClass n d q
      (activatedFullLaw η n d q z hd hb hq hslice hz) := by
  have hq1 : q ≤ 1 := by
    have hH := lowerEndpoint_one_le n q hq.le
    have hactivation := lower_activation_probability_le_one n q hq.le hslice
    nlinarith
  exact ⟨sampleLaw_iid n _,
    activatedFullLaw_randomized η n d q z hd hb hq hslice hz,
    activatedFullLaw_balanced η n d q z hd hb hq hslice hz,
    (activatedFullLaw_consistency η n d q z hd hb hq hslice hz).1,
    (activatedFullLaw_consistency η n d q z hd hb hq hslice hz).2,
    activatedFullLaw_mar η n d q z hd hb hq hslice hz,
    activatedFullLaw_occupiedCellArrival η n d q z hd hb hq hslice hz,
    hslice, hn, hd, hq, hq1⟩

end CausalSmith.Stat.MarRareqLogfrontier
