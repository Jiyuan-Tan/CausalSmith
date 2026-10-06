module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioVariance
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.IdealEstimator
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments

/-! Exact random membership-weight moments in roadmap (3), (21), and (24). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- For [the specified inputs and assumptions](hyp:n,d,P,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: membershipStreamIntensity
noncomputable def membershipStreamIntensity (n : ℕ) {d : ℕ}
    (P : FullLaw d) (j : Cell d) : ℝ≥0 :=
  ((n : ℝ≥0) / 2) *
    ((markedObsLaw P) (streamEvent 0 j false false)).toNNReal

-- @node: coe_membershipStreamIntensity
/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
lemma coe_membershipStreamIntensity (n : ℕ) {d : ℕ}
    (P : FullLaw d) (j : Cell d) :
    (membershipStreamIntensity n P j : ℝ) = streamSize n * cellProb P j := by
  unfold membershipStreamIntensity
  change ((n : ℝ) / 2) *
    ((markedObsLaw P) (streamEvent 0 j false false)).toReal = _
  rw [← measureReal_def, markedObsLaw_streamEvent_real,
    map_obsStreamEvent_membership_real]
  unfold streamSize
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: map_membershipCount_eq_poisson
lemma map_membershipCount_eq_poisson (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    Measure.map (fun s ↦ eventCount s (streamEvent 0 j false false))
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      poissonMeasure (membershipStreamIntensity n P j) := by
  classical
  exact finitePoissonSampleLaw_map_eventCount (markedObsLaw P) ((n : ℝ≥0) / 2)
    (streamEvent 0 j false false) (Set.Finite.measurableSet (Set.toFinite _))

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonMemberWeight
lemma memLp_poissonMemberWeight (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    MemLp (poissonMemberWeight n j) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  have h := Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
    (membershipStreamIntensity n P j)
  rw [← map_membershipCount_eq_poisson n d P j] at h
  have hc := h.comp_of_map
    (measurable_eventCount (streamEvent 0 j false false)
      (Set.Finite.measurableSet (Set.toFinite _))).aemeasurable
  change MemLp (fun s ↦ (eventCount s (streamEvent 0 j false false) : ℝ) /
    streamSize n) 2 _
  simpa [Function.comp_def, div_eq_mul_inv] using
    hc.mul_const (streamSize n)⁻¹

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_poissonMemberWeight
lemma integral_poissonMemberWeight (n d : ℕ) (P : FullLaw d) (j : Cell d)
    (hn : 0 < n) :
    (∫ s, poissonMemberWeight n j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) = cellProb P j := by
  classical
  have hm : streamSize n ≠ 0 := by
    unfold streamSize
    exact div_ne_zero (by exact_mod_cast hn.ne') (by norm_num)
  unfold poissonMemberWeight
  rw [integral_div]
  rw [← integral_map
    (measurable_eventCount (streamEvent 0 j false false)
      (Set.Finite.measurableSet (Set.toFinite _))).aemeasurable
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).aestronglyMeasurable,
    map_membershipCount_eq_poisson, poisson_count_first_moment,
    coe_membershipStreamIntensity]
  exact mul_div_cancel_left₀ _ hm

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonMemberWeight
lemma integral_sq_poissonMemberWeight (n d : ℕ) (P : FullLaw d) (j : Cell d)
    (hn : 0 < n) :
    (∫ s, (poissonMemberWeight n j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      (cellProb P j) ^ 2 + cellProb P j / streamSize n := by
  classical
  have hm : streamSize n ≠ 0 := by
    unfold streamSize
    exact div_ne_zero (by exact_mod_cast hn.ne') (by norm_num)
  simp only [poissonMemberWeight, div_pow]
  rw [integral_div]
  rw [← integral_map
    (measurable_eventCount (streamEvent 0 j false false)
      (Set.Finite.measurableSet (Set.toFinite _))).aemeasurable
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ) ^ 2)).aestronglyMeasurable,
    map_membershipCount_eq_poisson, poisson_count_second_moment,
    coe_membershipStreamIntensity]
  field_simp

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_poissonMemberWeight
lemma variance_poissonMemberWeight (n d : ℕ) (P : FullLaw d) (j : Cell d)
    (hn : 0 < n) :
    variance (poissonMemberWeight n j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      cellProb P j / streamSize n := by
  rw [variance_eq_sub (memLp_poissonMemberWeight n d P j)]
  change (∫ s, (poissonMemberWeight n j s) ^ 2
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
    (∫ s, poissonMemberWeight n j s
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ^ 2 = _
  rw [integral_sq_poissonMemberWeight n d P j hn,
    integral_poissonMemberWeight n d P j hn]
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,P,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_integral_sq_poissonMemberWeight_le
lemma sum_integral_sq_poissonMemberWeight_le (n d : ℕ) (P : FullLaw d)
    (hn : 0 < n) :
    (∑ j : Cell d, ∫ s, (poissonMemberWeight n j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      1 + 1 / streamSize n := by
  have hp (j : Cell d) : cellProb P j ≤ 1 := by
    calc
      cellProb P j ≤ ∑ i : Cell d, cellProb P i :=
        Finset.single_le_sum
          (fun i _ ↦ (show 0 ≤ cellProb P i from measureReal_nonneg)) (Finset.mem_univ j)
      _ = 1 := sum_cellProb_eq_one P
  calc
    _ = ∑ j : Cell d, ((cellProb P j) ^ 2 + cellProb P j / streamSize n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_sq_poissonMemberWeight n d P j hn
    _ ≤ ∑ j : Cell d, (cellProb P j + cellProb P j / streamSize n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonneg : 0 ≤ cellProb P j := measureReal_nonneg
      nlinarith [hp j]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_cellProb_eq_one]

/-- Given [the specified inputs and assumptions](hyp:n,d,P,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_membershipVariance_mul_ratioSecondMoment_le
lemma sum_membershipVariance_mul_ratioSecondMoment_le
    (n d : ℕ) (P : FullLaw d) (hn : 0 < n) :
    (∑ j : Cell d,
      variance (poissonMemberWeight n j)
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) *
      (∫ s, (poissonRatioBranch j s) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))) ≤
      1 / streamSize n := by
  have hm : 0 < streamSize n := by
    unfold streamSize
    exact div_pos (by exact_mod_cast hn) (by norm_num)
  calc
    _ ≤ ∑ j : Cell d, cellProb P j / streamSize n := by
      apply Finset.sum_le_sum
      intro j hj
      rw [variance_poissonMemberWeight n d P j hn]
      have hsecond : (∫ s, (poissonRatioBranch j s) ^ 2
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤ 1 := by
        calc
          _ ≤ ∫ _s : FiniteSample (ObsRecord d × Fin 3), (1 : ℝ)
              ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) := by
            apply integral_mono (integrable_poissonRatioBranch_sq n d P j)
              (integrable_const _)
            intro s
            rcases poissonRatioBranch_mem_unitInterval j s with ⟨hs0, hs1⟩
            nlinarith
          _ = 1 := by simp
      simpa using mul_le_mul_of_nonneg_left hsecond
        (div_nonneg (show 0 ≤ cellProb P j from measureReal_nonneg) hm.le)
    _ = _ := by rw [← Finset.sum_div, sum_cellProb_eq_one]

end CausalSmith.Stat.MarRareqLogfrontier
