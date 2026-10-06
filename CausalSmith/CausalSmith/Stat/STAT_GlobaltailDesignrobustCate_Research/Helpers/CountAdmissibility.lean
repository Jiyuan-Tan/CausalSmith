module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ObservedMass
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Risk

/-! # Count admissibility for tail adaptation

The count-only measurable events and the exponential Markov and admissibility
splitting steps in equations (5) and (7) of the adaptation roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped BigOperators

/-- Subcell admissibility is equivalently a lower bound on every cell's minimum count. -/
-- @node: selectorAdmissible_iff_minimumCount
lemma selectorAdmissible_iff_minimumCount {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β : ℝ) :
    selectorAdmissible sample j β ↔ ∀ Q : Fin d → Fin (2 ^ j),
      selectorThreshold j β ≤ minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q := by
  classical
  simp [selectorAdmissible, minimumCellCount]

/-- Admissibility is a measurable event determined by the observed subcell counts. -/
-- @node: selectorAdmissible_measurableSet
lemma selectorAdmissible_measurableSet (d n j : ℕ) (β : ℝ) :
    MeasurableSet {sample : Fin n → Obs d | selectorAdmissible sample j β} := by
  have heq : {sample : Fin n → Obs d | selectorAdmissible sample j β} =
      ⋂ Q : Fin d → Fin (2 ^ j), {sample | selectorThreshold j β ≤
        minimumCellCount sample true j (polynomialOrder β) (normingSubcells d β).radius Q} := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, selectorAdmissible_iff_minimumCount]
  rw [heq]
  apply MeasurableSet.iInter
  intro Q
  exact (measurableSet_Ici : MeasurableSet (Set.Ici (selectorThreshold j β))).preimage
    (minimumCellCount_measurable true j (polynomialOrder β) (normingSubcells d β).radius Q)

/-- The threshold is at least the inverse squared bias scale. -/
-- @node: selectorThreshold_lower
lemma selectorThreshold_lower (j : ℕ) (β : ℝ) :
    (dyadicWidth j) ^ (-(2 * β)) ≤ (selectorThreshold j β : ℝ) := by
  exact Nat.le_ceil _

/-- The count threshold is at most twice the inverse squared bias scale. -/
-- @node: selectorThreshold_upper
lemma selectorThreshold_upper (j : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    (selectorThreshold j β : ℝ) ≤ 2 * (dyadicWidth j) ^ (-(2 * β)) := by
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hh1 : dyadicWidth j ≤ 1 := by
    unfold dyadicWidth
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hpow : 1 ≤ (dyadicWidth j) ^ (-(2 * β)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hh1 (by linarith)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (dyadicWidth j) ^ (-(2 * β)))
  change (Nat.ceil ((dyadicWidth j) ^ (-(2 * β))) : ℝ) ≤ _
  linarith

/-- The fixed tilt-one Chernoff exponent is strictly positive. -/
-- @node: countTilt_one_positive
lemma countTilt_one_positive : 0 < 1 - Real.exp (-1) - (1 / 2 : ℝ) := by
  have hexp : 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hinv : Real.exp (-1) < (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hexp)
  linarith

/-- Equation (5) applied to the minimum count: if the expected minimum mass
is twice the threshold, the cell fails with exponentially small probability. -/
-- @node: minimumTreatedCount_below_threshold
lemma minimumTreatedCount_below_threshold {d n : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (hn : 0 < n) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j))
    (hmean : 2 * (selectorThreshold j β : ℝ) ≤ (n : ℝ) *
      minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) :
    (P.sample n).real {sample | minimumCellCount sample true j (polynomialOrder β)
      (normingSubcells d β).radius Q < selectorThreshold j β} ≤
      (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        Real.exp (-(1 - Real.exp (-1) - 1 / 2) * (n : ℝ) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) := by
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hP.iid hP.consistency
  have : IsProbabilityMeasure (P.sample n) := by
    rw [sample_eq_pi_obs P hP.iid hP.consistency hn]
    infer_instance
  have hsub : {sample : Fin n → Obs d | minimumCellCount sample true j (polynomialOrder β)
      (normingSubcells d β).radius Q < selectorThreshold j β} ⊆
      {sample | (minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q : ℝ) ≤ (selectorThreshold j β : ℝ)} := by
    intro sample hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    exact_mod_cast hs.le
  apply (measureReal_mono hsub).trans
  apply (minimumTreatedCount_lower_tail P β γ C L M hP hn j Q 1
    (selectorThreshold j β) (by norm_num)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith only [hmean]

/-- Union over parent cells retains their individual masses, ready for the
ordered-mass summation in equation (6); no extra independence is used. -/
-- @node: selectorAdmissible_failure_le_sum
lemma selectorAdmissible_failure_le_sum {d n : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (hn : 0 < n) (j : ℕ)
    (hmean : ∀ Q : Fin d → Fin (2 ^ j), 2 * (selectorThreshold j β : ℝ) ≤ (n : ℝ) *
      minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) :
    (P.sample n).real {sample | ¬ selectorAdmissible sample j β} ≤
      (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
        ∑ Q : Fin d → Fin (2 ^ j), Real.exp (-(1 - Real.exp (-1) - 1 / 2) * (n : ℝ) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) := by
  classical
  have heq : {sample : Fin n → Obs d | ¬ selectorAdmissible sample j β} =
      ⋃ Q : Fin d → Fin (2 ^ j), {sample | minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q < selectorThreshold j β} := by
    ext sample
    simp [selectorAdmissible_iff_minimumCount]
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun Q _ =>
    minimumTreatedCount_below_threshold P β γ C L M hP hn j Q (hmean Q))

/-- Equation (7)'s pointwise exponential split on an admissible cell. -/
-- @node: admissible_count_exp_split
lemma admissible_count_exp_split (s N H : ℝ) (hs : 0 ≤ s) (hNH : H ≤ N) :
    Real.exp (-s * N) ≤ Real.exp (-s * H / 2) * Real.exp (-(s / 2) * N) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hNH hs]

/-- Membership in the selector grid separates the deterministic grid condition
from the count-only admissibility condition. -/
-- @node: mem_admissibleLevels_iff
lemma mem_admissibleLevels_iff {d n : ℕ} (sample : Fin n → Obs d) (β : ℝ) (j : ℕ) :
    j ∈ admissibleLevels sample β ↔ j ≤ selectorMaxLevel d n β ∧
      selectorAdmissible sample j β := by
  classical
  simp [admissibleLevels]

/-- The entire finite set of admissible scales is a measurable count statistic. -/
-- @node: admissibleLevels_measurable
@[fun_prop] lemma admissibleLevels_measurable (d n : ℕ) (β : ℝ) :
    Measurable (fun sample : Fin n → Obs d => admissibleLevels sample β) := by
  classical
  apply measurable_finset_iff.mpr
  intro j
  apply measurableSet_setOfPred.mp
  simp only [mem_admissibleLevels_iff]
  by_cases hj : j ≤ selectorMaxLevel d n β
  · simpa only [hj, true_and] using selectorAdmissible_measurableSet d n j β
  · simp only [hj, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- The event that a particular grid level is selected is measurable, so
outcome concentration can be restricted to it in equation (7). -/
-- @node: selectedLevel_measurableSet
lemma selectedLevel_measurableSet (d n : ℕ) (β : ℝ) (j : ℕ) :
    MeasurableSet {sample : Fin n → Obs d | ∃ h : (admissibleLevels sample β).Nonempty,
      (admissibleLevels sample β).max' h = j} := by
  have hset : MeasurableSet {s : Finset ℕ | ∃ h : s.Nonempty, s.max' h = j} :=
    (Set.to_countable _).measurableSet
  exact hset.preimage (admissibleLevels_measurable d n β)

/-- The finest selected level belongs to the grid and is itself admissible. -/
-- @node: selectedLevel_admissible
lemma selectedLevel_admissible {d n : ℕ} (sample : Fin n → Obs d) (β : ℝ)
    (h : (admissibleLevels sample β).Nonempty) :
    (admissibleLevels sample β).max' h ≤ selectorMaxLevel d n β ∧
      selectorAdmissible sample ((admissibleLevels sample β).max' h) β := by
  exact (mem_admissibleLevels_iff sample β _).mp (Finset.max'_mem _ h)

/-- On the good event that an analysis scale is admissible, the smallest-width
rule selects a width no greater than that analysis width. -/
-- @node: selectedWidth_le_admissibleWidth
lemma selectedWidth_le_admissibleWidth {d n : ℕ} (sample : Fin n → Obs d) (β : ℝ)
    (h : (admissibleLevels sample β).Nonempty) (j : ℕ)
    (hj : j ≤ selectorMaxLevel d n β) (ha : selectorAdmissible sample j β) :
    dyadicWidth ((admissibleLevels sample β).max' h) ≤ dyadicWidth j := by
  have hmem := (mem_admissibleLevels_iff sample β j).mpr ⟨hj, ha⟩
  have hlevel := (admissibleLevels sample β).le_max' j hmem
  unfold dyadicWidth
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlevel)

/-- Averaging equation (7)'s split pays an admissibility threshold factor and
leaves a half-tilt count Laplace transform, already controlled by ObservedMass. -/
-- @node: admissible_count_laplace_split
lemma admissible_count_laplace_split {d n : ℕ} (P : Law d) (β γ C L M : ℝ)
    (hP : LawClass d β γ C L M P) (hn : 0 < n) (j : ℕ)
    (Q : Fin d → Fin (2 ^ j)) (s : ℝ) (hs : 0 ≤ s) :
    (∫ sample, {sample | selectorAdmissible sample j β}.indicator
      (fun sample => Real.exp (-s * (minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q : ℝ))) sample ∂P.sample n) ≤
      Real.exp (-s * (selectorThreshold j β : ℝ) / 2) *
        ((Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
          Real.exp (-(n : ℝ) *
            minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
            (1 - Real.exp (-(s / 2))))) := by
  classical
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hP.iid hP.consistency
  have : IsProbabilityMeasure (P.sample n) := by
    rw [sample_eq_pi_obs P hP.iid hP.consistency hn]
    infer_instance
  let N : (Fin n → Obs d) → ℝ := fun sample =>
    minimumCellCount sample true j (polynomialOrder β) (normingSubcells d β).radius Q
  have hN : Measurable N := by fun_prop
  have hint : Integrable (fun sample => Real.exp (-(s / 2) * N sample)) (P.sample n) := by
    apply Integrable.of_bound (hN.const_mul (-(s / 2))).exp.aestronglyMeasurable 1
    apply ae_of_all
    intro sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  calc
    _ ≤ ∫ sample, Real.exp (-s * (selectorThreshold j β : ℝ) / 2) *
        Real.exp (-(s / 2) * N sample) ∂P.sample n := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun sample => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) sample)
      · exact hint.const_mul _
      · apply ae_of_all
        intro sample
        by_cases ha : selectorAdmissible sample j β
        · rw [Set.indicator_of_mem ha]
          apply admissible_count_exp_split s (N sample) _ hs
          dsimp [N]
          exact_mod_cast (selectorAdmissible_iff_minimumCount sample j β).mp ha Q
        · rw [Set.indicator_of_notMem ha]
          positivity
    _ = Real.exp (-s * (selectorThreshold j β : ℝ) / 2) *
        ∫ sample, Real.exp (-(s / 2) * N sample) ∂P.sample n := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (minimumTreatedCount_laplace_le P β γ C L M hP hn j Q (s / 2) (by positivity))
      (Real.exp_nonneg _)

end CausalSmith.Stat.GlobalTailDesignRobustCate
