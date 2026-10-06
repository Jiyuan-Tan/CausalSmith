module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathOptionalVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.VarianceEstimatorMeasurability

/-!
# Pathwise comparison for the future-mark death studentizer

Uniform error in the estimated remaining mean controls its death optional
variation on a strict horizon. This is a finite-sum comparison and does not
require the estimated remaining mean to be predictable. Terminal variation
is partitioned exactly and its plug-in difference is bounded by the squared
deterministic remaining-horizon envelope, without a factor of two.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The ordinary remaining target lies in its deterministic projection interval. -/
-- @node: remainingTarget_zero_mem_Icc
lemma remainingTarget_zero_mem_Icc (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    remainingTarget c P a 0 u ∈ Icc 0 (c.lambdaMax * (1 - u)) := by
  have hi := (modelClass_target_intervalIntegrable c P hP a).mono_set
    (show uIcc u 1 ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le hu.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hu.1 le_rfl)
  have hnonneg : ∀ t ∈ Icc u 1, 0 ≤ survival P a t * P.lam a t := by
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le
      (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ⟨hu.1.trans ht.1, ht.2⟩).1)
  have hbound : ∀ t ∈ Icc u 1, survival P a t * P.lam a t ≤ c.lambdaMax := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1, ht.2⟩
    have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ht01).2
    have hl := hP.recurrenceBounds a t ht01
    calc
      _ ≤ 1 * P.lam a t := mul_le_mul_of_nonneg_right hs (c.lambdaMin_pos.le.trans hl.1)
      _ ≤ c.lambdaMax := by simpa using hl.2
  simp only [remainingTarget, continuationWeight, if_true, sub_zero, one_mul]
  refine ⟨intervalIntegral.integral_nonneg hu.2 hnonneg, ?_⟩
  calc
    _ ≤ ∫ _t in u..1, c.lambdaMax :=
      intervalIntegral.integral_mono_on hu.2 hi intervalIntegrable_const hbound
    _ = c.lambdaMax * (1 - u) := by simp [mul_comm]

/-- The estimated remaining mean obeys the same projection bounds. -/
-- @node: remainingMeanHat_mem_Icc
lemma remainingMeanHat_mem_Icc (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {u : ℝ} (hu : u ≤ 1) :
    remainingMeanHat c a s u ∈ Icc 0 (c.lambdaMax * (1 - u)) := by
  have hmax : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  exact ⟨le_max_left _ _, max_le (mul_nonneg hmax (sub_nonneg.mpr hu))
    (min_le_left _ _)⟩

/-- Uniform remaining-mean error controls squared coefficients with the
model's exact bounded envelope. -/
-- @node: remainingMeanHat_sq_error_le
lemma remainingMeanHat_sq_error_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (he : |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤ ε) :
    |remainingMeanHat c a s u ^ 2 - remainingTarget c P a 0 u ^ 2| ≤
      2 * c.lambdaMax * ε := by
  have hh := remainingMeanHat_mem_Icc c a s hu.2
  have ht := remainingTarget_zero_mem_Icc c P hP a hu
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hb : c.lambdaMax * (1 - u) ≤ c.lambdaMax := by nlinarith [hu.1]
  have he0 : 0 ≤ ε := (abs_nonneg _).trans he
  rw [show remainingMeanHat c a s u ^ 2 - remainingTarget c P a 0 u ^ 2 =
    (remainingMeanHat c a s u - remainingTarget c P a 0 u) *
      (remainingMeanHat c a s u + remainingTarget c P a 0 u) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hh.1 ht.1)]
  calc
    _ ≤ ε * (2 * c.lambdaMax) :=
      mul_le_mul he (by linarith [hh.2, ht.2]) (add_nonneg hh.1 ht.1) he0
    _ = _ := by ring

/-- Death optional variation with an arbitrary remaining-mean coefficient,
restricted to a deterministic horizon. -/
-- @node: localizedDeathVariation
noncomputable def localizedDeathVariation (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (T : ℝ) (H : ℝ → ℝ) : ℝ :=
  (n : ℝ) * ∑ i : Fin n,
    if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
      H (s i).exit ^ 2 * invRisk a s (s i).exit ^ 2 else 0

/-- Uniform plug-in error bounds the difference in localized death variation
by the total inverse-risk squared death variation, on every sample path. -/
-- @node: localizedDeathVariation_plugin_error_le
lemma localizedDeathVariation_plugin_error_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {T ε : ℝ} (hT : T ≤ 1)
    (hExit : ∀ i, 0 ≤ (s i).exit)
    (he : ∀ u ∈ Icc (0 : ℝ) T,
      |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤ ε) :
    |localizedDeathVariation a s T (remainingMeanHat c a s) -
      localizedDeathVariation a s T (remainingTarget c P a 0)| ≤
      2 * c.lambdaMax * ε * ((n : ℝ) * ∑ i : Fin n,
        if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
          invRisk a s (s i).exit ^ 2 else 0) := by
  classical
  unfold localizedDeathVariation
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (n : ℝ) * ∑ i : Fin n, |(if (s i).treatment = a ∧ (s i).deathInd ∧
        (s i).exit ≤ T then remainingMeanHat c a s (s i).exit ^ 2 *
          invRisk a s (s i).exit ^ 2 else 0) -
      (if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
        remainingTarget c P a 0 (s i).exit ^ 2 * invRisk a s (s i).exit ^ 2 else 0)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)
    _ ≤ (n : ℝ) * ∑ i : Fin n, (2 * c.lambdaMax * ε) *
        (if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
          invRisk a s (s i).exit ^ 2 else 0) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have hu : (s i).exit ∈ Icc (0 : ℝ) T := ⟨hExit i, hi.2.2⟩
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (invRisk a s (s i).exit))]
        exact mul_le_mul_of_nonneg_right
          (remainingMeanHat_sq_error_le c P hP a s ⟨hu.1, hu.2.trans hT⟩ (he _ hu))
          (sq_nonneg _)
      · simp
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A lower bound on the empirical risk fraction controls the scaled inverse
risk at the same time, including the totalized zero-risk convention. -/
-- @node: scaledInvRisk_le_of_riskFraction_lower
lemma scaledInvRisk_le_of_riskFraction_lower {n : ℕ} (hn : 0 < n)
    (a : Arm) (s : Fin n → ObsHistory) {t δ : ℝ} (hδ : 0 < δ)
    (hr : (n : ℝ) * δ ≤ riskSet a s t) :
    (n : ℝ) * invRisk a s t ≤ δ⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hy : 0 < (riskSet a s t : ℝ) := (mul_pos hnR hδ).trans_le hr
  have hz : riskSet a s t ≠ 0 := by exact_mod_cast hy.ne'
  simp only [invRisk, hz, ↓reduceIte]
  apply (mul_le_mul_iff_right₀ hy).mp
  apply (mul_le_mul_iff_right₀ hδ).mp
  field_simp
  nlinarith

/-- A positive lower empirical risk fraction bounds localized inverse-risk
squared death variation by a fixed constant. No independence is used. -/
-- @node: localizedDeathVariation_one_le
lemma localizedDeathVariation_one_le (a : Arm) {n : ℕ} (hn : 0 < n)
    (s : Fin n → ObsHistory) {T δ : ℝ} (hδ : 0 < δ)
    (hr : ∀ i, (s i).treatment = a → (s i).deathInd → (s i).exit ≤ T →
      (n : ℝ) * δ ≤ riskSet a s (s i).exit) :
    localizedDeathVariation a s T (fun _ => 1) ≤ δ⁻¹ ^ 2 := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb (i : Fin n) :
      (if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ T then
        invRisk a s (s i).exit ^ 2 else 0) ≤ δ⁻¹ ^ 2 / (n : ℝ) ^ 2 := by
    split_ifs with hi
    · have hscaled := scaledInvRisk_le_of_riskFraction_lower hn a s hδ
        (hr i hi.1 hi.2.1 hi.2.2)
      have hsq : ((n : ℝ) * invRisk a s (s i).exit) ^ 2 ≤ δ⁻¹ ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hnR.le (recurrence_invRisk_mem_Icc a s _).1)
          hscaled 2
      apply (le_div_iff₀ (sq_pos_of_pos hnR)).mpr
      nlinarith [hsq]
    · positivity
  unfold localizedDeathVariation
  simp only [one_pow, one_mul]
  calc
    _ ≤ (n : ℝ) * ∑ _i : Fin n, δ⁻¹ ^ 2 / (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) hnR.le
    _ = δ⁻¹ ^ 2 := by simp; field_simp

/-- On a localized positive-risk event, uniform remaining-mean error controls
the actual future-mark death studentizer by a deterministic multiple of that
error. This is the pathwise replacement in the consistency proof. -/
-- @node: localizedDeathVariation_plugin_error_le_of_riskFraction_lower
lemma localizedDeathVariation_plugin_error_le_of_riskFraction_lower
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {T ε δ : ℝ}
    (hT : T ≤ 1) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hExit : ∀ i, 0 ≤ (s i).exit)
    (he : ∀ u ∈ Icc (0 : ℝ) T,
      |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤ ε)
    (hr : ∀ i, (s i).treatment = a → (s i).deathInd → (s i).exit ≤ T →
      (n : ℝ) * δ ≤ riskSet a s (s i).exit) :
    |localizedDeathVariation a s T (remainingMeanHat c a s) -
      localizedDeathVariation a s T (remainingTarget c P a 0)| ≤
      2 * c.lambdaMax * ε * δ⁻¹ ^ 2 := by
  have hcompare := localizedDeathVariation_plugin_error_le c P hP a s hT hExit he
  have henergy := localizedDeathVariation_one_le a hn s hδ hr
  simp only [localizedDeathVariation, one_pow, one_mul] at henergy
  exact hcompare.trans (mul_le_mul_of_nonneg_left henergy
    (mul_nonneg (mul_nonneg (by norm_num) (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)) hε))

/-- Terminal death variation on the interval after a localization horizon.
The coefficient may depend on the full sample, including future marks. -/
-- @node: tailDeathVariation
noncomputable def tailDeathVariation (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (T U : ℝ) (H : ℝ → ℝ) : ℝ :=
  (n : ℝ) * ∑ i : Fin n,
    if (s i).treatment = a ∧ (s i).deathInd ∧ T < (s i).exit ∧ (s i).exit ≤ U then
      H (s i).exit ^ 2 * invRisk a s (s i).exit ^ 2 else 0

/-- Terminal optional variation is nonnegative for every coefficient. -/
-- @node: tailDeathVariation_nonneg
lemma tailDeathVariation_nonneg (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (T U : ℝ) (H : ℝ → ℝ) :
    0 ≤ tailDeathVariation a s T U H := by
  unfold tailDeathVariation
  positivity

/-- Localization and terminal variation partition the full finite death sum. -/
-- @node: localizedDeathVariation_split
lemma localizedDeathVariation_split (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {T U : ℝ} (hTU : T ≤ U) (H : ℝ → ℝ) :
    localizedDeathVariation a s U H =
      localizedDeathVariation a s T H + tailDeathVariation a s T U H := by
  classical
  unfold localizedDeathVariation tailDeathVariation
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · by_cases ht : (s i).exit ≤ T
      · simp [ha, hd, ht, ht.trans hTU, not_lt_of_ge ht]
      · simp [ha, hd, ht, lt_of_not_ge ht]
    · simp [ha, hd]
  · simp [ha]

/-- Two coefficients in the same nonnegative interval differ in squared
value by at most the square of that interval's upper endpoint. -/
-- @node: sq_sub_sq_abs_le_common_envelope
lemma sq_sub_sq_abs_le_common_envelope {x y B : ℝ}
    (hx : x ∈ Icc 0 B) (hy : y ∈ Icc 0 B) :
    |x ^ 2 - y ^ 2| ≤ B ^ 2 := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg x], by nlinarith [sq_nonneg y]⟩

/-- The terminal plug-in difference is dominated by a deterministic
remaining-horizon envelope. No predictability of future marks is used. -/
-- @node: tailDeathVariation_plugin_error_le_envelope
lemma tailDeathVariation_plugin_error_le_envelope (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (T : ℝ) (hExit : ∀ i, 0 ≤ (s i).exit) :
    |tailDeathVariation a s T 1 (remainingMeanHat c a s) -
      tailDeathVariation a s T 1 (remainingTarget c P a 0)| ≤
    tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)) := by
  classical
  unfold tailDeathVariation
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), ← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (Nat.cast_nonneg n)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (invRisk a s (s i).exit))]
    exact mul_le_mul_of_nonneg_right
      (sq_sub_sq_abs_le_common_envelope
        (remainingMeanHat_mem_Icc c a s hi.2.2.2)
        (remainingTarget_zero_mem_Icc c P hP a ⟨hExit i, hi.2.2.2⟩))
      (sq_nonneg _)
  · simp

/-- Full-horizon plug-in replacement reduces to localized replacement and
one deterministic terminal optional-variation envelope. -/
-- @node: fullDeathVariation_plugin_error_le_local_and_tail
lemma fullDeathVariation_plugin_error_le_local_and_tail (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {T : ℝ} (hT : T ≤ 1)
    (hExit : ∀ i, 0 ≤ (s i).exit) :
    |localizedDeathVariation a s 1 (remainingMeanHat c a s) -
      localizedDeathVariation a s 1 (remainingTarget c P a 0)| ≤
    |localizedDeathVariation a s T (remainingMeanHat c a s) -
      localizedDeathVariation a s T (remainingTarget c P a 0)| +
    tailDeathVariation a s T 1 (fun t => c.lambdaMax * (1 - t)) := by
  rw [localizedDeathVariation_split a s hT (remainingMeanHat c a s),
    localizedDeathVariation_split a s hT (remainingTarget c P a 0)]
  calc
    _ = |(localizedDeathVariation a s T (remainingMeanHat c a s) -
        localizedDeathVariation a s T (remainingTarget c P a 0)) +
        (tailDeathVariation a s T 1 (remainingMeanHat c a s) -
        tailDeathVariation a s T 1 (remainingTarget c P a 0))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add_right
      (tailDeathVariation_plugin_error_le_envelope c P hP a s T hExit) _)

/-- The paper's terminal death variation is the canonical terminal squared
inverse-risk mark sum on the observed pair sample. The positive tail threshold
eliminates the artificial time-zero risk of unassigned subjects. -/
-- @node: tailDeathVariation_eq_observedDeathSample_marks
lemma tailDeathVariation_eq_observedDeathSample_marks (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) {T U : ℝ} (hT : 0 ≤ T) (H : ℝ → ℝ) :
    tailDeathVariation a s T U H = (n : ℝ) * ∑ i : Fin n,
      if T < ((observedDeathSample a s) i).2 ∧
          ((observedDeathSample a s) i).2 ≤ U ∧
          ((observedDeathSample a s) i).2 < ((observedDeathSample a s) i).1 then
        H ((observedDeathSample a s) i).2 ^ 2 *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk
            ((observedDeathSample a s) i).2 (observedDeathSample a s) ^ 2
      else 0 := by
  classical
  unfold tailDeathVariation
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · by_cases ht : T < (s i).exit
      · have hi := observedDeathSample_inverseRisk a s (hT.trans_lt ht)
        simp only [observedDeathSample, observedDeathPair, if_pos ha, if_pos hd,
          Prod.fst, Prod.snd]
        simp [ha, hd, ht, hi, show (s i).exit < (s i).exit + 1 by linarith]
      · simp [observedDeathSample, observedDeathPair, ha, hd, ht]
    · simp [observedDeathSample, observedDeathPair, ha, hd,
        show ¬(s i).exit + 1 < (s i).exit by linarith]
  · simp [observedDeathSample, observedDeathPair, ha]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
