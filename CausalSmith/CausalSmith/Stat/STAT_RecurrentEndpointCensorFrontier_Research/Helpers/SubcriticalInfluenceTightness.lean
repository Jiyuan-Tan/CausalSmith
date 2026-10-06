module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalInfluenceAssembly

/-!
# Finite-sample bounds for the actual arm influence average

Roadmap (23), (27), and (30): exact oracle moments give a vanishing empirical
influence average and tight root-n sums. These bounds use the actual observed
influence, including its unbounded endpoint weights, and require no extra
moment hypothesis.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The iid arm sum has exactly n times the one-subject second moment. -/
-- @node: subcriticalInfluence_sum_secondMoment_eq_n_mul
lemma subcriticalInfluence_sum_secondMoment_eq_n_mul
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun s : Fin n → ObsHistory =>
      (∑ i, subcriticalInfluence c P a (s i)) ^ 2) (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory,
      (∑ i, subcriticalInfluence c P a (s i)) ^ 2 ∂sampleLaw P n) =
      (n : ℝ) * ∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P := by
  have hs := subcriticalInfluence_sum_moments c P hP hk a hn
  have ho := subcriticalInfluence_arm_moments c P hP hk a
  refine ⟨hs.2.2.1, ?_⟩
  rw [hs.2.2.2, ho.2.2.2]
  ring

/-- Averaging divides the exact arm second moment by the sample size. -/
-- @node: subcriticalInfluence_average_secondMoment
lemma subcriticalInfluence_average_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun s : Fin n → ObsHistory =>
      ((∑ i, subcriticalInfluence c P a (s i)) / n) ^ 2) (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory,
      ((∑ i, subcriticalInfluence c P a (s i)) / n) ^ 2 ∂sampleLaw P n) =
      (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P) / n := by
  have hs := subcriticalInfluence_sum_secondMoment_eq_n_mul c P hP hk a hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hi := hs.1.div_const ((n : ℝ) ^ 2)
  simp_rw [div_pow] at ⊢
  refine ⟨hi, ?_⟩
  rw [integral_div, hs.2]
  field_simp

/-- Markov applied to the actual square gives a quantitative influence LLN. -/
-- @node: subcriticalInfluence_average_probability_le
lemma subcriticalInfluence_average_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    (sampleLaw P n).real {s : Fin n → ObsHistory |
      ε < |(∑ i, subcriticalInfluence c P a (s i)) / n|} ≤
      (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P) /
        ((n : ℝ) * ε ^ 2) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hs := subcriticalInfluence_average_secondMoment c P hP hk a hn
  let Z := fun s : Fin n → ObsHistory => (∑ i, subcriticalInfluence c P a (s i)) / n
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (Z s))) hs.1 (ε ^ 2)
  have hsub : {s | ε < |Z s|} ⊆ {s | ε ^ 2 ≤ Z s ^ 2} := by
    intro s hs
    change ε < |Z s| at hs
    change ε ^ 2 ≤ Z s ^ 2
    have hsq := sq_abs (Z s)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.le)
      (add_nonneg (abs_nonneg (Z s)) hε.le)]
  have hb := (mul_le_mul_of_nonneg_left
    (measureReal_mono hsub (by finiteness)) (sq_nonneg ε)).trans hm
  rw [hs.2] at hb
  rw [div_mul_eq_div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  simpa only [Z, mul_comm] using hb

/-- The empirical arm influence average vanishes in probability. -/
-- @node: subcriticalInfluence_average_probability_tendsto_zero
lemma subcriticalInfluence_average_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real
      {s | ε < |(∑ i : Fin n, subcriticalInfluence c P a (s i)) / n|})
      atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P) /
        ((n : ℝ) * ε ^ 2)) atTop (nhds 0) := by
    simp only [div_mul_eq_div_div]
    simpa only [mul_zero, zero_div, div_eq_mul_inv, zero_mul, Pi.inv_apply] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul
        (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P)).div_const (ε ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact subcriticalInfluence_average_probability_le c P hP hk a (by omega) hε

/-- Root-n normalization retains the exact one-subject second moment. -/
-- @node: subcriticalInfluence_normalizedSum_secondMoment
lemma subcriticalInfluence_normalizedSum_secondMoment
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n) :
    Integrable (fun s : Fin n → ObsHistory =>
      ((∑ i, subcriticalInfluence c P a (s i)) / Real.sqrt n) ^ 2)
      (sampleLaw P n) ∧
    (∫ s : Fin n → ObsHistory,
      ((∑ i, subcriticalInfluence c P a (s i)) / Real.sqrt n) ^ 2 ∂sampleLaw P n) =
      ∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P := by
  have hs := subcriticalInfluence_sum_secondMoment_eq_n_mul c P hP hk a hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  simp_rw [div_pow, he]
  refine ⟨hs.1.div_const _, ?_⟩
  rw [integral_div, hs.2]
  exact mul_div_cancel_left₀ _ hn0

/-- The root-n arm influence sum has a sample-size-uniform tail bound. -/
-- @node: subcriticalInfluence_normalizedSum_probability_le
lemma subcriticalInfluence_normalizedSum_probability_le
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {n : ℕ} (hn : 0 < n)
    {K : ℝ} (hK : 0 < K) :
    (sampleLaw P n).real {s : Fin n → ObsHistory |
      K < |(∑ i, subcriticalInfluence c P a (s i)) / Real.sqrt n|} ≤
      (∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P) / K ^ 2 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hs := subcriticalInfluence_normalizedSum_secondMoment c P hP hk a hn
  let Z := fun s : Fin n → ObsHistory =>
    (∑ i, subcriticalInfluence c P a (s i)) / Real.sqrt n
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => sq_nonneg (Z s))) hs.1 (K ^ 2)
  have hsub : {s | K < |Z s|} ⊆ {s | K ^ 2 ≤ Z s ^ 2} := by
    intro s hs
    change K < |Z s| at hs
    change K ^ 2 ≤ Z s ^ 2
    have hsq := sq_abs (Z s)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.le)
      (add_nonneg (abs_nonneg (Z s)) hK.le)]
  have hb := (mul_le_mul_of_nonneg_left
    (measureReal_mono hsub (by finiteness)) (sq_nonneg K)).trans hm
  rw [hs.2] at hb
  apply (le_div_iff₀ (sq_pos_of_pos hK)).2
  simpa only [Z, mul_comm] using hb

/-- The actual arm influence sums are uniformly tight at root-n scale. -/
-- @node: subcriticalInfluence_normalizedSum_uniform_tight
lemma subcriticalInfluence_normalizedSum_uniform_tight
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      (sampleLaw P n).real {s |
        K < |(∑ i : Fin n, subcriticalInfluence c P a (s i)) / Real.sqrt n|} < ε := by
  let v := ∫ o, subcriticalInfluence c P a o ^ 2 ∂observedLaw P
  have hv : 0 ≤ v := integral_nonneg (fun _ => sq_nonneg _)
  let K := Real.sqrt (v / ε) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hsq : v / ε < K ^ 2 := by
    have he := Real.sq_sqrt (div_nonneg hv hε.le)
    have hp := Real.sqrt_nonneg (v / ε)
    dsimp [K]
    nlinarith
  have hb : v / K ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hK)).2
    have h := (div_lt_iff₀ hε).1 hsq
    nlinarith
  refine ⟨K, hK, fun n hn => ?_⟩
  exact (subcriticalInfluence_normalizedSum_probability_le c P hP hk a hn hK).trans_lt hb

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
