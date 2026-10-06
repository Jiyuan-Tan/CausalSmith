module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalPriors
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance

/-! Variance and Chebyshev concentration of the latent rare-cell target in
 equations (8) and (12) of the connected-interval lower bound. The connection
 of this target to the activated full-law ATE is supplied separately. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_reciprocal_ae_unit
lemma finiteReciprocalPrior_reciprocal_ae_unit {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) : ∀ᵐ z ∂π, z⁻¹ ∈ Icc (0 : ℝ) 1 := by
  letI := hπ.1
  obtain ⟨s, hs, hsupport⟩ := hπ.2
  have hae : ∀ᵐ z ∂π, z ∈ (s : Set ℝ) :=
    (ae_mem_iff_measure_eq s.measurableSet.nullMeasurableSet).2 (by simpa using hs)
  filter_upwards [hae] with z hz
  have hlow := (hsupport z hz).1
  exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hlow⟩

/-- For [the specified inputs and assumptions](hyp:J,b,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: intervalPriorTarget
noncomputable def intervalPriorTarget (J : ℕ) (b : ℝ) (z : Fin J → ℝ) : ℝ :=
  b * ∑ i, (z i)⁻¹

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J,b), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPriorTarget_integral
lemma intervalPriorTarget_integral {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J : ℕ) (b : ℝ) :
    (∫ z, intervalPriorTarget J b z ∂Measure.pi (fun _ : Fin J => π)) =
      (J : ℝ) * b * ∫ z, z⁻¹ ∂π := by
  letI := hπ.1
  have hf : Integrable (fun z : ℝ => z⁻¹) π := finiteReciprocalPrior_integrable hπ _
  unfold intervalPriorTarget
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin J => π) hf.aestronglyMeasurable]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  · intro i hi
    exact integrable_comp_eval (μ := fun _ : Fin J => π) (i := i) hf

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J,b), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPriorTarget_variance_le
lemma intervalPriorTarget_variance_le {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J : ℕ) (b : ℝ) :
    variance (intervalPriorTarget J b) (Measure.pi (fun _ : Fin J => π)) ≤
      (J : ℝ) * b ^ 2 / 4 := by
  letI := hπ.1
  have hbound := finiteReciprocalPrior_reciprocal_ae_unit hπ
  have hf : MemLp (fun z : ℝ => z⁻¹) 2 π :=
    memLp_of_bounded hbound (by fun_prop) 2
  have hvar : variance (fun z : ℝ => z⁻¹) π ≤ 1 / 4 := by
    have h := variance_le_sq_of_bounded hbound (show AEMeasurable (fun z : ℝ => z⁻¹) π by fun_prop)
    norm_num at h ⊢
    exact h
  unfold intervalPriorTarget
  rw [variance_const_mul]
  have heq : (fun z : Fin J → ℝ => ∑ i, (z i)⁻¹) =
      ∑ i : Fin J, fun z : Fin J → ℝ => (z i)⁻¹ := by
    funext z
    simp only [Finset.sum_apply]
  rw [heq, variance_sum_pi (fun _ => hf)]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hvar (show 0 ≤ (J : ℝ) * b ^ 2 by positivity)]

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J,b,w,hw), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPriorTarget_chebyshev
lemma intervalPriorTarget_chebyshev {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J : ℕ) (b w : ℝ) (hw : 0 < w) :
    (Measure.pi (fun _ : Fin J => π)).real
      {z | w < |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} ≤
        ((J : ℝ) * b ^ 2 / 4) / w ^ 2 := by
  letI := hπ.1
  have hf : MemLp (fun z : ℝ => z⁻¹) 2 π :=
    memLp_of_bounded (finiteReciprocalPrior_reciprocal_ae_unit hπ) (by fun_prop) 2
  have hsum : MemLp (intervalPriorTarget J b) 2 (Measure.pi (fun _ : Fin J => π)) := by
    have heq : intervalPriorTarget J b =
        fun z : Fin J → ℝ => b * (∑ i : Fin J, fun z : Fin J → ℝ => (z i)⁻¹) z := by
      funext z
      simp [intervalPriorTarget, Finset.sum_apply]
    rw [heq]
    exact (memLp_finsetSum' Finset.univ fun i hi =>
      hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin J => π) i)).const_mul b
  have htail := meas_ge_le_variance_div_sq hsum hw
  rw [intervalPriorTarget_integral hπ J b] at htail
  have hmono : (Measure.pi (fun _ : Fin J => π))
      {z | w < |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} ≤
        ENNReal.ofReal (((J : ℝ) * b ^ 2 / 4) / w ^ 2) := by
    have hsubset :
        {z : Fin J → ℝ | w < |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} ⊆
        {z | w ≤ |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} :=
      by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        exact le_of_lt hz
    refine (measure_mono hsubset).trans (htail.trans ?_)
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (intervalPriorTarget_variance_le hπ J b) (sq_nonneg w))
  have hreal := ENNReal.toReal_mono (by simp) hmono
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity :
    0 ≤ ((J : ℝ) * b ^ 2 / 4) / w ^ 2)] using hreal

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J,M,b,Δ,u,hb,hΔ,hu,hM,hgap,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalPriorTarget_concentration_budget
lemma intervalPriorTarget_concentration_budget {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J M : ℕ) (b Δ u : ℝ)
    (hb : 0 < b) (hΔ : 0 < Δ) (hu : 0 < u) (hM : 1 ≤ M)
    (hgap : (J : ℝ) * b / 12 ≤ Δ)
    (hJ : 18432 * (M : ℝ) ^ 2 / u ≤ (J : ℝ)) :
    (Measure.pi (fun _ : Fin J => π)).real
      {z | Δ / (8 * M) <
        |intervalPriorTarget J b z - (J : ℝ) * b * ∫ z, z⁻¹ ∂π|} ≤ u / 8 := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hJr : 0 < (J : ℝ) := lt_of_lt_of_le (by positivity) hJ
  have hJu : 18432 * (M : ℝ) ^ 2 ≤ (J : ℝ) * u := (div_le_iff₀ hu).mp hJ
  apply (intervalPriorTarget_chebyshev hπ J b (Δ / (8 * M)) (by positivity)).trans
  apply (div_le_iff₀ (by positivity : 0 < (Δ / (8 * M)) ^ 2)).mpr
  have hsq : ((J : ℝ) * b) ^ 2 ≤ 144 * Δ ^ 2 := by
    have hlinear : (J : ℝ) * b ≤ 12 * Δ := by linarith
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ (J : ℝ) * b) hlinear
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq hu.le
  have hcount := mul_le_mul_of_nonneg_right hJu (sq_nonneg b)
  field_simp
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,J,M,b,u,hb,hu,hM,hgap,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: intervalInterpolatedPrior_grid_concentration
lemma intervalInterpolatedPrior_grid_concentration {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (J M : ℕ) (b u : ℝ) (hb : 0 < b) (hu : 0 < u) (hM : 1 ≤ M)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|)
    (hJ : 18432 * (M : ℝ) ^ 2 / u ≤ (J : ℝ)) :
    ∀ j : Fin (M + 1),
      (Measure.pi (fun _ : Fin J =>
        intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).real
        {z | ((J : ℝ) * b * |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) / (8 * M) <
          |intervalPriorTarget J b z -
            ((J : ℝ) * b * (∫ z, z⁻¹ ∂π₀) +
              (j : ℝ) * ((J : ℝ) * b *
                ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M))|} ≤ u / 8 := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hJr : 0 < (J : ℝ) := lt_of_lt_of_le (by positivity) hJ
  have hdiff : 0 < |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀| :=
    lt_of_lt_of_le (by norm_num) hgap
  intro j
  have ht : (j : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hMr).mpr ?_⟩
    exact_mod_cast (by omega : j.val ≤ M)
  have hprior := finiteReciprocalPrior_interpolate h₀ h₁ ht
  have hsegment : (J : ℝ) * b / 12 ≤
      (J : ℝ) * b * |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀| := by
    nlinarith [mul_le_mul_of_nonneg_left hgap (show 0 ≤ (J : ℝ) * b by positivity)]
  have htail := intervalPriorTarget_concentration_budget hprior J M b
    ((J : ℝ) * b * |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) u hb
    (by positivity) hu hM hsegment hJ
  have hmean : (J : ℝ) * b *
      (∫ z, z⁻¹ ∂intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M)) =
      (J : ℝ) * b * (∫ z, z⁻¹ ∂π₀) +
        (j : ℝ) * ((J : ℝ) * b *
          ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M) := by
    rw [intervalInterpolatedPrior_integral h₀ h₁ ht]
    ring
  simpa only [hmean] using htail

end CausalSmith.Stat.MarRareqLogfrontier
