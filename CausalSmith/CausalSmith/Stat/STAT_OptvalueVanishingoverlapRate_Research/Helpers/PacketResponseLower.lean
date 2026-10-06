module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketIntegrationByParts

/-! # Separation attained by the completed Jackson packet

Evenness adds the two localized responses in roadmap (29). Fourier
annihilation removes the affine term, and normalization followed by
common-atom completion gives the explicit lower-prior witness in (30).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory

-- @node: packetOscillation_even
/-- The modulated Jackson kernel is even, so reflection preserves its response. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetOscillation_even (N : ℕ) (u : ℝ) :
    packetOscillation N (-u) = packetOscillation N u := by
  unfold packetOscillation packetKernel
  rw [Causalean.Mathlib.Analysis.JacksonApproximation.jackson_even N u]
  simp only [mul_neg, Real.cos_neg]

-- @node: packetRemainder_reflected_response
/-- The two kink centers give exactly equal responses, by reflection on the circle. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetRemainder_reflected_response (N : ℕ) (M ε θ : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) * packetOscillation N (t + θ) /
        (2 * Real.pi)) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) * packetOscillation N (t - θ) /
        (2 * Real.pi) := by
  let f := fun t => packetRemainder ε (packetIntensity M t) *
    packetOscillation N (t - θ) / (2 * Real.pi)
  have he (t : ℝ) : f (-t) = packetRemainder ε (packetIntensity M t) *
      packetOscillation N (t + θ) / (2 * Real.pi) := by
    dsimp [f]
    have ht : -t - θ = -(t + θ) := by ring
    rw [ht, packetOscillation_even]
    simp only [packetIntensity, Real.cos_neg]
  simp_rw [← he]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    intervalIntegral.integral_comp_neg]
  simp only [neg_neg]
  rfl

-- @node: packetWave_remainder_response
/-- The whole packet pairs with the nonlinear remainder as twice one response. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetWave_remainder_response (A K : ℕ) {M : ℝ} (hM : 0 ≤ M) (ε : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetWave A K M t * packetRemainder ε (packetIntensity M t) /
        (2 * Real.pi)) =
    2 * ∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) *
        packetOscillation (A * K) (t - Real.arccos (2 / M - 1)) /
          (2 * Real.pi) := by
  have hi (θ : ℝ) : IntegrableOn (fun t =>
      packetRemainder ε (packetIntensity M t) * packetOscillation (A * K) (t - θ) /
        (2 * Real.pi)) (Set.Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold packetRemainder packetIntensity packetOscillation packetKernel
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.add
        · fun_prop
        · apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro t ht
            have := (packetIntensity_mem_Icc hM t).1
            unfold packetIntensity at this
            linarith
      · fun_prop (disch := exact
          Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
    · fun_prop
    · intro t ht; exact ne_of_gt (by positivity)
  have he (t : ℝ) : packetWave A K M t * packetRemainder ε (packetIntensity M t) /
      (2 * Real.pi) =
      packetRemainder ε (packetIntensity M t) *
        packetOscillation (A * K) (t - Real.arccos (2 / M - 1)) / (2 * Real.pi) +
      packetRemainder ε (packetIntensity M t) *
        packetOscillation (A * K) (t + Real.arccos (2 / M - 1)) / (2 * Real.pi) := by
    unfold packetWave
    ring
  simp_rw [he]
  rw [integral_add (hi _) (by simpa only [IntegrableOn, sub_neg_eq_add] using hi (-Real.arccos (2 / M - 1))),
    packetRemainder_reflected_response]
  ring

/-- Fourier annihilation removes the affine part of phi, retaining the exact sum of the two nonlinear kink responses in roadmap (29). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM), the [stated conclusion](goal) holds. -/
lemma packetWave_phiEps_response {A K : ℕ} (hA : 1 ≤ A) (hK : 2 ≤ K)
    {M : ℝ} (hM : 0 ≤ M) (ε : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetWave A K M t * phiEpsFormula ε (packetIntensity M t) / (2 * Real.pi)) =
    2 * ∫ t in Set.Icc (-Real.pi) Real.pi,
      packetRemainder ε (packetIntensity M t) *
        packetOscillation (A * K) (t - Real.arccos (2 / M - 1)) /
          (2 * Real.pi) := by
  let p : Polynomial ℝ := Polynomial.C ε * (Polynomial.X - 1)
  have hp : p.natDegree ≤ K := by
    calc
      _ ≤ (Polynomial.C ε).natDegree + (Polynomial.X - 1 : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by
        simp only [Polynomial.natDegree_C, zero_add]
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ ≤ K := by omega
  have hz := packetWave_polynomial_annihilation hA hK M p hp
  have hpe (z : ℝ) : p.eval z = ε * (z - 1) := by simp [p]
  simp_rw [hpe] at hz
  have hsplit (t : ℝ) :
      packetWave A K M t * phiEpsFormula ε (packetIntensity M t) / (2 * Real.pi) =
      packetWave A K M t * (ε * (packetIntensity M t - 1)) / (2 * Real.pi) +
      packetWave A K M t * packetRemainder ε (packetIntensity M t) / (2 * Real.pi) := by
    rw [phiEps_eq_packetRemainder (packetIntensity_mem_Icc hM t).1]
    ring
  have hi1 : IntegrableOn (fun t => packetWave A K M t *
      (ε * (packetIntensity M t - 1)) / (2 * Real.pi)) (Set.Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold packetWave packetOscillation packetKernel
    fun_prop (disch := exact
      Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
  have hi2 : IntegrableOn (fun t => packetWave A K M t *
      packetRemainder ε (packetIntensity M t) / (2 * Real.pi))
      (Set.Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold packetRemainder
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · unfold packetWave packetOscillation packetKernel
        fun_prop (disch := exact
          Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
      · apply ContinuousOn.add
        · fun_prop
        · apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro t ht
            linarith [(packetIntensity_mem_Icc hM t).1]
    · fun_prop
    · intro t ht; exact ne_of_gt (by positivity)
  simp_rw [hsplit]
  rw [integral_add hi1 hi2, integral_div, hz, zero_div, zero_add,
    packetWave_remainder_response A K hM ε]

/-- The full unnormalized packet has a uniform response of order sqrt(M)/K, including zero overlap and the endpoint M = K². In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetWave_response_lower :
    ∃ (c : ℝ) (A : ℕ), 0 < c ∧ 1 ≤ A ∧
      ∀ (K : ℕ) (M ε : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        0 ≤ ε → ε ≤ 1 / 2 →
        c * Real.sqrt M / K ≤
          |∫ t in Set.Icc (-Real.pi) Real.pi,
            packetWave A K M t * phiEpsFormula ε (packetIntensity M t) / (2 * Real.pi)| := by
  obtain ⟨c, A, hc, hA, hresponse⟩ := packetRemainder_response_lower
  refine ⟨2 * c, A, by positivity, hA, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  rw [packetWave_phiEps_response hA hK (by linarith) ε, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul_of_nonneg_left (hresponse K M ε hK hM hMhi hε hεhi)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_div_assoc, mul_assoc] using h

/-- Normalization costs at most the universal weighted-variation bound 36. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetNormalized_response_lower :
    ∃ (c : ℝ) (A : ℕ), 0 < c ∧ 1 ≤ A ∧
      ∀ (K : ℕ) (M ε : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        0 ≤ ε → ε ≤ 1 / 2 →
        c * Real.sqrt M / K ≤
          |∫ t in Set.Icc (-Real.pi) Real.pi,
            (packetWave A K M t / packetWeight A K M / (2 * Real.pi)) *
              phiEpsFormula ε (packetIntensity M t)| := by
  obtain ⟨c, A, hc, hA, hresponse⟩ := packetWave_response_lower
  refine ⟨c / 36, A, by positivity, hA, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  have hW := packetWeight_pos hA hK hM
  have hWle := packetWeight_le hA hK hM hMhi
  have he (t : ℝ) :
      (packetWave A K M t / packetWeight A K M / (2 * Real.pi)) *
        phiEpsFormula ε (packetIntensity M t) =
      (packetWave A K M t * phiEpsFormula ε (packetIntensity M t) / (2 * Real.pi)) /
        packetWeight A K M := by ring
  simp_rw [he]
  rw [integral_div, abs_div, abs_of_pos hW]
  have hl := hresponse K M ε hK hM hMhi hε hεhi
  have hnum : 0 ≤ c * Real.sqrt M / K := by positivity
  calc
    c / 36 * Real.sqrt M / K = (c * Real.sqrt M / K) / 36 := by ring
    _ ≤ (c * Real.sqrt M / K) / packetWeight A K M :=
      div_le_div_of_nonneg_left hnum hW hWle
    _ ≤ _ := div_le_div_of_nonneg_right hl hW.le

/-- The explicit common-atom completion attains the uniform weighted lower separation, with support, mean one, and all K moments supplied by the constructed constrained-prior pair, as required by roadmap (30). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetCompletion_separation_lower :
    ∃ (c : ℝ) (A : ℕ), 0 < c ∧ 1 ≤ A ∧
      ∀ (K : ℕ) (M ε : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        0 ≤ ε → ε ≤ 1 / 2 →
        ∃ (p : ConstrainedPriorPair K M),
          ∃ hdom : CommonAtomDomain (packetPositive A K M) (packetNegative A K M),
          (packetPositive A K M Set.univ).toReal ≤ 1 / 2 ∧
          (1 / 2 : ℝ) ≤ (1 - ∫ z, z ∂packetPositive A K M) /
            (1 - (packetPositive A K M Set.univ).toReal) ∧
          (1 - ∫ z, z ∂packetPositive A K M) /
            (1 - (packetPositive A K M Set.univ).toReal) ≤ 2 ∧
          commonAtomCompletion (packetPositive A K M) (packetNegative A K M) hdom =
            (p.ν₀, p.ν₁) ∧
          c * Real.sqrt M / K ≤
            |(∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀)| := by
  obtain ⟨c, A, hc, hA, hresponse⟩ := packetNormalized_response_lower
  refine ⟨c, A, hc, hA, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  obtain ⟨p, hdom, ht, hzlo, hzhi, hcompletion, hgap⟩ :=
    packetCompletion_witness hA hK hM ε
  refine ⟨p, hdom, ht, hzlo, hzhi, hcompletion, ?_⟩
  rw [hgap]
  exact hresponse K M ε hK hM hMhi hε hεhi

-- @node: packetWeightedApproxError_lower
/-- The attained packet gap forces the claimed order of the weighted best approximation error: every admissible polynomial has the same moment pairing, so the proved residual envelope bounds the gap before taking the infimum. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetWeightedApproxError_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : ℕ) (M ε : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        0 ≤ ε → ε ≤ 1 / 2 →
        c * Real.sqrt M / K ≤ weightedApproxError K M ε := by
  obtain ⟨c, A, hc, hA, hprior⟩ := packetCompletion_separation_lower
  refine ⟨c / 4, by positivity, ?_⟩
  intro K M ε hK hM hMhi hε hεhi
  obtain ⟨p, _, _, _, _, _, hgap⟩ := hprior K M ε hK hM hMhi hε hεhi
  have hne : {e : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧
      e = sSup ((fun z : ℝ => |phiEpsFormula ε z - q.eval z| / (1 + z)) ''
        Set.Icc 0 M)}.Nonempty := by
    refine ⟨_, 0, ?_, rfl⟩
    simp
  apply le_csInf hne
  rintro e ⟨q, hq, rfl⟩
  have hbound := constrainedPriorPair_gap_le_polynomial_error p ε
    (by linarith) q hq
  have hscale : c / 4 * Real.sqrt M / K = (c * Real.sqrt M / K) / 4 := by ring
  rw [hscale]
  exact (div_le_div_of_nonneg_right hgap (by norm_num)).trans
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by linarith only [hbound]))

end CausalSmith.Stat.OptvalueVanishingoverlapRate
