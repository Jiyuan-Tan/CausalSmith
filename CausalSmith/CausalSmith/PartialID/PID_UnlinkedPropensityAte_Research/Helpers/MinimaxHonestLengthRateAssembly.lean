module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate

/-! Algebraic assembly of the finite-label and sampling lower rates. -/

@[expose] public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,mf,L,n,K,hOverlap,hα,hmf,hn,hK,hLabel,hSampling), this result [establishes the stated mathematical conclusion](goal). -/
lemma minimaxHonestLength_rate_assembly {ε α mf L : ℝ} {n K : ℕ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (hmf : 0 < mf) (hn : 0 < n) (hK : 0 < K)
    (hLabel :
      ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε))) *
          (K : ℝ)⁻¹ ≤ L)
    (hSampling :
      trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤ L) :
    let A := (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε))
    let B := trialCertificate α
    let c := min A B / 2
    0 < c ∧
      c * ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) ≤ L := by
  dsimp
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  have hgap : 0 < 1 - 2 * ε := by linarith [hOverlap.2]
  have hden : 0 < 1 - ε := by linarith [hOverlap.2]
  have hA :
      0 < (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)) := by
    positivity
  have hlog : 0 < Real.log (1 + (1 - 2 * α) ^ 2) := by
    exact Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hB : 0 < trialCertificate α := by
    unfold trialCertificate
    positivity
  have hc : 0 < min
      ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
      (trialCertificate α) / 2 := div_pos (lt_min hA hB) (by norm_num)
  refine ⟨hc, ?_⟩
  have hKinv : 0 ≤ (K : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_pos.mpr hK).le
  have hninv : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)).le
  have hLabelHalf :
      (min
          ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
          (trialCertificate α) / 2) * (K : ℝ)⁻¹ ≤ L / 2 := by
    calc
      _ ≤ (((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 /
          (2 * (1 - ε))) / 2) * (K : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) hKinv
      _ = ((((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 /
          (2 * (1 - ε))) * (K : ℝ)⁻¹) / 2) := by ring
      _ ≤ L / 2 := by linarith
  have hSamplingHalf :
      (min
          ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
          (trialCertificate α) / 2) * (Real.sqrt (n : ℝ))⁻¹ ≤ L / 2 := by
    calc
      _ ≤ (trialCertificate α / 2) * (Real.sqrt (n : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) hninv
      _ = (trialCertificate α * (Real.sqrt (n : ℝ))⁻¹) / 2 := by ring
      _ ≤ L / 2 := by linarith
  calc
    (min
        ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
        (trialCertificate α) / 2) *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) =
      (min
          ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
          (trialCertificate α) / 2) * (K : ℝ)⁻¹ +
        (min
          ((1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε)))
          (trialCertificate α) / 2) * (Real.sqrt (n : ℝ))⁻¹ := by ring
    _ ≤ L / 2 + L / 2 := add_le_add hLabelHalf hSamplingHalf
    _ = L := by ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
