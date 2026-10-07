module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificateTransfer

/-! Transfer of eventual uniform log certificates through an infimum and liminf. -/

public section

open Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:beta,C,R,hLower,hUpperWitness), this result [establishes the stated mathematical conclusion](goal). -/
lemma logCertificate_liminf_infimum_of_eventual_uniform
    (beta C : ℝ) (R : ℕ → ℕ → ℝ)
    (hLower : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      beta * (Real.sqrt (m : ℝ))⁻¹ ≤ R n m)
    (hUpperWitness : ∀ᶠ m : ℕ in atTop, ∃ n : ℕ, 0 < n ∧
      Real.sqrt (m : ℝ) * R n m ≤ C) :
    beta ≤ liminf (fun m : ℕ =>
      sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * R n m}) atTop := by
  let F : ℕ → ℝ := fun m =>
    sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
      v = Real.sqrt (m : ℝ) * R n m}
  have hFLower : ∀ᶠ m : ℕ in atTop, beta ≤ F m := by
    filter_upwards [hLower, eventually_gt_atTop (0 : ℕ)] with m hlower hm
    have hsqrt : 0 < Real.sqrt (m : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
    apply le_csInf
    · exact ⟨Real.sqrt (m : ℝ) * R 1 m, 1, by omega, rfl⟩
    · rintro v ⟨n, hn, rfl⟩
      have h := mul_le_mul_of_nonneg_left (hlower n hn) hsqrt.le
      field_simp at h
      simpa [mul_comm] using h
  have hFUpper : ∀ᶠ m : ℕ in atTop, F m ≤ C := by
    filter_upwards [hLower, hUpperWitness, eventually_gt_atTop (0 : ℕ)] with
      m hlower ⟨n, hn, hupper⟩ hm
    have hsqrt : 0 < Real.sqrt (m : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
    have hsetBelow : BddBelow {v : ℝ | ∃ n' : ℕ, 0 < n' ∧
        v = Real.sqrt (m : ℝ) * R n' m} := by
      refine ⟨beta, ?_⟩
      rintro v ⟨n', hn', rfl⟩
      have h := mul_le_mul_of_nonneg_left (hlower n' hn') hsqrt.le
      field_simp at h
      simpa [mul_comm] using h
    exact (csInf_le hsetBelow ⟨n, hn, rfl⟩).trans hupper
  have hCobounded : atTop.IsCoboundedUnder (· ≥ ·) F :=
    (isBoundedUnder_of_eventually_le hFUpper).isCoboundedUnder_ge
  exact le_liminf_of_le hCobounded hFLower

/-- Given [the stated mathematical inputs and assumptions](hyp:m,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalNormalizer_self (m : ℕ) (hm : 0 < m) :
    externalNormalizer m m = Real.sqrt (m : ℝ) / 2 := by
  have hsqrt : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  unfold externalNormalizer
  field_simp
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:beta,C,R,hLower,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma logCertificate_liminf_infimum_of_normalized_upper
    (beta C : ℝ) (R : ℕ → ℕ → ℝ)
    (hLower : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      beta * (Real.sqrt (m : ℝ))⁻¹ ≤ R n m)
    (hUpper : ∀ (n m : ℕ), 0 < n → 0 < m →
      externalNormalizer n m * R n m ≤ C) :
    beta ≤ liminf (fun m : ℕ =>
      sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * R n m}) atTop := by
  apply logCertificate_liminf_infimum_of_eventual_uniform beta (2 * C) R hLower
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  refine ⟨m, hm, ?_⟩
  have h := mul_le_mul_of_nonneg_left (hUpper m m hm hm) (by norm_num : (0 : ℝ) ≤ 2)
  rw [externalNormalizer_self m hm] at h
  nlinarith

end
end CausalSmith.PartialID.UnlinkedPropensityAte
