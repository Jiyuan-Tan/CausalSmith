module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate

/-! Transfer of pointwise two-sample certificates to a ratio-filter lower bound. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ,c,C,R,hTrial,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCertificate_ratio_liminf_of_upperBound
    (ρ : ℝ) (hρ : 0 < ρ) (c C : ℝ) (R : ℕ → ℕ → ℝ)
    (hTrial : ∀ (n m : ℕ), 0 < n → 0 < m →
      c * (Real.sqrt (n : ℝ))⁻¹ ≤ R n m)
    (hUpper : ∀ (n m : ℕ), 0 < n → 0 < m →
      externalNormalizer n m * R n m ≤ C) :
    c / (1 + Real.sqrt ρ) ≤
      liminf (fun nm : ℕ × ℕ => externalNormalizer nm.1 nm.2 * R nm.1 nm.2)
        (ratioFilter ρ) := by
  letI : (ratioFilter ρ).NeBot := ratioFilter_neBot ρ hρ
  let u : ℕ × ℕ → ℝ := fun nm =>
    externalNormalizer nm.1 nm.2 * R nm.1 nm.2
  let v : ℕ × ℕ → ℝ := fun nm =>
    c * (Real.sqrt (nm.2 : ℝ) /
      (Real.sqrt (nm.1 : ℝ) + Real.sqrt (nm.2 : ℝ)))
  have hvlim : Tendsto v (ratioFilter ρ)
      (nhds (c / (1 + Real.sqrt ρ))) := by
    have hconst : Tendsto (fun _ : ℕ × ℕ => c) (ratioFilter ρ) (nhds c) :=
      tendsto_const_nhds
    have h := hconst.mul (normalizedCertificate_ratio_trial ρ hρ)
    simpa [v, div_eq_mul_inv] using h
  have hle : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, v nm ≤ u nm := by
    filter_upwards [ratioFilter_eventually_pos ρ] with nm hnm
    simpa [v, u, mul_div_assoc] using
      normalizedCertificate_trial nm.1 nm.2 hnm.1 hnm.2 c (R nm.1 nm.2)
        (hTrial nm.1 nm.2 hnm.1 hnm.2)
  have hub : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, u nm ≤ C := by
    filter_upwards [ratioFilter_eventually_pos ρ] with nm hnm
    exact hUpper nm.1 nm.2 hnm.1 hnm.2
  have hvu : (ratioFilter ρ).IsBoundedUnder (· ≥ ·) v := hvlim.isBoundedUnder_ge
  have huu : (ratioFilter ρ).IsCoboundedUnder (· ≥ ·) u :=
    (isBoundedUnder_of_eventually_le hub).isCoboundedUnder_ge
  calc
    c / (1 + Real.sqrt ρ) = liminf v (ratioFilter ρ) := hvlim.liminf_eq.symm
    _ ≤ liminf u (ratioFilter ρ) := liminf_le_liminf hle hvu huu
    _ = liminf (fun nm : ℕ × ℕ =>
        externalNormalizer nm.1 nm.2 * R nm.1 nm.2) (ratioFilter ρ) := rfl

-- @node: logCertificate_ratio_liminf_of_upperBound
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ,c,C,R,hLog,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma logCertificate_ratio_liminf_of_upperBound
    (ρ : ℝ) (hρ : 0 < ρ) (c C : ℝ) (R : ℕ → ℕ → ℝ)
    (hLog : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      c * (Real.sqrt (m : ℝ))⁻¹ ≤ R n m)
    (hUpper : ∀ (n m : ℕ), 0 < n → 0 < m →
      externalNormalizer n m * R n m ≤ C) :
    c * Real.sqrt ρ / (1 + Real.sqrt ρ) ≤
      liminf (fun nm : ℕ × ℕ => externalNormalizer nm.1 nm.2 * R nm.1 nm.2)
        (ratioFilter ρ) := by
  letI : (ratioFilter ρ).NeBot := ratioFilter_neBot ρ hρ
  let u : ℕ × ℕ → ℝ := fun nm =>
    externalNormalizer nm.1 nm.2 * R nm.1 nm.2
  let v : ℕ × ℕ → ℝ := fun nm =>
    c * (Real.sqrt (nm.1 : ℝ) /
      (Real.sqrt (nm.1 : ℝ) + Real.sqrt (nm.2 : ℝ)))
  have hvlim : Tendsto v (ratioFilter ρ)
      (nhds (c * Real.sqrt ρ / (1 + Real.sqrt ρ))) := by
    have hconst : Tendsto (fun _ : ℕ × ℕ => c) (ratioFilter ρ) (nhds c) :=
      tendsto_const_nhds
    simpa only [v, mul_div_assoc] using
      hconst.mul (normalizedCertificate_ratio_log ρ hρ)
  have hlog' : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ,
      ∀ n : ℕ, 0 < n → c * (Real.sqrt (nm.2 : ℝ))⁻¹ ≤ R n nm.2 := by
    apply Filter.Eventually.filter_mono (by unfold ratioFilter; exact inf_le_left)
    have hfirst : ∀ᶠ _ : ℕ in atTop, True :=
      Filter.Eventually.of_forall (fun _ => True.intro)
    exact (hfirst.prod_mk hLog).mono (fun _ h => h.2)
  have hle : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, v nm ≤ u nm := by
    filter_upwards [ratioFilter_eventually_pos ρ, hlog'] with nm hnm hlognm
    simpa [v, u, mul_div_assoc] using
      normalizedCertificate_log nm.1 nm.2 hnm.1 hnm.2 c (R nm.1 nm.2)
        (hlognm nm.1 hnm.1)
  have hub : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, u nm ≤ C := by
    filter_upwards [ratioFilter_eventually_pos ρ] with nm hnm
    exact hUpper nm.1 nm.2 hnm.1 hnm.2
  have hvu : (ratioFilter ρ).IsBoundedUnder (· ≥ ·) v := hvlim.isBoundedUnder_ge
  have huu : (ratioFilter ρ).IsCoboundedUnder (· ≥ ·) u :=
    (isBoundedUnder_of_eventually_le hub).isCoboundedUnder_ge
  calc
    c * Real.sqrt ρ / (1 + Real.sqrt ρ) = liminf v (ratioFilter ρ) := hvlim.liminf_eq.symm
    _ ≤ liminf u (ratioFilter ρ) := liminf_le_liminf hle hvu huu
    _ = liminf (fun nm : ℕ × ℕ =>
        externalNormalizer nm.1 nm.2 * R nm.1 nm.2) (ratioFilter ρ) := rfl

-- @node: logCertificate_ratio_liminf_of_infimum
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ,c,C,R,hNonneg,hLog,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma logCertificate_ratio_liminf_of_infimum
    (ρ : ℝ) (hρ : 0 < ρ) (c C : ℝ) (R : ℕ → ℕ → ℝ)
    (hNonneg : ∀ n m : ℕ, 0 < n → 0 < m → 0 ≤ R n m)
    (hLog : c ≤ liminf (fun m : ℕ =>
      sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧ v = Real.sqrt (m : ℝ) * R n m}) atTop)
    (hUpper : ∀ n m : ℕ, 0 < n → 0 < m →
      externalNormalizer n m * R n m ≤ C) :
    c * Real.sqrt ρ / (1 + Real.sqrt ρ) ≤
      liminf (fun nm : ℕ × ℕ => externalNormalizer nm.1 nm.2 * R nm.1 nm.2)
        (ratioFilter ρ) := by
  let F : ℕ → ℝ := fun m =>
    sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧ v = Real.sqrt (m : ℝ) * R n m}
  have hFnonneg : ∀ᶠ m : ℕ in atTop, 0 ≤ F m := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    apply le_csInf
    · exact ⟨Real.sqrt (m : ℝ) * R 1 m, 1, by omega, rfl⟩
    · rintro v ⟨n, hn, rfl⟩
      exact mul_nonneg (Real.sqrt_nonneg _) (hNonneg n m hn hm)
  have hFbelow : atTop.IsBoundedUnder (· ≥ ·) F :=
    isBoundedUnder_of_eventually_ge hFnonneg
  have hweight : 0 < Real.sqrt ρ / (1 + Real.sqrt ρ) := by positivity
  apply le_of_forall_lt
  intro x hx
  have hxdiv : x / (Real.sqrt ρ / (1 + Real.sqrt ρ)) < c :=
    (div_lt_iff₀ hweight).mpr (by simpa only [mul_div_assoc] using hx)
  let β : ℝ := (x / (Real.sqrt ρ / (1 + Real.sqrt ρ)) + c) / 2
  have hβ : β < c := by dsimp [β]; linarith
  have hxβ : x < β * Real.sqrt ρ / (1 + Real.sqrt ρ) := by
    have h : x / (Real.sqrt ρ / (1 + Real.sqrt ρ)) < β := by
      dsimp [β]
      linarith
    simpa only [mul_div_assoc] using (div_lt_iff₀ hweight).mp h
  have hFevent : ∀ᶠ m : ℕ in atTop, β < F m :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hβ hLog) hFbelow
  have hEvent : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      β * (Real.sqrt (m : ℝ))⁻¹ ≤ R n m := by
    filter_upwards [hFevent, eventually_gt_atTop (0 : ℕ)] with m hβF hm
    intro n hn
    have hSbd : BddBelow {v : ℝ | ∃ n' : ℕ, 0 < n' ∧
        v = Real.sqrt (m : ℝ) * R n' m} := by
      refine ⟨0, ?_⟩
      rintro v ⟨n', hn', rfl⟩
      exact mul_nonneg (Real.sqrt_nonneg _) (hNonneg n' m hn' hm)
    have hFle : F m ≤ Real.sqrt (m : ℝ) * R n m :=
      csInf_le hSbd ⟨n, hn, rfl⟩
    have hsm : 0 < Real.sqrt (m : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
    have hprod : β ≤ R n m * Real.sqrt (m : ℝ) := by
      simpa only [mul_comm] using (le_trans hβF.le hFle)
    simpa only [div_eq_mul_inv] using (div_le_iff₀ hsm).mpr hprod
  have hTransfer := logCertificate_ratio_liminf_of_upperBound ρ hρ β C R
    hEvent hUpper
  exact lt_of_lt_of_le hxβ hTransfer

end
end CausalSmith.PartialID.UnlinkedPropensityAte
