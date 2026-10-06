module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TAllLabelAmbiguity
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TUniversalPointIdentification
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelFiniteGeometry
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelRateLower

/-! Uniform inverse-label bounds under a density floor, and an upper bound for every score law. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma worstCaseAmbiguity_nonneg {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hOverlap : Overlap ε)
    (hg : Measurable g) : 0 ≤ worstCaseAmbiguity H g := by
  rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
  apply Finset.sum_nonneg
  intro r _
  exact add_nonneg
    (cellAbsoluteDeviation_nonneg H g hOverlap true r)
    (cellAbsoluteDeviation_nonneg H g hOverlap false r)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,hOverlap,hK,H), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidthRelease_worstCaseAmbiguity_le_all {ε : ℝ} {K : ℕ}
    (hOverlap : Overlap ε) (hK : 0 < K)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H] :
    worstCaseAmbiguity H (equalWidthRelease ε K hK) ≤
      (1 - 2 * ε) / (2 * ε * (1 - ε) * K) := by
  let g := equalWidthRelease ε K hK
  let B : ℝ := (1 - 2 * ε) / (2 * K)
  let C : ℝ := (ε * (1 - ε))⁻¹
  have hg : Measurable g := equalWidthRelease_measurable ε K hK
  have hB : 0 ≤ B := by
    dsimp [B]
    apply div_nonneg
    · linarith [hOverlap.2]
    · positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact inv_nonneg.mpr (mul_nonneg hOverlap.1.le (by linarith [hOverlap.2]))
  have hcell (r : LabelSpace K) :
      cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r ≤
        C * B * H.real (cell g r) := by
    let z := equalWidthBinMidpoint ε K hK hOverlap r
    have hdist (e : ScoreSpace ε) (he : e ∈ cell g r) :
        |(e : ℝ) - (z : ℝ)| ≤ B := by
      have hb := equalWidthRelease_cell_subset_closedBin hOverlap hK r he
      rcases hb with ⟨hl, hu⟩
      have hz : (z : ℝ) = ε + ((r : ℕ) + (1 / 2 : ℝ)) *
          ((1 - 2 * ε) / K) :=
        equalWidthBinMidpoint_val ε K hK hOverlap r
      rw [hz]
      dsimp [B] at ⊢
      rw [abs_le]
      constructor <;> ring_nf at hl hu ⊢ <;> linarith
    have hint : IntegrableOn (fun e : ScoreSpace ε => |(e : ℝ) - (z : ℝ)|)
        (cell g r) H := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with e
      have he := e.property
      have hz := z.property
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_le.mpr
        ⟨by linarith [he.1, he.2, hz.1, hz.2, hOverlap.1],
          by linarith [he.1, he.2, hz.1, hz.2, hOverlap.1]⟩
    have hbound :
        (∫ e in cell g r, |(e : ℝ) - (z : ℝ)| ∂H) ≤
          B * H.real (cell g r) := by
      calc
        (∫ e in cell g r, |(e : ℝ) - (z : ℝ)| ∂H) ≤
            ∫ _e in cell g r, B ∂H := by
          apply setIntegral_mono_on hint (integrable_const B)
            (measurableSet_eq_fun hg measurable_const)
          exact hdist
        _ = B * H.real (cell g r) := by simp [mul_comm]
    calc
      cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r ≤
          C * ∫ e in cell g r, |(e : ℝ) - (z : ℝ)| ∂H :=
        sum_cellAbsoluteDeviation_le_centeredScoreIntegral H g hg hOverlap r z
      _ ≤ C * (B * H.real (cell g r)) :=
        mul_le_mul_of_nonneg_left hbound hC
      _ = C * B * H.real (cell g r) := by ring
  rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
  calc
    (∑ r : LabelSpace K,
        (cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r)) ≤
        ∑ r : LabelSpace K, C * B * H.real (cell g r) := by
      apply Finset.sum_le_sum
      intro r _
      exact hcell r
    _ = C * B * ∑ r : LabelSpace K, H.real (cell g r) := by
      rw [← Finset.mul_sum]
    _ = C * B := by
      have h := MeasureTheory.sum_measureReal_preimage_singleton (μ := H)
        (s := Finset.univ) (f := g)
        (by intro r hr; exact measurableSet_eq_fun hg measurable_const)
      have htotal : (∑ r : LabelSpace K, H.real (cell g r)) = 1 := by
        simpa [cell, Set.preimage, Set.mem_singleton_iff] using h
      rw [htotal, mul_one]
    _ = (1 - 2 * ε) / (2 * ε * (1 - ε) * K) := by
      dsimp [B, C]
      have hε : ε ≠ 0 := hOverlap.1.ne'
      have hε1 : 1 - ε ≠ 0 := by linarith [hOverlap.2]
      have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp

-- @node: thm:k-label-rate
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,hOverlap,hmf,K,hK), this result [establishes the stated mathematical conclusion](goal). -/
theorem optimalKAmbiguity_bounds {ε : ℝ} (mf : ℝ)
    (hOverlap : Overlap ε) (hmf : 0 < mf) -- @realizes mf(positive density floor)
    (K : ℕ) (hK : 0 < K) -- @realizes K(positive label budget)
    :
    (∀ (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ),
      LowerScoreDensity H f mf →
      mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K) ≤
        optimalKAmbiguity ε K H) ∧
    (∀ (H : Measure (ScoreSpace ε)), IsProbabilityMeasure H →
      optimalKAmbiguity ε K H ≤
        (1 - 2 * ε) / (2 * ε * (1 - ε) * K) ∧
      Measurable (equalWidthRelease ε K hK) ∧
      worstCaseAmbiguity H (equalWidthRelease ε K hK) ≤
        (1 - 2 * ε) / (2 * ε * (1 - ε) * K)) := by
  constructor
  · intro H f hDensity
    letI : IsProbabilityMeasure H := hDensity.probability
    exact optimalKAmbiguity_finiteLabel_lower mf hOverlap hmf K hK H f hDensity
  · intro H hH
    letI : IsProbabilityMeasure H := hH
    have heqMeas : Measurable (equalWidthRelease ε K hK) :=
      equalWidthRelease_measurable ε K hK
    have heqUpper := equalWidthRelease_worstCaseAmbiguity_le_all hOverlap hK H
    have hoptimalUpper :
        optimalKAmbiguity ε K H ≤
          (1 - 2 * ε) / (2 * ε * (1 - ε) * K) := by
      unfold optimalKAmbiguity
      calc
        sInf {d : ℝ | ∃ g ∈ kLabelReleases ε K,
            d = worstCaseAmbiguity H g} ≤
            worstCaseAmbiguity H (equalWidthRelease ε K hK) := by
          apply csInf_le
          · refine ⟨0, ?_⟩
            rintro d ⟨g, hg, rfl⟩
            exact worstCaseAmbiguity_nonneg H g hOverlap hg
          · exact ⟨equalWidthRelease ε K hK, heqMeas, rfl⟩
        _ ≤ _ := heqUpper
    exact ⟨hoptimalUpper, heqMeas, heqUpper⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
