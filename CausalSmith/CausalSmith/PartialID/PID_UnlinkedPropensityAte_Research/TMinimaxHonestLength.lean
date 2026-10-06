module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthFiniteLabelOuter
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthSamplingLower
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthRateAssembly
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthUpper

/-! Known-score minimax honest confidence-length order. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: thm:minimax-honest-length
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα), this result [establishes the stated mathematical conclusion](goal). -/
theorem minimaxHonestLength_order (ε α : ℝ)
    (hOverlap : Overlap ε)
    (hα : 0 < α ∧ α < 1 / 2) -- @realizes alpha(miscoverage range)
    :
    ∃ C samplingConstant : ℝ, 0 < C ∧ 0 < samplingConstant ∧
      (∀ (H : Measure (ScoreSpace ε)) (_hH : IsProbabilityMeasure H)
        (n K : ℕ) (_hn : 0 < n) (_hK : 0 < K),
        samplingConstant * (Real.sqrt (n : ℝ))⁻¹ ≤
          minimaxHonestLength n K H α) ∧
      (∀ (mf : ℝ) (_hmf : 0 < mf), -- @realizes mf(positive density floor)
        ∃ c : ℝ, 0 < c ∧
          ∀ (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
            (_hH : IsProbabilityMeasure H) (_hDensity : LowerScoreDensity H f mf)
            (n K : ℕ) (_hn : 0 < n) (hK : 0 < K),
            -- @realizes n(positive trial sample size) @realizes K(positive label budget)
            c * ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) ≤
              minimaxHonestLength n K H α ∧
            minimaxHonestLength n K H α ≤
              C * ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) ∧
            (∃ CI : IntervalProcedure n K,
              (equalWidthRelease ε K hK, CI) ∈ honestProcedures n K H α ∧
              (∀ x, CI.lo x = clampATE
                  (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K) ∧
                CI.hi x = clampATE
                  (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K)) ∧
              ∀ P ∈ CausalLaws H (equalWidthRelease ε K hK),
                (∫ x, CI.length x ∂(Measure.pi (fun _ : Fin n => releasedLaw P))) ≤
              C * ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹))) := by
  let B : ℝ := trialCertificate α
  let U : ℝ := midpointLengthConstant ε α
  let C : ℝ := max B U
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  have hlog : 0 < Real.log (1 + (1 - 2 * α) ^ 2) := by
    exact Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hB : 0 < B := by
    dsimp [B]
    unfold trialCertificate
    positivity
  have hC : 0 < C := lt_of_lt_of_le hB (le_max_left B U)
  refine ⟨C, B, hC, hB, ?_, ?_⟩
  · intro H hH n K hn hK
    let _ : IsProbabilityMeasure H := hH
    simpa [B] using
      (minimaxHonestLength_sampling_lower hOverlap hα H hn hK)
  · intro mf hmf
    let A : ℝ :=
      (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε))
    let c : ℝ := min A B / 2
    have hgap : 0 < 1 - 2 * ε := by linarith [hOverlap.2]
    have hden : 0 < 1 - ε := by linarith [hOverlap.2]
    have hA : 0 < A := by
      dsimp [A]
      positivity
    have hc : 0 < c := by
      dsimp [c]
      exact div_pos (lt_min hA hB) (by norm_num)
    refine ⟨c, hc, ?_⟩
    intro H f hH hDensity n K hn hK
    let _ : IsProbabilityMeasure H := hH
    let R : ℝ := (K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹
    have hFinite := minimaxHonestLength_finiteLabel_lower
      hOverlap hα hmf H f hDensity n K hn hK
    have hLabel : A * (K : ℝ)⁻¹ ≤ minimaxHonestLength n K H α := by
      have hKne : (K : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hK)
      have hdene : 1 - ε ≠ 0 := ne_of_gt hden
      calc
        A * (K : ℝ)⁻¹ =
            (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 /
              (2 * (1 - ε) * (K : ℝ)) := by
          dsimp [A]
          field_simp
        _ ≤ minimaxHonestLength n K H α := hFinite
    have hSampling := minimaxHonestLength_sampling_lower
      hOverlap hα H hn hK
    have hLowerAssembly := minimaxHonestLength_rate_assembly
      hOverlap hα hmf hn hK hLabel hSampling
    dsimp [A, B, c] at hLowerAssembly
    have hLower : c * R ≤ minimaxHonestLength n K H α := by
      simpa [c, A, B, R] using hLowerAssembly.2
    have hUpperAll := minimaxHonestLength_midpoint_upper
      hOverlap hα H n K hn hK
    have hUC : U ≤ C := le_max_right B U
    have hR : 0 ≤ R := by
      dsimp [R]
      positivity
    have hUpper : minimaxHonestLength n K H α ≤ C * R := by
      calc
        minimaxHonestLength n K H α ≤ U * R := by
          simpa [U, R] using hUpperAll
        _ ≤ C * R := mul_le_mul_of_nonneg_right hUC hR
    obtain ⟨CI, hCI, hformula, hCIU⟩ :=
      exists_equalWidth_midpointInterval hOverlap hα H n K hn hK
    refine ⟨by simpa [R] using hLower, by simpa [R] using hUpper,
      CI, hCI, hformula, ?_⟩
    intro P hP
    calc
      (∫ x, CI.length x ∂(Measure.pi (fun _ : Fin n => releasedLaw P))) ≤
          U * R := by simpa [U, R] using hCIU P hP
      _ ≤ C * R := mul_le_mul_of_nonneg_right hUC hR

end CausalSmith.PartialID.UnlinkedPropensityAte
