module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerBasic
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificateTransfer
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCoverage
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogFinal

/-! Assembly of the two-source lower certificate. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: externalExcessRisk_normalized_upper
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,α,hOverlap,hg,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessRisk_normalized_upper {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (hα : 0 < α ∧ α < 1 / 2)
    (Qj : ∀ n m, Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : ∀ (n m : ℕ), JointTrialIID g (Qj n m))
    (hLog : ∀ (n m : ℕ), ExternalLogIID g (Qj n m))
    (hInd : ∀ (n m : ℕ), ExternalLogIndependent g (Qj n m)) :
    ∃ C : ℝ, ∀ n m : ℕ, 0 < n → 0 < m →
      externalNormalizer n m * externalExcessRisk g (Qj n m) α ≤ C := by
  let L : ℝ := 4 * (ε⁻¹ + (ε ^ 2)⁻¹)
  let A : ℝ := L * (4 * J / α + 2 * J)
  let B : ℝ := L * (2 * J * (2 - 2 * ε) / α + J * (2 - 2 * ε))
  let C : ℝ := A + B + 1
  have hε : 0 < ε := hOverlap.1
  have hαpos : 0 < α := hα.1
  have hw : 0 < 2 - 2 * ε := by linarith [hOverlap.2]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hA : 0 ≤ A := by dsimp [A]; exact mul_nonneg hL (by positivity)
  have hB : 0 ≤ B := by dsimp [B]; exact mul_nonneg hL (by positivity)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  refine ⟨C, ?_⟩
  intro n m hn hm
  have hscale :
      4 * (ε⁻¹ + (ε ^ 2)⁻¹) *
        (4 * J / (α * Real.sqrt n) + 2 * J / Real.sqrt n +
          2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
          J * (2 - 2 * ε) / Real.sqrt m) ≤
        C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) := by
    have hAn : A ≤ C := by dsimp [C]; linarith
    have hBm : B ≤ C := by dsimp [C]; linarith
    calc
      _ = A * (Real.sqrt (n : ℝ))⁻¹ +
          B * (Real.sqrt (m : ℝ))⁻¹ := by
        dsimp [A, B, L]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ C * (Real.sqrt (n : ℝ))⁻¹ +
          C * (Real.sqrt (m : ℝ))⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_right hAn (by positivity))
          (mul_le_mul_of_nonneg_right hBm (by positivity))
      _ = _ := by ring
  let CI : ExternalIntervalProcedure ε J n m :=
    externalProjectionIntervalProcedure g α hOverlap hg
  have hCI : CI ∈ externalHonestProcedures g (Qj n m) α :=
    externalProjectionIntervalProcedure_honest g α hOverlap hg hn hm hα.1
      (Qj n m) (hTrial n m) (hLog n m) (hInd n m)
  have hExp : ∀ PH, ∀ hPH : PH ∈ ExternalLaws g,
      (∫ x, max 0 (CI.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH)) ∂(Qj n m PH.1 PH.2)) ≤
        C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) := by
    intro PH hPH
    exact (externalProjectionIntervalProcedure_population_meanExcessLength_le
      g (Qj n m) (hTrial n m) (hLog n m) (hInd n m)
      PH hPH hn hm α hα.1).trans hscale
  have hRisk := externalExcessRisk_le_of_honest_uniform_bound g α hOverlap hg
    (Qj n m) (hTrial n m) (hLog n m) (hInd n m) CI hCI _
    (by positivity) hExp
  exact (externalNormalizedRisk_le_of_rootSum_bound g (Qj n m) α C hn hm hRisk)

-- @node: lem:external-two-source-lower-certificate
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,α,hOverlap,hg,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessRisk_lower_certificates {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (hα : 0 < α ∧ α < 1 / 2)
    (Qj : ∀ n m, Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : ∀ (n m : ℕ), JointTrialIID g (Qj n m))
    (hLog : ∀ (n m : ℕ), ExternalLogIID g (Qj n m))
    (hInd : ∀ (n m : ℕ), ExternalLogIndependent g (Qj n m)) :
    (0 < fiberTripleSeparation g ∧ fiberTripleSeparation g ≤ 1) ∧
    (∀ (n m : ℕ), 0 < n → 0 < m →
      -- @realizes n(positive trial size) @realizes m(positive log size)
      trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
        externalExcessRisk g (Qj n m) α) ∧
    (logCertificate g α ≤
      liminf (fun m : ℕ => sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * externalExcessRisk g (Qj n m) α}) atTop ∧
      0 < logCertificate g α) ∧
    (∀ ρ : ℝ, 0 < ρ →
      -- @realizes rho(positive asymptotic ratio)
      max (trialCertificate α / (1 + Real.sqrt ρ))
        (logCertificate g α * Real.sqrt ρ / (1 + Real.sqrt ρ)) ≤
          liminf (fun nm : ℕ × ℕ =>
            externalNormalizedRisk g (Qj nm.1 nm.2) α) (ratioFilter ρ) ∧
      0 < max (trialCertificate α / (1 + Real.sqrt ρ))
        (logCertificate g α * Real.sqrt ρ / (1 + Real.sqrt ρ))) := by
  have hconstants := externalCertificate_constants_pos g α hOverlap hα
  have hLogCert : logCertificate g α ≤
      liminf (fun m : ℕ => sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * externalExcessRisk g (Qj n m) α}) atTop := by
    obtain ⟨C, hUpper⟩ := externalExcessRisk_normalized_upper g α
      hOverlap hg hα Qj hTrial hLog hInd
    exact scoreLog_logCertificate_liminf g hOverlap hg α hα Qj
      hTrial hLog hInd C hUpper
  have hTrialCert : ∀ (n m : ℕ), 0 < n → 0 < m →
      trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
        externalExcessRisk g (Qj n m) α := by
    intro n m hn hm
    let H : Measure (ScoreSpace ε) := Measure.dirac (trialCenterScore hOverlap)
    let P : Measure (FullRow ε J) := trialCenterFullLaw g hOverlap (1 / 2)
    have hPH : (P, H) ∈ ExternalLaws g :=
      ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by norm_num) (by norm_num),
        inferInstance,
        trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by norm_num) (by norm_num)⟩
    have hbase (C : ExternalIntervalProcedure ε J n m)
        (hC : C ∈ externalHonestProcedures g (Qj n m) α) :
        trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
          sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
            u = ∫ x, max 0 (C.length x -
              sharpATELength PH.2 g (releasedLaw PH.1)
                (externalLawCellMasses g PH hPH))
                ∂(externalExperiment n m PH.1 PH.2)} := by
      let U : Set ℝ := {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
        u = ∫ x, max 0 (C.length x -
          sharpATELength PH.2 g (releasedLaw PH.1)
            (externalLawCellMasses g PH hPH))
            ∂(externalExperiment n m PH.1 PH.2)}
      have hUbd : BddAbove U := by
        refine ⟨2, ?_⟩
        rintro u ⟨PH, hPH', rfl⟩
        simpa only [jointTrialLog_eq_externalExperiment g (Qj n m)
          (hTrial n m) (hLog n m) (hInd n m) PH hPH'] using
          externalExcessIntegral_le_two g (Qj n m) (hTrial n m)
            (hLog n m) (hInd n m) C PH hPH'
      have hzero : sharpATELength H g (releasedLaw P)
          (externalLawCellMasses g (P, H) hPH) = 0 :=
        trialCenter_sharpATELength_eq_zero g hOverlap (releasedLaw P)
          (externalLawCellMasses g (P, H) hPH)
      have hcenter : trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
          ∫ x, max 0 (C.length x -
            sharpATELength H g (releasedLaw P)
              (externalLawCellMasses g (P, H) hPH))
              ∂(externalExperiment n m P H) := by
        have hlen := trialCenter_honest_expectedLength g hOverlap hg α hα hn
          (Qj n m) (hTrial n m) (hLog n m) (hInd n m) C hC
        change trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
          ∫ x, C.length x ∂(Qj n m P H) at hlen
        rw [← jointTrialLog_eq_externalExperiment g (Qj n m)
          (hTrial n m) (hLog n m) (hInd n m) (P, H) hPH]
        convert hlen using 1
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hzero, sub_zero]
        exact max_eq_right (sub_nonneg.mpr (C.ordered x))
      exact hcenter.trans (le_csSup hUbd ⟨(P, H), hPH, rfl⟩)
    unfold externalExcessRisk
    apply le_csInf
    · refine ⟨sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
          u = ∫ x, max 0 ((externalFullInterval ε J n m).length x -
            sharpATELength PH.2 g (releasedLaw PH.1)
              (externalLawCellMasses g PH hPH))
              ∂(externalExperiment n m PH.1 PH.2)}, ?_⟩
      exact ⟨externalFullInterval ε J n m,
        externalFullInterval_honest g α hα.1.le (Qj n m)
          (hTrial n m) (hLog n m) (hInd n m), rfl⟩
    · rintro v ⟨C, hC, rfl⟩
      exact hbase C hC
  refine ⟨fiberTripleSeparation_bounds g hOverlap, hTrialCert, ?_, ?_⟩
  · exact ⟨hLogCert, hconstants.2⟩
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hUpper⟩ := externalExcessRisk_normalized_upper g α
        hOverlap hg hα Qj hTrial hLog hInd
      let R : ℕ → ℕ → ℝ := fun n m => externalExcessRisk g (Qj n m) α
      have hTrialRatio : trialCertificate α / (1 + Real.sqrt ρ) ≤
          liminf (fun nm : ℕ × ℕ => externalNormalizedRisk g (Qj nm.1 nm.2) α)
            (ratioFilter ρ) := by
        simpa only [R, externalNormalizedRisk] using
          trialCertificate_ratio_liminf_of_upperBound ρ hρ (trialCertificate α) C R
            (fun n m hn hm => by simpa only [R] using hTrialCert n m hn hm)
            (fun n m hn hm => hUpper n m hn hm)
      have hLogRatio : logCertificate g α * Real.sqrt ρ / (1 + Real.sqrt ρ) ≤
          liminf (fun nm : ℕ × ℕ => externalNormalizedRisk g (Qj nm.1 nm.2) α)
            (ratioFilter ρ) := by
        have hNonneg : ∀ n m : ℕ, 0 < n → 0 < m → 0 ≤ R n m := by
          intro n m hn hm
          have hfactor : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
          have hzero : 0 ≤ trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ :=
            mul_nonneg hconstants.1.le hfactor
          exact hzero.trans (by simpa only [R] using hTrialCert n m hn hm)
        simpa only [R, externalNormalizedRisk] using
          logCertificate_ratio_liminf_of_infimum ρ hρ (logCertificate g α) C R
            hNonneg (by simpa only [R] using hLogCert) hUpper
      exact max_le hTrialRatio hLogRatio
    have hden : 0 < 1 + Real.sqrt ρ := by positivity
    have hfirst : 0 < trialCertificate α / (1 + Real.sqrt ρ) :=
      div_pos hconstants.1 hden
    exact lt_of_lt_of_le hfirst (le_max_left _ _)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
