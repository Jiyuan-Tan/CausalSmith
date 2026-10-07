module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerBasic
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogHonestLength
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogThresholds
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogAttainment
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogExperiment
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogLimit

/-! Honest excess-risk transfer from two endpoint-attaining external laws. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,hα,Qj,hTrial,hLog,hInd,P0,P1,H0,H1,hPH0,hPH1,W0,Delta,hW0,htheta,hsep,hDelta,htv), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessRisk_lower_of_twoPoint
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (P0 P1 : Measure (FullRow ε J))
    (H0 H1 : Measure (ScoreSpace ε))
    (hPH0 : (P0, H0) ∈ ExternalLaws g)
    (hPH1 : (P1, H1) ∈ ExternalLaws g)
    (W0 Delta : ℝ)
    (hW0 : sharpATELength H0 g (releasedLaw P0)
      (externalLawCellMasses g (P0, H0) hPH0) = W0)
    (htheta : ate P0 ≤ ate P1)
    (hsep : ate P1 - ate P0 = W0 + Delta)
    (hDelta : 0 < Delta)
    (htv : Causalean.Stat.tvDist (Qj P0 H0) (Qj P1 H1) ≤
      (1 - 2 * α) / 2) :
    Delta * ((1 - 2 * α) / 2) ≤ externalExcessRisk g Qj α := by
  have hbase (C : ExternalIntervalProcedure ε J n m)
      (hC : C ∈ externalHonestProcedures g Qj α) :
      Delta * ((1 - 2 * α) / 2) ≤
        sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
          u = ∫ x, max 0 (C.length x -
            sharpATELength PH.2 g (releasedLaw PH.1)
              (externalLawCellMasses g PH hPH))
              ∂(externalExperiment n m PH.1 PH.2)} := by
    letI : IsProbabilityMeasure (Qj P0 H0) :=
      externalLaw_jointExperiment_probability g Qj hTrial hLog hInd
        (P0, H0) hPH0
    letI : IsProbabilityMeasure (Qj P1 H1) :=
      externalLaw_jointExperiment_probability g Qj hTrial hLog hInd
        (P1, H1) hPH1
    have hc0 := hC (P0, H0) hPH0
    have hc1 := hC (P1, H1) hPH1
    have hQ0 := jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd
      (P0, H0) hPH0
    have hQ1 := jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd
      (P1, H1) hPH1
    change 1 - α ≤ (externalExperiment n m P0 H0).real
      {x | C.contains x (ate P0)} at hc0
    change 1 - α ≤ (externalExperiment n m P1 H1).real
      {x | C.contains x (ate P1)} at hc1
    rw [← hQ0] at hc0
    rw [← hQ1] at hc1
    have hexcess := externalInterval_twoPoint_expectedExcessLength_of_tv
      C (Qj P0 H0) (Qj P1 H1) (ate P0) (ate P1) W0 Delta α
      htheta hsep hDelta hc0 hc1 htv
    rw [← hW0] at hexcess
    rw [hQ0] at hexcess
    let U : Set ℝ := {u | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
      u = ∫ x, max 0 (C.length x -
        sharpATELength PH.2 g (releasedLaw PH.1)
          (externalLawCellMasses g PH hPH))
          ∂(externalExperiment n m PH.1 PH.2)}
    have hUbd : BddAbove U := by
      refine ⟨2, ?_⟩
      rintro u ⟨PH, hPH', rfl⟩
      simpa only [jointTrialLog_eq_externalExperiment g Qj hTrial hLog hInd PH hPH']
        using externalExcessIntegral_le_two g Qj hTrial hLog hInd C PH hPH'
    exact hexcess.trans (le_csSup hUbd ⟨(P0, H0), hPH0, rfl⟩)
  unfold externalExcessRisk
  apply le_csInf
  · refine ⟨sSup {u : ℝ | ∃ PH, ∃ hPH : PH ∈ ExternalLaws g,
        u = ∫ x, max 0 ((externalFullInterval ε J n m).length x -
          sharpATELength PH.2 g (releasedLaw PH.1)
            (externalLawCellMasses g PH hPH))
            ∂(externalExperiment n m PH.1 PH.2)}, ?_⟩
    exact ⟨externalFullInterval ε J n m,
      externalFullInterval_honest g α hα.1.le Qj hTrial hLog hInd, rfl⟩
  · rintro v ⟨C, hC, rfl⟩
    exact hbase C hC

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,Qj,α,beta,C,hLower,hUpper), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalExcessRisk_log_liminf_of_eventual_uniform
    {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : ∀ n m,
      Measure (FullRow ε J) → Measure (ScoreSpace ε) →
        Measure (ExternalSample ε J n m))
    (α beta C : ℝ)
    (hLower : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n →
      beta * (Real.sqrt (m : ℝ))⁻¹ ≤
        externalExcessRisk g (Qj n m) α)
    (hUpper : ∀ (n m : ℕ), 0 < n → 0 < m →
      externalNormalizer n m * externalExcessRisk g (Qj n m) α ≤ C) :
    beta ≤ liminf (fun m : ℕ =>
      sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * externalExcessRisk g (Qj n m) α}) atTop := by
  exact logCertificate_liminf_infimum_of_normalized_upper beta C
    (fun n m => externalExcessRisk g (Qj n m) α) hLower hUpper

end
end CausalSmith.PartialID.UnlinkedPropensityAte
