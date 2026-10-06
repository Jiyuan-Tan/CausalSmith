module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificateAssembly
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCoverage
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Projection
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionPopulation
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionScorePopulation
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCandidateStability
public import Causalean.Stat.Minimax.TotalVariation

/-! Root-two-sample order for the external score-log experiment. -/

public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: thm:external-score-root-order
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,α,hOverlap,hg,hα,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
theorem externalExcessRisk_root_order {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (hα : 0 < α ∧ α < 1 / 2) -- @realizes alpha(miscoverage range)
    (Qj : ∀ n m, Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : ∀ (n m : ℕ), JointTrialIID g (Qj n m))
    (hLog : ∀ (n m : ℕ), ExternalLogIID g (Qj n m))
    (hInd : ∀ (n m : ℕ), ExternalLogIndependent g (Qj n m)) :
    (0 < fiberTripleSeparation g ∧ fiberTripleSeparation g ≤ 1) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ), 0 < n → 0 < m →
        -- @realizes n(positive trial size) @realizes m(positive log size)
        trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
          externalExcessRisk g (Qj n m) α ∧
        externalExcessRisk g (Qj n m) α ≤
          C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) ∧
        ∃ CI : ExternalIntervalProcedure ε J n m,
          CI ∈ externalHonestProcedures g (Qj n m) α ∧
          (∀ x, Set.Icc (CI.lo x) (CI.hi x) = externalProjectionCI g α x) ∧
          ∀ PH, ∀ hPH : PH ∈ ExternalLaws g,
            (∫ x, max 0 (CI.length x -
              sharpATELength PH.2 g (releasedLaw PH.1)
                (externalLawCellMasses g PH hPH)) ∂(Qj n m PH.1 PH.2)) ≤
                C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹)) ∧
    (logCertificate g α ≤
      liminf (fun m : ℕ => sInf {v : ℝ | ∃ n : ℕ, 0 < n ∧
        v = Real.sqrt (m : ℝ) * externalExcessRisk g (Qj n m) α}) atTop ∧
      0 < logCertificate g α) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
      -- @realizes rho(positive asymptotic ratio)
      max (trialCertificate α / (1 + Real.sqrt ρ))
        (logCertificate g α * Real.sqrt ρ / (1 + Real.sqrt ρ)) ≤
          liminf (fun nm : ℕ × ℕ =>
            externalNormalizedRisk g (Qj nm.1 nm.2) α) (ratioFilter ρ) ∧
      liminf (fun nm : ℕ × ℕ =>
        externalNormalizedRisk g (Qj nm.1 nm.2) α) (ratioFilter ρ) ≤
          limsup (fun nm : ℕ × ℕ =>
            externalNormalizedRisk g (Qj nm.1 nm.2) α) (ratioFilter ρ) ∧
      limsup (fun nm : ℕ × ℕ =>
        externalNormalizedRisk g (Qj nm.1 nm.2) α) (ratioFilter ρ) ≤ C ∧
      0 < max (trialCertificate α / (1 + Real.sqrt ρ))
        (logCertificate g α * Real.sqrt ρ / (1 + Real.sqrt ρ))) := by
  have hLower := externalExcessRisk_lower_certificates g α hOverlap hg hα Qj
    hTrial hLog hInd
  have hRate : ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ), 0 < n → 0 < m →
        trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
          externalExcessRisk g (Qj n m) α ∧
        externalExcessRisk g (Qj n m) α ≤
          C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) ∧
        ∃ CI : ExternalIntervalProcedure ε J n m,
          CI ∈ externalHonestProcedures g (Qj n m) α ∧
          (∀ x, Set.Icc (CI.lo x) (CI.hi x) = externalProjectionCI g α x) ∧
          ∀ PH, ∀ hPH : PH ∈ ExternalLaws g,
            (∫ x, max 0 (CI.length x -
              sharpATELength PH.2 g (releasedLaw PH.1)
                (externalLawCellMasses g PH hPH)) ∂(Qj n m PH.1 PH.2)) ≤
                C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) := by
    let L : ℝ := 4 * (ε⁻¹ + (ε ^ 2)⁻¹)
    let A : ℝ := L * (4 * J / α + 2 * J)
    let B : ℝ := L * (2 * J * (2 - 2 * ε) / α + J * (2 - 2 * ε))
    let C : ℝ := A + B + 1
    have hε : 0 < ε := hOverlap.1
    have hαpos : 0 < α := hα.1
    have hw : 0 < 2 - 2 * ε := by linarith [hOverlap.2]
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hL (by positivity)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hL (by positivity)
    have hC : 0 < C := by dsimp [C]; linarith
    have hscale (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
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
    refine ⟨C, hC, ?_⟩
    intro n m hn hm
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
        PH hPH hn hm α hα.1).trans (hscale n m hn hm)
    have hRisk : externalExcessRisk g (Qj n m) α ≤
        C * ((Real.sqrt (n : ℝ))⁻¹ + (Real.sqrt (m : ℝ))⁻¹) :=
      externalExcessRisk_le_of_honest_uniform_bound g α hOverlap hg
        (Qj n m) (hTrial n m) (hLog n m) (hInd n m) CI hCI _
        (by positivity) hExp
    refine ⟨hLower.2.1 n m hn hm, hRisk, CI, hCI, ?_, hExp⟩
    intro x
    exact externalProjectionIntervalProcedure_Icc g α hOverlap hg x
  refine ⟨hLower.1, hRate, hLower.2.2.1, ?_⟩
  obtain ⟨C, hC, hRate⟩ := hRate
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  let risk : ℕ × ℕ → ℝ := fun nm =>
    externalNormalizedRisk g (Qj nm.1 nm.2) α
  have hPoint : ∀ nm : ℕ × ℕ, 0 < nm.1 → 0 < nm.2 → risk nm ≤ C := by
    intro nm hn hm
    have hsum : 0 < (Real.sqrt (nm.1 : ℝ))⁻¹ +
        (Real.sqrt (nm.2 : ℝ))⁻¹ := by positivity
    have hb := (hRate nm.1 nm.2 hn hm).2.1
    dsimp [risk, externalNormalizedRisk, externalNormalizer]
    calc
      ((Real.sqrt (nm.1 : ℝ))⁻¹ + (Real.sqrt (nm.2 : ℝ))⁻¹)⁻¹ *
          externalExcessRisk g (Qj nm.1 nm.2) α ≤
        ((Real.sqrt (nm.1 : ℝ))⁻¹ + (Real.sqrt (nm.2 : ℝ))⁻¹)⁻¹ *
          (C * ((Real.sqrt (nm.1 : ℝ))⁻¹ + (Real.sqrt (nm.2 : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C := by field_simp
  have hEvUpper : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, risk nm ≤ C := by
    filter_upwards [ratioFilter_eventually_pos ρ] with nm hnm
    exact hPoint nm hnm.1 hnm.2
  have hEvLower : ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, 0 ≤ risk nm := by
    filter_upwards [ratioFilter_eventually_pos ρ] with nm hnm
    have htrial := (hRate nm.1 nm.2 hnm.1 hnm.2).1
    have hcert : 0 ≤ trialCertificate α := (externalCertificate_constants_pos g α hOverlap hα).1.le
    have hrisk : 0 ≤ externalExcessRisk g (Qj nm.1 nm.2) α :=
      le_trans (mul_nonneg hcert (by positivity)) htrial
    exact mul_nonneg (by dsimp [externalNormalizer]; positivity) hrisk
  haveI : (ratioFilter ρ).NeBot := ratioFilter_neBot ρ hρ
  have hBddAbove : IsBoundedUnder (· ≤ ·) (ratioFilter ρ) risk :=
    isBoundedUnder_of_eventually_le hEvUpper
  have hBddBelow : IsBoundedUnder (· ≥ ·) (ratioFilter ρ) risk :=
    isBoundedUnder_of_eventually_ge hEvLower
  have hLimsup : limsup risk (ratioFilter ρ) ≤ C :=
    limsup_le_of_le hBddBelow.isCoboundedUnder_le hEvUpper
  refine ⟨(hLower.2.2.2 ρ hρ).1, ?_, hLimsup,
    (hLower.2.2.2 ρ hρ).2⟩
  exact liminf_le_limsup

end CausalSmith.PartialID.UnlinkedPropensityAte
