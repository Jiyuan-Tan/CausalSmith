module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TUniformFrontier

/-! TErrorFreeReduction -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u


/-- At zero noise the direct branch gives the exact weak-design power law. [This is the stated conclusion](goal). -/
-- @node: frontierRate_zero
lemma frontierRate_zero (beta kappa : ℝ) (n : ℕ) :
    frontierRate beta kappa 0 n = (n : ℝ)^(-beta / effDim beta kappa) := by
  have hd : 0 ≤ directScale beta kappa n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  change (if 0 ≤ directScale beta kappa n then directScale beta kappa n
    else if 0 ≤ (logScale n)^(-1/2 : ℝ) then fourierScale beta kappa 0 n
    else polynomialScale 0 n)^beta = _
  rw [if_pos hd]
  change ((n : ℝ)^(-1 / effDim beta kappa))^beta = _
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

/-- Zero measurement error gives the same-class weak-design orders for minimax risk and for honest length at a noncoverage level below one half, and the separate Gaiffas experiment has comparable minimax absolute risk. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate,hGaiffas_of_gate,K,hbeta,hkappa,halpha,hK). [This is the stated conclusion](goal). -/
-- @node: prop:error-free-reduction
theorem error_free_reduction (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (hGaiffas_of_gate : GaiffasDirectBenchmark)
    (K : ClassConstants) (beta kappa alpha : ℝ) (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) (1/2))
    (hK : K.clo ≤ (kappa+1)*(2 : ℝ)^kappa ∧ (kappa+1)*(2 : ℝ)^kappa ≤ K.chi) :
    (∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ENNReal.ofReal (c*(n : ℝ)^(-beta/effDim beta kappa)) ≤ minimaxRisk E K beta kappa n 0 ∧
      minimaxRisk E K beta kappa n 0 ≤ ENNReal.ofReal (C*(n : ℝ)^(-beta/effDim beta kappa)) ∧
      ENNReal.ofReal (c*(n : ℝ)^(-beta/effDim beta kappa)) ≤ honestLength E K beta kappa alpha n 0 ∧
      honestLength E K beta kappa alpha n 0 ≤ ENNReal.ofReal (C*(n : ℝ)^(-beta/effDim beta kappa))) ∧
    (∀ cG rG MG tauG : ℝ, 0 < cG → 0 < rG → 0 < MG → 0 < tauG →
      ∀ xstar : Dose, 0 < (xstar : ℝ) → (xstar : ℝ) < 1 →
      ∀ delta : ℝ, 0 < delta → delta ≤ min (xstar : ℝ) (1-(xstar : ℝ)) →
      ∀ nu : ProbabilityMeasure Dose, GaiffasDesign kappa cG xstar delta nu →
      ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
        ENNReal.ofReal c * gaiffasMinimax beta kappa cG rG MG tauG xstar nu n ≤ minimaxRisk E K beta kappa n 0 ∧
        minimaxRisk E K beta kappa n 0 ≤ ENNReal.ofReal C * gaiffasMinimax beta kappa cG rG MG tauG xstar nu n) := by
  obtain ⟨⟨c, C, hc, hcC, n0, hfront⟩, _⟩ :=
    uniform_frontier hLocalization_of_gate hLipschitz_of_gate hNorm_of_gate
      hGamma_of_gate K beta kappa alpha hbeta hkappa halpha hK
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (1/4) := by constructor <;> norm_num
  have hdirect : ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ENNReal.ofReal (c*(n : ℝ)^(-beta/effDim beta kappa)) ≤ minimaxRisk E K beta kappa n 0 ∧
      minimaxRisk E K beta kappa n 0 ≤ ENNReal.ofReal (C*(n : ℝ)^(-beta/effDim beta kappa)) ∧
      ENNReal.ofReal (c*(n : ℝ)^(-beta/effDim beta kappa)) ≤ honestLength E K beta kappa alpha n 0 ∧
      honestLength E K beta kappa alpha n 0 ≤ ENNReal.ofReal (C*(n : ℝ)^(-beta/effDim beta kappa)) := by
    intro S _ E n hn
    simpa only [frontierRate_zero] using (hfront S E n hn).1 0 hzero
  refine ⟨⟨c, C, hc, hcC, n0, hdirect⟩, ?_⟩
  intro cG rG MG tauG hcG hrG hMG htauG xstar hx0 hx1 delta hdelta hdeltaBound nu hdesign
  have hbeta0 : 0 < beta := hbeta.1
  obtain ⟨cg, CG, hcg, hcgCG, nG, hG⟩ :=
    hGaiffas_of_gate beta kappa cG rG MG tauG hbeta0 hbeta.2 hkappa
      hcG hrG hMG htauG xstar hx0 hx1 delta hdelta hdeltaBound nu hdesign
  have hCG : 0 < CG := hcg.trans hcgCG
  have hC : 0 < C := hc.trans hcC
  let cl := c / CG
  let Cu := C / cg + cl + 1
  have hcl : 0 < cl := div_pos hc hCG
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  have hclCu : cl < Cu := by
    have : 0 < C / cg := div_pos hC hcg
    dsimp [Cu]
    linarith
  have hcancel : cl * CG = c := by dsimp [cl]; exact div_mul_cancel₀ c (ne_of_gt hCG)
  have hdom : C ≤ Cu * cg := by
    have hcancelG : C / cg * cg = C := div_mul_cancel₀ C (ne_of_gt hcg)
    dsimp [Cu]
    nlinarith
  refine ⟨cl, Cu, hcl, hclCu, max n0 nG, ?_⟩
  intro S _ E n hn
  have hn0 : n0 ≤ n := (le_max_left n0 nG).trans hn
  have hnG : nG ≤ n := (le_max_right n0 nG).trans hn
  have hrisk := hdirect S E n hn0
  have hbench := hG n hnG
  have hp : 0 ≤ (n : ℝ)^(-beta/effDim beta kappa) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbenchLower : ENNReal.ofReal (cg*(n : ℝ)^(-beta/effDim beta kappa)) ≤
      gaiffasMinimax beta kappa cG rG MG tauG xstar nu n := by
    simpa only [effDim] using hbench.2.1
  have hbenchUpper : gaiffasMinimax beta kappa cG rG MG tauG xstar nu n ≤
      ENNReal.ofReal (CG*(n : ℝ)^(-beta/effDim beta kappa)) := by
    simpa only [effDim] using hbench.2.2.1
  constructor
  · calc
      ENNReal.ofReal cl * gaiffasMinimax beta kappa cG rG MG tauG xstar nu n
          ≤ ENNReal.ofReal cl * ENNReal.ofReal (CG*(n : ℝ)^(-beta/effDim beta kappa)) :=
        mul_le_mul le_rfl hbenchUpper zero_le zero_le
      _ = ENNReal.ofReal (c*(n : ℝ)^(-beta/effDim beta kappa)) := by
        rw [← ENNReal.ofReal_mul hcl.le, ← mul_assoc, hcancel]
      _ ≤ minimaxRisk E K beta kappa n 0 := hrisk.1
  · calc
      minimaxRisk E K beta kappa n 0
          ≤ ENNReal.ofReal (C*(n : ℝ)^(-beta/effDim beta kappa)) := hrisk.2.1
      _ ≤ ENNReal.ofReal (Cu*(cg*(n : ℝ)^(-beta/effDim beta kappa))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hdom hp
      _ = ENNReal.ofReal Cu * ENNReal.ofReal (cg*(n : ℝ)^(-beta/effDim beta kappa)) :=
        ENNReal.ofReal_mul hCu.le
      _ ≤ ENNReal.ofReal Cu * gaiffasMinimax beta kappa cG rG MG tauG xstar nu n :=
        mul_le_mul le_rfl hbenchLower zero_le zero_le

end CausalSmith.Stat.NoisydoseWeakdesignTransition
