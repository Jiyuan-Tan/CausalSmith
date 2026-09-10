/- Correct four-mode inclusion and equilibrium-continuum obstruction. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.GuoXuRecursion
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.StochasticApproximation

/-! # Guo--Xu normalized-inclusion obstruction -/

open Set Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

local instance : MeasurableSpace GuoXuState := ⊤

def guoXuEquilibriumV (u : ℝ) : ℝ :=
  (3 * u + 18 - Real.sqrt (25 * u ^ 2 - 228 * u + 324)) / 32

def guoXuInclusionObstructionConclusion (sigma1 sigma2 : ℝ)
    (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2) : Prop :=
  let p : ℝ := 99 / 100
  let q : ℝ := 1 / 100
  let u0 : ℝ := (47 + Real.sqrt 4609) / 150
  let b0 : ℝ := (Real.sqrt 4609 - 91) / 1224
  let vstar : ℝ := 2097 / 3200 - 3 * Real.sqrt 5457 / 640
  0 < sigma1 ∧ 0 < sigma2 ∧
  (∀ u, u ∈ Icc u0 p →
    let v := guoXuEquilibriumV u
    guoXuAtom u v ∈ convexHull ℝ ((fun z : ℝ × ℝ => guoXuAtom z.1 z.2) ''
      (Icc q p ×ˢ Icc q p)) ∧
    (guoXuAtom u v) 0 < (guoXuAtom u v) 1 ∧
    0 ∈ guoXuSetValuedMap (guoXuAtom u v)) ∧
  vstar = guoXuEquilibriumV p ∧
  guoXuAtom p vstar ≠ guoXuAtom q p ∧
  guoXuAtom p vstar ≠ guoXuAtom u0 (1 - u0) ∧
  guoXuAtom p vstar ≠ guoXuAtom p q ∧
  (67 : ℝ) < Real.sqrt 4609 ∧ Real.sqrt 4609 < 68 ∧
  (73 : ℝ) < Real.sqrt 5457 ∧ Real.sqrt 5457 < 74 ∧
  (∀ u v, u ∈ Icc q p → v ∈ Icc q p →
    (guoXuAtom u v) 2 * (guoXuAtom u v) 1 =
      (guoXuAtom u v) 3 * (guoXuAtom u v) 0 →
    u ^ 2 + 12 * u * v - 21 * u - 64 * v ^ 2 + 72 * v = 0) ∧
  b0 = (Real.sqrt 4609 - 91) / 1224 ∧
  (∀ eta0 : Fin 2 → ℝ, ∀ heta : (∀ a, eta0 a ∈ Icc (-1 : ℝ) 1),
    ∀ᵐ noise ∂guoXuProcessLaw,
      let hsigma := guoXuPositiveScales_pair hsigma1 hsigma2
      let state := guoXuRecursion eta0 heta ![sigma1, sigma2] hsigma noise
      let D := guoXuNormalizedHandle eta0 heta ![sigma1, sigma2] hsigma noise
      state 0 = guoXuInitial eta0 heta ∧ D.state = state ∧
      (∀ t a, 0 < (state t).invGram a ∧ (state t).invGram a ≤ 1) ∧
      (∃ C > 0, ∀ᶠ t in Filter.atTop, ∀ a, (state t).invGram a ≤ C / t) ∧
      GuoXuReductionConditions D ∧
      (∃ interpolation : ℝ → Vec 4,
        (∀ t : ℕ, interpolation t = D.psi t) ∧
        (∀ t : ℕ, ∀ s ∈ Icc (0 : ℝ) 1,
          interpolation ((t : ℝ) + s) =
            (1 - s) • D.psi t + s • D.psi (t + 1)) ∧
        PerturbedSolution guoXuSetValuedMap interpolation ∧ BoundedPath interpolation ∧
        AsymptoticPseudoTrajectory guoXuSetValuedMap interpolation ∧
        InternallyChainTransitive guoXuSetValuedMap
          (DifferentialInclusionLimitSet interpolation) ∧
        DifferentialInclusionLimitSet interpolation ⊆
          (fun z : ℝ × ℝ => guoXuAtom z.1 z.2) '' (Icc q p ×ˢ Icc q p))) ∧
  (∃ (lockPlus lockMinus : Set GuoXuNoisePath) (c0 : ℝ),
    0 < c0 ∧
    lockPlus = {noise | ∀ (eta0 : Fin 2 → ℝ)
      (heta : ∀ a, eta0 a ∈ Icc (-1 : ℝ) 1),
      ∃ eps > 0, ∀ᶠ t in atTop,
        eps ≤ (guoXuRecursion eta0 heta ![sigma1, sigma2]
          (guoXuPositiveScales_pair hsigma1 hsigma2) noise t).slope 0 -
          (guoXuRecursion eta0 heta ![sigma1, sigma2]
            (guoXuPositiveScales_pair hsigma1 hsigma2) noise t).slope 1} ∧
    lockMinus = {noise | ∀ (eta0 : Fin 2 → ℝ)
      (heta : ∀ a, eta0 a ∈ Icc (-1 : ℝ) 1),
      ∃ eps > 0, ∀ᶠ t in atTop,
        (guoXuRecursion eta0 heta ![sigma1, sigma2]
          (guoXuPositiveScales_pair hsigma1 hsigma2) noise t).slope 0 -
          (guoXuRecursion eta0 heta ![sigma1, sigma2]
            (guoXuPositiveScales_pair hsigma1 hsigma2) noise t).slope 1 ≤ -eps} ∧
    (∀ eta0 : Fin 2 → ℝ, (∀ a, eta0 a ∈ Icc (-1 : ℝ) 1) →
      guoXuProcessLaw univ = 1 ∧ c0 ≤ (guoXuProcessLaw lockPlus).toReal ∧
        c0 ≤ (guoXuProcessLaw lockMinus).toReal) ∧
    (∀ noise ∈ lockPlus, ∀ (eta0 : Fin 2 → ℝ)
      (heta : ∀ a, eta0 a ∈ Icc (-1 : ℝ) 1),
      let hsigma := guoXuPositiveScales_pair hsigma1 hsigma2
      let z := guoXuRecursion eta0 heta ![sigma1, sigma2] hsigma noise
      Tendsto (fun t => WithLp.toLp 2 ![(z t).slope 0, (z t).slope 1])
        atTop (nhds (WithLp.toLp 2 ![19 / 46, -79 / 3804])) ∧
      Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
        ‖WithLp.toLp 2 ![(z t).slope 0, (z t).slope 1] -
          WithLp.toLp 2 ![19 / 46, -79 / 3804]‖) atTop (nhds 0)) ∧
    (∀ noise ∈ lockMinus, ∀ (eta0 : Fin 2 → ℝ)
      (heta : ∀ a, eta0 a ∈ Icc (-1 : ℝ) 1),
      let hsigma := guoXuPositiveScales_pair hsigma1 hsigma2
      let z := guoXuRecursion eta0 heta ![sigma1, sigma2] hsigma noise
      Tendsto (fun t => WithLp.toLp 2 ![(z t).slope 0, (z t).slope 1])
        atTop (nhds (WithLp.toLp 2 ![-79 / 634, 19 / 276])) ∧
      Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
        ‖WithLp.toLp 2 ![(z t).slope 0, (z t).slope 1] -
          WithLp.toLp 2 ![-79 / 634, 19 / 276]‖) atTop (nhds 0))) ∧
  ¬ (∀ psi, (0 ∈ guoXuSetValuedMap psi) →
    psi = guoXuAtom q p ∨ psi = guoXuAtom u0 (1 - u0) ∨ psi = guoXuAtom p q)

-- @node: thm:guoxu-normalized-inclusion-obstruction
theorem guoxu_normalized_inclusion_obstruction
    (hPerturbed : BHSPerturbedLimitSetICT) (hLyapunov : BHSLyapunovICT)
    (sigma1 sigma2 : ℝ) (hsigma1 : 0 < sigma1) (hsigma2 : 0 < sigma2) :
    guoXuInclusionObstructionConclusion sigma1 sigma2 hsigma1 hsigma2 := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
