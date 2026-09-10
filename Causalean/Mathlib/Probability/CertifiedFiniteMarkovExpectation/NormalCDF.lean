import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Quadrature
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Transcendental
import Causalean.Mathlib.Probability.StdNormalCDF
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Certified rational enclosures for the standard normal CDF

This module gives an executable, exact-rational checker for standard-normal CDF
values at rational endpoints.  It combines Causalean's certified Machin
enclosure for π, Newton square-root enclosure, exponential enclosure, and a
rigorously widened trapezoidal rule.  A caller may enlarge the computed result,
but cannot introduce a decimal endpoint without proving an exact rational
subinterval check.

## Scaling limitation — read before instantiating

The trapezoidal rule here uses a UNIFORM mesh, so the node count is set by the
worst-behaved part of the interval rather than by local curvature.  Away from the
origin this is severe: at endpoint `193/5` with target width `1e-12` the mesh floor
forces more than `5.7e16` exact-rational nodes, which is sound but not computable in
practice.  The checker is therefore usable for narrow targets near the origin and
unusable for tight enclosures at large endpoints.

A caller needing the latter wants a symmetry + central-series + Mills-tail
construction instead, which spends nodes only where the integrand is hard.  That
replacement was scoped as its own study after this limitation was found during
`stat_pomdp_latent_overlap_minimax` (2026-09-10); nothing here is wrong, it is a
question of which regime you are in.
-/

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The interval enclosing `2π` at a chosen exact arithmetic fuel level. -/
def twoPiInterval (fuel : ℕ) : RatInterval :=
  (RatInterval.point 2).mul
    (Complex.Transcendental.piInterval fuel)

/-- A normal-CDF schedule records a positive mesh and the exact rational side
conditions needed to invert the computed enclosure of `sqrt (2π)`. -/
structure NormalCDFSchedule where
  /-- Precision used by the π, square-root, and exponential interval evaluators. -/
  fuel : ℕ
  /-- Number of cells in the certified trapezoidal quadrature. -/
  mesh : ℕ
  /-- The quadrature mesh is nonempty. -/
  mesh_pos : 0 < mesh
  /-- The computed lower endpoint for `2π` is nonnegative. -/
  twoPi_nonneg : 0 ≤ (twoPiInterval fuel).lo
  /-- The computed square-root interval excludes zero, so its reciprocal is sound. -/
  sqrt_away :
    (RatInterval.sqrtInterval (twoPiInterval fuel) twoPi_nonneg fuel).AwayFromZero

/-- The certified rational enclosure of the standard-normal density's scale
factor `1 / sqrt (2π)` for a schedule. -/
def normalDensityScaleInterval (s : NormalCDFSchedule) : RatInterval :=
  let root := RatInterval.sqrtInterval (twoPiInterval s.fuel) s.twoPi_nonneg s.fuel
  root.inv s.sqrt_away

/-- At a rational nonnegative endpoint and a uniform mesh node, this interval
computes an enclosure of the rescaled Gaussian integrand used for CDF quadrature. -/
def normalDensityNode (q : ℚ) (s : NormalCDFSchedule) (k : ℕ) : RatInterval :=
  let x : ℚ := q * k / s.mesh
  let exponent : ℚ := -(x ^ 2) / 2
  ((RatInterval.point q).mul (normalDensityScaleInterval s)).mul
    (Transcendental.expInterval (RatInterval.point exponent) s.fuel)

/-- The complex rectangle obtained from a real Gaussian quadrature node by
adjoining the point interval at zero as imaginary coordinate. -/
def normalDensityComplexNode (q : ℚ) (s : NormalCDFSchedule) (k : ℕ) :
    ComplexRatInterval :=
  ⟨normalDensityNode q s k, RatInterval.point 0⟩

/-- For a nonnegative rational endpoint, the computed interval encloses the
integral of the standard-normal density from zero to that endpoint. -/
def nonnegativeNormalIntegralInterval (q : ℚ) (hq : 0 ≤ q)
    (s : NormalCDFSchedule) : RatInterval :=
  (CircleMesh.integralEnclosure
    (normalDensityComplexNode q s) (q ^ 3) (pow_nonneg hq 3)
    s.mesh s.mesh_pos).re

/-- The internally computed rational enclosure of the standard-normal CDF at
any rational endpoint, using symmetry for negative endpoints. -/
def normalCDFInterval (q : ℚ) (s : NormalCDFSchedule) : RatInterval :=
  let positive := (RatInterval.point (1 / 2)).add
    (nonnegativeNormalIntegralInterval |q| (abs_nonneg q) s)
  if 0 ≤ q then positive else (RatInterval.point 1).sub positive

/-- A standard-normal CDF certificate consists of a checked internal schedule,
a caller-facing rational interval, and an exact proof that the internally
computed interval refines the caller-facing one. -/
structure NormalCDFCertificate (q : ℚ) where
  /-- Internal exact-arithmetic evaluation schedule. -/
  schedule : NormalCDFSchedule
  /-- Rational interval reported in the caller's endpoint table. -/
  enclosure : RatInterval
  /-- Exact rational refinement check connecting the reported interval to the evaluator. -/
  checked : (normalCDFInterval q schedule).Subinterval enclosure

/-- The executable density-scale interval contains the mathematical constant
`1 / sqrt (2π)`. -/
theorem normalDensityScaleInterval_sound (s : NormalCDFSchedule) :
    (normalDensityScaleInterval s).Contains (1 / Real.sqrt (2 * Real.pi)) := by
  dsimp [normalDensityScaleInterval]
  rw [one_div]
  apply RatInterval.inv_sound s.sqrt_away
  apply RatInterval.sqrtInterval_sound s.twoPi_nonneg
  simpa [twoPiInterval] using RatInterval.mul_sound (RatInterval.point_sound 2)
    (Complex.Transcendental.piInterval_sound s.fuel)

/-- Every computed Gaussian quadrature node contains the corresponding value
of the rescaled standard-normal density. -/
theorem normalDensityNode_sound (q : ℚ) (hq : 0 ≤ q)
    (s : NormalCDFSchedule) (k : ℕ) :
    (normalDensityNode q s k).Contains
      ((q : ℝ) * Causalean.Mathlib.stdNormalPDF
        ((q : ℝ) * CircleMesh.meshPoint s.mesh k)) := by
  have hscale := normalDensityScaleInterval_sound s
  have hexp := Transcendental.expInterval_sound
    (RatInterval.point_sound (-(q * k / s.mesh) ^ 2 / 2)) s.fuel
  have h := RatInterval.mul_sound
    (RatInterval.mul_sound (RatInterval.point_sound q) hscale) hexp
  convert h using 1
  all_goals simp [normalDensityNode, Causalean.Mathlib.stdNormalPDF,
    ProbabilityTheory.gaussianPDFReal, CircleMesh.meshPoint]
  all_goals ring

/-- The rescaled standard-normal density on the unit interval is Lipschitz
with the exact rational constant `q³` for every nonnegative rational `q`. -/
theorem rescaledNormalDensity_lipschitz (q : ℚ) (hq : 0 ≤ q) :
    ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |(q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u) -
          (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * v)|
        ≤ (q ^ 3 : ℚ) * |u - v| := by
  let F : ℝ → ℝ := fun x =>
    (q : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-((q : ℝ) * x) ^ 2 / 2))
  have hF (x : ℝ) : F x =
      (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * x) := by
    simp [F, Causalean.Mathlib.stdNormalPDF,
      ProbabilityTheory.gaussianPDFReal]
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hscale_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hscale_le_one : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.one_le_sqrt]
      nlinarith [Real.pi_gt_three]
    exact (inv_le_one₀ (by positivity)).2 hsqrt
  have hderiv (x : ℝ) : HasDerivAt F
      (-((q : ℝ) ^ 3) * (Real.sqrt (2 * Real.pi))⁻¹ * x *
        Real.exp (-((q : ℝ) * x) ^ 2 / 2)) x := by
    have hi : HasDerivAt (fun y : ℝ => -((q : ℝ) * y) ^ 2 / 2)
        (-((q : ℝ) ^ 2) * x) x := by
      convert (((hasDerivAt_id x).const_mul (q : ℝ)).pow 2).neg.div_const 2 using 1 <;>
        try rfl
      all_goals simp only [id_eq]
      all_goals ring
    dsimp [F]
    convert ((hi.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).const_mul (q : ℝ)) using 1 <;>
      try rfl
    all_goals ring
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖-((q : ℝ) ^ 3) * (Real.sqrt (2 * Real.pi))⁻¹ * x *
          Real.exp (-((q : ℝ) * x) ^ 2 / 2)‖ ≤ (q : ℝ) ^ 3 := by
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (pow_nonneg hqR 3),
      abs_of_nonneg hscale_nonneg, abs_of_nonneg hx0,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-((q : ℝ) * x) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
    calc
      (q : ℝ) ^ 3 * (Real.sqrt (2 * Real.pi))⁻¹ * x *
          Real.exp (-((q : ℝ) * x) ^ 2 / 2)
          ≤ (q : ℝ) ^ 3 * 1 * 1 * 1 := by
            gcongr
      _ = (q : ℝ) ^ 3 := by ring
  intro u hu v hv
  rw [← hF u, ← hF v]
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hderiv x).hasDerivWithinAt) hbound hu hv
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmv

/-- The nonnegative-endpoint quadrature interval contains the exact integral
of the standard-normal density from zero to the endpoint. -/
theorem nonnegativeNormalIntegralInterval_sound (q : ℚ) (hq : 0 ≤ q)
    (s : NormalCDFSchedule) :
    (nonnegativeNormalIntegralInterval q hq s).Contains
      (∫ u in (0 : ℝ)..1,
        (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u)) := by
  let f : ℝ → ℝ := fun u =>
    (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u)
  have hquad := CircleMesh.integralEnclosure_sound
    (g := fun u => (f u : ℂ)) (nodes := normalDensityComplexNode q s)
    (pow_nonneg hq 3) s.mesh_pos
    (fun u hu v hv => by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [f] using rescaledNormalDensity_lipschitz q hq u hu v hv)
    (fun k hk => by
      constructor
      · simpa [normalDensityComplexNode, f] using normalDensityNode_sound q hq s k
      · simp [normalDensityComplexNode])
  have hre := hquad.1
  rw [intervalIntegral.integral_ofReal] at hre
  simpa [nonnegativeNormalIntegralInterval, f] using hre

/-- For a nonnegative real endpoint, its standard-normal CDF is one half plus
the integral of the rescaled density over the unit interval. -/
theorem stdNormalCDF_eq_half_add_rescaled_integral (q : ℚ) (hq : 0 ≤ q) :
    Causalean.Mathlib.stdNormalCDF (q : ℝ) =
      (1 / 2 : ℝ) + ∫ u in (0 : ℝ)..1,
        (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u) := by
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hzero : Causalean.Mathlib.stdNormalCDF 0 = (1 / 2 : ℝ) := by
    have hsym := Causalean.Mathlib.stdNormalCDF_neg 0
    norm_num at hsym ⊢
    linarith
  have hmeasure : (ProbabilityTheory.gaussianReal 0 1) (Ioc 0 (q : ℝ)) =
      ENNReal.ofReal (Causalean.Mathlib.stdNormalCDF (q : ℝ) -
        Causalean.Mathlib.stdNormalCDF 0) := by
    calc
      (ProbabilityTheory.gaussianReal 0 1) (Ioc 0 (q : ℝ)) =
          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)).measure
            (Ioc 0 (q : ℝ)) := by
              rw [ProbabilityTheory.measure_cdf]
      _ = ENNReal.ofReal
          (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (q : ℝ) -
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 0) := by
              rw [StieltjesFunction.measure_Ioc]
      _ = ENNReal.ofReal (Causalean.Mathlib.stdNormalCDF (q : ℝ) -
          Causalean.Mathlib.stdNormalCDF 0) := by
            rfl
  have hgauss : (ProbabilityTheory.gaussianReal 0 1) (Ioc 0 (q : ℝ)) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..(q : ℝ),
        Causalean.Mathlib.stdNormalPDF x) := by
    rw [ProbabilityTheory.gaussianReal_apply_eq_integral (μ := 0) (v := 1)
      one_ne_zero]
    simp [intervalIntegral.integral_of_le hqR,
      Causalean.Mathlib.stdNormalPDF]
  have hdiff_nonneg : 0 ≤ Causalean.Mathlib.stdNormalCDF (q : ℝ) -
      Causalean.Mathlib.stdNormalCDF 0 := sub_nonneg.mpr
    (Causalean.Mathlib.stdNormalCDF_monotone hqR)
  have hint_nonneg : 0 ≤ ∫ x in (0 : ℝ)..(q : ℝ),
      Causalean.Mathlib.stdNormalPDF x := by
    rw [intervalIntegral.integral_of_le hqR]
    exact integral_nonneg (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)
  have hdiff : Causalean.Mathlib.stdNormalCDF (q : ℝ) -
      Causalean.Mathlib.stdNormalCDF 0 =
        ∫ x in (0 : ℝ)..(q : ℝ), Causalean.Mathlib.stdNormalPDF x := by
    rw [← ENNReal.ofReal_eq_ofReal_iff hdiff_nonneg hint_nonneg]
    exact hmeasure.symm.trans hgauss
  have hsubst : (∫ u in (0 : ℝ)..1,
      (q : ℝ) * Causalean.Mathlib.stdNormalPDF ((q : ℝ) * u)) =
      ∫ x in (0 : ℝ)..(q : ℝ), Causalean.Mathlib.stdNormalPDF x := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.mul_integral_comp_mul_left]
    simp
  rw [hsubst, ← hdiff, hzero]
  ring

/-- The internally evaluated interval soundly contains the standard-normal CDF
at its rational endpoint; no external numerical approximation is assumed. -/
theorem normalCDFInterval_sound (q : ℚ) (s : NormalCDFSchedule) :
    (normalCDFInterval q s).Contains
      (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  by_cases hq : 0 ≤ q
  · have hint := nonnegativeNormalIntegralInterval_sound q hq s
    have hadd := RatInterval.add_sound (RatInterval.point_sound (1 / 2)) hint
    simp only [normalCDFInterval, if_pos hq]
    rw [stdNormalCDF_eq_half_add_rescaled_integral q hq]
    simpa [abs_of_nonneg hq] using hadd
  · have hqabs : 0 ≤ |q| := abs_nonneg q
    have hint := nonnegativeNormalIntegralInterval_sound |q| hqabs s
    have hadd := RatInterval.add_sound (RatInterval.point_sound (1 / 2)) hint
    have hpositive : ((RatInterval.point (1 / 2)).add
        (nonnegativeNormalIntegralInterval |q| hqabs s)).Contains
        (Causalean.Mathlib.stdNormalCDF (|q| : ℚ)) := by
      rw [stdNormalCDF_eq_half_add_rescaled_integral |q| hqabs]
      convert hadd using 1 <;> norm_num
    have hsub := RatInterval.sub_sound (RatInterval.point_sound 1) hpositive
    have hq_nonpos : q ≤ 0 := le_of_not_ge hq
    have hneg : (q : ℝ) = -(|q| : ℚ) := by
      have hnegQ : q = -|q| := by rw [abs_of_nonpos hq_nonpos]; simp
      exact_mod_cast hnegQ
    rw [hneg, Causalean.Mathlib.stdNormalCDF_neg]
    simpa [normalCDFInterval, hq] using hsub

/-- Given [a checked rational certificate at a rational endpoint](hyp:c), [the certificate's reported interval contains the true standard-normal cumulative probability at that endpoint](goal). -/
theorem NormalCDFCertificate.sound {q : ℚ} (c : NormalCDFCertificate q) :
    c.enclosure.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  exact (normalCDFInterval_sound q c.schedule).mono c.checked

/-- Subtracting two checked CDF enclosures contains the corresponding
difference of standard-normal CDF values, as used for threshold-cell probabilities. -/
theorem normalCDFDifference_sound {a b : ℚ}
    (ca : NormalCDFCertificate a) (cb : NormalCDFCertificate b) :
    (cb.enclosure.sub ca.enclosure).Contains
      (Causalean.Mathlib.stdNormalCDF (b : ℝ) -
        Causalean.Mathlib.stdNormalCDF (a : ℝ)) := by
  exact RatInterval.sub_sound cb.sound ca.sound

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
