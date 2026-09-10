import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Horn diagnostics -/

open MeasureTheory Set
open scoped ENNReal Topology Interval

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

-- @env: S4
variable (κ h0 α : ℝ)
  -- @realizes \alpha(positive severe-thinning exponent)

/-- Standing domain for the severe-thinning exponent. -/
def AdmissibleSeverityExponent (α : ℝ) : Prop := 0 < α
  -- @realizes \alpha(alpha>0)

-- @node: def:polynomial-horn
/-- The polynomial horn with vertical thickness `u^(κ-1)`. -/
def polynomialHorn (κ h0 : ℝ) : Set Score :=
  {z | 0 < z 0 ∧ z 0 < h0 ∧ |z 1| ≤ z 0 ^ (κ - 1)}
  -- @realizes \mathsf H_{\kappa}({0<u<h₀, |v|≤u^(κ-1)})

-- @node: def:exponential-modulus
/-- The exponentially thin horn's local mass modulus. -/
noncomputable def exponentialModulus (α h0 h : ℝ) : ℝ :=
  if 0 < α ∧ 0 < h ∧ h ≤ h0 then
    ∫ u in (0 : ℝ)..h, 2 * Real.exp (-(u ^ (-α)))
  else 0
  -- @realizes m_{\alpha}(integral 0..h of 2 exp(-u^-alpha))

-- @node: scoreToPair
/-- The volume-preserving coordinate equivalence from the Euclidean plane to
an ordinary pair of real coordinates. -/
noncomputable def scoreToPair : Score ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

-- @node: polynomialRegion_volume
/-- The exact volume of a symmetric region with vertical radius `c * u ^ r`. -/
lemma polynomialRegion_volume (r a c : ℝ) (hr : -1 < r) (ha : 0 < a) (hc : 0 < c) :
    volume (regionBetween (fun u : ℝ => -(c * u ^ r))
      (fun u => c * u ^ r) (Ioo 0 a)) =
      ENNReal.ofReal (2 * c * a ^ (r + 1) / (r + 1)) := by
  have hp : IntegrableOn (fun u : ℝ => u ^ r) (Ioo 0 a) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ha).2 hr
  have hf : IntegrableOn (fun u : ℝ => -(c * u ^ r)) (Ioo 0 a) volume :=
    (hp.const_mul c).neg
  have hg : IntegrableOn (fun u : ℝ => c * u ^ r) (Ioo 0 a) volume := hp.const_mul c
  have hfg : ∀ u ∈ Ioo (0 : ℝ) a, -(c * u ^ r) ≤ c * u ^ r := by
    intro u hu
    have : 0 ≤ u ^ r := Real.rpow_nonneg hu.1.le _
    nlinarith
  rw [Measure.volume_eq_prod,
    volume_regionBetween_eq_integral hf hg measurableSet_Ioo hfg]
  congr 1
  rw [show (∫ u in Ioo (0 : ℝ) a, ((fun u => c * u ^ r) -
      (fun u => -(c * u ^ r))) u) = ∫ u in Ioo (0 : ℝ) a, 2 * c * u ^ r by
        apply integral_congr_ae
        filter_upwards with u
        simp [Pi.sub_apply]
        ring]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr)]
  have hr1 : r + 1 ≠ 0 := by linarith
  rw [Real.zero_rpow hr1]
  field_simp
  ring

-- @node: lem:polynomial-horn-mass
/-- The planar mass of the polynomial horn in a small ball has exponent `κ`,
not `κ-1`. -/
lemma polynomialHorn_measure_asymp (κ h0 : ℝ) (hκ : 2 < κ) (hh0 : 0 < h0) :
    ∃ cκ Cκ hstar : ℝ, 0 < cκ ∧ cκ < Cκ ∧ 0 < hstar ∧
      ∀ h, 0 < h → h ≤ hstar →
        ENNReal.ofReal (cκ * h ^ κ) ≤ volume (polynomialHorn κ h0 ∩ Metric.closedBall 0 h) ∧
        volume (polynomialHorn κ h0 ∩ Metric.closedBall 0 h) ≤
          ENNReal.ofReal (Cκ * h ^ κ) := by
  let cκ : ℝ := (2 : ℝ)⁻¹ ^ κ / κ
  let Cκ : ℝ := 4 * 2 ^ κ / κ
  let hstar : ℝ := min 1 h0
  have hκ0 : 0 < κ := by linarith
  have hc : 0 < cκ := by positivity
  have hC : 0 < Cκ := by positivity
  have hcC : cκ < Cκ := by
    dsimp [cκ, Cκ]
    have hp : (0 : ℝ) < 2 ^ κ := Real.rpow_pos_of_pos (by norm_num) _
    have hi : (0 : ℝ) < (2 : ℝ)⁻¹ ^ κ := Real.rpow_pos_of_pos (by positivity) _
    have hbase : (2 : ℝ)⁻¹ < 2 := by norm_num
    have hpow : (2 : ℝ)⁻¹ ^ κ < 2 ^ κ :=
      Real.rpow_lt_rpow (by positivity) hbase hκ0
    have hlt : (2 : ℝ)⁻¹ ^ κ < 4 * 2 ^ κ := by nlinarith
    exact (div_lt_div_iff_of_pos_right hκ0).2 hlt
  refine ⟨cκ, Cκ, hstar, hc, hcC, lt_min zero_lt_one hh0, ?_⟩
  intro h hh hhstar
  have hh1 : h ≤ 1 := hhstar.trans (min_le_left _ _)
  have hhh0 : h ≤ h0 := hhstar.trans (min_le_right _ _)
  let low : Set (ℝ × ℝ) := regionBetween
    (fun u : ℝ => -((2 : ℝ)⁻¹ * u ^ (κ - 1)))
    (fun u => (2 : ℝ)⁻¹ * u ^ (κ - 1)) (Ioo 0 (h / 2))
  let high : Set (ℝ × ℝ) := regionBetween
    (fun u : ℝ => -(2 * u ^ (κ - 1)))
    (fun u => 2 * u ^ (κ - 1)) (Ioo 0 (2 * h))
  have hmp : MeasurePreserving (scoreToPair : Score → ℝ × ℝ) volume volume :=
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have hvol (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
      volume (scoreToPair ⁻¹' s) = volume s := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable hs]
  have hlow_meas : MeasurableSet low := by
    exact measurableSet_regionBetween (by fun_prop) (by fun_prop) measurableSet_Ioo
  have hhigh_meas : MeasurableSet high := by
    exact measurableSet_regionBetween (by fun_prop) (by fun_prop) measurableSet_Ioo
  have hlow : scoreToPair ⁻¹' low ⊆
      polynomialHorn κ h0 ∩ Metric.closedBall 0 h := by
    intro z hz
    change (z 0, z 1) ∈ low at hz
    rcases hz with ⟨hu, hv⟩
    have hu0 : 0 < z 0 := hu.1
    have huhalf : z 0 < h / 2 := hu.2
    have hu1 : z 0 ≤ 1 := by linarith
    have hrpow : z 0 ^ (κ - 1) ≤ z 0 :=
      Real.rpow_le_self_of_le_one hu0.le hu1 (by linarith)
    have hrpow0 : 0 ≤ z 0 ^ (κ - 1) := Real.rpow_nonneg hu0.le _
    have hvabs : |z 1| < (2 : ℝ)⁻¹ * z 0 ^ (κ - 1) := by
      rw [abs_lt]
      exact hv
    have hz1 : |z 1| < h / 4 := by
      have : (2 : ℝ)⁻¹ * z 0 ^ (κ - 1) ≤ z 0 / 2 := by nlinarith
      linarith
    constructor
    · exact ⟨hu0, by linarith, hvabs.le.trans (by
          have : (2 : ℝ)⁻¹ * z 0 ^ (κ - 1) ≤ z 0 ^ (κ - 1) := by nlinarith
          exact this)⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      rw [Real.sqrt_le_iff]
      constructor
      · exact hh.le
      · have hz1sq : (z 1) ^ 2 < (h / 4) ^ 2 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (z 1)]
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hhigh : polynomialHorn κ h0 ∩ Metric.closedBall 0 h ⊆
      scoreToPair ⁻¹' high := by
    intro z hz
    rcases hz with ⟨hzHorn, hzBall⟩
    change (z 0, z 1) ∈ high
    have hnorm : ‖z‖ ≤ h := by simpa [Metric.mem_closedBall, dist_zero_right] using hzBall
    have hcoord : z 0 ≤ ‖z‖ := by
      rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
      exact (Real.le_sqrt hzHorn.1.le (by positivity)).2 (by nlinarith [sq_nonneg (z 1)])
    constructor
    · exact ⟨hzHorn.1, by linarith⟩
    · rw [mem_Ioo]
      have hp0 : 0 ≤ z 0 ^ (κ - 1) := Real.rpow_nonneg hzHorn.1.le _
      have hp : 0 < z 0 ^ (κ - 1) := Real.rpow_pos_of_pos hzHorn.1 _
      have hzle : z 1 ≤ z 0 ^ (κ - 1) := (le_abs_self _).trans hzHorn.2.2
      have hneg : -(z 0 ^ (κ - 1)) ≤ z 1 := by
        nlinarith [neg_le_abs (z 1), hzHorn.2.2]
      constructor <;> nlinarith
  constructor
  · calc
      ENNReal.ofReal (cκ * h ^ κ) = volume low := by
        rw [polynomialRegion_volume (κ - 1) (h / 2) (2 : ℝ)⁻¹
          (by linarith) (by positivity) (by positivity)]
        congr 1
        dsimp [cκ]
        rw [show κ - 1 + 1 = κ by ring]
        rw [show h / 2 = h * (2 : ℝ)⁻¹ by ring,
          Real.mul_rpow hh.le (by positivity)]
        field_simp
      _ = volume (scoreToPair ⁻¹' low) := (hvol low hlow_meas).symm
      _ ≤ _ := measure_mono hlow
  · calc
      volume (polynomialHorn κ h0 ∩ Metric.closedBall 0 h)
          ≤ volume (scoreToPair ⁻¹' high) := measure_mono hhigh
      _ = volume high := hvol high hhigh_meas
      _ = ENNReal.ofReal (Cκ * h ^ κ) := by
        rw [polynomialRegion_volume (κ - 1) (2 * h) 2
          (by linarith) (by positivity) (by positivity)]
        congr 1
        dsimp [Cκ]
        rw [show κ - 1 + 1 = κ by ring,
          Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hh.le]
        field_simp
        ring

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
