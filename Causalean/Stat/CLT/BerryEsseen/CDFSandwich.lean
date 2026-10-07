module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceModulus
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernelTail
public import Mathlib.Probability.CDF
public import Mathlib.Probability.CentralLimitTheorem

/-! # A distribution-function sandwich for sinc smoothing

This module isolates the order-theoretic part of the Esseen smoothing
argument. A probability kernel with a controlled tail compares an original
CDF difference with its smoothed version against a Lipschitz reference CDF.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- A probability kernel transfers a one-sided comparison outside a tail set
to an integral comparison, with tail loss controlled by the uniform bound. -/
theorem kernel_sandwich_step
    (K G : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hK : Integrable K) (hG : ∀ z, Integrable (fun y => G (z - y) * K y))
    (hkn : ∀ y, 0 ≤ K y) (hki : ∫ y, K y = 1)
    (q : ℝ) (ht : ∫ y in s, K y ≤ q)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hGb : ∀ y, |G y| ≤ D)
    (x z : ℝ) (hp : ∀ y ∉ s, G x ≤ G (z - y) + c) :
    G x ≤ (∫ y, G (z - y) * K y) + c + 2 * q * D := by
  have hi : Integrable (s.indicator (fun y => 2 * D * K y)) :=
    (hK.const_mul (2 * D)).integrableOn.integrable_indicator hs
  have hpt (y : ℝ) : G x * K y ≤ (G (z - y) + c) * K y +
      s.indicator (fun y => 2 * D * K y) y := by
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      have h1 := le_abs_self (G x)
      have h2 := neg_abs_le (G (z - y))
      have h3 := hGb x
      have h4 := hGb (z - y)
      nlinarith [hkn y]
    · rw [Set.indicator_of_notMem hy]
      nlinarith [hp y hy, hkn y]
  have hl : Integrable (fun y => G x * K y) := hK.const_mul _
  have hmidint : Integrable (fun y => (G (z - y) + c) * K y) := by
    have heq : (fun y => (G (z - y) + c) * K y) =
        (fun y => G (z - y) * K y) + (fun y => c * K y) := by
      funext y
      simp only [Pi.add_apply, add_mul]
    rw [heq]
    exact (hG z).add (hK.const_mul c)
  have hr := hmidint.add hi
  have hm := integral_mono hl hr hpt
  have htail : (∫ y, s.indicator (fun y => 2 * D * K y) y) ≤ 2 * q * D := by
    rw [integral_indicator hs, integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * D)]
  have hmiddle : (∫ y, (G (z - y) + c) * K y) =
      (∫ y, G (z - y) * K y) + c := by
    calc
      _ = ∫ y, G (z - y) * K y + c * K y := by
        congr 1
        ext y
        ring
      _ = (∫ y, G (z - y) * K y) + ∫ y, c * K y :=
        integral_add (hG z) (hK.const_mul c)
      _ = _ := by rw [integral_const_mul, hki, mul_one]
  have hsplit : (∫ y, (G (z - y) + c) * K y +
      s.indicator (fun y => 2 * D * K y) y) =
      (∫ y, (G (z - y) + c) * K y) +
      ∫ y, s.indicator (fun y => 2 * D * K y) y := integral_add hmidint hi
  have hm' : (∫ y, G x * K y) ≤
      (∫ y, (G (z - y) + c) * K y) +
      ∫ y, s.indicator (fun y => 2 * D * K y) y := by
    simpa only [Pi.add_apply, hsplit] using hm
  rw [integral_const_mul, hki, mul_one, hmiddle] at hm'
  linarith

/-- If the reference law assigns every interval at most its length times
`L`, and the sinc-smoothed CDF discrepancy is everywhere at most `B`, then
the unsmoothed CDF discrepancy is at most `2 B + 24 L / T`. -/
theorem sinc4_cdf_sandwich
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T L B : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (hν : ∀ a b : ℝ, a ≤ b →
      (ν (Set.Ioc a b)).toReal ≤ L * (b - a))
    (hsmooth : ∀ z : ℝ,
      |∫ y : ℝ,
        ((μ (Set.Iic (z - y))).toReal -
          (ν (Set.Iic (z - y))).toReal) * sinc4Kernel T y| ≤ B)
    (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal| ≤
      2 * B + 24 * L / T := by
  let H : ℝ → ℝ := fun z =>
    (μ (Set.Iic z)).toReal - (ν (Set.Iic z)).toReal
  let K : ℝ → ℝ := sinc4Kernel T
  let a : ℝ := 6 / T
  let s : Set ℝ := {y | a ≤ |y|}
  let D : ℝ := sSup (Set.range fun z : ℝ => |H z|)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : MeasurableSet s := measurableSet_le measurable_const measurable_abs
  have hK : Integrable K := sinc4Kernel_integrable T hT
  have hkn : ∀ y, 0 ≤ K y := sinc4Kernel_nonneg T hT
  have hki : ∫ y, K y = 1 := sinc4Kernel_integral_eq_one T hT
  have ht : ∫ y in s, K y ≤ (1 / 4 : ℝ) :=
    sinc4Kernel_tail_le_quarter T hT
  have hCDF (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      Measurable (fun z : ℝ => (ρ (Set.Iic z)).toReal) := by
    have hm := (ProbabilityTheory.monotone_cdf ρ).measurable
    convert hm using 1
    ext z
    exact (ProbabilityTheory.cdf_eq_real ρ z).symm
  have hHm : Measurable H := (hCDF μ).sub (hCDF ν)
  have hHone (z : ℝ) : |H z| ≤ 1 := by
    have hμ0 : 0 ≤ (μ (Set.Iic z)).toReal := ENNReal.toReal_nonneg
    have hν0 : 0 ≤ (ν (Set.Iic z)).toReal := ENNReal.toReal_nonneg
    have hμ1 : (μ (Set.Iic z)).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono (measure_ne_top μ _)
        (measure_mono (Set.subset_univ (Set.Iic z)))
      simpa using h
    have hν1 : (ν (Set.Iic z)).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono (measure_ne_top ν _)
        (measure_mono (Set.subset_univ (Set.Iic z)))
      simpa using h
    dsimp [H]
    rw [abs_le]
    constructor <;> linarith
  have hbdd : BddAbove (Set.range fun z : ℝ => |H z|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hHone z
  have hD : 0 ≤ D := by
    have h := le_csSup hbdd (Set.mem_range_self x)
    exact le_trans (abs_nonneg _) h
  have hDb (z : ℝ) : |H z| ≤ D :=
    le_csSup hbdd (Set.mem_range_self z)
  have hD1 : D ≤ 1 :=
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨z, rfl⟩; exact hHone z)
  have hHint (z : ℝ) : Integrable (fun y => H (z - y) * K y) := by
    have hm : AEStronglyMeasurable (fun y => H (z - y)) volume :=
      (hHm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hb : ∀ᵐ y : ℝ ∂volume, ‖H (z - y)‖ ≤ (1 : ℝ) := by
      filter_upwards with y
      simpa only [Real.norm_eq_abs] using hHone (z - y)
    have heq : (fun y => H (z - y) * K y) =
        (fun y => K y * H (z - y)) := by
      funext y
      ring
    rw [heq]
    exact hK.mul_bdd hm hb
  have hNint (z : ℝ) : Integrable (fun y => (-H (z - y)) * K y) := by
    have heq : (fun y => (-H (z - y)) * K y) =
        -(fun y => H (z - y) * K y) := by
      funext y
      simp only [Pi.neg_apply, neg_mul]
    rw [heq]
    exact (hHint z).neg
  have hc : 0 ≤ 2 * a * L := by positivity
  have hpos (z : ℝ) :
      H z ≤ B + 2 * a * L + D / 2 := by
    have hp (y : ℝ) (hy : y ∉ s) :
        H z ≤ H ((z + a) - y) + 2 * a * L := by
      have hy' : |y| < a := lt_of_not_ge hy
      have hzy : z ≤ (z + a) - y := by linarith [le_abs_self y]
      have hd : ((z + a) - y) - z ≤ 2 * a := by
        linarith [neg_abs_le y]
      have hm := cdf_difference_one_sided_modulus μ ν L hν z
        ((z + a) - y) hzy
      have hmul := mul_le_mul_of_nonneg_left hd hL
      dsimp [H]
      linarith
    have h := kernel_sandwich_step K H s hs hK hHint hkn hki (1 / 4) ht
      D (2 * a * L) hD hc hDb z (z + a) hp
    have hb := (le_abs_self (∫ y, H ((z + a) - y) * K y)).trans (hsmooth (z + a))
    dsimp [H, K] at hb
    linarith
  have hneg (z : ℝ) :
      -H z ≤ B + 2 * a * L + D / 2 := by
    have hp (y : ℝ) (hy : y ∉ s) :
        -H z ≤ -H ((z - a) - y) + 2 * a * L := by
      have hy' : |y| < a := lt_of_not_ge hy
      have hzy : (z - a) - y ≤ z := by linarith [neg_abs_le y]
      have hd : z - ((z - a) - y) ≤ 2 * a := by
        linarith [le_abs_self y]
      have hm := cdf_difference_one_sided_modulus μ ν L hν
        ((z - a) - y) z hzy
      have hmul := mul_le_mul_of_nonneg_left hd hL
      dsimp [H]
      linarith
    have hnb (w : ℝ) : |(-H w)| ≤ D := by simpa using hDb w
    have h := kernel_sandwich_step K (fun w => -H w) s hs hK hNint hkn hki (1 / 4) ht
      D (2 * a * L) hD hc hnb z (z - a) hp
    have hni : (∫ y, (-H ((z - a) - y)) * K y) =
        -(∫ y, H ((z - a) - y) * K y) := by
      rw [← integral_neg]
      congr 1
      ext y
      ring
    rw [hni] at h
    have hb := (neg_le_abs (∫ y, H ((z - a) - y) * K y)).trans (hsmooth (z - a))
    dsimp [H, K] at hb
    linarith
  have hDtwo : D ≤ B + 2 * a * L + D / 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact abs_le.mpr ⟨by linarith [hneg z], by linarith [hpos z]⟩
  have hx := hDb x
  have hfinal : D ≤ 2 * B + 4 * a * L := by linarith
  dsimp [H] at hx
  have hconst : 4 * a * L = 24 * L / T := by
    dsimp [a]
    field_simp
    ring
  rw [← hconst]
  exact hx.trans hfinal

/-- For [real endpoints a ≤ b](hyp:hab), [the standard Gaussian gives the
interval `(a, b]` probability at most (b − a)/√(2π)](goal), the interval
length times the maximum of the Gaussian density. -/
theorem standardGaussian_interval_mass_le
    (a b : ℝ) (hab : a ≤ b) :
    ((gaussianReal 0 1) (Set.Ioc a b)).toReal ≤
      (b - a) / Real.sqrt (2 * Real.pi) := by
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (v := 1) one_ne_zero]
  have hnonneg : 0 ≤ ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  rw [ENNReal.toReal_ofReal hnonneg]
  rw [← intervalIntegral.integral_of_le hab]
  have hbound : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x
    rw [gaussianPDFReal]
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hs : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hexp hs)
  have hi : IntervalIntegrable (gaussianPDFReal 0 1) volume a b :=
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hc : IntervalIntegrable (fun _ : ℝ => (Real.sqrt (2 * Real.pi))⁻¹) volume a b :=
    intervalIntegrable_const
  calc
    ∫ x in a..b, gaussianPDFReal 0 1 x ≤
        ∫ x in a..b, (Real.sqrt (2 * Real.pi))⁻¹ :=
      intervalIntegral.integral_mono_on hab hi hc (fun x _ => hbound x)
    _ = (b - a) / Real.sqrt (2 * Real.pi) := by
      rw [intervalIntegral.integral_const]
      ring

end Causalean.Stat.CLT.BerryEsseen
