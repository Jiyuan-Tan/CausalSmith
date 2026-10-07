module
public import Causalean.Stat.CLT.BerryEsseen.CDFSandwich
public import Mathlib.Probability.CDF

/-! # CDF smoothing with an abstract probability kernel

This comparison isolates the concentration needed from a smoothing kernel.
It permits a sharper band-limited kernel in the Gaussian smoothing theorem.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- Let K be [an integrable](hyp:hK) [nonnegative](hyp:hKnonneg)
[probability density](hyp:hKmass) that [puts mass at most q outside the
open interval (−a, a)](hyp:hKtail), where [a ≥ 0](hyp:ha) and
[q < 1/2](hyp:hq). If [the reference law ν assigns every interval at
most L times its length, for a nonnegative constant L](hyp:hL,hν) and
[the CDF difference of μ and ν, convolved with K, is bounded in absolute
value at every point by a constant B](hyp:hsmooth),
then [the unsmoothed CDF difference is bounded in absolute value by
(B + 2aL)/(1 − 2q) at every point](goal). -/
theorem cdf_general_kernel_sandwich
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ → ℝ) (a q L B : ℝ)
    (ha : 0 ≤ a) (hq : q < 1 / 2)
    (hL : 0 ≤ L)
    (hK : Integrable K) (hKnonneg : ∀ y, 0 ≤ K y)
    (hKmass : ∫ y, K y = 1)
    (hKtail : ∫ y in {y : ℝ | a ≤ |y|}, K y ≤ q)
    (hν : ∀ u v : ℝ, u ≤ v →
      (ν (Set.Ioc u v)).toReal ≤ L * (v - u))
    (hsmooth : ∀ z : ℝ,
      |∫ y : ℝ,
        ((μ (Set.Iic (z - y))).toReal -
          (ν (Set.Iic (z - y))).toReal) * K y| ≤ B)
    (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal| ≤
      (B + 2 * a * L) / (1 - 2 * q) := by
  let H : ℝ → ℝ := fun z =>
    (μ (Set.Iic z)).toReal - (ν (Set.Iic z)).toReal
  let s : Set ℝ := {y | a ≤ |y|}
  let D : ℝ := sSup (Set.range fun z : ℝ => |H z|)
  have hs : MeasurableSet s := measurableSet_le measurable_const measurable_abs
  have ht : ∫ y in s, K y ≤ q := hKtail
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
      H z ≤ B + 2 * a * L + 2 * q * D := by
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
    have h := kernel_sandwich_step K H s hs hK hHint hKnonneg hKmass q ht
      D (2 * a * L) hD hc hDb z (z + a) hp
    have hb := (le_abs_self (∫ y, H ((z + a) - y) * K y)).trans (hsmooth (z + a))
    dsimp [H] at hb
    linarith
  have hneg (z : ℝ) :
      -H z ≤ B + 2 * a * L + 2 * q * D := by
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
    have h := kernel_sandwich_step K (fun w => -H w) s hs hK hNint hKnonneg hKmass q ht
      D (2 * a * L) hD hc hnb z (z - a) hp
    have hni : (∫ y, (-H ((z - a) - y)) * K y) =
        -(∫ y, H ((z - a) - y) * K y) := by
      rw [← integral_neg]
      congr 1
      ext y
      ring
    rw [hni] at h
    have hb := (neg_le_abs (∫ y, H ((z - a) - y) * K y)).trans (hsmooth (z - a))
    dsimp [H] at hb
    linarith
  have hDtwo : D ≤ B + 2 * a * L + 2 * q * D := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact abs_le.mpr ⟨by linarith [hneg z], by linarith [hpos z]⟩
  have hx := hDb x
  have hden : 0 < 1 - 2 * q := by linarith
  have hnum : D * (1 - 2 * q) ≤ B + 2 * a * L := by nlinarith [hDtwo]
  have hfinal : D ≤ (B + 2 * a * L) / (1 - 2 * q) :=
    (le_div_iff₀ hden).2 hnum
  exact hx.trans hfinal

end Causalean.Stat.CLT.BerryEsseen
