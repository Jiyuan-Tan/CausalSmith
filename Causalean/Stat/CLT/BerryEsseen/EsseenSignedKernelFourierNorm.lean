module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernel
public import Causalean.Stat.CLT.BerryEsseen.EsseenSinc4SecondMoment

/-! # Fourier norm bound for the signed sinc-fourth kernel

The absolute first moment of the shifted density bounds the magnitude
of every Fourier integral of the signed kernel.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- [The Fourier integral of the signed sinc-fourth comparison kernel has
magnitude at most one at every real frequency](goal). -/
theorem esseenSignedSinc4Kernel_fourier_norm_le_one (t : ℝ) :
    ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
      (esseenSignedSinc4Kernel y : ℂ)‖ ≤ 1 := by
  /- Bound by the L¹ norm. With x = -y, use
  |x|/8 ≤ (x² + 16)/64 and the shifted moments: the kernel has mass 1,
  first moment 4, and second moment 28, giving L¹ norm ≤ 44/64 < 1. -/
  let q : ℝ → ℝ := sinc4Kernel 1
  have hq : Integrable q volume := sinc4Kernel_integrable 1 (by norm_num)
  have hq0 : (∫ x : ℝ, q x) = 1 := sinc4Kernel_integral_eq_one 1 (by norm_num)
  have hq1 := sinc4Kernel_unit_first_moment
  have hq2 := sinc4Kernel_unit_second_moment
  have hpoly : Integrable (fun x : ℝ => (x + 4) ^ 2 * q x) volume := by
    have hi := (hq2.1.add (hq1.1.const_mul 8)).add (hq.const_mul 16)
    apply hi.congr
    filter_upwards with x
    dsimp [q]
    ring
  have hpoly_val : (∫ x : ℝ, (x + 4) ^ 2 * q x) = 28 := by
    have hp (x : ℝ) : (x + 4) ^ 2 * q x =
        x ^ 2 * q x + 8 * (x * q x) + 16 * q x := by ring
    simp_rw [hp]
    have ha := integral_add (hq2.1.add (hq1.1.const_mul 8)) (hq.const_mul 16)
    have hb := integral_add hq2.1 (hq1.1.const_mul 8)
    simp only [Pi.add_apply] at ha hb
    rw [ha, hb, integral_const_mul, integral_const_mul]
    rw [hq2.2, hq1.2, hq0]
    norm_num
  have hshift : (∫ y : ℝ, y ^ 2 * q (-y - 4)) = 28 := by
    have hn := integral_neg_eq_self (fun x : ℝ => x ^ 2 * q (x - 4)) volume
    have ha := integral_add_right_eq_self (μ := volume)
      (fun x : ℝ => (x + 4) ^ 2 * q x) (-4)
    have hn' : (∫ y : ℝ, y ^ 2 * q (-y - 4)) =
        ∫ x : ℝ, x ^ 2 * q (x - 4) := by
      simpa only [even_two, Even.neg_pow] using hn
    have ha' : (∫ x : ℝ, x ^ 2 * q (x - 4)) =
        ∫ x : ℝ, (x + 4) ^ 2 * q x := by
      simpa [sub_eq_add_neg, add_assoc] using ha
    rw [hn', ha', hpoly_val]
  have hshift_int : Integrable (fun y : ℝ => y ^ 2 * q (-y - 4)) volume := by
    have ha := hpoly.comp_add_left (-4)
    have hn := ha.comp_neg
    convert hn using 1
    ext y
    ring_nf
  have hqshift : Integrable (fun y : ℝ => q (-y - 4)) volume := by
    convert (hq.comp_add_left (-4)).comp_neg using 1
    ext y
    ring_nf
  have hqshift_val : (∫ y : ℝ, q (-y - 4)) = 1 := by
    rw [show (∫ y : ℝ, q (-y - 4)) = (∫ x : ℝ, q (x - 4)) from by
      simpa only [neg_sub] using
        (integral_neg_eq_self (fun x : ℝ => q (x - 4)) volume),
      show (∫ x : ℝ, q (x - 4)) = (∫ x : ℝ, q x) from by
        simpa [sub_eq_add_neg] using (integral_add_right_eq_self q (-4)), hq0]
  have hbound (y : ℝ) : |esseenSignedSinc4Kernel y| ≤
      (y ^ 2 + 16) / 64 * q (-y - 4) := by
    have hqnonneg : 0 ≤ q (-y - 4) := sinc4Kernel_nonneg 1 (by norm_num) _
    have hsq : 8 * |y| ≤ y ^ 2 + 16 := by
      nlinarith [sq_nonneg (|y| - 4), sq_abs y]
    unfold esseenSignedSinc4Kernel
    rw [abs_mul, abs_div, abs_neg, abs_of_nonneg hqnonneg]
    norm_num at *
    nlinarith
  have hmajor : Integrable (fun y : ℝ => (y ^ 2 + 16) / 64 * q (-y - 4)) volume := by
    have hi := (hshift_int.add (hqshift.const_mul 16)).const_mul (1 / 64 : ℝ)
    convert hi using 1
    ext y
    dsimp
    ring
  have hK : Integrable esseenSignedSinc4Kernel volume :=
    esseenSignedSinc4Kernel_integrable_continuous.1
  have hKbound : (∫ y : ℝ, |esseenSignedSinc4Kernel y|) ≤ 1 := by
    calc
      _ ≤ ∫ y : ℝ, (y ^ 2 + 16) / 64 * q (-y - 4) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
          hmajor (Filter.Eventually.of_forall hbound)
      _ = (28 + 16) / 64 := by
        have hp (y : ℝ) : (y ^ 2 + 16) / 64 * q (-y - 4) =
            (1 / 64 : ℝ) * (y ^ 2 * q (-y - 4) + 16 * q (-y - 4)) := by ring
        simp_rw [hp]
        rw [integral_const_mul, integral_add hshift_int (hqshift.const_mul 16),
          integral_const_mul, hshift, hqshift_val]
        ring
      _ ≤ 1 := by norm_num
  calc
    _ ≤ ∫ y : ℝ, ‖Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
        (esseenSignedSinc4Kernel y : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, |esseenSignedSinc4Kernel y| := by
      congr 1
      ext y
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ 1 := hKbound

end Causalean.Stat.CLT.BerryEsseen
