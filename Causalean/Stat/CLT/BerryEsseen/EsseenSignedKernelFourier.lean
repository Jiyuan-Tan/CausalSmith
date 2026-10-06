module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSignedKernel
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Fourier properties of the signed sinc-fourth kernel

The frequency support of this weighted kernel comes from differentiation
of the compactly supported transform of the unweighted sinc-fourth density.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory
open Filter

/-- [The Fourier integral of the signed sinc-fourth comparison kernel
vanishes](goal) at [every frequency t with |t| at least one](hyp:ht). -/
theorem esseenSignedSinc4Kernel_fourier_eq_zero
    (t : ℝ) (ht : 1 ≤ |t|) :
    (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
      (esseenSignedSinc4Kernel y : ℂ)) = 0 := by
  /- First prove the weighted unshifted transform vanishes at |t|>1:
  `Real.deriv_fourier` identifies it with the derivative of
  `sinc4Kernel_fourier_eq_zero` on an exterior neighborhood. Shift by four
  and reflect. At |t|=1 use continuity of the weighted transform, supplied
  by integrability from `esseenSignedSinc4Kernel_integrable_continuous`. -/
  let f : ℝ → ℂ := fun x => (sinc4Kernel 1 x : ℂ)
  let g : ℝ → ℂ := fun x => ((x + 4) * sinc4Kernel 1 x : ℂ)
  have hf : Integrable f := (sinc4Kernel_integrable 1 (by norm_num)).ofReal
  have hxf : Integrable (fun x : ℝ => x • f x) := by
    convert sinc4Kernel_unit_first_moment.1.ofReal using 1
    ext x
    simp [f, Complex.real_smul]
  have hF (w : ℝ) (hw : 1 < |(-2 * Real.pi) * w|) :
      FourierTransform.fourier f w = 0 := by
    rw [Real.fourier_eq']
    convert sinc4Kernel_fourier_eq_zero 1 ((-2 * Real.pi) * w)
      (by norm_num) (le_of_lt hw) using 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hderiv (w : ℝ) (hw : 1 < |(-2 * Real.pi) * w|) :
      deriv (FourierTransform.fourier f) w = 0 := by
    have hopen : IsOpen {v : ℝ | 1 < |(-2 * Real.pi) * v|} := by
      exact isOpen_lt continuous_const ((continuous_const.mul continuous_id).abs)
    have heq : FourierTransform.fourier f =ᶠ[nhds w] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact hF v hv
    rw [heq.deriv_eq]
    simp
  have hxF (w : ℝ) (hw : 1 < |(-2 * Real.pi) * w|) :
      FourierTransform.fourier (fun x : ℝ => x • f x) w = 0 := by
    have hd := congrFun (Real.deriv_fourier hf hxf) w
    rw [hderiv w hw] at hd
    have heq : (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • f x) =
        (-2 * Real.pi * Complex.I) • (fun x : ℝ => x • f x) := by
      ext x
      simp [Pi.smul_apply, mul_assoc]
    rw [heq] at hd
    have hscalar : FourierTransform.fourier
        ((-2 * Real.pi * Complex.I) • (fun x : ℝ => x • f x)) w =
        (-2 * Real.pi * Complex.I) •
          FourierTransform.fourier (fun x : ℝ => x • f x) w := by
      simp only [Real.fourier_real_eq_integral_exp_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    rw [hscalar] at hd
    have hc : (-2 * Real.pi * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    exact (smul_eq_zero.mp hd.symm).resolve_left hc
  have hgF (w : ℝ) (hw : 1 < |(-2 * Real.pi) * w|) :
      FourierTransform.fourier g w = 0 := by
    have heq : g = (fun x : ℝ => x • f x) + (4 : ℂ) • f := by
      funext x
      simp [g, f, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      ring
    have hsum : FourierTransform.fourier
        ((fun x : ℝ => x • f x) + (4 : ℂ) • f) w =
        FourierTransform.fourier (fun x : ℝ => x • f x) w +
          (4 : ℂ) * FourierTransform.fourier f w := by
      simp only [Real.fourier_real_eq_integral_exp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      have hi : Integrable (fun x : ℝ =>
          Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * (x • f x)) := by
        have he : Continuous (fun x : ℝ =>
            Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)) := by fun_prop
        have hb : ∀ᶠ x : ℝ in ae volume,
            ‖Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)‖ ≤ 1 :=
          Filter.Eventually.of_forall (fun x => by
            rw [Complex.norm_exp_ofReal_mul_I])
        convert hxf.mul_bdd he.aestronglyMeasurable hb using 1
        ext x
        exact mul_comm _ _
      have hj : Integrable (fun x : ℝ =>
          Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * f x) := by
        have he : Continuous (fun x : ℝ =>
            Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)) := by fun_prop
        have hb : ∀ᶠ x : ℝ in ae volume,
            ‖Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)‖ ≤ 1 :=
          Filter.Eventually.of_forall (fun x => by
            rw [Complex.norm_exp_ofReal_mul_I])
        convert hf.mul_bdd he.aestronglyMeasurable hb using 1
        ext x
        exact mul_comm _ _
      rw [← integral_add hi (hj.const_mul 4)]
      congr 1
      ext x
      ring
    rw [heq, hsum, hxF w hw, hF w hw]
    simp
  let H : ℝ → ℂ := fun s => ∫ y : ℝ,
    Complex.exp (((s * y : ℝ) : ℂ) * Complex.I) *
      (esseenSignedSinc4Kernel y : ℂ)
  have hstrict (s : ℝ) (hs : 1 < |s|) : H s = 0 := by
    let w : ℝ := s / (2 * Real.pi)
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hw : 1 < |(-2 * Real.pi) * w| := by
      have heq : (-2 * Real.pi) * w = -s := by
        dsimp [w]
        field_simp
      rw [heq, abs_neg]
      exact hs
    have hzero := hgF w hw
    have hp : (∫ x : ℝ,
        Complex.exp (((-(s * x) : ℝ) : ℂ) * Complex.I) * g x) = 0 := by
      rw [Real.fourier_real_eq_integral_exp_smul] at hzero
      convert hzero using 1
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul]
      congr 2
      have hr : -2 * Real.pi * x * w = -(s * x) := by
        dsimp [w]
        field_simp
      exact congrArg (fun r : ℝ => (r : ℂ) * Complex.I) hr.symm
    let q : ℝ → ℂ := fun x =>
      Complex.exp (((s * (-x - 4) : ℝ) : ℂ) * Complex.I) * ((1 / 8 : ℂ) * g x)
    have hq : (∫ x : ℝ, q x) = 0 := by
      have hc (x : ℝ) : q x =
          ((1 / 8 : ℂ) * Complex.exp (((-(4 * s) : ℝ) : ℂ) * Complex.I)) *
            (Complex.exp (((-(s * x) : ℝ) : ℂ) * Complex.I) * g x) := by
        dsimp [q]
        have he : (((s * (-x - 4) : ℝ) : ℂ) * Complex.I) =
            (((-(4 * s) : ℝ) : ℂ) * Complex.I) +
              (((-(s * x) : ℝ) : ℂ) * Complex.I) := by
          push_cast
          ring
        rw [he, Complex.exp_add]
        ring
      simp_rw [hc, integral_const_mul, hp, mul_zero]
    have hchange : H s = ∫ x : ℝ, q x := by
      letI : (volume : Measure ℝ).IsAddRightInvariant :=
        MeasureTheory.IsAddLeftInvariant.isAddRightInvariant
      have heq (y : ℝ) :
          Complex.exp (((s * y : ℝ) : ℂ) * Complex.I) *
            (esseenSignedSinc4Kernel y : ℂ) = q (-y - 4) := by
        dsimp [q, g, esseenSignedSinc4Kernel]
        have hy : -(-y - 4) - 4 = y := by ring
        rw [hy]
        push_cast
        ring
      calc
        H s = ∫ y : ℝ, q (-y - 4) := by
          apply integral_congr_ae
          filter_upwards with y
          exact heq y
        _ = ∫ y : ℝ, q (-y) := by
          have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
            (fun y : ℝ => q (-y)) 4
          convert hshift using 1
          congr 1
          ext y
          congr 1
          ring
        _ = ∫ y : ℝ, q y := integral_neg_eq_self q volume
    exact hchange.trans hq
  have hHcont : Continuous H := by
    have hfK : Integrable (fun y : ℝ => (esseenSignedSinc4Kernel y : ℂ)) :=
      esseenSignedSinc4Kernel_integrable_continuous.1.ofReal
    have hfourier (w : ℝ) : FourierTransform.fourier
        (fun y : ℝ => (esseenSignedSinc4Kernel y : ℂ)) w = H ((-2 * Real.pi) * w) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with y
      simp only [smul_eq_mul, RCLike.inner_apply', starRingEnd_apply, star_trivial]
      congr 2
      push_cast
      ring
    have hc : Continuous (FourierTransform.fourier
        (fun y : ℝ => (esseenSignedSinc4Kernel y : ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfK
    have heq : H = fun s : ℝ => FourierTransform.fourier
        (fun y : ℝ => (esseenSignedSinc4Kernel y : ℂ))
          (s / (-2 * Real.pi)) := by
      funext s
      rw [hfourier]
      congr 1
      field_simp
    rw [heq]
    fun_prop
  have hright : Set.EqOn H (fun _ => (0 : ℂ)) (Set.Ici 1) := by
    have h : Set.EqOn H (fun _ => (0 : ℂ)) (Set.Ioi 1) := by
      intro s hs
      exact hstrict s (by rw [abs_of_pos (by change 1 < s at hs; linarith)]; exact hs)
    simpa only [closure_Ioi] using h.closure hHcont continuous_const
  have hleft : Set.EqOn H (fun _ => (0 : ℂ)) (Set.Iic (-1)) := by
    have h : Set.EqOn H (fun _ => (0 : ℂ)) (Set.Iio (-1)) := by
      intro s hs
      exact hstrict s (by change s < -1 at hs; rw [abs_of_neg (by linarith)]; linarith)
    simpa only [closure_Iio] using h.closure hHcont continuous_const
  change H t = 0
  rcases le_total 0 t with hnonneg | hnonpos
  · exact hright (by simpa [abs_of_nonneg hnonneg] using ht)
  · exact hleft (by change t ≤ -1; rw [abs_of_nonpos hnonpos] at ht; linarith)

end Causalean.Stat.CLT.BerryEsseen
