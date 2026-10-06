module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourier
public import Mathlib.Analysis.Fourier.Inversion

/-! # Fourier bound for a band-limited convolution

This is the Fourier inversion and Fubini step of one-sided Esseen smoothing.
The kernel is supplied separately, so the sharp one-sided comparison can be
studied without repeating the frequency-domain argument.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For [an integrable real function H](hyp:hH) and
[a continuous integrable kernel K](hyp:hK,hKcont) whose
[Fourier transform is integrable](hyp:hKhat),
[vanishes outside (−T, T)](hyp:hsupp) for [a positive bandwidth T](hyp:hT),
and [has magnitude at most one](hyp:hnorm), if [the convolution integrand at
x is integrable](hyp:hconv), then [the convolution of H with K at x is
bounded in absolute value by 1/(2π) times the integral over [−T, T] of the
magnitude of the Fourier transform of H](goal). -/
theorem bandlimited_convolution_fourier_bound
    (H K : ℝ → ℝ) (hH : Integrable H volume)
    (hK : Integrable K volume) (hKcont : Continuous K)
    (hKhat : Integrable (fun t : ℝ =>
      ∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) volume)
    (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t : ℝ, T ≤ |t| →
      (∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)) = 0)
    (hnorm : ∀ t : ℝ,
      ‖∫ y : ℝ, Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (K y : ℂ)‖ ≤ 1)
    (x : ℝ)
    (hconv : Integrable (fun y : ℝ => H (x - y) * K y) volume) :
    |∫ y : ℝ, H (x - y) * K y| ≤
      (1 / (2 * Real.pi)) *
        ∫ t in (-T)..T,
          ‖∫ y : ℝ,
            Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * (H y : ℂ)‖ := by
  /- Invert K using hKcont and hKhat. Apply Fubini to H(x-y) times
  the inverse Fourier integral. The inner H-integral is a phase of H's
  Fourier transform, whose norm is unchanged. Restrict frequencies using
  hsupp and bound the remaining kernel transform by hnorm. -/
  let f : ℝ → ℂ := fun y => (K y : ℂ)
  let F : ℝ → ℂ := fun t => ∫ y : ℝ,
    Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) * f y
  have hf : Integrable f := hK.ofReal
  have hfc : Continuous f := by fun_prop
  have hzero (t : ℝ) (ht : T ≤ |t|) : F t = 0 := hsupp t ht
  have hFfourier (w : ℝ) : FourierTransform.fourier f w = F ((-2 * Real.pi) * w) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    simp only [smul_eq_mul, f, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [funext hFfourier]
    exact hKhat.comp_mul_left' (by positivity : (-2 * Real.pi : ℝ) ≠ 0)
  have hinv (y : ℝ) : (K y : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t := by
    have hgy : Function.support (fun t : ℝ =>
        Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t) ⊆
        Set.Ioc (-T) T := by
      intro t ht
      simp only [Function.mem_support, Set.mem_Ioc] at *
      constructor
      · by_contra hn
        exact ht (by rw [hzero t (by rw [abs_of_nonpos (by linarith)]; linarith)]; simp)
      · by_contra hn
        exact ht (by rw [hzero t (by rw [abs_of_nonneg (by linarith)]; linarith)]; simp)
    have hchange : (∫ w : ℝ,
        (Complex.exp (((-((-2 * Real.pi) * w * y) : ℝ) : ℂ) * Complex.I) *
          F ((-2 * Real.pi) * w))) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t := by
      let gy : ℝ → ℂ := fun t =>
        Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t
      change (∫ w : ℝ, gy ((-2 * Real.pi) * w)) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, gy t
      rw [Measure.integral_comp_mul_left]
      have hcoeff : |((-2 * Real.pi : ℝ)⁻¹)| = 1 / (2 * Real.pi) := by
        rw [abs_inv, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
        norm_num
      rw [hcoeff, Complex.real_smul]
    calc
      (K y : ℂ) = FourierTransform.fourierInv
          (FourierTransform.fourier f) y :=
        (hf.fourierInv_fourier_eq hFourierInt hfc.continuousAt).symm
      _ = ∫ w : ℝ,
          Complex.exp (((-((-2 * Real.pi) * w * y) : ℝ) : ℂ) * Complex.I) *
            F ((-2 * Real.pi) * w) := by
        rw [Real.fourierInv_eq']
        simp_rw [hFfourier]
        apply integral_congr_ae
        filter_upwards with w
        simp only [smul_eq_mul, RCLike.inner_apply', starRingEnd_apply, star_trivial]
        congr 2
        push_cast
        ring
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t := hchange
      _ = _ := by
        rw [← intervalIntegral.integral_eq_integral_of_support_subset hgy]
  let D : ℝ → ℝ := fun y => H (x - y)
  let Q : ℝ → ℝ → ℂ := fun t y =>
    F t * (Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * (D y : ℂ))
  have hD : Integrable D volume := hH.comp_sub_left x
  have hDℂ : Integrable (fun y : ℝ => (D y : ℂ)) volume := hD.ofReal
  have hFcont : Continuous F := by
    have hc : Continuous (FourierTransform.fourier f) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf
    have heq : F = fun t : ℝ => FourierTransform.fourier f (t / (-2 * Real.pi)) := by
      funext t
      rw [hFfourier]
      congr 1
      field_simp
    rw [heq]
    fun_prop
  have hFbound (t : ℝ) : ‖F t‖ ≤ 1 := hnorm t
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (-T) T)) := by
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)]
    infer_instance
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖(D p.2 : ℂ)‖)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) :=
    hDℂ.norm.comp_snd _
  have hQ : Integrable (Function.uncurry Q)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
    apply Integrable.mono' hmajor
    · have hc : Continuous (fun p : ℝ × ℝ =>
          F p.1 * Complex.exp (((-(p.1 * p.2) : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      have hd : AEStronglyMeasurable (fun p : ℝ × ℝ => (D p.2 : ℂ))
          ((volume.restrict (Set.uIoc (-T) T)).prod volume) :=
        (hDℂ.comp_snd _).aestronglyMeasurable
      convert hc.aestronglyMeasurable.mul hd using 1
      ext p
      simp only [Q, Function.uncurry, Pi.mul_apply]
      ring
    · filter_upwards with p
      dsimp [Q, Function.uncurry]
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hFbound p.1)
  have hswap := intervalIntegral_integral_swap (a := -T) (b := T) hQ
  have hrepr : ((∫ y : ℝ, D y * K y : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T, F t *
          (∫ y : ℝ,
            Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * (D y : ℂ)) := by
    calc
      ((∫ y : ℝ, D y * K y : ℝ) : ℂ) =
          ∫ y : ℝ, (D y : ℂ) * (K y : ℂ) := by
        calc
          ((∫ y : ℝ, D y * K y : ℝ) : ℂ) =
              ∫ y : ℝ, ((D y * K y : ℝ) : ℂ) :=
            (integral_complex_ofReal).symm
          _ = _ := by
            congr 1
            ext y
            push_cast
            rfl
      _ = ∫ y : ℝ, (D y : ℂ) *
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t in (-T)..T,
                Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hinv y]
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ y : ℝ, ∫ t in (-T)..T, Q t y := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        calc
          (D y : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t in (-T)..T,
                Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t) =
              ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ((D y : ℂ) * ∫ t in (-T)..T,
                  Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * F t) := by ring
          _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ t in (-T)..T, Q t y := by
            congr 1
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t _
            dsimp [Q]
            ring
      _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, ∫ y : ℝ, Q t y := by rw [hswap]
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [Q]
        rw [← integral_const_mul]
  have hshift (t : ℝ) :
      (∫ y : ℝ,
        Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) * (D y : ℂ)) =
        Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
          ∫ u : ℝ,
            Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ) := by
    have hHℂ : Integrable (fun u : ℝ => (H u : ℂ)) volume := hH.ofReal
    have hG : Integrable (fun u : ℝ =>
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)) volume := by
      apply hHℂ.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [] with u
        simpa only [← Complex.ofReal_mul] using
          (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * u)))
    have hphase (u : ℝ) :
        Complex.exp (((-(t * (x - u)) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hGshift : Integrable (fun u : ℝ =>
        Complex.exp (((-(t * (x - u)) : ℝ) : ℂ) * Complex.I) *
          (H u : ℂ)) volume := by
      convert hG.const_mul (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I)) using 1
      ext u
      rw [hphase u]
      ring
    have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) x
    have hGmap : AEStronglyMeasurable (fun u : ℝ =>
        Complex.exp (((-(t * (x - u)) : ℝ) : ℂ) * Complex.I) *
          (H u : ℂ))
        (Measure.map (fun y : ℝ => x - y) volume) := by
      rw [hmp.map_eq]
      exact hGshift.aestronglyMeasurable
    have hswapH := (integral_map hmp.measurable.aemeasurable hGmap).symm
    rw [hmp.map_eq] at hswapH
    calc
      _ = ∫ u : ℝ,
          Complex.exp (((-(t * (x - u)) : ℝ) : ℂ) * Complex.I) *
            (H u : ℂ) := by
        convert hswapH using 1
        congr 1
        ext y
        simp [D]
      _ = _ := by
        simp_rw [hphase, mul_assoc]
        rw [integral_const_mul]
  let h : ℝ → ℂ := fun u => (H u : ℂ)
  have hh : Integrable h := hH.ofReal
  have hHfourier (w : ℝ) : FourierTransform.fourier h w =
      ∫ u : ℝ,
        Complex.exp ((((-2 * Real.pi * w) * u : ℝ) : ℂ) * Complex.I) * h u := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul, h, RCLike.inner_apply', starRingEnd_apply, star_trivial]
    congr 2
    push_cast
    ring
  have hHhatcont : Continuous (fun t : ℝ =>
      ∫ u : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)) := by
    have hc : Continuous (FourierTransform.fourier h) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hh
    have heq : (fun t : ℝ =>
        ∫ u : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)) =
        fun t : ℝ => FourierTransform.fourier h (t / (-2 * Real.pi)) := by
      funext t
      rw [hHfourier]
      congr 1
      field_simp
      funext u
      dsimp [h]
      congr 1
      ring_nf
    rw [heq]
    fun_prop
  have hquot : IntervalIntegrable (fun t : ℝ =>
      ‖∫ u : ℝ,
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)‖)
      volume (-T) T := hHhatcont.norm.intervalIntegrable _ _
  have hpoint (t : ℝ) :
      ‖F t * (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
        ∫ u : ℝ,
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ))‖ ≤
        ‖∫ u : ℝ,
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)‖ := by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hFbound t)
  have hbound : ‖∫ t in (-T)..T,
      F t * (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
        ∫ u : ℝ,
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ))‖ ≤
      ∫ t in (-T)..T,
        ‖∫ u : ℝ,
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (H u : ℂ)‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ hquot
    filter_upwards [] with t
    exact fun _ => hpoint t
  have hfactor : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  simp_rw [hshift] at hrepr
  change ((∫ y : ℝ, H (x - y) * K y : ℝ) : ℂ) = _ at hrepr
  have hnormrepr := congrArg norm hrepr
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
    abs_of_nonneg hfactor] at hnormrepr
  rw [hnormrepr]
  exact mul_le_mul_of_nonneg_left hbound hfactor

end Causalean.Stat.CLT.BerryEsseen
