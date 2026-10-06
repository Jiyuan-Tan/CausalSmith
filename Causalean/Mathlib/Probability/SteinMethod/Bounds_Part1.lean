/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.SteinMethod.Solution
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Uniform bounds on the Stein solution (Chen–Goldstein–Shao)

For an absolutely continuous test function `h` with bounded derivative `‖h'‖_∞ ≤ L`, the Stein
solution `f_h` is uniformly bounded by `L` and its derivative by `2·L`:

    ‖f_h‖_∞ ≤ L,   ‖f_h'‖_∞ ≤ 2·L.

This first half proves the public bound `steinSol_abs_le` and develops the
needed Gaussian tail moment identities, two-sided lower Mills-ratio bounds,
and cancellation inequalities behind Chen-Goldstein-Shao Lemma 2.4, equation (2.13).
`Bounds_Part2.lean` imports this module and proves `steinSol_deriv_abs_le` and
`steinSol_deriv_lipschitz`, the latter packaging the second-derivative bound as
Lipschitz control of `f_h'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Real

namespace Causalean.Mathlib.Probability.SteinMethod
/-- For every [real argument](hyp:x), the [Gaussian weight](goal) is $e^{-x^2/2}$. -/
noncomputable def phi (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2)

/-- At [every real argument](hyp:x), [the Gaussian weight is strictly positive](goal). -/
theorem phi_pos (x : ℝ) : 0 < phi x := Real.exp_pos _

/-- The Gaussian weight `φ(x) = e^{-x²/2}` is continuous on the real line. -/
@[fun_prop]
theorem phi_continuous : Continuous phi := by
  unfold phi; fun_prop

/-- `∫ φ = √(2π)`. -/
theorem integral_phi : ∫ x, phi x = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have he : (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) = phi := by
    funext x; unfold phi; ring_nf
  rw [he] at h
  rw [h]
  congr 1
  rw [div_div_eq_mul_div]; ring

/-- The standard-normal pdf equals `(√(2π))⁻¹ · φ`. -/
private theorem gaussianPDFReal_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * phi x := by
  unfold gaussianPDFReal phi
  push_cast
  congr 2
  · norm_num
  · ring

/-- **Bridge:** `E[h(Z)] = (√(2π))⁻¹ ∫ h(x) φ(x) dx`. -/
theorem gExpect_eq (h : ℝ → ℝ) :
    gExpect h = (Real.sqrt (2 * π))⁻¹ * ∫ x, h x * phi x := by
  unfold gExpect
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [gaussianPDFReal_eq, smul_eq_mul]
  ring

/-- The Gaussian weight `φ` is integrable over the real line. -/
@[fun_prop]
theorem phi_integrable : Integrable phi := by
  have : phi = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x; unfold phi; ring_nf
  rw [this]
  exact integrable_exp_neg_mul_sq (by norm_num)

/-- `h·φ` is integrable when `h` is continuous and bounded. -/
theorem mul_phi_integrable {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) : Integrable (fun x => h x * phi x) := by
  have hdom : Integrable (fun x : ℝ => C * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hdom.mono' ((hh.mul phi_continuous).aestronglyMeasurable) ?_
  filter_upwards with x
  have hexp : phi x = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by unfold phi; ring_nf
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_pos x).le, hexp]
  have hxle : |h x| ≤ C := hb x
  gcongr

/-- **Centering:** `∫ (h x − E[h(Z)]) φ(x) dx = 0`. -/
private theorem integral_centered_phi {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) :
    ∫ x, (h x - gExpect h) * phi x = 0 := by
  have hsqrt_pos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hint : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
  have hcphi : Integrable (fun x => gExpect h * phi x) := by fun_prop
  have : (fun x => (h x - gExpect h) * phi x) = (fun x => h x * phi x - gExpect h * phi x) := by
    funext x; ring
  rw [this, integral_sub hint hcphi]
  rw [integral_const_mul, integral_phi, gExpect_eq]
  field_simp
  ring

/-- `h` is `L`-Lipschitz: `|h x − h y| ≤ L·|x − y|`. -/
private theorem h_lipschitz {h : ℝ → ℝ} {L : ℝ} (hd : ∀ x, |deriv h x| ≤ L)
    (hdiff : Differentiable ℝ h) (x y : ℝ) : |h x - h y| ≤ L * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := h) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => by simpa [Real.norm_eq_abs] using hd z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- Derivative of `-φ` is `x·φ`. -/
private theorem neg_phi_hasDerivAt (x : ℝ) : HasDerivAt (fun y => -phi y) (x * phi x) x := by
  unfold phi
  have hpow : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).fun_neg
    simpa [neg_div, pow_one] using this.congr_deriv (by ring)
  have hcomp : HasDerivAt (fun y => Real.exp (-y ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x := (Real.hasDerivAt_exp _).comp x hpow
  exact hcomp.fun_neg.congr_deriv (by ring)

/-- The absolute value of any real number is at most the exponential of one quarter of its
square. -/
theorem abs_le_exp_sq_div_four (x : ℝ) : |x| ≤ Real.exp (x ^ 2 / 4) := by
  have h1 : |x| ≤ 1 + x ^ 2 / 4 := by
    nlinarith [sq_nonneg (|x| / 2 - 1), sq_abs x, abs_nonneg x]
  exact h1.trans (by have := Real.add_one_le_exp (x ^ 2 / 4); linarith)

/-- The map `x ↦ x·φ(x)` is integrable over the real line. -/
@[fun_prop]
theorem x_mul_phi_integrable : Integrable (fun x : ℝ => x * phi x) := by
  have hdom : Integrable (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine hdom.mono' ((continuous_id.mul phi_continuous).aestronglyMeasurable) ?_
  filter_upwards with x
  have hexp : phi x = Real.exp (-(1/2 : ℝ) * x ^ 2) := by unfold phi; ring_nf
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_pos x).le, hexp]
  calc |x| * Real.exp (-(1/2 : ℝ) * x ^ 2)
      ≤ Real.exp (x ^ 2 / 4) * Real.exp (-(1/2 : ℝ) * x ^ 2) := by
        gcongr; exact abs_le_exp_sq_div_four x
    _ = Real.exp (-(1/4 : ℝ) * x ^ 2) := by rw [← Real.exp_add]; congr 1; ring

private theorem mul_phi_integrableOn_Ioi (w : ℝ) :
    IntegrableOn (fun x => x * phi x) (Set.Ioi w) := by
  exact x_mul_phi_integrable.integrableOn

private theorem mul_phi_integrableOn_Iic (w : ℝ) :
    IntegrableOn (fun x => x * phi x) (Set.Iic w) := by
  exact x_mul_phi_integrable.integrableOn

private theorem neg_mul_phi_integrableOn_Iic (w : ℝ) :
    IntegrableOn (fun x => (-x) * phi x) (Set.Iic w) := by
  simpa only [neg_mul] using (mul_phi_integrableOn_Iic w).fun_neg

/-- `φ → 0` at `-∞`. -/
private theorem phi_tendsto_atBot : Filter.Tendsto phi Filter.atBot (nhds 0) := by
  unfold phi
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atBot Filter.atTop := by
    have htop : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)
    have hcomp := htop.comp Filter.tendsto_neg_atBot_atTop
    change Filter.Tendsto (fun x : ℝ => (-x) ^ 2) Filter.atBot Filter.atTop at hcomp
    simpa only [neg_sq] using hcomp
  have h2 : Filter.Tendsto (fun x : ℝ => -x ^ 2 / 2) Filter.atBot Filter.atBot := by
    apply Filter.Tendsto.atBot_div_const (by norm_num)
    exact Filter.tendsto_neg_atBot_iff.mpr hsq
  exact Real.tendsto_exp_atBot.comp h2

/-- **Left tail moment:** `∫ x in Iic w, (-x)·φ x = φ w`. -/
private theorem integral_Iic_mul_phi (w : ℝ) : ∫ x in Set.Iic w, (-x) * phi x = phi w := by
  have hphideriv : ∀ x : ℝ, HasDerivAt phi ((-x) * phi x) x := by
    intro x
    have h := (neg_phi_hasDerivAt x).neg
    have hfun : (-fun y => -phi y) = phi := by funext y; simp
    rw [hfun] at h
    simpa only [neg_mul] using h
  have hderiv : ∀ x ∈ Set.Iic w, HasDerivAt phi ((-x) * phi x) x := fun x _ => hphideriv x
  have := integral_Iic_of_hasDerivAt_of_tendsto'
    (f := phi) (f' := fun x => (-x) * phi x) (a := w) (m := 0)
    hderiv (neg_mul_phi_integrableOn_Iic w) phi_tendsto_atBot
  simpa using this

/-- `-φ → 0` at `+∞`. -/
theorem neg_phi_tendsto_atTop : Filter.Tendsto (fun x => -phi x) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto phi Filter.atTop (nhds 0) := by
    unfold phi
    have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)
    have h2 : Filter.Tendsto (fun x : ℝ => -x ^ 2 / 2) Filter.atTop Filter.atBot := by
      apply Filter.Tendsto.atBot_div_const (by norm_num)
      exact Filter.tendsto_neg_atBot_iff.mpr hsq
    exact Real.tendsto_exp_atBot.comp h2
  simpa using this.neg

/-- **Tail moment:** `∫ x in Ioi w, x·φ x = φ w`. -/
private theorem integral_Ioi_mul_phi (w : ℝ) : ∫ x in Set.Ioi w, x * phi x = phi w := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y => -phi y) (f' := fun x => x * phi x) (a := w) (m := 0)
    (fun x _ => neg_phi_hasDerivAt x) (mul_phi_integrableOn_Ioi w) neg_phi_tendsto_atTop
  simpa using this

private theorem centered_phi_integrable {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) :
    Integrable (fun x => (h x - gExpect h) * phi x) := by
  have hhφ : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
  have hcφ : Integrable (fun x => gExpect h * phi x) := by fun_prop
  have hsub : Integrable (fun x => h x * phi x - gExpect h * phi x) := by fun_prop
  convert hsub using 1
  ext x
  ring

/-- The upper-tail representation of the Stein solution, obtained from centering. -/
private theorem steinSol_eq_Ioi (h : ℝ → ℝ) (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    steinSol h w =
      -Real.exp (w ^ 2 / 2) * ∫ x in Set.Ioi w, (h x - gExpect h) * phi x := by
  let F : ℝ → ℝ := fun x => (h x - gExpect h) * phi x
  have hFint : Integrable F := centered_phi_integrable hh hb
  have hsplit := MeasureTheory.integral_add_compl (μ := volume) (f := F)
    (s := Set.Iic w) measurableSet_Iic hFint
  have hcenter : ∫ x, F x = 0 := by
    simpa [F] using integral_centered_phi hh hb
  have hsum : (∫ x in Set.Iic w, F x) + (∫ x in Set.Ioi w, F x) = 0 := by
    simpa [F, Set.compl_Iic] using hsplit.trans hcenter
  have hleft : ∫ x in Set.Iic w, F x = -∫ x in Set.Ioi w, F x := by
    linarith
  rw [steinSol]
  change Real.exp (w ^ 2 / 2) * (∫ x in Set.Iic w, F x) =
    -Real.exp (w ^ 2 / 2) * ∫ x in Set.Ioi w, F x
  rw [hleft]
  ring

private theorem sub_mul_phi_integrableOn_Ioi (w : ℝ) :
    IntegrableOn (fun x => (x - w) * phi x) (Set.Ioi w) := by
  have hx : IntegrableOn (fun x => x * phi x) (Set.Ioi w) := mul_phi_integrableOn_Ioi w
  have hw : IntegrableOn (fun x => w * phi x) (Set.Ioi w) :=
    phi_integrable.integrableOn.const_mul _
  have heq : (fun x => (x - w) * phi x) = (fun x => x * phi x - w * phi x) := by
    funext x; ring
  rw [heq]
  exact hx.sub hw

private theorem sub_mul_phi_integrableOn_Iic (w : ℝ) :
    IntegrableOn (fun x => (w - x) * phi x) (Set.Iic w) := by
  have hx : IntegrableOn (fun x => (-x) * phi x) (Set.Iic w) :=
    neg_mul_phi_integrableOn_Iic w
  have hw : IntegrableOn (fun x => w * phi x) (Set.Iic w) :=
    phi_integrable.integrableOn.const_mul _
  have heq : (fun x => (w - x) * phi x) = (fun x => w * phi x + (-x) * phi x) := by
    funext x; ring
  rw [heq]
  exact hw.add hx

/-- At [a real cutoff](hyp:w), the upper-tail integral of the distance above the cutoff times the
Gaussian weight [equals the weight minus the cutoff times its upper-tail mass](goal). -/
theorem integral_Ioi_sub_mul_phi (w : ℝ) :
    ∫ x in Set.Ioi w, (x - w) * phi x =
      phi w - w * ∫ x in Set.Ioi w, phi x := by
  have hx : IntegrableOn (fun x => x * phi x) (Set.Ioi w) := mul_phi_integrableOn_Ioi w
  have hw : IntegrableOn (fun x => w * phi x) (Set.Ioi w) :=
    phi_integrable.integrableOn.const_mul _
  calc
    ∫ x in Set.Ioi w, (x - w) * phi x
        = ∫ x in Set.Ioi w, (x * phi x - w * phi x) := by
          congr 1
          ext x
          ring
    _ = (∫ x in Set.Ioi w, x * phi x) - ∫ x in Set.Ioi w, w * phi x := by
          rw [integral_sub hx hw]
    _ = phi w - w * ∫ x in Set.Ioi w, phi x := by
          rw [integral_Ioi_mul_phi, integral_const_mul]

/-- At [a real cutoff](hyp:w), [the lower-tail integral of the distance below the cutoff times the
Gaussian weight equals the cutoff times the lower-tail mass plus the weight at the cutoff](goal). -/
theorem integral_Iic_sub_mul_phi (w : ℝ) :
    ∫ x in Set.Iic w, (w - x) * phi x =
      w * (∫ x in Set.Iic w, phi x) + phi w := by
  have hx : IntegrableOn (fun x => (-x) * phi x) (Set.Iic w) :=
    neg_mul_phi_integrableOn_Iic w
  have hw : IntegrableOn (fun x => w * phi x) (Set.Iic w) :=
    phi_integrable.integrableOn.const_mul _
  calc
    ∫ x in Set.Iic w, (w - x) * phi x
        = ∫ x in Set.Iic w, (w * phi x + (-x) * phi x) := by
          congr 1
          ext x
          ring
    _ = (∫ x in Set.Iic w, w * phi x) + ∫ x in Set.Iic w, (-x) * phi x := by
          rw [integral_add hw hx]
    _ = w * (∫ x in Set.Iic w, phi x) + phi w := by
          rw [integral_Iic_mul_phi, integral_const_mul]

private theorem diff_phi_integrableOn_Ioi {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    IntegrableOn (fun x => (h x - h w) * phi x) (Set.Ioi w) := by
  have hhφ : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
  have hwφ : Integrable (fun x => h w * phi x) := by fun_prop
  have hsub : Integrable (fun x => h x * phi x - h w * phi x) := by fun_prop
  have hdiff : Integrable (fun x => (h x - h w) * phi x) := by
    convert hsub using 1
    ext x
    ring
  exact hdiff.integrableOn

private theorem diff_phi_integrableOn_Iic {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    IntegrableOn (fun x => (h x - h w) * phi x) (Set.Iic w) := by
  have hhφ : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
  have hwφ : Integrable (fun x => h w * phi x) := by fun_prop
  have hsub : Integrable (fun x => h x * phi x - h w * phi x) := by fun_prop
  have hdiff : Integrable (fun x => (h x - h w) * phi x) := by
    convert hsub using 1
    ext x
    ring
  exact hdiff.integrableOn

/-- If [a real function is continuous](hyp:hh), [is uniformly bounded](hyp:hb), [has derivative
bounded in absolute value by a constant](hyp:hd), and [is differentiable](hyp:hdiff), then at [a
real cutoff](hyp:w), [the absolute upper-tail integral of its increment times the Gaussian weight
is at most that derivative bound times the corresponding Gaussian first-moment expression](goal). -/
theorem abs_integral_diff_phi_Ioi_le {h : ℝ → ℝ} (hh : Continuous h) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h)
    (w : ℝ) :
    |∫ x in Set.Ioi w, (h x - h w) * phi x|
      ≤ L * (phi w - w * ∫ x in Set.Ioi w, phi x) := by
  have hδ : IntegrableOn (fun x => (h x - h w) * phi x) (Set.Ioi w) :=
    diff_phi_integrableOn_Ioi hh hb w
  have hm : IntegrableOn (fun x => L * ((x - w) * phi x)) (Set.Ioi w) :=
    (sub_mul_phi_integrableOn_Ioi w).const_mul _
  calc
    |∫ x in Set.Ioi w, (h x - h w) * phi x|
        ≤ ∫ x in Set.Ioi w, |(h x - h w) * phi x| := by
          exact abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Ioi w, L * ((x - w) * phi x) := by
          refine setIntegral_mono_on hδ.norm hm measurableSet_Ioi ?_
          intro x hx
          have hxle : w ≤ x := le_of_lt hx
          have hlip := h_lipschitz hd hdiff x w
          have hphi_nonneg : 0 ≤ phi x := (phi_pos x).le
          calc
            |(h x - h w) * phi x| = |h x - h w| * phi x := by
              rw [abs_mul, abs_of_nonneg hphi_nonneg]
            _ ≤ (L * |x - w|) * phi x := by
              exact mul_le_mul_of_nonneg_right hlip hphi_nonneg
            _ = L * ((x - w) * phi x) := by
              rw [abs_of_nonneg (sub_nonneg.mpr hxle)]
              ring
    _ = L * (phi w - w * ∫ x in Set.Ioi w, phi x) := by
          rw [integral_const_mul, integral_Ioi_sub_mul_phi]

/-- If [a real function is continuous](hyp:hh), [is uniformly bounded](hyp:hb), [has derivative
bounded in absolute value by a constant](hyp:hd), and [is differentiable](hyp:hdiff), then at [a
real cutoff](hyp:w), [the absolute lower-tail integral of its increment times the Gaussian weight
is at most that derivative bound times the corresponding Gaussian first-moment expression](goal). -/
theorem abs_integral_diff_phi_Iic_le {h : ℝ → ℝ} (hh : Continuous h) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h)
    (w : ℝ) :
    |∫ x in Set.Iic w, (h x - h w) * phi x|
      ≤ L * (w * (∫ x in Set.Iic w, phi x) + phi w) := by
  have hδ : IntegrableOn (fun x => (h x - h w) * phi x) (Set.Iic w) :=
    diff_phi_integrableOn_Iic hh hb w
  have hm : IntegrableOn (fun x => L * ((w - x) * phi x)) (Set.Iic w) :=
    (sub_mul_phi_integrableOn_Iic w).const_mul _
  calc
    |∫ x in Set.Iic w, (h x - h w) * phi x|
        ≤ ∫ x in Set.Iic w, |(h x - h w) * phi x| := by
          exact abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Iic w, L * ((w - x) * phi x) := by
          refine setIntegral_mono_on hδ.norm hm measurableSet_Iic ?_
          intro x hx
          have hxle : x ≤ w := hx
          have hlip := h_lipschitz hd hdiff x w
          have hphi_nonneg : 0 ≤ phi x := (phi_pos x).le
          calc
            |(h x - h w) * phi x| = |h x - h w| * phi x := by
              rw [abs_mul, abs_of_nonneg hphi_nonneg]
            _ ≤ (L * |x - w|) * phi x := by
              exact mul_le_mul_of_nonneg_right hlip hphi_nonneg
            _ = L * ((w - x) * phi x) := by
              rw [abs_of_nonpos (sub_nonpos.mpr hxle)]
              ring
    _ = L * (w * (∫ x in Set.Iic w, phi x) + phi w) := by
          rw [integral_const_mul, integral_Iic_sub_mul_phi]

/-- At [a real cutoff](hyp:w), [the lower- and upper-tail Gaussian-weight integrals sum to the
square root of twice π](goal). -/
theorem integral_Iic_add_Ioi_phi (w : ℝ) :
    (∫ x in Set.Iic w, phi x) + ∫ x in Set.Ioi w, phi x = Real.sqrt (2 * π) := by
  have h := intervalIntegral.integral_Iic_add_Ioi
    (f := phi) (μ := volume) (b := w) phi_integrable.integrableOn phi_integrable.integrableOn
  simpa [integral_phi] using h

private theorem integral_centered_split_Iic {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    ∫ x in Set.Iic w, (h x - gExpect h) * phi x =
      (∫ x in Set.Iic w, (h x - h w) * phi x) +
        (h w - gExpect h) * ∫ x in Set.Iic w, phi x := by
  have hδ := diff_phi_integrableOn_Iic hh hb w
  have hc : IntegrableOn (fun x => (h w - gExpect h) * phi x) (Set.Iic w) :=
    phi_integrable.integrableOn.const_mul _
  calc
    ∫ x in Set.Iic w, (h x - gExpect h) * phi x
        = ∫ x in Set.Iic w, ((h x - h w) * phi x +
            (h w - gExpect h) * phi x) := by
          congr 1
          ext x
          ring
    _ = (∫ x in Set.Iic w, (h x - h w) * phi x) +
          ∫ x in Set.Iic w, (h w - gExpect h) * phi x := by
          rw [integral_add hδ hc]
    _ = (∫ x in Set.Iic w, (h x - h w) * phi x) +
        (h w - gExpect h) * ∫ x in Set.Iic w, phi x := by
          rw [integral_const_mul]

private theorem integral_centered_split_Ioi {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    ∫ x in Set.Ioi w, (h x - gExpect h) * phi x =
      (∫ x in Set.Ioi w, (h x - h w) * phi x) +
        (h w - gExpect h) * ∫ x in Set.Ioi w, phi x := by
  have hδ := diff_phi_integrableOn_Ioi hh hb w
  have hc : IntegrableOn (fun x => (h w - gExpect h) * phi x) (Set.Ioi w) :=
    phi_integrable.integrableOn.const_mul _
  calc
    ∫ x in Set.Ioi w, (h x - gExpect h) * phi x
        = ∫ x in Set.Ioi w, ((h x - h w) * phi x +
            (h w - gExpect h) * phi x) := by
          congr 1
          ext x
          ring
    _ = (∫ x in Set.Ioi w, (h x - h w) * phi x) +
          ∫ x in Set.Ioi w, (h w - gExpect h) * phi x := by
          rw [integral_add hδ hc]
    _ = (∫ x in Set.Ioi w, (h x - h w) * phi x) +
        (h w - gExpect h) * ∫ x in Set.Ioi w, phi x := by
          rw [integral_const_mul]

/-- If [a real function is continuous](hyp:hh) and [uniformly bounded](hyp:hb), then at [a real
argument](hyp:w), [its Stein solution, multiplied by the square root of twice π, equals the
exponentially weighted difference of the two products formed from the opposite Gaussian-tail
masses and the corresponding centered tail integrals](goal). -/
theorem steinSol_weighted_identity {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (w : ℝ) :
    Real.sqrt (2 * π) * steinSol h w =
      Real.exp (w ^ 2 / 2) *
        ((∫ x in Set.Ioi w, phi x) * (∫ x in Set.Iic w, (h x - h w) * phi x) -
          (∫ x in Set.Iic w, phi x) * (∫ x in Set.Ioi w, (h x - h w) * phi x)) := by
  let P := ∫ x in Set.Ioi w, phi x
  let Q := ∫ x in Set.Iic w, phi x
  let A := ∫ x in Set.Iic w, (h x - h w) * phi x
  let B := ∫ x in Set.Ioi w, (h x - h w) * phi x
  let D := h w - gExpect h
  let E := Real.exp (w ^ 2 / 2)
  have hK : Real.sqrt (2 * π) = P + Q := by
    have h := integral_Iic_add_Ioi_phi w
    linarith
  have hIic : steinSol h w = E * (A + D * Q) := by
    rw [steinSol]
    change E * (∫ x in Set.Iic w, (h x - gExpect h) * phi x) = E * (A + D * Q)
    rw [integral_centered_split_Iic hh hb w]
  have hIoi : steinSol h w = -E * (B + D * P) := by
    rw [steinSol_eq_Ioi h hh hb w]
    change -E * (∫ x in Set.Ioi w, (h x - gExpect h) * phi x) = -E * (B + D * P)
    rw [integral_centered_split_Ioi hh hb w]
  calc
    Real.sqrt (2 * π) * steinSol h w
        = (P + Q) * steinSol h w := by rw [hK]
    _ = P * steinSol h w + Q * steinSol h w := by ring
    _ = P * (E * (A + D * Q)) + Q * steinSol h w := by
          rw [hIic]
    _ = P * (E * (A + D * Q)) + Q * (-E * (B + D * P)) := by
          rw [hIoi]
    _ = E * (P * A - Q * B) := by ring

/-- At [every real argument](hyp:w), [the Gaussian weight times the exponential of half the
squared argument equals one](goal). -/
theorem exp_mul_phi (w : ℝ) : Real.exp (w ^ 2 / 2) * phi w = 1 := by
  unfold phi
  rw [← Real.exp_add]
  rw [show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero]

private theorem weighted_moment_cancel (w : ℝ) :
    Real.exp (w ^ 2 / 2) *
      ((∫ x in Set.Ioi w, phi x) *
          (w * (∫ x in Set.Iic w, phi x) + phi w) +
        (∫ x in Set.Iic w, phi x) *
          (phi w - w * ∫ x in Set.Ioi w, phi x)) =
      Real.sqrt (2 * π) := by
  set E : ℝ := Real.exp (w ^ 2 / 2) with hE
  set P : ℝ := ∫ x in Set.Ioi w, phi x with hP
  set Q : ℝ := ∫ x in Set.Iic w, phi x with hQ
  have hK : Q + P = Real.sqrt (2 * π) := by
    simpa [P, Q] using integral_Iic_add_Ioi_phi w
  have hEφ : E * phi w = 1 := by
    simpa [E] using exp_mul_phi w
  calc
    E * (P * (w * Q + phi w) + Q * (phi w - w * P))
        = E * ((P + Q) * phi w) := by ring
    _ = Real.sqrt (2 * π) := by
      rw [add_comm P Q, hK]
      calc
        E * (Real.sqrt (2 * π) * phi w)
            = Real.sqrt (2 * π) * (E * phi w) := by ring
        _ = Real.sqrt (2 * π) := by rw [hEφ, mul_one]

/-- For a real-valued test function `h` that is [bounded in absolute value by a constant
`C`](hyp:hb), [has derivative bounded in absolute value by a constant `L`](hyp:hd), and
[is differentiable everywhere](hyp:hdiff), [the Stein equation's solution `steinSol h`, evaluated
at any point `w`, is bounded in absolute value by the derivative bound `L`](goal). -/
theorem steinSol_abs_le (h : ℝ → ℝ) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h) (w : ℝ) :
    |steinSol h w| ≤ L := by
  -- Notation for the four building blocks of the weighted identity.
  set P : ℝ := ∫ x in Set.Ioi w, phi x with hP
  set Q : ℝ := ∫ x in Set.Iic w, phi x with hQ
  set A : ℝ := ∫ x in Set.Iic w, (h x - h w) * phi x with hA
  set B : ℝ := ∫ x in Set.Ioi w, (h x - h w) * phi x with hB
  set E : ℝ := Real.exp (w ^ 2 / 2) with hE
  have hPpos : 0 ≤ P := by
    rw [hP]; exact setIntegral_nonneg measurableSet_Ioi (fun x _ => (phi_pos x).le)
  have hQpos : 0 ≤ Q := by
    rw [hQ]; exact setIntegral_nonneg measurableSet_Iic (fun x _ => (phi_pos x).le)
  have hEpos : 0 < E := Real.exp_pos _
  have hKpos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  -- Bounds on |A| and |B| coming from the Lipschitz estimates.
  have hAbound : |A| ≤ L * (w * Q + phi w) := by
    rw [hA, hQ]; exact abs_integral_diff_phi_Iic_le hdiff.continuous hb hd hdiff w
  have hBbound : |B| ≤ L * (phi w - w * P) := by
    rw [hB, hP]; exact abs_integral_diff_phi_Ioi_le hdiff.continuous hb hd hdiff w
  -- The weighted identity, with the cancellation pre-computed.
  have hid : Real.sqrt (2 * π) * steinSol h w = E * (P * A - Q * B) := by
    rw [hE, hP, hQ, hA, hB]; exact steinSol_weighted_identity hdiff.continuous hb w
  -- Bound `√(2π)·|steinSol|`.
  have hmain : Real.sqrt (2 * π) * |steinSol h w| ≤ Real.sqrt (2 * π) * L := by
    calc Real.sqrt (2 * π) * |steinSol h w|
        = |Real.sqrt (2 * π) * steinSol h w| := by
          rw [abs_mul, abs_of_nonneg hKpos.le]
      _ = |E * (P * A - Q * B)| := by rw [hid]
      _ = E * |P * A - Q * B| := by rw [abs_mul, abs_of_nonneg hEpos.le]
      _ ≤ E * (P * |A| + Q * |B|) := by
          gcongr
          calc |P * A - Q * B| ≤ |P * A| + |Q * B| := abs_sub _ _
            _ = P * |A| + Q * |B| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hPpos, abs_of_nonneg hQpos]
      _ ≤ E * (P * (L * (w * Q + phi w)) + Q * (L * (phi w - w * P))) := by
          gcongr
      _ = L * (E * (P * (w * Q + phi w) + Q * (phi w - w * P))) := by ring
      _ = L * Real.sqrt (2 * π) := by rw [weighted_moment_cancel w]
      _ = Real.sqrt (2 * π) * L := by ring
  -- Cancel the positive factor `√(2π)`.
  exact le_of_mul_le_mul_left hmain hKpos

end Causalean.Mathlib.Probability.SteinMethod
