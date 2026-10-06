module
public import Causalean.Mathlib.Analysis.Fourier.Interpolation
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Transferring a weighted energy to a Gaussian shifted design integral

The variance recipe is the ordinary integral with design factor 16 and design interval
[-1/2,1/2]. The full joint integrability hypothesis is a standard Fubini hypothesis;
no quantitative variance inequality is assumed. A shift costs at most the κ-th
Gaussian moment times σ^κ times the zeroth physical energy.

Primary source fetched at the installed Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean
This supplies `memLp_id_gaussianReal`, `integral_id_gaussianReal`, and
`variance_id_gaussianReal`; no exact moment formula needs to be reimplemented.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open Causalean.Mathlib.Analysis.Fourier
namespace Causalean.Stat.Nonparametric

/-- [A moment exponent](hyp:κ), [a Gaussian noise scale](hyp:σ), and [a complex physical-space kernel](hyp:g) determine [the Gaussian-shifted design variance integral](goal) [by averaging squared kernel values over the normalized design interval and standard Gaussian noise](step:1). -/
def shiftedVariance (κ σ : ℝ) (g : ℝ → ℂ) : ℝ :=
  16 * ∫ t in Icc (-1 / 2 : ℝ) (1 / 2),
    |t| ^ κ * (∫ z, ‖g (t + σ * z)‖ ^ 2 ∂gaussianReal 0 1)

/-- [A complex physical-space kernel](hyp:g), [a moment exponent and Gaussian noise scale](hyp:κ,σ), [kernel measurability](hyp:hg), and [integrability of its weighted joint squared norm](hyp:hjoint) imply [that taking the real part cannot increase the Gaussian-shifted design variance](goal). -/
theorem shiftedVariance_realPart_le (g : ℝ → ℂ) (κ σ : ℝ) (hg : Measurable g)
    (hjoint : Integrable
      (fun p : ℝ × ℝ => |p.1| ^ κ * ‖g (p.1 + σ * p.2)‖ ^ 2)
      (volume.prod (gaussianReal 0 1))) :
    shiftedVariance κ σ (fun v => ((g v).re : ℂ)) ≤ shiftedVariance κ σ g := by
  have hp (v : ℝ) : ‖((g v).re : ℂ)‖ ^ 2 ≤ ‖g v‖ ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      pow_le_pow_left₀ (abs_nonneg (g v).re) (Complex.abs_re_le_norm (g v)) 2
  have hw (t z : ℝ) :
      |t| ^ κ * ‖((g (t + σ * z)).re : ℂ)‖ ^ 2 ≤
        |t| ^ κ * ‖g (t + σ * z)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (hp _) (Real.rpow_nonneg (abs_nonneg t) κ)
  have hr : Integrable
      (fun p : ℝ × ℝ => |p.1| ^ κ * ‖((g (p.1 + σ * p.2)).re : ℂ)‖ ^ 2)
      (volume.prod (gaussianReal 0 1)) := by
    apply hjoint.mono'
    · fun_prop
    · filter_upwards [] with p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (abs_nonneg p.1) κ) (sq_nonneg _))]
      exact hw _ _
  have ho := hr.integral_prod_left
  have hoc := hjoint.integral_prod_left
  simp only [integral_const_mul] at ho hoc
  unfold shiftedVariance
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae ho.restrict hoc.restrict
  -- Keep the weight inside each slice. Integral linearity also holds when it
  -- vanishes, so no unweighted integrability is required on zero-weight slices.
  have hs : ∀ᵐ t ∂volume,
      |t| ^ κ * (∫ z, ‖((g (t + σ * z)).re : ℂ)‖ ^ 2 ∂gaussianReal 0 1) ≤
        |t| ^ κ * (∫ z, ‖g (t + σ * z)‖ ^ 2 ∂gaussianReal 0 1) := by
    filter_upwards [hr.prod_right_ae, hjoint.prod_right_ae] with t ht htc
    simpa only [integral_const_mul] using integral_mono ht htc (hw t)
  exact ae_restrict_of_ae hs

/-- [A moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2) has [a finite standard-Gaussian absolute moment bounded by two](goal). -/
theorem gaussian_abs_moment_le_two (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) :
    Integrable (fun z : ℝ => |z| ^ κ) (gaussianReal 0 1) ∧
    (∫ z : ℝ, |z| ^ κ ∂gaussianReal 0 1) ≤ 2 := by
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hsqi : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa [integral_id_gaussianReal] using h
  have hb (z : ℝ) : |z| ^ κ ≤ 1 + z ^ 2 := by
    by_cases hz : |z| ≤ 1
    · have := Real.rpow_le_one (abs_nonneg z) hz hκ0
      nlinarith [sq_nonneg z]
    · have := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hz) hκ2
      simp only [Real.rpow_two, sq_abs] at this
      linarith
  have hm : AEStronglyMeasurable (fun z : ℝ => |z| ^ κ) (gaussianReal 0 1) := by
    fun_prop
  have hi := (integrable_const (1 : ℝ)).add hsq
  have hiκ : Integrable (fun z : ℝ => |z| ^ κ) (gaussianReal 0 1) :=
    hi.mono' hm (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) κ)]
      exact hb z)
  refine ⟨hiκ, ?_⟩
  calc
    _ ≤ ∫ z : ℝ, (1 + z ^ 2) ∂gaussianReal 0 1 := integral_mono hiκ hi hb
    _ = 2 := by
      rw [integral_add (integrable_const _) hsq, hsqi]
      norm_num

/-- A translation increases a real-power weight by at most twice the sum of
its original weight and the shift weight, including exponent zero. -/
private theorem shift_weight_le (κ v c : ℝ) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) :
    |v - c| ^ κ ≤ 2 * (|v| ^ κ + |c| ^ κ) := by
  have hk : 0 ≤ κ / 2 := by linarith
  have hk1 : κ / 2 ≤ 1 := by linarith
  have hp (x : ℝ) : (x ^ 2) ^ (κ / 2) = |x| ^ κ := by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  calc
    |v - c| ^ κ = ((v - c) ^ 2) ^ (κ / 2) := (hp _).symm
    _ ≤ (2 * (v ^ 2 + c ^ 2)) ^ (κ / 2) := by
      apply Real.rpow_le_rpow (sq_nonneg _) _ hk
      nlinarith [sq_nonneg (v + c)]
    _ = 2 ^ (κ / 2) * (v ^ 2 + c ^ 2) ^ (κ / 2) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (v ^ 2 + c ^ 2) ^ (κ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hk1
    _ ≤ 2 * ((v ^ 2) ^ (κ / 2) + (c ^ 2) ^ (κ / 2)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_add_le_add_rpow (sq_nonneg _) (sq_nonneg _) hk hk1) (by norm_num)
    _ = _ := by rw [hp, hp]

/-- A fixed translation is bounded by the two physical energies. Only the
squared norm needs to be almost everywhere measurable, as supplied by integrability. -/
private theorem shifted_energy_le (g : ℝ → ℂ) (κ c : ℝ)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (h0 : Integrable (fun v => ‖g v‖ ^ 2))
    (hκ : Integrable (fun v => |v| ^ κ * ‖g v‖ ^ 2)) :
    (∫ t, |t| ^ κ * ‖g (t + c)‖ ^ 2) ≤
      2 * (weightedEnergy κ g + |c| ^ κ * energy g) := by
  have hb (v : ℝ) : |v - c| ^ κ * ‖g v‖ ^ 2 ≤
      2 * (|v| ^ κ * ‖g v‖ ^ 2 + |c| ^ κ * ‖g v‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_right (shift_weight_le κ v c hκ0 hκ2)
      (sq_nonneg ‖g v‖)
    nlinarith
  have hi : Integrable
      (fun v => 2 * (|v| ^ κ * ‖g v‖ ^ 2 + |c| ^ κ * ‖g v‖ ^ 2)) :=
    (hκ.add (h0.const_mul _)).const_mul _
  have hm : AEStronglyMeasurable (fun v => |v - c| ^ κ * ‖g v‖ ^ 2) volume := by
    have hw : AEStronglyMeasurable (fun v : ℝ => |v - c| ^ κ) volume := by
      fun_prop
    exact hw.mul h0.aestronglyMeasurable
  have hs : Integrable (fun v => |v - c| ^ κ * ‖g v‖ ^ 2) :=
    hi.mono' hm (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))]
      exact hb v)
  calc
    _ = ∫ v, |v - c| ^ κ * ‖g v‖ ^ 2 := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun v => |v - c| ^ κ * ‖g v‖ ^ 2) c
    _ ≤ ∫ v, 2 * (|v| ^ κ * ‖g v‖ ^ 2 + |c| ^ κ * ‖g v‖ ^ 2) :=
      integral_mono hs hi hb
    _ = _ := by
      rw [integral_const_mul, integral_add hκ (h0.const_mul _), integral_const_mul]
      rfl

/-- [A complex physical-space kernel](hyp:g), [a moment exponent in the interval from zero to two](hyp:κ,hκ0,hκ2), [a nonnegative Gaussian noise scale](hyp:σ,hσ), [finite ordinary and weighted squared energies](hyp:h0,hκ), and [integrability of the weighted joint squared norm](hyp:hjoint) imply [the stated Gaussian-shifted design variance bound](goal). -/
theorem shiftedVariance_le (g : ℝ → ℂ) (κ σ : ℝ)
    (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2) (hσ : 0 ≤ σ)
    (h0 : Integrable (fun v => ‖g v‖ ^ 2))
    (hκ : Integrable (fun v => |v| ^ κ * ‖g v‖ ^ 2))
    (hjoint : Integrable
      (fun p : ℝ × ℝ => |p.1| ^ κ * ‖g (p.1 + σ * p.2)‖ ^ 2)
      (volume.prod (gaussianReal 0 1))) :
    shiftedVariance κ σ g ≤ 32 * (weightedEnergy κ g + 2 * σ ^ κ * energy g) := by
  obtain ⟨hm, hm2⟩ := gaussian_abs_moment_le_two κ hκ0 hκ2
  have he : 0 ≤ energy g := integral_nonneg (fun v => sq_nonneg _)
  have hσk : 0 ≤ σ ^ κ := Real.rpow_nonneg hσ κ
  have hc (z : ℝ) : |σ * z| ^ κ = σ ^ κ * |z| ^ κ := by
    rw [abs_mul, abs_of_nonneg hσ, Real.mul_rpow hσ (abs_nonneg z)]
  have ho := hjoint.integral_prod_left
  simp only [integral_const_mul] at ho
  have hn : ∀ t : ℝ,
      0 ≤ |t| ^ κ * (∫ z, ‖g (t + σ * z)‖ ^ 2 ∂gaussianReal 0 1) := by
    intro t
    exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (integral_nonneg fun z => sq_nonneg _)
  have hb : Integrable
      (fun z : ℝ => 2 * (weightedEnergy κ g + σ ^ κ * |z| ^ κ * energy g))
      (gaussianReal 0 1) := by
    have hi := ((integrable_const (weightedEnergy κ g)).add
      (hm.const_mul (σ ^ κ * energy g))).const_mul 2
    convert hi using 1
    ext z
    dsimp only [Pi.add_apply]
    ring
  have hfixed (z : ℝ) : (∫ t, |t| ^ κ * ‖g (t + σ * z)‖ ^ 2) ≤
      2 * (weightedEnergy κ g + σ ^ κ * |z| ^ κ * energy g) := by
    simpa only [hc, mul_assoc] using shifted_energy_le g κ (σ * z) hκ0 hκ2 h0 hκ
  have hnoise :
      (∫ z, 2 * (weightedEnergy κ g + σ ^ κ * |z| ^ κ * energy g)
        ∂gaussianReal 0 1) ≤
      2 * (weightedEnergy κ g + 2 * σ ^ κ * energy g) := by
    have hi : Integrable (fun z : ℝ => σ ^ κ * |z| ^ κ * energy g)
        (gaussianReal 0 1) := (hm.const_mul _).mul_const _
    rw [integral_const_mul, integral_add (integrable_const _) hi]
    simp only [integral_const, probReal_univ, one_smul,
      integral_mul_const, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hm2 (mul_nonneg hσk he)
    nlinarith
  unfold shiftedVariance
  calc
    _ ≤ 16 * ∫ t, |t| ^ κ *
        (∫ z, ‖g (t + σ * z)‖ ^ 2 ∂gaussianReal 0 1) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral ho (Filter.Eventually.of_forall hn)) (by norm_num)
    _ = 16 * ∫ z, (∫ t, |t| ^ κ * ‖g (t + σ * z)‖ ^ 2)
        ∂gaussianReal 0 1 := by
      congr 1
      simp_rw [← integral_const_mul]
      exact integral_integral_swap hjoint
    _ ≤ 16 * ∫ z, 2 * (weightedEnergy κ g + σ ^ κ * |z| ^ κ * energy g)
        ∂gaussianReal 0 1 :=
      mul_le_mul_of_nonneg_left
        (integral_mono hjoint.integral_prod_right hb hfixed) (by norm_num)
    _ ≤ 16 * (2 * (weightedEnergy κ g + 2 * σ ^ κ * energy g)) :=
      mul_le_mul_of_nonneg_left hnoise (by norm_num)
    _ = _ := by ring

end Causalean.Stat.Nonparametric
