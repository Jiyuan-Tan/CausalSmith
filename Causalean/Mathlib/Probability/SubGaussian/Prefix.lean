module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Integral of a capped Gaussian union tail

The first deterministic ingredient controls the maximum of at most `m`
sub-Gaussian coordinates sharing the same variance proxy.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory

/-- [A universal positive constant bounds the integrable clipped Gaussian union
tail by its scale times the square root of the logarithm of its number of
terms](goal).

Proof strategy: split the integral at `σ * sqrt (2 * log (2 * m))`.
Below the split use the bound by one.  Above it use the Gaussian tail
integral bound `∫_u^∞ exp(-t²/(2σ²)) dt ≤ (σ²/u) exp(-u²/(2σ²))`.
Simplify with `m ≥ 1`. -/
theorem clipped_gaussian_integral :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (σ : ℝ), 1 ≤ m → 0 < σ →
        let g : ℝ → ℝ := fun t =>
          min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))
        IntegrableOn g (Set.Ioi (0 : ℝ)) volume ∧
          ∫ t in Set.Ioi (0 : ℝ), g t ≤
            C * σ * Real.sqrt (1 + Real.log (m : ℝ)) := by
  refine ⟨Real.exp 4, Real.exp_pos _, ?_⟩
  intro m σ hm hσ
  dsimp
  let s : ℝ := Real.sqrt (1 + Real.log (m : ℝ))
  let r : ℝ := σ * s
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmreal
  have hsarg : 0 < 1 + Real.log (m : ℝ) := by linarith
  have hs : 0 < s := Real.sqrt_pos.2 hsarg
  have hs2 : s ^ 2 = 1 + Real.log (m : ℝ) := Real.sq_sqrt hsarg.le
  have hsge : 1 ≤ s ^ 2 := by rw [hs2]; linarith
  have hlogm : Real.log (2 * (m : ℝ)) ≤ s ^ 2 := by
    rw [hs2, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne']
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hr : 0 < r := mul_pos hσ hs
  have hb : 0 < (1 / (2 * σ ^ 2) : ℝ) := by positivity
  have hi : IntegrableOn
      (fun t : ℝ => 2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))
      (Set.Ioi (0 : ℝ)) volume := by
    have hgauss : IntegrableOn
        (fun t : ℝ => 2 * (m : ℝ) * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2))
        (Set.Ioi (0 : ℝ)) volume :=
      ((integrable_exp_neg_mul_sq hb).const_mul (2 * (m : ℝ))).integrableOn
    have hfun : (fun t : ℝ =>
        2 * (m : ℝ) * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2)) =
        (fun t : ℝ =>
          2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2))) := by
      funext t
      congr 1
      ring
    rw [hfun] at hgauss
    exact hgauss
  have hgi : IntegrableOn
      (fun t : ℝ => min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2))))
      (Set.Ioi (0 : ℝ)) volume := by
    apply hi.mono'
    · fun_prop
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _
  have ha : -(1 / r) < (0 : ℝ) := neg_lt_zero.mpr (by positivity)
  have heq : (fun t : ℝ => Real.exp (4 - t / r)) =
      (fun t : ℝ => Real.exp 4 * Real.exp ((-(1 / r)) * t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  have hei : IntegrableOn (fun t : ℝ => Real.exp (4 - t / r))
      (Set.Ioi (0 : ℝ)) volume := by
    rw [heq]
    exact (integrableOn_exp_mul_Ioi ha 0).const_mul _
  have heval : (∫ t in Set.Ioi (0 : ℝ), Real.exp (4 - t / r)) =
      Real.exp 4 * r := by
    rw [heq, integral_const_mul, integral_exp_mul_Ioi ha]
    simp
  have hpoint (t : ℝ) :
      min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2))) ≤
        Real.exp (4 - t / r) := by
    by_cases ht : t ≤ 4 * r
    · calc
        min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2))) ≤ 1 :=
          min_le_left _ _
        _ = Real.exp 0 := by simp
        _ ≤ Real.exp (4 - t / r) := Real.exp_le_exp.mpr (by
          have hdiv : t / r ≤ 4 := (div_le_iff₀ hr).2 (by nlinarith)
          linarith)
    · have hx : 4 ≤ t / r := (le_div_iff₀ hr).2 (by linarith)
      have hx2 : 0 ≤ (t / r) ^ 2 / 2 - 1 := by nlinarith
      have hprod : 0 ≤ (s ^ 2 - 1) * ((t / r) ^ 2 / 2 - 1) :=
        mul_nonneg (by linarith) hx2
      have hquad : s ^ 2 - s ^ 2 * (t / r) ^ 2 / 2 ≤ 4 - t / r := by
        nlinarith [sq_nonneg (t / r - 1)]
      have hid : t ^ 2 / (2 * σ ^ 2) = s ^ 2 * (t / r) ^ 2 / 2 := by
        dsimp [r]
        field_simp
      have hpos : 0 < 2 * (m : ℝ) := by positivity
      calc
        min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2))) ≤
            2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := min_le_right _ _
        _ = Real.exp (Real.log (2 * (m : ℝ)) - t ^ 2 / (2 * σ ^ 2)) := by
          simp [Real.exp_sub, Real.exp_log hpos, Real.exp_neg, div_eq_mul_inv]
        _ ≤ Real.exp (4 - t / r) := Real.exp_le_exp.mpr (by rw [hid]; linarith)
  refine ⟨hgi, ?_⟩
  calc
    (∫ t in Set.Ioi (0 : ℝ),
      min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * σ ^ 2)))) ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (4 - t / r) :=
      setIntegral_mono_ae hgi hei (Filter.Eventually.of_forall hpoint)
    _ = Real.exp 4 * σ * Real.sqrt (1 + Real.log (m : ℝ)) := by
      rw [heval]
      dsimp [r, s]
      ring

end Causalean.Mathlib.Probability.SubGaussian
