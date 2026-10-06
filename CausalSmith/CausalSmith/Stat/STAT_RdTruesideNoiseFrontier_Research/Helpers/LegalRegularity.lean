module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LegendreBlock
public import Mathlib.Analysis.Calculus.MeanValue


/-!
# Full-domain regularity of the tapered Legendre extension

Clamping to the polynomial interval preserves the derivative-based Lipschitz bound.
The unit bound and that Lipschitz bound give the required fractional seminorm.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The endpoint continuation is evaluation at the clamped, rescaled argument. Given [the displayed inputs and assumptions](hyp:hleg,b,m,hb,x), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_eq_clamp (hleg : ClassicalLegendreFacts) (b : ℝ) (m : ℕ)
    (hb : 0 < b) (x : ℝ) :
    legalExtension b m x = block m (max 0 (min 1 (x/b))) := by
  by_cases hx : x < 0
  · have hxb : x/b < 0 := div_neg_of_neg_of_pos hx hb
    simp [legalExtension, hx, min_eq_right (by linarith : x/b ≤ 1),
      max_eq_left hxb.le, block_zero hleg m]
  · by_cases hxb : x ≤ b
    · have h0 : 0 ≤ x/b := div_nonneg (le_of_not_gt hx) hb.le
      have h1 : x/b ≤ 1 := (div_le_one hb).mpr hxb
      simp [legalExtension, hx, hxb, min_eq_right h1, max_eq_right h0]
    · have h1 : 1 ≤ x/b := (le_div_iff₀ hb).mpr (by linarith)
      simp [legalExtension, hx, hxb, min_eq_left h1, block_one m]

/-- Clamping the argument puts it in the polynomial's unit interval. Given [the displayed inputs and assumptions](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma unitClamp_mem (z : ℝ) : max 0 (min 1 z) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The continuation retains the polynomial's uniform unit bound across both seams. Given [the displayed inputs and assumptions](hyp:hleg,b,m,hb,x), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_abs_le_one (hleg : ClassicalLegendreFacts) (b : ℝ) (m : ℕ)
    (hb : 0 < b) (x : ℝ) : |legalExtension b m x| ≤ 1 := by
  rw [legalExtension_eq_clamp hleg b m hb x]
  exact block_abs_le_one hleg m _ (unitClamp_mem _)

/-- The polynomial derivative bound extends across both constant pieces by clamping. Given [the displayed inputs and assumptions](hyp:hleg,b,m,hb,hm,x,t), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_sub_le (hleg : ClassicalLegendreFacts) (b : ℝ) (m : ℕ)
    (hb : 0 < b) (hm : 2 ≤ m) (x t : ℝ) :
    |legalExtension b m x - legalExtension b m t| ≤
      (7 * (m : ℝ)^2 / b) * |x-t| := by
  have hd : Differentiable ℝ (block m) := by
    change Differentiable ℝ (fun t => (1-t) * (blockNorm m)⁻¹ * legendreBlockSum m t)
    fun_prop
  have hp := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Icc (0 : ℝ) 1) => hd z)
    (fun z hz => by simpa only [Real.norm_eq_abs] using block_deriv_bound hleg m hm z hz)
    (convex_Icc (0 : ℝ) 1) (unitClamp_mem (t/b)) (unitClamp_mem (x/b))
  have hc : |max 0 (min 1 (x/b)) - max 0 (min 1 (t/b))| ≤ |x-t|/b := by
    calc
      _ ≤ |min 1 (x/b) - min 1 (t/b)| := by
        simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (min 1 (x/b) - min 1 (t/b)))] using
          abs_max_sub_max_le_max (0 : ℝ) (min 1 (x/b)) 0 (min 1 (t/b))
      _ ≤ |x/b-t/b| := by
        simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x/b - t/b))] using
          abs_min_sub_min_le_max (1 : ℝ) (x/b) 1 (t/b)
      _ = _ := by rw [← sub_div, abs_div, abs_of_pos hb]
  rw [legalExtension_eq_clamp hleg b m hb x, legalExtension_eq_clamp hleg b m hb t]
  calc
    _ ≤ 7 * (m : ℝ)^2 * |max 0 (min 1 (x/b)) - max 0 (min 1 (t/b))| := by
      simpa only [Real.norm_eq_abs] using hp
    _ ≤ 7 * (m : ℝ)^2 * (|x-t|/b) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- The unit and Lipschitz bounds imply the full-domain Hölder bound at every legal exponent. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_holder_bound (hleg : ClassicalLegendreFacts) (β b : ℝ) (m : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : 0 < b) (hm : 2 ≤ m) :
    holderSeminorm β (legalExtension b m) ≤
      ENNReal.ofReal (7 * (b/(m : ℝ)^2) ^ (-β)) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let A : ℝ := (m : ℝ)^2 / b
  have hA : 0 < A := by dsimp [A]; positivity
  have hscale : A ^ β = (b/(m : ℝ)^2) ^ (-β) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    congr 1
    dsimp [A]
    field_simp
  unfold holderSeminorm
  apply sSup_le
  rintro r ⟨x, hx, t, ht, hxt, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  have hd : 0 < |x-t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
  have hprod : 0 < A * |x-t| := mul_pos hA hd
  have hpow : (A * |x-t|)^β = A^β * |x-t|^β := Real.mul_rpow hA.le hd.le
  have hbound : |legalExtension b m x - legalExtension b m t| ≤
      7 * (A * |x-t|)^β := by
    by_cases hsmall : A * |x-t| ≤ 1
    · have hinterp : A * |x-t| ≤ (A * |x-t|)^β := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge hprod hsmall hβ.2
      calc
        _ ≤ 7 * (A * |x-t|) := by
          simpa only [A, mul_div_assoc, mul_assoc] using legalExtension_sub_le hleg b m hb hm x t
        _ ≤ _ := mul_le_mul_of_nonneg_left hinterp (by norm_num)
    · have hlarge : 1 ≤ (A * |x-t|)^β :=
        Real.one_le_rpow (le_of_not_ge hsmall) hβ.1.le
      have hunit : |legalExtension b m x - legalExtension b m t| ≤ 2 := by
        calc
          _ ≤ |legalExtension b m x| + |legalExtension b m t| := abs_sub _ _
          _ ≤ 1+1 := add_le_add (legalExtension_abs_le_one hleg b m hb x)
            (legalExtension_abs_le_one hleg b m hb t)
          _ = 2 := by norm_num
      linarith
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hd β)).mpr
  rw [← hscale, mul_assoc, ← hpow]
  exact hbound

end CausalSmith.Stat.RdTruesideNoiseFrontier
