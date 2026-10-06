module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic

/-! Algebraic bounds for the exact coordinate Hölder norm used by the marked priors. -/

public section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
variable {d : ℕ}

/-- Scalar multiplication commutes with each continuous coordinate partial on the cube.  Given [the specified input f](hyp:f), [the specified input a](hyp:a), [the specified input N](hyp:N), [the specified input hf](hyp:hf), [the multi-index](hyp:κ), [its order bound](hyp:hκ), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the coordinate partial const mul conclusion](goal) holds. -/
lemma coordinatePartial_const_mul (f : Cov d → ℝ) (a : ℝ) (N : ℕ)
    (hf : ContDiffOn ℝ N f (cube d)) (κ : Fin d → ℕ)
    (hκ : multiOrder κ ≤ N) (x : Cov d) (hx : x ∈ cube d) :
    coordinatePartial (fun x => a * f x) κ x = a * coordinatePartial f κ x := by
  unfold coordinatePartial
  change (iteratedFDerivWithin ℝ (multiOrder κ) (a • f) (cube d) x) _ = _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (by exact_mod_cast hκ)) x hx) (uniqueDiffOn_cube d) hx]
  rfl

/-- A finite Hölder bound scales by the absolute value of a scalar.  Given [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input A](hyp:A), [the specified input a](hyp:a), [the specified input hA](hyp:hA), [the specified input hf](hyp:hf), [the holder norm const mul bound conclusion](goal) holds. -/
lemma holderNorm_const_mul_bound (f : Cov d → ℝ) (s A a : ℝ)
    (hA : 0 ≤ A) (hf : holderNorm f s ≤ ENNReal.ofReal A) :
    holderNorm (fun x => a * f x) s ≤ ENNReal.ofReal (|a| * A) := by
  have h := (holderNorm_le_iff f s A hA).mp hf
  apply (holderNorm_le_iff _ s (|a| * A) (mul_nonneg (abs_nonneg _) hA)).mpr
  refine ⟨contDiffOn_const.mul h.1, ?_, ?_⟩
  · intro κ hκ x hx
    rw [coordinatePartial_const_mul f a _ h.1 κ hκ x hx, abs_mul]
    exact mul_le_mul_of_nonneg_left (h.2.1 κ hκ x hx) (abs_nonneg a)
  · intro κ hκ x hx y hy hxy
    rw [coordinatePartial_const_mul f a _ h.1 κ hκ.le x hx,
      coordinatePartial_const_mul f a _ h.1 κ hκ.le y hy, ← mul_sub, abs_mul]
    calc
      _ ≤ |a| * (A * dist x y ^ (s - (Nat.ceil s - 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left (h.2.2 κ hκ x hx y hy hxy) (abs_nonneg a)
      _ = _ := by ring

/-- Constant functions have Hölder norm at most their absolute value, at every order.  Given [the specified input c](hyp:c), [the specified input s](hyp:s), [the holder norm const bound conclusion](goal) holds. -/
lemma holderNorm_const_bound (c s : ℝ) :
    holderNorm (fun _ : Cov d => c) s ≤ ENNReal.ofReal |c| := by
  have hc (k : ℕ) (v : Fin k → Cov d) (x : Cov d) :
      (iteratedFDerivWithin ℝ k (fun _ : Cov d => c) (cube d) x) v =
        if k = 0 then c else 0 := by
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDerivWithin_const_of_ne (Nat.succ_ne_zero k)]
  have hp (κ : Fin d → ℕ) (x : Cov d) :
      coordinatePartial (fun _ : Cov d => c) κ x = if multiOrder κ = 0 then c else 0 :=
    hc _ _ x
  apply (holderNorm_le_iff _ s |c| (abs_nonneg _)).mpr
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · intro κ hκ x hx
    rw [hp]
    split_ifs <;> simp
  · intro κ hκ x hx y hy hxy
    rw [hp, hp, sub_self, abs_zero]
    positivity

/-- Adding two finite Hölder bounds adds their radii.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input s](hyp:s), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the holder norm add bound conclusion](goal) holds. -/
lemma holderNorm_add_bound (f g : Cov d → ℝ) (s A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : holderNorm f s ≤ ENNReal.ofReal A)
    (hg : holderNorm g s ≤ ENNReal.ofReal B) :
    holderNorm (fun x => f x + g x) s ≤ ENNReal.ofReal (A + B) := by
  exact (holderNorm_add_le f g s).trans
    ((add_le_add hf hg).trans_eq (ENNReal.ofReal_add hA hB).symm)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
