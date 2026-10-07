module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic

/-!
# Geometry of affine maps between closed rectangular boxes

For boxes with positive side lengths, a point lies in the source box exactly
when the coordinatewise affine map sends it into the target box. The map's
distance distortion also controls every real power of the distance, including
negative exponents.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- [The closed coordinate box](goal) with [lower corner lo and upper corner
hi](hyp:lo,hi) is the set of points whose i-th coordinate lies in
`[lo i, hi i]` for every i. -/
def rectBox {d : ℕ} (lo hi : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (lo i) (hi i)}

/-- [The coordinatewise affine map](goal) from [the box with corners lo, hi to
the box with corners lo', hi'](hyp:lo,hi,lo',hi') sends [a point x](hyp:x) to the
point whose i-th coordinate is lo'_i + (hi'_i − lo'_i)/(hi_i − lo_i)·(x_i − lo_i).
It carries the first box onto the second when both have positive side lengths. -/
noncomputable def rectAffine {d : ℕ} (lo hi lo' hi' : Fin d → ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => lo' i + (hi' i - lo' i) / (hi i - lo i) * (x i - lo i)

/-- If [the box with corners lo and hi has strictly positive side
lengths](hyp:h), then [it has unique within-set derivatives at every point,
including its faces](goal). -/
theorem uniqueDiffOn_rectBox {d : ℕ} (lo hi : Fin d → ℝ)
    (h : ∀ i, lo i < hi i) : UniqueDiffOn ℝ (rectBox lo hi) := by
  have hbox : rectBox lo hi = Set.univ.pi (fun i : Fin d => Set.Icc (lo i) (hi i)) := by
    ext x
    simp [rectBox, Pi.le_def, forall_and]
  rw [hbox]
  exact UniqueDiffOn.pi (fun i _ => uniqueDiffOn_Icc (h i))

/-- If [the source box with corners lo, hi](hyp:hsource) and [the target box with
corners lo', hi' both have positive side lengths](hyp:htarget), then [a point lies
in the source box exactly when its image under the coordinatewise affine map
lies in the target box](goal).

For each coordinate, cancel the positive source width and compare the two
endpoint inequalities. The reverse implication needs positivity of the target
width as well. -/
theorem rectAffine_preimage_rectBox {d : ℕ}
    (lo hi lo' hi' : Fin d → ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i) :
    rectAffine lo hi lo' hi' ⁻¹' rectBox lo' hi' = rectBox lo hi := by
  ext x
  simp only [Set.mem_preimage, rectBox, Set.mem_ofPred_eq]
  constructor <;> intro hx i
  · have hs : 0 < hi i - lo i := sub_pos.mpr (hsource i)
    have ht : 0 < hi' i - lo' i := sub_pos.mpr (htarget i)
    have ha : 0 < (hi' i - lo' i) / (hi i - lo i) := div_pos ht hs
    have heq : (hi' i - lo' i) / (hi i - lo i) * (hi i - lo i) =
        hi' i - lo' i := div_mul_cancel₀ _ hs.ne'
    have h := hx i
    change lo' i ≤ lo' i + (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) ∧
      lo' i + (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) ≤ hi' i at h
    constructor
    · have : 0 ≤ (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) := by linarith [h.1]
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp this)
    · have : (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) ≤
          (hi' i - lo' i) / (hi i - lo i) * (hi i - lo i) := by linarith [h.2]
      exact sub_nonneg.mp (by nlinarith [(mul_le_mul_iff_of_pos_left ha).mp this])
  · have hs : 0 < hi i - lo i := sub_pos.mpr (hsource i)
    have ht : 0 < hi' i - lo' i := sub_pos.mpr (htarget i)
    have ha : 0 < (hi' i - lo' i) / (hi i - lo i) := div_pos ht hs
    have heq : (hi' i - lo' i) / (hi i - lo i) * (hi i - lo i) =
        hi' i - lo' i := div_mul_cancel₀ _ hs.ne'
    have h := hx i
    change lo i ≤ x i ∧ x i ≤ hi i at h
    change lo' i ≤ lo' i + (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) ∧
      lo' i + (hi' i - lo' i) / (hi i - lo i) * (x i - lo i) ≤ hi' i
    constructor
    · have := mul_nonneg ha.le (sub_nonneg.mpr h.1)
      linarith
    · have := (mul_le_mul_iff_of_pos_left ha).mpr (sub_le_sub_right h.2 (lo i))
      linarith

/-- If [the source box](hyp:hsource) and [the target box both have positive side
lengths](hyp:htarget), then for [any real power s](hyp:s) [there is a positive
constant C such that the s-th power of the distance between the images of any
two points under the coordinatewise affine map is at most C times the s-th power
of the distance between the points](goal).

Use the upper Lipschitz bound when `0 ≤ s` and the lower Lipschitz bound when
`s < 0`. At `x = y`, both sides are zero in Lean's real-power convention. -/
theorem exists_rectAffine_rpow_constant {d : ℕ}
    (lo hi lo' hi' : Fin d → ℝ) (s : ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin d → ℝ,
      ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ ^ s
        ≤ C * ‖x - y‖ ^ s := by
  let a : Fin d → ℝ := fun i => (hi' i - lo' i) / (hi i - lo i)
  have ha : ∀ i, 0 < a i := fun i => div_pos (sub_pos.mpr (htarget i))
    (sub_pos.mpr (hsource i))
  let K : ℝ := 1 + ∑ i : Fin d, (a i + (a i)⁻¹)
  have hK : 0 < K := by
    dsimp [K]
    have : 0 ≤ ∑ i : Fin d, (a i + (a i)⁻¹) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (ha i).le (inv_nonneg.mpr (ha i).le))
    linarith
  have haK : ∀ i, a i ≤ K := by
    intro i
    have hsum : a i + (a i)⁻¹ ≤ ∑ j : Fin d, (a j + (a j)⁻¹) :=
      Finset.single_le_sum (fun j _ => add_nonneg (ha j).le
        (inv_nonneg.mpr (ha j).le)) (Finset.mem_univ i)
    dsimp [K]
    have := inv_nonneg.mpr (ha i).le
    linarith
  have hainvK : ∀ i, (a i)⁻¹ ≤ K := by
    intro i
    have hsum : a i + (a i)⁻¹ ≤ ∑ j : Fin d, (a j + (a j)⁻¹) :=
      Finset.single_le_sum (fun j _ => add_nonneg (ha j).le
        (inv_nonneg.mpr (ha j).le)) (Finset.mem_univ i)
    dsimp [K]
    linarith [ha i]
  have hcoord (x y : Fin d → ℝ) (i : Fin d) :
      (rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y) i =
        a i * ((x - y) i) := by
    simp only [Pi.sub_apply, rectAffine]
    dsimp [a]
    ring
  have hforward (x y : Fin d → ℝ) :
      ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ ≤ K * ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK.le (norm_nonneg _))).2
    intro i
    rw [hcoord, norm_mul, Real.norm_eq_abs, abs_of_pos (ha i)]
    exact (mul_le_mul_of_nonneg_right (haK i) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) i) hK.le)
  have hreverse (x y : Fin d → ℝ) :
      ‖x - y‖ ≤ K * ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK.le (norm_nonneg _))).2
    intro i
    have heq : (x - y) i = (a i)⁻¹ *
        (rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y) i := by
      rw [hcoord]
      field_simp [ne_of_gt (ha i)]
    rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha i))]
    exact (mul_le_mul_of_nonneg_right (hainvK i) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        (norm_le_pi_norm (rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y) i)
        hK.le)
  by_cases hs : 0 ≤ s
  · refine ⟨K ^ s, Real.rpow_pos_of_pos hK _, ?_⟩
    intro x y
    calc
      ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ ^ s ≤
          (K * ‖x - y‖) ^ s :=
        Real.rpow_le_rpow (norm_nonneg _) (hforward x y) hs
      _ = K ^ s * ‖x - y‖ ^ s := Real.mul_rpow hK.le (norm_nonneg _)
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    refine ⟨(K⁻¹) ^ s, Real.rpow_pos_of_pos (inv_pos.mpr hK) _, ?_⟩
    intro x y
    by_cases hxy : x = y
    · subst y
      simp [Real.zero_rpow (lt_of_not_ge hs).ne]
    · have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hnorm' : 0 < ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ := by
        have := hreverse x y
        nlinarith [norm_nonneg (rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y)]
      have hlow : K⁻¹ * ‖x - y‖ ≤
          ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ := by
        rw [inv_mul_le_iff₀ hK]
        exact hreverse x y
      calc
        ‖rectAffine lo hi lo' hi' x - rectAffine lo hi lo' hi' y‖ ^ s ≤
            (K⁻¹ * ‖x - y‖) ^ s :=
          Real.rpow_le_rpow_of_nonpos (mul_pos (inv_pos.mpr hK) hnorm) hlow hs'
        _ = (K⁻¹) ^ s * ‖x - y‖ ^ s :=
          Real.mul_rpow (inv_pos.mpr hK).le (norm_nonneg _)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
