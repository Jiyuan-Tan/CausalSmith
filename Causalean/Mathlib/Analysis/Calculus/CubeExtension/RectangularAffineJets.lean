module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularAffineGeometry

/-!
# Intrinsic jets under a rectangular affine change of variables

These identities isolate the chain rule needed to transport an intrinsic
Hölder ball between fixed nondegenerate boxes. The derivatives are taken
within the corresponding boxes, including at their faces.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped Pointwise

/-- If [the source box with corners lo, hi](hyp:hsource) and [the target box with
corners lo', hi' both have positive side lengths](hyp:htarget), then [there is a
continuous linear equivalence e that multiplies coordinate i by
(hi'_i − lo'_i)/(hi_i − lo_i), and the coordinatewise affine map between the
boxes equals e followed by translation by the vector with i-th coordinate
lo'_i − (hi'_i − lo'_i)/(hi_i − lo_i)·lo_i](goal). -/
theorem exists_rectAffine_linearEquiv {d : ℕ}
    (lo hi lo' hi' : Fin d → ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i) :
    ∃ e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ),
      (∀ x i, e x i = (hi' i - lo' i) / (hi i - lo i) * x i) ∧
      (∀ x, rectAffine lo hi lo' hi' x =
        e x + (fun i => lo' i -
          (hi' i - lo' i) / (hi i - lo i) * lo i)) := by
  /- Build the diagonal linear equivalence from the positive scalars and
  their inverses, with continuity from finite-dimensionality. The final
  identity follows by coordinate extensionality and `ring`. -/
  let a : Fin d → ℝ := fun i => (hi' i - lo' i) / (hi i - lo i)
  have ha (i : Fin d) : a i ≠ 0 :=
    ne_of_gt (div_pos (sub_pos.mpr (htarget i)) (sub_pos.mpr (hsource i)))
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.piCongrRight
      (fun i => (LinearEquiv.smulOfNeZero ℝ ℝ (a i) (ha i)).toContinuousLinearEquiv)
  refine ⟨e, ?_, ?_⟩
  · intro x i
    simp [e, a]
  · intro x
    funext i
    simp only [Pi.add_apply, rectAffine, e, ContinuousLinearEquiv.piCongrRight_apply,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      smul_eq_mul]
    dsimp [a]
    ring

/-- If [the source box](hyp:hsource) and [the target box both have positive side
lengths](hyp:htarget) and [a response u is m times continuously differentiable
within the target box](hyp:hu), then [its pullback along the coordinatewise
affine map is m times continuously differentiable within the source
box](goal). -/
theorem contDiffOn_rectAffine {d m : ℕ}
    (lo hi lo' hi' : Fin d → ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i)
    {u : (Fin d → ℝ) → ℝ}
    (hu : ContDiffOn ℝ m u (rectBox lo' hi')) :
    ContDiffOn ℝ m (fun x => u (rectAffine lo hi lo' hi' x))
      (rectBox lo hi) := by
  obtain ⟨e, _, he⟩ :=
    exists_rectAffine_linearEquiv lo hi lo' hi' hsource htarget
  let c : Fin d → ℝ := fun i => lo' i -
    (hi' i - lo' i) / (hi i - lo i) * lo i
  have hmap : ContDiff ℝ m (fun x : Fin d → ℝ => e x + c) :=
    e.contDiff.add contDiff_const
  have hcomp : ContDiffOn ℝ m
      (u ∘ fun x : Fin d → ℝ => e x + c) (rectBox lo hi) :=
    hu.comp hmap.contDiffOn (by
      intro x hx
      change e x + c ∈ rectBox lo' hi'
      have hx' : rectAffine lo hi lo' hi' x ∈ rectBox lo' hi' := by
        exact (Set.ext_iff.mp
          (rectAffine_preimage_rectBox lo hi lo' hi' hsource htarget) x).2 hx
      simpa only [he] using hx')
  convert hcomp using 1
  funext x
  simp only [Function.comp_def, he]
  rfl

/-- If [the source box with corners lo, hi](hyp:hsource) and [the target box with
corners lo', hi' both have positive side lengths](hyp:htarget), then at [any point
x of the source box](hyp:hx), including boundary points, [each order-j intrinsic
coordinate jet on the source box of the pullback of a response u along the
coordinatewise affine map, in directions f(0), …, f(j − 1), equals the product
over k of the scale factors (hi'_{f(k)} − lo'_{f(k)})/(hi_{f(k)} − lo_{f(k)})
times the corresponding intrinsic jet of u on the target box at the image of
x](goal). -/
theorem coordJetOn_rectAffine {d j : ℕ}
    (lo hi lo' hi' : Fin d → ℝ)
    (hsource : ∀ i, lo i < hi i)
    (htarget : ∀ i, lo' i < hi' i)
    (u : (Fin d → ℝ) → ℝ) (f : Fin j → Fin d)
    {x : Fin d → ℝ} (hx : x ∈ rectBox lo hi) :
    coordJetOn (rectBox lo hi) j
        (fun z => u (rectAffine lo hi lo' hi' z)) f x =
      (∏ k : Fin j, (hi' (f k) - lo' (f k)) /
        (hi (f k) - lo (f k))) *
        coordJetOn (rectBox lo' hi') j u f
          (rectAffine lo hi lo' hi' x) := by
  /- The diagonal linear map is invertible by positive side lengths. Apply
  `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`, with Mathlib's
  translation rule, then evaluate on the basis directions and factor each
  scalar by multilinearity. Rewrite the domain using
  `rectAffine_preimage_rectBox`. No regularity premise is needed for the
  equivalence chain rule. -/
  obtain ⟨e, he, hfa⟩ :=
    exists_rectAffine_linearEquiv lo hi lo' hi' hsource htarget
  let c : Fin d → ℝ := fun i => lo' i -
    (hi' i - lo' i) / (hi i - lo i) * lo i
  let a : Fin d → ℝ := e.symm c
  have hea (z : Fin d → ℝ) : e (z + a) = rectAffine lo hi lo' hi' z := by
    rw [map_add, show e a = c from e.apply_symm_apply c, ← hfa]
  have hT : a +ᵥ rectBox lo hi = e ⁻¹' rectBox lo' hi' := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem,
      ← rectAffine_preimage_rectBox lo hi lo' hi' hsource htarget]
    change rectAffine lo hi lo' hi' (-a + z) ∈ rectBox lo' hi' ↔
      e z ∈ rectBox lo' hi'
    rw [← hea]
    rw [show -a + z + a = z by abel]
  have hx' : e (x + a) ∈ rectBox lo' hi' := by
    rw [hea]
    exact (Set.ext_iff.mp
      (rectAffine_preimage_rectBox lo hi lo' hi' hsource htarget) x).2 hx
  unfold coordJetOn
  have htrans := iteratedFDerivWithin_comp_add_right
    (𝕜 := ℝ) (s := rectBox lo hi) (f := fun z => u (e z)) j a x
  rw [hT] at htrans
  rw [show (fun z => u (rectAffine lo hi lo' hi' z)) =
      (fun z => u (e (z + a))) from funext (fun z => by rw [hea]), htrans]
  change iteratedFDerivWithin ℝ j
    (u ∘ (e : (Fin d → ℝ) → (Fin d → ℝ)))
    (e ⁻¹' rectBox lo' hi') (x + a)
    (fun k => Pi.single (f k) 1) = _
  rw [e.iteratedFDerivWithin_comp_right u
    (Causalean.Mathlib.Analysis.Calculus.CubeExtension.uniqueDiffOn_rectBox
      lo' hi' htarget) hx' j]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  have hb (k : Fin j) : e (Pi.single (f k) (1 : ℝ)) =
      ((hi' (f k) - lo' (f k)) / (hi (f k) - lo (f k))) •
        Pi.single (f k) (1 : ℝ) := by
    ext i
    by_cases h : i = f k <;>
      simp [he, Pi.smul_apply, smul_eq_mul, h]
  simp only [hb]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, hea]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
