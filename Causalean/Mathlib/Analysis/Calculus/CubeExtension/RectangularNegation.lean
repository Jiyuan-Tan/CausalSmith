module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularAffineJets

/-!
# Intrinsic rectangular jets under coordinate negation

Negating every coordinate exchanges the lower and upper faces of a closed
box. The within-box jets transform with the usual order-dependent sign,
which lets the lower-face reflection theorem handle upper faces as well.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- [A point x lies in the coordinatewise negated box, with corners −hi and −lo,
exactly when −x lies in the original box with corners lo and hi](goal). -/
theorem mem_rectBox_neg_iff {d : ℕ} (lo hi : Fin d → ℝ)
    (x : Fin d → ℝ) :
    x ∈ rectBox (fun i => -hi i) (fun i => -lo i) ↔
      -x ∈ rectBox lo hi := by
  constructor <;> intro hx i
  · have h := hx i
    change -hi i ≤ x i ∧ x i ≤ -lo i at h
    change lo i ≤ -x i ∧ -x i ≤ hi i
    constructor <;> linarith
  · have h := hx i
    change lo i ≤ -x i ∧ -x i ≤ hi i at h
    change -hi i ≤ x i ∧ x i ≤ -lo i
    constructor <;> linarith

/-- If [the box with corners lo, hi has positive side lengths](hyp:hbox), then
at [every point x of the negated box](hyp:hx) [the order-j intrinsic coordinate
jet on the negated box of the response z ↦ u(−z) equals (−1)^j times the
corresponding intrinsic jet of u on the original box at −x](goal), including on
the faces of the box.

Use `LinearIsometryEquiv.neg` and its `iteratedFDerivWithin_comp_right`
identity. The map sends the negated box to the original box by
`mem_rectBox_neg_iff`; evaluation on basis vectors gives one negative sign
per coordinate direction. -/
theorem coordJetOn_rectBox_neg {d j : ℕ}
    (lo hi : Fin d → ℝ) (hbox : ∀ i, lo i < hi i)
    (u : (Fin d → ℝ) → ℝ) (f : Fin j → Fin d)
    {x : Fin d → ℝ}
    (hx : x ∈ rectBox (fun i => -hi i) (fun i => -lo i)) :
    coordJetOn (rectBox (fun i => -hi i) (fun i => -lo i)) j
        (fun z => u (-z)) f x =
      (-1 : ℝ) ^ j * coordJetOn (rectBox lo hi) j u f (-x) := by
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
  have he (z : Fin d → ℝ) : e z = -z := by simp [e]
  have hpre : e ⁻¹' rectBox lo hi =
      rectBox (fun i => -hi i) (fun i => -lo i) := by
    ext z
    change e z ∈ rectBox lo hi ↔
      z ∈ rectBox (fun i => -hi i) (fun i => -lo i)
    rw [he]
    exact (mem_rectBox_neg_iff lo hi z).symm
  have hx' : e x ∈ rectBox lo hi := by
    rw [he]
    exact (mem_rectBox_neg_iff lo hi x).mp hx
  unfold coordJetOn
  rw [← hpre]
  change iteratedFDerivWithin ℝ j (u ∘ e) (e ⁻¹' rectBox lo hi) x
    (fun k => Pi.single (f k) 1) = _
  rw [e.iteratedFDerivWithin_comp_right u
    (uniqueDiffOn_rectBox lo hi hbox) hx' j]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  have hb (k : Fin j) : e (Pi.single (f k) (1 : ℝ)) =
      (-1 : ℝ) • Pi.single (f k) (1 : ℝ) := by
    rw [he]
    simp
  simp only [hb]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const, smul_eq_mul, he]

/-- If [the box with corners lo, hi has positive side lengths](hyp:hbox) and [a
response u lies in the intrinsic Hölder ball of order m, exponent s and radius L
on the box](hyp:hu), then [the response x ↦ u(−x) lies in the intrinsic Hölder
ball with the same order, exponent and radius on the negated box](goal). All
bounds use within-box jets, so the claim applies to any ambient representative
of the original response.

Apply `coordJetOn_rectBox_neg` to each derivative bound and both points in
the top-order modulus. Negation preserves distances; its sign has absolute
value one. Regularity follows by composing with the smooth negation map. -/
theorem holderBallOn_rectBox_neg {d m : ℕ}
    (lo hi : Fin d → ℝ) (hbox : ∀ i, lo i < hi i)
    (s L : ℝ) (u : (Fin d → ℝ) → ℝ)
    (hu : HolderBallOn (rectBox lo hi) m s L u) :
    HolderBallOn (rectBox (fun i => -hi i) (fun i => -lo i))
      m s L (fun x => u (-x)) := by
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
  have he (z : Fin d → ℝ) : e z = -z := by simp [e]
  have hmap : ∀ z ∈ rectBox (fun i => -hi i) (fun i => -lo i),
      e z ∈ rectBox lo hi := by
    intro z hz
    rw [he]
    exact (mem_rectBox_neg_iff lo hi z).mp hz
  refine ⟨?_, ?_, ?_⟩
  · have hc := hu.regularity.comp e.contDiff.contDiffOn hmap
    simpa only [Function.comp_def, he] using hc
  · intro j hj f x hx
    rw [coordJetOn_rectBox_neg lo hi hbox u f hx]
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      hu.derivBound j hj f (-x) ((mem_rectBox_neg_iff lo hi x).mp hx)
  · intro f x hx y hy
    rw [coordJetOn_rectBox_neg lo hi hbox u f hx,
      coordJetOn_rectBox_neg lo hi hbox u f hy]
    have hxy : ‖(-x) - (-y)‖ = ‖x - y‖ := by
      rw [show (-x) - (-y) = -(x - y) by abel, norm_neg]
    calc
      |(-1 : ℝ) ^ m * coordJetOn (rectBox lo hi) m u f (-x) -
          (-1 : ℝ) ^ m * coordJetOn (rectBox lo hi) m u f (-y)| =
          |coordJetOn (rectBox lo hi) m u f (-x) -
            coordJetOn (rectBox lo hi) m u f (-y)| := by
              rw [← mul_sub, abs_mul]
              simp
      _ ≤ L * ‖(-x) - (-y)‖ ^ s :=
        hu.modulus f (-x) ((mem_rectBox_neg_iff lo hi x).mp hx)
          (-y) ((mem_rectBox_neg_iff lo hi y).mp hy)
      _ = L * ‖x - y‖ ^ s := by rw [hxy]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
