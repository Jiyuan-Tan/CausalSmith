module
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Piecewise

/-!
# Scalar gluing through two derivatives

The reusable gluing lemmas in this file assemble scalar branches with matching
value, first derivative, and second derivative at a single junction. They do not
assume that the branches agree on a neighborhood of the junction.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- [The join](goal) of [two scalar branches f and g](hyp:f,g) at [a junction
a](hyp:a), evaluated at [a point x](hyp:x), equals f(x) when x ≤ a and g(x)
otherwise. -/
noncomputable def joinAt (a : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then f x else g x

/-- [Continuous branches](hyp:hf,hg) with [matching junction values](hyp:hv)
have [a continuous join](goal) at [the junction](hyp:a). -/
theorem joinAt_continuous (a : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hv : f a = g a) :
    Continuous (joinAt a f g) := by
  apply hf.if (p := fun x => x ≤ a) _ hg
  intro x hx
  have hx' : x = a := by
    simpa only [show {x : ℝ | x ≤ a} = Set.Iic a from rfl,
      frontier_Iic, Set.mem_singleton_iff] using hx
  simpa only [hx'] using hv

/-- [Differentiable branches with specified derivative functions](hyp:hf,hg)
and [matching value and derivative](hyp:hv,hd) at [a junction](hyp:a) have
[the joined derivative at every point](goal).

At the junction, use the left/right slope criterion, or combine within-half-line
derivatives; away from it use eventual equality. No neighborhood equality of the
two branches is available or needed. -/
theorem joinAt_hasDerivAt (a : ℝ) {f g df dg : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a = g a) (hd : df a = dg a) (x : ℝ) :
    HasDerivAt (joinAt a f g) (joinAt a df dg x) x := by
  rcases lt_trichotomy x a with hxa | hEq | hax
  · simp only [joinAt, if_pos hxa.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxa] with y hy
    simp only [joinAt, if_pos (le_of_lt (Set.mem_Iio.mp hy))]
  · subst x
    simp only [joinAt, if_pos le_rfl]
    have hl : HasDerivWithinAt (joinAt a f g) (df a) (Set.Iic a) a :=
      (hf a).hasDerivWithinAt.congr
        (fun y hy => by simp only [joinAt, if_pos (Set.mem_Iic.mp hy)])
        (by simp only [joinAt, if_pos le_rfl])
    have hr : HasDerivWithinAt (joinAt a f g) (df a) (Set.Ioi a) a := by
      rw [hd]
      exact (hg a).hasDerivWithinAt.congr
        (fun y hy => by simp only [joinAt, if_neg (not_le_of_gt (Set.mem_Ioi.mp hy))])
        (by simpa only [joinAt, if_pos le_rfl] using hv)
    simpa only [Set.Iic_union_Ioi, hasDerivWithinAt_univ] using hl.union hr
  · simp only [joinAt, if_neg (not_le_of_gt hax)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hax] with y hy
    simp only [joinAt, if_neg (not_le_of_gt (Set.mem_Ioi.mp hy))]

/-- [Twice continuously differentiable scalar branches](hyp:hf,hg) whose
[value, first derivative, and second derivative match](hyp:hv,hd,hdd) at
[the junction](hyp:a) have [a globally twice continuously differentiable join](goal).

Apply `joinAt_hasDerivAt` twice and `joinAt_continuous` to the second
derivative, then use `contDiff_succ_iff_deriv` twice. -/
theorem joinAt_contDiff_two (a : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hv : f a = g a) (hd : deriv f a = deriv g a)
    (hdd : deriv (deriv f) a = deriv (deriv g) a) :
    ContDiff ℝ 2 (joinAt a f g) := by
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hg' : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have h₁ := joinAt_hasDerivAt a
    (fun x => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x => (hg.differentiable (by simp) x).hasDerivAt) hv hd
  have h₂ := joinAt_hasDerivAt a
    (fun x => (hf'.differentiable (by simp) x).hasDerivAt)
    (fun x => (hg'.differentiable (by simp) x).hasDerivAt) hd hdd
  have he₁ : deriv (joinAt a f g) = joinAt a (deriv f) (deriv g) :=
    funext fun x => (h₁ x).deriv
  have he₂ : deriv (joinAt a (deriv f) (deriv g)) =
      joinAt a (deriv (deriv f)) (deriv (deriv g)) :=
    funext fun x => (h₂ x).deriv
  apply (contDiff_succ_iff_deriv (n := 1)).2
  refine ⟨fun x => (h₁ x).differentiableAt, by simp, ?_⟩
  rw [he₁]
  apply contDiff_one_iff_deriv.2
  refine ⟨fun x => (h₂ x).differentiableAt, ?_⟩
  rw [he₂]
  exact joinAt_continuous a hf'.continuous_deriv_one hg'.continuous_deriv_one hdd

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
