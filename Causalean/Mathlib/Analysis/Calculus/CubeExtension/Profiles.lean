module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Cutoff
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetBounds
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Odd products of exact coordinate cutoffs

The profile is coordinate zero times the product of all cutoffs in positive
dimension. In dimension zero it is defined to be zero. Both the sup-norm
coordinate space and its Euclidean counterpart are exposed.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- In [a finite dimension](hyp:d), [the closed coordinate support](goal) is
[the set where every coordinate has absolute value at most one](step:1). -/
def coordinateSupport (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i| ≤ 1}

/-- At [a coordinate vector](hyp:x) in [dimension](hyp:d), [the odd product profile](goal)
is [coordinate zero times all cutoffs in positive dimension, and zero in dimension zero](step:1). -/
noncomputable def oddProduct {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  if hd : 0 < d then x ⟨0, hd⟩ * ∏ i : Fin d, cutoff (x i) else 0

/-- At [a Euclidean vector](hyp:x) in [dimension](hyp:d), [the Euclidean odd profile](goal)
is [the same exact coordinate formula](step:1). -/
noncomputable def oddEuclidean {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  oddProduct (fun i => x i)

/-- [The dimension-zero odd profile is identically zero](goal). -/
theorem oddProduct_dim_zero : oddProduct (d := 0) = fun _ => 0 := by
  funext x
  simp [oddProduct]

/-- [The odd product changes sign under simultaneous coordinate negation](goal)
in [every dimension](hyp:d) at [every point](hyp:x). -/
theorem oddProduct_neg {d : ℕ} (x : Fin d → ℝ) : oddProduct (-x) = -oddProduct x := by
  by_cases hd : 0 < d
  · simp [oddProduct, hd, cutoff_neg]
  · simp [oddProduct, hd]

/-- [The odd product has compact support](goal) in [every finite dimension](hyp:d). -/
-- Reuse the cube argument of CubeExtension.productBump_hasCompactSupport:
-- `isCompact_pi_infinite (fun _ => isCompact_Icc)` and
-- `HasCompactSupport.intro`. Off the cube, one cutoff factor is zero.
-- The d = 0 branch is identically zero; do not introduce a positive-dimension premise.
theorem oddProduct_hasCompactSupport {d : ℕ} : HasCompactSupport (oddProduct (d := d)) := by
  classical
  apply HasCompactSupport.intro
    (K := {x : Fin d → ℝ | ∀ i, x i ∈ Set.Icc (-1) 1})
    (isCompact_pi_infinite (fun _ => isCompact_Icc))
  intro x hx
  have hx' : ¬∀ i, |x i| ≤ 1 := by
    simpa only [Set.mem_ofPred_eq, Set.mem_Icc, ← abs_le] using hx
  obtain ⟨i, hi⟩ := not_forall.mp hx'
  have hz : ∏ j : Fin d, cutoff (x j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [cutoff, hi])
  simp [oddProduct, hz]

/-- [The odd product is globally twice continuously differentiable](goal)
in [every finite dimension](hyp:d). -/
-- Split `0 < d`, then use `contDiff_prod`, `cutoff_contDiff.comp`,
-- the coordinate evaluation continuous linear maps, and `ContDiff.mul`.
theorem oddProduct_contDiff {d : ℕ} : ContDiff ℝ 2 (oddProduct (d := d)) := by
  classical
  change ContDiff ℝ 2 (fun x : Fin d → ℝ => oddProduct x)
  by_cases hd : 0 < d
  · simp only [oddProduct, dif_pos hd]
    apply ContDiff.mul
    · fun_prop
    · apply contDiff_prod
      intro i _
      exact cutoff_contDiff.comp (by fun_prop)
  · simpa only [oddProduct, dif_neg hd] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : Fin d → ℝ => (0 : ℝ)))

/-- At [a point](hyp:x) [off the closed coordinate support](hyp:hx) in
[dimension](hyp:d), [the value and both ambient jets vanish](goal). -/
-- Failure of closed coordinate support supplies a STRICT exterior coordinate.
-- Its continuous absolute value stays > 1 on a neighborhood; the product is
-- eventually zero there. Apply the closed `jets_zero_of_eventually_zero` helper.
theorem oddProduct_jets_zero {d : ℕ} (x : Fin d → ℝ) (hx : x ∉ coordinateSupport d) :
    oddProduct x = 0 ∧ fderiv ℝ oddProduct x = 0 ∧
      fderiv ℝ (fderiv ℝ (oddProduct (d := d))) x = 0 := by
  classical
  have hx' : ¬∀ i, |x i| ≤ 1 := hx
  obtain ⟨i, hi⟩ := not_forall.mp hx'
  have hcont : Continuous (fun y : Fin d → ℝ => |y i|) :=
    (continuous_apply i).abs
  have hnear : ∀ᶠ y in nhds x, 1 < |y i| :=
    hcont.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hi))
  apply jets_zero_of_eventually_zero
  filter_upwards [hnear] with y hy
  have hz : ∏ j : Fin d, cutoff (y j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [cutoff, not_le.mpr hy])
  simp [oddProduct, hz]

/-- [A dimension-dependent finite constant bounds all three global jets](goal)
of the odd product in [dimension](hyp:d). -/
theorem oddProduct_jetBounds (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ JetBounds (oddProduct (d := d)) C := by
  exact exists_jetBounds_of_compactSupport oddProduct_contDiff oddProduct_hasCompactSupport

/-- [The Euclidean odd product has compact support](goal) in [dimension](hyp:d). -/
-- `EuclideanSpace.equiv (Fin d) ℝ` is the existing continuous linear equivalence
-- to the coordinate sup-norm space. Transfer compact support via its homeomorphism.
theorem oddEuclidean_hasCompactSupport {d : ℕ} : HasCompactSupport (oddEuclidean (d := d)) := by
  exact oddProduct_hasCompactSupport.comp_homeomorph
    (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph

/-- [The Euclidean odd product is globally twice continuously differentiable](goal)
in [dimension](hyp:d). -/
-- Compose `oddProduct_contDiff` with `EuclideanSpace.equiv (Fin d) ℝ`.
-- Its coercion evaluates to the same coordinates as the unchanged definition.
theorem oddEuclidean_contDiff {d : ℕ} : ContDiff ℝ 2 (oddEuclidean (d := d)) := by
  exact oddProduct_contDiff.comp (EuclideanSpace.equiv (Fin d) ℝ).contDiff

/-- [All three Euclidean jets vanish](goal) at [a point](hyp:x) in [dimension](hyp:d)
[off its closed coordinate support](hyp:hx). -/
theorem oddEuclidean_jets_zero {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (hx : ¬∀ i, |x i| ≤ 1) :
    oddEuclidean x = 0 ∧ fderiv ℝ oddEuclidean x = 0 ∧
      fderiv ℝ (fderiv ℝ (oddEuclidean (d := d))) x = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => |y i|) :=
    ((continuous_apply i).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous).abs
  have hnear : ∀ᶠ y in nhds x, 1 < |y i| :=
    hcont.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hi))
  apply jets_zero_of_eventually_zero
  filter_upwards [hnear] with y hy
  have hz : ∏ j : Fin d, cutoff (y j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [cutoff, not_le.mpr hy])
  simp [oddEuclidean, oddProduct, hz]

/-- [A finite dimension-dependent constant bounds all Euclidean jets through order two](goal)
in [dimension](hyp:d). -/
theorem oddEuclidean_jetBounds (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ JetBounds (oddEuclidean (d := d)) C := by
  exact exists_jetBounds_of_compactSupport oddEuclidean_contDiff oddEuclidean_hasCompactSupport

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
