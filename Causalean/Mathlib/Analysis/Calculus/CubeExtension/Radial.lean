module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Profiles
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RadialBase

/-!
# Odd tangent products with a complementary radial plateau

The mixed profile is the exact tangent odd product multiplied by the quintic
plateau of the complementary Euclidean radius. Its support is a coordinate cube
times a radius-two ball, and its global jets have dimension-dependent bounds.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- In [fixed tangent and complementary dimensions](hyp:t,c), [the mixed profile](goal)
at [a Euclidean coordinate vector](hyp:x) is [the tangent odd product multiplied
by the plateau of the complementary Euclidean norm](step:1). -/
noncomputable def mixedProfile {t c : ℕ} (x : EuclideanSpace ℝ (Fin t ⊕ Fin c)) : ℝ :=
  oddProduct (fun i => x (Sum.inl i)) *
    plateau ‖(WithLp.toLp 2 (fun i : Fin c => x (Sum.inr i)) : EuclideanSpace ℝ (Fin c))‖

/-- In [fixed dimensions](hyp:t,c), [the closed mixed support](goal) is
[the tangent coordinate cube times the complementary radius-two ball](step:1). -/
def mixedSupport (t c : ℕ) : Set (EuclideanSpace ℝ (Fin t ⊕ Fin c)) :=
  {x | (∀ i : Fin t, |x (Sum.inl i)| ≤ 1) ∧
    ‖(WithLp.toLp 2 (fun i : Fin c => x (Sum.inr i)) : EuclideanSpace ℝ (Fin c))‖ ≤ 2}

/-- [The mixed profile has compact support](goal) in [fixed dimensions](hyp:t,c). -/
-- Split the ambient space using `EuclideanSpace.sumEquivProd`. On the product,
-- use the compact set `tsupport oddEuclidean ×ˢ Metric.closedBall 0 2`,
-- then transfer it through the inverse homeomorphism. Outside this set either
-- the tangent factor is zero or `plateau_eq_zero` kills the radial factor.
-- Neither individual factor pulled back to the ambient space has compact
-- support in general: both coordinate projections can have nontrivial kernels.
theorem mixedProfile_hasCompactSupport {t c : ℕ} :
    HasCompactSupport (mixedProfile (t := t) (c := c)) := by
  let e : EuclideanSpace ℝ (Fin t ⊕ Fin c) ≃L[ℝ]
      EuclideanSpace ℝ (Fin t) × EuclideanSpace ℝ (Fin c) :=
    EuclideanSpace.sumEquivProd
  have hp : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin t) ×
      EuclideanSpace ℝ (Fin c) => oddEuclidean p.1 * plateau ‖p.2‖) := by
    apply HasCompactSupport.intro
      (K := tsupport (oddEuclidean (d := t)) ×ˢ Metric.closedBall 0 2)
      (oddEuclidean_hasCompactSupport.isCompact.prod (isCompact_closedBall _ _))
    intro p hp
    by_cases ht : p.1 ∈ tsupport (oddEuclidean (d := t))
    · have hc : p.2 ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin c)) 2 :=
        fun hc => hp ⟨ht, hc⟩
      have hr : ¬ ‖p.2‖ ≤ 2 := by simpa using hc
      rw [plateau_eq_zero _ (lt_of_not_ge hr).le, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  exact hp.comp_homeomorph e.toHomeomorph

/-- [The mixed profile is globally twice continuously differentiable](goal)
in [fixed dimensions](hyp:t,c). -/
-- Compose `oddEuclidean_contDiff` with the first continuous linear projection
-- of `EuclideanSpace.sumEquivProd`, and use `radialPlateau_contDiff` for the
-- second projection. Multiply the two C² functions and unfold only to identify
-- the exact existing formula. This reuses local constancy at projected zero.
-- Primary source: Mathlib/Analysis/InnerProductSpace/PiL2.lean, sumEquivProd,
-- and `radialPlateau_contDiff` for the norm composition.
theorem mixedProfile_contDiff {t c : ℕ} : ContDiff ℝ 2 (mixedProfile (t := t) (c := c)) := by
  let e : EuclideanSpace ℝ (Fin t ⊕ Fin c) ≃L[ℝ]
      EuclideanSpace ℝ (Fin t) × EuclideanSpace ℝ (Fin c) :=
    EuclideanSpace.sumEquivProd
  let P := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin t))
    (EuclideanSpace ℝ (Fin c))).comp e.toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin t))
    (EuclideanSpace ℝ (Fin c))).comp e.toContinuousLinearMap
  exact (oddEuclidean_contDiff.comp P.contDiff).mul (radialPlateau_contDiff Q)

/-- At [a point](hyp:x) [off the mixed closed support](hyp:hx) in
[fixed dimensions](hyp:t,c), [the value and both ambient jets vanish](goal). -/
-- Negating mixedSupport gives a strict tangent exterior coordinate or a strict
-- complementary radius > 2. Continuity keeps that strict inequality on a
-- neighborhood, where one factor vanishes. Apply `jets_zero_of_eventually_zero`
-- to the whole product, avoiding second-derivative product expansions.
-- Keep the t = 0 and c = 0 cases; no positive-dimension hypothesis is needed.
theorem mixedProfile_jets_zero {t c : ℕ} (x : EuclideanSpace ℝ (Fin t ⊕ Fin c))
    (hx : x ∉ mixedSupport t c) :
    mixedProfile x = 0 ∧ fderiv ℝ mixedProfile x = 0 ∧
      fderiv ℝ (fderiv ℝ (mixedProfile (t := t) (c := c))) x = 0 := by
  classical
  apply jets_zero_of_eventually_zero
  by_cases ht : ∀ i : Fin t, |x (Sum.inl i)| ≤ 1
  · let e : EuclideanSpace ℝ (Fin t ⊕ Fin c) ≃L[ℝ]
        EuclideanSpace ℝ (Fin t) × EuclideanSpace ℝ (Fin c) :=
      EuclideanSpace.sumEquivProd
    let Q := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin t))
      (EuclideanSpace ℝ (Fin c))).comp e.toContinuousLinearMap
    have hr : 2 < ‖Q x‖ := lt_of_not_ge (fun hr => hx ⟨ht, hr⟩)
    have hnear := Q.continuous.norm.continuousAt.eventually (Ioi_mem_nhds hr)
    filter_upwards [hnear] with y hy
    change 2 < ‖(WithLp.toLp 2 (fun i : Fin c => y (Sum.inr i)) :
      EuclideanSpace ℝ (Fin c))‖ at hy
    simp only [mixedProfile, plateau_eq_zero _ hy.le, mul_zero]
  · obtain ⟨i, hi⟩ := not_forall.mp ht
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin t ⊕ Fin c) =>
        |y (Sum.inl i)|) :=
      ((continuous_apply (Sum.inl i)).comp
        (EuclideanSpace.equiv (Fin t ⊕ Fin c) ℝ).continuous).abs
    have hnear := hcont.continuousAt.eventually (Ioi_mem_nhds (lt_of_not_ge hi))
    filter_upwards [hnear] with y hy
    have hz : oddProduct (fun j : Fin t => y (Sum.inl j)) = 0 :=
      (oddProduct_jets_zero _ (fun h => (not_le.mpr hy) (h i))).1
    simp only [mixedProfile, hz, zero_mul]

/-- For [every tangent dimension t and complementary dimension c](hyp:t,c)
[there is a constant C ≥ 1 such that the mixed profile is twice continuously
differentiable on the whole space and its absolute value, the operator norm of
its derivative and the operator norm of its second derivative are all at most C
at every point](goal). -/
theorem mixedProfile_jetBounds (t c : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ JetBounds (mixedProfile (t := t) (c := c)) C := by
  exact exists_jetBounds_of_compactSupport mixedProfile_contDiff mixedProfile_hasCompactSupport

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
