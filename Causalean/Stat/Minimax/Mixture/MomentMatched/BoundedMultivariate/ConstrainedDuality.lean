module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.FeatureSeparation
public import Mathlib

/-!
# Finite constrained moment duality

A positive uniform approximation error against a finite family of continuous
functions yields two finitely supported probability measures that match every
constraint and separate the target. This is the functional-analytic step needed
when the approximation space contains an inverse power as well as polynomials.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- The image of the compact interval under the joint feature map is compact.
  Its convex hull is compact in the finite-dimensional product. If no two
  convex-hull points with identical constraint coordinates have target
  coordinates separated by δ, separation of two disjoint translates gives
  an affine constraint approximant with uniform error below δ. -/

/-- A [nondegenerate interval](hyp:hrs), [positive gap](hyp:hδ), [target function and finite constraint family](hyp:f,g), [their interval continuity](hyp:hf,hg), and [a uniform affine approximation gap](hyp:hgap) yield [two joint feature-hull points that match every constraint while separating the target by the gap](goal). -/
theorem exists_matching_convexHull_features_of_gap
    {m : ℕ} {r s δ : ℝ} (hrs : r < s) (hδ : 0 < δ)
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc r s))
    (hg : ∀ i, ContinuousOn (g i) (Set.Icc r s))
    (hgap : ∀ α : ℝ, ∀ c : Fin m → ℝ,
      ∃ x ∈ Set.Icc r s,
        δ ≤ |f x - (α + ∑ i, c i * g i x)|) :
    ∃ y₀ y₁ : ℝ × (Fin m → ℝ),
      y₀ ∈ convexHull ℝ ((fun x : ℝ => (f x, fun i => g i x)) '' Set.Icc r s) ∧
      y₁ ∈ convexHull ℝ ((fun x : ℝ => (f x, fun i => g i x)) '' Set.Icc r s) ∧
      y₀.2 = y₁.2 ∧ δ ≤ |y₀.1 - y₁.1| := by
  have hF : ContinuousOn (fun x : ℝ => (f x, fun i => g i x))
      (Set.Icc r s) := hf.prodMk (continuousOn_pi.mpr hg)
  have hS : IsCompact
      ((fun x : ℝ => (f x, fun i => g i x)) '' Set.Icc r s) :=
    isCompact_Icc.image_of_continuousOn hF
  apply exists_matching_convexHull_of_compact_feature_gap hS hδ
  intro α c
  obtain ⟨x, hx, herror⟩ := hgap α c
  exact ⟨(f x, fun i => g i x), ⟨x, hx, rfl⟩, herror⟩

/- A convex-hull point is a finite convex combination of feature values.
  Use the same weights on Dirac measures at the corresponding points. The
  integral of each coordinate is the indicated finite weighted sum. -/

/-- A [target function and finite constraint family](hyp:f,g), [a joint feature point](hyp:y), and [its membership in the interval feature hull](hyp:hy) yield [a finitely supported probability prior with the prescribed target and constraint expectations](goal). -/
theorem finitePrior_of_convexHull_features
    {m : ℕ} {r s : ℝ} (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (y : ℝ × (Fin m → ℝ))
    (hy : y ∈ convexHull ℝ
      ((fun x : ℝ => (f x, fun i => g i x)) '' Set.Icc r s)) :
    ∃ ω : Measure ℝ, IsProbabilityMeasure ω ∧
      (∃ t : Finset ℝ, ω (t : Set ℝ) = 1) ∧
      ω (Set.Icc r s) = 1 ∧
      (∫ x, f x ∂ω) = y.1 ∧
      (∀ i, (∫ x, g i x ∂ω) = y.2 i) := by
  classical
  obtain ⟨ι, hι, w, z, hw₀, hw₁, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype (R := ℝ)).mp hy
  letI : Fintype ι := hι
  have hz' : ∀ j : ι, ∃ x ∈ Set.Icc r s,
      (f x, fun i => g i x) = z j := by
    intro j
    rcases hz j with ⟨x, hx, hzx⟩
    exact ⟨x, hx, hzx⟩
  choose x hx hzx using hz'
  let ω : Measure ℝ :=
    Measure.sum fun j : ι => ENNReal.ofReal (w j) • Measure.dirac (x j)
  have hp : IsProbabilityMeasure ω := by
    dsimp [ω]
    apply HasSum.isProbabilityMeasure_sum_dirac hw₀
    simpa [hw₁] using (hasSum_fintype w)
  have hmass (A : Set ℝ) (hA : ∀ j, x j ∈ A) : ω A = 1 := by
    have hdirac : ∀ j, Measure.dirac (x j) A = 1 := by
      intro j
      exact Measure.dirac_apply_of_mem (hA j)
    change (Measure.sum fun j : ι => ENNReal.ofReal (w j) •
      Measure.dirac (x j)) A = 1
    rw [Measure.sum_apply_of_countable, tsum_fintype]
    simp only [Measure.smul_apply, hdirac, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw₀ j), hw₁]
    simp
  have hint (F : ℝ → ℝ) :
      (∫ t, F t ∂ω) = ∑ j, w j * F (x j) := by
    change (∫ t, F t ∂Measure.sum (fun j : ι =>
      ENNReal.ofReal (w j) • Measure.dirac (x j))) = _
    rw [integral_sum_dirac (by simp), tsum_fintype]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ENNReal.toReal_ofReal (hw₀ j), smul_eq_mul]
  refine ⟨ω, hp, ?_, hmass _ hx, ?_, ?_⟩
  · refine ⟨Finset.univ.image x, ?_⟩
    apply hmass
    intro j
    simp
  · rw [hint]
    have hproj := congrArg Prod.fst hsum
    simpa only [Prod.fst_sum, Prod.smul_fst, ← hzx, Prod.fst,
      smul_eq_mul] using hproj
  · intro i
    rw [hint]
    have hproj := congrArg (fun z : ℝ × (Fin m → ℝ) => z.2 i) hsum
    simpa only [Prod.snd_sum, Prod.smul_snd, ← hzx, Prod.snd,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hproj

/- The span includes a free constant coefficient. This is essential: otherwise
  an annihilating signed measure need not have total mass zero, so its positive
  and negative parts need not normalize to two probability measures.

  Prove finite-dimensional strong duality for the quotient of C([r,s]) by the
  span of 1 and the gᵢ. A norming signed functional annihilates that span;
  split its Jordan parts, then apply finite-dimensional convex-hull reduction
  to preserve the gᵢ and f integrals with finite support. -/

/-- A [nondegenerate interval](hyp:hrs), [positive approximation gap](hyp:hδ), [target function](hyp:f), and [finite constraint family](hyp:g) whose [target is continuous](hyp:hf), [constraints are continuous](hyp:hg), and [affine constrained approximants miss the target by the stated gap](hyp:hgap) produce [finitely supported probability priors that match every constraint and retain that target separation](goal). -/
theorem exists_finitePriors_of_constrainedApproxGap
    {m : ℕ} {r s δ : ℝ} (hrs : r < s) (hδ : 0 < δ)
    (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc r s))
    (hg : ∀ i, ContinuousOn (g i) (Set.Icc r s))
    (hgap : ∀ α : ℝ, ∀ c : Fin m → ℝ,
      ∃ x ∈ Set.Icc r s,
        δ ≤ |f x - (α + ∑ i, c i * g i x)|) :
    ∃ ω₀ ω₁ : Measure ℝ,
      IsProbabilityMeasure ω₀ ∧ IsProbabilityMeasure ω₁ ∧
      (∃ t : Finset ℝ, ω₀ (t : Set ℝ) = 1) ∧
      (∃ t : Finset ℝ, ω₁ (t : Set ℝ) = 1) ∧
      ω₀ (Set.Icc r s) = 1 ∧ ω₁ (Set.Icc r s) = 1 ∧
      (∀ i, (∫ x, g i x ∂ω₀) = ∫ x, g i x ∂ω₁) ∧
      δ ≤ |(∫ x, f x ∂ω₀) - ∫ x, f x ∂ω₁| := by
  obtain ⟨y₀, y₁, hy₀, hy₁, hconstraint, hsep⟩ :=
    exists_matching_convexHull_features_of_gap hrs hδ f g hf hg hgap
  obtain ⟨ω₀, hp₀, hfin₀, hs₀, hf₀, hg₀⟩ :=
    finitePrior_of_convexHull_features f g y₀ hy₀
  obtain ⟨ω₁, hp₁, hfin₁, hs₁, hf₁, hg₁⟩ :=
    finitePrior_of_convexHull_features f g y₁ hy₁
  refine ⟨ω₀, ω₁, hp₀, hp₁, hfin₀, hfin₁, hs₀, hs₁, ?_, ?_⟩
  · intro i
    rw [hg₀ i, hg₁ i, hconstraint]
  · rwa [hf₀, hf₁]

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
