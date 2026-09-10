import CausalSmith.Substrate.SemialgebraicStratificationSard.NashWhitney

/-!
# Semialgebraic Sard and generic translation transversality

This file defines regular points and critical values for Nash maps between embedded Nash manifolds,
states the semialgebraic Sard dimension drop, and packages its finite-union consequence for the
subtraction maps attached to two finite Nash Whitney stratifications.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CausalSmith.SemialgebraicStratificationSard

/-- A point of the source is regular for a map between embedded manifolds when the derivative maps
source tangent vectors onto all target tangent vectors. -/
def IsRegularPointOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (source : Set (ι → ℝ)) (target : Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ)) (x : ι → ℝ) : Prop :=
  x ∈ source ∧ f x ∈ target ∧
    ∀ w ∈ tangentVectors target (f x),
      ∃ γ : ℝ → (ι → ℝ), γ 0 = x ∧ (∀ᶠ t in 𝓝 0, γ t ∈ source) ∧
        HasDerivAt γ (deriv γ 0) 0 ∧ HasDerivAt (f ∘ γ) w 0

/-- The critical points of a map between embedded manifolds are its source points that are not
regular. -/
def criticalPointsOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (source : Set (ι → ℝ)) (target : Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ)) : Set (ι → ℝ) :=
  {x | x ∈ source ∧ ¬IsRegularPointOn source target f x}

/-- The critical values of a map between embedded manifolds are images of its critical points. -/
def criticalValuesOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (source : Set (ι → ℝ)) (target : Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ)) : Set (κ → ℝ) :=
  f '' criticalPointsOn source target f

/-- A map between embedded Nash manifolds is Nash when it maps the source into the target and is
locally Nash along the source. -/
def IsNashMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (source : Set (ι → ℝ)) (target : Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  MapsTo f source target ∧ IsNashOn source f

/-- **Semialgebraic Sard theorem.** Critical values of a Nash map between nonempty Nash manifolds
form a semialgebraic set of dimension strictly below the target manifold dimension
(Bochnak--Coste--Roy, Theorem 9.6.2). -/
theorem nash_sard {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r q : ℕ} {source : Set (ι → ℝ)} {target : Set (κ → ℝ)}
    {f : (ι → ℝ) → (κ → ℝ)}
    (hsource : IsNashManifold r source) (htarget : IsNashManifold q target)
    (hf : IsNashMap source target f) :
    IsSemialgebraic (criticalValuesOn source target f) ∧
      semialgebraicDim (criticalValuesOn source target f) < (q : ℤ) := by
  -- The proof must first identify the curve-based regularity predicate with surjectivity of the
  -- chart derivative.  Rank conditions are polynomial in Nash charts, after which semialgebraic
  -- Sard gives the dimension drop and Tarski--Seidenberg gives semialgebraicity of the image.
  sorry

/-- The subtraction map on a pair of finite real coordinate spaces. -/
def subtractionMap {ι : Type*} (z : Sum ι ι → ℝ) : ι → ℝ :=
  fun i => z (.inl i) - z (.inr i)

/-- A product of two Nash manifolds is a Nash manifold whose dimension is the sum of their
dimensions. -/
theorem IsNashManifold.coordinateProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r q : ℕ} {s : Set (ι → ℝ)} {t : Set (κ → ℝ)}
    (hs : IsNashManifold r s) (ht : IsNashManifold q t) :
    IsNashManifold (r + q) (coordinateProduct s t) := by
  sorry

/-- On the product of any two Nash strata, coordinate subtraction is a Nash map to the ambient
coordinate space. -/
theorem subtraction_isNashMap {ι : Type*} [Fintype ι]
    {r q : ℕ} {s t : Set (ι → ℝ)}
    (hs : IsNashManifold r s) (ht : IsNashManifold q t) :
    IsNashMap (coordinateProduct s t) (Set.univ : Set (ι → ℝ)) subtractionMap := by
  sorry

/-- Two strata are transverse at translation `a` when, at every pair with `u - e = a`, differences
of their tangent vectors span the ambient coordinate space. -/
def TransverseAtTranslation {ι : Type*} [Fintype ι]
    (uStratum eStratum : Set (ι → ℝ)) (a : ι → ℝ) : Prop :=
  ∀ u ∈ uStratum, ∀ e ∈ eStratum, u - e = a →
    ∀ w : ι → ℝ, ∃ vu ∈ tangentVectors uStratum u,
      ∃ ve ∈ tangentVectors eStratum e, vu - ve = w

/-- The exceptional translations for two finite stratifications are those at which at least one
pair of strata fails to be transverse. -/
def exceptionalTranslations {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (C : NashWhitneyStratification c)
    (E : NashWhitneyStratification e) : Set (ι → ℝ) :=
  {a | ¬∀ i j, TransverseAtTranslation (C.stratum i) (E.stratum j) a}

/-- The exceptional-translation set is the finite union of the critical-value sets of the
subtraction maps on all pairs of strata. -/
theorem exceptionalTranslations_eq_iUnion_criticalValues {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (C : NashWhitneyStratification c)
    (E : NashWhitneyStratification e) :
    exceptionalTranslations C E =
      ⋃ i, ⋃ j, criticalValuesOn (coordinateProduct (C.stratum i) (E.stratum j))
        (Set.univ : Set (ι → ℝ)) subtractionMap := by
  sorry

/-- The exceptional translations for two finite Nash Whitney stratifications form a semialgebraic
set of dimension strictly below the ambient dimension. -/
theorem exceptionalTranslations_semialgebraic_dim_lt {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (C : NashWhitneyStratification c)
    (E : NashWhitneyStratification e) :
    IsSemialgebraic (exceptionalTranslations C E) ∧
      semialgebraicDim (exceptionalTranslations C E) < (Fintype.card ι : ℤ) := by
  sorry

/-- **Generic translation transversality.** Outside a Lebesgue-null set of translations, every
pair of strata in two finite Nash Whitney stratifications is transverse under subtraction. -/
theorem generic_translation_transversality {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (C : NashWhitneyStratification c)
    (E : NashWhitneyStratification e) :
    volume (exceptionalTranslations C E) = 0 := by
  exact volume_eq_zero_of_semialgebraicDim_lt_ambient
    (exceptionalTranslations_semialgebraic_dim_lt C E).1
    (exceptionalTranslations_semialgebraic_dim_lt C E).2

/-- For Lebesgue-almost every translation, every pair of strata in two finite Nash Whitney
stratifications is transverse under coordinate subtraction. -/
theorem ae_all_strata_transverse {ι : Type*} [Fintype ι]
    {c e : Set (ι → ℝ)} (C : NashWhitneyStratification c)
    (E : NashWhitneyStratification e) :
    ∀ᵐ a ∂(volume : Measure (ι → ℝ)), ∀ i j,
      TransverseAtTranslation (C.stratum i) (E.stratum j) a := by
  rw [MeasureTheory.ae_iff]
  simpa [exceptionalTranslations] using generic_translation_transversality C E

/-- A semialgebraic set and the boundary of a compact, full-dimensional, regular-closed
semialgebraic set have finite Nash Whitney stratifications whose exceptional translations are
Lebesgue-null. -/
theorem exists_stratifications_set_frontier_generic_translation
    {ι : Type*} [Fintype ι] {c e : Set (ι → ℝ)}
    (hc : IsSemialgebraic c) (he : IsSemialgebraic e) (_hcompact : IsCompact e)
    (_hfull : semialgebraicDim e = (Fintype.card ι : ℤ))
    (_hregularClosed : closure (interior e) = e) :
    ∃ (C : NashWhitneyStratification c) (E : NashWhitneyStratification (frontier e)),
      volume (exceptionalTranslations C E) = 0 := by
  obtain ⟨C⟩ := exists_nashWhitneyStratification hc
  obtain ⟨E⟩ := exists_nashWhitneyStratification he.frontier
  exact ⟨C, E, generic_translation_transversality C E⟩

end CausalSmith.SemialgebraicStratificationSard
