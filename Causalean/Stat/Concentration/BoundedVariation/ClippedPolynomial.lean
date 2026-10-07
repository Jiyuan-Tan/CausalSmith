module
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Mathlib.Probability.Independence.Basic

/-!
# Clipped finite factorial-polynomial paths

A finite linear combination of deterministic continuous coefficient paths, with random scalar
factorial monomials, yields a continuous path. If the coefficients have bounded variation and the
monomials have finite second moments, clipping preserves bounded variation and gives an
integrable squared path size. Independence follows from disjoint measurable coordinate blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.BoundedVariation
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [A clipping radius and a scalar value x](hyp:cap,x) determine [the value x clipped to the symmetric interval from minus the radius to the radius, that is, the smaller of the radius and the larger of minus the radius and x](goal).

Scalar clipping to the symmetric interval with radius `cap`; the radius is meant to be nonnegative.
-/
def scalarClip (cap x : ℝ) : ℝ := min cap (max (-cap) x)

private theorem scalarClip_lipschitz (cap : ℝ) : LipschitzWith 1 (scalarClip cap) := by
  unfold scalarClip
  have hmax : LipschitzWith 1 (fun x : ℝ => max (-cap) x) := by
    simpa using (LipschitzWith.max (LipschitzWith.const (-cap)) LipschitzWith.id)
  simpa using (LipschitzWith.min (LipschitzWith.const cap) hmax)

private theorem eVariationOn_add_le (f g : Time → ℝ) :
    eVariationOn (fun t => f t + g t) Set.univ ≤
      eVariationOn f Set.univ + eVariationOn g Set.univ := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n,
      edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))) ≤
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ ≤ eVariationOn f Set.univ + eVariationOn g Set.univ :=
      add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

private theorem eVariationOn_finset_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → Time → ℝ) :
    eVariationOn (fun t => ∑ a ∈ s, f a t) Set.univ ≤
      ∑ a ∈ s, eVariationOn (f a) Set.univ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (eVariationOn.constant_on
      (f := fun _ : Time => (0 : ℝ)) (s := Set.univ) (by simp))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (eVariationOn_add_le (f a) _).trans (add_le_add_right ih _)

private theorem eVariationOn_const_mul_le (a : ℝ) (f : Time → ℝ) :
    eVariationOn (fun t => a * f t) Set.univ ≤
      (‖a‖₊ : ENNReal) * eVariationOn f Set.univ := by
  have h := (lipschitzWith_smul a).lipschitzOnWith.comp_eVariationOn_le
    (g := f) (s := Set.univ) (t := Set.univ) (by simp)
  simpa [Function.comp_def, smul_eq_mul] using h

private theorem eVariationOn_weighted_sum_le {ι : Type*} [Fintype ι]
    (c : ι → Path) (x : ι → ℝ) :
    eVariationOn (fun t => ∑ a, x a * c a t) Set.univ ≤
      ∑ a, (‖x a‖₊ : ENNReal) * eVariationOn (c a) Set.univ := by
  calc
    _ ≤ ∑ a, eVariationOn (fun t => x a * c a t) Set.univ := by
      simpa using eVariationOn_finset_sum_le Finset.univ
        (fun a t => x a * c a t)
    _ ≤ _ := Finset.sum_le_sum (fun a _ => eVariationOn_const_mul_le (x a) (c a))

private theorem eVariationOn_clipped_weighted_sum_le {ι : Type*} [Fintype ι]
    (c : ι → Path) (x : ι → ℝ) (cap : ℝ) :
    eVariationOn (fun t => scalarClip cap (∑ a, x a * c a t)) Set.univ ≤
      ∑ a, (‖x a‖₊ : ENNReal) * eVariationOn (c a) Set.univ := by
  have h := (scalarClip_lipschitz cap).lipschitzOnWith.comp_eVariationOn_le
    (g := fun t : Time => ∑ a, x a * c a t)
    (s := Set.univ) (t := Set.univ) (by simp)
  have hclip : eVariationOn (fun t => scalarClip cap (∑ a, x a * c a t)) Set.univ ≤
      eVariationOn (fun t => ∑ a, x a * c a t) Set.univ := by
    simpa [Function.comp_def] using h
  exact hclip.trans (eVariationOn_weighted_sum_le c x)

/-- A finite linear combination of continuous coefficient paths remains continuous after scalar
clipping. -/
theorem continuous_clipped_finite_sum {ι : Type*} [Fintype ι]
    (c : ι → Path) (x : ι → ℝ) (cap : ℝ) :
    Continuous (fun t : Time => scalarClip cap (∑ a, x a * c a t)) := by
  unfold scalarClip
  apply Continuous.min continuous_const
  apply Continuous.max continuous_const
  fun_prop

/-- [Finitely many coefficient paths c_a, random scalar coefficients X_a, a clipping radius, and a sample point ω](hyp:c,X,cap,ω) determine [the clipped continuous path sending each time t to the finite sum Σ_a X_a(ω)·c_a(t), clipped to the symmetric interval of that radius](goal).

The intended use is a random finite factorial-polynomial path: the coefficient paths are
deterministic and the scalar coefficients are monomial values.
-/
def clippedFinitePath {ι Ω : Type*} [Fintype ι]
    (c : ι → Path) (X : Ω → ι → ℝ) (cap : ℝ) (ω : Ω) : Path :=
  ⟨fun t => scalarClip cap (∑ a, X ω a * c a t),
    continuous_clipped_finite_sum c (X ω) cap⟩

/-- Clipping a finite sum of bounded-variation coefficient paths has path size bounded by the
weighted sum of coefficient path sizes. The clip radius is assumed nonnegative.
-/
theorem clippedFinitePath_pathSize_le {ι Ω : Type*} [Fintype ι]
    (c : ι → Path) (X : Ω → ι → ℝ) (cap : ℝ) (hcap : 0 ≤ cap)
    (hBV : ∀ a, eVariationOn (c a) Set.univ < ⊤) (ω : Ω) :
    pathSize (clippedFinitePath c X cap ω) ≤
      ∑ a, |X ω a| * pathSize (c a) := by
  let y : Path := clippedFinitePath c X cap ω
  have hnorm : ‖y‖ ≤ ∑ a, |X ω a| * ‖c a‖ := by
    have hnonneg : 0 ≤ (∑ a, |X ω a| * ‖c a‖) :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
    apply (ContinuousMap.norm_le y hnonneg).2
    intro t
    have hclip0 : scalarClip cap 0 = 0 := by
      simp [scalarClip, hcap]
    have hpoint : ‖scalarClip cap (∑ a, X ω a * c a t)‖ ≤
        ‖∑ a, X ω a * c a t‖ := by
      have h := (scalarClip_lipschitz cap).dist_le_mul
        (∑ a, X ω a * c a t) 0
      simpa [hclip0, Real.norm_eq_abs] using h
    calc
      ‖y t‖ ≤ ‖∑ a, X ω a * c a t‖ := hpoint
      _ ≤ ∑ a, ‖X ω a * c a t‖ := norm_sum_le _ _
      _ ≤ ∑ a, |X ω a| * ‖c a‖ := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm (c a) t)
          (abs_nonneg _)
  have hfin : (∑ a, (‖X ω a‖₊ : ENNReal) *
      eVariationOn (c a) Set.univ) < ⊤ := by
    exact ENNReal.sum_lt_top.mpr (fun a _ =>
      ENNReal.mul_lt_top (by simp) (hBV a))
  have htv : pathTV y ≤ ∑ a, |X ω a| * pathTV (c a) := by
    have h := ENNReal.toReal_mono (ne_of_lt hfin)
      (eVariationOn_clipped_weighted_sum_le c (X ω) cap)
    rw [ENNReal.toReal_sum (fun a _ => ne_of_lt
      (ENNReal.mul_lt_top (by simp) (hBV a)))] at h
    simpa [pathTV, y, clippedFinitePath, ENNReal.toReal_mul, Real.norm_eq_abs] using h
  dsimp [pathSize]
  simp only [Finset.sum_add_distrib, mul_add]
  linarith

/-- A finite sum of bounded-variation coefficient paths, after scalar clipping, still has finite
total variation on the threshold interval. -/
theorem clippedFinitePath_bv {ι Ω : Type*} [Fintype ι]
    (c : ι → Path) (X : Ω → ι → ℝ) (cap : ℝ)
    (hBV : ∀ a, eVariationOn (c a) Set.univ < ⊤) (ω : Ω) :
    eVariationOn (clippedFinitePath c X cap ω) Set.univ < ⊤ := by
  apply lt_of_le_of_lt (eVariationOn_clipped_weighted_sum_le c (X ω) cap)
  exact ENNReal.sum_lt_top.mpr (fun a _ =>
    ENNReal.mul_lt_top (by simp) (hBV a))

/-- Measurable scalar monomials produce a measurable random continuous path when their
coefficient paths and clipping radius are deterministic. -/
theorem measurable_clippedFinitePath {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (c : ι → Path) (X : Ω → ι → ℝ)
    (hX : ∀ a, Measurable (fun ω => X ω a)) (cap : ℝ) :
    Measurable (clippedFinitePath c X cap) := by
  have hcont : Continuous (fun x : ι → ℝ =>
      clippedFinitePath c (fun _ => x) cap ()) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (ι → ℝ) × Time =>
      scalarClip cap (∑ a, p.1 a * c a p.2))
    unfold scalarClip
    fun_prop
  have hvec : Measurable X := measurable_pi_lambda _ hX
  let : BorelSpace Path := ⟨rfl⟩
  exact hcont.measurable.comp hvec

/-- Under [a probability measure](hyp:μ), take [finitely many coefficient paths c_a, random scalar coefficients X_a, and a clip radius](hyp:c,X,cap) with [the radius nonnegative](hyp:hcap), [every coefficient path of finite total variation](hyp:hBV), and [the scalar coefficients measurable](hyp:hXmeas) and [square integrable](hyp:hXsq). Then [the squared size of the clipped path t ↦ clip(Σ_a X_a·c_a(t)) is integrable, and its expectation is at most (Σ_a size(c_a)²)·(Σ_a E[X_a²]), where the size of a path is its supremum norm plus its total variation](goal).

This supplies square integrability for finite factorial
polynomials from their coordinatewise Poisson moment bounds.
-/
theorem clippedFinitePath_sq_integral_le {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ι → Path) (X : Ω → ι → ℝ) (cap : ℝ) (hcap : 0 ≤ cap)
    (hBV : ∀ a, eVariationOn (c a) Set.univ < ⊤)
    (hXmeas : ∀ a, Measurable (fun ω => X ω a))
    (hXsq : ∀ a, Integrable (fun ω => (X ω a) ^ 2) μ) :
    Integrable (fun ω => (pathSize (clippedFinitePath c X cap ω)) ^ 2) μ ∧
      (∫ ω, (pathSize (clippedFinitePath c X cap ω)) ^ 2 ∂μ) ≤
        (∑ a, (pathSize (c a)) ^ 2) *
          ∑ a, (∫ ω, (X ω a) ^ 2 ∂μ) := by
  let K : ℝ := ∑ a, (pathSize (c a)) ^ 2
  let S (ω : Ω) : ℝ := ∑ a, (X ω a) ^ 2
  let Y (ω : Ω) : ℝ := (pathSize (clippedFinitePath c X cap ω)) ^ 2
  have hK : 0 ≤ K := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hYmeas : Measurable Y := by
    let : BorelSpace Path := ⟨rfl⟩
    have hm := measurable_clippedFinitePath c X hXmeas cap
    unfold Y pathSize
    exact ((continuous_norm.measurable.comp hm).add
      (measurable_pathTV.comp hm)).pow_const 2
  have hSint : Integrable S μ := by
    unfold S
    exact integrable_finsetSum _ (fun a _ => hXsq a)
  have hdomint : Integrable (fun ω => K * S ω) μ := hSint.const_mul K
  have hpoint (ω : Ω) : Y ω ≤ K * S ω := by
    have hsize := clippedFinitePath_pathSize_le c X cap hcap hBV ω
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun a => |X ω a|) (fun a => pathSize (c a))
    have hsum : 0 ≤ ∑ a, |X ω a| * pathSize (c a) :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (abs_nonneg _) (pathSize_nonneg _))
    have hsq := (sq_le_sq₀ (pathSize_nonneg _) hsum).mpr hsize
    dsimp [Y, K, S]
    calc
      (pathSize (clippedFinitePath c X cap ω)) ^ 2 ≤
          (∑ a, |X ω a| * pathSize (c a)) ^ 2 := hsq
      _ ≤ (∑ a, |X ω a| ^ 2) * ∑ a, (pathSize (c a)) ^ 2 := hcs
      _ = (∑ a, (pathSize (c a)) ^ 2) * ∑ a, (X ω a) ^ 2 := by
        simp only [sq_abs]
        ring
  have hYint : Integrable Y μ := by
    apply Integrable.mono' hdomint hYmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  constructor
  · exact hYint
  · calc
      ∫ ω, Y ω ∂μ ≤ ∫ ω, K * S ω ∂μ :=
        integral_mono hYint hdomint hpoint
      _ = K * ∑ a, (∫ ω, (X ω a) ^ 2 ∂μ) := by
        rw [integral_const_mul, integral_finsetSum _ (fun a _ => hXsq a)]

/-- Measurable functions of independent coordinate blocks produce independent clipped finite
paths, even when every block uses the same deterministic coefficient family. -/
theorem clippedFinitePath_independent_blocks
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (block : Fin n → Ω → (ι → ℝ))
    (hblock : iIndepFun block μ) (c : Fin n → ι → Path) (cap : Fin n → ℝ) :
    iIndepFun (fun j ω =>
      clippedFinitePath (c j) (fun ω a => block j ω a) (cap j) ω) μ := by
  have hmap (j : Fin n) : Measurable (fun x : ι → ℝ =>
      clippedFinitePath (c j) (fun _ => x) (cap j) ()) := by
    have hcont : Continuous (fun x : ι → ℝ =>
        clippedFinitePath (c j) (fun _ => x) (cap j) ()) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : (ι → ℝ) × Time =>
        scalarClip (cap j) (∑ a, p.1 a * c j a p.2))
      unfold scalarClip
      fun_prop
    let : BorelSpace Path := ⟨rfl⟩
    exact hcont.measurable
  exact hblock.comp _ hmap

end Causalean.Stat.Concentration.BoundedVariation

