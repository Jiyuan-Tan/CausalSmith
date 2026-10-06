module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureConditionalIntegration
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureLabelTensorization

/-! # From component densities to conditional label masses

The uniform four-label reference cancels the number of label arrays exactly.
Pointwise bounds for component likelihood densities therefore give the same
bound for the summed Hellinger discrepancy of component probability masses.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Scaling two nonnegative likelihoods scales their squared square-root
 discrepancy by the same factor. [the documented result](goal) Under [the stated assumptions](hyp:hc). -/
-- @node: mixture_sqrt_discrepancy_scale
lemma mixture_sqrt_discrepancy_scale (c f g : ℝ) (hc : 0 ≤ c) :
    (Real.sqrt (c*f)-Real.sqrt (c*g))^2 =
      c*(Real.sqrt f-Real.sqrt g)^2 := by
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, ← mul_sub, mul_pow,
    Real.sq_sqrt hc]

/-- [A product of actual record densities is four to the block size times
its conditional label probability, before any hidden-sign averaging. [the documented result](goal) Under [the stated assumptions](hyp:x,l). -/
-- @node: record_density_product_eq_label_mass
lemma record_density_product_eq_label_mass {ι : Type*} [Fintype ι]
    (P : ι → ObservedLaw) (x : ι → Covariate) (l : ι → Bool × Bool) :
    (∏ i, recordCellDensity (P i) (x i,l i)) =
      (4 : ℝ)^Fintype.card ι * ∏ i, (P i).cells (l i).1 (l i).2 (x i) := by
  simp only [recordCellDensity, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

/-- [The owned-sign component density has exactly the same normalization
factor as its component label mass, including an empty block. [the documented result](goal) Under [the stated assumptions](hyp:x,l). -/
-- @node: conditionalComponent_density_eq_scaled_mass
lemma conditionalComponent_density_eq_scaled_mass {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ]
    [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws : (ν → Bool) → ObservedLaw) (x : ι → Covariate)
    (c : κ) (l : {i : ι // block i = c} → Bool × Bool) :
    (Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
      (∑ σ : {s : ν // owner s = c} → Bool,
        ∏ i : {i : ι // block i = c},
          recordCellDensity (laws (componentSignExtension owner c σ)) (x i.1,l i)) =
      (4 : ℝ)^Fintype.card {i : ι // block i = c} *
        conditionalComponentLabelMass owner block laws x c l := by
  simp_rw [record_density_product_eq_label_mass]
  rw [← Finset.mul_sum]
  unfold conditionalComponentLabelMass
  ring

/-- [Summing a pointwise density bound over the four-label arrays costs no
factor: the component reference is a probability measure. [the documented result](goal) Under [the stated assumptions](hyp:f,g,h). -/
-- @node: mixture_label_mass_hellinger_le_density_bound
lemma mixture_label_mass_hellinger_le_density_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool × Bool) → ℝ) (B : ℝ)
    (h : ∀ l, (Real.sqrt ((4 : ℝ)^Fintype.card ι*f l)-
      Real.sqrt ((4 : ℝ)^Fintype.card ι*g l))^2 ≤ B) :
    (∑ l, (Real.sqrt (f l)-Real.sqrt (g l))^2) ≤ B := by
  have hc : 0 < (4 : ℝ)^Fintype.card ι := by positivity
  simp_rw [mixture_sqrt_discrepancy_scale _ _ _ hc.le] at h
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => h l)
  rw [← Finset.mul_sum] at hs
  have hcard : (Fintype.card (ι → Bool × Bool) : ℝ) = (4 : ℝ)^Fintype.card ι := by
    simp [Fintype.card_fun, Fintype.card_prod]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hs
  exact (mul_le_mul_iff_right₀ hc).mp hs

/-- Integration of the full conditional likelihood discrepancy equals the
sum of discrepancies of its conditional probability masses. [the documented result](goal) Under [the stated assumptions](hyp:x). -/
-- @node: mixture_conditional_hellinger_eq_label_sum
lemma mixture_conditional_hellinger_eq_label_sum (n k : ℕ)
    (laws₀ laws₁ : (Fin (k+1) → Bool) → ObservedLaw) (x : Fin n → Covariate) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
      (fun l => signMixtureCellDensity n k laws₀ (fun i => (x i,l i)))
      (fun l => signMixtureCellDensity n k laws₁ (fun i => (x i,l i))) =
    ∑ l : Fin n → Bool × Bool,
      (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
          ∑ σ, ∏ i, (laws₀ σ).cells (l i).1 (l i).2 (x i))-
       Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
          ∑ σ, ∏ i, (laws₁ σ).cells (l i).1 (l i).2 (x i)))^2 := by
  unfold Causalean.Stat.hellingerSqDensity
  rw [integral_labelReference_pi]
  simp_rw [signMixtureCellDensity_card_average, record_density_product_eq_label_mass]
  simp only [Fintype.card_fin]
  simp_rw [← Finset.mul_sum]
  have he (a b : ℝ) : a*((4 : ℝ)^n*b) = (4 : ℝ)^n*(a*b) := by ring
  simp_rw [he, mixture_sqrt_discrepancy_scale ((4 : ℝ)^n) _ _ (by positivity)]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_pow]
  norm_num

/-- [A pointwise bound for the two owned-sign component densities controls the
component Hellinger distance after summing its conditional label masses. [the documented result](goal) Under [the stated assumptions](hyp:x,h). -/
-- @node: conditionalComponent_mass_hellinger_le_density_bound
lemma conditionalComponent_mass_hellinger_le_density_bound {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ]
    [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws₀ laws₁ : (ν → Bool) → ObservedLaw) (x : ι → Covariate) (c : κ) (B : ℝ)
    (h : ∀ l : {i : ι // block i = c} → Bool × Bool,
      (Real.sqrt ((Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : ι // block i = c},
          recordCellDensity (laws₀ (componentSignExtension owner c σ)) (x i.1,l i))-
       Real.sqrt ((Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : ι // block i = c},
          recordCellDensity (laws₁ (componentSignExtension owner c σ)) (x i.1,l i)))^2 ≤ B) :
    (∑ l, (Real.sqrt (conditionalComponentLabelMass owner block laws₀ x c l)-
      Real.sqrt (conditionalComponentLabelMass owner block laws₁ x c l))^2) ≤ B := by
  apply mixture_label_mass_hellinger_le_density_bound
  intro l
  simpa only [conditionalComponent_density_eq_scaled_mass] using h l

end CausalSmith.Stat.LogoddsLowsmoothFrontier
