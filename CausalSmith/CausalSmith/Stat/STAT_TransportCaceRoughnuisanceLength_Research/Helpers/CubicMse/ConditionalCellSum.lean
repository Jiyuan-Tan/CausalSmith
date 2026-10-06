module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SubsetAggregation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Conditional second moments of centered cell sums

Roadmap (16) follows by expanding the square under conditional expectation,
using the factored block covariances, and counting diagonal and off-diagonal
cell pairs. Training coefficients may depend on the conditioned observation.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The conditional second moment of a finite sum is its ordered cross-moment
sum. No independence between the cells is needed.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,Y,hcross), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_cellSum_eq_sum_cross
lemma condExp_sq_cellSum_eq_sum_cross
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {K : ℕ} (Y : Fin K → Ω → ℝ)
    (hcross : ∀ l r, Integrable (fun ω => Y l ω * Y r ω) μ) :
    condExp m μ (fun ω => (∑ l : Fin K, Y l ω) ^ 2) =ᵐ[μ]
      (fun ω => ∑ l : Fin K, ∑ r : Fin K,
        condExp m μ (fun ξ => Y l ξ * Y r ξ) ω) := by
  have hsquare : (fun ω => (∑ l : Fin K, Y l ω) ^ 2) =
      (fun ω => ∑ l : Fin K, ∑ r : Fin K, Y l ω * Y r ω) := by
    funext ω
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsquare]
  have houter := condExp_finsetSum (s := Finset.univ)
    (f := fun l ω => ∑ r : Fin K, Y l ω * Y r ω)
    (fun l _ => integrable_finsetSum _ (fun r _ => hcross l r)) m
  have hinner (l : Fin K) := condExp_finsetSum (s := Finset.univ)
    (f := fun r ω => Y l ω * Y r ω) (fun r _ => hcross l r) m
  filter_upwards [houter, ae_all_iff.mpr hinner] with ω ho hi
  simp only [Finset.sum_fn, Finset.sum_apply] at ho hi
  rw [ho]
  exact Finset.sum_congr rfl fun l _ => hi l


/-- Conditional version of the diagonal/off-diagonal cell-pair bound. The
cross-moment identity is supplied by independent evaluation blocks and the
training-coefficient pull-out lemma.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,q,Y,c,κ,C,D,O,hC,hD,hO,hcross,hfactor,hc,hκdiag,hκoff), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_cellSum_factored_le
lemma condExp_sq_cellSum_factored_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {K q : ℕ} (Y : Fin K → Ω → ℝ) (c : Fin K → Ω → ℝ)
    (κ : Fin q → Fin K → Fin K → ℝ) (C D O : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hO : 0 ≤ O)
    (hcross : ∀ l r, Integrable (fun ω => Y l ω * Y r ω) μ)
    (hfactor : ∀ l r,
      condExp m μ (fun ξ => Y l ξ * Y r ξ) =ᵐ[μ]
        (fun ω => c l ω * c r ω * ∏ t : Fin q, κ t l r))
    (hc : ∀ᵐ ω ∂μ, ∀ l, |c l ω| ≤ C)
    (hκdiag : ∀ t l, |κ t l l| ≤ D)
    (hκoff : ∀ t l r, l ≠ r → |κ t l r| ≤ O) :
    ∀ᵐ ω ∂μ, condExp m μ (fun ξ => (∑ l : Fin K, Y l ξ) ^ 2) ω ≤
      (K : ℝ) * C ^ 2 * D ^ q + (K : ℝ) ^ 2 * C ^ 2 * O ^ q := by
  have hall : ∀ᵐ ω ∂μ, ∀ l r,
      condExp m μ (fun ξ => Y l ξ * Y r ξ) ω =
        c l ω * c r ω * ∏ t : Fin q, κ t l r :=
    ae_all_iff.mpr fun l => ae_all_iff.mpr (hfactor l)
  filter_upwards [@condExp_sq_cellSum_eq_sum_cross Ω mΩ μ m K Y hcross, hall, hc]
    with ω hsum hf hcω
  rw [hsum]
  calc
    _ = ∑ l : Fin K, ∑ r : Fin K,
        c l ω * c r ω * ∏ t : Fin q, κ t l r := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_congr rfl fun r _ => hf l r
    _ ≤ |∑ l : Fin K, ∑ r : Fin K,
        c l ω * c r ω * ∏ t : Fin q, κ t l r| := le_abs_self _
    _ ≤ _ := abs_cellPair_product_sum_le (fun l => c l ω) κ C D O
      hC hD hO hcω hκdiag hκoff

/-- A normalized cell sum of conditionally centered summands is conditionally
centered, even when its coefficients depend on training.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,Y,hY,hzero), [the stated conclusion holds](goal). -/
-- @node: condExp_cellAverage_zero
lemma condExp_cellAverage_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {K : ℕ} (Y : Fin K → Ω → ℝ)
    (hY : ∀ l, Integrable (Y l) μ)
    (hzero : ∀ l, condExp m μ (Y l) =ᵐ[μ] (0 : Ω → ℝ)) :
    condExp m μ (fun ω => (K : ℝ)⁻¹ * ∑ l : Fin K, Y l ω) =ᵐ[μ]
      (0 : Ω → ℝ) := by
  have hsum := condExp_finsetSum (μ := μ) (s := Finset.univ)
    (f := Y) (fun l _ => hY l) m
  have hscale := condExp_smul (μ := μ) (K : ℝ)⁻¹
    (fun ω => ∑ l : Fin K, Y l ω) m
  filter_upwards [hsum, hscale, ae_all_iff.mpr hzero] with ω hs ht hz
  simp only [Finset.sum_fn, Finset.sum_apply] at hs
  simp only [Pi.smul_def, smul_eq_mul] at ht
  rw [ht, hs]
  simp only [hz, Pi.zero_apply, Finset.sum_const_zero, mul_zero]

/-- The exact normalized diagonal/off-diagonal bound in roadmap (16), for
`q+1` centered residual blocks. Taking `q=0,1,2` gives all nonempty subsets
in the quadratic and cubic expansions.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,q,hK,Y,c,κ,C,V,B,hC,hV,hB,hcross,hfactor,hc,hκdiag,hκoff), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_cellAverage_factored_le
lemma condExp_sq_cellAverage_factored_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {K q : ℕ} (hK : 0 < K) (Y : Fin K → Ω → ℝ) (c : Fin K → Ω → ℝ)
    (κ : Fin (q + 1) → Fin K → Fin K → ℝ) (C V B : ℝ)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hB : 0 < B)
    (hcross : ∀ l r, Integrable (fun ω => Y l ω * Y r ω) μ)
    (hfactor : ∀ l r,
      condExp m μ (fun ξ => Y l ξ * Y r ξ) =ᵐ[μ]
        (fun ω => c l ω * c r ω * ∏ t : Fin (q + 1), κ t l r))
    (hc : ∀ᵐ ω ∂μ, ∀ l, |c l ω| ≤ C)
    (hκdiag : ∀ t l, |κ t l l| ≤ V * K / B)
    (hκoff : ∀ t l r, l ≠ r → |κ t l r| ≤ V / B) :
    ∀ᵐ ω ∂μ,
      condExp m μ (fun ξ => ((K : ℝ)⁻¹ * ∑ l : Fin K, Y l ξ) ^ 2) ω ≤
        C ^ 2 * V ^ (q + 1) *
          ((K : ℝ) ^ q / B ^ (q + 1) + 1 / B ^ (q + 1)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hbound := @condExp_sq_cellSum_factored_le Ω mΩ μ m K (q + 1)
    Y c κ C (V * K / B) (V / B) hC
    (by positivity) (by positivity) hcross hfactor hc hκdiag hκoff
  have hscale := condExp_smul (μ := μ) ((K : ℝ)⁻¹ ^ 2)
    (fun ξ => (∑ l : Fin K, Y l ξ) ^ 2) m
  have heq : (fun ξ => ((K : ℝ)⁻¹ * ∑ l : Fin K, Y l ξ) ^ 2) =
      ((K : ℝ)⁻¹ ^ 2) • (fun ξ => (∑ l : Fin K, Y l ξ) ^ 2) := by
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [heq]
  filter_upwards [hbound, hscale] with ω hb hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs]
  calc
    _ ≤ (K : ℝ)⁻¹ ^ 2 *
        ((K : ℝ) * C ^ 2 * (V * K / B) ^ (q + 1) +
          (K : ℝ) ^ 2 * C ^ 2 * (V / B) ^ (q + 1)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      simp only [div_pow, mul_pow, pow_succ]
      field_simp

/-- Conditional variance of the normalized cell sum equals its centered
second moment and satisfies the factored bound. This joins conditional
centering with the cell-pair computation rather than assuming a variance
estimate.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,q,hK,Y,c,κ,C,V,B,hC,hV,hB,hY,hzero,hcross,hfactor,hc,hκdiag,hκoff), [the stated conclusion holds](goal). -/
-- @node: conditional_variance_cellAverage_factored_le
lemma conditional_variance_cellAverage_factored_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {K q : ℕ} (hK : 0 < K) (Y : Fin K → Ω → ℝ) (c : Fin K → Ω → ℝ)
    (κ : Fin (q + 1) → Fin K → Fin K → ℝ) (C V B : ℝ)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hB : 0 < B)
    (hY : ∀ l, Integrable (Y l) μ)
    (hzero : ∀ l, condExp m μ (Y l) =ᵐ[μ] (0 : Ω → ℝ))
    (hcross : ∀ l r, Integrable (fun ω => Y l ω * Y r ω) μ)
    (hfactor : ∀ l r,
      condExp m μ (fun ξ => Y l ξ * Y r ξ) =ᵐ[μ]
        (fun ω => c l ω * c r ω * ∏ t : Fin (q + 1), κ t l r))
    (hc : ∀ᵐ ω ∂μ, ∀ l, |c l ω| ≤ C)
    (hκdiag : ∀ t l, |κ t l l| ≤ V * K / B)
    (hκoff : ∀ t l r, l ≠ r → |κ t l r| ≤ V / B) :
    ∀ᵐ ω ∂μ, condExp m μ (fun ξ =>
      ((K : ℝ)⁻¹ * ∑ l : Fin K, Y l ξ -
        condExp m μ (fun ζ => (K : ℝ)⁻¹ * ∑ l : Fin K, Y l ζ) ξ) ^ 2) ω ≤
      C ^ 2 * V ^ (q + 1) *
        ((K : ℝ) ^ q / B ^ (q + 1) + 1 / B ^ (q + 1)) := by
  have hz := @condExp_cellAverage_zero Ω mΩ μ m K Y hY hzero
  have heq := condExp_congr_ae (m := m) (show
      (fun ξ => ((K : ℝ)⁻¹ * ∑ l : Fin K, Y l ξ -
        condExp m μ (fun ζ => (K : ℝ)⁻¹ * ∑ l : Fin K, Y l ζ) ξ) ^ 2) =ᵐ[μ]
      (fun ξ => ((K : ℝ)⁻¹ * ∑ l : Fin K, Y l ξ) ^ 2) by
    filter_upwards [hz] with ξ hξ
    rw [hξ]
    simp only [Pi.zero_apply, sub_zero])
  have hb := @condExp_sq_cellAverage_factored_le Ω mΩ μ m K q hK Y c κ C V B
    hC hV hB hcross hfactor hc hκdiag hκoff
  exact heq.trans_le hb

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
