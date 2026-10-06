module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalCellSum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Bounded training coefficients in centered cell averages

The coefficient pull-out and integrability argument in roadmap (16), uniformly
for every nonempty subset of evaluation blocks.
-/

public section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Bounded training coefficients preserve the factored centered-cell variance
estimate. The input cross moments are identities, rather than variance gates.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,hm,K,q,hK,X,c,κ,C,V,B,hC,hV,hB,hcmeas,hc,hlp,hzero,hfactor,hdiag,hoff), [the stated conclusion holds](goal). -/
-- @node: conditional_variance_weighted_centered_cells
lemma conditional_variance_weighted_centered_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {K q : ℕ} (hK : 0 < K) (X : Fin K → Ω → ℝ)
    (c : Fin K → Ω → ℝ) (κ : Fin (q + 1) → Fin K → Fin K → ℝ)
    (C V B : ℝ) (hC : 0 ≤ C) (hV : 0 ≤ V) (hB : 0 < B)
    (hcmeas : ∀ l, StronglyMeasurable[m] (c l))
    (hc : ∀ᵐ x ∂μ, ∀ l, |c l x| ≤ C)
    (hlp : ∀ l, MemLp (X l) 2 μ)
    (hzero : ∀ l, condExp m μ (X l) =ᵐ[μ] (0 : Ω → ℝ))
    (hfactor : ∀ l r, condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
      (fun _ => ∏ t : Fin (q + 1), κ t l r))
    (hdiag : ∀ t l, |κ t l l| ≤ V * K / B)
    (hoff : ∀ t l r, l ≠ r → |κ t l r| ≤ V / B) :
    ∀ᵐ x ∂μ, condExp m μ (fun y =>
      ((K : ℝ)⁻¹ * ∑ l : Fin K, c l y * X l y -
        condExp m μ (fun z => (K : ℝ)⁻¹ * ∑ l : Fin K, c l z * X l z) y) ^ 2) x ≤
      C ^ 2 * V ^ (q + 1) *
        ((K : ℝ) ^ q / B ^ (q + 1) + 1 / B ^ (q + 1)) := by
  let : MeasurableSpace Ω := mΩ
  let Y (l : Fin K) (x : Ω) := c l x * X l x
  have hca (l : Fin K) : AEStronglyMeasurable (c l) μ :=
    ((hcmeas l).mono hm).aestronglyMeasurable
  have hcb (l : Fin K) : ∀ᵐ x ∂μ, ‖c l x‖ ≤ C := by
    filter_upwards [hc] with x hx
    simpa only [Real.norm_eq_abs] using hx l
  have hcab (l r : Fin K) : ∀ᵐ x ∂μ, ‖c l x * c r x‖ ≤ C ^ 2 := by
    filter_upwards [hc] with x hx
    simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
      mul_le_mul (hx l) (hx r) (abs_nonneg _) hC
  have hxi (l : Fin K) : Integrable (X l) μ := (hlp l).integrable (by norm_num)
  have hyi (l : Fin K) : Integrable (Y l) μ := (hxi l).bdd_mul (hca l) (hcb l)
  have hxij (l r : Fin K) : Integrable (fun x => X l x * X r x) μ :=
    (hlp l).integrable_mul (hlp r)
  have hyij (l r : Fin K) : Integrable (fun x => Y l x * Y r x) μ := by
    have h := (hxij l r).bdd_mul ((hca l).mul (hca r)) (hcab l r)
    convert h using 1
    funext x
    dsimp [Y]
    ring
  have hy0 (l : Fin K) : condExp m μ (Y l) =ᵐ[μ]
      (0 : Ω → ℝ) := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hcmeas l) (hyi l) (hxi l)
    have hz : condExp m μ (X l) =ᵐ[μ]
        (0 : Ω → ℝ) :=
      hzero l
    filter_upwards [hp, hz] with x hp hz
    change condExp m μ (Y l) x = c l x * condExp m μ (X l) x at hp
    rw [hz] at hp
    simpa only [Pi.zero_apply, mul_zero] using hp
  have hyfactor (l r : Fin K) :
      condExp m μ (fun x => Y l x * Y r x) =ᵐ[μ]
        (fun x => c l x * c r x * ∏ t : Fin (q + 1), κ t l r) := by
    have hab : StronglyMeasurable[m] (fun x => c l x * c r x) :=
      (hcmeas l).mul (hcmeas r)
    have habi := (hxij l r).bdd_mul ((hca l).mul (hca r)) (hcab l r)
    have hp := condExp_mul_of_stronglyMeasurable_left hab habi (hxij l r)
    have heq : (fun x => Y l x * Y r x) =
        (fun x => (c l x * c r x) * (X l x * X r x)) := by
      funext x
      dsimp [Y]
      ring
    rw [heq]
    have hx : condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
        (fun _ => ∏ t : Fin (q + 1), κ t l r) :=
      hfactor l r
    filter_upwards [hp, hx] with x hp hx
    change condExp m μ (fun x => (c l x * c r x) * (X l x * X r x)) x =
      c l x * c r x * condExp m μ (fun x => X l x * X r x) x at hp
    rw [hx] at hp
    exact hp
  exact conditional_variance_cellAverage_factored_le hK Y c κ C V B
    hC hV hB hyi hy0 hyij hyfactor hc hdiag hoff

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
