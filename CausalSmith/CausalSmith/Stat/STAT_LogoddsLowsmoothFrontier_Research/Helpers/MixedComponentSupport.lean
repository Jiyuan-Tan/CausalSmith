module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ComponentPriorRestriction
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedCoordinateDerivatives

/-! # Mixed component bounds from calibrated record support

The full derivative envelope supplies scalar amplitude partials. Product
differentiation and two-axis cancellation bound each actual block likelihood;
restriction of the uniform hidden sign prior transfers the bound to components.
-/
public section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

attribute [local instance] Classical.propDecidable

/-- [Every scalar partial needed by the rectangular Taylor estimate follows
from the actual mixed record's full derivative and smoothness envelopes. [the documented result](goal) Under [the stated assumptions](hyp:x,hx,hy). Under [the stated assumptions](hyp:hk). -/
-- @node: mixed_record_derivatives_from_support
lemma mixed_record_derivatives_from_support (k : ℕ) (hk : 1 ≤ k)
    (b : Bool) (σ : Fin (k+1) → Bool) (o : Record) (x y : ℝ)
    (hx : |x| ≤ calibEps) (hy : |y| ≤ calibEps) :
    (∀ᶠ z in 𝓝 y, DifferentiableAt ℝ
      (fun r => recordCellDensity (mixedLaw b k σ r z) o) x) ∧
    DifferentiableAt ℝ (fun z => recordCellDensity (mixedLaw b k σ x z) o) y ∧
    DifferentiableAt ℝ (fun z => deriv (fun r =>
      recordCellDensity (mixedLaw b k σ r z) o) x) y ∧
    |deriv (fun r => recordCellDensity (mixedLaw b k σ r y) o) x| ≤ calibM ∧
    |deriv (fun z => recordCellDensity (mixedLaw b k σ x z) o) y| ≤ calibM ∧
    |deriv (fun z => deriv (fun r =>
      recordCellDensity (mixedLaw b k σ r z) o) x) y| ≤ calibM := by
  have hs := calib_mixed_smoothness_spec k hk σ x y hx hy b o.2.1 o.2.2 o.1
  have hd := (((calib_constants_spec.2.2.2 k hk σ).1 x y hx hy b).2
    o.2.1 o.2.2 o.1).2.2
  exact mixed_coordinate_derivative_bounds _ x y calibM hs
    (hd 1 le_rfl (by norm_num)) (hd 2 (by norm_num) le_rfl)

/-- [The actual mixed block satisfies the two-axis component Hellinger estimate
with the jointly selected support constants and no independent-record premise. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ). Under [the stated assumptions](hyp:hk). -/
-- @node: mixed_block_hellinger_from_support
lemma mixed_block_hellinger_from_support {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (I : Finset (Fin n)) (o : Fin n → Record) (η ζ : ℝ)
    (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw false k σ η ζ) (o i)) -
      Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw true k σ η ζ) (o i)))^2 ≤
      calibM^4 * (I.card : ℝ)^4 * 8^I.card * (η*ζ)^2 := by
  have hsmall (z a : ℝ) (hz : z ∈ Set.uIcc 0 a) (ha : |a| ≤ calibEps) :
      |z| ≤ calibEps := by
    rw [Set.mem_uIcc] at hz
    rcases hz with hz | hz
    · rw [abs_of_nonneg hz.1]
      exact hz.2.trans ((le_abs_self a).trans ha)
    · rw [abs_of_nonpos hz.2]
      exact (neg_le_neg hz.1).trans ((neg_le_abs a).trans ha)
  have hp (x : ℝ) (hx : x ∈ Set.uIcc 0 η) (y : ℝ) (hy : y ∈ Set.uIcc 0 ζ)
      (b : Bool) (σ : Fin (k+1) → Bool) (i : Fin n) :=
    mixed_record_derivatives_from_support k hk b σ (o i) x y
      (hsmall x η hx hη) (hsmall y ζ hy hζ)
  apply mixed_component_hellinger_of_record_derivatives k I o η ζ calibM
    (hη.trans calib_regularity_spec.1) (hζ.trans calib_regularity_spec.1)
    calib_regularity_spec.2.1
  · intro x hx y hy
    simp only [Filter.eventually_all]
    intro b σ i hi
    exact (hp x hx y hy b σ i).1
  · intro x hx y hy b σ i hi
    exact (hp x hx y hy b σ i).2.1
  · intro x hx y hy b σ i hi
    exact (hp x hx y hy b σ i).2.2.1
  · intro x hx y hy b σ i hi
    exact (hp x hx y hy b σ i).2.2.2.1
  · intro x hx y hy b σ i hi
    exact (hp x hx y hy b σ i).2.2.2.2.1
  · intro x hx y hy b σ i hi
    exact (hp x hx y hy b σ i).2.2.2.2.2

/-- [Restricting the uniform sign prior preserves the actual mixed block bound,
with the exact number of original records in the selected graph component. [the documented result](goal) Under [the stated assumptions](hyp:x,l,hη,hζ). Under [the stated assumptions](hyp:hk). -/
-- @node: mixed_component_hellinger_from_support
lemma mixed_component_hellinger_from_support {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (η ζ : ℝ) (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : Fin n // block i = c},
          recordCellDensity (mixedLaw false k (componentSignExtension owner c σ) η ζ) (x i.1,l i)) -
      Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : Fin n // block i = c},
          recordCellDensity (mixedLaw true k (componentSignExtension owner c σ) η ζ) (x i.1,l i)))^2 ≤
      calibM^4 * (Fintype.card {i : Fin n // block i = c} : ℝ)^4 *
        8^(Fintype.card {i : Fin n // block i = c}) * (η*ζ)^2 := by
  classical
  dsimp only
  rw [← mixedDensity_block_average_restrict k hk x c l false η ζ hη hζ,
    ← mixedDensity_block_average_restrict k hk x c l true η ζ hη hζ]
  let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
  let I := Finset.univ.filter (fun i => block i = c)
  let o : Fin n → Record := fun i => (x i, if h : block i = c then l ⟨i,h⟩ else (false,false))
  have hp (P : ObservedLaw) : (∏ i ∈ I, recordCellDensity P (o i)) =
      ∏ i : {i : Fin n // block i = c}, recordCellDensity P (x i.1,l i) := by
    rw [Finset.prod_subtype (p := fun i => block i = c) I (by simp [I])]
    apply Finset.prod_congr rfl
    intro i _
    simp only [o, dif_pos i.2]
    rfl
  have hc : I.card = Fintype.card {i : Fin n // block i = c} := by
    rw [Fintype.card_subtype]
  have h := mixed_block_hellinger_from_support k hk I o η ζ hη hζ
  simp only [hp, hc] at h
  exact h

end CausalSmith.Stat.LogoddsLowsmoothFrontier
