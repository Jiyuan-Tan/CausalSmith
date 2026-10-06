module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairMixtureParity
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Mixed component cancellation and the rectangular Taylor estimate

Both amplitude axes cancel for any block of original records under the hidden
sign prior. Two applications of the mean value theorem turn a bound on the
actual mixed derivative into the product-amplitude component estimate. The
smoothness and product derivative bounds remain explicit inputs, rather than
being assumed by the paper's mixture theorem.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Difference of the two actual block likelihoods, averaged over the same
hidden endpoint-sign prior without assuming independence inside the block. -/
-- @node: mixedComponentDifference
def mixedComponentDifference {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (o : Fin n → Record) (η ζ : ℝ) : ℝ :=
  (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
    ((∑ σ : Fin (k + 1) → Bool, ∏ i ∈ I, recordCellDensity (mixedLaw false k σ η ζ) (o i)) -
      ∑ σ : Fin (k + 1) → Bool, ∏ i ∈ I, recordCellDensity (mixedLaw true k σ η ζ) (o i))

/-- On the zero propensity axis the actual block likelihoods agree draw by draw. [the stated conclusion](goal) holds. -/
-- @node: mixedComponentDifference_zero_left
lemma mixedComponentDifference_zero_left {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (o : Fin n → Record) (ζ : ℝ) : mixedComponentDifference k I o 0 ζ = 0 := by
  simp only [mixedComponentDifference, mixedLaw, mixedCells_zero_left, sub_self, mul_zero]

/-- On the zero prognosis axis global sign reversal reindexes the block prior. [the stated conclusion](goal) holds. -/
-- @node: mixedComponentDifference_zero_right
lemma mixedComponentDifference_zero_right {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (o : Fin n → Record) (η : ℝ) : mixedComponentDifference k I o η 0 = 0 := by
  unfold mixedComponentDifference
  simp only [mixedLaw, mixedCells_zero_right_reverse]
  rw [endpointSign_prior_reverse k (fun σ =>
    ∏ i ∈ I, recordCellDensity (totalCellLaw (mixedCells true k σ η 0)) (o i))]
  simp

/-- Two mean value estimates on the signed rectangle give a product-amplitude
bound when both axes vanish. The derivatives are of the fully substituted function. [the documented result](goal) Under [the stated assumptions](hyp:hleft,hright,hDiff,hCrossDiff,hCross). -/
-- @node: mixture_rectangle_bound
lemma mixture_rectangle_bound (f : ℝ → ℝ → ℝ) (η ζ C : ℝ)
    (hleft : ∀ y, f 0 y = 0) (hright : ∀ x, f x 0 = 0)
    (hDiff : ∀ x ∈ Set.uIcc 0 η, DifferentiableAt ℝ (fun s => f s ζ) x)
    (hCrossDiff : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      DifferentiableAt ℝ (fun s => deriv (fun r => f r s) x) y)
    (hCross : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      |deriv (fun s => deriv (fun r => f r s) x) y| ≤ C) :
    |f η ζ| ≤ C * |η * ζ| := by
  have hAxis (x : ℝ) : deriv (fun r => f r 0) x = 0 := by
    have he : (fun r => f r 0) = (fun _ : ℝ => (0 : ℝ)) := funext hright
    rw [he, deriv_const]
  have hFirst (x : ℝ) (hx : x ∈ Set.uIcc 0 η) :
      |deriv (fun r => f r ζ) x| ≤ C * |ζ| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (hCrossDiff x hx) (fun y hy => by simpa only [Real.norm_eq_abs] using hCross x hx y hy)
      (convex_uIcc (0 : ℝ) ζ) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa only [hAxis, sub_zero, Real.norm_eq_abs] using h
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hDiff
    (fun x hx => by simpa only [Real.norm_eq_abs] using hFirst x hx)
    (convex_uIcc (0 : ℝ) η) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [hleft, sub_zero, Real.norm_eq_abs] at h
  calc
    |f η ζ| ≤ C * |ζ| * |η| := h
    _ = C * |η * ζ| := by rw [abs_mul]; ring

/-- [Applying the rectangular estimate to actual mixed blocks uses the two
proved axis identities. Product differentiation is the remaining analytic input. [the documented result](goal) Under [the stated assumptions](hyp:hDiff,hCrossDiff,hCross). -/
-- @node: mixedComponentDifference_taylor_bound
lemma mixedComponentDifference_taylor_bound {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (o : Fin n → Record) (η ζ M : ℝ)
    (hDiff : ∀ x ∈ Set.uIcc 0 η,
      DifferentiableAt ℝ (fun s => mixedComponentDifference k I o s ζ) x)
    (hCrossDiff : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      DifferentiableAt ℝ (fun s => deriv (fun r => mixedComponentDifference k I o r s) x) y)
    (hCross : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      |deriv (fun s => deriv (fun r => mixedComponentDifference k I o r s) x) y| ≤
        2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) :
    |mixedComponentDifference k I o η ζ| ≤
      2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card * |η * ζ| := by
  exact mixture_rectangle_bound _ η ζ _ (mixedComponentDifference_zero_left k I o)
    (mixedComponentDifference_zero_right k I o) hDiff hCrossDiff hCross

/-- Each singleton block cancels throughout the signed support neighborhood,
using exact matching of the actual observed cell tables. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedComponentDifference_singleton
lemma mixedComponentDifference_singleton {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (o : Fin n → Record) (η ζ : ℝ)
    (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    mixedComponentDifference k {i} o η ζ = 0 := by
  simp only [mixedComponentDifference, Finset.prod_singleton, recordCellDensity,
    ← Finset.mul_sum]
  have hmatch := (calib_singletons_spec k hk).1 η ζ hη hζ
    (o i).2.1 (o i).2.2 (o i).1
  calc
    _ = 4 * ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
      ∑ σ, (mixedLaw false k σ η ζ).cells (o i).2.1 (o i).2.2 (o i).1) -
      4 * ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
      ∑ σ, (mixedLaw true k σ η ζ).cells (o i).2.1 (o i).2.2 (o i).1) := by ring
    _ = 0 := by rw [hmatch]; ring

/-- [The actual mixed component square-root discrepancy follows from its
rectangular Taylor estimate and one-record floors. No record independence
inside the block is used. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hDiff,hCrossDiff,hCross). -/
-- @node: mixed_component_hellinger_taylor_bound
lemma mixed_component_hellinger_taylor_bound {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (o : Fin n → Record) (η ζ M : ℝ)
    (hη : |η| ≤ 1 / 100) (hζ : |ζ| ≤ 1 / 100)
    (hDiff : ∀ x ∈ Set.uIcc 0 η,
      DifferentiableAt ℝ (fun s => mixedComponentDifference k I o s ζ) x)
    (hCrossDiff : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      DifferentiableAt ℝ (fun s => deriv (fun r => mixedComponentDifference k I o r s) x) y)
    (hCross : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      |deriv (fun s => deriv (fun r => mixedComponentDifference k I o r s) x) y| ≤
        2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) :
    (Real.sqrt ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw false k σ η ζ) (o i)) -
      Real.sqrt ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw true k σ η ζ) (o i))) ^ 2 ≤
      M ^ 4 * (I.card : ℝ) ^ 4 * 8 ^ I.card * (η * ζ) ^ 2 := by
  have hfloor (b : Bool) (σ : Fin (k + 1) → Bool) (i : Fin n) :
      (1 / 2 : ℝ) ≤ recordCellDensity (mixedLaw b k σ η ζ) (o i) :=
    (mixedDensity_bounds b k σ η ζ hη hζ (o i).2.1 (o i).2.2 (o i).1).1
  have hFlo := mixture_average_product_lower k I
    (fun σ i => recordCellDensity (mixedLaw false k σ η ζ) (o i))
    (fun σ i _ => hfloor false σ i)
  have hGlo := mixture_average_product_lower k I
    (fun σ i => recordCellDensity (mixedLaw true k σ η ζ) (o i))
    (fun σ i _ => hfloor true σ i)
  have hTaylor := mixedComponentDifference_taylor_bound k I o η ζ M hDiff hCrossDiff hCross
  have hDifference :
      |(Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
          (∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw false k σ η ζ) (o i)) -
        (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
          ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw true k σ η ζ) (o i)| ≤
      2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card * |η * ζ| := by
    simpa only [mixedComponentDifference, mul_sub] using hTaylor
  exact mixture_component_pointwise_bound I.card M (η * ζ) _ _ hFlo hGlo hDifference

end CausalSmith.Stat.LogoddsLowsmoothFrontier
