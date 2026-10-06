module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ContractionSeries
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowEnergyCounts

/-!
# Averaging and counting disjoint active rows

The revealed and hidden active row sets are counted with their labels intact.
Their independent reveal-energy averages feed the finite contraction series.
-/

public section

open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Counting subsets of the remaining labeled rows gives a binomial sum, extended
by zero to the full row range.  [For the stated data and conditions](hyp:B,A,F), [the stated conclusion holds](goal). -/
-- @node: active_row_complement_sum
lemma active_row_complement_sum (B : ℕ) (A : Finset (Fin B)) (F : ℕ → ℝ) :
    (∑ E ∈ (Finset.univ \ A).powerset, F E.card) =
      ∑ b ∈ Finset.range (B + 1), ((B - A.card).choose b : ℝ) * F b := by
  classical
  rw [Finset.sum_powerset_apply_card]
  have hc : (Finset.univ \ A).card = B - A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp
  simp only [hc, nsmul_eq_mul]
  apply Finset.sum_subset
  · intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  · intro b hb hn
    have hlt : B - A.card < b := by
      simp only [Finset.mem_range] at hn
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- Ordered disjoint active row sets of sizes a and b have exactly the two
binomial factors used by the contraction series.  [For the stated data and conditions](hyp:B,F), [the stated conclusion holds](goal). -/
-- @node: active_row_pair_sum_by_card
lemma active_row_pair_sum_by_card (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
      F A.card E.card) =
      ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
        (B.choose a : ℝ) * ((B - a).choose b : ℝ) * F a b := by
  classical
  simp_rw [active_row_complement_sum]
  have hc := Finset.sum_powerset_apply_card
    (fun a => ∑ b ∈ Finset.range (B + 1), ((B - a).choose b : ℝ) * F a b)
    (x := (Finset.univ : Finset (Fin B)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hc
  rw [hc]
  simp only [Finset.mul_sum, mul_assoc]

/-- A good-event indicator can be dropped from each nonnegative disjoint active
row contribution before averaging independent source reveals.  [For the stated data and conditions](hyp:B,d,h,p,hp,A,E,hAE,G), [the stated conclusion holds](goal). -/
-- @node: active_row_indicator_mean_le
lemma active_row_indicator_mean_le (B d : ℕ) (h p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (A E : Finset (Fin B)) (hAE : Disjoint A E)
    (G : Set (Fin B → Fin d → Bool)) :
    (∫ rows : Fin B → Fin d → Bool, Set.indicator G
      (fun rows => (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
        ((∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
          (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ)))) rows
      ∂Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d => bernoulliLaw p))) ≤
      (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
        ((p * etaOne d h) ^ A.card * (eta d h) ^ E.card) := by
  classical
  let := bernoulliLaw_probability p hp
  let μ := Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d => bernoulliLaw p))
  let c : ℝ := (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card
  let F (rows : Fin B → Fin d → Bool) : ℝ :=
    (∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
      (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hF (rows) : 0 ≤ F rows := mul_nonneg
    (Finset.prod_nonneg (fun ℓ _ => (rowRevealEnergy_bounds d h (rows ℓ)).1))
    (Finset.prod_nonneg (fun ℓ _ => (rowRevealEnergy_bounds d h (rows ℓ)).2.1))
  change (∫ rows, Set.indicator G (fun rows => c * F rows) rows ∂μ) ≤ _
  calc
    _ ≤ ∫ rows, c * F rows ∂μ := by
      apply integral_mono
      · fun_prop
      · fun_prop
      · intro rows
        by_cases hg : rows ∈ G
        · simp [Set.indicator_of_mem hg]
        · simpa [Set.indicator_of_notMem hg] using mul_nonneg hc (hF rows)
    _ = c * ∫ rows, F rows ∂μ := integral_const_mul c F
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (independent_rowRevealEnergy_product_bound B d h p hp A E hAE) hc

/-- Summing labeled disjoint row contributions, omitting the constant term, and
then averaging gives exactly the finite binomial contraction bound.  [For the stated data and conditions](hyp:B,d,h,p,hp,G), [the stated conclusion holds](goal). -/
-- @node: active_row_nonconstant_average_le
lemma active_row_nonconstant_average_le (B d : ℕ) (h p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (G : Set (Fin B → Fin d → Bool)) :
    (∫ rows : Fin B → Fin d → Bool,
      ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        if A.card + E.card = 0 then 0 else Set.indicator G
          (fun rows => (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
            ((∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
              (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ)))) rows
      ∂Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d => bernoulliLaw p))) ≤
      ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
        if a + b = 0 then 0 else
          (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
            (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
              (p * etaOne d h) ^ a * (eta d h) ^ b := by
  classical
  let := bernoulliLaw_probability p hp
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  calc
    _ ≤ ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        if A.card + E.card = 0 then 0 else
          (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
            ((p * etaOne d h) ^ A.card * (eta d h) ^ E.card) := by
      apply Finset.sum_le_sum
      intro A _
      apply Finset.sum_le_sum
      intro E hE
      by_cases hz : A.card + E.card = 0
      · simp [hz]
      · simp only [hz, if_false]
        apply active_row_indicator_mean_le B d h p hp A E
        · apply Finset.disjoint_left.mpr
          intro ℓ hA hEℓ
          have hs := Finset.mem_powerset.mp hE hEℓ
          exact (Finset.mem_sdiff.mp hs).2 hA
    _ = _ := by
      rw [active_row_pair_sum_by_card B (fun a b =>
        if a + b = 0 then 0 else
          (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
            ((p * etaOne d h) ^ a * (eta d h) ^ b))]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring

/-- The averaged nonconstant active-row energy, with any good-event indicator,
is bounded by the exponential/geometric expression of the contraction roadmap.  [For the stated data and conditions](hyp:B,d,h,p,hB,hp,hsmall,G), [the stated conclusion holds](goal). -/
-- @node: active_row_average_contraction_bound
lemma active_row_average_contraction_bound (B d : ℕ) (h p : ℝ)
    (hB : 0 < B) (hp : p ∈ Set.Icc 0 1)
    (hsmall : 4 * Real.exp 1 * eta d h < 1)
    (G : Set (Fin B → Fin d → Bool)) :
    (∫ rows : Fin B → Fin d → Bool,
      ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        if A.card + E.card = 0 then 0 else Set.indicator G
          (fun rows => (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
            ((∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
              (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ)))) rows
      ∂Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d => bernoulliLaw p))) ≤
      Real.exp (Real.exp 1 * B * p * etaOne d h) /
        (1 - 4 * Real.exp 1 * eta d h) - 1 := by
  have henergy := eta_nonneg_le_etaOne d h
  have hx : 0 ≤ p * etaOne d h := mul_nonneg hp.1 (henergy.1.trans henergy.2)
  have hs := contraction_nonconstant_sum_bound B (p * etaOne d h)
    (eta d h) hB hx henergy.1 hsmall
  rw [show Real.exp 1 * (B : ℝ) * (p * etaOne d h) =
    Real.exp 1 * B * p * etaOne d h by ring] at hs
  exact (active_row_nonconstant_average_le B d h p hp G).trans hs

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
