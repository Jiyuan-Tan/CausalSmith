module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseRowMoments
public import Mathlib.Probability.Moments.Variance

/-!
# Labeled source-row variance in the reverse test

Actual source fibers have the row marginals used in the sign calculations.
Their disjoint labels give independent row signals and additive variances.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The revealed sign sum at the original labels of a source row. -/
-- @node: reverseRowA
def reverseRowA (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
    if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0

/-- The total sign sum at the original labels of a source row. -/
-- @node: reverseRowT
def reverseRowT (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
    signOf (zr.1 ⟨j.val, by omega⟩)

/-- Reindexing a true source fiber connects its two sums to the actual row law.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ,p,hp,f), [the stated conclusion holds](goal). -/
-- @node: reverse_source_row_integral
lemma reverse_source_row_integral (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (f : ℝ → ℝ → ℝ) :
    (∫ zr, f (reverseRowA n B d hfit s ℓ zr) (reverseRowT n B d hfit s ℓ zr)
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) =
    ∫ zr, f (∑ k : Fin d, if zr.2 k then signOf (zr.1 k) else 0)
      (∑ k : Fin d, signOf (zr.1 k))
      ∂((halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p))) := by
  let R := Finset.univ.filter (fun j => s.1 j = ℓ)
  let e : Fin d ≃ R := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact (s.2 ℓ).symm)
  let j : Fin d → Fin (B * d) := fun k => (e k).val
  let v : Fin d → Fin n := fun k => ⟨(j k).val, by have := (j k).isLt; omega⟩
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hv : Function.Injective v := by
    intro a b hab
    apply hj
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
  have hs (g : Fin (B * d) → ℝ) : (∑ k : Fin d, g (j k)) = ∑ k ∈ R, g k := by
    rw [← Finset.sum_coe_sort R g]
    exact e.sum_comp (fun k : R => g k.val)
  have hA (zr : Assign (Fin n) × (Fin (B * d) → Bool)) :
      reverseRowA n B d hfit s ℓ zr =
        ∑ k : Fin d, if zr.2 (j k) then signOf (zr.1 (v k)) else 0 := by
    exact (hs (fun k => if zr.2 k then signOf (zr.1 ⟨k.val, by omega⟩) else 0)).symm
  have hT (zr : Assign (Fin n) × (Fin (B * d) → Bool)) :
      reverseRowT n B d hfit s ℓ zr = ∑ k : Fin d, signOf (zr.1 (v k)) := by
    exact (hs (fun k => signOf (zr.1 ⟨k.val, by omega⟩))).symm
  simp_rw [hA, hT]
  exact reverse_row_injection_integral p hp v j hv hj
    (fun zr => f (∑ k, if zr.2 k then signOf (zr.1 k) else 0)
      (∑ k, signOf (zr.1 k)))

/-- The actual revealed row energy equals dp.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_row_second
lemma reverse_source_row_second (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, (reverseRowA n B d hfit s ℓ zr) ^ 2
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) = d * p := by
  rw [reverse_source_row_integral n B d hfit s ℓ p hp (fun a _ => a ^ 2)]
  exact reverse_row_second_moment d p hp

/-- The actual row signal mean equals dp.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_row_product_mean
lemma reverse_source_row_product_mean (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) = d * p := by
  rw [reverse_source_row_integral n B d hfit s ℓ p hp (fun a t => a * t)]
  exact reverse_row_product_mean d p hp

/-- The actual row signal second moment is at most 3d²p.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_row_product_second_le
lemma reverse_source_row_product_second_le (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, (reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr) ^ 2
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) ≤ 3 * (d : ℝ) ^ 2 * p := by
  rw [reverse_source_row_integral n B d hfit s ℓ p hp (fun a t => (a * t) ^ 2)]
  exact reverse_row_product_second_le d p hp

/-- Each source's sign and reveal form an independent paired coordinate.  [For the stated data and conditions](hyp:n,B,d,hfit,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_pairs_independent
lemma reverse_source_pairs_independent (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    iIndepFun (fun j : Fin (B * d) =>
      fun zr : Assign (Fin n) × (Fin (B * d) → Bool) =>
        (zr.1 ⟨j.val, by omega⟩, zr.2 j))
      ((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p))) := by
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability (1 / 2) (by constructor <;> norm_num)
  let := bernoulliLaw_probability p hp
  let v : Fin (B * d) → Fin n := fun j => ⟨j.val, by omega⟩
  have hv : Function.Injective v := by
    intro a b hab
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hab)
  let ν := (halfBernoulli (Fin n)).prod
    (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p))
  let g := fun zr : Assign (Fin n) × (Fin (B * d) → Bool) =>
    fun j => (zr.1 (v j), zr.2 j)
  let ρ := (bernoulliLaw (1 / 2)).prod (bernoulliLaw p)
  have hm : ν.map g = Measure.pi (fun _ : Fin (B * d) => ρ) := by
    have hr := reverse_row_injection_law p hp v id hv Function.injective_id
    have he := MeasurePreserving.symm
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin (B * d)))
      (measurePreserving_arrowProdEquivProdArrow Bool Bool (Fin (B * d))
        (fun _ => bernoulliLaw (1 / 2)) (fun _ => bernoulliLaw p))
    have ht := congrArg (fun μ => μ.map
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin (B * d))).symm) hr
    rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at ht
    change ν.map g = _ at ht
    exact ht.trans he.map_eq
  have hc (j : Fin (B * d)) : ν.map (fun zr => g zr j) = ρ := by
    change ν.map ((fun x : Fin (B * d) → Bool × Bool => x j) ∘ g) = ρ
    rw [← Measure.map_map (measurable_pi_apply j) (measurable_of_finite g), hm]
    exact (measurePreserving_eval (fun _ : Fin (B * d) => ρ) j).map_eq
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ =>
    (measurable_of_finite _).aemeasurable)).mpr
  change ν.map g = Measure.pi (fun j => ν.map (fun zr => g zr j))
  simp only [hc, hm]

/-- Disjoint source fibers give independent row signals in the original-input law.  [For the stated data and conditions](hyp:n,B,d,hfit,s,p,hp,i,j,hij), [the stated conclusion holds](goal). -/
-- @node: reverse_source_row_signals_independent
lemma reverse_source_row_signals_independent (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (i j : Fin B) (hij : i ≠ j) :
    IndepFun
      (fun zr => reverseRowA n B d hfit s i zr * reverseRowT n B d hfit s i zr)
      (fun zr => reverseRowA n B d hfit s j zr * reverseRowT n B d hfit s j zr)
      ((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p))) := by
  let R (ℓ : Fin B) := Finset.univ.filter (fun k => s.1 k = ℓ)
  have hd : Disjoint (R i) (R j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    exact hij ((Finset.mem_filter.mp hki).2.symm.trans (Finset.mem_filter.mp hkj).2)
  have hi := (reverse_source_pairs_independent n B d hfit p hp).indepFun_finset
    (R i) (R j) hd (fun _ => measurable_of_finite _)
  let f (ℓ : Fin B) (x : R ℓ → Bool × Bool) : ℝ :=
    (∑ k : R ℓ, if (x k).2 then signOf (x k).1 else 0) *
      (∑ k : R ℓ, signOf (x k).1)
  have hf (ℓ : Fin B) (zr : Assign (Fin n) × (Fin (B * d) → Bool)) :
      f ℓ (fun k => (zr.1 ⟨k.val.val, by have := k.val.isLt; omega⟩, zr.2 k.val)) =
        reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr := by
    dsimp only [f]
    rw [Finset.sum_coe_sort (R ℓ) (fun k =>
      if zr.2 k then signOf (zr.1 ⟨k.val, by omega⟩) else 0),
      Finset.sum_coe_sort (R ℓ) (fun k => signOf (zr.1 ⟨k.val, by omega⟩))]
    rfl
  have ht := hi.comp (measurable_of_finite (f i)) (measurable_of_finite (f j))
  simpa only [Function.comp_def, hf] using ht

/-- Independent row variances sum to at most B times the row second-moment bound.  [For the stated data and conditions](hyp:n,B,d,hfit,s,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_signal_variance_le
lemma reverse_source_signal_variance_le (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, ((∑ ℓ, reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr) -
      (B : ℝ) * d * p) ^ 2
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) ≤
      (B : ℝ) * (3 * (d : ℝ) ^ 2 * p) := by
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability p hp
  let ν := (halfBernoulli (Fin n)).prod
    (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p))
  let X := fun ℓ zr => reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr
  have hX (ℓ : Fin B) : MemLp (X ℓ) 2 ν :=
    ⟨(measurable_of_finite _).aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩
  have hm : (∫ zr, ∑ ℓ, X ℓ zr ∂ν) = (B : ℝ) * d * p := by
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp only [X, ν, reverse_source_row_product_mean n B d hfit s _ p hp]
    simp
    ring
  have hv : variance (fun zr => ∑ ℓ, X ℓ zr) ν = ∑ ℓ, variance (X ℓ) ν := by
    have hv := IndepFun.variance_sum (s := Finset.univ) (fun ℓ _ => hX ℓ)
      (fun i _ j _ hij => reverse_source_row_signals_independent n B d hfit s p hp i j hij)
    have hsum : (∑ ℓ, X ℓ) = (fun zr => ∑ ℓ, X ℓ zr) := by
      funext zr
      simp
    rw [hsum] at hv
    exact hv
  have he : (∫ zr, ((∑ ℓ, X ℓ zr) - (B : ℝ) * d * p) ^ 2 ∂ν) =
      variance (fun zr => ∑ ℓ, X ℓ zr) ν := by
    rw [variance_eq_integral (measurable_of_finite _).aemeasurable, hm]
  change (∫ zr, ((∑ ℓ, X ℓ zr) - (B : ℝ) * d * p) ^ 2 ∂ν) ≤ _
  rw [he]
  rw [hv]
  calc
    _ ≤ ∑ _ℓ : Fin B, 3 * (d : ℝ) ^ 2 * p := by
      apply Finset.sum_le_sum
      intro ℓ _
      exact (variance_le_expectation_sq (measurable_of_finite _).aestronglyMeasurable).trans
        (reverse_source_row_product_second_le n B d hfit s ℓ p hp)
    _ = _ := by simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
