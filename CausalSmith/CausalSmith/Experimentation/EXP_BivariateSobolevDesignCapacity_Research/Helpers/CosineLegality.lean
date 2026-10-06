module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineFourierEndpoints

/-! # Pooled legality of the normalized cosine prior

The canonical pair coefficients instantiate the proved cutoff restriction bound.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Summing prior coordinates is equivalent to summing ordered pairs and local frequencies.](goal) -/
-- @node: pairIdx_sum_pairs
lemma pairIdx_sum_pairs {d L : ℕ} (f : PairIdx d L → ℝ) :
    (∑ α, f α) = ∑ jl : {jl : Fin d × Fin d // jl.1 < jl.2},
      ∑ ab : Fin L × Fin L, f ⟨(jl.val, ab), jl.property⟩ := by
  let e : PairIdx d L ≃ {jl : Fin d × Fin d // jl.1 < jl.2} × (Fin L × Fin L) :=
    { toFun := fun α => (⟨α.val.1, α.property⟩, α.val.2)
      invFun := fun α => ⟨(α.1.val, α.2), α.1.property⟩
      left_inv := by intro α; rfl
      right_inv := by intro α; rfl }
  calc
    _ = ∑ x : {jl : Fin d × Fin d // jl.1 < jl.2} × (Fin L × Fin L), f (e.symm x) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Each canonical pair effect is the local polynomial with its normalized sign coefficients. Under [the stated conditions](hyp:hjl), [the asserted mathematical result follows](goal). -/
-- @node: mXi_g2_pairCosinePolynomial
lemma mXi_g2_pairCosinePolynomial {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) :
    (fun u : Cube 2 => g2 (mXi s L ξ) j l (u 0) (u 1)) =
      pairCosinePolynomial (fun ab : Fin L × Fin L =>
        (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
          sgn (ξ ⟨((j, l), ab), hjl⟩)) := by
  classical
  funext u
  rw [mXi_g2 s ξ j l hjl, pairIdx_sum_pairs]
  have hc (jl : {jl : Fin d × Fin d // jl.1 < jl.2}) :
      (jl.val.1 = j ∧ jl.val.2 = l) ↔ jl = ⟨(j, l), hjl⟩ := by
    simp [Subtype.ext_iff, Prod.ext_iff]
  simp_rw [hc, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]
  unfold pairCosinePolynomial
  apply Finset.sum_congr rfl
  intro ab _
  ring

/-- [ A local array of normalized signs has squared coefficient energy equal to its cardinality.](goal) Under [the stated conditions](hyp:hjl). -/
-- @node: prior_pair_coefficient_energy
lemma prior_pair_coefficient_energy {d L : ℕ} (s : ℝ) (ξ : PairIdx d L → Bool)
    (j l : Fin d) (hjl : j < l) :
    (∑ ab : Fin L × Fin L,
      ((C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
        sgn (ξ ⟨((j, l), ab), hjl⟩)) ^ 2) =
      (L : ℝ) ^ 2 * (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2 := by
  have hs (ab : Fin L × Fin L) : sgn (ξ ⟨((j, l), ab), hjl⟩) ^ 2 = 1 := by
    cases ξ ⟨((j, l), ab), hjl⟩ <;> norm_num [sgn]
  simp only [mul_pow, hs, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  ring

/-- [ The ordered-coordinate sum of a common pair budget counts each pair exactly once.](goal) Under [the stated conditions](hyp:a). -/
-- @node: ordered_pair_budget_sum
lemma ordered_pair_budget_sum (d : ℕ) (a : ℝ≥0∞) :
    (∑ j : Fin d, ∑ l : Fin d, if j < l then a else 0) = (d.choose 2 : ℝ≥0∞) * a := by
  classical
  rw [← Fintype.sum_prod_type (fun jl : Fin d × Fin d => if jl.1 < jl.2 then a else 0)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc := Fintype.card_product_filter_lt (α := Fin d)
  simpa only [Fintype.card_fin] using congrArg (fun k : ℕ => (k : ℝ≥0∞) * a) hc

/-- [ The pooled real coefficient normalization is exactly one.](goal) Under [the stated conditions](hyp:hd,hL). -/
-- @node: prior_pair_budget_normalized
lemma prior_pair_budget_normalized {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L)
    (s : ℝ) (ξ : PairIdx d L → Bool) :
    (d.choose 2 : ℝ) * (C0 ^ 2 * ((L : ℝ) ^ s) ^ 2) *
      ((L : ℝ) ^ 2 * (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2) = 1 := by
  have hsign (α : PairIdx d L) : sgn (ξ α) ^ 2 = 1 := by
    cases ξ α <;> norm_num [sgn]
  have hb := mXi_coefficient_budget hd hL s ξ
  simp only [mul_pow, hsign, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, pairIdx_card] at hb
  simp only [priorDimension, pairCount, Nat.cast_mul, Nat.cast_pow] at hb ⊢
  nlinarith [hb]

/-- [ Every prior realization satisfies the pooled restriction budget.](goal) Under [the stated conditions](hyp:hd,hL,hs,hs1,hm). -/
-- @node: mXi_pooledBudget
lemma mXi_pooledBudget {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ξ : PairIdx d L → Bool)
    (hm : Measurable (mXi s L ξ) ∧ MemLp (mXi s L ξ) 2 (cubeMeasure d) ∧
      (∫ x, mXi s L ξ x ∂cubeMeasure d) = 0) :
    PooledBudget s ⟨mXi s L ξ, hm⟩ := by
  classical
  let A := ENNReal.ofReal (C0 ^ 2 * ((L : ℝ) ^ s) ^ 2)
  let H := ENNReal.ofReal ((L : ℝ) ^ 2 *
    (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ ^ 2)
  have hp (j l : Fin d) (hjl : j < l) :
      sobolevNormSq 2 s (fun u => g2 (mXi s L ξ) j l (u 0) (u 1)) ≤ A * H := by
    rw [mXi_g2_pairCosinePolynomial s ξ j l hjl]
    have he := pairCosinePolynomial_restriction_bound hL
      (fun ab : Fin L × Fin L =>
        (C0 * (L : ℝ) ^ s * Real.sqrt (priorDimension d L))⁻¹ *
          sgn (ξ ⟨((j, l), ab), hjl⟩)) hs hs1
    rw [prior_pair_coefficient_energy] at he
    exact he
  unfold PooledBudget
  change (∑ j, sobolevNormSq 1 s (fun u => g1 (mXi s L ξ) j (u 0))) + _ ≤ 1
  rw [mXi_main_budget_zero, zero_add]
  calc
    _ ≤ ∑ j : Fin d, ∑ l : Fin d, if j < l then A * H else 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      split_ifs with hjl
      · exact hp j l hjl
      · rfl
    _ = (d.choose 2 : ℝ≥0∞) * (A * H) := ordered_pair_budget_sum d (A * H)
    _ = 1 := by
      dsimp [A, H]
      have hcast : (d.choose 2 : ℝ≥0∞) = ENNReal.ofReal (d.choose 2 : ℝ) := by simp
      rw [hcast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      rw [← mul_assoc, prior_pair_budget_normalized hd hL s ξ]
      norm_num

-- @node: lem:cosine-prior
/-- Every coefficient realization is legal, and all pair features are jointly isotropic,
including pairs sharing a coordinate. This uses [the stated conclusion](goal). -/
lemma cosinePrior_legal_and_isotropic :
    (∀ (d L : ℕ), 2 ≤ d → 1 ≤ L → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ ξ : PairIdx d L → Bool,
      ∃ hm : Measurable (mXi s L ξ) ∧ MemLp (mXi s L ξ) 2 (cubeMeasure d) ∧
        (∫ x, mXi s L ξ x ∂cubeMeasure d) = 0,
        SobolevClass d s ⟨mXi s L ξ, hm⟩) ∧
    (∀ (n d L : ℕ) (hn : 0 < n) (hd : 2 ≤ d) (hL : 1 ≤ L)
      (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Covariates n d),
      UniformDraw μ X → ∀ α β : PairIdx d L,
        (∫ ω, pairFeature α (X ω ⟨0, hn⟩) * pairFeature β (X ω ⟨0, hn⟩) ∂μ) =
          if α = β then 1 else 0) := by
  constructor
  · intro d L hd hL s hs hs1 ξ
    refine ⟨⟨mXi_measurable s ξ, mXi_memLp s ξ, mXi_mean_zero s ξ⟩, ?_⟩
    refine ⟨mXi_orderTwo s ξ _, ?_⟩
    exact mXi_pooledBudget hd hL s hs hs1 ξ _
  · intro n d L hn hd hL Ω _ μ X hX α β
    exact uniformDraw_pairFeature_inner_product hX ⟨0, hn⟩ α β


end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
