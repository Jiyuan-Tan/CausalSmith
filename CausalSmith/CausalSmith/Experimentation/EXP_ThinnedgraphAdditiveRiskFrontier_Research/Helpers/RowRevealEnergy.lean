module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockReveal
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelEnergy

/-!
# Revealed and hidden row energies

Splits the nonconstant Walsh energy by whether a source subset contains a revealed
label. Under independent source reveals, the expected revealed energy is at most
the reveal probability times the order-weighted channel energy.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Nonconstant energy attached to a labeled source subset; the empty subset is excluded. -/
-- @node: rowSubsetEnergy
def rowSubsetEnergy (d : ℕ) (h : ℝ) (E : Finset (Fin d)) : ℝ :=
  if E = ∅ then 0 else gamma d h E.card

/-- Energy of source subsets containing at least one actually revealed label. -/
-- @node: rowRevealedEnergy
def rowRevealedEnergy (d : ℕ) (h : ℝ) (r : Fin d → Bool) : ℝ :=
  ∑ E : Finset (Fin d), if ∃ j ∈ E, r j = true then rowSubsetEnergy d h E else 0

/-- Energy of nonempty source subsets containing only hidden labels. -/
-- @node: rowHiddenEnergy
def rowHiddenEnergy (d : ℕ) (h : ℝ) (r : Fin d → Bool) : ℝ :=
  ∑ E : Finset (Fin d), if ∃ j ∈ E, r j = true then 0 else rowSubsetEnergy d h E

/-- Each source subset contributes nonnegative energy.  [For the stated data and conditions](hyp:d,h,E), [the stated conclusion holds](goal). -/
-- @node: rowSubsetEnergy_nonneg
lemma rowSubsetEnergy_nonneg (d : ℕ) (h : ℝ) (E : Finset (Fin d)) :
    0 ≤ rowSubsetEnergy d h E := by
  unfold rowSubsetEnergy
  split_ifs
  · exact le_rfl
  · exact gamma_nonneg d h E.card

/-- Counting subsets by cardinality recovers the total nonconstant channel energy.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: rowSubsetEnergy_sum
lemma rowSubsetEnergy_sum (d : ℕ) (h : ℝ) :
    (∑ E : Finset (Fin d), rowSubsetEnergy d h E) = eta d h := by
  have hc := Finset.sum_powerset_apply_card
    (fun s => if s = 0 then (0 : ℝ) else gamma d h s)
    (x := (Finset.univ : Finset (Fin d)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_eq_zero, nsmul_eq_mul] at hc
  change (∑ E : Finset (Fin d), if E = ∅ then 0 else gamma d h E.card) = _
  rw [hc]
  have hr : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext s
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [ite_true, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [if_neg (by have := (Finset.mem_Icc.mp hs).1; omega)]

/-- Revealed and hidden subsets partition the full nonconstant row energy.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowRevealEnergy_split
lemma rowRevealEnergy_split (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    rowRevealedEnergy d h r + rowHiddenEnergy d h r = eta d h := by
  rw [rowRevealedEnergy, rowHiddenEnergy, ← Finset.sum_add_distrib,
    ← rowSubsetEnergy_sum d h]
  apply Finset.sum_congr rfl
  intro E _
  split_ifs <;> simp

/-- Both parts are nonnegative, and hidden row energy is bounded by total energy.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: rowRevealEnergy_bounds
lemma rowRevealEnergy_bounds (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    0 ≤ rowRevealedEnergy d h r ∧ 0 ≤ rowHiddenEnergy d h r ∧
      rowHiddenEnergy d h r ≤ eta d h := by
  have hR : 0 ≤ rowRevealedEnergy d h r := by
    apply Finset.sum_nonneg
    intro E _
    split_ifs
    · exact rowSubsetEnergy_nonneg d h E
    · exact le_rfl
  have hH : 0 ≤ rowHiddenEnergy d h r := by
    apply Finset.sum_nonneg
    intro E _
    split_ifs
    · exact le_rfl
    · exact rowSubsetEnergy_nonneg d h E
  exact ⟨hR, hH, by linarith [rowRevealEnergy_split d h r]⟩

/-- A subset of independently revealed source labels is hit with its exact OR probability.  [For the stated data and conditions](hyp:d,E,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowSubset_reveal_law
lemma rowSubset_reveal_law (d : ℕ) (E : Finset (Fin d)) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (Measure.pi (fun _ : Fin d => bernoulliLaw p)).map
      (fun r => decide (∃ j ∈ E, r j = true)) = bernoulliLaw (retentionP E.card p) := by
  let e : Fin E.card ≃ E := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Fin E.card → Fin d := fun j => (e j).val
  have hf : Function.Injective f := by
    intro j k hjk
    exact e.injective (Subtype.ext hjk)
  have hs := bernoulli_select_coordinates f hf p hp
  have hm := congrArg (fun μ : Measure (Fin E.card → Bool) =>
    μ.map (fun r => decide (∃ j, r j = true))) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop), bernoulli_any_coordinate E.card p hp] at hm
  convert hm using 1
  congr 1
  funext r
  apply Bool.decide_congr
  constructor
  · rintro ⟨j, hj, hr⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨j, hj⟩
    exact ⟨k, by simpa [f, hk] using hr⟩
  · rintro ⟨k, hk⟩
    exact ⟨f k, (e k).property, hk⟩

/-- Exact mean of a subset's reveal indicator.  [For the stated data and conditions](hyp:d,E,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowSubset_reveal_mean
lemma rowSubset_reveal_mean (d : ℕ) (E : Finset (Fin d)) (p : ℝ)
    (hp : p ∈ Set.Icc 0 1) :
    (∫ r, (if ∃ j ∈ E, r j = true then (1 : ℝ) else 0)
      ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) = retentionP E.card p := by
  have he := integral_map (μ := Measure.pi (fun _ : Fin d => bernoulliLaw p))
    (φ := fun r => decide (∃ j ∈ E, r j = true)) (by fun_prop)
    (f := fun b : Bool => if b = true then (1 : ℝ) else 0) (by fun_prop)
  rw [rowSubset_reveal_law d E p hp] at he
  simp only [decide_eq_true_eq] at he
  have hp' := retentionP_mem_Icc E.card p hp
  rw [← he]
  rw [bernoulliLaw, integral_add_measure, integral_smul_measure, integral_smul_measure]
  · simp [ENNReal.toReal_ofReal hp'.1]
  · exact (Integrable.of_finite (μ := Measure.dirac false)).smul_measure (by finiteness)
  · exact (Integrable.of_finite (μ := Measure.dirac true)).smul_measure (by finiteness)

/-- The elementary union bound controls a subset's probability of containing a reveal.  [For the stated data and conditions](hyp:s,p,hp), [the stated conclusion holds](goal). -/
-- @node: retentionP_le_order_mul
lemma retentionP_le_order_mul (s : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    retentionP s p ≤ (s : ℝ) * p := by
  have hpow := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith [hp.2]) s
  unfold retentionP
  convert (show 1 - (1 + -p) ^ s ≤ (s : ℝ) * p by linarith [hpow]) using 1
  ring

/-- Independent source reveals give exactly the cardinality-weighted revealed row energy.  [For the stated data and conditions](hyp:d,h,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowRevealedEnergy_mean
lemma rowRevealedEnergy_mean (d : ℕ) (h p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r, rowRevealedEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) =
      ∑ E : Finset (Fin d), retentionP E.card p * rowSubsetEnergy d h E := by
  let := bernoulliLaw_probability p hp
  unfold rowRevealedEnergy
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro E _
  have hf : (fun r : Fin d → Bool => if ∃ j ∈ E, r j = true then rowSubsetEnergy d h E else 0) =
      fun r => (if ∃ j ∈ E, r j = true then (1 : ℝ) else 0) * rowSubsetEnergy d h E := by
    funext r
    split_ifs <;> simp
  rw [hf, integral_mul_const, rowSubset_reveal_mean d E p hp]

/-- Counting source subsets by order gives the exact revealed-energy mean from the roadmap.  [For the stated data and conditions](hyp:d,h,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowRevealedEnergy_mean_by_order
lemma rowRevealedEnergy_mean_by_order (d : ℕ) (h p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r, rowRevealedEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) =
      ∑ s ∈ Finset.Icc 1 d, (d.choose s : ℝ) * retentionP s p * gamma d h s := by
  rw [rowRevealedEnergy_mean d h p hp]
  have hf (E : Finset (Fin d)) : retentionP E.card p * rowSubsetEnergy d h E =
      retentionP E.card p * gamma d h E.card := by
    by_cases hE : E = ∅
    · simp [hE, retentionP]
    · simp [rowSubsetEnergy, hE]
  simp_rw [hf]
  have hc := Finset.sum_powerset_apply_card (fun s => retentionP s p * gamma d h s)
    (x := (Finset.univ : Finset (Fin d)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  rw [hc]
  have hr : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext s
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [retentionP, pow_zero, sub_self, zero_mul, mul_zero, zero_add, mul_assoc]

/-- Counting order-weighted subset energies recovers the weighted Walsh channel energy.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: rowSubsetEnergy_weighted_sum
lemma rowSubsetEnergy_weighted_sum (d : ℕ) (h : ℝ) :
    (∑ E : Finset (Fin d), (E.card : ℝ) * rowSubsetEnergy d h E) = etaOne d h := by
  have hc := Finset.sum_powerset_apply_card (fun s => (s : ℝ) * gamma d h s)
    (x := (Finset.univ : Finset (Fin d)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  have hf (E : Finset (Fin d)) : (E.card : ℝ) * rowSubsetEnergy d h E =
      (E.card : ℝ) * gamma d h E.card := by
    by_cases hE : E = ∅
    · simp [hE]
    · simp [rowSubsetEnergy, hE]
  simp_rw [hf]
  rw [hc]
  have hr : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext s
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The expected revealed row energy is at most reveal probability times weighted energy.  [For the stated data and conditions](hyp:d,h,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowRevealedEnergy_mean_le
lemma rowRevealedEnergy_mean_le (d : ℕ) (h p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r, rowRevealedEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) ≤
      p * etaOne d h := by
  rw [rowRevealedEnergy_mean d h p hp, ← rowSubsetEnergy_weighted_sum d h, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro E _
  calc
    _ ≤ ((E.card : ℝ) * p) * rowSubsetEnergy d h E :=
      mul_le_mul_of_nonneg_right (retentionP_le_order_mul E.card p hp)
        (rowSubsetEnergy_nonneg d h E)
    _ = _ := by ring

/-- The mean hidden energy is the complement of the mean revealed energy.  [For the stated data and conditions](hyp:d,h,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowHiddenEnergy_mean_split
lemma rowHiddenEnergy_mean_split (d : ℕ) (h p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r, rowRevealedEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) +
      (∫ r, rowHiddenEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) =
        eta d h := by
  let := bernoulliLaw_probability p hp
  rw [← integral_add Integrable.of_finite Integrable.of_finite]
  simp_rw [rowRevealEnergy_split]
  simp

/-- The mean hidden row energy lies between zero and total channel energy.  [For the stated data and conditions](hyp:d,h,p,hp), [the stated conclusion holds](goal). -/
-- @node: rowHiddenEnergy_mean_bounds
lemma rowHiddenEnergy_mean_bounds (d : ℕ) (h p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    0 ≤ (∫ r, rowHiddenEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) ∧
      (∫ r, rowHiddenEnergy d h r ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) ≤
        eta d h := by
  have hR : 0 ≤ (∫ r, rowRevealedEnergy d h r
      ∂(Measure.pi (fun _ : Fin d => bernoulliLaw p))) :=
    integral_nonneg (fun r => (rowRevealEnergy_bounds d h r).1)
  exact ⟨integral_nonneg (fun r => (rowRevealEnergy_bounds d h r).2.1),
    by linarith [rowHiddenEnergy_mean_split d h p hp]⟩

/-- Independent row reveals factor the energies of disjoint active revealed and hidden
row sets, giving the product bound in the contraction roadmap.  [For the stated data and conditions](hyp:B,d,h,p,hp,A,E,hAE), [the stated conclusion holds](goal). -/
-- @node: independent_rowRevealEnergy_product_bound
lemma independent_rowRevealEnergy_product_bound (B d : ℕ) (h p : ℝ)
    (hp : p ∈ Set.Icc 0 1) (A E : Finset (Fin B)) (hAE : Disjoint A E) :
    (∫ rows : Fin B → Fin d → Bool,
      (∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
        (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ))
      ∂(Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d => bernoulliLaw p)))) ≤
      (p * etaOne d h) ^ A.card * (eta d h) ^ E.card := by
  let := bernoulliLaw_probability p hp
  let μ := Measure.pi (fun _ : Fin d => bernoulliLaw p)
  let F (ℓ : Fin B) (r : Fin d → Bool) : ℝ :=
    (if ℓ ∈ A then rowRevealedEnergy d h r else 1) *
      (if ℓ ∈ E then rowHiddenEnergy d h r else 1)
  have hF (rows : Fin B → Fin d → Bool) :
      (∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
        (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ)) = ∏ ℓ, F ℓ (rows ℓ) := by
    simp only [F, Finset.prod_mul_distrib]
    simp
  simp_rw [hF]
  rw [integral_fintype_prod_eq_prod F]
  calc
    (∏ ℓ : Fin B, ∫ r, F ℓ r ∂μ) ≤
        ∏ ℓ : Fin B, (if ℓ ∈ A then p * etaOne d h else 1) *
          (if ℓ ∈ E then eta d h else 1) := by
      apply Finset.prod_le_prod
      · intro ℓ _
        apply integral_nonneg
        intro r
        exact mul_nonneg
          (by split_ifs <;> first | exact (rowRevealEnergy_bounds d h r).1 | positivity)
          (by split_ifs <;> first | exact (rowRevealEnergy_bounds d h r).2.1 | positivity)
      · intro ℓ _
        by_cases hA : ℓ ∈ A
        · have hE : ℓ ∉ E := fun hE => Finset.disjoint_left.mp hAE hA hE
          simpa [F, μ, hA, hE] using rowRevealedEnergy_mean_le d h p hp
        · by_cases hE : ℓ ∈ E
          · simpa [F, μ, hA, hE] using (rowHiddenEnergy_mean_bounds d h p hp).2
          · simp [F, μ, hA, hE]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
