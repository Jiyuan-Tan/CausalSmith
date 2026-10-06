module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockStatistics
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ContractionSeries
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowReferenceDomination

/-!
# Weighted energy of constrained hidden allocations

Finite weighted Cauchy–Schwarz and the exact allocation weight count bound each
active-row coefficient's squared norm. The good-event binomial ratio then gives
one contraction factor per hidden active row. These bounds do not assume the
unfinished identification of the conditional likelihood.
-/

public section

open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- Nonnegative allocation weights give the pointwise weighted Cauchy–Schwarz bound.  [For the stated data and conditions](hyp:ι,S,w,v,hw), [the stated conclusion holds](goal). -/
-- @node: hidden_weighted_sum_sq_le
lemma hidden_weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w v : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * v i) ^ 2 ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S, w i * v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * v i)
  have hs (i : ι) (hi : i ∈ S) : Real.sqrt (w i) ^ 2 = w i :=
    Real.sq_sqrt (hw i hi)
  have hp (i : ι) (hi : i ∈ S) :
      Real.sqrt (w i) * (Real.sqrt (w i) * v i) = w i * v i := by
    rw [← mul_assoc, ← pow_two, hs i hi]
  simpa only [Finset.sum_congr rfl hs, Finset.sum_congr rfl hp, mul_pow,
    Finset.sum_congr rfl (fun i hi => congrArg (fun x => x * v i ^ 2) (hs i hi))] using h

/-- Square-integrable summands make a finite weighted sum square-integrable, with
its integral bounded by the sum of the individual weighted energies.  [For the stated data and conditions](hyp:ι,Ω,μ,S,w,v,hw,hm,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_weighted_sum_energy_le
lemma hidden_weighted_sum_energy_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (w : ι → ℝ) (v : ι → Ω → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hm : ∀ i ∈ S, AEStronglyMeasurable (v i) μ)
    (hi : ∀ i ∈ S, Integrable (fun y => v i y ^ 2) μ) :
    Integrable (fun y => (∑ i ∈ S, w i * v i y) ^ 2) μ ∧
      (∫ y, (∑ i ∈ S, w i * v i y) ^ 2 ∂μ) ≤
        (∑ i ∈ S, w i) * ∑ i ∈ S, w i * ∫ y, v i y ^ 2 ∂μ := by
  have hdom : Integrable
      (fun y => (∑ i ∈ S, w i) * ∑ i ∈ S, w i * v i y ^ 2) μ :=
    (integrable_finsetSum S (fun i hiS => (hi i hiS).const_mul (w i))).const_mul _
  have hmeas : AEStronglyMeasurable (fun y => (∑ i ∈ S, w i * v i y) ^ 2) μ :=
    by fun_prop
  have hpoint (y : Ω) := hidden_weighted_sum_sq_le S w (fun i => v i y) hw
  have hint : Integrable (fun y => (∑ i ∈ S, w i * v i y) ^ 2) μ :=
    hdom.mono' hmeas (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (∑ i ∈ S, w i * v i y))] using hpoint y))
  refine ⟨hint, ?_⟩
  have hbound := integral_mono hint hdom hpoint
  rw [integral_const_mul, integral_finsetSum S
    (fun i hiS => (hi i hiS).const_mul (w i))] at hbound
  simpa only [integral_const_mul] using hbound

/-- Restricting the allocation tuples at a fixed total degree can only reduce
 their binomial weight sum. The unrestricted sum is the exact global slot count.  [For the stated data and conditions](hyp:B,u,k,S,hS), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_weight_sum_le
lemma hidden_allocation_weight_sum_le (B : ℕ) (u : Fin B → ℕ) (k : ℕ)
    (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (hS : ∀ t ∈ S, k = ∑ ℓ, (t ℓ).val) :
    (∑ t ∈ S, ∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) ≤
      ((∑ ℓ, u ℓ).choose k : ℝ) := by
  classical
  rw [← block_allocation_weights_sum B u k]
  calc
    _ = ∑ t ∈ S, if k = ∑ ℓ, (t ℓ).val then
        ∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [if_pos (hS t ht)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun t _ _ => by split_ifs <;> positivity)

/-- Each constrained coefficient has energy at most the global binomial count
 times the weighted individual coefficient energies.  [For the stated data and conditions](hyp:Ω,μ,B,u,k,S,v,hS,hm,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_energy_le
lemma hidden_allocation_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℕ) (u : Fin B → ℕ) (k : ℕ)
    (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (v : (∀ ℓ, Fin (u ℓ + 1)) → Ω → ℝ)
    (hS : ∀ t ∈ S, k = ∑ ℓ, (t ℓ).val)
    (hm : ∀ t ∈ S, AEStronglyMeasurable (v t) μ)
    (hi : ∀ t ∈ S, Integrable (fun y => v t y ^ 2) μ) :
    Integrable (fun y => (∑ t ∈ S,
      (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * v t y) ^ 2) μ ∧
    (∫ y, (∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * v t y) ^ 2 ∂μ) ≤
      ((∑ ℓ, u ℓ).choose k : ℝ) *
        ∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * ∫ y, v t y ^ 2 ∂μ := by
  have h := hidden_weighted_sum_energy_le μ S
    (fun t => ∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) v
    (fun t _ => by positivity) hm hi
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (hidden_allocation_weight_sum_le B u k S hS)
    (Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity)
      (integral_nonneg (fun _ => sq_nonneg _))))

/-- Requiring a positive hidden degree on each hidden active row forces the
 total degree to be at least the number of those rows.  [For the stated data and conditions](hyp:B,u,E,t,hE), [the stated conclusion holds](goal). -/
-- @node: hidden_active_rows_le_degree
lemma hidden_active_rows_le_degree (B : ℕ) (u : Fin B → ℕ)
    (E : Finset (Fin B)) (t : ∀ ℓ, Fin (u ℓ + 1))
    (hE : ∀ ℓ ∈ E, 0 < (t ℓ).val) :
    E.card ≤ ∑ ℓ, (t ℓ).val := by
  calc
    E.card = ∑ ℓ ∈ E, 1 := by simp
    _ ≤ ∑ ℓ ∈ E, (t ℓ).val := Finset.sum_le_sum (fun ℓ hℓ => hE ℓ hℓ)
    _ ≤ ∑ ℓ, (t ℓ).val := Finset.sum_le_sum_of_subset (Finset.subset_univ E)

/-- If only active rows have positive capacity and each row has at most d slots,
 their total slot count is at most d times the number of active rows.  [For the stated data and conditions](hyp:B,d,u,T,hzero,hcap), [the stated conclusion holds](goal). -/
-- @node: hidden_active_capacity_le
lemma hidden_active_capacity_le (B d : ℕ) (u : Fin B → ℕ) (T : Finset (Fin B))
    (hzero : ∀ ℓ ∉ T, u ℓ = 0) (hcap : ∀ ℓ ∈ T, u ℓ ≤ d) :
    (∑ ℓ, u ℓ) ≤ d * T.card := by
  calc
    (∑ ℓ, u ℓ) = ∑ ℓ ∈ T, u ℓ := by
      exact (Finset.sum_subset (Finset.subset_univ T)
        (fun ℓ _ hℓ => hzero ℓ hℓ)).symm
    _ ≤ ∑ ℓ ∈ T, d := Finset.sum_le_sum hcap
    _ = d * T.card := by simp [Nat.mul_comm]

/-- Dividing a constrained coefficient energy by the global hidden-slot
 normalizer exposes the binomial ratio from the contraction roadmap.  [For the stated data and conditions](hyp:Ω,μ,B,u,M,k,S,v,hS,hm,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_normalized_energy_le
lemma hidden_allocation_normalized_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℕ) (u : Fin B → ℕ) (M k : ℕ)
    (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (v : (∀ ℓ, Fin (u ℓ + 1)) → Ω → ℝ)
    (hS : ∀ t ∈ S, k = ∑ ℓ, (t ℓ).val)
    (hm : ∀ t ∈ S, AEStronglyMeasurable (v t) μ)
    (hi : ∀ t ∈ S, Integrable (fun y => v t y ^ 2) μ) :
    (∫ y, (∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * v t y) ^ 2 ∂μ) /
      (M.choose k : ℝ) ≤
      (((∑ ℓ, u ℓ).choose k : ℝ) / (M.choose k : ℝ)) *
        ∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * ∫ y, v t y ^ 2 ∂μ := by
  have h := div_le_div_of_nonneg_right
    (hidden_allocation_energy_le μ B u k S v hS hm hi).2
    (Nat.cast_nonneg (M.choose k) : (0 : ℝ) ≤ M.choose k)
  simpa only [mul_div_right_comm] using h

/-- On the good event, a constrained active-row coefficient contracts by one
 factor for each hidden active row. The row energies remain explicit, so this
 does not assume a likelihood expansion or the theorem's chi-squared bound.  [For the stated data and conditions](hyp:Ω,μ,B,d,M,a,b,k,u,S,v,hB,hd,hUM,hU,hgood,hbk,hS,hm,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_good_event_energy_le
lemma hidden_allocation_good_event_energy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B d M a b k : ℕ) (u : Fin B → ℕ)
    (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (v : (∀ ℓ, Fin (u ℓ + 1)) → Ω → ℝ)
    (hB : 0 < B) (hd : 0 < d) (hUM : (∑ ℓ, u ℓ) ≤ M)
    (hU : (∑ ℓ, u ℓ) ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M) (hbk : b ≤ k)
    (hS : ∀ t ∈ S, k = ∑ ℓ, (t ℓ).val)
    (hm : ∀ t ∈ S, AEStronglyMeasurable (v t) μ)
    (hi : ∀ t ∈ S, Integrable (fun y => v t y ^ 2) μ) :
    (∫ y, (∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * v t y) ^ 2 ∂μ) /
      (M.choose k : ℝ) ≤
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
        ∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) * ∫ y, v t y ^ 2 ∂μ := by
  apply (hidden_allocation_normalized_energy_le μ B u M k S v hS hm hi).trans
  exact mul_le_mul_of_nonneg_right
    (hidden_choose_ratio_good_event B d (∑ ℓ, u ℓ) M a b k hB hd hUM hU hgood hbk)
    (Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity)
      (integral_nonneg (fun _ => sq_nonneg _))))

/-- The squared Walsh coefficient is integrable under the normalized row
 reference; boundedness supplies this regularity without an added premise.  [For the stated data and conditions](hyp:d,h,s), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_sq_reference_integrable
lemma walshCoeff_sq_reference_integrable (d : ℕ) (h : ℝ) (s : ℕ) :
    Integrable (fun w => walshCoeff d h s w ^ 2)
      (volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) := by
  let := referenceRowLaw_probability d h
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (walshCoeff_abs_le_one d h w s)

/-- The paper's row energy is exactly the coefficient's squared norm under
 the row reference law, including reference-density zeros.  [For the stated data and conditions](hyp:d,h,s), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_sq_reference_integral
lemma walshCoeff_sq_reference_integral (d : ℕ) (h : ℝ) (s : ℕ) :
    (∫ w, walshCoeff d h s w ^ 2
      ∂volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) = gamma d h s := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (refDensity_nonneg d h _), smul_eq_mul]
  simp_rw [mul_comm (refDensity d h _)]
  rfl

/-- Products of row coefficients have finite squared norm, and independence
 factors that norm into the product of the row energies.  [For the stated data and conditions](hyp:B,d,h,s), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_product_reference_energy
lemma walshCoeff_product_reference_energy (B d : ℕ) (h : ℝ) (s : Fin B → ℕ) :
    Integrable (fun y : Fin B → ℝ => (∏ ℓ, walshCoeff d h (s ℓ) (y ℓ)) ^ 2)
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) ∧
    (∫ y : Fin B → ℝ, (∏ ℓ, walshCoeff d h (s ℓ) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) = ∏ ℓ, gamma d h (s ℓ) := by
  let := referenceRowLaw_probability d h
  have he (y : Fin B → ℝ) : (∏ ℓ, walshCoeff d h (s ℓ) (y ℓ)) ^ 2 =
      ∏ ℓ, walshCoeff d h (s ℓ) (y ℓ) ^ 2 := (Finset.prod_pow _ _ _).symm
  simp_rw [he]
  constructor
  · exact Integrable.fintype_prod (fun ℓ => walshCoeff_sq_reference_integrable d h (s ℓ))
  · rw [integral_fintype_prod_eq_prod (fun ℓ w => walshCoeff d h (s ℓ) w ^ 2)]
    simp_rw [walshCoeff_sq_reference_integral]

/-- Applying the constrained allocation estimate to the actual row Walsh
 coefficients yields the active-row bound in terms of the paper's gamma energies.  [For the stated data and conditions](hyp:B,d,M,a,b,k,h,u,j,S,hB,hd,hUM,hU,hgood,hbk,hS), [the stated conclusion holds](goal). -/
-- @node: hidden_allocation_walsh_energy_le
lemma hidden_allocation_walsh_energy_le (B d M a b k : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (S : Finset (∀ ℓ, Fin (u ℓ + 1)))
    (hB : 0 < B) (hd : 0 < d) (hUM : (∑ ℓ, u ℓ) ≤ M)
    (hU : (∑ ℓ, u ℓ) ≤ d * (a + b))
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M) (hbk : b ≤ k)
    (hS : ∀ t ∈ S, k = ∑ ℓ, (t ℓ).val) :
    (∫ y : Fin B → ℝ, (∑ t ∈ S,
      (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
        ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) / (M.choose k : ℝ) ≤
      (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
        ∑ t ∈ S, (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, gamma d h (j ℓ + (t ℓ).val) := by
  have hbound := hidden_allocation_good_event_energy_le
    (Measure.pi (fun _ : Fin B => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w)))) B d M a b k u S
    (fun t y => ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ))
    hB hd hUM hU hgood hbk hS
    (fun t _ => by
      first | fun_prop |
        exact (Finset.measurable_prod Finset.univ (fun ℓ _ =>
          (walshCoeff_measurable d h (j ℓ + (t ℓ).val)).comp
            (measurable_pi_apply ℓ))).aestronglyMeasurable)
    (fun t _ => (walshCoeff_product_reference_energy B d h
      (fun ℓ => j ℓ + (t ℓ).val)).1)
  simpa only [(walshCoeff_product_reference_energy B d h _).2] using hbound

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
