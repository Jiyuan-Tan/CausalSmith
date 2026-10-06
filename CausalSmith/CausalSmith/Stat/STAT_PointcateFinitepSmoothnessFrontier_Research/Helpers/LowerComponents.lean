module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerComponentFactorization
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerDensityIdentification
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerInformationScales
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerProgramGeometry
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerSampleDensity
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerTensorization
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds

/-! Conditional Hellinger component ledger and the lower-mixture programme. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- Subset likelihoods depend only on their own record coordinates. -/
-- @node: subset_density_depends_on_records
lemma subset_density_depends_on_records (S : Finset (Fin n))
    (x : Fin n → unitInterval) (s t : ℝ) (v w : Fin n → Bool × ℝ)
    (ha : ∀ i ∈ S, v i = w i) :
    subsetDensity κ n S x s t v = subsetDensity κ n S x s t w := by
  unfold subsetDensity
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro i hi
  rw [ha i hi]

/-- Subset likelihoods are measurable as functions of the full record-mark array. -/
-- @node: measurable_subsetDensity_marks
@[fun_prop] lemma measurable_subsetDensity_marks (S : Finset (Fin n))
    (x : Fin n → unitInterval) (s t : ℝ) : Measurable (subsetDensity κ n S x s t) := by
  unfold subsetDensity
  fun_prop

/-- Size-zero and size-one subsets have no Hellinger discrepancy. -/
-- @node: subset_hellinger_small_card
lemma subset_hellinger_small_card (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hS : S.card < 2) (x : Fin n → unitInterval) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (subsetDensity κ n S x (lowerA κ n) (lowerB κ n))
      (subsetDensity κ n S x (lowerA κ n) (-lowerB κ n)) = 0 := by
  by_cases h0 : S.card = 0
  · have he := Finset.card_eq_zero.mp h0
    subst S
    unfold Causalean.Stat.hellingerSqDensity
    simp [subset_density_empty]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
    exact subset_hellinger_singleton κ n hκ hb hn i x

/-- Size at least two components automatically qualify for the macro-window count. -/
-- @node: shared_components_card_filter
lemma shared_components_card_filter (hn : 0 < n) (x : Fin n → unitInterval)
    (m : ℕ) (hm : 2 ≤ m) :
    (sharedComponents κ n x).filter (fun S => S.card = m) =
      (Finset.univ.powersetCard m).filter (fun S =>
        Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
          ∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) := by
  ext S
  simp only [sharedComponents, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hc, hcard⟩
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact ⟨hcard, hc, i, hi, shared_component_vertex_in_window κ n S i hi (by omega) x hc⟩
  · rintro ⟨hcard, hc, _⟩
    exact ⟨hc, hcard⟩

/-- Grouping the weighted component sum by cardinality gives the displayed component ledger. -/
-- @node: shared_components_weighted_sum
lemma shared_components_weighted_sum (hn : 0 < n) (x : Fin n → unitInterval)
    (B : ℕ → ℝ) :
    (∑ S ∈ sharedComponents κ n x, if 2 ≤ S.card then B S.card else 0) =
      ∑ m ∈ Finset.range (n+1), if 2 ≤ m then componentCount κ n m x*B m else 0 := by
  have hm : ∀ S ∈ sharedComponents κ n x, S.card ∈ Finset.range (n+1) := by
    intro S _
    have hc : S.card ≤ n := (Finset.card_le_card (Finset.subset_univ S)).trans_eq (by simp)
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h2 : 2 ≤ m
  · rw [if_pos h2]
    have he (S : Finset (Fin n)) (hS : S ∈ (sharedComponents κ n x).filter
        (fun S => S.card = m)) : (if 2 ≤ S.card then B S.card else 0) = B m := by
      rw [(Finset.mem_filter.mp hS).2, if_pos h2]
    rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul,
      shared_components_card_filter κ n hn x m h2]
    rfl
  · rw [if_neg h2]
    apply Finset.sum_eq_zero
    intro S hS
    rw [(Finset.mem_filter.mp hS).2, if_neg h2]

/-- Tensorized affinity bounds conditional Hellinger discrepancy by all component defects. -/
-- @node: conditional_hellinger_component_sum
lemma conditional_hellinger_component_sum (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (x : Fin n → unitInterval) :
  Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
    (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
    (componentDensity κ n n x (lowerA κ n) (-lowerB κ n)) ≤
  ∑ m ∈ Finset.range (n+1), if 2 ≤ m then
    componentCount κ n m x *
      (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*(m : ℝ)^4*(9/2 : ℝ)^m)
    else 0 := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have ha := (lower_scale_small κ n hκ hn).2.1.1.le
  have hb0 := (lower_scale_small κ n hκ hn).2.2.1.le
  have hapos : |lowerA κ n| ≤ lowerA κ n := by rw [abs_of_nonneg ha]
  have hbpos : |lowerB κ n| ≤ lowerB κ n := by rw [abs_of_nonneg hb0]
  have hbneg : |-lowerB κ n| ≤ lowerB κ n := by rw [abs_neg, abs_of_nonneg hb0]
  have htensor := reference_hellinger_disjoint_blocks_le_sum κ n hκ hn
    (sharedComponents κ n x) id
    (fun S => subsetDensity κ n S x (lowerA κ n) (lowerB κ n))
    (fun S => subsetDensity κ n S x (lowerA κ n) (-lowerB κ n))
    (shared_components_disjoint κ n x)
    (fun S _ => measurable_subsetDensity_marks κ n S x _ _)
    (fun S _ => measurable_subsetDensity_marks κ n S x _ _)
    (fun S _ v w => subset_density_depends_on_records κ n S x _ _ v w)
    (fun S _ v w => subset_density_depends_on_records κ n S x _ _ v w)
    (fun S _ => subset_density_nonneg_ae κ n hκ hn S x _ _ hapos hbpos)
    (fun S _ => subset_density_nonneg_ae κ n hκ hn S x _ _ hapos hbneg)
    (fun S _ => subset_density_integral_one κ n hκ hn S x _ _)
    (fun S _ => subset_density_integral_one κ n hκ hn S x _ _)
  have hfacp := conditional_component_factorization κ n hκ hb hn x
    (lowerA κ n) (lowerB κ n) hapos hbpos
  have hfacm := conditional_component_factorization κ n hκ hb hn x
    (lowerA κ n) (-lowerB κ n) hapos hbneg
  have hfp : (fun z => ∏ S ∈ sharedComponents κ n x,
      subsetDensity κ n S x (lowerA κ n) (lowerB κ n) z) =
      componentDensity κ n n x (lowerA κ n) (lowerB κ n) := by
    funext z
    exact (hfacp z).symm
  have hfm : (fun z => ∏ S ∈ sharedComponents κ n x,
      subsetDensity κ n S x (lowerA κ n) (-lowerB κ n) z) =
      componentDensity κ n n x (lowerA κ n) (-lowerB κ n) := by
    funext z
    exact (hfacm z).symm
  rw [hfp, hfm] at htensor
  apply htensor.trans
  rw [← shared_components_weighted_sum κ n (by omega) x
    (fun m => 144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
      (m : ℝ)^4*(9/2 : ℝ)^m)]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : 2 ≤ S.card
  · rw [if_pos hS]
    exact subset_hellinger_bound κ n hκ hb hn S hS x
  · rw [if_neg hS, subset_hellinger_small_card κ n hκ hb hn S (by omega) x]

/-- At the maximal permitted argument, the cubic coefficient tail has a geometric majorant. -/
-- @node: component_coefficient_majorant
lemma component_coefficient_majorant (m : ℕ) :
    ((m+3 : ℕ) : ℝ)^3 * (1/4 : ℝ)^(m+1) ≤ (27/4 : ℝ)*(2/3 : ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hstep : ((m : ℝ)+4)^3 ≤ (8/3 : ℝ)*((m : ℝ)+3)^3 := by
      nlinarith [sq_nonneg (m : ℝ), mul_nonneg hm (sq_nonneg (m : ℝ))]
    have hpow : 0 ≤ (1/4 : ℝ)^(m+1) := by positivity
    calc
      ((m+1+3 : ℕ) : ℝ)^3 * (1/4 : ℝ)^(m+1+1)
          = (((m : ℝ)+4)^3 * (1/4 : ℝ)^(m+1)) / 4 := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ ((8/3 : ℝ)*((m : ℝ)+3)^3 * (1/4 : ℝ)^(m+1)) / 4 := by
        gcongr
      _ = (2/3 : ℝ)*(((m+3 : ℕ) : ℝ)^3 * (1/4 : ℝ)^(m+1)) := by
        push_cast
        ring
      _ ≤ (2/3 : ℝ)*((27/4 : ℝ)*(2/3 : ℝ)^m) := by gcongr
      _ = (27/4 : ℝ)*(2/3 : ℝ)^(m+1) := by rw [pow_succ]; ring

/-- Summing the coefficient majorant controls the cubic series at one quarter. -/
-- @node: component_quarter_series
lemma component_quarter_series :
    Summable (fun m : ℕ => ((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) ∧
    (∑' m : ℕ, ((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) ≤ 32 := by
  have hg := (hasSum_geometric_of_lt_one (r := (2/3 : ℝ)) (by norm_num)
    (by norm_num)).mul_left (27/4 : ℝ)
  have ht : Summable (fun m : ℕ => ((m+1+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^(m+1)) :=
    Summable.of_nonneg_of_le (fun m => by positivity)
      (fun m => by simpa [Nat.add_assoc] using component_coefficient_majorant m) hg.summable
  have hs : Summable (fun m : ℕ => ((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) :=
    (summable_nat_add_iff 1).mp ht
  refine ⟨hs, ?_⟩
  rw [tsum_eq_zero_add' (f := fun m : ℕ => ((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) ht]
  rw [show ((0+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^0 = 8 by norm_num]
  have hb := ht.tsum_le_tsum
    (fun m => by simpa [Nat.add_assoc] using component_coefficient_majorant m) hg.summable
  rw [hg.tsum_eq] at hb
  have hnum : (27/4 : ℝ) * (1 - 2/3)⁻¹ = 81/4 := by norm_num
  rw [hnum] at hb
  linarith

/-- The numerical all-size geometric ledger has no logarithmic loss. -/
-- @node: component_geometric_series
lemma component_geometric_series (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1/4) :
  Summable (fun m : ℕ => ((m+2 : ℕ) : ℝ)^3 * z^(m+1)) ∧
  (∑' m : ℕ, ((m+2 : ℕ) : ℝ)^3 * z^(m+1)) ≤ 32*z := by
  have hq := component_quarter_series
  have hg := hq.1.mul_right z
  have hdom (m : ℕ) : ((m+2 : ℕ) : ℝ)^3 * z^(m+1) ≤
      (((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) * z := by
    rw [pow_succ z m, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz.1 hz.2 m) (by positivity)) hz.1
  have hz0 := hz.1
  have hs := Summable.of_nonneg_of_le (fun m => by positivity) hdom hg
  refine ⟨hs, ?_⟩
  calc
    (∑' m : ℕ, ((m+2 : ℕ) : ℝ)^3 * z^(m+1))
        ≤ ∑' m : ℕ, (((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) * z :=
      hs.tsum_le_tsum hdom hg
    _ = (∑' m : ℕ, ((m+2 : ℕ) : ℝ)^3 * (1/4 : ℝ)^m) * z := tsum_mul_right
    _ ≤ 32*z := mul_le_mul_of_nonneg_right hq.2 hz.1

/-- The exponential series controls the factorial denominator in the tree count. -/
-- @node: component_factorial_bound
lemma component_factorial_bound (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ)^(m-1)/(Nat.factorial m : ℝ) ≤ (3 : ℝ)^m/(m : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have h := Real.pow_div_factorial_le_exp (m : ℝ) hm0.le (m-1)
  have he : Real.exp (m : ℝ) ≤ (3 : ℝ)^m := by
    rw [← mul_one (m : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le m
  have hfacNat : Nat.factorial m = m*Nat.factorial (m-1) := by
    conv_lhs => rw [show m = (m-1)+1 by omega, Nat.factorial_succ]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hfac : (Nat.factorial m : ℝ) = (m : ℝ)*(Nat.factorial (m-1) : ℝ) := by
    exact_mod_cast hfacNat
  rw [hfac, mul_comm (m : ℝ), ← div_div]
  exact div_le_div_of_nonneg_right (h.trans he) hm0.le

/-- Component counts are finite sums of measurable bounded indicators. -/
-- @node: integrable_componentCount
lemma integrable_componentCount (m : ℕ) :
    Integrable (componentCount κ n m) (Measure.pi (fun _ : Fin n => design)) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have he : componentCount κ n m = fun x =>
      ∑ S ∈ Finset.univ.powersetCard m, if
        Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
          (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0 := by
    funext x
    simp [componentCount, Finset.sum_boole]
  rw [he]
  apply integrable_finsetSum
  intro S _
  exact (integrable_const (1 : ℝ)).mono_nonneg
    ((Measurable.ite (measurable_shared_component_event κ n S)
      measurable_const measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))
    (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))

/-- The expected size-m discrepancy has the cubic geometric coefficient from the roadmap. -/
-- @node: expected_component_discrepancy_bound
lemma expected_component_discrepancy_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1)
    (hn : 2 ≤ n) (m : ℕ) (hm : 2 ≤ m) :
    (∫ x, componentCount κ n m x *
      (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
        (m : ℝ)^4*(9/2 : ℝ)^m) ∂Measure.pi (fun _ : Fin n => design)) ≤
      3888*(n : ℝ)*lowerH κ n *
        (lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)) *
        (m : ℝ)^3 * (54*(n : ℝ)*lowerEll κ n)^(m-1) := by
  have he := (lower_scale_small κ n hκ hn).1.1
  have hh := (lower_macro_scale κ n hκ hb hn).2.1
  have hB := (lower_rare_scale κ n hκ hn).1
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hchoose : (Nat.choose n m : ℝ)*(m : ℝ)^(m-1) ≤
      (n : ℝ)^m*(3 : ℝ)^m/(m : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^m/(Nat.factorial m : ℝ))*(m : ℝ)^(m-1) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div m n) (by positivity)
      _ = (n : ℝ)^m*((m : ℝ)^(m-1)/(Nat.factorial m : ℝ)) := by ring
      _ ≤ (n : ℝ)^m*((3 : ℝ)^m/(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (component_factorial_bound m hm) (by positivity)
      _ = _ := by ring
  rw [integral_mul_const]
  apply (mul_le_mul_of_nonneg_right (expected_component_count κ n hκ hb hn m hm)
    (by positivity)).trans
  calc
    _ ≤ ((n : ℝ)^m*(3 : ℝ)^m/(m : ℝ))*(2*lowerH κ n)*(4*lowerEll κ n)^(m-1)*
        (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
          (m : ℝ)^4*(9/2 : ℝ)^m) := by gcongr
    _ = _ := by
      rw [show m = (m-1)+1 by omega, pow_succ (n : ℝ), pow_succ (3 : ℝ),
        pow_succ (9/2 : ℝ)]
      rw [show m-1+1-1 = m-1 by omega]
      rw [show ((m-1+1 : ℕ) : ℝ) = (m : ℝ) by congr 1; omega]
      rw [show (54 : ℝ) = 3*4*(9/2) by norm_num]
      simp only [mul_pow]
      field_simp
      ring

/-- The finite all-size ledger is bounded by the convergent cubic series. -/
-- @node: component_finite_series_bound
lemma component_finite_series_bound (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1/4) (N : ℕ) :
    (∑ m ∈ Finset.range (N+1), if 2 ≤ m then (m : ℝ)^3*z^(m-1) else 0) ≤ 32*z := by
  have hs := component_geometric_series z hz
  have hz0 := hz.1
  have hf : (∑ m ∈ Finset.range (N+1), if 2 ≤ m then (m : ℝ)^3*z^(m-1) else 0) ≤
      ∑ m ∈ Finset.range (N+1), ((m+2 : ℕ) : ℝ)^3*z^(m+1) := by
    calc
      _ ≤ ∑ m ∈ Finset.range (2+(N+1)), if 2 ≤ m then (m : ℝ)^3*z^(m-1) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega))
        intro m _ _
        split_ifs <;> positivity
      _ = _ := by
        rw [Finset.sum_range_add]
        simp [Finset.sum_range_succ, Nat.add_comm]
  exact hf.trans ((Summable.sum_le_tsum (Finset.range (N+1))
    (fun _ _ => by positivity) hs.1).trans hs.2)

/-- Integrating the full component ledger gives the explicit sample-size information bound. -/
-- @node: expected_component_ledger_bound
lemma expected_component_ledger_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    (∫ x, (∑ m ∈ Finset.range (n+1), if 2 ≤ m then
      componentCount κ n m x *
        (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
          (m : ℝ)^4*(9/2 : ℝ)^m) else 0)
      ∂Measure.pi (fun _ : Fin n => design)) ≤
      (2 : ℝ)^24*(n : ℝ)^2*lowerH κ n*lowerEll κ n*
        lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let w := lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)
  let z := 54*(n : ℝ)*lowerEll κ n
  have he := (lower_scale_small κ n hκ hn).1.1
  have hh := (lower_macro_scale κ n hκ hb hn).2.1
  have hB := (lower_rare_scale κ n hκ hn).1
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hz := lower_component_series_argument κ n hκ hb hn
  have hint (m : ℕ) : Integrable (fun x => if 2 ≤ m then
      componentCount κ n m x *
        (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
          (m : ℝ)^4*(9/2 : ℝ)^m) else 0)
      (Measure.pi (fun _ : Fin n => design)) := by
    by_cases hm : 2 ≤ m
    · simp only [if_pos hm]
      exact (integrable_componentCount κ n m).mul_const _
    · simp only [if_neg hm]
      exact integrable_const 0
  rw [integral_finsetSum _ (fun m _ => hint m)]
  calc
    _ ≤ ∑ m ∈ Finset.range (n+1),
        (3888*(n : ℝ)*lowerH κ n*w) * (if 2 ≤ m then (m : ℝ)^3*z^(m-1) else 0) := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hm : 2 ≤ m
      · simp only [if_pos hm]
        simpa only [w, z, mul_assoc] using expected_component_discrepancy_bound κ n hκ hb hn m hm
      · simp only [if_neg hm, integral_zero, mul_zero, le_refl]
    _ = (3888*(n : ℝ)*lowerH κ n*w) *
        (∑ m ∈ Finset.range (n+1), if 2 ≤ m then (m : ℝ)^3*z^(m-1) else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (3888*(n : ℝ)*lowerH κ n*w)*(32*z) :=
      mul_le_mul_of_nonneg_left (component_finite_series_bound z hz n) (by positivity)
    _ = (3888*32*54 : ℝ)*((n : ℝ)^2*lowerH κ n*lowerEll κ n*w) := by dsimp [z]; ring
    _ ≤ (2 : ℝ)^24*((n : ℝ)^2*lowerH κ n*lowerEll κ n*w) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by dsimp [w]; ring

/-- The mixture likelihood is jointly Borel in covariates and observed marks. -/
-- @node: measurable_componentDensity_joint
@[fun_prop] lemma measurable_componentDensity_joint (m : ℕ) (s t : ℝ) :
    Measurable (fun p : (Fin m → unitInterval) × (Fin m → Bool × ℝ) =>
      componentDensity κ n m p.1 s t p.2) := by
  unfold componentDensity lowerDensity lowerField lowerSquare lowerCutoff markV
  fun_prop

/-- Integrating the jointly measurable squared-root difference is Borel in covariates. -/
-- @node: measurable_conditional_hellinger
@[fun_prop] lemma measurable_conditional_hellinger (hκ : κ.Valid) (hn : 2 ≤ n) :
    Measurable (fun x : Fin n → unitInterval => Causalean.Stat.hellingerSqDensity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
      (componentDensity κ n n x (lowerA κ n) (-lowerB κ n))) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hm : Measurable (fun p : (Fin n → unitInterval) × (Fin n → Bool × ℝ) =>
      (Real.sqrt (componentDensity κ n n p.1 (lowerA κ n) (lowerB κ n) p.2) -
        Real.sqrt (componentDensity κ n n p.1 (lowerA κ n) (-lowerB κ n) p.2))^2) := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The conditional discrepancy is integrable under the exact uniform covariate law. -/
-- @node: integrable_conditional_hellinger
lemma integrable_conditional_hellinger (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    Integrable (fun x => Causalean.Stat.hellingerSqDensity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
      (componentDensity κ n n x (lowerA κ n) (-lowerB κ n)))
      (Measure.pi (fun _ : Fin n => design)) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hInt : Integrable (fun x => ∑ m ∈ Finset.range (n+1), if 2 ≤ m then
      componentCount κ n m x *
        (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
          (m : ℝ)^4*(9/2 : ℝ)^m) else 0)
      (Measure.pi (fun _ : Fin n => design)) := by
    apply integrable_finsetSum
    intro m _
    by_cases hm : 2 ≤ m
    · simp only [if_pos hm]
      exact (integrable_componentCount κ n m).mul_const _
    · simp only [if_neg hm]
      exact integrable_const 0
  apply hInt.mono' (measurable_conditional_hellinger κ n hκ hn).aestronglyMeasurable
  filter_upwards [] with x
  have hnonneg : 0 ≤ Causalean.Stat.hellingerSqDensity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
      (componentDensity κ n n x (lowerA κ n) (-lowerB κ n)) := by
    unfold Causalean.Stat.hellingerSqDensity
    exact integral_nonneg (fun _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact conditional_hellinger_component_sum κ n hκ hb hn x

/-- Exact uniform covariates average the conditional discrepancy to the optimized small budget. -/
-- @node: expected_conditional_hellinger_bound
lemma expected_conditional_hellinger_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    (∫ x, Causalean.Stat.hellingerSqDensity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
      (componentDensity κ n n x (lowerA κ n) (-lowerB κ n))
      ∂Measure.pi (fun _ : Fin n => design)) ≤ 1/65536 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hInt : Integrable (fun x => ∑ m ∈ Finset.range (n+1), if 2 ≤ m then
      componentCount κ n m x *
        (144*lowerA κ n^2*lowerB κ n^2*lowerAmplitude κ n^(κ.p-2)*
          (m : ℝ)^4*(9/2 : ℝ)^m) else 0)
      (Measure.pi (fun _ : Fin n => design)) := by
    apply integrable_finsetSum
    intro m _
    by_cases hm : 2 ≤ m
    · simp only [if_pos hm]
      exact (integrable_componentCount κ n m).mul_const _
    · simp only [if_neg hm]
      exact integrable_const 0
  exact (integral_mono_ae (integrable_conditional_hellinger κ n hκ hb hn) hInt
    (Filter.Eventually.of_forall (conditional_hellinger_component_sum κ n hκ hb hn))).trans
    ((expected_component_ledger_bound κ n hκ hb hn).trans (lower_information_budget κ n hκ hn))

/-- The all-size component ledger gives the original mixture total-variation bound. -/
-- @node: lower_mixture_tv
lemma lower_mixture_tv (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
  Causalean.Stat.tvDist (lowerMixture κ n true) (lowerMixture κ n false) ≤ 1/4 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  let μ := Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))
  have hf := integrable_lowerSampleLikelihood κ n hκ hn true
  have hg := integrable_lowerSampleLikelihood κ n hκ hn false
  have hf0 := lowerSampleLikelihood_nonneg κ n true
  have hg0 := lowerSampleLikelihood_nonneg κ n false
  have hf1 := lower_sample_likelihood_integral_one κ n hκ hb hn true
  have hg1 := lower_sample_likelihood_integral_one κ n hκ hb hn false
  have htv := Causalean.Stat.tvDist_le_sqrt_two_mul_one_sub_affinity μ
    (lowerSampleLikelihood κ n true) (lowerSampleLikelihood κ n false) hf hg hf0 hg0 hf1 hg1
  rw [← Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity μ
    _ _ hf hg hf0 hg0 hf1 hg1,
    ← lower_mixture_withDensity κ n hκ hb hn true,
    ← lower_mixture_withDensity κ n hκ hb hn false] at htv
  have hH : Causalean.Stat.hellingerSqDensity μ
      (lowerSampleLikelihood κ n true) (lowerSampleLikelihood κ n false) ≤ 1/65536 := by
    let e := MeasurableEquiv.arrowProdEquivProdArrow unitInterval (Bool × ℝ) (Fin n)
    let νX := Measure.pi (fun _ : Fin n => design)
    let νZ := Measure.pi (fun _ : Fin n => referenceMarks κ n)
    let F := fun p : (Fin n → unitInterval) × (Fin n → Bool × ℝ) =>
      (Real.sqrt (componentDensity κ n n p.1 (lowerA κ n) (lowerB κ n) p.2) -
        Real.sqrt (componentDensity κ n n p.1 (lowerA κ n) (-lowerB κ n) p.2))^2
    have hFm : Measurable F := by dsimp [F]; fun_prop
    have hFi : Integrable F (νX.prod νZ) := by
      apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall (fun x => reference_marks_pi_integrable κ n hκ hn _)
      · have heq : (fun x => ∫ z, ‖F (x,z)‖ ∂νZ) =
            (fun x => Causalean.Stat.hellingerSqDensity νZ
              (componentDensity κ n n x (lowerA κ n) (lowerB κ n))
              (componentDensity κ n n x (lowerA κ n) (-lowerB κ n))) := by
          funext x
          simp only [F, Real.norm_eq_abs, abs_pow, sq_abs]
          rfl
        rw [heq]
        exact integrable_conditional_hellinger κ n hκ hb hn
    have hp := measurePreserving_arrowProdEquivProdArrow unitInterval (Bool × ℝ) (Fin n)
      (fun _ => design) (fun _ => referenceMarks κ n)
    unfold Causalean.Stat.hellingerSqDensity
    rw [← hp.symm.integral_comp']
    have heq : (fun p => (Real.sqrt (lowerSampleLikelihood κ n true (e.symm p)) -
        Real.sqrt (lowerSampleLikelihood κ n false (e.symm p)))^2) =ᵐ[νX.prod νZ] F := by
      have hLm (ε : Bool) : Measurable (lowerSampleLikelihood κ n ε) := by
        unfold lowerSampleLikelihood
        fun_prop
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
        (by fun_prop) hFm)).mpr
      filter_upwards [] with x
      filter_upwards [lower_sample_likelihood_conditional κ n hκ hn true x,
        lower_sample_likelihood_conditional κ n hκ hn false x] with z hz₁ hz₂
      change (Real.sqrt (lowerSampleLikelihood κ n true (fun i => (x i,z i))) -
        Real.sqrt (lowerSampleLikelihood κ n false (fun i => (x i,z i))))^2 = F (x,z)
      rw [hz₁,hz₂]
      simp only [sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
      rfl
    rw [integral_congr_ae heq, integral_prod _ hFi]
    exact expected_conditional_hellinger_bound κ n hκ hb hn
  apply htv.trans
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · exact hH.trans (by norm_num)

/-- The optimized construction exists with one positive constant family, uniform on compact
interaction regions; its proof uses the explicit rare-mark laws and shared-component estimates. -/
-- @node: lower_handle_exists
lemma lower_handle_exists : ∃ c : Params → ℝ,
    (∀ κ, κ.Valid → boundary κ ≤ 1 → 0 < c κ) ∧
    (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid ∧ boundary κ ≤ 1} →
      ∃ c0 : ℝ, 0 < c0 ∧ ∀ κ ∈ K, c0 ≤ c κ) ∧
    ∀ κ n, ∃ program : LowerProgram, LowerProgramCertificate κ n (c κ) program := by
  refine ⟨cInter, fun κ _ _ => cInter_pos κ, cInter_compact_lower_bound, ?_⟩
  intro κ n
  refine ⟨⟨signCount κ n, lowerEll κ n, lowerH κ n, lowerA κ n, lowerB κ n,
    lowerAmplitude κ n, lowerRare κ n, lowerP0, frame κ n, lowerCutoff κ n,
    lowerPriorLaw κ n⟩, ?_⟩
  intro hd
  have hs := lower_scale_small κ n hd.1 hd.2.2
  have hr := lower_rare_scale κ n hd.1 hd.2.2
  have hB : 1 ≤ lowerAmplitude κ n := by
    unfold lowerAmplitude
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs.2.2.1
      (hs.2.2.2.trans (by norm_num))
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hd.1.1.1.le))
  dsimp only [LowerProgramCertificate]
  refine ⟨hs.1.1, hs.1.2, rfl, hs.2.1.1, hs.2.2.1, hB, rfl,
    by norm_num [lowerP0], by norm_num [lowerP0], rfl, hr.2.1,
    continuous_frame κ n, frame_square_partition κ n (by omega), frame_active_card κ n,
    frame_support_diameter κ n (by omega), fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro ε v
    have hm := lower_prior_membership κ n hd.1 hd.2.1 hd.2.2 ε v
    refine ⟨hm.1, hm.1.uniform, ?_, ?_, ?_, ?_, ?_⟩
    · rw [lowerPriorLaw, dif_pos hd]
      rfl
    · rw [lowerPriorLaw, dif_pos hd]
      rfl
    · rw [hm.2]
      rfl
    · have he : (fun x => -(sign ε*lowerA κ n*lowerB κ n*(lowerCutoff κ n x)^2)/
          (lowerP0*(1-lowerP0))) = lowerEffect κ n ε := rfl
      rw [he, ← hm.2]
      exact hm.1.effectHolder
    · intro z x
      have hmean : (if z then (lowerPriorLaw κ n ε v).m1 x
          else (lowerPriorLaw κ n ε v).m0 x) = lowerMean κ n ε v z x := by
        rw [lowerPriorLaw, dif_pos hd]
        cases z
        · rfl
        · change lowerMean κ n ε v false x + lowerEffect κ n ε x = lowerMean κ n ε v true x
          linarith [lowerMean_effect_identity κ n ε v x]
      rw [hmean, lowerPriorLaw, dif_pos hd]
      rfl
  · exact lower_singleton_mixtures_equal κ n hd.1 hd.2.1 hd.2.2
  · change cInter κ*(n : ℝ)^(-rInter κ) ≤
      |lowerEffect κ n true xstar-lowerEffect κ n false xstar|
    rw [cInter_separation_identity κ n hd.2.2]
    nlinarith [abs_nonneg (lowerEffect κ n true xstar-lowerEffect κ n false xstar)]
  · exact lower_mixture_tv κ n hd.1 hd.2.1 hd.2.2
/-- The constant family selected from the named full-programme existence theorem. -/
def lowerHandleConstant : Params → ℝ := Classical.choose lower_handle_exists
-- @node: def:lower-handle
/-- Select the finite shared-sign rare-mark programme from lower_handle_exists, retaining every
certificate clause. Concrete frames, scales and off-domain extensions above remain auxiliary witnesses. -/
def lowerHandle : {program : LowerProgram // LowerProgramCertificate κ n (lowerHandleConstant κ) program} :=
  ⟨Classical.choose ((Classical.choose_spec lower_handle_exists).2.2 κ n),
    Classical.choose_spec ((Classical.choose_spec lower_handle_exists).2.2 κ n)⟩ -- @realizes lowerHandle(certified finite shared-sign rare-mark programme)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
