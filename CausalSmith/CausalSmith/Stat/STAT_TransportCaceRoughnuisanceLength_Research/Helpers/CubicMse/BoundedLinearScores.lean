module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.LinearStatisticBridge
public import Mathlib.Probability.Moments.Variance

/-! # Density-free variance bounds for linear marked scores

Roadmap (19) uses bounded observation scores rather than the absolute
cell-pair envelope in (15). Keeping the signed covariance sum gives a bound
independent of the density envelope and of the number of cells.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A bounded score averaged over an actual iid block has variance at most
its squared envelope divided by the block size.  Under [the displayed assumptions and inputs](hyp:Ω,n,S,hS,f,hf,C,_hC,hb), [the stated conclusion holds](goal). -/
-- @node: variance_iidBlockHeight_one_le
lemma variance_iidBlockHeight_one_le
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (S : Finset (Fin n)) (hS : 0 < S.card) (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C) :
    variance (iidBlockHeight 1 S f) (Measure.pi (fun _ : Fin n => μ)) ≤
      C ^ 2 / S.card := by
  have hlp : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable C (by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hb x)
  have hblock : Measurable (iidBlockHeight 1 S f) := by
    unfold iidBlockHeight
    fun_prop
  rw [← covariance_self hblock.aemeasurable,
    covariance_iidBlockHeight S hS f f hf hf hlp hlp,
    covariance_self hf.aemeasurable]
  have hv := variance_le_sq_of_bounded (μ := μ) (a := -C) (b := C)
    (X := f) (by
      filter_upwards [] with x
      exact abs_le.mp (hb x)) hf.aemeasurable
  have hv' : variance f μ ≤ C ^ 2 := by
    convert hv using 1 <;> ring
  norm_num only [Nat.cast_one, one_pow]
  calc
    _ ≤ (1 / (S.card : ℝ)) * C ^ 2 :=
      mul_le_mul_of_nonneg_left hv' (by positivity)
    _ = C ^ 2 / S.card := by ring

/-- The covariance quadratic form of cell histograms is the variance of the
single-record cell score, with the exact iid normalization.  Under [the displayed assumptions and inputs](hyp:Ω,n,K,hK,S,hS,f,hf,hlp,c), [the stated conclusion holds](goal). -/
-- @node: normalized_iid_cell_covariance_sum_eq_variance
lemma normalized_iid_cell_covariance_sum_eq_variance
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n K : ℕ}
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (f : Fin K → Ω → ℝ) (hf : ∀ l, Measurable (f l))
    (hlp : ∀ l, MemLp (f l) 2 μ) (c : Fin K → ℝ) :
    (K : ℝ)⁻¹ ^ 2 * ∑ l : Fin K, ∑ r : Fin K,
      c l * c r * covariance (iidBlockHeight K S (f l))
        (iidBlockHeight K S (f r)) (Measure.pi (fun _ : Fin n => μ)) =
      variance (fun x => ∑ l : Fin K, c l * f l x) μ / S.card := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hsumlp : MemLp (fun x => ∑ l : Fin K, c l * f l x) 2 μ :=
    memLp_finsetSum Finset.univ (fun l _ => (hlp l).const_mul (c l))
  have hvar : variance (fun x => ∑ l : Fin K, c l * f l x) μ =
      ∑ l : Fin K, ∑ r : Fin K, c l * c r * covariance (f l) (f r) μ := by
    rw [← covariance_self hsumlp.aemeasurable,
      covariance_fun_sum_fun_sum' (fun l _ => (hlp l).const_mul (c l))
        (fun r _ => (hlp r).const_mul (c r))]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hvar]
  simp_rw [covariance_iidBlockHeight S hS _ _ (hf _) (hf _) (hlp _) (hlp _)]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  field_simp

/-- Bounded coefficients on disjoint cells produce a bounded source score,
including outside the covariate support where all cell scores vanish.  Under [the displayed assumptions and inputs](hyp:K,hK,i,c,C,hC,hc,o), [the stated conclusion holds](goal). -/
-- @node: abs_weighted_sourceCellScore_sum_le
lemma abs_weighted_sourceCellScore_sum_le {K : ℕ} (hK : 0 < K)
    (i : Fin 7) (c : Fin K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l, |c l| ≤ C) (o : SourceObs) :
    |∑ l : Fin K, c l * sourceCellScore i K l o| ≤ C := by
  classical
  by_cases hx : o.1 ∈ covariateSpace
  · obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK o.1 hx
    rw [Finset.sum_eq_single l]
    · rw [sourceCellScore, if_pos hl, abs_mul,
        abs_of_nonneg (sourceCellMark_mem_unit_interval i o).1]
      exact (mul_le_mul_of_nonneg_right (hc l)
        (sourceCellMark_mem_unit_interval i o).1).trans
        (by nlinarith [(sourceCellMark_mem_unit_interval i o).2])
    · intro r _ hrl
      rw [sourceCellScore, if_neg (fun hr =>
        Set.disjoint_left.mp (cell_disjoint hK hrl) hr hl), mul_zero]
    · exact fun h => (h (Finset.mem_univ l)).elim
  · have hz (l : Fin K) : sourceCellScore i K l o = 0 := by
      rw [sourceCellScore, if_neg (fun hl => hx (cell_subset_covariateSpace hK l hl))]
    simp only [hz, mul_zero, Finset.sum_const_zero, abs_zero]
    exact hC

/-- The target score has the same cell-disjointness bound, with unit marks.  Under [the displayed assumptions and inputs](hyp:K,hK,c,C,hC,hc,x), [the stated conclusion holds](goal). -/
-- @node: abs_weighted_targetCellScore_sum_le
lemma abs_weighted_targetCellScore_sum_le {K : ℕ} (hK : 0 < K)
    (c : Fin K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l, |c l| ≤ C) (x : ℝ) :
    |∑ l : Fin K, c l * targetCellScore K l x| ≤ C := by
  classical
  by_cases hx : x ∈ covariateSpace
  · obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK x hx
    rw [Finset.sum_eq_single l]
    · simpa [targetCellScore, hl] using hc l
    · intro r _ hrl
      rw [targetCellScore, if_neg (fun hr =>
        Set.disjoint_left.mp (cell_disjoint hK hrl) hr hl), mul_zero]
    · exact fun h => (h (Finset.mem_univ l)).elim
  · have hz (l : Fin K) : targetCellScore K l x = 0 := by
      rw [targetCellScore, if_neg (fun hl => hx (cell_subset_covariateSpace hK l hl))]
    simp only [hz, mul_zero, Finset.sum_const_zero, abs_zero]
    exact hC

/-- The signed source cell-pair sum retains cancellation and costs only
`C² / m`, with no density or resolution factor.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,i,c,C,hC,hc), [the stated conclusion holds](goal). -/
-- @node: normalized_source_cell_covariance_sum_le
lemma normalized_source_cell_covariance_sum_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (i : Fin 7) (c : Fin K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l, |c l| ≤ C) :
    (K : ℝ)⁻¹ ^ 2 * ∑ l : Fin K, ∑ r : Fin K,
      c l * c r * covariance (iidBlockHeight K S (sourceCellScore i K l))
        (iidBlockHeight K S (sourceCellScore i K r))
        (Measure.pi (fun _ : Fin n => sourceObsLaw P)) ≤ C ^ 2 / S.card := by
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hlp (l : Fin K) : MemLp (sourceCellScore i K l) 2 (sourceObsLaw P) :=
    memLp_two_of_mem_unit_interval (measurable_sourceCellScore i K l)
      (sourceCellScore_mem_unit_interval i K l)
  rw [normalized_iid_cell_covariance_sum_eq_variance hK S hS _
    (measurable_sourceCellScore i K) hlp c]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hv := variance_le_sq_of_bounded (μ := sourceObsLaw P) (a := -C) (b := C)
    (X := fun o => ∑ l : Fin K, c l * sourceCellScore i K l o) (by
      filter_upwards [] with o
      exact abs_le.mp (abs_weighted_sourceCellScore_sum_le hK i c C hC hc o))
    (by fun_prop)
  convert hv using 1 <;> first | ring | rfl

/-- The target channel obeys the identical density-free variance bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,c,C,hC,hc), [the stated conclusion holds](goal). -/
-- @node: normalized_target_cell_covariance_sum_le
lemma normalized_target_cell_covariance_sum_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (S : Finset (Fin n)) (hS : 0 < S.card)
    (c : Fin K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l, |c l| ≤ C) :
    (K : ℝ)⁻¹ ^ 2 * ∑ l : Fin K, ∑ r : Fin K,
      c l * c r * covariance (iidBlockHeight K S (targetCellScore K l))
        (iidBlockHeight K S (targetCellScore K r))
        (Measure.pi (fun _ : Fin n => targetXLaw P)) ≤ C ^ 2 / S.card := by
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hlp (l : Fin K) : MemLp (targetCellScore K l) 2 (targetXLaw P) :=
    memLp_two_of_mem_unit_interval (measurable_targetCellScore K l)
      (targetCellScore_mem_unit_interval K l)
  rw [normalized_iid_cell_covariance_sum_eq_variance hK S hS _
    (measurable_targetCellScore K) hlp c]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hv := variance_le_sq_of_bounded (μ := targetXLaw P) (a := -C) (b := C)
    (X := fun x => ∑ l : Fin K, c l * targetCellScore K l x) (by
      filter_upwards [] with x
      exact abs_le.mp (abs_weighted_targetCellScore_sum_le hK c C hC hc x))
    (by fun_prop)
  convert hv using 1 <;> first | ring | rfl

/-- The signed covariance bound survives the flattening of the actual
source and target experiment, for every marked coordinate.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,b,hcard,i,c,C,hC,hc), [the stated conclusion holds](goal). -/
-- @node: normalized_flatBlockHeight_covariance_sum_le
lemma normalized_flatBlockHeight_covariance_sum_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (b : Fin 4) (hcard : 0 < (blockIdx n b).card)
    (i : Fin 7) (c : Fin K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l, |c l| ≤ C) :
    (K : ℝ)⁻¹ ^ 2 * ∑ l : Fin K, ∑ r : Fin K,
      c l * c r * covariance
        (fun z => flatBlockHeight i b l
          (Causalean.Mathlib.Probability.Independence.finsetCoordProj (flatBlock n b) z))
        (fun z => flatBlockHeight i b r
          (Causalean.Mathlib.Probability.Independence.finsetCoordProj (flatBlock n b) z))
        (Measure.pi (flatLaw P n)) ≤ C ^ 2 / blockSize n b := by
  rw [← block_card]
  by_cases hi : i = 0
  · subst i
    simp_rw [flatBlockHeight_proj_target]
    have hcov (l r : Fin K) := covariance_flatLaw_target c_f C_f L P n hP
      (iidBlockHeight K (blockIdx n b) (targetCellScore K l))
      (iidBlockHeight K (blockIdx n b) (targetCellScore K r))
      (by unfold iidBlockHeight; fun_prop) (by unfold iidBlockHeight; fun_prop)
    simp_rw [hcov]
    exact normalized_target_cell_covariance_sum_le c_f C_f L P n K hP hK
      (blockIdx n b) hcard c C hC hc
  · simp_rw [flatBlockHeight_proj_source i hi]
    have hcov (l r : Fin K) := covariance_flatLaw_source c_f C_f L P n hP
      (iidBlockHeight K (blockIdx n b) (sourceCellScore i K l))
      (iidBlockHeight K (blockIdx n b) (sourceCellScore i K r))
      (by unfold iidBlockHeight; fun_prop) (by unfold iidBlockHeight; fun_prop)
    simp_rw [hcov]
    exact normalized_source_cell_covariance_sum_le c_f C_f L P n K hP hK
      (blockIdx n b) hcard i c C hC hc

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
