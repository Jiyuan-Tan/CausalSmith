module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Histogram
public import Mathlib.MeasureTheory.Function.Floor

/-! Histogram representer identities and its uniform squared-integral bound. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A histogram cell lies within its closed geometric bin, including the last endpoint. -/
-- @node: histogramCell_subset_bin
lemma histogramCell_subset_bin (J : ℕ) (hJ : 0 < J) (i : Fin J) :
    histogramCell J (i.val + 1) ⊆ Set.Icc ((i.val : ℝ) / J) ((i.val + 1 : ℝ) / J) := by
  intro y hy
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hn : 0 ≤ (J : ℝ) * y := mul_nonneg hpos.le hy.1.1
  have hc : min J (1 + ⌊(J : ℝ) * y⌋₊) = i.val + 1 := hy.2
  constructor
  · apply (div_le_iff₀ hpos).2
    have hf : i.val ≤ ⌊(J : ℝ) * y⌋₊ := by
      have := min_le_right J (1 + ⌊(J : ℝ) * y⌋₊)
      omega
    have hfr : (i.val : ℝ) ≤ ⌊(J : ℝ) * y⌋₊ := by exact_mod_cast hf
    nlinarith [Nat.floor_le hn]
  · apply (le_div_iff₀ hpos).2
    by_cases hl : i.val + 1 = J
    · have hlr : (i.val : ℝ) + 1 = J := by exact_mod_cast hl
      nlinarith [hy.1.2]
    · have hf : 1 + ⌊(J : ℝ) * y⌋₊ = i.val + 1 := by omega
      have hfr : (⌊(J : ℝ) * y⌋₊ : ℝ) = i.val := by
        exact_mod_cast (by omega : ⌊(J : ℝ) * y⌋₊ = i.val)
      nlinarith [Nat.lt_floor_add_one ((J : ℝ) * y)]

/-- Each histogram cell has Lebesgue mass at most the reciprocal rank. -/
-- @node: histogramCell_mass_le
lemma histogramCell_mass_le (J : ℕ) (hJ : 0 < J) (i : Fin J) :
    unitVolume.real (histogramCell J (i.val + 1)) ≤ 1 / (J : ℝ) := by
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  calc
    _ ≤ volume.real (histogramCell J (i.val + 1)) := by
      apply ENNReal.toReal_mono ((measure_mono (histogramCell_subset_bin J hJ i)).trans_lt
        (by simp [Real.volume_Icc])).ne
      exact Measure.restrict_apply_le _ _
    _ ≤ volume.real (Set.Icc ((i.val : ℝ) / J) ((i.val + 1 : ℝ) / J)) :=
      measureReal_mono (histogramCell_subset_bin J hJ i) (by simp [Real.volume_Icc])
    _ = 1 / (J : ℝ) := by
      rw [Real.volume_real_Icc_of_le (by apply div_le_div_of_nonneg_right _ hpos.le; linarith)]
      ring

/-- Every half-open geometric bin is contained in its one-based histogram cell. -/
-- @node: bin_subset_histogramCell
lemma bin_subset_histogramCell (J : ℕ) (hJ : 0 < J) (i : Fin J) :
    Set.Ico ((i.val : ℝ) / J) ((i.val + 1 : ℝ) / J) ⊆
      histogramCell J (i.val + 1) := by
  intro y hy
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hil : (i.val : ℝ) + 1 ≤ J := by exact_mod_cast i.isLt
  have hlo : (i.val : ℝ) ≤ (J : ℝ) * y := by
    nlinarith [(div_le_iff₀ hpos).1 hy.1]
  have hhi : (J : ℝ) * y < (i.val : ℝ) + 1 := by
    nlinarith [(lt_div_iff₀ hpos).1 hy.2]
  have hf : ⌊(J : ℝ) * y⌋₊ = i.val := (Nat.floor_eq_iff (a := (J : ℝ) * y) (n := i.val)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) i.val])).2 ⟨hlo, hhi⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) i.val]
  · have := (lt_div_iff₀ hpos).1 hy.2
    nlinarith
  · simp only [cell, hf]
    omega

/-- Uniform histogram cells have exactly reciprocal-rank Lebesgue mass. -/
-- @node: histogramCell_mass_eq
lemma histogramCell_mass_eq (J : ℕ) (hJ : 0 < J) (i : Fin J) :
    unitVolume.real (histogramCell J (i.val + 1)) = 1 / (J : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply le_antisymm (histogramCell_mass_le J hJ i)
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hbin : Set.Ico ((i.val : ℝ) / J) ((i.val + 1 : ℝ) / J) ⊆ Set.Icc 0 1 := by
    intro y hy
    exact (bin_subset_histogramCell J hJ i hy).1
  calc
    _ = unitVolume.real (Set.Ico ((i.val : ℝ) / J) ((i.val + 1 : ℝ) / J)) := by
      rw [measureReal_def, unitVolume, Measure.restrict_apply measurableSet_Ico,
        Set.inter_eq_left.mpr hbin]
      rw [← measureReal_def, Real.volume_real_Ico_of_le
        (by apply div_le_div_of_nonneg_right _ hpos.le; linarith)]
      ring
    _ ≤ _ := measureReal_mono (bin_subset_histogramCell J hJ i) (measure_ne_top _ _)

/-- The one-based histogram label is measurable. -/
-- @node: measurable_cell
@[fun_prop] lemma measurable_cell (J : ℕ) : Measurable (cell J) := by
  unfold cell
  have hf : Measurable (fun x : ℝ => ⌊(J : ℝ) * x⌋₊) :=
    Nat.measurable_floor.comp (by fun_prop)
  fun_prop

/-- Histogram cells are measurable restrictions of label fibers. -/
lemma measurableSet_histogramCell (J c : ℕ) : MeasurableSet (histogramCell J c) := by
  exact measurableSet_Icc.inter (measurable_cell J (measurableSet_singleton c))

/-- Subtracting a point value from a cell average averages its within-cell deviations. -/
-- @node: outcomeProjection_sub_eq
lemma outcomeProjection_sub_eq (J : ℕ) (hJ : 0 < J) (i : Fin J)
    (f : ℝ → ℝ) (hf : Integrable f unitVolume) (y : ℝ)
    (hc : cell J y = i.val + 1) :
    outcomeProjection J f y - f y =
      (J : ℝ) * ∫ z in histogramCell J (i.val + 1), f z - f y ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  rw [integral_sub hf.integrableOn (integrable_const _), integral_const]
  have hm : (unitVolume.restrict (histogramCell J (i.val + 1))).real Set.univ =
      1 / (J : ℝ) := by
    simpa [measureReal_def] using histogramCell_mass_eq J hJ i
  simp only [smul_eq_mul, hm]
  dsimp [outcomeProjection]
  rw [hc]
  have hne : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp

/-- A within-cell oscillation envelope bounds the error of its uniform projection. -/
-- @node: outcomeProjection_error_le
lemma outcomeProjection_error_le (J : ℕ) (hJ : 0 < J) (i : Fin J)
    (f : ℝ → ℝ) (hf : Integrable f unitVolume) (y B : ℝ)
    (hc : cell J y = i.val + 1)
    (hb : ∀ᵐ z ∂unitVolume.restrict (histogramCell J (i.val + 1)), |f z - f y| ≤ B) :
    |outcomeProjection J f y - f y| ≤ B := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  rw [outcomeProjection_sub_eq J hJ i f hf y hc, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg J)]
  have hn : ∀ᵐ z ∂unitVolume.restrict (histogramCell J (i.val + 1)), ‖f z - f y‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hb
  have hi := norm_integral_le_of_norm_le_const hn
  simp only [Measure.real, Measure.restrict_apply_univ] at hi
  have hm := histogramCell_mass_eq J hJ i
  have hne : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  calc
    _ ≤ (J : ℝ) * (B * unitVolume.real (histogramCell J (i.val + 1))) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs, measureReal_def] using hi) (Nat.cast_nonneg J)
    _ = B := by rw [hm]; field_simp

/-- The model's outcome Lipschitz condition gives the approximation envelope in (26). -/
-- @node: model_outcomeProjection_error_le
lemma model_outcomeProjection_error_le (P : ObsLaw) (hModel : Model P)
    (J : ℕ) (hJ : 0 < J) (a : Bool) (x y : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |outcomeProjection J (P.eta a x) y - P.eta a x y| ≤ 10 / (J : ℝ) := by
  have hind : 1 ≤ cell J y ∧ cell J y ≤ J := by
    unfold cell
    constructor <;> omega
  let i : Fin J := ⟨cell J y - 1, by omega⟩
  have hc : cell J y = i.val + 1 := by dsimp [i]; omega
  apply outcomeProjection_error_le J hJ i _ (P.eta_integrable a x hx) y _ hc
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell J (i.val + 1))] with z hz
  have hb := histogramCell_subset_bin J hJ i hz
  have hby := histogramCell_subset_bin J hJ i ⟨hy, hc⟩
  have hd : |z - y| ≤ 1 / (J : ℝ) := by
    simp only [add_div] at hb hby
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2, hby.1, hby.2]
  exact (hModel.density_outcome_lipschitz a x hx z hz.1 y hy).trans
    (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 10))

/-- Pairing the representer with coefficients evaluates their histogram function. -/
-- @node: inner_phiCoefficients
lemma inner_phiCoefficients (J : ℕ) (f : Hj J) (y : ℝ) :
    inner ℝ (phiCoefficients J y) f = histogramFunction f y := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [phiCoefficients, RCLike.inner_apply, conj_trivial]
  change f i * (if cell J y = i.val + 1 then Real.sqrt J else 0) =
    (if cell J y = i.val + 1 then Real.sqrt J * f i else 0)
  split_ifs <;> simp [mul_comm]

/-- At most one histogram coordinate is nonzero at each outcome. -/
-- @node: histogramFunction_sq
lemma histogramFunction_sq (J : ℕ) (f : Hj J) (y : ℝ) :
    (histogramFunction f y) ^ 2 =
      ∑ i : Fin J, if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0 := by
  classical
  by_cases h : ∃ i : Fin J, cell J y = i.val + 1
  · obtain ⟨i, hi⟩ := h
    have heq (l : Fin J) : cell J y = l.val + 1 ↔ l = i := by
      rw [hi]
      constructor
      · intro h; apply Fin.ext; omega
      · rintro rfl; rfl
    simp only [histogramFunction, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg J)]
  · have heq (i : Fin J) : cell J y ≠ i.val + 1 := fun hi => h ⟨i, hi⟩
    simp [histogramFunction, heq]

/-- Fixed histogram test functions are measurable. -/
-- @node: measurable_histogramFunction
@[fun_prop] lemma measurable_histogramFunction (J : ℕ) (f : Hj J) :
    Measurable (histogramFunction f) := by
  have hc : Measurable (cell J) := by
    unfold cell
    have hf : Measurable (fun x : ℝ => ⌊(J : ℝ) * x⌋₊) :=
      Nat.measurable_floor.comp (by fun_prop)
    fun_prop
  unfold histogramFunction
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (hc (measurableSet_singleton _)) measurable_const measurable_const

/-- Fixed histogram functions have a finite deterministic pointwise bound. -/
-- @node: histogramFunction_abs_le
lemma histogramFunction_abs_le (J : ℕ) (f : Hj J) (y : ℝ) :
    |histogramFunction f y| ≤ ∑ i : Fin J, |Real.sqrt J * f i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> simp only [abs_zero, le_refl]
  exact abs_nonneg _

/-- Histogram tests and their squares are integrable on the unit outcome domain. -/
-- @node: histogramFunction_integrable
lemma histogramFunction_integrable (J : ℕ) (f : Hj J) :
    Integrable (histogramFunction f) unitVolume ∧
      Integrable (fun y => (histogramFunction f y) ^ 2) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hb := histogramFunction_abs_le J f
  constructor
  · exact Integrable.of_bound (by fun_prop) _ (Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using hb y))
  · apply Integrable.of_bound (by fun_prop) ((∑ i : Fin J, |Real.sqrt J * f i|) ^ 2)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := mul_self_le_mul_self (abs_nonneg _) (hb y)
    simpa only [← sq, sq_abs] using h

/-- The squared outcome integral is bounded by the Euclidean coefficient norm. -/
-- @node: histogramFunction_squared_integral_le
lemma histogramFunction_squared_integral_le (J : ℕ) (hJ : 0 < J) (f : Hj J) :
    (∫ y, (histogramFunction f y) ^ 2 ∂unitVolume) ≤ ‖f‖ ^ 2 := by
  classical
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hs (i : Fin J) : MeasurableSet {y | cell J y = i.val + 1} := by
    have hc : Measurable (cell J) := by
      unfold cell
      have hf : Measurable (fun x : ℝ => ⌊(J : ℝ) * x⌋₊) :=
        Nat.measurable_floor.comp (by fun_prop)
      fun_prop
    exact hc (measurableSet_singleton _)
  have hi (i : Fin J) : Integrable (fun y =>
      if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0) unitVolume := by
    have heq : (fun y => if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0) =
        {y | cell J y = i.val + 1}.indicator (fun _ => (J : ℝ) * (f i) ^ 2) := by
      funext y
      simp [Set.indicator]
    rw [heq]
    exact (integrable_const (μ := unitVolume) _).indicator (hs i)
  simp_rw [histogramFunction_sq]
  rw [integral_finsetSum _ (fun i _ => hi i), EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have heq : (∫ y, (if cell J y = i.val + 1 then (J : ℝ) * (f i) ^ 2 else 0)
      ∂unitVolume) = unitVolume.real (histogramCell J (i.val + 1)) * ((J : ℝ) * (f i) ^ 2) := by
    have hcell : MeasurableSet (histogramCell J (i.val + 1)) :=
      measurableSet_Icc.inter (hs i)
    calc
      _ = ∫ y, (histogramCell J (i.val + 1)).indicator
          (fun _ => (J : ℝ) * (f i) ^ 2) y ∂unitVolume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        simp [Set.indicator, histogramCell, hy.1, hy.2]
      _ = _ := by
        rw [integral_indicator hcell, integral_const]
        simp [measureReal_def, smul_eq_mul]
  rw [heq]
  calc
    _ ≤ (1 / (J : ℝ)) * ((J : ℝ) * (f i) ^ 2) :=
      mul_le_mul_of_nonneg_right (histogramCell_mass_le J hJ i) (by positivity)
    _ = (f i) ^ 2 := by field_simp

end CausalSmith.Stat.DensityEffectRoughNull
