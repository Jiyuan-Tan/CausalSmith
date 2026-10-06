module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Projections
public import Causalean.Mathlib.MeasureTheory.FiniteIntervalPartition

/-! Finite-moment homogeneity testing: Helpers/ProjectionGeometry. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The explicit featureMap construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_featureMap
@[fun_prop] lemma measurable_featureMap (J : ℕ) : Measurable (featureMap J) := by
  unfold featureMap
  apply (PiLp.continuous_toLp 2 (fun _ : Fin J => ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro j
  apply Measurable.ite
  · change MeasurableSet {x : unitInterval | (j:ℝ)/J ≤ (x:ℝ) ∧
        ((x:ℝ) < ((j:ℝ)+1)/J ∨ (j.val+1=J ∧ (x:ℝ) ≤ 1))}
    measurability
  · fun_prop
  · fun_prop
/-- The explicit projKernel construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_projKernel
@[fun_prop] lemma measurable_projKernel (J : ℕ) : Measurable (fun x : unitInterval × unitInterval => projKernel J x.1 x.2) := by
  unfold projKernel
  fun_prop
/-- Real histogram cells form the standard interval partition. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_real_partition
lemma histogram_real_partition (J : ℕ) (hJ : 0 < J) :
    Causalean.Mathlib.MeasureTheory.IsIntervalPartition (0:ℝ) 1 J
      (fun j : Fin J => if j.val+1=J then Icc ((j:ℝ)/J) (((j:ℝ)+1)/J)
        else Ico ((j:ℝ)/J) (((j:ℝ)+1)/J)) := by
  have h := Causalean.Mathlib.MeasureTheory.orderedIntervalCells_partition
    (fun i : ℕ => (i:ℝ)/J) J hJ (by
      intro i j hij hj
      exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity))
  simpa [Nat.cast_add, Nat.cast_one, ne_of_gt hJ] using h

/-- Membership in a subtype histogram cell is membership in its real interval. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_mem
lemma histogram_cell_mem (J : ℕ) (hJ : 0 < J) (j : Fin J) (x : unitInterval) :
    x ∈ cell J j ↔ (x:ℝ) ∈
      (if j.val+1=J then Icc ((j:ℝ)/J) (((j:ℝ)+1)/J)
        else Ico ((j:ℝ)/J) (((j:ℝ)+1)/J)) := by
  by_cases hj : j.val+1=J
  · have he : ((j:ℝ)+1)/J = 1 := by
      have hj' : (j:ℝ)+1 = J := by exact_mod_cast hj
      rw [hj', div_self (by positivity : (J:ℝ) ≠ 0)]
    simp [cell, hj, he, x.property.2]
  · simp [cell, hj]

/-- Each point belongs to exactly one histogram cell, including the right endpoint. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_unique
lemma histogram_cell_unique (J : ℕ) (hJ : 0 < J) (x : unitInterval) :
    ∃ j : Fin J, x ∈ cell J j ∧ ∀ k : Fin J, x ∈ cell J k → k=j := by
  obtain ⟨hm, hd, hc⟩ := histogram_real_partition J hJ
  have hx : (x:ℝ) ∈ ⋃ j : Fin J,
      (if j.val+1=J then Icc ((j:ℝ)/J) (((j:ℝ)+1)/J)
        else Ico ((j:ℝ)/J) (((j:ℝ)+1)/J)) := by
    rw [hc]
    exact x.property
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  refine ⟨j, (histogram_cell_mem J hJ j x).mpr hj, ?_⟩
  intro k hk
  by_contra hkj
  exact Set.disjoint_left.mp (hd k j hkj)
    ((histogram_cell_mem J hJ k x).mp hk) hj

/-- Histogram cells are measurable. [This is the stated conclusion](goal). -/
-- @node: measurableSet_histogram_cell
lemma measurableSet_histogram_cell (J : ℕ) (j : Fin J) :
    MeasurableSet (cell J j) := by
  unfold cell
  measurability

/-- Every histogram cell has uniform-design mass equal to the reciprocal rank. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_volume
lemma histogram_cell_volume (J : ℕ) (hJ : 0 < J) (j : Fin J) :
    design (cell J j) = ENNReal.ofReal ((J:ℝ)⁻¹) := by
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hlo : 0 ≤ (j:ℝ)/J := by positivity
  have hhi : ((j:ℝ)+1)/J ≤ 1 := by
    apply (div_le_iff₀ hJr).mpr
    norm_cast
    omega
  have himg : Subtype.val '' cell J j =
      (if j.val+1=J then Icc ((j:ℝ)/J) (((j:ℝ)+1)/J)
        else Ico ((j:ℝ)/J) (((j:ℝ)+1)/J)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (histogram_cell_mem J hJ j x).mp hx
    · intro hy
      have hr : 0 ≤ y ∧ y ≤ 1 := by
        split_ifs at hy <;> exact ⟨hlo.trans hy.1, (by linarith [hy.2])⟩
      exact ⟨⟨y, hr⟩, (histogram_cell_mem J hJ j ⟨y, hr⟩).mpr hy, rfl⟩
  rw [design, unitInterval.volume_apply, himg]
  have he : ((j:ℝ)+1)/J-(j:ℝ)/J = (J:ℝ)⁻¹ := by ring
  split_ifs
  · rw [Real.volume_Icc, he]
  · rw [Real.volume_Ico, he]

/-- A kernel row is rank times the indicator of the point's unique cell. This statement assumes [the hJ condition](hyp:hJ), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: histogram_kernel_row
lemma histogram_kernel_row (J : ℕ) (hJ : 0 < J) (x : unitInterval)
    (j : Fin J) (hj : x ∈ cell J j) (z : unitInterval) :
    projKernel J x z = if z ∈ cell J j then (J:ℝ) else 0 := by
  obtain ⟨k, hk, hu⟩ := histogram_cell_unique J hJ x
  have huniq : ∀ i : Fin J, x ∈ cell J i → i=j := by
    intro i hi
    exact (hu i hi).trans (hu j hj).symm
  simp only [projKernel, PiLp.inner_apply, featureMap, 
    RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_eq_single j]
  · simp only [if_pos hj]
    split_ifs <;> simp [Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ J)]
  · intro i hi hij
    have hxi : x ∉ cell J i := fun hi => hij (huniq i hi)
    simp [hxi]
  · simp

/-- Projection rows: the displayed mathematical construction or bound. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: projection_rows
lemma projection_rows (J : ℕ) (hJ : 0 < J) (x : unitInterval) :
    (∫ z, projKernel J x z ∂design) = 1 ∧ (∫ z, projKernel J x z^2 ∂design) = J := by
  obtain ⟨j, hj, hu⟩ := histogram_cell_unique J hJ x
  have hr : projKernel J x = (cell J j).indicator (fun _ => (J:ℝ)) := by
    funext z
    simpa [Set.indicator] using histogram_kernel_row J hJ x j hj z
  have hr2 : (fun z => projKernel J x z^2) = (cell J j).indicator (fun _ => (J:ℝ)^2) := by
    funext z
    rw [histogram_kernel_row J hJ x j hj z]
    by_cases hz : z ∈ cell J j <;> simp [hz]
  have hmass : design.real (cell J j) = (J:ℝ)⁻¹ := by
    rw [Measure.real, histogram_cell_volume J hJ j, ENNReal.toReal_ofReal (by positivity)]
  constructor
  · rw [hr, integral_indicator (measurableSet_histogram_cell J j), setIntegral_const, hmass]
    simp [ne_of_gt hJ]
  · rw [hr2, integral_indicator (measurableSet_histogram_cell J j), setIntegral_const, hmass]
    simp only [smul_eq_mul]
    field_simp

/-- Two points in one histogram cell are at distance at most the reciprocal rank. This statement assumes [the hJ condition](hyp:hJ), [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_diameter
lemma histogram_cell_diameter (J : ℕ) (hJ : 0 < J) (j : Fin J)
    (x z : unitInterval) (hx : x ∈ cell J j) (hz : z ∈ cell J j) :
    |(x:ℝ)-(z:ℝ)| ≤ (J:ℝ)⁻¹ := by
  have hx' := (histogram_cell_mem J hJ j x).mp hx
  have hz' := (histogram_cell_mem J hJ j z).mp hz
  have hwidth : ((j:ℝ)+1)/J-(j:ℝ)/J = (J:ℝ)⁻¹ := by ring
  apply abs_le.mpr
  split_ifs at hx' hz' <;> constructor <;> linarith [hx'.1, hx'.2, hz'.1, hz'.2]

/-- Histogram cell averaging approximates a Holder function at the cell diameter scale. This statement assumes [the hJ condition](hyp:hJ), [the hs condition](hyp:hs), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: projection_holder_error
lemma projection_holder_error (J : ℕ) (hJ : 0 < J) (s : ℝ) (hs : 0 < s ∧ s ≤ 1)
    (f : unitInterval → ℝ) (hf : holderBall s f) (x : unitInterval) :
    |f x-projOp J f x| ≤ 20*(J:ℝ)^(-s) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  obtain ⟨j, hj, hu⟩ := histogram_cell_unique J hJ x
  have hm : design.real (cell J j) = (J:ℝ)⁻¹ := by
    rw [Measure.real, histogram_cell_volume J hJ j, ENNReal.toReal_ofReal (by positivity)]
  have hi : Integrable f design := by
    have hcont : Continuous f := hf.1
    apply (integrable_const (20:ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun z => by simpa [Real.norm_eq_abs] using hf.2.1 z)
  have hp : projOp J f x = ∫ z in cell J j, (J:ℝ)*f z ∂design := by
    unfold projOp
    rw [← integral_indicator (measurableSet_histogram_cell J j)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [histogram_kernel_row J hJ x j hj z]
    by_cases hz : z ∈ cell J j <;> simp [hz]
  have hc : (∫ z in cell J j, (J:ℝ)*f x ∂design) = f x := by
    rw [setIntegral_const, hm, smul_eq_mul]
    field_simp
  have he : f x-projOp J f x = ∫ z in cell J j, (J:ℝ)*(f x-f z) ∂design := by
    calc
      f x-projOp J f x = (∫ z in cell J j, (J:ℝ)*f x ∂design) -
          (∫ z in cell J j, (J:ℝ)*f z ∂design) := by rw [hc, hp]
      _ = ∫ z in cell J j, (J:ℝ)*(f x-f z) ∂design := by
        rw [← integral_sub (integrable_const _) (hi.const_mul _).integrableOn]
        congr 1
        funext z
        ring
  have hb (z : unitInterval) (hz : z ∈ cell J j) :
      |(J:ℝ)*(f x-f z)| ≤ (J:ℝ)*(20*(J:ℝ)^(-s)) := by
    rw [abs_mul, abs_of_pos hJr]
    apply mul_le_mul_of_nonneg_left _ hJr.le
    calc
      |f x-f z| ≤ 20*|(x:ℝ)-(z:ℝ)|^s := hf.2.2 x z
      _ ≤ 20*((J:ℝ)⁻¹)^s := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (histogram_cell_diameter J hJ j x z hj hz) hs.1.le) (by norm_num)
      _ = 20*(J:ℝ)^(-s) := by rw [Real.rpow_neg_eq_inv_rpow]
  rw [he]
  calc
    |∫ z in cell J j, (J:ℝ)*(f x-f z) ∂design| ≤
        ∫ z in cell J j, |(J:ℝ)*(f x-f z)| ∂design := abs_integral_le_integral_abs
    _ ≤ ∫ z in cell J j, (J:ℝ)*(20*(J:ℝ)^(-s)) ∂design := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (integrable_const _)
      exact (ae_restrict_mem (measurableSet_histogram_cell J j)).mono (fun z hz => hb z hz)
    _ = 20*(J:ℝ)^(-s) := by
      rw [setIntegral_const, hm, smul_eq_mul]
      field_simp

/-- The inner product with a histogram feature has exactly one active coordinate. This statement assumes [the hJ condition](hyp:hJ), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: histogram_feature_inner
lemma histogram_feature_inner (J : ℕ) (hJ : 0 < J) (u : Vec J)
    (x : unitInterval) (j : Fin J) (hj : x ∈ cell J j) :
    inner ℝ u (featureMap J x) = Real.sqrt J*u j := by
  obtain ⟨k, hk, hu⟩ := histogram_cell_unique J hJ x
  have huniq : ∀ i : Fin J, x ∈ cell J i → i=j := by
    intro i hi
    exact (hu i hi).trans (hu j hj).symm
  simp only [PiLp.inner_apply, featureMap, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i hi hij
    have hxi : x ∉ cell J i := fun hi => hij (huniq i hi)
    simp [hxi]
  · simp

/-- Feature isometry: the displayed mathematical construction or bound. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: feature_isometry
lemma feature_isometry (J : ℕ) (hJ : 0 < J) (u : Vec J) :
    (∫ x, (inner ℝ u (featureMap J x))^2 ∂design) = ‖u‖^2 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let f : Fin J → unitInterval → ℝ := fun j =>
    (cell J j).indicator (fun _ => (J:ℝ)*(u j)^2)
  have he : (fun x => (inner ℝ u (featureMap J x))^2) = fun x => ∑ j, f j x := by
    funext x
    obtain ⟨j, hj, hu⟩ := histogram_cell_unique J hJ x
    rw [histogram_feature_inner J hJ u x j hj, Finset.sum_eq_single j]
    · simp only [f, Set.indicator_of_mem hj, mul_pow]
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ J)]
    · intro i hi hij
      exact Set.indicator_of_notMem (fun hi => hij (hu i hi)) _
    · simp
  have hi (j : Fin J) : Integrable (f j) design := by
    exact (integrable_const _).indicator (measurableSet_histogram_cell J j)
  rw [he, integral_finset_sum _ (fun j _ => hi j), EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [f]
  rw [integral_indicator (measurableSet_histogram_cell J j), setIntegral_const,
    Measure.real, histogram_cell_volume J hJ j, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  field_simp

/-- A fine histogram cell lies in its quotient-indexed coarse cell. This statement assumes [the hJ condition](hyp:hJ), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_refinement
lemma histogram_cell_refinement (J m : ℕ) (hJ : 0 < J) (hm : 0 < m)
    (k : Fin (J*m)) :
    ∃ j : Fin J, cell (J*m) k ⊆ cell J j := by
  have hidx : k.val / m < J := (Nat.div_lt_iff_lt_mul hm).mpr k.isLt
  let j : Fin J := ⟨k.val / m, hidx⟩
  refine ⟨j, ?_⟩
  intro x hx
  have hklo : (j.val:ℝ)*(m:ℝ) ≤ k.val := by
    exact_mod_cast Nat.div_mul_le_self k.val m
  have hkhi : (k.val:ℝ)+1 ≤ ((j.val:ℝ)+1)*(m:ℝ) := by
    have hh := Nat.mod_lt k.val hm
    have he := Nat.mod_add_div k.val m
    rw [Nat.mul_comm m] at he
    have hn : k.val+1 ≤ (j.val+1)*m := by
      dsimp [j]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact_mod_cast hn
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hKr : 0 < ((J*m:ℕ):ℝ) := by positivity
  have hxlo := hx.1
  have hxhi := hx.2
  change (j:ℝ)/J ≤ (x:ℝ) ∧
    ((x:ℝ) < ((j:ℝ)+1)/J ∨ (j.val+1=J ∧ (x:ℝ) ≤ 1))
  have hleft : (j:ℝ)/J ≤ (k:ℝ)/(J*m:ℕ) := by
    rw [div_le_div_iff₀ hJr hKr, Nat.cast_mul]
    nlinarith
  refine ⟨hleft.trans hxlo, ?_⟩
  by_cases hj : j.val+1=J
  · exact Or.inr ⟨hj, x.property.2⟩
  · left
    have hknlast : k.val+1 ≠ J*m := by
      intro he
      have he' : (k.val:ℝ)+1 = (J:ℝ)*(m:ℝ) := by exact_mod_cast he
      have hj' : (j.val:ℝ)+1 < J := by exact_mod_cast (show j.val+1 < J by omega)
      nlinarith
    have hlt : (x:ℝ) < ((k:ℝ)+1)/(J*m:ℕ) := hxhi.resolve_right (by simp [hknlast])
    apply hlt.trans_le
    rw [div_le_div_iff₀ hKr hJr, Nat.cast_mul]
    nlinarith

/-- Histogram kernels are symmetric and bounded by their rank. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_kernel_bounds
lemma histogram_kernel_bounds (J : ℕ) (hJ : 0 < J) (x z : unitInterval) :
    projKernel J x z = projKernel J z x ∧ |projKernel J x z| ≤ J := by
  constructor
  · exact real_inner_comm _ _
  · obtain ⟨j, hj, _⟩ := histogram_cell_unique J hJ x
    rw [histogram_kernel_row J hJ x j hj z]
    split_ifs <;> simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ J)]

/-- Integrating the product of a coarse and fine histogram row recovers the coarse row. This statement assumes [the hJ condition](hyp:hJ), [the hKpos condition](hyp:hKpos), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: histogram_kernel_composition
lemma histogram_kernel_composition (J K : ℕ) (hJ : 0 < J) (hKpos : 0 < K)
    (hJK : J ∣ K) (x z : unitInterval) :
    (∫ y, projKernel J x y*projKernel K y z ∂design) = projKernel J x z := by
  obtain ⟨m, rfl⟩ := hJK
  have hm : 0 < m := by nlinarith
  obtain ⟨k, hk, _⟩ := histogram_cell_unique (J*m) hKpos z
  obtain ⟨j, hj⟩ := histogram_cell_refinement J m hJ hm k
  have hzj := hj hk
  have he (y : unitInterval) :
      projKernel J x y*projKernel (J*m) y z =
        projKernel J x z*projKernel (J*m) z y := by
    rw [(histogram_kernel_bounds (J*m) hKpos y z).1,
      histogram_kernel_row (J*m) hKpos z k hk y]
    by_cases hy : y ∈ cell (J*m) k
    · have hyj := hj hy
      have hxy : projKernel J x y = projKernel J x z := by
        rw [(histogram_kernel_bounds J hJ x y).1,
          (histogram_kernel_bounds J hJ x z).1,
          histogram_kernel_row J hJ y j hyj x, histogram_kernel_row J hJ z j hzj x]
      simp [hy, hxy]
    · simp [hy]
  simp_rw [he]
  rw [integral_const_mul, (projection_rows (J*m) hKpos z).1, mul_one]

/-- Nested positive histogram ranks satisfy the exact cell-averaging tower identity. This statement assumes [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hKpos condition](hyp:hKpos), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: projection_nesting
lemma projection_nesting (J K : ℕ) (hJ : 0 < J) (hK : J ∣ K) (hKpos : 0 < K)
    (f : unitInterval → ℝ) (hf : Integrable f design) : projOp J (projOp K f) = projOp J f := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  funext x
  have hi : Integrable (fun yz : unitInterval × unitInterval =>
      (projKernel J x yz.1*projKernel K yz.1 yz.2)*f yz.2) (design.prod design) := by
    apply (hf.comp_snd design).bdd_mul
    · fun_prop
    · apply ae_of_all
      intro yz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (histogram_kernel_bounds J hJ x yz.1).2
        (histogram_kernel_bounds K hKpos yz.1 yz.2).2 (abs_nonneg _) (by positivity)
  unfold projOp
  calc
    (∫ y, projKernel J x y*(∫ z, projKernel K y z*f z ∂design) ∂design) =
        ∫ y, ∫ z, (projKernel J x y*projKernel K y z)*f z ∂design ∂design := by
      simp_rw [← integral_const_mul, mul_assoc]
    _ = ∫ z, ∫ y, (projKernel J x y*projKernel K y z)*f z ∂design ∂design :=
      integral_integral_swap hi
    _ = ∫ z, projKernel J x z*f z ∂design := by
      simp_rw [integral_mul_const, histogram_kernel_composition J K hJ hKpos hK x]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
