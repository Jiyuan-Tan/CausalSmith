module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovariateKernelMoments

/-! Squared-norm contraction of correction-cell averaging under the uniform
design and exact multiband squared-kernel masses. These estimates apply
contraction before summing orthogonal bands in the multiband covariance proof. -/

public section

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- On a normalized cell, the squared norm of a mean is bounded by its second moment. -/
-- @node: correctionCellLaw_norm_integral_sq_le
lemma correctionCellLaw_norm_integral_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (i : Fin k) (f : ℝ → E)
    (hf : Integrable f unitVolume)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) unitVolume) :
    ‖∫ x, f x ∂correctionCellLaw k i‖ ^ 2 ≤
      ∫ x, ‖f x‖ ^ 2 ∂correctionCellLaw k i := by
  let := correctionCellLaw_probability k hk i
  have hn := integrable_correctionCellLaw k i (fun x => ‖f x‖) hf.norm
  have hn2 := integrable_correctionCellLaw k i _ hf2
  have hv : 0 ≤ ∫ x, (‖f x‖ - ∫ z, ‖f z‖ ∂correctionCellLaw k i) ^ 2
      ∂correctionCellLaw k i := integral_nonneg (fun x => sq_nonneg _)
  rw [← cell_variance_centered_identity (correctionCellLaw k i) _ hn hn2] at hv
  have hm : 0 ≤ ∫ x, ‖f x‖ ∂correctionCellLaw k i :=
    integral_nonneg (fun x => norm_nonneg (f x))
  exact ((sq_le_sq₀ (norm_nonneg _) hm).2
    (norm_integral_le_integral_norm f)).trans (by linarith)

/-- The pointwise cell mean satisfies Jensen's squared-norm inequality. -/
-- @node: cellAverage_norm_sq_le
lemma cellAverage_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (f : ℝ → E)
    (hf : Integrable f unitVolume)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) unitVolume) (x : ℝ) :
    ‖cellAverage k f x‖ ^ 2 ≤ cellAverage k (fun z => ‖f z‖ ^ 2) x := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hx : cell k x = i.val + 1 := by dsimp [i]; omega
  rw [cellAverage_eq_correctionCellLaw k i f x hx,
    cellAverage_eq_correctionCellLaw k i (fun z => ‖f z‖ ^ 2) x hx]
  exact correctionCellLaw_norm_integral_sq_le k hk i f hf hf2

/-- Squared cell-average norms are integrable, being constant on finitely many cells. -/
-- @node: integrable_cellAverage_norm_sq
@[fun_prop] lemma integrable_cellAverage_norm_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (f : ℝ → E) :
    Integrable (fun x => ‖cellAverage k f x‖ ^ 2) unitVolume := by
  apply integrable_histogram_cellwise_vector k hk _
    (fun i => ‖∫ z, f z ∂correctionCellLaw k i‖ ^ 2)
  intro i
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  rw [cellAverage_eq_correctionCellLaw k i f x hx.2]

/-- Averaging on any positive-rank partition contracts the integrated squared norm. -/
-- @node: integral_cellAverage_norm_sq_le
lemma integral_cellAverage_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (f : ℝ → E)
    (hf : Integrable f unitVolume)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) unitVolume) :
    (∫ x, ‖cellAverage k f x‖ ^ 2 ∂unitVolume) ≤ ∫ x, ‖f x‖ ^ 2 ∂unitVolume := by
  calc
    _ ≤ ∫ x, cellAverage k (fun z => ‖f z‖ ^ 2) x ∂unitVolume :=
      integral_mono (integrable_cellAverage_norm_sq k hk f)
        (integrable_cellAverage k hk _) (cellAverage_norm_sq_le k hk f hf hf2)
    _ = _ := integral_cellAverage_vector k hk _ hf2


/-- Squared band norms are integrable under an integrable squared norm envelope. -/
-- @node: integrable_Qband_norm_sq
@[fun_prop] lemma integrable_Qband_norm_sq (L T : ℕ) (hL : Dyadic L) (t : ℕ) (ht : t ≤ T)
    (v : ℝ → Hj (2 ^ T * L)) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) :
    Integrable (fun x => ‖Qband L (2 ^ T * L) t (v x)‖ ^ 2) unitVolume := by
  have hi := integrable_Qband unitVolume L (2 ^ T * L) t v hv
  apply hv2.mono' (hi.aestronglyMeasurable.norm.pow 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    ((band_projection_algebra L T hL).2.2 t ht (v x))

/-- Differing averaging ranks still give total band energy at most the original energy. -/
-- @node: integral_band_cellAverage_energy_le
lemma integral_band_cellAverage_energy_le (L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (v : ℝ → Hj (2 ^ T * L)) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) :
    (∑ t ∈ Finset.range (T + 1), ∫ x,
      ‖cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x‖ ^ 2
        ∂unitVolume) ≤ ∫ x, ‖v x‖ ^ 2 ∂unitVolume := by
  have ht (t : ℕ) (ht : t ∈ Finset.range (T + 1)) : t ≤ T := by
    have := Finset.mem_range.mp ht
    omega
  calc
    _ ≤ ∑ t ∈ Finset.range (T + 1), ∫ x,
        ‖Qband L (2 ^ T * L) t (v x)‖ ^ 2 ∂unitVolume := by
      apply Finset.sum_le_sum
      intro t hmem
      exact integral_cellAverage_norm_sq_le (kt t) (hkt t (ht t hmem)) _
        (integrable_Qband unitVolume L (2 ^ T * L) t v hv)
        (integrable_Qband_norm_sq L T hL t (ht t hmem) v hv hv2)
    _ = ∫ x, ∑ t ∈ Finset.range (T + 1),
        ‖Qband L (2 ^ T * L) t (v x)‖ ^ 2 ∂unitVolume := by
      symm
      exact integral_finsetSum _ (fun t hmem =>
        integrable_Qband_norm_sq L T hL t (ht t hmem) v hv hv2)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← band_remainder_sum_norm_sq L T hL _ ht (fun _ => v x),
        (band_projection_algebra L T hL).1 (v x)]

/-- The reconstructed vector of differently averaged bands has no band-count energy loss. -/
-- @node: integral_multiband_cellAverage_norm_sq_le
lemma integral_multiband_cellAverage_norm_sq_le (L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (v : ℝ → Hj (2 ^ T * L)) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) :
    (∫ x, ‖∑ t ∈ Finset.range (T + 1),
      cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x‖ ^ 2
        ∂unitVolume) ≤ ∫ x, ‖v x‖ ^ 2 ∂unitVolume := by
  have he (x : ℝ) :
      ‖∑ t ∈ Finset.range (T + 1),
        cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x‖ ^ 2 =
      ∑ t ∈ Finset.range (T + 1),
        ‖cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x‖ ^ 2 := by
    simp_rw [← Qband_cellAverage _ L (2 ^ T * L) _ v hv]
    exact band_remainder_sum_norm_sq L T hL _
      (fun t ht => by have := Finset.mem_range.mp ht; omega)
      (fun t => cellAverage (kt t) v x)
  simp_rw [he]
  rw [integral_finsetSum _ (fun t ht =>
    integrable_cellAverage_norm_sq (kt t)
      (hkt t (by have := Finset.mem_range.mp ht; omega)) _)]
  exact integral_band_cellAverage_energy_le L T hL kt hkt v hv hv2

/-- Vector cell averages are integrable because only finitely many values occur. -/
-- @node: integrable_cellAverage_vector
@[fun_prop] lemma integrable_cellAverage_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (f : ℝ → E) :
    Integrable (cellAverage k f) unitVolume := by
  apply integrable_histogram_cellwise_vector k hk _
    (fun i => ∫ z, f z ∂correctionCellLaw k i)
  intro i
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  exact cellAverage_eq_correctionCellLaw k i f x hx.2

/-- An arbitrary histogram contrast of averaged bands is bounded by the original vector energy. -/
-- @node: integral_multiband_cellAverage_inner_sq_le
lemma integral_multiband_cellAverage_inner_sq_le (L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (v : ℝ → Hj (2 ^ T * L)) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) (f : Hj (2 ^ T * L)) :
    (∫ x, (inner ℝ (∑ t ∈ Finset.range (T + 1),
      cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x) f) ^ 2
        ∂unitVolume) ≤ (∫ x, ‖v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
  let w := fun x => ∑ t ∈ Finset.range (T + 1),
    cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x
  have ht (t : ℕ) (ht : t ∈ Finset.range (T + 1)) : t ≤ T := by
    have := Finset.mem_range.mp ht
    omega
  have hw : Integrable w unitVolume := by
    exact integrable_finsetSum _ (fun t hmem =>
      integrable_cellAverage_vector (kt t) (hkt t (ht t hmem)) _)
  have hw2 : Integrable (fun x => ‖w x‖ ^ 2) unitVolume := by
    have hi := integrable_finsetSum (Finset.range (T + 1)) (fun t hmem =>
      integrable_cellAverage_norm_sq (kt t) (hkt t (ht t hmem))
        (fun z => Qband L (2 ^ T * L) t (v z)))
    apply hi.congr
    filter_upwards [] with x
    dsimp [w]
    simp_rw [← Qband_cellAverage _ L (2 ^ T * L) _ v hv]
    exact (band_remainder_sum_norm_sq L T hL _ ht
      (fun t => cellAverage (kt t) v x)).symm
  have hb (x : ℝ) : (inner ℝ (w x) f) ^ 2 ≤ ‖w x‖ ^ 2 * ‖f‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (w x) f
    rw [Real.norm_eq_abs] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    simpa only [sq_abs, mul_pow] using hs
  have hi : Integrable (fun x => (inner ℝ (w x) f) ^ 2) unitVolume := by
    apply (hw2.mul_const (‖f‖ ^ 2)).mono'
      (((continuous_id.inner continuous_const).comp_aestronglyMeasurable
        hw.aestronglyMeasurable).pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (inner ℝ (w x) f))]
    exact hb x
  calc
    _ ≤ ∫ x, ‖w x‖ ^ 2 * ‖f‖ ^ 2 ∂unitVolume :=
      integral_mono hi (hw2.mul_const _) hb
    _ = (∫ x, ‖w x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (integral_multiband_cellAverage_norm_sq_le L T hL kt hkt v hv hv2) (sq_nonneg _)

/-- Squared kernel rows are integrable on the uniform design. -/
-- @node: integrable_covariateKernel_sq
@[fun_prop] lemma integrable_covariateKernel_sq (k : ℕ) (x : ℝ) :
    Integrable (fun z => (covariateKernel k x z) ^ 2) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply (integrable_const ((k : ℝ) ^ 2)).mono' (by fun_prop)
  filter_upwards [] with z
  unfold covariateKernel
  split_ifs <;> simp

/-- Orthogonality integrates a multiband kernel's exact squared norm without cross terms. -/
-- @node: integral_multiband_kernel_norm_sq
lemma integral_multiband_kernel_norm_sq (L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (f : Hj (2 ^ T * L)) :
    (∫ x, ∫ z, ‖∑ t ∈ Finset.range (T + 1),
      covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2
        ∂unitVolume ∂unitVolume) =
      ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have he (x z : ℝ) :
      ‖∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2 =
      ∑ t ∈ Finset.range (T + 1), (covariateKernel (kt t) x z) ^ 2 *
        ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    simp_rw [← Qband_smul]
    rw [band_remainder_sum_norm_sq L T hL _
      (fun t ht => by have := Finset.mem_range.mp ht; omega)]
    simp only [Qband_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hr (x : ℝ) :
      (∫ z, ‖∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2 ∂unitVolume) =
      ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) *
        ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    simp_rw [he]
    rw [integral_finsetSum _ (fun t _ =>
      (integrable_covariateKernel_sq (kt t) x).mul_const _)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [integral_mul_const, integral_covariateKernel_sq (kt t)
      (hkt t (by have := Finset.mem_range.mp ht; omega))]
  simp_rw [hr]
  simp

end CausalSmith.Stat.DensityEffectRoughNull
