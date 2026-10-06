module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotCellBounds

/-! Concrete normalized correction cells and the integrated remainders in (25) and (28). -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Uniform probability law within a positive-rank correction cell. -/
-- @node: correctionCellLaw
def correctionCellLaw (k : ℕ) (i : Fin k) : Measure ℝ :=
  (k : ℝ≥0∞) • unitVolume.restrict (histogramCell k (i.val + 1))

/-- Each correction cell has mass one after multiplication by its rank. -/
-- @node: correctionCellLaw_probability
lemma correctionCellLaw_probability (k : ℕ) (hk : 0 < k) (i : Fin k) :
    IsProbabilityMeasure (correctionCellLaw k i) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  constructor
  have hm := histogramCell_mass_eq k hk i
  have he : unitVolume (histogramCell k (i.val + 1)) = (k : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simpa using hk.ne')).1
    simpa [measureReal_def] using hm
  simp only [correctionCellLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, he]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hk.ne') (by simp)

/-- The normalized correction law is supported on its stated unit-interval cell. -/
-- @node: correctionCellLaw_support
lemma correctionCellLaw_support (k : ℕ) (i : Fin k) :
    ∀ᵐ x ∂correctionCellLaw k i, x ∈ Set.Icc 0 1 ∧ cell k x = i.val + 1 := by
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))

/-- The concrete kernel average is exactly expectation under the normalized cell law. -/
-- @node: cellAverage_eq_correctionCellLaw
lemma cellAverage_eq_correctionCellLaw {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (i : Fin k) (f : ℝ → E) (x : ℝ)
    (hx : cell k x = i.val + 1) :
    cellAverage k f x = ∫ z, f z ∂correctionCellLaw k i := by
  rw [correctionCellLaw, integral_smul_measure]
  simp only [ENNReal.toReal_natCast]
  unfold cellAverage
  rw [← integral_smul, ← integral_indicator (measurableSet_histogramCell k (i.val + 1))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
  simp [covariateKernel, hx, Set.indicator, histogramCell, hz.1, hz.2, eq_comm]

/-- Constancy on measurable histogram fibers implies measurability. -/
-- @node: measurable_of_histogram_const
lemma measurable_of_histogram_const (k : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x z, cell k x = cell k z → f x = f z) : Measurable f := by
  obtain ⟨g, rfl⟩ := (Function.factorsThrough_iff f).1 (fun _ _ h => hf _ _ h)
  exact (measurable_of_countable g).comp (measurable_histogram_cell k)

/-- Fixed trained propensity pilots are measurable in the covariate. -/
@[fun_prop] lemma measurable_pilotPi_covariate {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) : Measurable (pilotPi train mx a) := by
  apply measurable_of_histogram_const mx
  exact pilotPi_eq_of_cell_eq train mx a

/-- Normalization retains measurability of a fixed outcome slice of the trained pilot. -/
-- @node: measurable_densityPilot_covariate
@[fun_prop] lemma measurable_densityPilot_covariate {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (y : ℝ) :
    Measurable (fun x => densityPilot train mx my a x y) := by
  apply measurable_of_histogram_const mx
  intro x z h
  exact densityPilot_eq_of_cell_eq train mx my a x z y h

/-- Relative propensity errors are measurable for every fixed training realization. -/
-- @node: measurable_uerr_covariate
@[fun_prop] lemma measurable_uerr_covariate {m : ℕ} (P : ObsLaw)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) : Measurable (uerr P train mx a) := by
  have he := P.e_measurable
  unfold uerr pi armProbability
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- The weighted density error is measurable on each fixed outcome slice. -/
-- @node: measurable_verr_covariate
@[fun_prop] lemma measurable_verr_covariate {m : ℕ} (P : ObsLaw)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (y : ℝ) :
    Measurable (fun x => verr P train mx my a x y) := by
  have he : Measurable (fun x => P.eta a x y) :=
    (P.eta_measurable a).comp (measurable_id.prodMk measurable_const)
  unfold verr werr
  fun_prop


/-- Bounded propensity errors are integrable on the known design. -/
-- @node: integrable_uerr_covariate
lemma integrable_uerr_covariate {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) :
    Integrable (uerr P train mx a) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa only [Real.norm_eq_abs] using uerr_abs_le P hModel train mx a x hx

/-- Every positive integer power of the relative error is integrable on the design. -/
-- @node: integrable_uerr_pow_covariate
lemma integrable_uerr_pow_covariate {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (n : ℕ) :
    Integrable (fun x => (uerr P train mx a x) ^ n) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) (2 ^ n)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (uerr_abs_le P hModel train mx a x hx) n

/-- Good-pilot outcome slices are integrable in the covariate without an extra premise. -/
-- @node: goodPilot_integrable_verr_covariate
lemma goodPilot_integrable_verr_covariate {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    Integrable (fun x => verr P train mx my a x y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) (3 * hAllow C0 m mx my)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa only [Real.norm_eq_abs] using goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx hy

/-- Products needed for correction-cell covariances are integrable from clipping and G. -/
-- @node: goodPilot_integrable_uerr_pow_mul_verr
lemma goodPilot_integrable_uerr_pow_mul_verr {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my : ℕ)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1)
    (n : ℕ) : Integrable (fun x => (uerr P train mx a x) ^ n *
      verr P train mx my a x y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) (2 ^ n * (3 * hAllow C0 m mx my))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) (uerr_abs_le P hModel train mx a x hx) n)
    (goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx hy)
    (abs_nonneg _) (by positivity)

/-- Integrable design functions remain integrable under normalized correction-cell laws. -/
-- @node: integrable_correctionCellLaw
lemma integrable_correctionCellLaw (k : ℕ) (i : Fin k) (f : ℝ → ℝ)
    (hf : Integrable f unitVolume) : Integrable f (correctionCellLaw k i) := by
  exact hf.integrableOn.smul_measure (by simp)

/-- Scalar kernel averages are measurable, since their values depend only on a cell label. -/
-- @node: measurable_cellAverage_scalar
@[fun_prop] lemma measurable_cellAverage_scalar (k : ℕ) (f : ℝ → ℝ) :
    Measurable (cellAverage k f) := by
  apply measurable_of_histogram_const k
  intro x z h
  simp only [cellAverage, covariateKernel, h]

/-- Averaging a uniform scalar envelope on any correction cell preserves that envelope. -/
-- @node: cellAverage_abs_le
lemma cellAverage_abs_le (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ) (b : ℝ)
    (hf : ∀ᵐ z ∂unitVolume, |f z| ≤ b) (x : ℝ) : |cellAverage k f x| ≤ b := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  let := correctionCellLaw_probability k hk i
  rw [cellAverage_eq_correctionCellLaw k i f x hc]
  have hb : ∀ᵐ z ∂correctionCellLaw k i, ‖f z‖ ≤ b :=
    Measure.ae_smul_measure (ae_restrict_of_ae (by simpa only [Real.norm_eq_abs] using hf)) _
  simpa [Real.norm_eq_abs, measureReal_def] using
    norm_integral_le_of_norm_le_const hb

/-- The squared cell-average product in (28) is an integrable observable design function. -/
-- @node: goodPilot_integrable_cellAverage_sq_mul
lemma goodPilot_integrable_cellAverage_sq_mul {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ) (hk : 0 < k)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    Integrable (fun x => (cellAverage k (uerr P train mx a) x) ^ 2 *
      cellAverage k (fun z => verr P train mx my a z y) x) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hu : ∀ᵐ z ∂unitVolume, |uerr P train mx a z| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact uerr_abs_le P hModel train mx a z hz
  have hv : ∀ᵐ z ∂unitVolume, |verr P train mx my a z y| ≤ 3 * hAllow C0 m mx my := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact goodPilot_verr_abs_le P hModel train C0 mx my hG a z y hz hy
  apply Integrable.of_bound (by fun_prop) (4 * (3 * hAllow C0 m mx my))
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul (by
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) (cellAverage_abs_le k hk _ 2 hu x) 2)
    (cellAverage_abs_le k hk _ _ hv x) (abs_nonneg _) (by norm_num)


/-- Positive-rank histogram cells partition the entire design domain. -/
-- @node: histogramCells_cover
lemma histogramCells_cover (k : ℕ) (hk : 0 < k) :
    (⋃ i : Fin k, histogramCell k (i.val + 1)) = Set.Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
    exact hx.1
  · intro hx
    have hi := cell_index_mem k hk x
    let i : Fin k := ⟨cell k x - 1, by omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, hx, ?_⟩
    dsimp [i]
    omega

/-- Distinct histogram labels give disjoint correction cells. -/
-- @node: histogramCells_disjoint
lemma histogramCells_disjoint (k : ℕ) :
    Pairwise (fun i j : Fin k => Disjoint (histogramCell k (i.val + 1))
      (histogramCell k (j.val + 1))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hz
  apply hij
  apply Fin.ext
  have h := hx.2.symm.trans hz.2
  omega

/-- Design integration splits exactly into the finitely many correction cells. -/
-- @node: integral_eq_sum_histogramCells
lemma integral_eq_sum_histogramCells (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ)
    (hf : ∀ i : Fin k, IntegrableOn f (histogramCell k (i.val + 1)) unitVolume) :
    (∫ x, f x ∂unitVolume) =
      ∑ i : Fin k, ∫ x in histogramCell k (i.val + 1), f x ∂unitVolume := by
  have h := integral_iUnion_fintype (fun i : Fin k =>
    measurableSet_histogramCell k (i.val + 1)) (histogramCells_disjoint k) hf
  rw [histogramCells_cover k hk] at h
  simpa only [unitVolume, Measure.restrict_restrict measurableSet_Icc, Set.inter_self] using h

/-- Averaging on the uniform partition preserves the design integral exactly. -/
-- @node: integral_cellAverage
lemma integral_cellAverage (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ)
    (hf : Integrable f unitVolume) :
    (∫ x, cellAverage k f x ∂unitVolume) = ∫ x, f x ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hc (i : Fin k) : ∀ᵐ x ∂unitVolume.restrict (histogramCell k (i.val + 1)),
      cellAverage k f x = ∫ z, f z ∂correctionCellLaw k i := by
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    exact cellAverage_eq_correctionCellLaw k i f x hx.2
  have hi (i : Fin k) : IntegrableOn (cellAverage k f) (histogramCell k (i.val + 1))
      unitVolume := (integrable_const _).congr (Filter.EventuallyEq.symm (hc i))
  rw [integral_eq_sum_histogramCells k hk _ hi,
    integral_eq_sum_histogramCells k hk f (fun _ => hf.integrableOn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_congr_ae (hc i), integral_const]
  have hm : (unitVolume.restrict (histogramCell k (i.val + 1))).real Set.univ = 1 / (k : ℝ) := by
    simpa [measureReal_def] using histogramCell_mass_eq k hk i
  rw [hm, correctionCellLaw, integral_smul_measure]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Every uniformly bounded scalar design function has an integrable cell average. -/
-- @node: integrable_cellAverage_of_bound
lemma integrable_cellAverage_of_bound (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ)
    (b : ℝ) (hf : ∀ᵐ z ∂unitVolume, |f z| ≤ b) :
    Integrable (cellAverage k f) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) b
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using cellAverage_abs_le k hk f b hf x

/-- Equation (28)'s local remainder bound now applies to the actual kernel cell averages. -/
-- @node: goodPilot_cellAverage_squared_error_abs_le
lemma goodPilot_cellAverage_squared_error_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) (x : ℝ) :
    |cellAverage k (fun z => (uerr P train mx a z) ^ 2 * verr P train mx my a z y) x -
      (cellAverage k (uerr P train mx a) x) ^ 2 *
        cellAverage k (fun z => verr P train mx my a z y) x| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  let := correctionCellLaw_probability k hk i
  rw [cellAverage_eq_correctionCellLaw k i _ x hc,
    cellAverage_eq_correctionCellLaw k i _ x hc,
    cellAverage_eq_correctionCellLaw k i _ x hc]
  exact goodPilot_cell_squared_error_abs_le P hModel train C0 mx my k hmx hk hdiv hG hh
    a y hy (correctionCellLaw k i) (i.val + 1) (correctionCellLaw_support k i)
    (integrable_correctionCellLaw k i _ (integrable_uerr_covariate P hModel train mx a))
    (integrable_correctionCellLaw k i _ (integrable_uerr_pow_covariate P hModel train mx a 2))
    (integrable_correctionCellLaw k i _ (goodPilot_integrable_verr_covariate P hModel train C0 mx my hG a y hy))
    (integrable_correctionCellLaw k i _ (goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 2))

/-- Integrating the actual third-order remainder gives the dimension-free bound in (28). -/
-- @node: goodPilot_integrated_squared_error_abs_le
lemma goodPilot_integrated_squared_error_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |∫ x, (cellAverage k (uerr P train mx a) x) ^ 2 *
        cellAverage k (fun z => verr P train mx my a z y) x -
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume| ≤
      27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let f := fun x => (uerr P train mx a x) ^ 2 * verr P train mx my a x y
  have hf := goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 2
  have hp := goodPilot_integrable_cellAverage_sq_mul P hModel train C0 mx my k hk hG a y hy
  have hb : ∀ᵐ x ∂unitVolume, |f x| ≤ 4 * (3 * hAllow C0 m mx my) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    dsimp [f]
    rw [abs_mul, abs_pow]
    exact mul_le_mul (by
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) (uerr_abs_le P hModel train mx a x hx) 2)
      (goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx hy)
      (abs_nonneg _) (by norm_num)
  have hav := integrable_cellAverage_of_bound k hk f _ hb
  rw [integral_sub hp hf, ← integral_cellAverage k hk f hf,
    ← integral_sub hp hav]
  have hpoint : ∀ᵐ x ∂unitVolume,
      ‖(cellAverage k (uerr P train mx a) x) ^ 2 *
        cellAverage k (fun z => verr P train mx my a z y) x - cellAverage k f x‖ ≤
        27200 * hAllow C0 m mx my * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      goodPilot_cellAverage_squared_error_abs_le P hModel train C0 mx my k
        hmx hk hdiv hG hh a y hy x
  simpa [Real.norm_eq_abs, measureReal_def] using
    norm_integral_le_of_norm_le_const hpoint

/-- Final-rank projection preserves the integrated third remainder's 27200h q⁻¹ᐟ⁵ bound. -/
-- @node: goodPilot_squared_error_coefficients_norm_le
lemma goodPilot_squared_error_coefficients_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my q J : ℕ)
    (hmx : 0 < mx) (hq : 0 < q) (hJ : 0 < J) (hdiv : mx ∣ q)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1) (a : Bool) :
    ‖coefficients J (fun y => ∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 *
        cellAverage q (fun z => verr P train mx my a z y) x -
        (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume)‖ ≤
      27200 * hAllow C0 m mx my * (q : ℝ) ^ (-1 / 5 : ℝ) := by
  apply coefficients_norm_le_of_abs_le J hJ _ _
    (mul_nonneg (mul_nonneg (by norm_num)
      (goodPilot_allowance_nonneg P hModel train C0 mx my hG)) (by positivity))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_integrated_squared_error_abs_le P hModel train C0 mx my q hmx hq hdiv hG hh a y hy


/-- The second-order cell-average product is integrable on the uniform design domain. -/
-- @node: goodPilot_integrable_cellAverage_mul
lemma goodPilot_integrable_cellAverage_mul {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ) (hk : 0 < k)
    (hG : GoodPilot P train C0 mx my) (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    Integrable (fun x => cellAverage k (uerr P train mx a) x *
      cellAverage k (fun z => verr P train mx my a z y) x) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hu : ∀ᵐ z ∂unitVolume, |uerr P train mx a z| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact uerr_abs_le P hModel train mx a z hz
  have hv : ∀ᵐ z ∂unitVolume, |verr P train mx my a z y| ≤ 3 * hAllow C0 m mx my := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact goodPilot_verr_abs_le P hModel train C0 mx my hG a z y hz hy
  apply Integrable.of_bound (by fun_prop) (2 * (3 * hAllow C0 m mx my))
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (cellAverage_abs_le k hk _ 2 hu x)
    (cellAverage_abs_le k hk _ _ hv x) (abs_nonneg _) (by norm_num)

/-- Equation (25)'s covariance bound applies to the concrete kernel cell averages. -/
-- @node: goodPilot_cellAverage_covariance_abs_le
lemma goodPilot_cellAverage_covariance_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) (x : ℝ) :
    |cellAverage k (fun z => uerr P train mx a z * verr P train mx my a z y) x -
      cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x| ≤
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  let := correctionCellLaw_probability k hk i
  rw [cellAverage_eq_correctionCellLaw k i _ x hc,
    cellAverage_eq_correctionCellLaw k i _ x hc,
    cellAverage_eq_correctionCellLaw k i _ x hc]
  exact goodPilot_cell_covariance_abs_le P hModel train C0 mx my k hmx hk hdiv hG hh
    a y hy (correctionCellLaw k i) (i.val + 1) (correctionCellLaw_support k i)
    (integrable_correctionCellLaw k i _ (integrable_uerr_covariate P hModel train mx a))
    (integrable_correctionCellLaw k i _ (goodPilot_integrable_verr_covariate P hModel train C0 mx my hG a y hy))
    (integrable_correctionCellLaw k i _ (by simpa using
      goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 1))

/-- Design integration preserves the second remainder's 2800k⁻¹ᐟ⁵ envelope. -/
-- @node: goodPilot_integrated_covariance_abs_le
lemma goodPilot_integrated_covariance_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    |∫ x, uerr P train mx a x * verr P train mx my a x y -
      cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x ∂unitVolume| ≤
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let f := fun x => uerr P train mx a x * verr P train mx my a x y
  have hf : Integrable f unitVolume := by
    simpa [f] using goodPilot_integrable_uerr_pow_mul_verr P hModel train C0 mx my hG a y hy 1
  have hp := goodPilot_integrable_cellAverage_mul P hModel train C0 mx my k hk hG a y hy
  have hb : ∀ᵐ x ∂unitVolume, |f x| ≤ 2 * (3 * hAllow C0 m mx my) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    dsimp [f]
    rw [abs_mul]
    exact mul_le_mul (uerr_abs_le P hModel train mx a x hx)
      (goodPilot_verr_abs_le P hModel train C0 mx my hG a x y hx hy)
      (abs_nonneg _) (by norm_num)
  have hav := integrable_cellAverage_of_bound k hk f _ hb
  rw [integral_sub hf hp, ← integral_cellAverage k hk f hf, ← integral_sub hav hp]
  have hpoint : ∀ᵐ x ∂unitVolume,
      ‖cellAverage k f x - cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x‖ ≤
        2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using
      goodPilot_cellAverage_covariance_abs_le P hModel train C0 mx my k
        hmx hk hdiv hG hh a y hy x
  simpa [Real.norm_eq_abs, measureReal_def] using norm_integral_le_of_norm_le_const hpoint

/-- The initial-band remainder's final-rank coefficients obey the bound in (27). -/
-- @node: goodPilot_covariance_coefficients_norm_le
lemma goodPilot_covariance_coefficients_norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (C0 : ℝ) (mx my k J : ℕ)
    (hmx : 0 < mx) (hk : 0 < k) (hJ : 0 < J) (hdiv : mx ∣ k)
    (hG : GoodPilot P train C0 mx my) (hh : hAllow C0 m mx my ≤ 1) (a : Bool) :
    ‖coefficients J (fun y => ∫ x, uerr P train mx a x * verr P train mx my a x y -
      cellAverage k (uerr P train mx a) x *
        cellAverage k (fun z => verr P train mx my a z y) x ∂unitVolume)‖ ≤
      2800 * (k : ℝ) ^ (-1 / 5 : ℝ) := by
  apply coefficients_norm_le_of_abs_le J hJ _ _ (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact goodPilot_integrated_covariance_abs_le P hModel train C0 mx my k hmx hk hdiv hG hh a y hy

end CausalSmith.Stat.DensityEffectRoughNull
