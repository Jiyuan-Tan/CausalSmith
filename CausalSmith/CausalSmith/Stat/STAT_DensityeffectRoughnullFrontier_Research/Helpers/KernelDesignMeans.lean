module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellProjectionMeans
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ProjectedBandRemainders

/-! Uniform-design kernel integration for the second and third role means in (21).
Cellwise factors can be pulled through correction-cell expectations; integrating the
result gives the products of cell means without any smoothness or good-pilot premise. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A cellwise constant scalar factor pulls through vector-valued cell averaging. -/
-- @node: cellAverage_cellwise_smul
lemma cellAverage_cellwise_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (c : ℝ → ℝ) (f : ℝ → E)
    (hc : ∀ x z, cell k x = cell k z → c x = c z) (x : ℝ) :
    cellAverage k (fun z => c z • f z) x = c x • cellAverage k f x := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hx : cell k x = i.val + 1 := by dsimp [i]; omega
  rw [cellAverage_eq_correctionCellLaw k i _ x hx,
    cellAverage_eq_correctionCellLaw k i f x hx, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [correctionCellLaw_support k i] with z hz
  rw [hc z x (hz.2.trans hx.symm)]

/-- Multiplying an integrable vector by a cellwise constant scalar preserves integrability. -/
-- @node: integrable_cellwise_smul
lemma integrable_cellwise_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (c : ℝ → ℝ) (f : ℝ → E)
    (hc : ∀ x z, cell k x = cell k z → c x = c z)
    (hf : Integrable f unitVolume) : Integrable (fun x => c x • f x) unitVolume := by
  have hi : ∀ i : Fin k, IntegrableOn (fun x => c x • f x)
      (histogramCell k (i.val + 1)) unitVolume := by
    intro i
    apply (hf.integrableOn.smul (c (midpoint k i))).congr
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    rw [hc (midpoint k i) x ((cell_midpoint_self k i).trans hx.2.symm)]
    rfl
  have h := integrableOn_finite_iUnion.mpr hi
  rw [histogramCells_cover k hk] at h
  simpa only [IntegrableOn, unitVolume, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_self] using h

/-- In an integrated cellwise scalar product the vector may be replaced by its cell mean. -/
-- @node: integral_cellwise_smul_eq_cellAverage
lemma integral_cellwise_smul_eq_cellAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) (hk : 0 < k)
    (c : ℝ → ℝ) (f : ℝ → E)
    (hc : ∀ x z, cell k x = cell k z → c x = c z)
    (hf : Integrable f unitVolume) :
    (∫ x, c x • f x ∂unitVolume) =
      ∫ x, c x • cellAverage k f x ∂unitVolume := by
  rw [← integral_cellAverage_vector k hk _ (integrable_cellwise_smul k hk c f hc hf)]
  simp_rw [cellAverage_cellwise_smul k hk c f hc]

/-- Independent uniform-design records integrate a two-role kernel to the product of cell means. -/
-- @node: integral_pair_design_kernel
lemma integral_pair_design_kernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → E) (hg : Integrable g unitVolume)
    (hf : Integrable f unitVolume) :
    (∫ x, ∫ z, (g x * covariateKernel k x z) • f z ∂unitVolume ∂unitVolume) =
      ∫ z, cellAverage k g z • cellAverage k f z ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi : Integrable (fun p : ℝ × ℝ =>
      (g p.1 * covariateKernel k p.1 p.2) • f p.2) (unitVolume.prod unitVolume) := by
    have h := hg.smul_prod hf
    have hm : Measurable (fun p : ℝ × ℝ => covariateKernel k p.1 p.2) := by fun_prop
    have hb : ∀ᵐ p ∂unitVolume.prod unitVolume, ‖covariateKernel k p.1 p.2‖ ≤ k := by
      filter_upwards [] with p
      unfold covariateKernel
      split_ifs <;> simp
    have hbnd := h.bdd_smul (k : ℝ) hm.aestronglyMeasurable hb
    change Integrable (fun p : ℝ × ℝ => covariateKernel k p.1 p.2 •
      (g p.1 • f p.2)) _ at hbnd
    simpa only [smul_smul, mul_comm] using hbnd
  rw [integral_integral_swap hi]
  have he (z : ℝ) :
      (∫ x, (g x * covariateKernel k x z) • f z ∂unitVolume) =
        cellAverage k g z • f z := by
    rw [integral_smul_const]
    congr 1
    unfold cellAverage
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [covariateKernel, smul_eq_mul]
    by_cases h : cell k x = cell k z
    · rw [if_pos h, if_pos h.symm, mul_comm]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero, zero_mul]
  simp_rw [he]
  exact integral_cellwise_smul_eq_cellAverage k hk (cellAverage k g) f
    (fun x z h => cellAverage_eq_of_cell_eq k g x z h) hf

/-- A cellwise constant vector factor pulls through scalar cell averaging. -/
-- @node: cellAverage_smul_cellwise_vector
lemma cellAverage_smul_cellwise_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) (hk : 0 < k) (g : ℝ → ℝ) (c : ℝ → E)
    (hc : ∀ x z, cell k x = cell k z → c x = c z) (x : ℝ) :
    cellAverage k (fun z => g z • c z) x = cellAverage k g x • c x := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hx : cell k x = i.val + 1 := by dsimp [i]; omega
  rw [cellAverage_eq_correctionCellLaw k i _ x hx,
    cellAverage_eq_correctionCellLaw k i g x hx, ← integral_smul_const]
  apply integral_congr_ae
  filter_upwards [correctionCellLaw_support k i] with z hz
  rw [hc z x (hz.2.trans hx.symm)]

/-- An integrable scalar times a cellwise constant vector is integrable on the design. -/
-- @node: integrable_smul_cellwise_vector
lemma integrable_smul_cellwise_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (hk : 0 < k) (g : ℝ → ℝ) (c : ℝ → E)
    (hg : Integrable g unitVolume)
    (hc : ∀ x z, cell k x = cell k z → c x = c z) :
    Integrable (fun x => g x • c x) unitVolume := by
  have hi : ∀ i : Fin k, IntegrableOn (fun x => g x • c x)
      (histogramCell k (i.val + 1)) unitVolume := by
    intro i
    apply (hg.integrableOn.smul_const (c (midpoint k i))).congr
    filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
    rw [hc (midpoint k i) x ((cell_midpoint_self k i).trans hx.2.symm)]
  have h := integrableOn_finite_iUnion.mpr hi
  rw [histogramCells_cover k hk] at h
  simpa only [IntegrableOn, unitVolume, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_self] using h

/-- Three independent design roles give the squared scalar cell mean times the vector mean. -/
-- @node: integral_triple_design_kernel
lemma integral_triple_design_kernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → E) (hg : Integrable g unitVolume) :
    (∫ x, ∫ y, ∫ z,
      (g x * covariateKernel k x y * g y * covariateKernel k y z) • f z
        ∂unitVolume ∂unitVolume ∂unitVolume) =
      ∫ y, (cellAverage k g y) ^ 2 • cellAverage k f y ∂unitVolume := by
  have hc : ∀ x z, cell k x = cell k z → cellAverage k f x = cellAverage k f z :=
    fun x z h => cellAverage_eq_of_cell_eq k f x z h
  have hi := integrable_smul_cellwise_vector k hk g (cellAverage k f) hg hc
  have he (x y : ℝ) : (∫ z,
      (g x * covariateKernel k x y * g y * covariateKernel k y z) • f z ∂unitVolume) =
      (g x * covariateKernel k x y) • (g y • cellAverage k f y) := by
    simp only [mul_smul, cellAverage]
    rw [integral_smul, integral_smul, integral_smul]
  simp_rw [he]
  rw [integral_pair_design_kernel k hk g (fun y => g y • cellAverage k f y) hg hi]
  simp_rw [cellAverage_smul_cellwise_vector k hk g (cellAverage k f) hc, smul_smul,
    ← pow_two]

/-- Jointly integrable outcome functions have integrable coefficient vectors over the design. -/
-- @node: integrable_coefficients_design
lemma integrable_coefficients_design (J : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) :
    Integrable (fun x => coefficients J (f x)) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi := (integrable_joint_weighted_phiCoefficients J f hf).integral_prod_left
  apply hi.congr
  filter_upwards [hf.prod_right_ae] with x hx
  exact integral_weighted_phiCoefficients J (f x) hx

/-- The second-order design kernel for pilot errors has exactly the cell-product mean in (21). -/
-- @node: second_role_design_mean
lemma second_role_design_mean {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J k : ℕ) (hk : 0 < k) (a : Bool) :
    (∫ x, ∫ z, (uerr P train mx a x * covariateKernel k x z) •
      coefficients J (verr P train mx my a z) ∂unitVolume ∂unitVolume) =
    ∫ z, cellAverage k (uerr P train mx a) z •
      cellAverage k (fun x => coefficients J (verr P train mx my a x)) z ∂unitVolume := by
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  exact integral_pair_design_kernel k hk _ _
    (integrable_uerr_covariate P hModel train mx a) (integrable_coefficients_design J _ hv)

/-- The third-order design kernel for pilot errors gives the squared-cell-mean product in (21). -/
-- @node: third_role_design_mean
lemma third_role_design_mean {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J q : ℕ) (hq : 0 < q) (a : Bool) :
    (∫ x, ∫ z, ∫ w,
      (uerr P train mx a x * covariateKernel q x z * uerr P train mx a z *
        covariateKernel q z w) • coefficients J (verr P train mx my a w)
        ∂unitVolume ∂unitVolume ∂unitVolume) =
    ∫ z, (cellAverage q (uerr P train mx a) z) ^ 2 •
      cellAverage q (fun x => coefficients J (verr P train mx my a x)) z ∂unitVolume := by
  exact integral_triple_design_kernel q hq _ _ (integrable_uerr_covariate P hModel train mx a)

end CausalSmith.Stat.DensityEffectRoughNull
