module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellAverages

/-! The exact integrated cell-centering identity (25) for the uniform design partition. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Integrability on all cells gives integrability on the whole uniform design domain. -/
-- @node: integrable_of_histogramCells
lemma integrable_of_histogramCells (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ)
    (hf : ∀ i : Fin k, IntegrableOn f (histogramCell k (i.val + 1)) unitVolume) :
    Integrable f unitVolume := by
  have h := integrableOn_finite_iUnion.mpr hf
  rw [histogramCells_cover k hk] at h
  simpa only [IntegrableOn, unitVolume, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_self] using h

/-- A cell average is constant on each cell and hence integrable at every positive rank. -/
-- @node: integrable_cellAverage
lemma integrable_cellAverage (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ) :
    Integrable (cellAverage k f) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply integrable_of_histogramCells k hk
  intro i
  apply (integrable_const (∫ z, f z ∂correctionCellLaw k i)).congr
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  exact (cellAverage_eq_correctionCellLaw k i f x hx.2).symm

/-- The product of two cell averages is integrable, since both are cellwise constant. -/
-- @node: integrable_cellAverage_mul
lemma integrable_cellAverage_mul (k : ℕ) (hk : 0 < k) (g r : ℝ → ℝ) :
    Integrable (fun x => cellAverage k g x * cellAverage k r x) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply integrable_of_histogramCells k hk
  intro i
  apply (integrable_const ((∫ z, g z ∂correctionCellLaw k i) *
    (∫ z, r z ∂correctionCellLaw k i))).congr
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  rw [cellAverage_eq_correctionCellLaw k i g x hx.2,
    cellAverage_eq_correctionCellLaw k i r x hx.2]

/-- Centering integrable factors by their own cell means preserves product integrability. -/
-- @node: integrable_cell_centered_mul
lemma integrable_cell_centered_mul (k : ℕ) (hk : 0 < k) (g r : ℝ → ℝ)
    (hg : Integrable g unitVolume) (hr : Integrable r unitVolume)
    (hgr : Integrable (fun x => g x * r x) unitVolume) :
    Integrable (fun x => (g x - cellAverage k g x) * (r x - cellAverage k r x))
      unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply integrable_of_histogramCells k hk
  intro i
  let G := ∫ z, g z ∂correctionCellLaw k i
  let R := ∫ z, r z ∂correctionCellLaw k i
  have hi : IntegrableOn (fun x => g x * r x - g x * R - G * r x + G * R)
      (histogramCell k (i.val + 1)) unitVolume :=
    ((hgr.integrableOn.sub (hg.integrableOn.mul_const R)).sub
      (hr.integrableOn.const_mul G)).add (integrable_const _)
  apply hi.congr
  filter_upwards [ae_restrict_mem (measurableSet_histogramCell k (i.val + 1))] with x hx
  rw [cellAverage_eq_correctionCellLaw k i g x hx.2,
    cellAverage_eq_correctionCellLaw k i r x hx.2]
  dsimp [G, R]
  ring

/-- The concrete kernel average of the centered product is the cell covariance. -/
-- @node: cellAverage_covariance_centered_identity
lemma cellAverage_covariance_centered_identity (k : ℕ) (hk : 0 < k) (g r : ℝ → ℝ)
    (hg : Integrable g unitVolume) (hr : Integrable r unitVolume)
    (hgr : Integrable (fun x => g x * r x) unitVolume) (x : ℝ) :
    cellAverage k (fun z => g z * r z) x - cellAverage k g x * cellAverage k r x =
      cellAverage k (fun z => (g z - cellAverage k g z) * (r z - cellAverage k r z)) x := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hc : cell k x = i.val + 1 := by dsimp [i]; omega
  let := correctionCellLaw_probability k hk i
  rw [cellAverage_eq_correctionCellLaw k i _ x hc,
    cellAverage_eq_correctionCellLaw k i g x hc,
    cellAverage_eq_correctionCellLaw k i r x hc,
    cellAverage_eq_correctionCellLaw k i _ x hc]
  have h := cell_covariance_centered_identity (correctionCellLaw k i) g r
    (integrable_correctionCellLaw k i g hg) (integrable_correctionCellLaw k i r hr)
    (by simpa only [smul_eq_mul] using integrable_correctionCellLaw k i _ hgr)
  rw [show (∫ z, g z * r z ∂correctionCellLaw k i) -
      (∫ z, g z ∂correctionCellLaw k i) * (∫ z, r z ∂correctionCellLaw k i) =
      ∫ z, (g z - ∫ w, g w ∂correctionCellLaw k i) *
        (r z - ∫ w, r w ∂correctionCellLaw k i) ∂correctionCellLaw k i by
    simpa only [smul_eq_mul] using h]
  apply integral_congr_ae
  filter_upwards [correctionCellLaw_support k i] with z hz
  rw [cellAverage_eq_correctionCellLaw k i g z hz.2,
    cellAverage_eq_correctionCellLaw k i r z hz.2]

/-- Integrating cell covariances gives exactly the centered-product identity (25). -/
-- @node: integrated_cell_covariance_centered_identity
lemma integrated_cell_covariance_centered_identity (k : ℕ) (hk : 0 < k) (g r : ℝ → ℝ)
    (hg : Integrable g unitVolume) (hr : Integrable r unitVolume)
    (hgr : Integrable (fun x => g x * r x) unitVolume) :
    (∫ x, g x * r x - cellAverage k g x * cellAverage k r x ∂unitVolume) =
      ∫ x, (g x - cellAverage k g x) * (r x - cellAverage k r x) ∂unitVolume := by
  rw [integral_sub hgr (integrable_cellAverage_mul k hk g r),
    ← integral_cellAverage k hk _ hgr,
    ← integral_sub (integrable_cellAverage k hk _) (integrable_cellAverage_mul k hk g r)]
  simp_rw [cellAverage_covariance_centered_identity k hk g r hg hr hgr]
  exact integral_cellAverage k hk _ (integrable_cell_centered_mul k hk g r hg hr hgr)

end CausalSmith.Stat.DensityEffectRoughNull
