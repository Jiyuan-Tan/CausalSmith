module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ProjectionMeans

/-! Projection commutes with correction-cell averaging in the role-mean identities (21).
Joint integrability is derived from the bounded correction kernel. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Histogram coefficients preserve scalar multiplication, including nonintegrable inputs. -/
-- @node: coefficients_const_mul
lemma coefficients_const_mul (J : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    coefficients J (fun y => c * f y) = c • coefficients J f := by
  ext i
  change Real.sqrt J * (∫ y in histogramCell J (i.val + 1), c * f y ∂unitVolume) =
    c * (Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y ∂unitVolume))
  rw [integral_const_mul]
  ring

/-- Multiplication by a fixed correction kernel preserves joint integrability. -/
-- @node: integrable_covariateKernel_mul_joint
lemma integrable_covariateKernel_mul_joint (k : ℕ) (x : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) :
    Integrable (fun z : ℝ × ℝ => covariateKernel k x z.1 * f z.1 z.2)
      (unitVolume.prod unitVolume) := by
  have hm : Measurable (fun z : ℝ × ℝ => covariateKernel k x z.1) := by fun_prop
  have hb : ∀ᵐ z ∂unitVolume.prod unitVolume, ‖covariateKernel k x z.1‖ ≤ k := by
    filter_upwards [] with z
    unfold covariateKernel
    split_ifs <;> simp
  simpa only [Function.uncurry, mul_comm] using hf.mul_bdd hm.aestronglyMeasurable hb

/-- Outcome projection commutes with averaging on each correction cell. -/
-- @node: cellAverage_coefficients_eq
lemma cellAverage_coefficients_eq (k J : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) (x : ℝ) :
    cellAverage k (fun z => coefficients J (f z)) x =
      coefficients J (fun y => cellAverage k (fun z => f z y) x) := by
  unfold cellAverage
  simp_rw [← coefficients_const_mul]
  exact integral_coefficients_eq_coefficients_integral J
    (fun z y => covariateKernel k x z * f z y)
    (integrable_covariateKernel_mul_joint k x f hf)

/-- Kernel averages agree at covariates with the same correction-cell label. -/
-- @node: cellAverage_eq_of_cell_eq
lemma cellAverage_eq_of_cell_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : ℝ → E) (x z : ℝ) (hxz : cell k x = cell k z) :
    cellAverage k f x = cellAverage k f z := by
  simp only [cellAverage, covariateKernel, hxz]

/-- Every cell-mean product needed in (21) is jointly integrable by the finite cell partition. -/
-- @node: integrable_cellAverage_pow_mul_joint
lemma integrable_cellAverage_pow_mul_joint (k : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (cellAverage k g z.1) ^ n *
      cellAverage k (fun x => f x z.2) z.1) (unitVolume.prod unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let F (i : Fin k) (z : ℝ × ℝ) : ℝ :=
    (histogramCell k (i.val + 1)).indicator (fun _ => (1 : ℝ)) z.1 *
      ((cellAverage k g (midpoint k i)) ^ n *
        cellAverage k (fun x => f x z.2) (midpoint k i))
  have hi (i : Fin k) : Integrable (F i) (unitVolume.prod unitVolume) := by
    have hout : Integrable (fun y => cellAverage k (fun x => f x y) (midpoint k i))
        unitVolume := by
      exact (integrable_covariateKernel_mul_joint k (midpoint k i) f hf).integral_prod_right
    exact ((integrable_const (1 : ℝ)).indicator
      (measurableSet_histogramCell k (i.val + 1))).mul_prod (hout.const_mul _)
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
  have hx : ∀ᵐ z ∂unitVolume.prod unitVolume, z.1 ∈ Set.Icc 0 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod MeasurableSet.univ)).2 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact Filter.Eventually.of_forall (fun _ => ⟨hx, Set.mem_univ _⟩)) |>.mono (fun _ h => h.1)
  filter_upwards [hx] with z hz
  have hlabel := cell_index_mem k hk z.1
  let i : Fin k := ⟨cell k z.1 - 1, by omega⟩
  have hc : cell k z.1 = i.val + 1 := by dsimp [i]; omega
  rw [Finset.sum_eq_single i]
  · have hmem : z.1 ∈ histogramCell k (i.val + 1) := ⟨hz, hc⟩
    dsimp [F]
    rw [Set.indicator_of_mem hmem, one_mul,
      cellAverage_eq_of_cell_eq k g (midpoint k i) z.1 ((cell_midpoint_self k i).trans hc.symm),
      cellAverage_eq_of_cell_eq k (fun x => f x z.2) (midpoint k i) z.1
        ((cell_midpoint_self k i).trans hc.symm)]
  · intro j _ hji
    have hnot : z.1 ∉ histogramCell k (j.val + 1) := by
      intro hj
      apply hji
      apply Fin.ext
      have hjc := hj.2
      omega
    simp [F, Set.indicator_of_notMem hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

/-- The projected second- and third-role cell products equal projection of their scalar means. -/
-- @node: integral_cellAverage_pow_smul_coefficients
lemma integral_cellAverage_pow_smul_coefficients (k J : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) (n : ℕ) :
    (∫ x, (cellAverage k g x) ^ n •
      cellAverage k (fun z => coefficients J (f z)) x ∂unitVolume) =
    coefficients J (fun y => ∫ x, (cellAverage k g x) ^ n *
      cellAverage k (fun z => f z y) x ∂unitVolume) := by
  simp_rw [cellAverage_coefficients_eq k J f hf, ← coefficients_const_mul]
  exact integral_coefficients_eq_coefficients_integral J _
    (integrable_cellAverage_pow_mul_joint k hk g f hf n)

/-- Projecting an integrated correction remainder gives the difference of its two role means. -/
-- @node: coefficients_integrated_cell_remainder
lemma coefficients_integrated_cell_remainder (k J : ℕ) (hk : 0 < k)
    (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) (n : ℕ)
    (hgf : Integrable (fun z : ℝ × ℝ => (g z.1) ^ n * f z.1 z.2)
      (unitVolume.prod unitVolume)) :
    coefficients J (fun y => ∫ x, (g x) ^ n * f x y -
      (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x ∂unitVolume) =
    (∫ x, coefficients J (fun y => (g x) ^ n * f x y) ∂unitVolume) -
      (∫ x, (cellAverage k g x) ^ n •
        cellAverage k (fun z => coefficients J (f z)) x ∂unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hav := integrable_cellAverage_pow_mul_joint k hk g f hf n
  rw [integral_coefficients_eq_coefficients_integral J (fun x y => (g x) ^ n * f x y) hgf,
    integral_cellAverage_pow_smul_coefficients k J hk g f hf n]
  have hcongr : (fun y => ∫ x, (g x) ^ n * f x y -
      (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x ∂unitVolume) =ᵐ[unitVolume]
      (fun y => (∫ x, (g x) ^ n * f x y ∂unitVolume) -
        ∫ x, (cellAverage k g x) ^ n * cellAverage k (fun z => f z y) x ∂unitVolume) := by
    filter_upwards [hgf.prod_left_ae, hav.prod_left_ae] with y hy hay
    exact integral_sub hy hay
  rw [coefficients_congr_ae J _ _ hcongr]
  simpa only [one_mul, one_smul] using coefficients_const_mul_sub J 1 _ _
    hgf.integral_prod_right hav.integral_prod_right

end CausalSmith.Stat.DensityEffectRoughNull
