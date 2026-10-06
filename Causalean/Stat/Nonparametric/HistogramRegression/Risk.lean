module
public import Causalean.Stat.Nonparametric.HistogramRegression.Centered
public import Causalean.Stat.Nonparametric.HistogramRegression.IIDTransfer
public import Causalean.Stat.Nonparametric.HistogramRegression.PartitionTotals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.IdentDistribIndep

/-!
# Integrated finite-partition histogram risk

The universal bound is twice the mass-weighted squared oscillation plus six
times the number of positive-mass cells divided by `m+1`. Sampling may be
presented either as the canonical iid product law or as an independent family
on an arbitrary probability space with a common observation law. No density,
positive lower cell mass, or nonempty-sample premise is required.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [A measurable finite partition and regression inputs](hyp:hlabel,hX,hY,hg),
[bounded responses and default](hyp:hbound,ha), [the population conditional
mean identity](hyp:hmean), and [within-cell oscillation bounds](hyp:hδ,hosc)
imply [expected integrated squared histogram error is bounded by twice the
mass-weighted squared oscillation plus six times the positive-cell count
divided by the sample-size successor](goal). -/
theorem histogram_risk_le {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (g : A → ℝ) (a : ℝ) (δ : κ → ℝ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hg : Measurable g) (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hmean : ConditionalMean μ X Y g)
    (hδ : ∀ k, 0 ≤ δ k)
    (hosc : ∀ k x x', label x = k → label x' = k → |g x - g x'| ≤ δ k) :
    risk μ (Measure.pi (fun _ : Fin m => μ)) label X Y a g ≤
      2 * (∑ k ∈ positiveCells μ label X, cellMass μ label X k * δ k ^ 2) +
        6 * ((positiveCells μ label X).card : ℝ) / (m + 1 : ℝ) := by
  let ν := Measure.pi (fun _ : Fin m => μ)
  let c := cellMean μ label X Y
  let p := cellMass μ label X
  let K := positiveCells μ label X
  let L := fun (z : Fin m → Ω) (ω : Ω) =>
    (histogram label X Y a z (X ω) - g (X ω)) ^ 2
  -- Regression is bounded almost surely; clipping bounds every training tuple.
  have hb := regression_mem_Icc_ae μ X Y g hX hg hbound hmean
  have hc (k : κ) : c k ∈ Set.Icc (0 : ℝ) 1 :=
    cellMean_mem_Icc μ label X Y k hlabel hX hY hbound
  have he (k : κ) (z : Fin m → Ω) :
      cellEstimate label X Y a k z ∈ Set.Icc (0 : ℝ) 1 := by
    unfold cellEstimate
    split_ifs
    · exact ha
    · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hsq (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
      (hv : v ∈ Set.Icc (0 : ℝ) 1) : (u - v) ^ 2 ≤ 1 := by
    simpa using (sq_le_sq' (by linarith [hu.1, hv.2])
      (by linarith [hu.2, hv.1]) : (u - v) ^ 2 ≤ (1 : ℝ) ^ 2)
  have hLm : Measurable (Function.uncurry L) := by
    exact (((measurable_histogram label X Y a hlabel hX hY).comp
      (measurable_fst.prodMk (hX.comp measurable_snd))).sub
      (hg.comp (hX.comp measurable_snd))).pow_const 2
  have hLi (z : Fin m → Ω) : Integrable (L z) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (hLm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq _ _ (he (label (X ω)) z) hω
  have hBi (k : κ) : Integrable (fun ω => (c k - g (X ω)) ^ 2) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.sub (hg.comp hX)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq _ _ (hc k) hω
  have hRi : Integrable (fun z => ∫ ω, L z ω ∂μ) ν := by
    refine (integrable_const (1 : ℝ)).mono'
      (hLm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)]
    have hh := integral_mono_ae (hLi z) (integrable_const (1 : ℝ))
      (hb.mono fun ω hω => hsq _ _ (he (label (X ω)) z) hω)
    simpa using hh
  have hEi (k : κ) : Integrable
      (fun z : Fin m → Ω => (cellEstimate label X Y a k z - c k) ^ 2) ν :=
    integrable_cellEstimate_sq_error μ label X Y a (c k) k hlabel hX hY ha (hc k)
  have hTi (k : κ) : Integrable (fun z : Fin m → Ω =>
      2 * p k * (cellEstimate label X Y a k z - c k) ^ 2 +
        2 * (p k * δ k ^ 2)) ν :=
    ((hEi k).const_mul _).add (integrable_const _)
  -- Split the fresh integral and bound each cell by estimation error plus bias.
  have hpoint (z : Fin m → Ω) : (∫ ω, L z ω ∂μ) ≤
      ∑ k ∈ K, (2 * p k * (cellEstimate label X Y a k z - c k) ^ 2 +
        2 * (p k * δ k ^ 2)) := by
    rw [integral_eq_sum_positive_cells μ label X (L z) hlabel hX (hLi z)]
    apply Finset.sum_le_sum
    intro k hk
    have hs : MeasurableSet (cell label X k) :=
      (measurableSet_singleton k).preimage (hlabel.comp hX)
    have hh := integral_mono_ae (hLi z).integrableOn
      (((integrable_const ((cellEstimate label X Y a k z - c k) ^ 2)).add
        (hBi k).integrableOn).const_mul 2)
      (ae_restrict_of_forall_mem hs (fun ω hω => by
        change label (X ω) = k at hω
        dsimp [L, histogram]
        rw [hω]
        convert (add_sq_le (a := cellEstimate label X Y a k z - c k)
          (b := c k - g (X ω))) using 1; ring))
    simp only [Pi.add_apply] at hh
    rw [integral_const_mul, integral_add (integrable_const _) (hBi k).integrableOn,
      integral_const] at hh
    have hbl := cell_bias_le μ label X Y g k (δ k) hlabel hX hg hbound hmean
      (hδ k) (hosc k)
    change (∫ ω in cell label X k, (c k - g (X ω)) ^ 2 ∂μ) ≤ p k * δ k ^ 2 at hbl
    calc
      _ ≤ 2 * (p k * (cellEstimate label X Y a k z - c k) ^ 2 +
          ∫ ω in cell label X k, (c k - g (X ω)) ^ 2 ∂μ) := by
        simpa [p, cellMass, Measure.real, smul_eq_mul] using hh
      _ ≤ 2 * (p k * (cellEstimate label X Y a k z - c k) ^ 2 +
          p k * δ k ^ 2) := mul_le_mul_of_nonneg_left (add_le_add_right hbl _) (by norm_num)
      _ = _ := by ring
  -- Integrate the finite sum and apply the mass-weighted cell MSE bound.
  have hi := integral_mono_ae hRi (integrable_finsetSum K (fun k _ => hTi k))
    (Filter.Eventually.of_forall hpoint)
  rw [integral_finsetSum K (fun k _ => hTi k)] at hi
  have hcell (k : κ) (hk : k ∈ K) :
      (∫ z : Fin m → Ω, 2 * p k * (cellEstimate label X Y a k z - c k) ^ 2 +
        2 * (p k * δ k ^ 2) ∂ν) ≤
      2 * (p k * δ k ^ 2) + 6 / (m + 1 : ℝ) := by
    rw [integral_add ((hEi k).const_mul _) (integrable_const _),
      integral_const_mul, integral_const]
    have hp : 0 < cellMass μ label X k := by
      simpa [K, positiveCells] using hk
    have hh := cell_estimation_mse_le (m := m) μ label X Y a k hlabel hX hY hbound ha hp
    change p k * (∫ z, (cellEstimate label X Y a k z - c k) ^ 2 ∂ν) ≤
      3 / (m + 1 : ℝ) at hh
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have hh2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = 2 * (p k * (∫ z, (cellEstimate label X Y a k z - c k) ^ 2 ∂ν)) +
          2 * (p k * δ k ^ 2) := by ring
      _ ≤ 2 * (3 / (m + 1 : ℝ)) + 2 * (p k * δ k ^ 2) :=
        add_le_add_left hh2 _
      _ = _ := by ring
  change (∫ z, (∫ ω, L z ω ∂μ) ∂ν) ≤ _
  calc
    _ ≤ ∑ k ∈ K, (∫ z : Fin m → Ω,
        2 * p k * (cellEstimate label X Y a k z - c k) ^ 2 +
          2 * (p k * δ k ^ 2) ∂ν) := hi
    _ ≤ ∑ k ∈ K, (2 * (p k * δ k ^ 2) + 6 / (m + 1 : ℝ)) :=
      Finset.sum_le_sum hcell
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      dsimp [K, p]
      ring

/-- [Measurable iid observation maps with common law](hyp:hZ,hind,hident),
[measurable regression inputs](hyp:hlabel,hX,hY,hg), [bounded responses and
default](hyp:hbound,ha), [the conditional-mean identity](hyp:hmean), and
[cellwise oscillation bounds](hyp:hδ,hosc) give [the same integrated histogram
risk bound on the original sample probability space](goal). -/
theorem histogram_risk_le_iid {m : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (Z : Fin m → S → Ω) (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (g : A → ℝ) (a : ℝ) (δ : κ → ℝ)
    (hZ : ∀ r, Measurable (Z r)) (hind : iIndepFun Z ν)
    (hident : ∀ r, IdentDistrib (Z r) id ν μ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hg : Measurable g) (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hmean : ConditionalMean μ X Y g)
    (hδ : ∀ k, 0 ≤ δ k)
    (hosc : ∀ k x x', label x = k → label x' = k → |g x - g x'| ≤ δ k) :
    (∫ s, (∫ ω, (histogram label X Y a (fun r => Z r s) (X ω) - g (X ω)) ^ 2 ∂μ) ∂ν) ≤
      2 * (∑ k ∈ positiveCells μ label X, cellMass μ label X k * δ k ^ 2) +
        6 * ((positiveCells μ label X).card : ℝ) / (m + 1 : ℝ) := by
  -- The measurable integrated loss has the same expectation under the iid
  -- observation maps and the canonical product law, including sample size zero.
  rw [integral_histogram_loss_eq_risk_iid μ ν Z label X Y g a
    hZ hind hident hlabel hX hY hg]
  exact histogram_risk_le μ label X Y g a δ hlabel hX hY hg hbound ha hmean hδ hosc

end

end Causalean.Stat.Nonparametric.HistogramRegression
