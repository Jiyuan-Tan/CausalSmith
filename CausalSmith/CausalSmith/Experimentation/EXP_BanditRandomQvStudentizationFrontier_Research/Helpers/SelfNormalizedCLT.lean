/- Paper-owned early-measurable self-normalized martingale CLTs. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.MartingaleCLT

/-! # Early-scale self-normalized martingale limits -/

open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def arraySum {Ω I : Type*} (N : ℕ → ℕ) (X : ℕ → I → ℕ → Ω → ℝ) : ℕ → I → Ω → ℝ :=
  fun n i ω => ∑ t ∈ Finset.Icc 1 (N n), X n i t ω

def arrayQV {Ω I : Type*} (N : ℕ → ℕ) (X : ℕ → I → ℕ → Ω → ℝ) : ℕ → I → Ω → ℝ :=
  fun n i ω => ∑ t ∈ Finset.Icc 1 (N n), (X n i t ω) ^ 2

def arraySuffixPredictableQV {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (G : ℕ → I → Filtration ℕ ‹MeasurableSpace Ω›)
    (N h : ℕ → ℕ) (X : ℕ → I → ℕ → Ω → ℝ) : ℕ → I → Ω → ℝ :=
  fun n i ω => ∑ t ∈ Finset.Icc (h n + 1) (N n),
    (μ n i)[(fun ω' => (X n i t ω') ^ 2) | G n i (t - 1)] ω

def UniformInProbability {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (X Y : ℕ → I → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop, ∀ i,
    (μ n i {ω | ε < |X n i ω - Y n i ω|}).toReal ≤ δ

def UniformEventCertain {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (A : ℕ → I → Set Ω) : Prop :=
  ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, 1 - δ ≤ (μ n i (A n i)).toReal

-- @node: lem:early-measurable-scale-self-normalized-martingale-clt
lemma early_measurable_scale_self_normalized_martingale_clt
    {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (G : ℕ → I → Filtration ℕ ‹MeasurableSpace Ω›)
    (N h : ℕ → ℕ) (X : ℕ → I → ℕ → Ω → ℝ)
    (lambda : ℕ → I → Ω → ℝ) (nu : ℕ → ℝ) (L : ℝ)
    (hcut : ∀ n, h n < N n)
    (hmd : ∀ n i, martingaleDifference (μ n i) (G n i) (N n) (X n i))
    (hbounded : ∀ n i t, 1 ≤ t → t ≤ N n →
      ∀ᵐ ω ∂μ n i, |X n i t ω| ≤ L)
    (hmeas : ∀ n i, Measurable[G n i (h n)] (lambda n i))
    (hfloor : (∀ n, 0 < nu n) ∧
      ∀ n i, ∀ᵐ ω ∂μ n i, 0 < lambda n i ω ∧ nu n ≤ lambda n i ω)
    (hgrowth : Tendsto (fun n => (N n : ℝ) * nu n) atTop atTop)
    (hprefix : Tendsto (fun n => (h n : ℝ) / ((N n : ℝ) * nu n)) atTop (𝓝 0))
    (hstabilizes : UniformInProbability μ
      (fun n i ω => arraySuffixPredictableQV μ G N h X n i ω /
        ((N n : ℝ) * lambda n i ω)) (fun _ _ _ => 1)) :
    UniformInProbability μ
      (fun n i ω => arrayQV N X n i ω / ((N n : ℝ) * lambda n i ω))
      (fun _ _ _ => 1) ∧
    UniformEventCertain μ (fun n i => {ω | 0 < arrayQV N X n i ω}) ∧
    UniformCDFConverges μ
      (fun n i ω => if arrayQV N X n i ω = 0 then 0 else
        arraySum N X n i ω / Real.sqrt (arrayQV N X n i ω))
      Causalean.Mathlib.stdNormalCDF := by sorry

-- @node: lem:early-measurable-l4-self-normalized-martingale-clt
lemma early_measurable_l4_self_normalized_martingale_clt
    {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (G : ℕ → I → Filtration ℕ ‹MeasurableSpace Ω›)
    (N h : ℕ → ℕ) (X : ℕ → I → ℕ → Ω → ℝ)
    (lambda : ℕ → I → Ω → ℝ) (C4 lambdaMin : ℝ)
    (hN : Tendsto N atTop atTop)
    (hprefix : Tendsto (fun n => (h n : ℝ) / N n) atTop (𝓝 0))
    (hcut : ∀ n, h n < N n)
    (hmd : ∀ n i, martingaleDifference (μ n i) (G n i) (N n) (X n i))
    (hfourth_integrable : ∀ n i t, 1 ≤ t → t ≤ N n →
      Integrable (fun ω => |X n i t ω| ^ 4) (μ n i))
    (hfourth : ∀ n i t, 1 ≤ t → t ≤ N n →
      ∫ ω, |X n i t ω| ^ 4 ∂μ n i ≤ C4)
    (hmeas : ∀ n i, Measurable[G n i (h n)] (lambda n i))
    (hfloor : 0 < lambdaMin ∧ ∀ n i, ∀ᵐ ω ∂μ n i,
      0 < lambda n i ω ∧ lambdaMin ≤ lambda n i ω)
    (hstabilizes : UniformInProbability μ
      (fun n i ω => arraySuffixPredictableQV μ G N h X n i ω /
        ((N n : ℝ) * lambda n i ω)) (fun _ _ _ => 1)) :
    UniformInProbability μ
      (fun n i ω => arrayQV N X n i ω / ((N n : ℝ) * lambda n i ω))
      (fun _ _ _ => 1) ∧
    UniformEventCertain μ (fun n i => {ω | 0 < arrayQV N X n i ω}) ∧
    UniformCDFConverges μ
      (fun n i ω => if arrayQV N X n i ω = 0 then 0 else
        arraySum N X n i ω / Real.sqrt (arrayQV N X n i ω))
      Causalean.Mathlib.stdNormalCDF := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
