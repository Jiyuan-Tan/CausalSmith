module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Model
public import Mathlib.Probability.Moments.Basic

/-! # Finite conditional sub-Gaussian sums -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory

/-- Independent centred residuals with coordinatewise Gaussian MGF bounds
retain the sum of their variance proxies under a finite weighted sum. [For the stated inputs and conditions](hyp:Ω,n,μ,Z,v,hindep,hmeas,hmgf,t), [the asserted conclusion holds](goal). -/
lemma independentResidualSum_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin n → Ω → ℝ) (v : Fin n → ℝ)
    (hindep : iIndepFun Z μ) (hmeas : ∀ i, Measurable (Z i))
    (hmgf : ∀ i t, mgf (Z i) μ t ≤ Real.exp (v i * t ^ 2 / 2))
    (t : ℝ) :
    mgf (∑ i : Fin n, Z i) μ t ≤
      Real.exp ((∑ i : Fin n, v i) * t ^ 2 / 2) := by
  rw [hindep.mgf_sum hmeas Finset.univ]
  calc
    (∏ i : Fin n, mgf (Z i) μ t) ≤
        ∏ i : Fin n, Real.exp (v i * t ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        exact hmgf i t
    _ = Real.exp ((∑ i : Fin n, v i) * t ^ 2 / 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_mul, Finset.sum_div]

/-- Fixed design weights turn a common residual proxy into the squared-weight
proxy used by the selected coefficient bounds. [For the stated inputs and conditions](hyp:Ω,n,μ,Y,w,B,hindep,hmeas,hmgf,t), [the asserted conclusion holds](goal). -/
lemma independentWeightedResidual_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ) (w : Fin n → ℝ) (B : ℝ)
    (hindep : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hmgf : ∀ i t, mgf (Y i) μ t ≤ Real.exp (B ^ 2 * t ^ 2 / 2))
    (t : ℝ) :
    mgf (∑ i : Fin n, fun ω => w i * Y i ω) μ t ≤
      Real.exp (B ^ 2 * (∑ i : Fin n, (w i) ^ 2) * t ^ 2 / 2) := by
  have hi : iIndepFun (fun i ω => w i * Y i ω) μ := by
    simpa only [Function.comp_def] using
      hindep.comp (fun i x => w i * x) (by fun_prop)
  have hm : ∀ i, Measurable (fun ω => w i * Y i ω) := by fun_prop
  have hb : ∀ i s, mgf (fun ω => w i * Y i ω) μ s ≤
      Real.exp ((B ^ 2 * w i ^ 2) * s ^ 2 / 2) := by
    intro i s
    rw [mgf_const_mul]
    convert hmgf i (w i * s) using 1 <;> ring
  have h := independentResidualSum_mgf_le μ (fun i ω => w i * Y i ω)
    (fun i => B ^ 2 * w i ^ 2) hi hm hb t
  have hs : (∑ i : Fin n, B ^ 2 * w i ^ 2) =
      B ^ 2 * ∑ i : Fin n, w i ^ 2 := by rw [Finset.mul_sum]
  rw [hs] at h
  exact h

/-- Exponential integrability is preserved under the same finite weighted
sum, so the maximal inequality can use the coefficient MGF bounds. [For the stated inputs and conditions](hyp:Ω,n,μ,Y,w,hindep,hmeas,hint,t), [the asserted conclusion holds](goal). -/
lemma independentWeightedResidual_integrable_exp_sum
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ) (w : Fin n → ℝ)
    (hindep : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i t, Integrable (fun ω => Real.exp (t * Y i ω)) μ)
    (t : ℝ) :
    Integrable (fun ω => Real.exp
      (t * (∑ i : Fin n, (fun ξ => w i * Y i ξ)) ω)) μ := by
  have hi : iIndepFun (fun i ω => w i * Y i ω) μ := by
    simpa only [Function.comp_def] using
      hindep.comp (fun i x => w i * x) (by fun_prop)
  have hm : ∀ i, Measurable (fun ω => w i * Y i ω) := by fun_prop
  apply hi.integrable_exp_mul_sum hm
  intro i _
  convert hint i (t * w i) using 1
  ext ω
  congr 1
  ring

end CausalSmith.Stat.WeakOverlap
