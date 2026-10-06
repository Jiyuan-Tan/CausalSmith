module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedDomination
public import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Seeded empirical-average moments

The IID second-moment calculation in FC.5 is unchanged by appending the
independent procedure seed. The remaining population calculations concern a
single observed summand, rather than the full sample experiment.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- An IID empirical average retains its mean and centered second-moment bound
when an independent probability seed is appended, as required in FC.5. Given [the displayed inputs and assumptions](hyp:Ω,T,μ,ν,n,hn,F,hF,V,hV), [the stated mathematical conclusion holds](goal). -/
lemma seeded_iid_centered_moments {Ω T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace T] (μ : Measure Ω) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) (V : ℝ)
    (hV : (∫ o, (F o)^2 ∂μ) ≤ V) :
    let Z := fun z : (Fin n → Ω) × T =>
      (n : ℝ)⁻¹ * ∑ i, F (z.1 i) - ∫ o, F o ∂μ
    let Q := (Measure.pi fun _ : Fin n => μ).prod ν
    MemLp Z 2 Q ∧ (∫ z, Z z ∂Q) = 0 ∧ (∫ z, (Z z)^2 ∂Q) ≤ V / n := by
  let S := Measure.pi fun _ : Fin n => μ
  let A := fun s : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i, F (s i)
  have hA : MemLp A 2 S := by
    exact (memLp_finset_sum Finset.univ (fun i _ =>
      hF.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))).const_mul _
  have hZ : MemLp (fun s => A s - ∫ o, F o ∂μ) 2 S := hA.sub (memLp_const _)
  have hf : MeasurePreserving Prod.fst (S.prod ν) S := measurePreserving_fst
  have hm : (∫ s, A s ∂S) = ∫ o, F o ∂μ :=
    Causalean.Mathlib.Probability.iid_average_integral μ n hn F (hF.integrable (by norm_num))
  refine ⟨hZ.comp_measurePreserving hf, ?_, ?_⟩
  · change (∫ z, ((fun s => A s - ∫ o, F o ∂μ) ∘ Prod.fst) z ∂S.prod ν) = 0
    rw [integral_prod _ ((hZ.comp_measurePreserving hf).integrable (by norm_num))]
    dsimp only [Function.comp_def]
    simp only [integral_const, probReal_univ, one_smul]
    rw [integral_sub
      (hA.integrable (by norm_num)) (integrable_const _), hm]
    simp
  · change (∫ z, (((fun s => A s - ∫ o, F o ∂μ) ∘ Prod.fst) z)^2 ∂S.prod ν) ≤ V / n
    rw [integral_prod _ (hZ.comp_measurePreserving hf).integrable_sq]
    dsimp only [Function.comp_def]
    simp only [integral_const, probReal_univ, one_smul]
    exact (Causalean.Mathlib.Probability.iid_mean_sq_le μ hn F hF).trans
      (div_le_div_of_nonneg_right hV (by positivity))

/-- The observed law is normalized independently of the noise scale. Given [the displayed inputs and assumptions](hyp:P,σ), [the stated mathematical conclusion holds](goal). -/
lemma empirical_Pobs_probability (P : LatentLaw) (σ : ℝ) :
    IsProbabilityMeasure (Pobs P σ) := by
  letI := P.prob
  exact Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable

/-- The expectation of a seeded IID average is its single-observation mean. Given [the displayed inputs and assumptions](hyp:Ω,T,μ,ν,n,hn,F,hF), [the stated mathematical conclusion holds](goal). -/
lemma seeded_iid_average_integral {Ω T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace T] (μ : Measure Ω) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n)
    (F : Ω → ℝ) (hF : Integrable F μ) :
    (∫ z : (Fin n → Ω) × T, (n : ℝ)⁻¹ * ∑ i, F (z.1 i)
      ∂(Measure.pi fun _ : Fin n => μ).prod ν) = ∫ o, F o ∂μ := by
  have hA : Integrable (fun s : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i, F (s i))
      (Measure.pi fun _ : Fin n => μ) :=
    (integrable_finset_sum Finset.univ (fun i _ =>
      (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hF)).const_mul _
  have hi := (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => μ) (ν := ν)).integrable_comp_of_integrable hA
  change (∫ z, ((fun s : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i, F (s i)) ∘ Prod.fst) z
    ∂(Measure.pi fun _ : Fin n => μ).prod ν) = _
  rw [integral_prod _ hi]
  dsimp only [Function.comp_def]
  simp only [integral_const, probReal_univ, one_smul]
  exact Causalean.Mathlib.Probability.iid_average_integral μ n hn F hF

/-- The population denominator expectation reduces to one observed weight. Given [the displayed inputs and assumptions](hyp:P,σ,n,L,d,hn,hF), [the stated mathematical conclusion holds](goal). -/
lemma unmarkedMean_eq_single_observation (P : LatentLaw) (σ : ℝ)
    (n L : ℕ) (d : Bool) (hn : 0 < n)
    (hF : Integrable (fun o : Obs => (if o.2.1 = d then 1 else 0) *
      (inverseHeat L σ).eval (sgn d * o.1)) (Pobs P σ)) :
    unmarkedMean d L σ P n = ∫ o : Obs, (if o.2.1 = d then 1 else 0) *
      (inverseHeat L σ).eval (sgn d * o.1) ∂Pobs P σ := by
  letI := empirical_Pobs_probability P σ
  haveI : IsProbabilityMeasure seedLaw := by unfold seedLaw; infer_instance
  exact seeded_iid_average_integral (Pobs P σ) seedLaw n hn _ hF

/-- Single-observation marked moments suffice for all centered marked-average
moments under the actual seeded experiment; no sample-level bound is assumed. Given [the displayed inputs and assumptions](hyp:P,σ,n,L,d,hn,hF,hV), [the stated mathematical conclusion holds](goal). -/
lemma markedAvg_centered_moments_of_single_observation
    (P : LatentLaw) (σ : ℝ) (n L : ℕ) (d : Bool) (hn : 0 < n)
    (hF : MemLp (fun o : Obs => (if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat L σ).eval (sgn d * o.1)) 2 (Pobs P σ))
    (hV : (∫ o : Obs, ((if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat L σ).eval (sgn d * o.1))^2 ∂Pobs P σ) ≤ kernelVariance L σ) :
    let A := ∫ o : Obs, (if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat L σ).eval (sgn d * o.1) ∂Pobs P σ
    MemLp (fun z : Input n => markedAvg d L σ z.1 - A) 2 (experiment P σ n) ∧
    (∫ z : Input n, markedAvg d L σ z.1 - A ∂experiment P σ n) = 0 ∧
    (∫ z : Input n, (markedAvg d L σ z.1 - A)^2 ∂experiment P σ n) ≤
      kernelVariance L σ / n := by
  letI := empirical_Pobs_probability P σ
  haveI : IsProbabilityMeasure seedLaw := by unfold seedLaw; infer_instance
  exact seeded_iid_centered_moments (Pobs P σ) seedLaw n hn _ hF _ hV

/-- Single-observation unmarked moments suffice for all centered denominator
moments under the actual seeded experiment. Given [the displayed inputs and assumptions](hyp:P,σ,n,L,d,hn,hF,hV), [the stated mathematical conclusion holds](goal). -/
lemma unmarkedAvg_centered_moments_of_single_observation
    (P : LatentLaw) (σ : ℝ) (n L : ℕ) (d : Bool) (hn : 0 < n)
    (hF : MemLp (fun o : Obs => (if o.2.1 = d then 1 else 0) *
      (inverseHeat L σ).eval (sgn d * o.1)) 2 (Pobs P σ))
    (hV : (∫ o : Obs, ((if o.2.1 = d then 1 else 0) *
      (inverseHeat L σ).eval (sgn d * o.1))^2 ∂Pobs P σ) ≤ kernelVariance L σ) :
    let B := ∫ o : Obs, (if o.2.1 = d then 1 else 0) *
      (inverseHeat L σ).eval (sgn d * o.1) ∂Pobs P σ
    MemLp (fun z : Input n => unmarkedAvg d L σ z.1 - B) 2 (experiment P σ n) ∧
    (∫ z : Input n, unmarkedAvg d L σ z.1 - B ∂experiment P σ n) = 0 ∧
    (∫ z : Input n, (unmarkedAvg d L σ z.1 - B)^2 ∂experiment P σ n) ≤
      kernelVariance L σ / n := by
  letI := empirical_Pobs_probability P σ
  haveI : IsProbabilityMeasure seedLaw := by unfold seedLaw; infer_instance
  exact seeded_iid_centered_moments (Pobs P σ) seedLaw n hn _ hF _ hV

end CausalSmith.Stat.RdTruesideNoiseFrontier
