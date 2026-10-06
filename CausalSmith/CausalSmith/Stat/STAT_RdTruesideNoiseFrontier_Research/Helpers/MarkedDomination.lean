module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.WitnessModel

/-!
# Domination of the full marked witness laws

Interior Bernoulli probabilities bound the latent likelihood ratio. Measure
products and the observation map preserve this domination, providing absolute
continuity and square integrability on the entire observed space (ML.1–ML.2).
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Given the [noise scale](hyp:σ), the true-side assignment and Gaussian proxy form a [measurable observation map](goal). -/
@[fun_prop] lemma obs_measurable (σ : ℝ) : Measurable (obs σ) := by
  unfold obs proxy outcome side score errorCoord
  have hs : MeasurableSet {ω : Latent | 0 ≤ ω.1} :=
    measurableSet_le measurable_const measurable_fst
  have hd : Measurable (fun ω : Latent => decide (0 ≤ ω.1)) := by
    have he : (fun ω : Latent => decide (0 ≤ ω.1)) =
        fun ω => if 0 ≤ ω.1 then true else false := by
      funext ω
      by_cases h : 0 ≤ ω.1 <;> simp [h]
    rw [he]
    exact measurable_const.ite hs measurable_const
  exact (measurable_fst.add (measurable_const.mul measurable_snd.snd.snd)).prodMk
    (hd.prodMk (measurable_snd.snd.fst.ite (by simpa using hs) measurable_snd.fst))

/-- Interior success and failure weights dominate each other by a factor three. Given [the displayed inputs and assumptions](hyp:p,q,hp,hq), [the stated mathematical conclusion holds](goal). -/
lemma bernoulliBool_le_three (p q : ℝ)
    (hp : p ∈ Icc (1/4 : ℝ) (3/4)) (hq : q ∈ Icc (1/4 : ℝ) (3/4)) :
    Causalean.Mathlib.Probability.bernoulliBool p ≤
      (3 : ℝ≥0∞) • Causalean.Mathlib.Probability.bernoulliBool q := by
  have ht : ENNReal.ofReal p ≤ 3 * ENNReal.ofReal q := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hp.2, hq.1]
  have hf : ENNReal.ofReal (1-p) ≤ 3 * ENNReal.ofReal (1-q) := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hp.1, hq.2]
  unfold Causalean.Mathlib.Probability.bernoulliBool
  rw [smul_add, smul_smul, smul_smul]
  apply Measure.le_iff'.mpr
  intro s
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_left ht _) (mul_le_mul_left hf _)

/-- Fibrewise bounded domination survives a composition product. Given [the displayed inputs and assumptions](hyp:α,γ,μ,κ,η,h), [the stated mathematical conclusion holds](goal). -/
lemma compProd_le_three_of_fibres {α γ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ]
    (κ η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : ∀ x, κ x ≤ (3 : ℝ≥0∞) • η x) :
    μ ⊗ₘ κ ≤ (3 : ℝ≥0∞) • (μ ⊗ₘ η) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.compProd_apply hs, Measure.smul_apply, Measure.compProd_apply hs,
    smul_eq_mul, ← lintegral_const_mul' _ _ (by norm_num)]
  apply lintegral_mono
  intro x
  simpa only [Measure.smul_apply, smul_eq_mul] using h x (Prod.mk x ⁻¹' s)

/-- The full latent witness, including both potentials and the Gaussian, is dominated. Given [the displayed inputs and assumptions](hyp:p,q,hp,hq,hpb,hqb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_le_three (p q : ℝ → ℝ) (hp : Measurable p) (hq : Measurable q)
    (hpb : ∀ x, p x ∈ Icc (1/4 : ℝ) (3/4))
    (hqb : ∀ x, q x ∈ Icc (1/4 : ℝ) (3/4)) :
    witnessMeasure p ≤ (3 : ℝ≥0∞) • witnessMeasure q := by
  have h := compProd_le_three_of_fibres
    (uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
    (Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1))
    (Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => q z.1)) (by
      intro z
      rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply (fun z : ℝ × Bool => p z.1) (by fun_prop),
        Causalean.Mathlib.Probability.bernoulliMarkKernel_apply (fun z : ℝ × Bool => q z.1) (by fun_prop)]
      exact bernoulliBool_le_three _ _ (hpb z.1) (hqb z.1))
  have hprod := Measure.prod_mono h (le_refl (gaussianReal 0 1))
  rw [Measure.prod_smul_left] at hprod
  have hmap := Measure.map_mono hprod
    (show Measurable (fun z : ((ℝ × Bool) × Bool) × ℝ =>
      (z.1.1.1, z.1.1.2, z.1.2, z.2)) from by fun_prop)
  simpa only [witnessMeasure, Measure.map_smul] using hmap

/-- Both alternative observation laws obey bounded domination at every noise scale. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,s,t,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_le_three (hleg : ClassicalLegendreFacts) (β b σ : ℝ) (m : ℕ)
    (s t : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    Pobs (altLaw hleg β b m s hβ hb hm) σ ≤
      (3 : ℝ≥0∞) • Pobs (altLaw hleg β b m t hβ hb hm) σ := by
  have h := witnessMeasure_le_three (altProbability β b m s) (altProbability β b m t)
    (altProbability_continuous β b m s hb.1).measurable
    (altProbability_continuous β b m t hb.1).measurable
    (altProbability_mean_bounds hleg β b m s hβ hb hm)
    (altProbability_mean_bounds hleg β b m t hβ hb hm)
  have hmap := Measure.map_mono h (obs_measurable σ)
  simpa only [Pobs, altLaw, bernoulliWitness, Measure.map_smul] using hmap

/-- Domination gives absolute continuity for the entire observed triple. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,s,t,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_absolutelyContinuous (hleg : ClassicalLegendreFacts) (β b σ : ℝ) (m : ℕ)
    (s t : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    Pobs (altLaw hleg β b m s hβ hb hm) σ ≪
      Pobs (altLaw hleg β b m t hβ hb hm) σ := by
  exact Measure.absolutelyContinuous_of_le_smul
    (altLaw_observed_le_three hleg β b σ m s t hβ hb hm)

/-- A uniformly dominated finite law has an integrable centered likelihood square. Given [the displayed inputs and assumptions](hyp:α,μ,ν,h), [the stated mathematical conclusion holds](goal). -/
lemma rnDeriv_square_integrable_of_le_three {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≤ (3 : ℝ≥0∞) • ν) :
    Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν := by
  letI : IsFiniteMeasure ((3 : ℝ≥0∞) • ν) := Measure.smul_finite ν (by norm_num)
  have hle : ∀ᵐ x ∂ν, μ.rnDeriv ((3 : ℝ≥0∞) • ν) x ≤ 1 :=
    (Measure.absolutelyContinuous_smul (μ := ν) (c := (3 : ℝ≥0∞))
      (by norm_num)).ae_le
      (Measure.rnDeriv_le_one_of_le h)
  have hr := Measure.rnDeriv_smul_right_of_ne_top μ ν
    (r := (3 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have hbound : ∀ᵐ x ∂ν, (μ.rnDeriv ν x).toReal ≤ 3 := by
    filter_upwards [hle, hr] with x hx he
    rw [he] at hx
    have ht := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hx
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at ht
    linarith
  apply Integrable.of_bound
    ((((μ.measurable_rnDeriv ν).ennreal_toReal.sub measurable_const).pow_const 2).aestronglyMeasurable)
    4
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hn := ENNReal.toReal_nonneg (a := μ.rnDeriv ν x)
  change ((μ.rnDeriv ν x).toReal - 1)^2 ≤ 4
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hx)]

/-- The full observed alternative likelihood square is integrable on all cells. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,s,t,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_likelihood_square_integrable (hleg : ClassicalLegendreFacts)
    (β b σ : ℝ) (m : ℕ) (s t : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    let plus := Pobs (altLaw hleg β b m s hβ hb hm) σ
    let minus := Pobs (altLaw hleg β b m t hβ hb hm) σ
    Integrable (fun o => ((plus.rnDeriv minus o).toReal - 1)^2) minus := by
  letI := (altLaw hleg β b m s hβ hb hm).prob
  letI := (altLaw hleg β b m t hβ hb hm).prob
  haveI : IsProbabilityMeasure (Pobs (altLaw hleg β b m s hβ hb hm) σ) :=
    Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable
  haveI : IsProbabilityMeasure (Pobs (altLaw hleg β b m t hβ hb hm) σ) :=
    Measure.isProbabilityMeasure_map (obs_measurable σ).aemeasurable
  exact rnDeriv_square_integrable_of_le_three _ _
    (altLaw_observed_le_three hleg β b σ m s t hβ hb hm)

end CausalSmith.Stat.RdTruesideNoiseFrontier
