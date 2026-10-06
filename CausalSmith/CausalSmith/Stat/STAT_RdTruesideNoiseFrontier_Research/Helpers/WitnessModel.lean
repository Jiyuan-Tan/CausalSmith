module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LegalRegularity

/-!
# Model membership of the cancellation witnesses

The product construction supplies the Gaussian marginal and joint independence.
The unit and Hölder bounds keep the conditional means inside the benchmark class.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The two-mark schedule law is a probability measure for valid Bernoulli probabilities. Given [the displayed inputs and assumptions](hyp:p,hp,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_schedule_probability (p : ℝ → ℝ) (hp : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure
      ((uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
        ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)) := by
  letI := witnessMeasure_probability p hp hb
  rw [← witnessMeasure_schedule p]
  exact Measure.isProbabilityMeasure_map (by unfold score; fun_prop)

/-- The independent product Gaussian survives the coordinate rearrangement. Given [the displayed inputs and assumptions](hyp:p,hp,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_error (p : ℝ → ℝ) (hp : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessMeasure p).map errorCoord = gaussianReal 0 1 := by
  letI := witnessMeasure_schedule_probability p hp hb
  unfold witnessMeasure
  rw [Measure.map_map (by unfold errorCoord; fun_prop) (by fun_prop)]
  change Measure.map Prod.snd _ = _
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The Gaussian is independent of the score and both potentials jointly. Given [the displayed inputs and assumptions](hyp:p,hp,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_error_independent (p : ℝ → ℝ) (hp : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    IndepFun errorCoord (fun ω : Latent => (score ω, ω.2.1, ω.2.2.1))
      (witnessMeasure p) := by
  let M := (uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
    ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  letI : IsProbabilityMeasure M := witnessMeasure_schedule_probability p hp hb
  letI := witnessMeasure_probability p hp hb
  apply (indepFun_iff_map_prod_eq_prod_map_map (by unfold errorCoord; fun_prop)
    (by unfold score; fun_prop)).2
  unfold witnessMeasure
  rw [Measure.map_map (by unfold errorCoord score; fun_prop) (by fun_prop),
    Measure.map_map (by unfold errorCoord; fun_prop) (by fun_prop),
    Measure.map_map (by unfold score; fun_prop) (by fun_prop)]
  exact (indepFun_prod (μ := M) (ν := gaussianReal 0 1)
    (X := fun z : (ℝ × Bool) × Bool => (z.1.1, z.1.2, z.2))
    (Y := fun z : ℝ => z) (by fun_prop) measurable_id).symm.map_prod_eq_prod_map_map
      (by unfold errorCoord; fun_prop) (by unfold score; fun_prop)

/-- Legal widths and degrees give a positive endpoint resolution at most one. Given [the displayed inputs and assumptions](hyp:b,m,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma cancellationResolution_mem (b : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1)
    (hm : 2 ≤ m) : b / (m : ℝ)^2 ∈ Ioc (0 : ℝ) 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm2 : (1 : ℝ) ≤ (m : ℝ)^2 := by nlinarith
  exact ⟨div_pos hb.1 (by positivity), (div_le_one (by positivity)).2 (by linarith [hb.2])⟩

/-- Extract the pointwise modulus from the established full-domain seminorm bound. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,hβ,hb,hm,x,t,hx,ht), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_holder_pointwise (hleg : ClassicalLegendreFacts) (β b : ℝ)
    (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : 0 < b) (hm : 2 ≤ m)
    (x t : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |legalExtension b m x - legalExtension b m t| ≤
      7 * (b/(m : ℝ)^2)^(-β) * |x-t|^β := by
  by_cases hxt : x = t
  · subst t
    simp only [sub_self, abs_zero]
    positivity
  have hd : 0 < |x-t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
  have hquot : ENNReal.ofReal (|legalExtension b m x - legalExtension b m t| / |x-t|^β) ≤
      holderSeminorm β (legalExtension b m) := by
    exact le_sSup ⟨x, hx, t, ht, hxt, rfl⟩
  have hbnd := hquot.trans (legalExtension_holder_bound hleg β b m hβ hb hm)
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbnd
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hd β)).mp hr

/-- The small perturbation keeps the treated mean in the model's interior interval. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,s,hβ,hb,hm,x), [the stated mathematical conclusion holds](goal). -/
lemma altProbability_mean_bounds (hleg : ClassicalLegendreFacts) (β b : ℝ) (m : ℕ)
    (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (x : ℝ) : 1/4 ≤ altProbability β b m s x ∧ altProbability β b m s x ≤ 3/4 := by
  have hr := cancellationResolution_mem b m hb hm
  have hp0 := Real.rpow_nonneg hr.1.le β
  have hp1 := Real.rpow_le_one hr.1.le hr.2 hβ.1.le
  have hv := legalExtension_abs_le_one hleg b m hb.1 x
  have hprod : |(b/(m : ℝ)^2)^β * legalExtension b m x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact (mul_le_mul_of_nonneg_left hv hp0).trans (by simpa using hp1)
  have hbounds := abs_le.mp hprod
  cases s <;> simp only [altProbability, witnessSign, Bool.false_eq_true, if_false, if_true, kappa]
  · constructor <;> nlinarith [hbounds.1, hbounds.2]
  · constructor <;> nlinarith [hbounds.1, hbounds.2]

/-- The perturbation amplitude cancels the resolution factor in its Hölder modulus. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,s,hβ,hb,hm,x,t,hx,ht), [the stated mathematical conclusion holds](goal). -/
lemma altProbability_holder (hleg : ClassicalLegendreFacts) (β b : ℝ) (m : ℕ)
    (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (x t : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |altProbability β b m s x - altProbability β b m s t| ≤ 2 * |x-t|^β := by
  have hr := cancellationResolution_mem b m hb hm
  have hp0 := Real.rpow_nonneg hr.1.le β
  have hcancel : (b/(m : ℝ)^2)^β * (b/(m : ℝ)^2)^(-β) = 1 := by
    rw [← Real.rpow_add hr.1]
    simp
  have hv := legalExtension_holder_pointwise hleg β b m hβ hb.1 hm x t hx ht
  have hsign : |witnessSign s| = 1 := by cases s <;> norm_num [witnessSign]
  have heq : altProbability β b m s x - altProbability β b m s t =
      witnessSign s * kappa * (b/(m : ℝ)^2)^β *
        (legalExtension b m x - legalExtension b m t) := by unfold altProbability; ring
  rw [heq, abs_mul, abs_mul, abs_mul, hsign, abs_of_nonneg hp0]
  norm_num [kappa]
  calc
    _ ≤ 1/100 * (b/(m : ℝ)^2)^β *
        (7 * (b/(m : ℝ)^2)^(-β) * |x-t|^β) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (7/100 : ℝ) * ((b/(m : ℝ)^2)^β * (b/(m : ℝ)^2)^(-β)) * |x-t|^β := by ring
    _ = (7/100 : ℝ) * |x-t|^β := by rw [hcancel, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _)

/-- All five model atoms hold for each constructed cancellation alternative. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,s,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_model (hleg : ClassicalLegendreFacts) (β b σ : ℝ) (m : ℕ)
    (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    Model β σ (altLaw hleg β b m s hβ hb hm) := by
  have hp := altProbability_properties hleg β b m s hβ hb hm
  constructor
  · exact witnessMeasure_error _ hp.1 hp.2.2
  · exact witnessMeasure_error_independent _ hp.1 hp.2.2
  · intro x hx
    change 1/4 ≤ uniformDensity x ∧ uniformDensity x ≤ 3/4
    norm_num [uniformDensity, hx]
  · intro d x hx
    change 1/4 ≤ witnessMu (altProbability β b m s) d x ∧
      witnessMu (altProbability β b m s) d x ≤ 3/4
    cases d
    · norm_num [witnessMu]
    · exact altProbability_mean_bounds hleg β b m s hβ hb hm x
  · intro d x hx t ht
    change |witnessMu (altProbability β b m s) d x - witnessMu (altProbability β b m s) d t| ≤ _
    cases d
    · simp only [witnessMu, Bool.false_eq_true, if_false, sub_self, abs_zero]
      positivity
    · exact altProbability_holder hleg β b m s hβ hb hm x t hx ht

end CausalSmith.Stat.RdTruesideNoiseFrontier
