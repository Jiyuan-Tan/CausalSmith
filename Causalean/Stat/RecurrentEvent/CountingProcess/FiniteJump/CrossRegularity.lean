module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.FullSample

/-!
# Predictability and absolute integrability of cross-subject payoffs

All subjects share the full-sample history filtration. A bounded predictable
payoff times another subject's strict-past integral is therefore predictable.
The count second moments and bounded rates supply its jump and time envelopes.
This analytic layer is independent of diffuse jumps and pathwise cross products.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The oriented cross payoff is the current full-sample integrand times the
other subject's strict-past compensated integral. -/
noncomputable def SampleModel.crossPayoff (S : SampleModel n Ω μ)
    (H : ℝ → (Fin n → Ω) → ℝ) (j : Fin n) : ℝ → (Fin n → Ω) → ℝ :=
  fun t x => H t x * (S.process j).prefixIntegral H t x

/-- An oriented cross payoff remains predictable for any subject's process,
since all component processes share the full-sample history filtration. -/
theorem SampleModel.crossPayoff_predictable (S : SampleModel n Ω μ)
    (H : ℝ → (Fin n → Ω) → ℝ) (hH : S.LeftPredictable H) (i j : Fin n) :
    (S.process i).Predictable (S.crossPayoff H j) := by
  have hp := (S.process j).predictable_prefix H (S.process_predictable H hH j)
  have hp' : (S.process i).Predictable ((S.process j).prefixIntegral H) := by
    unfold Model.Predictable at hp ⊢
    rw [S.process_filtration j] at hp
    rw [S.process_filtration i]
    exact hp
  exact (S.process_predictable H hH i).mul hp'

/-- The sum over one subject's jumps of the absolute oriented cross payoff
is Bochner integrable for a bounded full-sample predictable integrand. -/
theorem SampleModel.crossPayoff_jump_abs_integrable (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → (Fin n → Ω) → ℝ) (hH : S.LeftPredictable H)
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C) (i j : Fin n) :
    Integrable ((S.process i).jumpIntegral
      (fun t x => |S.crossPayoff H j t x|) (S.process i).horizon)
      (finiteSampleLaw n μ) := by
  /- Use Model.abs_prefixIntegral_le on the j process and the common horizon.
     The payoff envelope is C^2*(count_j + R_j*T). Its product with count_i
     is integrable by MemLp.integrable_mul and the supplied count squares;
     the remaining count_i term uses integrable_eventCount. Apply the closed
     Model.integrable_jump_of_envelope to the measurable absolute payoff.
     Counts need not be independent, and i=j is deliberately included. -/
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t x, |H t x| ≤ C :=
    fun t x => (hC₀ t x).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := (S.process j).rate_horizon_uniform_bound
  let B : (Fin n → Ω) → ℝ := fun x =>
    C * (C * (((S.process j).eventTimes x).card : ℝ) +
      C * (R * (S.process j).horizon))
  have hpay := (S.process i).predictable_joint_measurable _
    (S.crossPayoff_predictable H hH i j)
  have hpaybound (t : ℝ) (x : Fin n → Ω) (ht : 0 < t)
      (hT : t ≤ (S.process i).horizon) : |S.crossPayoff H j t x| ≤ B x := by
    have hTj : t ≤ (S.process j).horizon := by
      simpa only [S.process_horizon] using hT
    have hp := (S.process j).abs_prefixIntegral_le H C R hC hR hb
      (fun s x hs hS => (hr s x hs hS).2) t ⟨ht.le, hTj⟩ x
    unfold SampleModel.crossPayoff
    rw [abs_mul]
    exact mul_le_mul (hb t x) hp (abs_nonneg _) hC
  have hi₂ : MemLp (fun x => (((S.process i).eventTimes x).card : ℝ)) 2
      (finiteSampleLaw n μ) :=
    (memLp_two_iff_integrable_sq
      (S.process i).integrable_eventCount.aestronglyMeasurable).2
      (S.process i).count_square_integrable
  have hj₂ : MemLp (fun x => (((S.process j).eventTimes x).card : ℝ)) 2
      (finiteSampleLaw n μ) :=
    (memLp_two_iff_integrable_sq
      (S.process j).integrable_eventCount.aestronglyMeasurable).2
      (S.process j).count_square_integrable
  have hi : Integrable (fun x => B x *
      (((S.process i).eventTimes x).card : ℝ)) (finiteSampleLaw n μ) := by
    have h := ((hj₂.integrable_mul hi₂).const_mul (C * C)).add
      ((S.process i).integrable_eventCount.const_mul
        (C * C * (R * (S.process j).horizon)))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp [B]
    ring
  exact (S.process i).integrable_jump_of_envelope _ hpay.abs B hi
    (fun t x ht hT => by simpa only [abs_abs] using hpaybound t x ht hT)


/-- The intensity integral for one subject of the absolute oriented cross
payoff is Bochner integrable for a bounded full-sample predictable integrand. -/
theorem SampleModel.crossPayoff_energy_abs_integrable (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → (Fin n → Ω) → ℝ) (hH : S.LeftPredictable H)
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C) (i j : Fin n) :
    Integrable ((S.process i).energyIntegral
      (fun t x => |S.crossPayoff H j t x|) (S.process i).horizon)
      (finiteSampleLaw n μ) := by
  /- The same prefix envelope C^2*(count_j + R_j*T) has a first moment.
     Use Model.integrable_energy_of_envelope with process i's rate bound,
     and predictable_joint_measurable applied to crossPayoff_predictable.
     Transfer the horizon with process_horizon. This does not depend on the
     jump-integrability lemma, no-common-jumps, or compensation. -/
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t x, |H t x| ≤ C :=
    fun t x => (hC₀ t x).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := (S.process j).rate_horizon_uniform_bound
  let B : (Fin n → Ω) → ℝ := fun x =>
    C * (C * (((S.process j).eventTimes x).card : ℝ) +
      C * (R * (S.process j).horizon))
  have hpay := (S.process i).predictable_joint_measurable _
    (S.crossPayoff_predictable H hH i j)
  have hpaybound (t : ℝ) (x : Fin n → Ω) (ht : 0 < t)
      (hT : t ≤ (S.process i).horizon) : |S.crossPayoff H j t x| ≤ B x := by
    have hTj : t ≤ (S.process j).horizon := by
      simpa only [S.process_horizon] using hT
    have hp := (S.process j).abs_prefixIntegral_le H C R hC hR hb
      (fun s x hs hS => (hr s x hs hS).2) t ⟨ht.le, hTj⟩ x
    unfold SampleModel.crossPayoff
    rw [abs_mul]
    exact mul_le_mul (hb t x) hp (abs_nonneg _) hC
  have hi : Integrable B (finiteSampleLaw n μ) :=
    (((S.process j).integrable_eventCount.const_mul C).add
      (integrable_const (C * (R * (S.process j).horizon)))).const_mul C
  have hnonneg (x : Fin n → Ω) : 0 ≤ B x := by
    dsimp [B]
    have hT := (S.process j).horizon_pos.le
    positivity
  obtain ⟨Ri, hRi, hri⟩ := (S.process i).rate_horizon_uniform_bound
  exact (S.process i).integrable_energy_of_envelope _ hpay.abs B hi hnonneg Ri
    (fun t x ht hT => (hri t x ht hT).2)
    (fun t x ht hT => by simpa only [abs_abs] using hpaybound t x ht hT)


/-- The absolute jump sum and absolute intensity integral of an oriented
cross payoff are Bochner integrable under count second moments and bounded rates.
[The sample model and payoff](hyp:S,H), [left predictability](hyp:hH), [the
uniform bound](hyp:hbound), and [the two subject indices](hyp:i,j) give [both
Bochner-integrability conclusions](goal). -/
theorem SampleModel.crossPayoff_integrable (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → (Fin n → Ω) → ℝ) (hH : S.LeftPredictable H)
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C) (i j : Fin n) :
    Integrable ((S.process i).jumpIntegral
      (fun t x => |S.crossPayoff H j t x|) (S.process i).horizon)
      (finiteSampleLaw n μ) ∧
    Integrable ((S.process i).energyIntegral
      (fun t x => |S.crossPayoff H j t x|) (S.process i).horizon)
      (finiteSampleLaw n μ) := by
  exact ⟨S.crossPayoff_jump_abs_integrable H hH hbound i j,
    S.crossPayoff_energy_abs_integrable H hH hbound i j⟩

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
