module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PrefixBounds

/-!
# Analytic regularity of finite-jump prefixes

The count second moment and pathwise bounds give integrability without using
compensation or predictable-prefix closure. Ordinary joint measurability of the
prefix suffices here, making this layer independent of filtration arguments.
-/

public section

open MeasureTheory Set Filter

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A jointly measurable payoff has a jointly measurable strict-past
compensated prefix, including the totalized time-integral definition. -/
theorem Model.measurable_prefixIntegral (M : Model Ω μ)
    (H : ℝ → Ω → ℝ)
    (hH : Measurable (fun p : ℝ × Ω => H p.1 p.2)) :
    Measurable (fun p : ℝ × Ω => M.prefixIntegral H p.1 p.2) := by
  classical
  let J : ℝ × Ω → ℝ := fun p =>
    ∑ s ∈ (M.eventTimes p.2).filter (fun s => s < p.1), H s p.2
  have henum (p : ℝ × Ω) : J p =
      ∑ k ∈ Finset.range (M.eventTimes p.2).card,
        if M.jumpTime k p.2 < p.1 then H (M.jumpTime k p.2) p.2 else 0 := by
    have he := M.jumpIntegral_eq_sum_jumpTime
      (fun s ω => if s < p.1 then H s ω else 0) p.2
    simpa [Model.jumpIntegral, J, Finset.sum_filter,
      Finset.filter_eq_self.mpr (fun s hs => (M.events_in_horizon p.2 s hs).2)] using he
  have hterm (k : ℕ) : Measurable (fun p : ℝ × Ω =>
      if M.jumpTime k p.2 < p.1 then H (M.jumpTime k p.2) p.2 else 0) := by
    exact Measurable.ite
      (measurableSet_lt ((M.measurable_jumpTime k).comp measurable_snd) measurable_fst)
      (hH.comp (((M.measurable_jumpTime k).comp measurable_snd).prodMk measurable_snd))
      measurable_const
  have hsum (n : ℕ) : Measurable (fun p : ℝ × Ω =>
      ∑ k ∈ Finset.range n,
        if M.jumpTime k p.2 < p.1 then H (M.jumpTime k p.2) p.2 else 0) :=
    Finset.measurable_sum _ (fun k _ => hterm k)
  have hj : Measurable J := by
    apply measurable_of_Iio
    intro a
    have hset : J ⁻¹' Iio a = ⋃ n : ℕ,
        {p : ℝ × Ω | (M.eventTimes p.2).card = n} ∩
        (fun p : ℝ × Ω => ∑ k ∈ Finset.range n,
          if M.jumpTime k p.2 < p.1 then H (M.jumpTime k p.2) p.2 else 0) ⁻¹' Iio a := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨(M.eventTimes p.2).card, rfl, ?_⟩
        change (∑ k ∈ Finset.range (M.eventTimes p.2).card,
          if M.jumpTime k p.2 < p.1 then H (M.jumpTime k p.2) p.2 else 0) < a
        rwa [henum p] at h
      · rintro ⟨n, hn, h⟩
        rw [henum p, hn]
        exact h
    rw [hset]
    exact MeasurableSet.iUnion (fun n =>
      ((M.measurable_eventCard.comp measurable_snd) (measurableSet_singleton n)).inter
        (hsum n measurableSet_Iio))
  let K : (ℝ × Ω) × ℝ → ℝ := fun q =>
    if 0 < q.2 ∧ q.2 ≤ q.1.1 then
      H q.2 q.1.2 * (M.atRisk q.2 q.1.2 * M.intensity q.2 q.1.2) else 0
  have hk : Measurable K := by
    have hp : Measurable (fun q : (ℝ × Ω) × ℝ => (q.2, q.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    exact Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst)))
      ((hH.comp hp).mul ((M.atRisk_joint_measurable.comp hp).mul
        (M.intensity_joint_measurable.comp hp))) measurable_const
  have he : Measurable (fun p : ℝ × Ω => M.energyIntegral H p.1 p.2) := by
    have hi := (hk.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    convert hi using 1
    funext p
    simpa only [Model.energyIntegral, K, Set.indicator, Set.mem_Ioc] using
      (integral_indicator (μ := volume)
        (f := fun s => H s p.2 * (M.atRisk s p.2 * M.intensity s p.2))
        (s := Ioc 0 p.1) measurableSet_Ioc).symm
  exact hj.sub he

/-- The mixed strict-past jump payoff is integrable because it grows at most
quadratically in the finite event count. -/
theorem Model.integrable_prefix_jump (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.jumpIntegral (M.prefixPayoff H) M.horizon) μ := by
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t ω, |H t ω| ≤ C :=
    fun t ω => (hC₀ t ω).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  let B : Ω → ℝ := fun ω =>
    2 * C * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon))
  have hm := M.predictable_joint_measurable H hH
  have hpay : Measurable (fun p : ℝ × Ω => M.prefixPayoff H p.1 p.2) :=
    (measurable_const.mul hm).mul (M.measurable_prefixIntegral H hm)
  have hpaybound (t : ℝ) (ω : Ω) (ht : 0 < t) (hT : t ≤ M.horizon) :
      |M.prefixPayoff H t ω| ≤ B ω := by
    have hp := M.abs_prefixIntegral_le H C R hC hR hb
      (fun s ω hs hS => (hr s ω hs hS).2) t ⟨ht.le, hT⟩ ω
    calc
      |M.prefixPayoff H t ω| = 2 * |H t ω| * |M.prefixIntegral H t ω| := by
        simp [Model.prefixPayoff, abs_mul]
      _ ≤ (2 * C) * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hb t ω) (by norm_num)) hp
          (abs_nonneg _) (mul_nonneg (by norm_num) hC)
      _ = B ω := rfl
  have hi : Integrable (fun ω => B ω * ((M.eventTimes ω).card : ℝ)) μ := by
    have h := (M.count_square_integrable.const_mul (2 * C * C)).add
      (M.integrable_eventCount.const_mul (2 * C * C * (R * M.horizon)))
    have heq : (fun ω => B ω * ((M.eventTimes ω).card : ℝ)) =
        (fun ω => 2 * C * C * ((M.eventTimes ω).card : ℝ) ^ 2 +
          (2 * C * C * (R * M.horizon)) * ((M.eventTimes ω).card : ℝ)) := by
      funext ω
      dsimp [B]
      ring
    rw [heq]
    exact h
  exact M.integrable_jump_of_envelope _ hpay B hi hpaybound

/-- The sum of absolute mixed strict-past jump payoffs is integrable; this
controls truncation in the predictable-compensator theorem. -/
theorem Model.integrable_prefix_jump_abs (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.jumpIntegral
      (fun t ω => |M.prefixPayoff H t ω|) M.horizon) μ := by
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t ω, |H t ω| ≤ C :=
    fun t ω => (hC₀ t ω).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  let B : Ω → ℝ := fun ω =>
    2 * C * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon))
  have hm := M.predictable_joint_measurable H hH
  have hpay : Measurable (fun p : ℝ × Ω => M.prefixPayoff H p.1 p.2) :=
    (measurable_const.mul hm).mul (M.measurable_prefixIntegral H hm)
  have hpaybound (t : ℝ) (ω : Ω) (ht : 0 < t) (hT : t ≤ M.horizon) :
      |M.prefixPayoff H t ω| ≤ B ω := by
    have hp := M.abs_prefixIntegral_le H C R hC hR hb
      (fun s ω hs hS => (hr s ω hs hS).2) t ⟨ht.le, hT⟩ ω
    calc
      |M.prefixPayoff H t ω| = 2 * |H t ω| * |M.prefixIntegral H t ω| := by
        simp [Model.prefixPayoff, abs_mul]
      _ ≤ (2 * C) * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hb t ω) (by norm_num)) hp
          (abs_nonneg _) (mul_nonneg (by norm_num) hC)
      _ = B ω := rfl
  have hi : Integrable (fun ω => B ω * ((M.eventTimes ω).card : ℝ)) μ := by
    have h := (M.count_square_integrable.const_mul (2 * C * C)).add
      (M.integrable_eventCount.const_mul (2 * C * C * (R * M.horizon)))
    have heq : (fun ω => B ω * ((M.eventTimes ω).card : ℝ)) =
        (fun ω => 2 * C * C * ((M.eventTimes ω).card : ℝ) ^ 2 +
          (2 * C * C * (R * M.horizon)) * ((M.eventTimes ω).card : ℝ)) := by
      funext ω
      dsimp [B]
      ring
    rw [heq]
    exact h
  exact M.integrable_jump_of_envelope _ hpay.abs B hi
    (fun t ω ht hT => by simpa only [abs_abs] using hpaybound t ω ht hT)

/-- The mixed strict-past compensator payoff is integrable because it grows
at most linearly in the finite event count. -/
theorem Model.integrable_prefix_energy (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.energyIntegral (M.prefixPayoff H) M.horizon) μ := by
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t ω, |H t ω| ≤ C :=
    fun t ω => (hC₀ t ω).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  let B : Ω → ℝ := fun ω =>
    2 * C * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon))
  have hm := M.predictable_joint_measurable H hH
  have hpay : Measurable (fun p : ℝ × Ω => M.prefixPayoff H p.1 p.2) :=
    (measurable_const.mul hm).mul (M.measurable_prefixIntegral H hm)
  have hpaybound (t : ℝ) (ω : Ω) (ht : 0 < t) (hT : t ≤ M.horizon) :
      |M.prefixPayoff H t ω| ≤ B ω := by
    have hp := M.abs_prefixIntegral_le H C R hC hR hb
      (fun s ω hs hS => (hr s ω hs hS).2) t ⟨ht.le, hT⟩ ω
    calc
      |M.prefixPayoff H t ω| = 2 * |H t ω| * |M.prefixIntegral H t ω| := by
        simp [Model.prefixPayoff, abs_mul]
      _ ≤ (2 * C) * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hb t ω) (by norm_num)) hp
          (abs_nonneg _) (mul_nonneg (by norm_num) hC)
      _ = B ω := rfl
  have hi : Integrable B μ :=
    ((M.integrable_eventCount.const_mul C).add
      (integrable_const (C * (R * M.horizon)))).const_mul (2 * C)
  have hnonneg (ω : Ω) : 0 ≤ B ω := by
    dsimp [B]
    have hT := M.horizon_pos.le
    positivity
  exact M.integrable_energy_of_envelope _ hpay B hi hnonneg R hR
    (fun t ω ht hT => (hr t ω ht hT).2) hpaybound

/-- The integral of the absolute mixed strict-past payoff against the
compensator is integrable; this controls truncation in predictable
compensation. -/
theorem Model.integrable_prefix_energy_abs (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (M.energyIntegral
      (fun t ω => |M.prefixPayoff H t ω|) M.horizon) μ := by
  obtain ⟨C₀, hC₀⟩ := hbound
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hb : ∀ t ω, |H t ω| ≤ C :=
    fun t ω => (hC₀ t ω).trans (le_abs_self C₀)
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  let B : Ω → ℝ := fun ω =>
    2 * C * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon))
  have hm := M.predictable_joint_measurable H hH
  have hpay : Measurable (fun p : ℝ × Ω => M.prefixPayoff H p.1 p.2) :=
    (measurable_const.mul hm).mul (M.measurable_prefixIntegral H hm)
  have hpaybound (t : ℝ) (ω : Ω) (ht : 0 < t) (hT : t ≤ M.horizon) :
      |M.prefixPayoff H t ω| ≤ B ω := by
    have hp := M.abs_prefixIntegral_le H C R hC hR hb
      (fun s ω hs hS => (hr s ω hs hS).2) t ⟨ht.le, hT⟩ ω
    calc
      |M.prefixPayoff H t ω| = 2 * |H t ω| * |M.prefixIntegral H t ω| := by
        simp [Model.prefixPayoff, abs_mul]
      _ ≤ (2 * C) * (C * ((M.eventTimes ω).card : ℝ) + C * (R * M.horizon)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hb t ω) (by norm_num)) hp
          (abs_nonneg _) (mul_nonneg (by norm_num) hC)
      _ = B ω := rfl
  have hi : Integrable B μ :=
    ((M.integrable_eventCount.const_mul C).add
      (integrable_const (C * (R * M.horizon)))).const_mul (2 * C)
  have hnonneg (ω : Ω) : 0 ≤ B ω := by
    dsimp [B]
    have hT := M.horizon_pos.le
    positivity
  exact M.integrable_energy_of_envelope _ hpay.abs B hi hnonneg R hR
    (fun t ω ht hT => (hr t ω ht hT).2)
    (fun t ω ht hT => by simpa only [abs_abs] using hpaybound t ω ht hT)

/-- A bounded predictable compensated integral is square integrable under a
second moment for the finite event count and a bounded intensity. [The model
and payoff](hyp:M,H), [predictability](hyp:hH), and [boundedness](hyp:hbound)
give [square integrability of the compensated integral](goal). -/
theorem Model.integrable_stochastic_square (M : Model Ω μ) [IsProbabilityMeasure μ]
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) :
    Integrable (fun ω => (M.stochasticIntegral H M.horizon ω) ^ 2) μ := by
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  let D : ℝ := |C| * (R * M.horizon)
  have hD : 0 ≤ D := mul_nonneg (abs_nonneg C)
    (mul_nonneg hR M.horizon_pos.le)
  have hi : Integrable (fun ω =>
      2 * |C| ^ 2 * ((M.eventTimes ω).card : ℝ) ^ 2 + 2 * D ^ 2) μ :=
    (M.count_square_integrable.const_mul (2 * |C| ^ 2)).add (integrable_const _)
  apply hi.mono' ((M.measurable_stochasticIntegral H hH).pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := M.abs_stochasticIntegral_le H |C| R (abs_nonneg C) hR
    (fun t ω => (hC t ω).trans (le_abs_self C))
    (fun t ω ht hT => (hr t ω ht hT).2) ω
  change |M.stochasticIntegral H M.horizon ω| ≤
    |C| * ((M.eventTimes ω).card : ℝ) + D at hb
  have hsq := pow_le_pow_left₀ (abs_nonneg (M.stochasticIntegral H M.horizon ω)) hb 2
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (|C| * ((M.eventTimes ω).card : ℝ) - D)]

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
