module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.EmpiricalPopulationBridge
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.PopulationBias

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Given [the displayed inputs and assumptions](hyp:J,σ,x), [this definition specifies the stated object](goal). -/
@[no_expose]
def inverseHeatSquareSeries (J : ℕ) (σ x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (kernelDegree J + 1),
    σ ^ (2 * j) * ((polyDeriv j (endpointKernel J)).eval x) ^ 2 /
      (Nat.factorial j : ℝ)

/-- Given [the displayed inputs and assumptions](hyp:J,σ), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeatSquareSeries_continuous (J : ℕ) (σ : ℝ) :
    Continuous (inverseHeatSquareSeries J σ) := by
  unfold inverseHeatSquareSeries
  fun_prop

/-- Given [the displayed inputs and assumptions](hyp:J,σ,x), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeatSquareSeries_nonneg (J : ℕ) (σ x : ℝ) :
    0 ≤ inverseHeatSquareSeries J σ x := by
  unfold inverseHeatSquareSeries
  apply Finset.sum_nonneg
  intro j hj
  apply div_nonneg
  · apply mul_nonneg
    · rw [show 2 * j = j * 2 by omega, pow_mul]
      positivity
    · positivity
  · positivity

/-- Given [the displayed inputs and assumptions](hyp:legendre,hermite,β,σ,Q,hQ,hσ,J,hJ,d), [the stated mathematical conclusion holds](goal). -/
lemma unmarked_observed_sq_eq_interval (legendre : ClassicalLegendreFacts)
    (hermite : ClassicalHermiteFacts) (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (hσ : σ ∈ Icc (0 : ℝ) 1) (J : ℕ) (hJ : 1 ≤ J)
    (d : Bool) :
    (∫ o : Obs, ((if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1)) ^ 2 ∂Pobs Q σ) =
      ∫ x in (0 : ℝ)..1, inverseHeatSquareSeries J σ x * Q.f (sgn d * x) := by
  obtain ⟨C, hC, hall⟩ := exact_covariance
  have hcov := (hall J hJ σ hσ).1
  let I : (ℝ × Bool × Bool) → ℝ := fun s => if decide (0 ≤ s.1) = d then 1 else 0
  let K : (ℝ × Bool × Bool) × ℝ → ℝ := fun sz => I sz.1 *
    (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)
  let H : (ℝ × Bool × Bool) × ℝ → ℝ := fun sz => (K sz) ^ 2
  letI : IsProbabilityMeasure Q.P := Q.prob
  letI : IsProbabilityMeasure (Q.P.map latentSchedule) :=
    Measure.isProbabilityMeasure_map latentSchedule_measurable.aemeasurable
  have hImeas : Measurable I := by
    dsimp [I]
    have hs : Measurable (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) := by
      have hset : MeasurableSet {s : ℝ × Bool × Bool | 0 ≤ s.1} :=
        measurableSet_le measurable_const measurable_fst
      have heq : (fun s : ℝ × Bool × Bool => decide (0 ≤ s.1)) =
          fun s => if 0 ≤ s.1 then true else false := by
        funext s; by_cases h : 0 ≤ s.1 <;> simp [h]
      rw [heq]
      exact measurable_const.ite hset measurable_const
    exact measurable_const.ite ((measurableSet_singleton d).preimage hs) measurable_const
  have hITop : MemLp (fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1) ⊤
      ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    apply memLp_top_of_bound (hImeas.comp measurable_fst).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun sz => by dsimp [I]; split_ifs <;> norm_num
  have hKLp : MemLp K 2 ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) := by
    have hb := inverseHeat_schedule_gaussian_memLp_two hermite Q d J σ
    change MemLp ((fun sz : (ℝ × Bool × Bool) × ℝ => I sz.1) *
      fun sz => (inverseHeat J σ).eval (sgn d * sz.1.1 + σ * sz.2)) 2 _
    exact hb.mul hITop
  have hHint : Integrable H ((Q.P.map latentSchedule).prod (gaussianReal 0 1)) :=
    hKLp.integrable_sq
  have hpull : (∫ o : Obs, ((if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1)) ^ 2 ∂Pobs Q σ) =
      ∫ ω, H (latentSchedule ω, sgn d * errorCoord ω) ∂Q.P := by
    rw [integral_Pobs_eq_integral_obs_comp]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        dsimp [H, K, I, obs, latentSchedule]
        rw [sgn_mul_proxy]
        rw [latentSchedule_fst]
        change ((if side ω = d then (1 : ℝ) else 0) * _) ^ 2 =
          ((if decide (0 ≤ score ω) = d then (1 : ℝ) else 0) * _) ^ 2
        rfl
    · have hiobs : Measurable (fun o : Obs => if o.2.1 = d then (1 : ℝ) else 0) :=
        measurable_const.ite ((measurableSet_singleton d).preimage measurable_snd.fst)
          measurable_const
      exact ((hiobs.mul (by fun_prop)).pow_const 2).aestronglyMeasurable
  rw [hpull, integral_latentSchedule_signedError β σ Q hQ d H hHint]
  have hinner (s : ℝ × Bool × Bool) :
      (∫ z, H (s,z) ∂gaussianReal 0 1) =
        I s * inverseHeatSquareSeries J σ (sgn d * s.1) := by
    dsimp [H, K]
    have hI : I s = 0 ∨ I s = 1 := by dsimp [I]; split_ifs <;> simp
    rcases hI with hI | hI
    · simp [hI]
    · simp [hI, inverseHeatSquareSeries, (hcov (sgn d * s.1)).2]
  simp_rw [hinner]
  have houtmeas : AEStronglyMeasurable (fun s => I s *
      inverseHeatSquareSeries J σ (sgn d * s.1)) (Q.P.map latentSchedule) :=
    (hImeas.mul ((inverseHeatSquareSeries_continuous J σ).measurable.comp
      (by fun_prop))).aestronglyMeasurable
  rw [integral_map latentSchedule_measurable.aemeasurable houtmeas]
  have harmint : (∫ ω, I (latentSchedule ω) *
      inverseHeatSquareSeries J σ (sgn d * (latentSchedule ω).1) ∂Q.P) =
      ∫ ω, (if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        inverseHeatSquareSeries J σ (sgn d * score ω) ∂Q.P := by
    apply integral_congr_ae
    filter_upwards [arm_indicator_ae_eq_reflected_Icc Q d] with ω harm
    simp only [I, latentSchedule_fst]
    change (if decide (0 ≤ score ω) = d then (1 : ℝ) else 0) * _ = _
    rw [show (if decide (0 ≤ score ω) = d then (1 : ℝ) else 0) =
      if sgn d * score ω ∈ Icc (0 : ℝ) 1 then 1 else 0 by
        change (if side ω = d then (1 : ℝ) else 0) = _; exact harm]
  rw [harmint]
  have hw : Measurable (fun x =>
      (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        inverseHeatSquareSeries J σ (sgn d * x)) := by
    exact (measurable_const.ite (measurableSet_Icc.preimage (by fun_prop))
      measurable_const).mul ((inverseHeatSquareSeries_continuous J σ).measurable.comp (by fun_prop))
  rw [integral_scoreWeight Q _ hw]
  rw [show (fun x => ((if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
      inverseHeatSquareSeries J σ (sgn d * x)) * Q.f x) =
      fun x => (if sgn d * x ∈ Icc (0 : ℝ) 1 then 1 else 0) *
        (inverseHeatSquareSeries J σ (sgn d * x) * Q.f x) by funext x; ring]
  cases d
  · simpa [sgn, mul_assoc] using reflected_Icc_integral false
      (fun x => inverseHeatSquareSeries J σ x * Q.f (sgn false * x))
  · simpa [sgn, mul_assoc] using reflected_Icc_integral true
      (fun x => inverseHeatSquareSeries J σ x * Q.f (sgn true * x))

/-- Given [the displayed inputs and assumptions](hyp:J,σ), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeatSquareSeries_interval (J : ℕ) (σ : ℝ) :
    (3 / 4 : ℝ) * (∫ x in (0 : ℝ)..1, inverseHeatSquareSeries J σ x) =
      kernelVariance J σ := by
  unfold inverseHeatSquareSeries kernelVariance
  rw [intervalIntegral.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp_rw [show ∀ x : ℝ,
      σ ^ (2 * j) * ((polyDeriv j (endpointKernel J)).eval x) ^ 2 /
          (Nat.factorial j : ℝ) =
        (σ ^ (2 * j) / (Nat.factorial j : ℝ)) *
          ((polyDeriv j (endpointKernel J)).eval x) ^ 2 by intro x; ring]
    rw [intervalIntegral.integral_const_mul]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ =>
      σ ^ (2 * j) * ((polyDeriv j (endpointKernel J)).eval x) ^ 2 /
        (Nat.factorial j : ℝ))).intervalIntegrable (0 : ℝ) 1

/-- Given [the displayed inputs and assumptions](hyp:legendre,hermite,β,σ,Q,hQ,hσ,J,hJ,d), [the stated mathematical conclusion holds](goal). -/
lemma unmarked_observed_sq_le_kernelVariance (legendre : ClassicalLegendreFacts)
    (hermite : ClassicalHermiteFacts) (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (hσ : σ ∈ Icc (0 : ℝ) 1) (J : ℕ) (hJ : 1 ≤ J)
    (d : Bool) :
    (∫ o : Obs, ((if o.2.1 = d then 1 else 0) *
      (inverseHeat J σ).eval (sgn d * o.1)) ^ 2 ∂Pobs Q σ) ≤ kernelVariance J σ := by
  rw [unmarked_observed_sq_eq_interval legendre hermite β σ Q hQ hσ J hJ d]
  calc
    (∫ x in (0 : ℝ)..1, inverseHeatSquareSeries J σ x * Q.f (sgn d * x)) ≤
        ∫ x in (0 : ℝ)..1, (3 / 4 : ℝ) * inverseHeatSquareSeries J σ x := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · have hc : ContinuousOn
            (fun u : ℝ => inverseHeatSquareSeries J σ u * Q.f (sgn d * u))
            (Icc (0 : ℝ) 1) :=
          (inverseHeatSquareSeries_continuous J σ).continuousOn.mul
            (continuousOn_arm_reflection d Q.f Q.f_cont)
        exact (hc.mono (by
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable
      · exact ((inverseHeatSquareSeries_continuous J σ).const_mul
          (3 / 4 : ℝ)).intervalIntegrable (0 : ℝ) 1
      · intro x hx
        have hf := (hQ.density (sgn d * x) (arm_reflection_mem d hx)).2
        have hs := inverseHeatSquareSeries_nonneg J σ x
        nlinarith
    _ = (3 / 4 : ℝ) * (∫ x in (0 : ℝ)..1, inverseHeatSquareSeries J σ x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = kernelVariance J σ := inverseHeatSquareSeries_interval J σ

/-- Given [the displayed inputs and assumptions](hyp:legendre,hermite,β,σ,Q,hQ,hσ,J,hJ,d), [the stated mathematical conclusion holds](goal). -/
lemma marked_observed_sq_le_kernelVariance (legendre : ClassicalLegendreFacts)
    (hermite : ClassicalHermiteFacts) (β σ : ℝ) (Q : LatentLaw)
    (hQ : Model β σ Q) (hσ : σ ∈ Icc (0 : ℝ) 1) (J : ℕ) (hJ : 1 ≤ J)
    (d : Bool) :
    (∫ o : Obs, ((if o.2.1 = d then 1 else 0) * bit o.2.2 *
      (inverseHeat J σ).eval (sgn d * o.1)) ^ 2 ∂Pobs Q σ) ≤ kernelVariance J σ := by
  have hm := observed_arm_summands_memLp_two hermite β σ Q hQ d J
  apply (integral_mono hm.1.integrable_sq hm.2.integrable_sq ?_).trans
    (unmarked_observed_sq_le_kernelVariance legendre hermite β σ Q hQ hσ J hJ d)
  intro o
  cases h : o.2.2 <;> simp [bit, h] <;> positivity

end CausalSmith.Stat.RdTruesideNoiseFrontier
