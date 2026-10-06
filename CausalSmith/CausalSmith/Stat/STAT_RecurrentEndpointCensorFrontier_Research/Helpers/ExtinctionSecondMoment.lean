module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExtinctionFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RecurrenceScoreMeasurability

/-!
# Explicit extinction second moment

The extinction remainder is supported on the empty endpoint risk set. Its
squared envelope is averaged using the exact iid empty-risk probability and
the endpoint lower retention bound.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The empty endpoint risk event is measurable. -/
-- @node: measurableSet_endpointRiskZero
lemma measurableSet_endpointRiskZero {n : ℕ} (a : Arm) (h : ℝ) :
    MeasurableSet {s : Fin n → ObsHistory | riskSet a s (1 - h) = 0} := by
  exact measurableSet_eq_fun
    ((measurable_recurrenceRiskSet_joint a).comp
      (measurable_id.prodMk measurable_const)) measurable_const

/-- The endpoint empty-risk probability has the declared exponential envelope. -/
-- @node: endpointRiskZero_probability_le_explicit
lemma endpointRiskZero_probability_le_explicit (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hhcap : h ≤ c.x0 / 2) :
    (sampleLaw P n).real {s | riskSet a s (1 - h) = 0} ≤
      Real.exp (-(c.pMin * c.gMin * Real.exp (-c.dMax) / 2 * n * h ^ c.kappa)) := by
  have ht : 1 - h ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [c.x0_le]
  have hr := retention_ge_half_gMin_rpow c P hP a
    (t := 1 - h) (by constructor <;> linarith [c.x0_pos])
  simp only [sub_sub_cancel] at hr
  have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ht).1
  have hp := hP.treatmentOverlap a
  have hl : c.pMin * Real.exp (-c.dMax) * (c.gMin / 2 * h ^ c.kappa) ≤
      P.p a * survival P a (1 - h) * retention P a (1 - h) := by
    apply mul_le_mul
    · exact mul_le_mul hp hs (Real.exp_pos _).le (c.pMin_pos.le.trans hp)
    · exact hr
    · exact mul_nonneg (div_nonneg c.gMin_pos.le (by norm_num))
        (Real.rpow_nonneg hh.le _)
    · exact mul_nonneg (c.pMin_pos.le.trans hp) (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-(n * (P.p a * survival P a (1 - h) * retention P a (1 - h)))) :=
      riskSet_zero_probability_le_exp P hP a n ht
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n)]

/-- The pathwise squared extinction envelope holds almost surely, including
empty treatment arms. -/
-- @node: extinctionError_sq_le_endpointIndicator_ae
lemma extinctionError_sq_le_endpointIndicator_ae (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) :
    ∀ᵐ s ∂sampleLaw P n, extinctionError c P a s h ^ 2 ≤
      ({s : Fin n → ObsHistory | riskSet a s (1 - h) = 0}).indicator
        (fun _ => (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2) s := by
  filter_upwards [sample_exit_nonneg P hP.deathHazard n,
    sample_exit_le_one P n] with s hs0 hs1
  have hb := extinctionError_abs_le_indicator c P hP a s
    (fun i _ => ⟨hs0 i, hs1 i⟩) hh
  have hB : 0 ≤ weightEnvelope c * c.lambdaMax * Real.exp c.dMax := by
    have hW : 0 ≤ weightEnvelope c := by unfold weightEnvelope continuationNorm; positivity
    have hL := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
    positivity
  by_cases hz : riskSet a s (1 - h) = 0
  · simpa [hz, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 (by simpa [hz] using hb)
  · have he : extinctionError c P a s h = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa [hz] using hb) (abs_nonneg _))
    simp [hz, he]

/-- Averaging the extinction indicator gives its explicit finite-sample
second-moment bound. -/
-- @node: extinctionError_secondMoment_le_explicit
lemma extinctionError_secondMoment_le_explicit (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) (a : Arm) (n : ℕ)
    {h : ℝ} (hh : 0 < h) (hhcap : h ≤ c.x0 / 2) :
    (∫ s : Fin n → ObsHistory, extinctionError c P a s h ^ 2 ∂sampleLaw P n) ≤
      weightEnvelope c ^ 2 * c.lambdaMax ^ 2 * Real.exp (2 * c.dMax) *
        Real.exp (-(c.pMin * c.gMin * Real.exp (-c.dMax) / 2 * n * h ^ c.kappa)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  let E := {s : Fin n → ObsHistory | riskSet a s (1 - h) = 0}
  let B := (weightEnvelope c * c.lambdaMax * Real.exp c.dMax) ^ 2
  have hE : MeasurableSet E := measurableSet_endpointRiskZero a h
  calc
    _ ≤ ∫ s, E.indicator (fun _ => B) s ∂sampleLaw P n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        ((integrable_const B).indicator hE)
        (extinctionError_sq_le_endpointIndicator_ae c P hP a n hh)
    _ = (sampleLaw P n).real E * B := by rw [integral_indicator_const B hE]; rfl
    _ ≤ Real.exp (-(c.pMin * c.gMin * Real.exp (-c.dMax) / 2 * n * h ^ c.kappa)) * B :=
      mul_le_mul_of_nonneg_right
        (endpointRiskZero_probability_le_explicit c P hP a n hh hhcap) (sq_nonneg _)
    _ = _ := by
      dsimp [B]
      rw [mul_pow, mul_pow, pow_two (Real.exp c.dMax), ← Real.exp_add]
      rw [show c.dMax + c.dMax = 2 * c.dMax by ring]
      ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
