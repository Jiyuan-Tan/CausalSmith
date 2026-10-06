module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.JumpEnumeration

/-!
# Predictable cylinders and the counting-compensator generator identity

The predictable cylinders form a π-system. On each cylinder, conditional
intensity gives equality of expected event and compensator masses after
clipping its time interval to the counting process's finite horizon.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Left-endpoint predictable cylinders are closed under finite
intersections when the filtration increases with time. -/
theorem predictableCylinders_isPiSystem (ℱ : ℝ → MeasurableSpace Ω)
    (hℱ : Monotone ℱ) : IsPiSystem (predictableCylinders ℱ) := by
  intro S hS T hT _
  obtain ⟨a, b, B, hB, rfl⟩ := hS
  obtain ⟨c, d, C, hC, rfl⟩ := hT
  refine ⟨max a c, min b d, B ∩ C, ?_, ?_⟩
  · exact ((hℱ (le_max_left a c)) B hB).inter
      ((hℱ (le_max_right a c)) C hC)
  · rw [prod_inter_prod, Ioc_inter_Ioc]

/-- The expected event and intensity masses agree on every predictable
cylinder, including cylinders extending outside the counting horizon. [The
model and cylinder data](hyp:M,a,b,B), [left-endpoint measurability](hyp:hB),
and [integrability of both indicator integrals](hyp:hjump,henergy) give [the
cylinder compensation identity](goal). -/
theorem Model.predictable_cylinder_compensator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (a b : ℝ) (B : Set Ω)
    (hB : MeasurableSet[M.filtration a] B)
    (hjump : Integrable
      (M.jumpIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
        (fun _ => (1 : ℝ)) (t, ω)) M.horizon) μ)
    (henergy : Integrable
      (M.energyIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
        (fun _ => (1 : ℝ)) (t, ω)) M.horizon) μ) :
    (∫ ω, M.jumpIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
      (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω ∂μ) =
      ∫ ω, M.energyIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
        (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω ∂μ := by
  let u : ℝ := max 0 a
  let v : ℝ := min M.horizon b
  let F : Ω → ℝ := B.indicator (fun _ => 1)
  have htime (t : ℝ) (ht : 0 < t ∧ t ≤ M.horizon) :
      (a < t ∧ t ≤ b) ↔ (u < t ∧ t ≤ v) := by
    simp only [u, v, max_lt_iff, le_min_iff]
    exact ⟨fun h => ⟨⟨ht.1, h.1⟩, ⟨ht.2, h.2⟩⟩,
      fun h => ⟨h.1.2, h.2.2⟩⟩
  have hJump (ω : Ω) :
      M.jumpIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
        (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω =
      F ω * (((M.eventTimes ω).filter (fun t => u < t ∧ t ≤ v)).card : ℝ) := by
    classical
    have hfilter : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) =
        M.eventTimes ω := Finset.filter_eq_self.mpr
      (fun t ht => (M.events_in_horizon ω t ht).2)
    have heq (t : ℝ) (ht : t ∈ M.eventTimes ω) :
        (Ioc a b ×ˢ B).indicator (fun _ => (1 : ℝ)) (t, ω) =
          if u < t ∧ t ≤ v then F ω else 0 := by
      by_cases hb : ω ∈ B
      · simp [F, Set.indicator_apply, mem_prod, mem_Ioc, hb,
          htime t (M.events_in_horizon ω t ht)]
      · simp [F, mem_prod, hb]
    simp only [Model.jumpIntegral, hfilter]
    rw [Finset.sum_congr rfl heq]
    simp [Finset.sum_ite, Finset.sum_const, mul_comm]
  have hEnergy (ω : Ω) :
      M.energyIntegral (fun t ω => (Ioc a b ×ˢ B).indicator
        (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω =
      F ω * (∫ t in Ioc u v,
        M.atRisk t ω * M.intensity t ω ∂volume) := by
    have heq : (fun t : ℝ =>
        (Ioc a b ×ˢ B).indicator (fun _ => (1 : ℝ)) (t, ω) *
          (M.atRisk t ω * M.intensity t ω)) =
        (Ioc a b).indicator (fun t => F ω *
          (M.atRisk t ω * M.intensity t ω)) := by
      funext t
      by_cases hb : ω ∈ B
      · by_cases ht : t ∈ Ioc a b <;>
          simp [F, mem_prod, hb, ht]
      · simp [F, Set.indicator_apply, mem_prod, hb]
    change (∫ t in Ioc 0 M.horizon,
      (Ioc a b ×ˢ B).indicator (fun _ => (1 : ℝ)) (t, ω) *
        (M.atRisk t ω * M.intensity t ω) ∂volume) = _
    rw [heq, setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc,
      integral_const_mul]
  by_cases huv : u ≤ v
  · have hu0 : 0 ≤ u := le_max_left 0 a
    have hvT : v ≤ M.horizon := min_le_left _ _
    have hFu : Measurable[M.filtration u] F := by
      have haU : a ≤ u := le_max_right 0 a
      exact (measurable_const.indicator ((M.filtration_mono haU) B hB))
    have hbounded : ∃ C : ℝ, ∀ ω, |F ω| ≤ C := by
      refine ⟨1, ?_⟩
      intro ω
      by_cases hb : ω ∈ B <;> simp [F, hb]
    have hc : Integrable (fun ω => F ω *
        (((M.eventTimes ω).filter (fun t => u < t ∧ t ≤ v)).card : ℝ)) μ := by
      simpa only [← hJump] using hjump
    have hr : Integrable (fun ω => F ω *
        ∫ t in Ioc u v, M.atRisk t ω * M.intensity t ω ∂volume) μ := by
      simpa only [← hEnergy] using henergy
    simpa only [hJump, hEnergy] using
      M.conditional_intensity_increment u v F hu0 huv hvT hFu hbounded hc hr
  · have hzero : Ioc u v = (∅ : Set ℝ) := Ioc_eq_empty_iff.mpr (not_lt_of_ge (le_of_not_ge huv))
    have hcard (ω : Ω) : (M.eventTimes ω).filter (fun t => u < t ∧ t ≤ v) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ ht
      exact huv (le_trans (le_of_lt ht.1) ht.2)
    simp [hJump, hEnergy, hzero, hcard]

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
