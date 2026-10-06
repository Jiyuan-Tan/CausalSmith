module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.JumpEnumeration

/-!
# The event occupation measure of a finite-jump path

The event occupation measure records every ordered jump together with its
sample path. Its total mass is the expected number of events, and its mass on
a measurable time-sample set is the expected finite event sum of its indicator.
-/

@[expose] public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The event occupation measure sums the laws of the indexed jump time and
sample, restricted to paths with that jump index present. -/
noncomputable def Model.jumpOccupation (M : Model Ω μ) : Measure (ℝ × Ω) :=
  Measure.sum (fun k : ℕ =>
    Measure.map (fun ω : Ω => (M.jumpTime k ω, ω))
      (μ.restrict {ω | k < (M.eventTimes ω).card}))

private theorem Model.jumpOccupation_apply (M : Model Ω μ)
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S) :
    M.jumpOccupation S =
      ∫⁻ ω, ENNReal.ofReal
        (M.jumpIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
          M.horizon ω) ∂μ := by
  let A : ℕ → Set Ω := fun k =>
    {ω | k < (M.eventTimes ω).card ∧ (M.jumpTime k ω, ω) ∈ S}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    ((M.measurable_eventCard measurableSet_Ioi).inter
      (((M.measurable_jumpTime k).prodMk measurable_id) hS))
  have hmass (k : ℕ) :
      (Measure.map (fun ω : Ω => (M.jumpTime k ω, ω))
        (μ.restrict {ω | k < (M.eventTimes ω).card})) S = μ (A k) := by
    rw [Measure.map_apply (f := fun ω : Ω => (M.jumpTime k ω, ω))
      (by exact (M.measurable_jumpTime k).prodMk measurable_id) hS,
      Measure.restrict_apply]
    · congr 1
      ext ω
      simp [A, and_comm]
    · exact ((M.measurable_jumpTime k).prodMk measurable_id) hS
  have hpoint (ω : Ω) :
      (∑' k : ℕ, (A k).indicator (fun _ => (1 : ENNReal)) ω) =
        ENNReal.ofReal (M.jumpIntegral
          (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω) := by
    rw [tsum_eq_sum (s := Finset.range (M.eventTimes ω).card)]
    · rw [M.jumpIntegral_eq_sum_jumpTime]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        by_cases hs : (M.jumpTime k ω, ω) ∈ S <;>
          simp [A, Set.indicator, hk', hs]
      · intro k hk
        unfold Set.indicator
        split_ifs <;> norm_num
    · intro k hk
      simp [A, Set.indicator, Finset.mem_range] at hk ⊢
      omega
  calc
    M.jumpOccupation S = ∑' k : ℕ, μ (A k) := by
      rw [Model.jumpOccupation, Measure.sum_apply _ hS]
      simp_rw [hmass]
    _ = ∫⁻ ω, ∑' k : ℕ, (A k).indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
      rw [lintegral_tsum (fun k => (measurable_const.indicator (hA k)).aemeasurable)]
      congr 1
      funext k
      exact (lintegral_indicator_one (hA k)).symm
    _ = _ := by simp_rw [hpoint]

/-- Under a probability law and an integrable event count, the total mass of
the event occupation measure is finite. -/
theorem Model.jumpOccupation_finite (M : Model Ω μ) [IsProbabilityMeasure μ] :
    M.jumpOccupation univ < ⊤ := by
  have hmeas : Measurable (fun ω => ((M.eventTimes ω).card : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp M.measurable_eventCard
  have hcount : Integrable (fun ω => ((M.eventTimes ω).card : ℝ)) μ :=
    ((memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
      M.count_square_integrable).integrable one_le_two
  have heq : M.jumpOccupation univ =
      ∫⁻ ω, ENNReal.ofReal ((M.eventTimes ω).card : ℝ) ∂μ := by
    rw [M.jumpOccupation_apply univ MeasurableSet.univ]
    congr 1
    funext ω
    have hf : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) =
        M.eventTimes ω := Finset.filter_eq_self.mpr
          (fun t ht => (M.events_in_horizon ω t ht).2)
    simp [Model.jumpIntegral, hf]
  rw [heq]
  exact lt_top_iff_ne_top.mpr
    ((lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))).2 hcount)

/-- The mass of a measurable time-sample set under the event occupation
measure is the expected finite sum of its indicator over event times. [The
model and measurable set](hyp:M,S,hS), together with [integrability of its
event indicator](hyp:hjump), give [the occupation-mass identity](goal). -/
theorem Model.jumpOccupation_indicator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (hjump : Integrable
      (M.jumpIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) μ) :
    (M.jumpOccupation S).toReal =
      ∫ ω, M.jumpIntegral
        (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon ω ∂μ := by
  let F : Ω → ℝ := M.jumpIntegral
    (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon
  have hnonneg : ∀ ω, 0 ≤ F ω := by
    intro ω
    change 0 ≤ M.jumpIntegral
      (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω
    rw [M.jumpIntegral_eq_sum_jumpTime]
    apply Finset.sum_nonneg
    intro k hk
    unfold Set.indicator
    split_ifs <;> norm_num
  have hlintegral : ENNReal.ofReal (∫ ω, F ω ∂μ) = M.jumpOccupation S := by
    rw [M.jumpOccupation_apply S hS]
    exact ofReal_integral_eq_lintegral_ofReal hjump
      (Filter.Eventually.of_forall hnonneg)
  rw [← hlintegral]
  exact ENNReal.toReal_ofReal (integral_nonneg hnonneg)

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
