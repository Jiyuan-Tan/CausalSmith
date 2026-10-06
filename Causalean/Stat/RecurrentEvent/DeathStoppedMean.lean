module
public import Causalean.Stat.RecurrentEvent.PoissonCampbell
public import Causalean.Stat.RecurrentEvent.TailRetention

/-!
# Mean recurrence count stopped by independent death

A finite Poisson recurrence sample is stopped strictly before independent
death and the fixed horizon, without censoring.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M) determines [the expected count of
primitive Poisson recurrence points before independent death and the fixed
horizon](goal), without censoring. -/
noncomputable def Model.deathStoppedCountMean (M : Model A X) : ℝ≥0∞ :=
  letI := M.pointProb
  ∫⁻ z,
    ∑ i : Fin z.1.1,
      if M.time (z.1.2 i) < z.2 ∧ M.time (z.1.2 i) < M.horizon
      then (1 : ℝ≥0∞) else 0
    ∂((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      M.pointLaw M.poissonRate).prod M.deathLaw)

/-- [A recurrent-event model](hyp:M) has [an independently death-stopped
Poisson recurrence mean equal to the integral of death survival times
recurrence intensity over the fixed horizon](goal). -/
theorem Model.death_stopped_poisson_mean (M : Model A X) :
    M.deathStoppedCountMean =
      ∫⁻ t in Ico (0 : ℝ) M.horizon,
        M.deathLaw (Ici t) * (M.intensity t : ℝ≥0∞) ∂volume := by
  letI := M.pointProb
  letI := M.deathProb
  let μ := Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
    M.pointLaw M.poissonRate
  let F : Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X × ℝ →
      ℝ≥0∞ := fun z =>
    ∑ i : Fin z.1.1,
      if M.time (z.1.2 i) < z.2 ∧ M.time (z.1.2 i) < M.horizon
      then 1 else 0
  have hF : Measurable F := by
    have he (n : ℕ) : MeasurableEmbedding
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
          (X := X) n) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y h
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      · exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_fixedSizeEmbed n
      · intro s hs
        change @MeasurableSet _
          (⨅ m, (inferInstance : MeasurableSpace (Fin m → X)).map (Sigma.mk m))
          (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed n '' s)
        rw [MeasurableSpace.measurableSet_iInf]
        intro m
        change MeasurableSet
          ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
            (X := X) m) ⁻¹'
          ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
            (X := X) n) '' s))
        by_cases h : m = n
        · subst m
          rw [Set.preimage_image_eq s (fun x y h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
          exact hs
        · convert MeasurableSet.empty using 1
          ext x
          simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
          rintro ⟨y, _, heq⟩
          exact h (congrArg Sigma.fst heq).symm
    intro t ht
    have hset : F ⁻¹' t = ⋃ n : ℕ,
        (Prod.map (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
          (X := X) n) id) ''
          {z : (Fin n → X) × ℝ | F (⟨n, z.1⟩, z.2) ∈ t} := by
      ext ⟨⟨n, x⟩, d⟩
      constructor
      · intro ht
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        exact ⟨(x, d), ht, rfl⟩
      · intro ht
        obtain ⟨m, ⟨y, e⟩, hy, hz⟩ := Set.mem_iUnion.mp ht
        cases hz
        exact hy
    rw [hset]
    apply MeasurableSet.iUnion
    intro n
    apply ((he n).prodMap MeasurableEmbedding.id).measurableSet_image.mpr
    have hn : Measurable (fun z : (Fin n → X) × ℝ => F (⟨n, z.1⟩, z.2)) := by
      change Measurable (fun z : (Fin n → X) × ℝ =>
        ∑ i : Fin n, if M.time (z.1 i) < z.2 ∧ M.time (z.1 i) < M.horizon
          then (1 : ℝ≥0∞) else 0)
      apply Finset.measurable_sum
      intro i hi
      apply Measurable.ite
      · exact (measurableSet_lt
          (M.measurable_time.comp ((measurable_pi_apply i).comp measurable_fst))
          measurable_snd).inter
          (measurableSet_lt
            (M.measurable_time.comp ((measurable_pi_apply i).comp measurable_fst))
            measurable_const)
      · exact measurable_const
      · exact measurable_const
    exact hn ht
  change (∫⁻ z, F z ∂μ.prod M.deathLaw) = _
  rw [lintegral_prod_symm' F hF]
  calc
    (∫⁻ d, ∫⁻ s, F (s, d) ∂μ ∂M.deathLaw) =
        ∫⁻ d, ∫⁻ t in Ico (0 : ℝ) M.horizon,
          if t < d then (M.intensity t : ℝ≥0∞) else 0 ∂volume ∂M.deathLaw := by
      apply lintegral_congr
      intro d
      exact M.poisson_count_before_death d
    _ = ∫⁻ t in Ico (0 : ℝ) M.horizon,
          ∫⁻ d, if t < d then (M.intensity t : ℝ≥0∞) else 0
            ∂M.deathLaw ∂volume := by
      have hG : Measurable (fun z : ℝ × ℝ =>
          if z.2 < z.1 then (M.intensity z.2 : ℝ≥0∞) else 0) := by
        exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
          (M.measurable_intensity.coe_nnreal_ennreal.comp measurable_snd) measurable_const
      exact lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ t in Ico (0 : ℝ) M.horizon,
          M.deathLaw (Ioi t) * (M.intensity t : ℝ≥0∞) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ico
      intro t ht
      change (∫⁻ d, (Ioi t).indicator (fun _ => (M.intensity t : ℝ≥0∞)) d
        ∂M.deathLaw) = _
      rw [lintegral_indicator_const measurableSet_Ioi]
      exact mul_comm _ _
    _ = ∫⁻ t in Ico (0 : ℝ) M.horizon,
          M.deathLaw (Ici t) * (M.intensity t : ℝ≥0∞) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_measure_Ioi_eq_Ici M.deathLaw)] with t ht
      rw [ht]

end Causalean.Stat.RecurrentEvent
