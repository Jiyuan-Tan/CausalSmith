module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Basic

/-!
# Finite-jump square and cross-term identities

These pathwise identities reduce the counting integral's square to finite-sum
algebra and the continuous compensator square identity.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The square of a finite event sum is the sum of squared event payoffs plus
twice every event payoff times the sum over strictly earlier events. [The
model, payoff, and path](hyp:M,H,ω) give [the finite-jump square expansion](goal). -/
theorem Model.jumpIntegral_square (M : Model Ω μ) (H : ℝ → Ω → ℝ) (ω : Ω) :
    (M.jumpIntegral H M.horizon ω) ^ 2 =
      M.jumpIntegral (fun t ω => (H t ω) ^ 2) M.horizon ω +
      M.jumpIntegral (fun t ω =>
        2 * H t ω *
          (∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω))
        M.horizon ω := by
  /- Order the finite set of event times. Every unordered pair contributes
     twice, and has exactly one strictly later endpoint. -/
  classical
  have hs (s : Finset ℝ) (f : ℝ → ℝ) :
      (∑ t ∈ s, f t) ^ 2 =
        (∑ t ∈ s, (f t) ^ 2) +
          ∑ t ∈ s, 2 * f t * (∑ u ∈ s.filter (fun u => u < t), f u) := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | @insert a s ha ih =>
      have han : a ∉ s := fun h => (lt_irrefl a) (ha a h)
      have hlt (t : ℝ) (ht : t ∈ s) : ¬ a < t := (ha t ht).not_gt
      simp only [Finset.sum_insert han, Finset.filter_insert] 
      simp only [if_neg (lt_irrefl a)]
      have hfilt : s.filter (fun u => u < a) = s :=
        Finset.filter_true_of_mem (fun u hu => ha u hu)
      simp only [hfilt]
      have hsum :
          (∑ t ∈ s, 2 * f t *
            ∑ u ∈ (if a < t then insert a (s.filter (fun u => u < t))
              else s.filter (fun u => u < t)), f u) =
          ∑ t ∈ s, 2 * f t * ∑ u ∈ s.filter (fun u => u < t), f u := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [if_neg (hlt t ht)]
      rw [hsum]
      nlinarith [ih]
  have hfin : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) = M.eventTimes ω :=
    Finset.filter_true_of_mem (fun t ht => (M.events_in_horizon ω t ht).2)
  simpa [Model.jumpIntegral, hfin] using hs (M.eventTimes ω) (fun t => H t ω)

/-- Twice the product of the event sum and the compensator integral splits
at each event into a past-compensator jump term and a past-event rate term. -/
theorem Model.jump_energy_cross (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : M.Predictable H)
    (hbound : ∃ C : ℝ, ∀ t ω, |H t ω| ≤ C) (ω : Ω) :
    2 * M.jumpIntegral H M.horizon ω * M.energyIntegral H M.horizon ω =
      M.jumpIntegral (fun t ω => 2 * H t ω * M.energyIntegral H t ω)
        M.horizon ω +
      M.energyIntegral (fun t ω => 2 * H t ω *
        (∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω))
        M.horizon ω := by
  /- Expand the finite jump sum. For each event s split the compensator
     integral into (0,s] and (s,T]. Exchange the finite sum and the latter
     integral; endpoints have zero Lebesgue measure. -/
  classical
  let E := M.eventTimes ω
  let r : ℝ → ℝ := fun t => M.atRisk t ω * M.intensity t ω
  let f : ℝ → ℝ := fun t => H t ω * r t
  have hHjoint : Measurable (fun p : ℝ × Ω => H p.1 p.2) := by
    apply Measurable.le ?_ hH
    apply (MeasurableSpace.generateFrom_le_iff _).mpr
    rintro S ⟨a, b, B, hB, rfl⟩
    exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  have hHm : Measurable (fun t => H t ω) :=
    hHjoint.comp (measurable_id.prodMk measurable_const)
  have hrm : Measurable r :=
    (M.atRisk_joint_measurable.comp (measurable_id.prodMk measurable_const)).mul
      (M.intensity_joint_measurable.comp (measurable_id.prodMk measurable_const))
  obtain ⟨C, hC⟩ := hbound
  have hf : IntegrableOn f (Ioc 0 M.horizon) volume := by
    apply Integrable.mono' ((M.rate_integrable ω).abs.const_mul |C|)
    · exact (hHm.mul hrm).aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, f, abs_mul]
      simpa [r, abs_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right ((hC t ω).trans (le_abs_self C)) (abs_nonneg (r t))
  have hsplit (s : ℝ) (hs : s ∈ E) :
      (∫ t in Ioc 0 M.horizon, f t ∂volume) =
        (∫ t in Ioc 0 s, f t ∂volume) +
          ∫ t in Ioc s M.horizon, f t ∂volume := by
    have hs0 := (M.events_in_horizon ω s hs).1.le
    have hsT := (M.events_in_horizon ω s hs).2
    have hdisj : Disjoint (Ioc 0 s) (Ioc s M.horizon) := by
      apply Set.disjoint_left.mpr
      intro t ht hu
      exact (not_lt_of_ge ht.2) hu.1
    rw [← Ioc_union_Ioc_eq_Ioc hs0 hsT,
      setIntegral_union hdisj measurableSet_Ioc
        (hf.mono_set (Ioc_subset_Ioc_right hsT))
        (hf.mono_set (Ioc_subset_Ioc_left hs0))]
  let g : ℝ → ℝ → ℝ := fun s t => if s < t then 2 * H s ω * f t else 0
  have hg (s : ℝ) : IntegrableOn (g s) (Ioc 0 M.horizon) volume := by
    change Integrable ((Ioi s).indicator (fun t => 2 * H s ω * f t))
      (volume.restrict (Ioc 0 M.horizon))
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((hf.const_mul (2 * H s ω)).mono_measure Measure.restrict_le_self)
  have htail (s : ℝ) (hs : s ∈ E) :
      (∫ t in Ioc 0 M.horizon, g s t ∂volume) =
        2 * H s ω * ∫ t in Ioc s M.horizon, f t ∂volume := by
    have hs0 := (M.events_in_horizon ω s hs).1.le
    have hset : Ioc 0 M.horizon ∩ Ioi s = Ioc s M.horizon := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, htT⟩, hst⟩
        exact ⟨hst, htT⟩
      · rintro ⟨hst, htT⟩
        exact ⟨⟨lt_of_le_of_lt hs0 hst, htT⟩, hst⟩
    calc
      (∫ t in Ioc 0 M.horizon, g s t ∂volume) =
          ∫ t in Ioc 0 M.horizon,
            (Ioi s).indicator (fun t => 2 * H s ω * f t) t ∂volume := by
              congr 1
      _ = ∫ t in Ioc s M.horizon, 2 * H s ω * f t ∂volume := by
        rw [setIntegral_indicator measurableSet_Ioi, hset]
      _ = _ := by rw [integral_const_mul]
  have hsum :
      (∫ t in Ioc 0 M.horizon, ∑ s ∈ E, g s t ∂volume) =
        ∑ s ∈ E, ∫ t in Ioc 0 M.horizon, g s t ∂volume :=
    integral_finsetSum E (fun s _ => hg s)
  have hpoint (t : ℝ) :
      (∑ s ∈ E, g s t) =
        2 * H t ω * (∑ s ∈ E.filter (fun s => s < t), H s ω) * r t := by
    rw [Finset.sum_filter]
    calc
      (∑ s ∈ E, g s t) =
          ∑ s ∈ E, 2 * H t ω * (if s < t then H s ω else 0) * r t := by
            apply Finset.sum_congr rfl
            intro s hs
            simp only [g]
            split_ifs <;> simp [f] <;> ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  have hfin : E.filter (fun t => t ≤ M.horizon) = E :=
    Finset.filter_true_of_mem (fun t ht => (M.events_in_horizon ω t ht).2)
  dsimp only [Model.jumpIntegral, Model.energyIntegral]
  change (2 * (∑ s ∈ E.filter (fun s => s ≤ M.horizon), H s ω) *
    ∫ t in Ioc 0 M.horizon, f t ∂volume) =
    (∑ s ∈ E.filter (fun s => s ≤ M.horizon),
      2 * H s ω * ∫ t in Ioc 0 s, f t ∂volume) +
    ∫ t in Ioc 0 M.horizon,
      2 * H t ω * (∑ s ∈ E.filter (fun s => s < t), H s ω) * r t ∂volume
  rw [hfin]
  calc
    2 * (∑ s ∈ E, H s ω) * (∫ t in Ioc 0 M.horizon, f t ∂volume) =
        ∑ s ∈ E, 2 * H s ω * ∫ t in Ioc 0 M.horizon, f t ∂volume := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ s ∈ E, ((2 * H s ω * ∫ t in Ioc 0 s, f t ∂volume) +
            (2 * H s ω * ∫ t in Ioc s M.horizon, f t ∂volume)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hsplit s hs]
          ring
    _ = (∑ s ∈ E, 2 * H s ω * ∫ t in Ioc 0 s, f t ∂volume) +
        ∫ t in Ioc 0 M.horizon,
          2 * H t ω * (∑ s ∈ E.filter (fun s => s < t), H s ω) * r t ∂volume := by
          rw [Finset.sum_add_distrib]
          congr 1
          calc
            (∑ s ∈ E, 2 * H s ω * ∫ t in Ioc s M.horizon, f t ∂volume) =
                ∑ s ∈ E, ∫ t in Ioc 0 M.horizon, g s t ∂volume := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  exact (htail s hs).symm
            _ = ∫ t in Ioc 0 M.horizon, ∑ s ∈ E, g s t ∂volume := hsum.symm
            _ = _ := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro t ht
              exact hpoint t

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
