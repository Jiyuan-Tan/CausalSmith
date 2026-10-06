module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.FullSample

/-!
# No common recurrent-event jumps in independent subjects

Absolutely continuous conditional intensities imply that a subject has no jump
at any fixed deterministic time. Independent coordinate paths then have disjoint
finite stopped event sets almost surely. Independence of stochastic integrals
with a shared full-sample integrand is neither asserted nor used.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The guarded enumeration covers the finite event set. -/
private theorem Model.eventTimes_eq_image (M : Model Ω μ) (ω : Ω) :
    (Finset.range (M.eventTimes ω).card).image (fun k => M.jumpTime k ω) =
      M.eventTimes ω := by
  classical
  have hsub : (Finset.range (M.eventTimes ω).card).image
      (fun k => M.jumpTime k ω) ⊆ M.eventTimes ω := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact M.jumpTime_mem k ω (Finset.mem_range.mp hk)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj heq
  exact M.jumpTime_injective ω i j (Finset.mem_range.mp hi)
    (Finset.mem_range.mp hj) heq

/-- A simple finite-jump process with an absolutely continuous conditional
intensity has probability zero of a jump at a fixed deterministic time. -/
theorem Model.deterministic_jump_null (M : Model Ω μ)
    [IsProbabilityMeasure μ] (t : ℝ) :
    ∀ᵐ ω ∂μ, t ∉ M.eventTimes ω := by
  /- Prove the predictable measurability of the deterministic time singleton,
     apply occupation agreement, and use its zero Lebesgue mass. Equivalently,
     bound the expected count on shrinking left intervals by rateBound times
     interval length, using the bounded conditional increment test F=1.
     `measurable_jumpTime` and its finite enumeration establish measurability
     of the event. This is diffuse jump mass, not an assumed no-ties premise. -/
  classical
  have hfst : Measurable[predictableSpace M.filtration] (Prod.fst : ℝ × Ω → ℝ) := by
    change @Measurable _ _ (predictableSpace M.filtration) (borel ℝ) Prod.fst
    rw [borel_eq_generateFrom_Ioc ℝ]
    apply @measurable_generateFrom (ℝ × Ω) ℝ (predictableSpace M.filtration)
    rintro A ⟨a, b, hab, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, univ,
      MeasurableSet.univ, by ext p; simp⟩
  let A : Set (ℝ × Ω) := {t} ×ˢ univ
  have hA : MeasurableSet A := (measurableSet_singleton t).prod MeasurableSet.univ
  have hAp : MeasurableSet[predictableSpace M.filtration] A := by
    convert hfst (measurableSet_singleton t) using 1
    ext p
    simp [A]
  have hzero : M.jumpOccupation A = 0 := by
    rw [M.occupation_agree A hAp]
    apply withDensity_absolutelyContinuous _ _
    simp [A, Measure.prod_prod]
  have hkzero (k : ℕ) : μ {ω | k < (M.eventTimes ω).card ∧ M.jumpTime k ω = t} = 0 := by
    have h := (Measure.sum_apply_eq_zero.mp hzero) k
    rw [Measure.map_apply (f := fun ω => (M.jumpTime k ω, ω))
      ((M.measurable_jumpTime k).prodMk measurable_id) hA,
      Measure.restrict_apply] at h
    · convert h using 1
      congr 1
      ext ω
      simp [A, and_comm]
    · exact ((M.measurable_jumpTime k).prodMk measurable_id) hA
  have hk (k : ℕ) : ∀ᵐ ω ∂μ, ¬ (k < (M.eventTimes ω).card ∧ M.jumpTime k ω = t) :=
    ae_iff.mpr (by simpa using hkzero k)
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro ht
  rw [← M.eventTimes_eq_image ω] at ht
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp ht
  exact hω k ⟨Finset.mem_range.mp hk, heq⟩

/-- A measurable random time independent of each enumerated event time and
the event count almost surely avoids every event of a process with an
absolutely continuous conditional intensity. -/
theorem Model.independent_time_avoids_events (M : Model Ω μ)
    [IsProbabilityMeasure μ] (τ : Ω → ℝ) (hτ : Measurable τ)
    (hindependent : ∀ k : ℕ, ProbabilityTheory.IndepFun τ
      (fun ω => ((M.eventTimes ω).card, M.jumpTime k ω)) μ) :
    ∀ᵐ ω ∂μ, τ ω ∉ M.eventTimes ω := by
  /- For each k use IndepFun.map_prod_eq_prod_map_map on τ and the measurable
     pair (count, jumpTime k). The bad set is {p | k < p.2.1 ∧ p.1 = p.2.2}.
     For every fixed t, its second-coordinate section is null by
     deterministic_jump_null and jumpTime_mem. Fubini makes the product bad
     set null. Pull back through the joint law and intersect over k. The
     existing injective enumeration has the same cardinality as eventTimes,
     hence covers every event. Out-of-range default jumpTime values must
     remain guarded by k<count: they can have atoms even in a diffuse model.
     Independence concerns event paths only, never the full-sample payoff. -/
  classical
  have hk (k : ℕ) : ∀ᵐ ω ∂μ,
      ¬ (k < (M.eventTimes ω).card ∧ τ ω = M.jumpTime k ω) := by
    let f : Ω → ℕ × ℝ := fun ω => ((M.eventTimes ω).card, M.jumpTime k ω)
    have hf : Measurable f := M.measurable_eventCard.prodMk (M.measurable_jumpTime k)
    let B : Set (ℝ × (ℕ × ℝ)) := {p | k < p.2.1 ∧ p.1 = p.2.2}
    have hB : MeasurableSet B :=
      (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
        (measurableSet_eq_fun measurable_fst (measurable_snd.comp measurable_snd))
    have hsection (t : ℝ) : ∀ᵐ y ∂μ.map f, (t, y) ∉ B := by
      apply (ae_map_iff hf.aemeasurable (hB.preimage measurable_prodMk_left).compl).mpr
      filter_upwards [M.deterministic_jump_null t] with ω hω
      rintro ⟨hcount, heq⟩
      apply hω
      change t = M.jumpTime k ω at heq
      rw [heq]
      exact M.jumpTime_mem k ω hcount
    have hprod : ∀ᵐ p ∂(μ.map τ).prod (μ.map f), p ∉ B :=
      (Measure.ae_prod_iff_ae_ae hB.compl).mpr (Filter.Eventually.of_forall hsection)
    rw [← (hindependent k).map_prod_eq_prod_map_map hτ.aemeasurable hf.aemeasurable] at hprod
    exact ae_of_ae_map (hτ.prodMk hf).aemeasurable hprod
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro ht
  rw [← M.eventTimes_eq_image ω] at ht
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp ht
  exact hω k ⟨Finset.mem_range.mp hk, heq.symm⟩

/-- Distinct subjects in the iid finite sample almost surely have no common
stopped recurrent-event time, as a consequence of conditional intensity and
independence of their coordinate paths. [The sample model](hyp:S), [the two
indices](hyp:i,j), and [their distinctness](hyp:hij) give [almost-sure
disjointness of their stopped jumps](goal). -/
theorem SampleModel.no_common_jumps {n : ℕ} (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ] (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ x ∂finiteSampleLaw n μ,
      Disjoint ((S.process i).eventTimes x) ((S.process j).eventTimes x) := by
  /- Apply independent_time_avoids_events to each i jumpTime and process j.
     The maps (eventCard, jumpTime k) depend only on their subject coordinate:
     process_events identifies their event sets, and jumpTime is defined from
     the filtered counts. For a measurable coordinate factorization, compose
     these already-measurable maps with a constant sample updated at i or j
     (the probability law supplies Nonempty Ω). Use iIndepFun_pi and IndepFun.comp
     for the two coordinate maps. Intersect over k, then use the finite
     enumeration to obtain disjointness. No independence of H is required. -/
  classical
  let ω₀ : Ω := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  let lift : Fin n → Ω → (Fin n → Ω) :=
    fun a ω => Function.update (fun _ => ω₀) a ω
  have hlift (a : Fin n) : Measurable (lift a) := by
    apply measurable_pi_lambda
    intro b
    by_cases hab : b = a
    · subst b
      intro A hA
      simpa [lift] using hA
    · simp [lift, Function.update_of_ne hab]
  have hevents (a : Fin n) (x : Fin n → Ω) :
      (S.process a).eventTimes (lift a (x a)) = (S.process a).eventTimes x := by
    simp [S.process_events, lift]
  have hjump (a : Fin n) (k : ℕ) (x : Fin n → Ω) :
      (S.process a).jumpTime k (lift a (x a)) = (S.process a).jumpTime k x := by
    unfold Model.jumpTime Model.count
    rw [hevents]
  have hcoords : ProbabilityTheory.iIndepFun
      (fun a : Fin n => fun x : Fin n → Ω => x a) (finiteSampleLaw n μ) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have havoid (k : ℕ) : ∀ᵐ x ∂finiteSampleLaw n μ,
      (S.process i).jumpTime k x ∉ (S.process j).eventTimes x := by
    apply (S.process j).independent_time_avoids_events
      ((S.process i).jumpTime k) ((S.process i).measurable_jumpTime k)
    intro l
    have h := (hcoords.indepFun hij).comp
      (((S.process i).measurable_jumpTime k).comp (hlift i))
      ((((S.process j).measurable_eventCard).prodMk
        ((S.process j).measurable_jumpTime l)).comp (hlift j))
    simpa only [Function.comp_def, hevents, hjump] using h
  filter_upwards [ae_all_iff.mpr havoid] with x hx
  apply Finset.disjoint_left.mpr
  intro t hi hj
  rw [← (S.process i).eventTimes_eq_image x] at hi
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hi
  exact hx k (heq.symm ▸ hj)

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
