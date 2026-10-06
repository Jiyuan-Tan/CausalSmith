module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessIntegrand

/-! # Observed-history adapter for the death counting process -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- A canonical pair with the same arm-specific risk and death-count paths as
an observed record through time one. -/
def observedDeathPair (a : Arm) (o : ObsHistory) : ℝ × ℝ :=
  if o.treatment = a then
    if o.deathInd then (o.exit + 1, o.exit) else (o.exit, o.exit + 1)
  else (0, 1)

lemma measurable_observedDeathPair (a : Arm) : Measurable (observedDeathPair a) := by
  unfold observedDeathPair
  apply Measurable.ite
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const)
  · apply Measurable.ite
      (measurableSet_eq_fun measurable_obsHistory_deathInd measurable_const)
    · exact ((measurable_obsHistory_exit.add measurable_const).prodMk
        measurable_obsHistory_exit)
    · exact measurable_obsHistory_exit.prodMk
        (measurable_obsHistory_exit.add measurable_const)
  · exact measurable_const

def observedDeathSample (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) :
    Causalean.Stat.RecurrentEvent.CountingProcess.Sample n :=
  fun i => observedDeathPair a (s i)

/-- Convert a capped canonical failure/death pair into its synthetic observed
record. Strict comparison matches the canonical counted-event convention. -/
noncomputable def stoppedSyntheticDeathPair (q : ℝ × ℝ) : ℝ × ℝ :=
  let e := min q.1 q.2
  if q.2 < q.1 then (e + 1, e) else (e, e + 1)

lemma measurable_stoppedSyntheticDeathPair : Measurable stoppedSyntheticDeathPair := by
  unfold stoppedSyntheticDeathPair
  apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
  · exact (((measurable_fst.min measurable_snd).add measurable_const).prodMk
      (measurable_fst.min measurable_snd))
  · exact (measurable_fst.min measurable_snd).prodMk
      ((measurable_fst.min measurable_snd).add measurable_const)

/-- Away from a death/follow-up tie, the latent observed record and the
stopped canonical pair give the same synthetic record. -/
lemma observedDeathPair_eq_stoppedSyntheticDeathPair (a : Arm)
    (z : LatentSubject) (hd0 : 0 ≤ z.death a)
    (hne : z.treatment = a → z.death a ≠ censorHorizon z a) :
    observedDeathPair a (observe z) = stoppedSyntheticDeathPair
      (armDeathFailureTime a z, min (z.death a) 1) := by
  have hc0 : 0 ≤ censorHorizon z a := by
    unfold censorHorizon
    split_ifs <;> simp
  have hc1 : censorHorizon z a ≤ 1 := by
    unfold censorHorizon
    split_ifs <;> simp
  by_cases ha : z.treatment = a
  · have hobs : (observe z).treatment = a := by simp [observe, ha]
    rw [show armDeathFailureTime a z = censorHorizon z a by simp [armDeathFailureTime, ha]]
    have hne' := hne ha
    by_cases hdc : z.death a < censorHorizon z a
    · have hd1 : z.death a ≤ 1 := le_trans hdc.le hc1
      simp [observedDeathPair, stoppedSyntheticDeathPair, observe, ha, hobs,
        hdc, hdc.le, min_eq_left hd1]
    · have hcd : censorHorizon z a < z.death a := lt_of_le_of_ne
        (le_of_not_gt hdc) hne'.symm
      have hcap : censorHorizon z a ≤ min (z.death a) 1 :=
        le_min hcd.le hc1
      have hn1 : ¬(1 : ℝ) < censorHorizon z a := not_lt_of_ge hc1
      simp [observedDeathPair, stoppedSyntheticDeathPair, observe, ha, hobs,
        hdc, not_le_of_gt hcd, min_eq_right hcd.le, min_eq_left hcap, hn1]
  · have hobs : (observe z).treatment ≠ a := by simp [observe, ha]
    have hcap0 : 0 ≤ min (z.death a) 1 := le_min hd0 (by norm_num)
    simp [observedDeathPair, stoppedSyntheticDeathPair, observe, ha, hobs,
      armDeathFailureTime, hcap0, hd0]

/-- Assigned-arm follow-up and death have no ties under the paper atoms. -/
lemma armDeathFailureTime_ne_death_ae (P : SubjectLaw)
    (hDeath : DeathHazard P) (hRandom : RandomAssignment P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    ∀ᵐ z ∂P.latent, armDeathFailureTime a z ≠ z.death a := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure ((observedLaw P).map (observedDeathPair a)) :=
    Measure.isProbabilityMeasure_map (measurable_observedDeathPair a).aemeasurable
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    Measure.isProbabilityMeasure_map (measurable_armDeathFailureTime a).aemeasurable
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure
      ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)) := inferInstance
  letI : IsProbabilityMeasure
      (((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
        (fun q => stoppedSyntheticDeathPair (q.1, min q.2 1))) :=
    Measure.isProbabilityMeasure_map
      (measurable_stoppedSyntheticDeathPair.comp
        (measurable_fst.prodMk (measurable_snd.min measurable_const))).aemeasurable
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    Measure.isProbabilityMeasure_map
      (measurable_armDeathFailureTime a).aemeasurable
  letI : IsProbabilityMeasure (armDeathEventLaw P a) :=
    Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  letI : NullSingletonClass (armDeathEventLaw P a) :=
    ⟨fun x => (hDeath.2.2.1 a) (measure_singleton x)⟩
  have hprod : ∀ᵐ q ∂(armDeathFailureLaw P a).prod (armDeathEventLaw P a),
      q.1 ≠ q.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
    filter_upwards [] with f
    filter_upwards [(armDeathEventLaw P a).ae_ne f] with d hd
    exact hd.symm
  have hmap := armDeath_pair_map_eq_prod P hRandom hCensor a
  rw [← hmap] at hprod
  exact (ae_map_iff
    ((measurable_armDeathFailureTime a).prodMk
      (measurable_latentSubject_death a)).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).1 hprod

lemma latentDeath_nonneg_ae (P : SubjectLaw) (hDeath : DeathHazard P) (a : Arm) :
    ∀ᵐ z ∂P.latent, 0 ≤ z.death a := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have htail : P.latent.real {z | (0 : ℝ) ≤ z.death a} = 1 := by
    simpa [survival] using hDeath.2.2.2.1 a 0 (by norm_num)
  have hmeas : MeasurableSet {z : LatentSubject | (0 : ℝ) ≤ z.death a} :=
    measurableSet_le measurable_const (measurable_latentSubject_death a)
  have hcomp := measureReal_compl (μ := P.latent) hmeas
  have huniv : P.latent.real Set.univ = 1 := by simp [Measure.real, P.prob]
  rw [htail, huniv] at hcomp
  have hzero : P.latent {z | ¬(0 : ℝ) ≤ z.death a} = 0 := by
    rw [← compl_setOf]
    exact (measureReal_eq_zero_iff).mp (by linarith [hcomp])
  exact ae_iff.mpr hzero

lemma observedDeathPair_eq_stoppedSyntheticDeathPair_ae (P : SubjectLaw)
    (hDeath : DeathHazard P) (hRandom : RandomAssignment P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    (fun z => observedDeathPair a (observe z)) =ᵐ[P.latent]
      (fun z => stoppedSyntheticDeathPair
        (armDeathFailureTime a z, min (z.death a) 1)) := by
  filter_upwards [latentDeath_nonneg_ae P hDeath a,
    armDeathFailureTime_ne_death_ae P hDeath hRandom hCensor a] with z hd hne
  apply observedDeathPair_eq_stoppedSyntheticDeathPair a z hd
  intro ha
  simpa [armDeathFailureTime, ha] using hne.symm

/-- The one-subject synthetic observed record has the stopped reference-pair
pushforward law. -/
lemma observedDeathPair_map_eq_reference (P : SubjectLaw)
    (hDeath : DeathHazard P) (hRandom : RandomAssignment P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    P.latent.map (fun z => observedDeathPair a (observe z)) =
      ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
        (fun q => stoppedSyntheticDeathPair (q.1, min q.2 1)) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  calc
    _ = P.latent.map (fun z => stoppedSyntheticDeathPair
        (armDeathFailureTime a z, min (z.death a) 1)) :=
      Measure.map_congr
        (observedDeathPair_eq_stoppedSyntheticDeathPair_ae
          P hDeath hRandom hCensor a)
    _ = (P.latent.map (fun z =>
        (armDeathFailureTime a z, min (z.death a) 1))).map
          stoppedSyntheticDeathPair := by
      rw [Measure.map_map measurable_stoppedSyntheticDeathPair (by fun_prop)]
      rfl
    _ = (((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
        (fun q : ℝ × ℝ => (q.1, min q.2 1))).map
          stoppedSyntheticDeathPair := by
      rw [armDeath_stopped_pair_map_eq_reference P hRandom hCensor a]
    _ = _ := by
      rw [Measure.map_map measurable_stoppedSyntheticDeathPair (by fun_prop)]
      rfl

noncomputable def referenceStoppedSyntheticSample {n : ℕ}
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) :
    Causalean.Stat.RecurrentEvent.CountingProcess.Sample n :=
  fun i => stoppedSyntheticDeathPair ((x i).1, min (x i).2 1)

lemma measurable_referenceStoppedSyntheticSample {n : ℕ} :
    Measurable (referenceStoppedSyntheticSample (n := n)) := by
  exact measurable_pi_lambda _ (fun i =>
    measurable_stoppedSyntheticDeathPair.comp
      ((measurable_pi_apply i).fst.prodMk
        ((measurable_pi_apply i).snd.min measurable_const)))

/-- Finite iid observed samples transport to the stopped synthetic reference
counting-process sample. -/
lemma observedDeathSample_map_eq_reference {n : ℕ} (P : SubjectLaw)
    (hDeath : DeathHazard P) (hRandom : RandomAssignment P)
    (hCensor : IndependentCensoring P) (a : Arm) :
    (sampleLaw P n).map (observedDeathSample a) =
      (Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw n
        (armDeathFailureLaw P a) (referenceDeathLaw P a)).map
          referenceStoppedSyntheticSample := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure ((observedLaw P).map (observedDeathPair a)) :=
    Measure.isProbabilityMeasure_map (measurable_observedDeathPair a).aemeasurable
  letI : IsProbabilityMeasure (armDeathFailureLaw P a) :=
    Measure.isProbabilityMeasure_map (measurable_armDeathFailureTime a).aemeasurable
  letI : IsProbabilityMeasure (referenceDeathLaw P a) := inferInstance
  letI : IsProbabilityMeasure
      ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)) := inferInstance
  letI : IsProbabilityMeasure
      (((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
        (fun q => stoppedSyntheticDeathPair (q.1, min q.2 1))) :=
    Measure.isProbabilityMeasure_map
      (measurable_stoppedSyntheticDeathPair.comp
        (measurable_fst.prodMk (measurable_snd.min measurable_const))).aemeasurable
  unfold sampleLaw Causalean.Stat.RecurrentEvent.CountingProcess.sampleLaw
  calc
    _ = Measure.pi (fun _ : Fin n =>
        (observedLaw P).map (observedDeathPair a)) := by
      exact Measure.pi_map_pi
        (μ := fun _ : Fin n => observedLaw P)
        (f := fun _ => observedDeathPair a)
        (fun _ => (measurable_observedDeathPair a).aemeasurable)
    _ = Measure.pi (fun _ : Fin n =>
        ((armDeathFailureLaw P a).prod (referenceDeathLaw P a)).map
          (fun q => stoppedSyntheticDeathPair (q.1, min q.2 1))) := by
      congr 1
      funext i
      rw [observedLaw, Measure.map_map (measurable_observedDeathPair a)
        measurable_observe]
      exact observedDeathPair_map_eq_reference P hDeath hRandom hCensor a
    _ = _ := by
      exact (Measure.pi_map_pi
        (μ := fun _ : Fin n =>
          (armDeathFailureLaw P a).prod (referenceDeathLaw P a))
        (f := fun _ q => stoppedSyntheticDeathPair (q.1, min q.2 1))
        (fun _ => (measurable_stoppedSyntheticDeathPair.comp
          (measurable_fst.prodMk
            (measurable_snd.min measurable_const))).aemeasurable)).symm

lemma observedDeathSample_riskIndicator {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (i : Fin n) {t : ℝ} (ht0 : 0 < t) :
    Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t
        (observedDeathSample a s) =
      if (s i).treatment = a ∧ t ≤ (s i).exit then 1 else 0 := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator
    observedDeathSample observedDeathPair
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd
    · by_cases he : t ≤ (s i).exit <;> simp [ha, hd, ht0.le, he] <;> linarith
    · by_cases he : t ≤ (s i).exit <;> simp [ha, hd, ht0.le, he] <;> linarith
  · simp [ha, show ¬t ≤ (0 : ℝ) by linarith]

lemma observedDeathSample_riskSet {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) {t : ℝ} (ht0 : 0 < t) :
    Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t
        (observedDeathSample a s) = riskSet a s t := by
  classical
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskSet riskSet
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hi := observedDeathSample_riskIndicator a s i ht0
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator at hi
  exact_mod_cast hi

lemma observedDeathSample_inverseRisk {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) {t : ℝ} (ht0 : 0 < t) :
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t
        (observedDeathSample a s) = invRisk a s t := by
  unfold Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk invRisk
  rw [observedDeathSample_riskSet a s ht0]
  simp only [one_div]

/-- The strict-left event predicate in the pair product is the paper death
predicate with exit strictly before the evaluation time. -/
lemma observedDeathSample_deathBefore {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (i : Fin n) (t : ℝ) :
    ((observedDeathSample a s i).2 < t ∧
      (observedDeathSample a s i).2 < (observedDeathSample a s i).1) ↔
      ((s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit < t) := by
  unfold observedDeathSample observedDeathPair
  by_cases ha : (s i).treatment = a
  · by_cases hd : (s i).deathInd <;> simp [ha, hd]
  · simp [ha]

/-- On histories with nonnegative exits, the pair product is the product of
the paper factors indexed by individual observed deaths. -/
lemma pairDeathKMLeft_observedDeathSample {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (t : ℝ) :
    pairDeathKMLeft t (observedDeathSample a s) =
      ∏ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit < t then
        1 - invRisk a s (s i).exit else 1 := by
  classical
  unfold pairDeathKMLeft
  apply Finset.prod_congr rfl
  intro i _
  rw [if_congr (observedDeathSample_deathBefore a s i t) rfl rfl]
  split_ifs with hi
  · have hsecond : (observedDeathSample a s i).2 = (s i).exit := by
      simp [observedDeathSample, observedDeathPair, hi.1, hi.2.1]
    rw [hsecond, observedDeathSample_inverseRisk a s
      (hDeathPos i hi.1 hi.2.1)]
  · rfl

/-- With no tied observed death exits, a paper death jump at an observed
death exit has size one. -/
lemma deathJump_eq_one_of_no_death_ties {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit)
    (i : Fin n) (hai : (s i).treatment = a) (hdi : (s i).deathInd) :
    deathJump a s (s i).exit = 1 := by
  classical
  unfold deathJump
  rw [Finset.sum_eq_single i]
  · simp [hai, hdi]
  · intro j _ hji
    by_cases hj : (s j).treatment = a ∧ (s j).deathInd ∧
        (s j).exit = (s i).exit
    · exact False.elim ((hNoTies i j hji.symm hai hdi hj.1 hj.2.1) hj.2.2.symm)
    · simp [hj]
  · simp

/-- A time which is not the exit of an arm-specific observed death has zero
paper death jump. -/
lemma deathJump_eq_zero_of_not_mem_death_image {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (u : ℝ)
    (hu : u ∉ (Finset.univ.filter (fun i : Fin n =>
      (s i).treatment = a ∧ (s i).deathInd)).image (fun i => (s i).exit)) :
    deathJump a s u = 0 := by
  classical
  unfold deathJump
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = u
  · exfalso
    apply hu
    exact Finset.mem_image.mpr ⟨i, by simp [hi.1, hi.2.1], hi.2.2⟩
  · simp [hi]

/-- On a regular observed path, the canonical per-subject product is exactly
the paper's grouped strict-left death Kaplan--Meier product. -/
lemma pairDeathKMLeft_observedDeathSample_eq_deathKMLeft {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory)
    (hDeathPos : ∀ i, (s i).treatment = a → (s i).deathInd → 0 < (s i).exit)
    (hNoTies : ∀ i j, i ≠ j → (s i).treatment = a → (s i).deathInd →
      (s j).treatment = a → (s j).deathInd → (s i).exit ≠ (s j).exit)
    (t : ℝ) :
    pairDeathKMLeft t (observedDeathSample a s) = deathKMLeft a s t := by
  classical
  rw [pairDeathKMLeft_observedDeathSample a s hDeathPos t]
  let D := Finset.univ.filter (fun i : Fin n =>
    (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit < t)
  let ED := D.image (fun i => (s i).exit)
  let E := (exitTimes s).filter (fun u => u < t)
  have hleft :
      (∏ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
          (s i).exit < t then 1 - invRisk a s (s i).exit else 1) =
        ∏ i ∈ D, (1 - invRisk a s (s i).exit) := by
    simpa only [D] using
      (Finset.prod_filter (s := Finset.univ)
        (fun i : Fin n => (s i).treatment = a ∧ (s i).deathInd ∧
          (s i).exit < t) (fun i => 1 - invRisk a s (s i).exit)).symm
  rw [hleft]
  unfold deathKMLeft
  change (∏ i ∈ D, (1 - invRisk a s (s i).exit)) =
    ∏ u ∈ E, (1 - invRisk a s u * deathJump a s u)
  have hEDsub : ED ⊆ E := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hiD := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨by simp [exitTimes], hiD.2.2.2⟩
  have hright :
      (∏ u ∈ E, (1 - invRisk a s u * deathJump a s u)) =
        ∏ u ∈ ED, (1 - invRisk a s u * deathJump a s u) := by
    calc
      _ = ∏ u ∈ E, if u ∈ ED then
          (1 - invRisk a s u * deathJump a s u) else 1 := by
        apply Finset.prod_congr rfl
        intro u hu
        by_cases hud : u ∈ ED
        · simp [hud]
        · rw [deathJump_eq_zero_of_not_mem_death_image a s u]
          · simp [hud]
          · intro hmem
            apply hud
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
            have hip := (Finset.mem_filter.mp hi).2
            apply Finset.mem_image.mpr
            exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
              hip.1, hip.2, (Finset.mem_filter.mp hu).2⟩, rfl⟩
      _ = ∏ u ∈ E.filter (fun u => u ∈ ED),
          (1 - invRisk a s u * deathJump a s u) := by
        exact (Finset.prod_filter (s := E) (fun u => u ∈ ED)
          (fun u => 1 - invRisk a s u * deathJump a s u)).symm
      _ = _ := by
        congr 1
        ext u
        simp [hEDsub]
  rw [hright]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i hi
    have hip := (Finset.mem_filter.mp hi).2
    rw [deathJump_eq_one_of_no_death_ties a s hNoTies i hip.1 hip.2.1]
    ring
  · intro i hi j hj heq
    have hip := (Finset.mem_filter.mp hi).2
    have hjp := (Finset.mem_filter.mp hj).2
    by_contra hij
    exact (hNoTies i j hij hip.1 hip.2.1 hjp.1 hjp.2.1) heq

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
