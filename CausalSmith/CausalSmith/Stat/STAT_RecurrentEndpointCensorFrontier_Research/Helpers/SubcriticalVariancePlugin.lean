module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonDeathVariation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonDeathPlugin
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalAsymptoticLinearity

public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FullHorizonRecurrenceVariation

/-!
# Removal of future marks from the actual subcritical studentizer

Roadmap (38)--(41): the full-horizon pathwise plug-in replacement applies to
both arms of the observable variance estimate. Recurrence variation is retained
exactly, and the death variation uses the deterministic remaining target.
This reduces variance consistency to the two actual optional-variation limits.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The actual variance statistic with deterministic remaining-target death
marks; its observed risk sets and recurrence variation are retained. -/
-- @node: deterministicRemainingSigmaHatSq
noncomputable def deterministicRemainingSigmaHatSq (c : ClassConstants)
    (P : SubjectLaw) {n : ℕ} (s : Fin n → ObsHistory) : ℝ :=
  ∑ a : Arm, (
    (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
      Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
        (fun t => (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2)) else 0) +
    localizedDeathVariation a s 1 (remainingTarget c P a 0))

/-- On samples in the study window, subtracting the comparison statistic
cancels recurrence variation exactly and leaves the two death plug-in errors. -/
-- @node: sigmaHatSq_sub_deterministicRemaining_eq
lemma sigmaHatSq_sub_deterministicRemaining_eq (c : ClassConstants)
    (P : SubjectLaw) {n : ℕ} (s : Fin n → ObsHistory)
    (hExit : ∀ i, (s i).exit ≤ 1) :
    sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s =
      ∑ a : Arm, (localizedDeathVariation a s 1 (remainingMeanHat c a s) -
        localizedDeathVariation a s 1 (remainingTarget c P a 0)) := by
  classical
  unfold sigmaHatSq deterministicRemainingSigmaHatSq
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he : (n : ℝ) * (∑ i : Fin n,
      if (s i).treatment = a ∧ (s i).deathInd then
        (remainingMeanHat c a s (s i).exit) ^ 2 * (invRisk a s (s i).exit) ^ 2
      else 0) = localizedDeathVariation a s 1 (remainingMeanHat c a s) := by
    unfold localizedDeathVariation
    simp only [hExit, and_true]
  rw [he]
  ring

/-- The exact cancellation holds almost surely under the actual observed
sample law, since observed exits lie within the study window. -/
-- @node: sigmaHatSq_sub_deterministicRemaining_eq_ae
lemma sigmaHatSq_sub_deterministicRemaining_eq_ae (c : ClassConstants)
    (P : SubjectLaw) (hD : DeathHazard P) (n : ℕ) :
    (fun s => sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s) =ᵐ[sampleLaw P n]
      fun s => ∑ a : Arm,
        (localizedDeathVariation a s 1 (remainingMeanHat c a s) -
          localizedDeathVariation a s 1 (remainingTarget c P a 0)) := by
  filter_upwards [sample_exit_mem_Icc_ae P hD n] with s hs
  exact sigmaHatSq_sub_deterministicRemaining_eq c P s (fun i => (hs i).2)

/-- Future recurrence marks may be removed from the observable studentizer
in probability under the subcritical model, with no independence or
predictability assumption on those marks. -/
-- @node: sigmaHatSq_deterministicRemaining_difference_probability_tendsto_zero
lemma sigmaHatSq_deterministicRemaining_difference_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s|})
      atTop (nhds 0) := by
  let D := fun (a : Arm) n (s : Fin n → ObsHistory) =>
    localizedDeathVariation a s 1 (remainingMeanHat c a s) -
      localizedDeathVariation a s 1 (remainingTarget c P a 0)
  have ht := sampleLaw_negligible_sub P (D true) (fun n s => -D false n s)
    (fun _ hδ => fullDeathVariation_plugin_probability_tendsto_zero c P hP hk true hδ)
    (fun _ hδ => by simpa only [abs_neg] using
      fullDeathVariation_plugin_probability_tendsto_zero c P hP hk false hδ) hε
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  filter_upwards [sigmaHatSq_sub_deterministicRemaining_eq_ae c P hP.deathHazard n]
    with s hs
  change (ε < |D true n s - -D false n s|) =
    (ε < |sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s|)
  rw [hs]
  simp only [D, Arm, Fintype.sum_bool, sub_neg_eq_add]

/-- The exact influence variance splits into the two integrable oracle
contributions in each arm. -/
-- @node: subcriticalVariance_eq_sum_oracle_components
lemma subcriticalVariance_eq_sum_oracle_components
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (hk : c.kappa < 1) :
    subcriticalVariance c P = ∑ a : Arm,
      ((P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, survival P a t * P.lam a t / retention P a t) +
       (P.p a)⁻¹ * (∫ t in (0 : ℝ)..1, remainingTarget c P a 0 t ^ 2 * P.hazard a t /
         (survival P a t * retention P a t))) := by
  unfold subcriticalVariance
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalIntegral.integral_add
    (subcritical_recurrence_energy_intervalIntegrable c P hP hk a)
    (subcritical_death_energy_intervalIntegrable c P hP hk a), mul_add]

/-- Both actual optional-variation limits give consistency of the comparison
statistic, with no independence between its contributions. -/
-- @node: deterministicRemainingSigmaHatSq_probability_tendsto_limit
lemma deterministicRemainingSigmaHatSq_probability_tendsto_limit
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |deterministicRemainingSigmaHatSq c P s - subcriticalVariance c P|})
      atTop (nhds 0) := by
  let R := fun (a : Arm) (n : ℕ) (s : Fin n → ObsHistory) =>
    (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
      Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
        (fun t => deathKMLeft a s t ^ 2 * invRisk a s t ^ 2)) else 0)
  let D := fun (a : Arm) (n : ℕ) (s : Fin n → ObsHistory) =>
    localizedDeathVariation a s 1 (remainingTarget c P a 0)
  let VR := fun a => (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
    survival P a t * P.lam a t / retention P a t
  let VD := fun a => (P.p a)⁻¹ * ∫ t in (0 : ℝ)..1,
    remainingTarget c P a 0 t ^ 2 * P.hazard a t / (survival P a t * retention P a t)
  let E := fun (a : Arm) n (s : Fin n → ObsHistory) => R a n s + D a n s - (VR a + VD a)
  have hE (a : Arm) (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n : ℕ => (sampleLaw P n).real {s | δ < |E a n s|}) atTop (nhds 0) := by
    have ht := sampleLaw_negligible_sub P (fun n s => R a n s - VR a)
      (fun n s => -(D a n s - VD a))
      (fun _ hγ => subcritical_recurrenceVariation_probability_tendsto_limit c P hP hk a hγ)
      (fun _ hγ => by simpa only [abs_neg] using
        subcritical_deathVariation_probability_tendsto_limit c P hP hk a hγ) hδ
    convert ht using 1
    funext n
    congr 1
    ext s
    simp only [mem_setOf_eq]
    have he : E a n s = (R a n s - VR a) - -(D a n s - VD a) := by dsimp [E]; ring
    rw [he]
  have ht := sampleLaw_negligible_sub P (E true) (fun n s => -E false n s)
    (hE true) (fun _ hδ => by simpa only [abs_neg] using hE false _ hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [mem_setOf_eq]
  rw [subcriticalVariance_eq_sum_oracle_components c P hP hk]
  have he : deterministicRemainingSigmaHatSq c P s -
      (∑ a : Arm, (VR a + VD a)) = E true n s - -E false n s := by
    simp only [deterministicRemainingSigmaHatSq, Arm, Fintype.sum_bool, E, R, D, VR, VD]
    ring
  rw [he]

/-- The observable studentizer is consistent after replacing its future
recurrence marks by the deterministic remaining target (42). -/
-- @node: sigmaHatSq_probability_tendsto_subcriticalVariance
lemma sigmaHatSq_probability_tendsto_subcriticalVariance
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |sigmaHatSq c s - subcriticalVariance c P|}) atTop (nhds 0) := by
  have ht := sampleLaw_negligible_sub P
    (fun n s => sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s)
    (fun n s => subcriticalVariance c P - deterministicRemainingSigmaHatSq c P s)
    (fun _ hδ => sigmaHatSq_deterministicRemaining_difference_probability_tendsto_zero
      c P hP hk hδ)
    (fun _ hδ => by simpa only [abs_sub_comm] using
      deterministicRemainingSigmaHatSq_probability_tendsto_limit c P hP hk hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [mem_setOf_eq]
  have he : sigmaHatSq c s - deterministicRemainingSigmaHatSq c P s -
      (subcriticalVariance c P - deterministicRemainingSigmaHatSq c P s) =
      sigmaHatSq c s - subcriticalVariance c P := by ring
  rw [he]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
