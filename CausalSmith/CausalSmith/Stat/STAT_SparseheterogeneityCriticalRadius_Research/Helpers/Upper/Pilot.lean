module
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovariance
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Estimator
public import Causalean.Mathlib.Analysis.ClipInterval
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Prefix
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Risk

/-! Uniform pilot risk estimate (display (11)). -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators
open Causalean.Stat
open Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

private lemma pilotSize_le (n : ℕ) : pilotSize n ≤ n := by
  exact Nat.div_le_self n 2

private def pilotPrefix {n : ℕ} (sample : Fin n → SampleObs n) :
    Fin (pilotSize n) → SampleObs n :=
  fun i => sample (Fin.castLE (pilotSize_le n) i)

private lemma pilot_sum_prefix {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Fin n → R) (Q : Fin n → Prop) [DecidablePred Q] :
    (∑ i : Fin n, if i.val < pilotSize n ∧ Q i then f i else 0) =
      ∑ j : Fin (pilotSize n),
        if Q (Fin.castLE (pilotSize_le n) j) then
          f (Fin.castLE (pilotSize_le n) j) else 0 := by
  calc
    _ = ∑ i : Fin n, if i.val < pilotSize n then
          (if Q i then f i else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      aesop
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < pilotSize n),
          (if Q i then f i else 0) := by rw [Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun i : Fin n => i.val < pilotSize n)
    (Finset.univ.filter (fun i : Fin n => i.val < pilotSize n)) (by simp)]
  rw [← (Fin.castLEquiv (pilotSize_le n)).sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

private lemma pilotCount_eq_groupArmCount {n : ℕ}
    (sample : Fin n → SampleObs n) (a : Bool) (k : Fin n) :
    pilotCount n sample a k =
      groupArmCount (fun o : SampleObs n => o.x) (fun o => o.a)
        (pilotPrefix sample) a k := by
  rw [pilotCount, pilot_sum_prefix]
  unfold groupArmCount pilotPrefix
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma pilotSum_eq_armSum {n : ℕ}
    (sample : Fin n → SampleObs n) (a : Bool) (k : Fin n) :
    pilotSum n sample a k =
      armSum (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y)
        (pilotPrefix sample) a k := by
  rw [pilotSum, pilot_sum_prefix]
  unfold armSum armResidualSum supportedArmGroupResidual armGroupResidual
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (sample (Fin.castLE (pilotSize_le n) i)).x = k ∧
      (sample (Fin.castLE (pilotSize_le n) i)).a = a
  · simp [Set.indicator, armGroupEvent, pilotPrefix, h]
  · simp [Set.indicator, armGroupEvent, pilotPrefix, h]

private lemma pilotMean_eq_armMean {n : ℕ}
    (sample : Fin n → SampleObs n) (a : Bool) (k : Fin n) :
    pilotMean n sample a k =
      armMean (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y)
        (pilotPrefix sample) a k := by
  rw [pilotMean, armMean, armResidualMean, pilotCount_eq_groupArmCount,
    pilotSum_eq_armSum]
  by_cases h : groupArmCount (fun o : SampleObs n => o.x) (fun o => o.a)
      (pilotPrefix sample) a k = 0
  · simp [h]
  · have hp : 0 < groupArmCount (fun o : SampleObs n => o.x) (fun o => o.a)
        (pilotPrefix sample) a k := Nat.pos_of_ne_zero h
    simp [h, hp, armSum, div_eq_inv_mul]

private lemma pilotMatched_eq_counts {n : ℕ}
    (sample : Fin n → SampleObs n) (k : Fin n) :
    pilotMatched n sample k =
      if 0 < groupArmCount (fun o : SampleObs n => o.x) (fun o => o.a)
          (pilotPrefix sample) false k *
          groupArmCount (fun o : SampleObs n => o.x) (fun o => o.a)
            (pilotPrefix sample) true k then 1 else 0 := by
  unfold pilotMatched
  rw [pilotCount_eq_groupArmCount, pilotCount_eq_groupArmCount]

private lemma pilotOccupancy_eq_usableTotal {n : ℕ}
    (sample : Fin n → SampleObs n) :
    pilotOccupancy n sample =
      usableTotal (fun o : SampleObs n => o.x) (fun o => o.a)
        (pilotPrefix sample) := by
  unfold pilotOccupancy usableTotal usableGroupTotal groupCount
  apply Finset.sum_congr rfl
  intro k hk
  rw [pilotCount_eq_groupArmCount, pilotCount_eq_groupArmCount,
    pilotMatched_eq_counts]
  unfold usableGroup
  split <;> simp_all [Nat.mul_pos]

private lemma pilotTau_eq_clipped_prefix_collision {n : ℕ} (M : ℝ) (hM : 0 ≤ M)
    (sample : Fin n → SampleObs n) :
    pilotTau n M sample = clipM M
      (collisionEstimator (fun o : SampleObs n => o.x) (fun o => o.a)
        (fun o => o.y) (pilotPrefix sample)) := by
  unfold pilotTau collisionEstimator
  rw [pilotOccupancy_eq_usableTotal]
  by_cases hzero : usableTotal (fun o : SampleObs n => o.x) (fun o => o.a)
      (pilotPrefix sample) = 0
  · simp [hzero, clipM, hM]
  · have hpos : 0 < usableTotal (fun o : SampleObs n => o.x) (fun o => o.a)
        (pilotPrefix sample) := Nat.pos_of_ne_zero hzero
    simp only [hzero, if_false, hpos, if_true]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pilotCount_eq_groupArmCount, pilotCount_eq_groupArmCount,
      pilotMatched_eq_counts, pilotMean_eq_armMean, pilotMean_eq_armMean]
    unfold groupCount matchedCell usableGroup
    split <;> simp_all [Nat.mul_pos]

-- @node: observedCellMass_eq
lemma observedCellMass_eq {n : ℕ} (P : Law n) (k : Fin n) :
    cellMass P.observedLaw (fun o : SampleObs n => o.x) k = P.cellMass k := by
  simpa [cellMass, groupEvent, DiscreteAteHeterogeneityFrontier.realMass] using
    (P.cellMass_eq k).symm

-- @node: observedArmMass_eq
lemma observedArmMass_eq {n : ℕ} (P : Law n) (a : Bool) (k : Fin n) :
    armCellMass P.observedLaw (fun o : SampleObs n => o.x) (fun o => o.a) a k =
      P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) := by
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have h := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  simpa [armCellMass, armGroupEvent, DiscreteAteHeterogeneityFrontier.realMass] using h.symm

-- @node: observedCenter
noncomputable def observedCenter {n : ℕ} (P : Law n)
    (a : Bool) (k : Fin n) : ℝ :=
  if 0 < P.cellMass k then P.outcomeMean a k else 0

private lemma knownResidual_memLp {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) (a : Bool) (k : Fin n) :
    MemLp (supportedArmGroupResidual (fun o : SampleObs n => o.x) (fun o => o.a)
      (fun o => o.y) (observedCenter P.law) a k) 2 P.law.observedLaw := by
  let E : Set (SampleObs n) := {o | o.x = k ∧ o.a = a}
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : SampleObs n => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : SampleObs n => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : SampleObs n => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hE : MeasurableSet E := by
    exact ((measurableSet_singleton k).preimage hx).inter
      ((measurableSet_singleton a).preimage ha)
  have hmeas : AEStronglyMeasurable
      (supportedArmGroupResidual (fun o : SampleObs n => o.x) (fun o => o.a)
        (fun o => o.y) (observedCenter P.law) a k) P.law.observedLaw :=
    (measurable_supportedArmGroupResidual _ _ _ _ hx ha hy a k).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  by_cases hk : P.law.cellMass k = 0
  · have hnull :=
      DiscreteAteHeterogeneityFrontier.observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk
    refine (integrable_const 0).congr (ae_iff.mpr ?_)
    apply measure_mono_null _ hnull
    intro o ho
    by_contra hout
    change ¬(o.x = k ∧ o.a = a) at hout
    simp [supportedArmGroupResidual, armGroupEvent, Set.indicator, hout] at ho
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hcenterEq : observedCenter P.law a k = P.law.outcomeMean a k := by
      simp [observedCenter, hkpos]
    simp only [supportedArmGroupResidual, armGroupResidual, hcenterEq]
    have hc := (P.variance_envelope a k hkpos).1
    have hc' := hc.smul_measure (c := ENNReal.ofReal
      (P.law.cellMass k * (if a then P.law.propensity k else 1 - P.law.propensity k)))
      ENNReal.ofReal_ne_top
    rw [← DiscreteAteHeterogeneityFrontier.observed_arm_cell_outcome_measure P.law a k] at hc'
    have hrestrict : Integrable (fun o : SampleObs n =>
        (o.y - P.law.outcomeMean a k) ^ 2) (P.law.observedLaw.restrict E) :=
      (integrable_map_measure
        ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
        hy.aemeasurable).mp hc'
    have hind : Integrable (E.indicator (fun o : SampleObs n =>
        (o.y - P.law.outcomeMean a k) ^ 2)) P.law.observedLaw :=
      (integrable_indicator_iff hE).2 hrestrict
    convert hind using 1
    funext o
    by_cases ho : o.x = k ∧ o.a = a <;>
      simp [supportedArmGroupResidual, armGroupResidual, armGroupEvent, E,
        Set.indicator, ho, hcenterEq]

private lemma knownResidual_centered {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) (a : Bool) (k : Fin n) :
    ∫ o in armGroupEvent (fun o : SampleObs n => o.x) (fun o => o.a) a k,
      armGroupResidual (fun o => o.y) (observedCenter P.law) a k o
        ∂P.law.observedLaw = 0 := by
  let E : Set (SampleObs n) := {o | o.x = k ∧ o.a = a}
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : SampleObs n => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  by_cases hk : P.law.cellMass k = 0
  · exact setIntegral_measure_zero _
      (DiscreteAteHeterogeneityFrontier.observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk)
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hcenterEq : observedCenter P.law a k = P.law.outcomeMean a k := by
      simp [observedCenter, hkpos]
    simp only [armGroupResidual, hcenterEq]
    let _ : IsProbabilityMeasure (P.law.outcomeLaw a k) :=
      P.law.outcome_isProbability a k
    have hc := (P.variance_envelope a k hkpos).1
    have hcLp : MemLp (fun y : ℝ => y - P.law.outcomeMean a k) 2
        (P.law.outcomeLaw a k) :=
      (memLp_two_iff_integrable_sq
        ((measurable_id.sub measurable_const).aestronglyMeasurable)).2 hc
    have hcInt : Integrable (fun y : ℝ => y - P.law.outcomeMean a k)
        (P.law.outcomeLaw a k) := hcLp.integrable (by norm_num)
    have hyInt : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) := by
      refine (hcInt.add (integrable_const (P.law.outcomeMean a k))).congr ?_
      filter_upwards with y
      simp
    have hcenter : (∫ y, y - P.law.outcomeMean a k
        ∂P.law.outcomeLaw a k) = 0 := by
      rw [integral_sub hyInt (integrable_const _), integral_const,
        ← P.law.outcomeMean_eq]
      simp
    calc
      _ = ∫ y, y - P.law.outcomeMean a k
          ∂Measure.map (fun o : SampleObs n => o.y)
            (P.law.observedLaw.restrict E) := by
        convert (integral_map hy.aemeasurable
          (measurable_id.sub measurable_const).aestronglyMeasurable).symm using 1 <;> rfl
      _ = ∫ y, y - P.law.outcomeMean a k ∂(
          ENNReal.ofReal (P.law.cellMass k *
            (if a then P.law.propensity k else 1 - P.law.propensity k)) •
              P.law.outcomeLaw a k) := by
        rw [DiscreteAteHeterogeneityFrontier.observed_arm_cell_outcome_measure P.law a k]
      _ = 0 := by rw [integral_smul_measure, hcenter]; simp

private lemma knownResidual_sq_le {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) (a : Bool) (k : Fin n) :
    ∫ o in armGroupEvent (fun o : SampleObs n => o.x) (fun o => o.a) a k,
      (armGroupResidual (fun o => o.y) (observedCenter P.law) a k o) ^ 2
        ∂P.law.observedLaw ≤
      armCellMass P.law.observedLaw (fun o : SampleObs n => o.x) (fun o => o.a)
        a k * M ^ 2 := by
  let E : Set (SampleObs n) := {o | o.x = k ∧ o.a = a}
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : SampleObs n => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hq : 0 ≤ if a then P.law.propensity k else 1 - P.law.propensity k := by
    split
    · exact (P.law.propensity_range k).1
    · linarith [(P.law.propensity_range k).2]
  rw [observedArmMass_eq]
  by_cases hk : P.law.cellMass k = 0
  · unfold armGroupResidual armGroupEvent
    rw [setIntegral_measure_zero _
      (DiscreteAteHeterogeneityFrontier.observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk), hk,
      zero_mul]
    positivity
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hcenterEq : observedCenter P.law a k = P.law.outcomeMean a k := by
      simp [observedCenter, hkpos]
    simp only [armGroupResidual, hcenterEq]
    have hc := P.variance_envelope a k hkpos
    have hscale : 0 ≤ P.law.cellMass k *
        (if a then P.law.propensity k else 1 - P.law.propensity k) :=
      mul_nonneg hkpos.le hq
    calc
      _ = ∫ y, (y - P.law.outcomeMean a k) ^ 2
          ∂Measure.map (fun o : SampleObs n => o.y)
            (P.law.observedLaw.restrict E) := by
        convert (integral_map hy.aemeasurable
          ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable).symm
          using 1 <;> rfl
      _ = ∫ y, (y - P.law.outcomeMean a k) ^ 2 ∂(
          ENNReal.ofReal (P.law.cellMass k *
            (if a then P.law.propensity k else 1 - P.law.propensity k)) •
              P.law.outcomeLaw a k) := by
        rw [DiscreteAteHeterogeneityFrontier.observed_arm_cell_outcome_measure P.law a k]
      _ = (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)) *
            (∫ y, (y - P.law.outcomeMean a k) ^ 2 ∂P.law.outcomeLaw a k) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hscale]
        simp only [smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 hscale

private lemma populationContrast_eq_rawAte {n : ℕ} (P : Law n) :
    populationContrast P.observedLaw (fun o : SampleObs n => o.x) (observedCenter P) =
      DiscreteAteHeterogeneityFrontier.rawAteFormula P := by
  unfold populationContrast DiscreteAteHeterogeneityFrontier.rawAteFormula
    DiscreteAteHeterogeneityFrontier.cellEffect
  apply Finset.sum_congr rfl
  intro k hk
  rw [observedCellMass_eq]
  by_cases hmass : 0 < P.cellMass k
  · simp [observedCenter, hmass]
  · have hz : P.cellMass k = 0 := le_antisymm (not_lt.mp hmass) (P.cellMass_range k).1
    simp [observedCenter, hmass, hz]

-- @node: knownObservedAssumptions
lemma knownObservedAssumptions {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) :
    ObservedAssumptions P.law.observedLaw (fun o : SampleObs n => o.x)
      (fun o => o.a) (fun o => o.y) (observedCenter P.law) (1 / 4) M rho := by
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : SampleObs n => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : SampleObs n => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : SampleObs n => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  refine
    { epsilon_pos := by norm_num
      epsilon_lt_half := by norm_num
      X_measurable := hx
      A_measurable := ha
      Y_measurable := hy
      overlap := ?_
      center_envelope := ?_
      residual_L2 := knownResidual_memLp P
      residual_centered := knownResidual_centered P
      residual_second_moment := knownResidual_sq_le P
      homogeneity := ?_ }
  · intro a k hk
    rw [observedCellMass_eq] at hk ⊢
    rw [observedArmMass_eq]
    have hov := P.overlap k hk
    have hpk := (P.law.cellMass_range k).1
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
  · intro a k
    by_cases hk : 0 < P.law.cellMass k
    · simpa [observedCenter, hk] using (P.mean_envelope a k hk).trans (by linarith)
    · simp [observedCenter, hk, hM]
  · intro k hk
    rw [observedCellMass_eq] at hk
    rw [populationContrast_eq_rawAte]
    simp only [observedCenter, if_pos hk]
    simpa [DiscreteAteHeterogeneityFrontier.cellDeviation,
      DiscreteAteHeterogeneityFrontier.cellEffect, mul_comm] using P.radius.2 k hk

-- @node: rawAte_mem_clip
lemma rawAte_mem_clip {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M rho) :
    DiscreteAteHeterogeneityFrontier.rawAteFormula P.law ∈ Icc (-M) M := by
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hterm (k : Fin n) :
      |P.law.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P.law k| ≤
        P.law.cellMass k * M := by
    by_cases hk : P.law.cellMass k = 0
    · simp [hk]
    · have hkpos : 0 < P.law.cellMass k :=
        lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
      rw [abs_mul, abs_of_nonneg (P.law.cellMass_range k).1]
      apply mul_le_mul_of_nonneg_left _ (P.law.cellMass_range k).1
      unfold DiscreteAteHeterogeneityFrontier.cellEffect
      calc
        |P.law.outcomeMean true k - P.law.outcomeMean false k| ≤
            |P.law.outcomeMean true k| + |P.law.outcomeMean false k| := abs_sub _ _
        _ ≤ M / 2 + M / 2 := add_le_add
          (P.mean_envelope true k hkpos) (P.mean_envelope false k hkpos)
        _ = M := by ring
  have habs : |DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ≤ M := by
    unfold DiscreteAteHeterogeneityFrontier.rawAteFormula
    calc
      |∑ k : Fin n, P.law.cellMass k *
          DiscreteAteHeterogeneityFrontier.cellEffect P.law k| ≤
          ∑ k : Fin n, |P.law.cellMass k *
            DiscreteAteHeterogeneityFrontier.cellEffect P.law k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin n, P.law.cellMass k * M :=
        Finset.sum_le_sum fun k hk => hterm k
      _ = M := by
        rw [← Finset.sum_mul,
          DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one]
        simp
  exact abs_le.mp habs

lemma pilot_risk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n M rho (P : KnownRadiusClass n M rho),
      3 ≤ n →
      DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M) ≤
        C * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ)) := by
  obtain ⟨C₀, hC₀, hcollision⟩ :=
    observed_collision_mse_le (1 / 4 : ℝ) (by norm_num) (by norm_num)
  refine ⟨12 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro n M rho P hn
  let m := pilotSize n
  have hmposNat : 0 < m := by
    dsimp [m, pilotSize]
    omega
  have hmn : m ≤ n := pilotSize_le n
  have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hthree : n ≤ 3 * m := by
    dsimp [m, pilotSize]
    omega
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hassumptions := knownObservedAssumptions P
  have hraw := hcollision (SampleObs n) (Fin n) P.law.observedLaw
    (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y)
    (observedCenter P.law) M rho m hmposNat hassumptions
  have htarget := populationContrast_eq_rawAte P.law
  rw [htarget] at hraw
  let F : (Fin n → SampleObs n) → (Fin m → SampleObs n) :=
    fun z i => z (Fin.castLE hmn i)
  let g : (Fin m → SampleObs n) → ℝ := fun z =>
    (collisionEstimator (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y) z -
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
  have htuple : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : SampleObs n => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : SampleObs n => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : SampleObs n => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hg : Integrable g (Measure.pi (fun _ : Fin m => P.law.observedLaw)) := by
    simpa [g, htarget] using (collision_sub_target_memLp (n := m) P.law.observedLaw
      (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y)
      (observedCenter P.law) (1 / 4) M rho hassumptions).integrable_sq
  have hF : Measurable F := by
    dsimp [F]
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hgFull : Integrable (fun z => g (F z))
      (DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
    rw [show DiscreteAteHeterogeneityFrontier.productLaw n P.law =
      Measure.pi (fun _ : Fin n => P.law.observedLaw) from rfl]
    apply (integrable_map_measure
      (((measurable_collisionEstimator (n := m) _ _ _ hx ha hy).sub
        measurable_const).pow_const 2).aestronglyMeasurable hF.aemeasurable).mp
    change Integrable g ((Measure.pi (fun _ : Fin n => P.law.observedLaw)).map
      (fun z : Fin n → SampleObs n => fun i : Fin m => z (Fin.castLE hmn i)))
    rw [iid_prefix_map P.law.observedLaw hmn]
    exact hg
  have hclipRaw : DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M) ≤
      ∫ z : Fin n → SampleObs n, g (F z)
        ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law := by
    unfold DiscreteAteHeterogeneityFrontier.mse
    apply integral_mono_of_nonneg
    · filter_upwards with z
      positivity
    · exact hgFull
    · filter_upwards with z
      rw [pilotTau_eq_clipped_prefix_collision M hM]
      dsimp [g, F]
      have hPF : pilotPrefix z =
          (fun i : Fin m => z (Fin.castLE hmn i)) := by
        funext i
        rfl
      rw [← hPF]
      simpa [clipM, Causalean.Mathlib.Analysis.clipIcc] using
        Causalean.Mathlib.Analysis.clipIcc_sub_sq_le (rawAte_mem_clip P)
          (collisionEstimator (fun o : SampleObs n => o.x) (fun o => o.a)
            (fun o => o.y) (pilotPrefix z))
  have hprefix :
      (∫ z : Fin n → SampleObs n, g (F z)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) =
        ∫ z : Fin m → SampleObs n, g z
          ∂Measure.pi (fun _ : Fin m => P.law.observedLaw) := by
    simpa [g, F, htarget, DiscreteAteHeterogeneityFrontier.productLaw] using
      integral_prefix_collision_error_sq P.law.observedLaw
        (fun o : SampleObs n => o.x) (fun o => o.a) (fun o => o.y)
        (observedCenter P.law) hx ha hy hmn
  rw [hprefix] at hclipRaw
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hthreeR : (n : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hthree
  have hinv : 1 / (m : ℝ) ≤ 3 / (n : ℝ) := by
    apply (div_le_div_iff₀ hmR hnR).2
    nlinarith
  have hdim : (n : ℝ) / (m : ℝ) ^ 2 ≤ 9 / (n : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hmR) hnR).2
    nlinarith [sq_nonneg ((n : ℝ) - 3 * m)]
  have hrate : 1 / (m : ℝ) + rho ^ 2 + (n : ℝ) / (m : ℝ) ^ 2 ≤
      12 * (rho ^ 2 + 1 / (n : ℝ)) := by
    have hinvn : 0 ≤ 1 / (n : ℝ) := by positivity
    calc
      _ ≤ 3 / (n : ℝ) + rho ^ 2 + 9 / (n : ℝ) :=
        add_le_add (add_le_add hinv (le_refl _)) hdim
      _ = rho ^ 2 + 12 / (n : ℝ) := by ring
      _ = rho ^ 2 + 12 * (1 / (n : ℝ)) := by ring
      _ ≤ _ := by nlinarith [sq_nonneg rho]
  calc
    DiscreteAteHeterogeneityFrontier.mse P.law (pilotTau n M) ≤
        ∫ z : Fin m → SampleObs n, g z
          ∂Measure.pi (fun _ : Fin m => P.law.observedLaw) := hclipRaw
    _ ≤ C₀ * M ^ 2 *
        (1 / (m : ℝ) + rho ^ 2 + (Fintype.card (Fin n) : ℝ) / (m : ℝ) ^ 2) := hraw
    _ ≤ 12 * C₀ * M ^ 2 * (rho ^ 2 + 1 / (n : ℝ)) := by
      rw [Fintype.card_fin]
      have hfac : 0 ≤ C₀ * M ^ 2 := mul_nonneg hC₀.le (sq_nonneg M)
      calc
        C₀ * M ^ 2 * (1 / (m : ℝ) + rho ^ 2 + (n : ℝ) / (m : ℝ) ^ 2) ≤
            C₀ * M ^ 2 * (12 * (rho ^ 2 + 1 / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hrate hfac
        _ = _ := by ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
