module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.ClassifierMoments
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Representation

/-! Pointwise representation of legal fixed prefixes. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

private lemma sum_fin_slice {α : Type*} [AddCommMonoid α]
    {n lo len : ℕ} (h : lo + len ≤ n) (f : Fin n → α) :
    (∑ i : Fin n, if lo ≤ i.val ∧ i.val < lo + len then f i else 0) =
      ∑ j : Fin len, f ⟨lo + j.val, by omega⟩ := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => ⟨i.val - lo, by
    have := (Finset.mem_filter.mp hi).2
    omega⟩)
  · simp
  · intro a ha b hb hab
    apply Fin.ext
    have hab' := congrArg Fin.val hab
    simp only at hab'
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  · intro j hj
    let i : Fin n := ⟨lo + j.val, by omega⟩
    have hi : i ∈ Finset.univ.filter (fun i : Fin n => lo ≤ i.val ∧ i.val < lo + len) := by
      simp [i]
    refine ⟨i, hi, ?_⟩
    apply Fin.ext
    simp [i]
  · intro i hi
    congr 1
    apply Fin.ext
    have hi' := (Finset.mem_filter.mp hi).2
    simp
    omega

noncomputable def finiteSampleArmCellCount {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) : ℕ :=
  ∑ i : Fin s.count, if (s.points i).x = k ∧ (s.points i).a = a then 1 else 0

noncomputable def finiteSampleArmCellSum {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) : ℝ :=
  ∑ i : Fin s.count,
    if (s.points i).x = k ∧ (s.points i).a = a then (s.points i).y else 0

noncomputable def armCellIndices {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) :
    Finset (Fin s.count) :=
  Finset.univ.filter (fun i => (s.points i).x = k ∧ (s.points i).a = a)

noncomputable def finiteSampleArmCellOutcomes {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) : FiniteSample ℝ :=
  let t := armCellIndices s a k
  ⟨t.card, fun i => (s.points (t.orderIsoOfFin rfl i)).y⟩

private lemma finiteSampleArmCellOutcomes_count {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) :
    (finiteSampleArmCellOutcomes s a k).count = finiteSampleArmCellCount s a k := by
  rcases s with ⟨m, x⟩
  unfold finiteSampleArmCellOutcomes finiteSampleArmCellCount armCellIndices
  simp only [FiniteSample.count, FiniteSample.points]
  exact Finset.card_filter _ _

private lemma finiteSampleArmCellOutcomes_sum {n : ℕ}
    (s : FiniteSample (SampleObs n)) (a : Bool) (k : Fin n) :
    (∑ i : Fin (finiteSampleArmCellOutcomes s a k).count,
        (finiteSampleArmCellOutcomes s a k).points i) =
      finiteSampleArmCellSum s a k := by
  classical
  rcases s with ⟨m, x⟩
  let t : Finset (Fin m) :=
    Finset.univ.filter (fun i => (x i).x = k ∧ (x i).a = a)
  have heq : (∑ i : Fin t.card, (x (t.orderIsoOfFin rfl i).1).y) =
      ∑ i : t, (x i.1).y := by
    exact Fintype.sum_equiv (t.orderIsoOfFin rfl).toEquiv _ _ (fun _ => rfl)
  unfold finiteSampleArmCellOutcomes
  dsimp only [FiniteSample.count, FiniteSample.points]
  change (∑ i : Fin t.card, (x (t.orderIsoOfFin rfl i).1).y) =
    finiteSampleArmCellSum (⟨m, x⟩ : FiniteSample (SampleObs n)) a k
  rw [heq, ← Finset.sum_subtype t (by intro i; simp [t]) (fun i => (x i).y)]
  unfold finiteSampleArmCellSum
  dsimp only [FiniteSample.count, FiniteSample.points]
  rw [Finset.sum_filter]
  rfl

noncomputable def prefixCenteredNumerator {n : ℕ} (t : ℝ)
    (s : FiniteSample (SampleObs n)) (k : Fin n) : ℝ :=
  finiteSampleArmCellCount s false k * finiteSampleArmCellSum s true k -
  finiteSampleArmCellCount s true k * finiteSampleArmCellSum s false k -
  t * finiteSampleArmCellCount s false k * finiteSampleArmCellCount s true k

noncomputable def prefixOutcomePair {n : ℕ}
    (s : FiniteSample (SampleObs n)) (k : Fin n) :
    FiniteSample ℝ × FiniteSample ℝ :=
  (finiteSampleArmCellOutcomes s false k, finiteSampleArmCellOutcomes s true k)

lemma prefixCenteredNumerator_eq_pairSum {n : ℕ} (P : Law n) (t : ℝ)
    (s : FiniteSample (SampleObs n)) (k : Fin n) :
    prefixCenteredNumerator t s k =
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t)
        (prefixOutcomePair s k).1 (prefixOutcomePair s k).2 := by
  let s0 := finiteSampleArmCellOutcomes s false k
  let s1 := finiteSampleArmCellOutcomes s true k
  have hpair := fixedCount_centeredNumerator_eq_pairSum t s0.count s1.count
    s0.points s1.points
  have hleft : prefixCenteredNumerator t s k =
      (s0.count : ℝ) * (∑ j : Fin s1.count, s1.points j) -
        (s1.count : ℝ) * (∑ i : Fin s0.count, s0.points i) -
        t * (s0.count : ℝ) * (s1.count : ℝ) := by
    unfold prefixCenteredNumerator
    dsimp only [s0, s1]
    rw [finiteSampleArmCellOutcomes_sum, finiteSampleArmCellOutcomes_sum,
      finiteSampleArmCellOutcomes_count, finiteSampleArmCellOutcomes_count]
  rw [hleft, hpair]
  rfl

noncomputable def prefixLightCorrection {n : ℕ} (rho t : ℝ)
    (s : FiniteSample (SampleObs n)) (k : Fin n) : ℝ :=
  prefixCenteredNumerator t s k *
    lightFactorialCoefficient n rho (finiteSampleArmCellCount s false k)
      (finiteSampleArmCellCount s true k)

noncomputable def prefixHeavyCorrection {n : ℕ} (t : ℝ)
    (s : FiniteSample (SampleObs n)) (k : Fin n) : ℝ :=
  prefixCenteredNumerator t s k *
    heavyCoefficient n (finiteSampleArmCellCount s false k)
      (finiteSampleArmCellCount s true k)

noncomputable def prefixSelectedCorrection {n : ℕ} (rho t : ℝ)
    (p : FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) (k : Fin n) : ℝ :=
  if finiteSampleCellCount p.1 k ≤ 256 * degree n rho then
    prefixLightCorrection rho t p.2 k else prefixHeavyCorrection t p.2 k

lemma prefixSelectedCorrection_eq_idealSelectedCorrection {n : ℕ}
    (P : Law n) (rho t : ℝ)
    (p : FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) (k : Fin n) :
    prefixSelectedCorrection rho t p k =
      idealSelectedCorrection P k t rho (p.1, prefixOutcomePair p.2 k) := by
  unfold prefixSelectedCorrection idealSelectedCorrection prefixLightCorrection
    prefixHeavyCorrection idealLightCorrection idealHeavyCorrection
  rw [prefixCenteredNumerator_eq_pairSum P t p.2 k]
  simp only [prefixOutcomePair, finiteSampleArmCellOutcomes_count]

private lemma finiteSampleCellCount_fixedSize {n m : ℕ}
    (x : Fin m → SampleObs n) (k : Fin n) :
    finiteSampleCellCount (fixedSizeEmbed m x) k =
      ∑ i : Fin m, if (x i).x = k then 1 else 0 := by
  unfold finiteSampleCellCount finiteSampleHistogram
  rw [Fintype.card_subtype, Finset.card_filter]
  rfl

lemma classifierCount_eq_finiteSampleCellCount {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (sample : Fin n → SampleObs n) (k : Fin n) :
    classifierCount n sample u k =
      finiteSampleCellCount (fixedPrefixSamples n u v h sample).1 k := by
  rw [show (fixedPrefixSamples n u v h sample).1 =
      fixedSizeEmbed u (classifierPrefix n u v h sample) by rfl,
    finiteSampleCellCount_fixedSize]
  unfold classifierCount classifierPrefix
  rw [show (fun i : Fin n =>
      if pilotSize n ≤ i.val ∧ i.val < pilotSize n + u ∧ (sample i).x = k
      then 1 else 0) = fun i =>
      if pilotSize n ≤ i.val ∧ i.val < pilotSize n + u then
        (if (sample i).x = k then 1 else 0) else 0 by
    funext i
    split_ifs <;> simp_all]
  rw [sum_fin_slice (show pilotSize n + u ≤ n by
    simp only [postPilotSize, pilotSize] at h ⊢
    omega) (fun i => if (sample i).x = k then 1 else 0)]

lemma estimationCount_eq_finiteSampleArmCellCount {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (sample : Fin n → SampleObs n)
    (a : Bool) (k : Fin n) :
    estimationCount n sample u v a k =
      finiteSampleArmCellCount (fixedPrefixSamples n u v h sample).2 a k := by
  unfold estimationCount fixedPrefixSamples finiteSampleArmCellCount
  simp only [FiniteSample.points, FiniteSample.count, fixedSizeEmbed, estimationPrefix]
  rw [show (fun i : Fin n =>
      if pilotSize n + u ≤ i.val ∧ i.val < pilotSize n + u + v ∧
          (sample i).x = k ∧ (sample i).a = a then 1 else 0) = fun i =>
      if pilotSize n + u ≤ i.val ∧ i.val < pilotSize n + u + v then
        (if (sample i).x = k ∧ (sample i).a = a then 1 else 0) else 0 by
    funext i
    split_ifs <;> simp_all]
  rw [sum_fin_slice (show pilotSize n + u + v ≤ n by
    simp only [postPilotSize, pilotSize] at h ⊢
    omega) (fun i => if (sample i).x = k ∧ (sample i).a = a then 1 else 0)]
  rfl

lemma estimationSum_eq_finiteSampleArmCellSum {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (sample : Fin n → SampleObs n)
    (a : Bool) (k : Fin n) :
    estimationSum n sample u v a k =
      finiteSampleArmCellSum (fixedPrefixSamples n u v h sample).2 a k := by
  unfold estimationSum fixedPrefixSamples finiteSampleArmCellSum
  simp only [FiniteSample.points, FiniteSample.count, fixedSizeEmbed, estimationPrefix]
  rw [show (fun i : Fin n =>
      if pilotSize n + u ≤ i.val ∧ i.val < pilotSize n + u + v ∧
          (sample i).x = k ∧ (sample i).a = a then (sample i).y else 0) = fun i =>
      if pilotSize n + u ≤ i.val ∧ i.val < pilotSize n + u + v then
        (if (sample i).x = k ∧ (sample i).a = a then (sample i).y else 0) else 0 by
    funext i
    split_ifs <;> simp_all]
  rw [sum_fin_slice (show pilotSize n + u + v ≤ n by
    simp only [postPilotSize, pilotSize] at h ⊢
    omega) (fun i => if (sample i).x = k ∧ (sample i).a = a then (sample i).y else 0)]
  rfl

lemma centeredNumerator_eq_prefixCenteredNumerator {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (M : ℝ)
    (sample : Fin n → SampleObs n) (k : Fin n) :
    centeredNumerator n M sample u v k =
      prefixCenteredNumerator (pilotTau n M sample)
        (fixedPrefixSamples n u v h sample).2 k := by
  unfold centeredNumerator prefixCenteredNumerator
  rw [estimationCount_eq_finiteSampleArmCellCount h sample false k,
    estimationCount_eq_finiteSampleArmCellCount h sample true k,
    estimationSum_eq_finiteSampleArmCellSum h sample false k,
    estimationSum_eq_finiteSampleArmCellSum h sample true k]

lemma lightIndicator_eq_prefix {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (rho : ℝ)
    (sample : Fin n → SampleObs n) (k : Fin n) :
    lightIndicator n rho sample u k =
      if finiteSampleCellCount (fixedPrefixSamples n u v h sample).1 k ≤
          256 * degree n rho then 1 else 0 := by
  unfold lightIndicator
  rw [classifierCount_eq_finiteSampleCellCount h sample k]

lemma lightCorrection_eq_prefixLightCorrection {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (M rho : ℝ)
    (sample : Fin n → SampleObs n) (k : Fin n) :
    lightCorrection n M rho sample u v k =
      prefixLightCorrection rho (pilotTau n M sample)
        (fixedPrefixSamples n u v h sample).2 k := by
  rw [prefixLightCorrection, ← centeredNumerator_eq_prefixCenteredNumerator h M sample k]
  unfold lightCorrection lightFactorialCoefficient
  rw [estimationCount_eq_finiteSampleArmCellCount h sample false k,
    estimationCount_eq_finiteSampleArmCellCount h sample true k]
  split_ifs <;> simp_all

lemma heavyCorrection_eq_prefixHeavyCorrection {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (M : ℝ)
    (sample : Fin n → SampleObs n) (k : Fin n) :
    heavyCorrection n M sample u v k =
      prefixHeavyCorrection (pilotTau n M sample)
        (fixedPrefixSamples n u v h sample).2 k := by
  rw [prefixHeavyCorrection, ← centeredNumerator_eq_prefixCenteredNumerator h M sample k]
  unfold heavyCorrection heavyCoefficient centeredNumerator
  rw [estimationCount_eq_finiteSampleArmCellCount h sample false k,
    estimationCount_eq_finiteSampleArmCellCount h sample true k,
    estimationSum_eq_finiteSampleArmCellSum h sample false k,
    estimationSum_eq_finiteSampleArmCellSum h sample true k]
  let N0 := finiteSampleArmCellCount (fixedPrefixSamples n u v h sample).2 false k
  let N1 := finiteSampleArmCellCount (fixedPrefixSamples n u v h sample).2 true k
  let S0 := finiteSampleArmCellSum (fixedPrefixSamples n u v h sample).2 false k
  let S1 := finiteSampleArmCellSum (fixedPrefixSamples n u v h sample).2 true k
  by_cases h0 : N0 = 0
  · simp [N0, h0]
  by_cases h1 : N1 = 0
  · simp [N1, h1]
  simp only [N0, N1] at h0 h1 ⊢
  simp only [h0, h1, false_or, ↓reduceIte]
  field_simp

lemma lightHeavyCorrection_eq_prefixSelectedCorrection {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (M rho : ℝ)
    (sample : Fin n → SampleObs n) (k : Fin n) :
    lightIndicator n rho sample u k * lightCorrection n M rho sample u v k +
        (1 - lightIndicator n rho sample u k) * heavyCorrection n M sample u v k =
      prefixSelectedCorrection rho (pilotTau n M sample)
        (fixedPrefixSamples n u v h sample) k := by
  rw [lightIndicator_eq_prefix h rho sample k,
    lightCorrection_eq_prefixLightCorrection h M rho sample k,
    heavyCorrection_eq_prefixHeavyCorrection h M sample k]
  unfold prefixSelectedCorrection
  split_ifs <;> ring

/-- On every legal triangular prefix, the actual conditional estimator is
the clipped pilot plus the selected corrections computed solely from the two
finite prefix samples. -/
lemma conditionalEstimator_eq_prefixSelectedCorrection_sum {n u v : ℕ}
    (h : u + v ≤ postPilotSize n) (M rho : ℝ)
    (sample : Fin n → SampleObs n) :
    conditionalEstimator n M rho sample u v =
      clipM M (pilotTau n M sample +
        ∑ k : Fin n, prefixSelectedCorrection rho (pilotTau n M sample)
          (fixedPrefixSamples n u v h sample) k) := by
  unfold conditionalEstimator
  rw [if_pos h]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  exact lightHeavyCorrection_eq_prefixSelectedCorrection h M rho sample k

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
