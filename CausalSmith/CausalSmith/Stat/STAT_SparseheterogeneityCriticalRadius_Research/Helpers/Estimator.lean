module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Basic

/-! The total finite Poisson-average estimator at a supplied radius. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators

def pilotSize (n : ℕ) : ℕ := n / 2 -- @realizes m_0(floor n/2)
def postPilotSize (n : ℕ) : ℕ := n - pilotSize n -- @realizes r(post-pilot size)
noncomputable def blockMean (n : ℕ) : ℝ := (postPilotSize n : ℝ) / 4
  -- @realizes m(Poisson block mean)
noncomputable def auditConstant : ℝ :=
  Real.exp (2 ^ (20 : ℕ) : ℝ) -- @realizes A_\star(exp 2^20)
noncomputable def degree (n : ℕ) (rho : ℝ) : ℕ :=
  max 2 (Nat.floor (Hrho n rho / (16 * Real.log auditConstant)))
  -- @realizes K_n(rho_n)(radius-indexed polynomial degree)
noncomputable def lightScale (n : ℕ) (rho : ℝ) : ℝ :=
  4096 * (degree n rho : ℝ) / blockMean n
  -- @realizes B_n(rho_n)(light-cell scale)

-- keep: public critical-radius specialization of the estimator's tuned degree
noncomputable def criticalDegree (n : ℕ) : ℕ :=
  degree n (criticalRadius n) -- @realizes K_n(critical degree)

-- keep: public critical-radius specialization of the estimator's light-cell scale
noncomputable def criticalLightScale (n : ℕ) : ℝ :=
  lightScale n (criticalRadius n) -- @realizes B_n(critical light scale)

def falling (x ell : ℕ) : ℕ := Nat.descFactorial x ell
  -- @realizes (x)_ell(falling factorial, zero when x<ell)

noncomputable def gCoeff (K ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell * 2 ^ (2 * ell + 3) *
    (Nat.choose (K + ell + 2) (2 * ell + 4) : ℝ) /
    ((K : ℝ) * (K + ell + 2 : ℕ))
  -- @realizes g_{K_n ell}(reciprocal polynomial coefficient)

def pilotCount (n : ℕ) (sample : Fin n → SampleObs n)
    (a : Bool) (k : Fin n) : ℕ := -- @realizes a(Bool arm) @realizes k(Fin n cell)
  ∑ i : Fin n, if i.val < pilotSize n ∧ (sample i).x = k ∧ (sample i).a = a
    -- @realizes i(Fin n sample index)
    then 1 else 0
  -- @realizes \widetilde N_{ak}(pilot arm-cell count)

noncomputable def pilotSum (n : ℕ) (sample : Fin n → SampleObs n)
    (a : Bool) (k : Fin n) : ℝ :=
  ∑ i : Fin n, if i.val < pilotSize n ∧ (sample i).x = k ∧ (sample i).a = a
    then (sample i).y else 0

noncomputable def pilotMean (n : ℕ) (sample : Fin n → SampleObs n)
    (a : Bool) (k : Fin n) : ℝ :=
  if pilotCount n sample a k = 0 then 0 else
    pilotSum n sample a k / pilotCount n sample a k
  -- @realizes tilde Y_{ak}(guarded pilot arm-cell mean)

def pilotMatched (n : ℕ) (sample : Fin n → SampleObs n) (k : Fin n) : ℕ :=
  if 0 < pilotCount n sample false k * pilotCount n sample true k then 1 else 0
  -- @realizes \widetilde J_k(matched pilot cell indicator)

def pilotOccupancy (n : ℕ) (sample : Fin n → SampleObs n) : ℕ :=
  ∑ k : Fin n, (pilotCount n sample false k + pilotCount n sample true k) *
    pilotMatched n sample k
  -- @realizes \widetilde R(usable pilot occupancy)

noncomputable def pilotTau (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) : ℝ :=
  if pilotOccupancy n sample = 0 then 0 else
    clipM M ((∑ k : Fin n,
      ((pilotCount n sample false k + pilotCount n sample true k : ℕ) : ℝ) *
      pilotMatched n sample k *
      (pilotMean n sample true k - pilotMean n sample false k)) /
      pilotOccupancy n sample)
  -- @realizes tilde tau(clipped occupancy pilot)

def classifierCount (n : ℕ) (sample : Fin n → SampleObs n)
    (u : ℕ) (k : Fin n) : ℕ :=
  ∑ i : Fin n, if pilotSize n ≤ i.val ∧ i.val < pilotSize n + u ∧
    (sample i).x = k then 1 else 0
  -- @realizes C_k^{u,v}(classifier count, independent of v)

def estimationCount (n : ℕ) (sample : Fin n → SampleObs n)
    (u v : ℕ) (a : Bool) (k : Fin n) : ℕ :=
  ∑ i : Fin n, if pilotSize n + u ≤ i.val ∧
    i.val < pilotSize n + u + v ∧ (sample i).x = k ∧ (sample i).a = a
    then 1 else 0
  -- @realizes N_{ak}^{u,v}(estimation arm-cell count)

noncomputable def estimationSum (n : ℕ) (sample : Fin n → SampleObs n)
    (u v : ℕ) (a : Bool) (k : Fin n) : ℝ :=
  ∑ i : Fin n, if pilotSize n + u ≤ i.val ∧
    i.val < pilotSize n + u + v ∧ (sample i).x = k ∧ (sample i).a = a
    then (sample i).y else 0
  -- @realizes S_{ak}^{u,v}(estimation arm-cell outcome sum)

noncomputable def centeredNumerator (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) (u v : ℕ) (k : Fin n) : ℝ :=
  estimationCount n sample u v false k * estimationSum n sample u v true k -
  estimationCount n sample u v true k * estimationSum n sample u v false k -
  pilotTau n M sample * estimationCount n sample u v false k *
    estimationCount n sample u v true k
  -- @realizes D_k^{u,v}(centered mixed-arm numerator)

noncomputable def lightIndicator (n : ℕ) (rho : ℝ) (sample : Fin n → SampleObs n)
    (u : ℕ) (k : Fin n) : ℝ :=
  if classifierCount n sample u k ≤ 256 * degree n rho then 1 else 0
  -- @realizes L_k^{u,v}(light-cell classifier)

noncomputable def lightCorrection (n : ℕ) (M rho : ℝ)
    (sample : Fin n → SampleObs n) (u v : ℕ) (k : Fin n) : ℝ :=
  if estimationCount n sample u v false k = 0 ∨
      estimationCount n sample u v true k = 0 then 0 else
    centeredNumerator n M sample u v k *
      ∑ ell ∈ Finset.range (degree n rho - 1),
        gCoeff (degree n rho) ell *
          ((falling (estimationCount n sample u v false k - 1) ell : ℝ) +
            (falling (estimationCount n sample u v true k - 1) ell : ℝ)) /
          (lightScale n rho ^ (ell + 1) * blockMean n ^ (ell + 2))
  -- @realizes P_k^{u,v}(guarded light-cell factorial correction)

noncomputable def heavyCorrection (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) (u v : ℕ) (k : Fin n) : ℝ :=
  if estimationCount n sample u v false k = 0 ∨
      estimationCount n sample u v true k = 0 then 0 else
    ((estimationCount n sample u v false k +
      estimationCount n sample u v true k : ℕ) : ℝ) / blockMean n *
      (estimationSum n sample u v true k /
          estimationCount n sample u v true k -
        estimationSum n sample u v false k /
          estimationCount n sample u v false k - pilotTau n M sample)
  -- @realizes H_k^{u,v}(guarded heavy-cell correction)

noncomputable def conditionalEstimator (n : ℕ) (M rho : ℝ)
    (sample : Fin n → SampleObs n) (u v : ℕ) : ℝ :=
  if u + v ≤ postPilotSize n then
    clipM M (pilotTau n M sample + (∑ k : Fin n,
      (
      lightIndicator n rho sample u k * lightCorrection n M rho sample u v k +
      (1 - lightIndicator n rho sample u k) * heavyCorrection n M sample u v k)))
  else pilotTau n M sample
  -- @realizes U_{u,v}(clipped conditional estimator)

noncomputable def poissonWeight (n u v : ℕ) : ℝ :=
  Real.exp (-2 * blockMean n) * blockMean n ^ (u + v) /
    ((Nat.factorial u : ℝ) * (Nat.factorial v : ℝ))

-- @node: def:critical-estimator
noncomputable def knownRadiusEstimator (n : ℕ) (M rho : ℝ)
    (sample : Fin n → SampleObs n) : ℝ :=
  (∑ u ∈ Finset.range (postPilotSize n + 1),
    ∑ v ∈ Finset.range (postPilotSize n - u + 1),
      poissonWeight n u v * conditionalEstimator n M rho sample u v) +
  (1 - ∑ u ∈ Finset.range (postPilotSize n + 1),
    ∑ v ∈ Finset.range (postPilotSize n - u + 1), poissonWeight n u v) *
    pilotTau n M sample
  -- @realizes hat tau_{n,rho_n}^{cf}(finite data-only Poisson average)

noncomputable def criticalEstimator (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) : ℝ :=
  knownRadiusEstimator n M (criticalRadius n) sample
  -- @realizes hat tau_n^{cf}(critical-radius specialization)

-- @node: measurable_sample_x
@[fun_prop] lemma measurable_sample_x (n : ℕ) (i : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => (sample i).x) := by
  have h : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_fst.comp h).comp (measurable_pi_apply i)

-- @node: measurable_sample_a
@[fun_prop] lemma measurable_sample_a (n : ℕ) (i : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => (sample i).a) := by
  have h : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_fst.comp (measurable_snd.comp h)).comp (measurable_pi_apply i)

-- @node: measurable_sample_y
@[fun_prop] lemma measurable_sample_y (n : ℕ) (i : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => (sample i).y) := by
  have h : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_snd.comp (measurable_snd.comp h)).comp (measurable_pi_apply i)

-- @node: pilotCount_measurable
@[fun_prop] lemma pilotCount_measurable (n : ℕ) (a : Bool) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => pilotCount n sample a k) := by
  classical
  unfold pilotCount
  apply Finset.measurable_sum
  intro i hi
  by_cases hidx : i.val < pilotSize n
  · simp only [hidx, true_and]
    apply Measurable.ite
    · exact ((measurableSet_singleton k).preimage (measurable_sample_x n i)).inter
        ((measurableSet_singleton a).preimage (measurable_sample_a n i))
    · exact measurable_const
    · exact measurable_const
  · simp [hidx]

-- @node: pilotSum_measurable
@[fun_prop] lemma pilotSum_measurable (n : ℕ) (a : Bool) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => pilotSum n sample a k) := by
  classical
  unfold pilotSum
  apply Finset.measurable_sum
  intro i hi
  by_cases hidx : i.val < pilotSize n
  · simp only [hidx, true_and]
    apply Measurable.ite
    · exact ((measurableSet_singleton k).preimage (measurable_sample_x n i)).inter
        ((measurableSet_singleton a).preimage (measurable_sample_a n i))
    · exact measurable_sample_y n i
    · exact measurable_const
  · simp [hidx]

-- @node: measurable_natCast_estimator
lemma measurable_natCast_estimator {α : Type*} [MeasurableSpace α] (f : α → ℕ)
    (hf : Measurable f) : Measurable (fun x => (f x : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hf

-- @node: pilotMean_measurable
@[fun_prop] lemma pilotMean_measurable (n : ℕ) (a : Bool) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => pilotMean n sample a k) := by
  unfold pilotMean
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (pilotCount_measurable n a k)
  · exact measurable_const
  · exact (pilotSum_measurable n a k).div
      (measurable_natCast_estimator _ (pilotCount_measurable n a k))

-- @node: pilotMatched_measurable
@[fun_prop] lemma pilotMatched_measurable (n : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => pilotMatched n sample k) := by
  unfold pilotMatched
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      ((pilotCount_measurable n false k).mul (pilotCount_measurable n true k))
  · exact measurable_const
  · exact measurable_const

-- @node: pilotOccupancy_measurable
@[fun_prop] lemma pilotOccupancy_measurable (n : ℕ) :
    Measurable (pilotOccupancy n) := by
  unfold pilotOccupancy
  measurability

-- @node: pilotTau_measurable
@[fun_prop] lemma pilotTau_measurable (n : ℕ) (M : ℝ) :
    Measurable (pilotTau n M) := by
  unfold pilotTau clipM
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (pilotOccupancy_measurable n)
  · exact measurable_const
  · apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Measurable.div
    · apply Finset.measurable_sum
      intro k hk
      exact (((measurable_natCast_estimator _
          ((pilotCount_measurable n false k).add (pilotCount_measurable n true k))).mul
          (measurable_natCast_estimator _ (pilotMatched_measurable n k))).mul
          ((pilotMean_measurable n true k).sub (pilotMean_measurable n false k)))
    · exact measurable_natCast_estimator _ (pilotOccupancy_measurable n)

-- @node: classifierCount_measurable
@[fun_prop] lemma classifierCount_measurable (n : ℕ) (u : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => classifierCount n sample u k) := by
  classical
  unfold classifierCount
  apply Finset.measurable_sum
  intro i hi
  by_cases hstart : pilotSize n ≤ i.val
  · by_cases hend : i.val < pilotSize n + u
    · simp only [hstart, hend, true_and]
      apply Measurable.ite
      · exact (measurableSet_singleton k).preimage (measurable_sample_x n i)
      · exact measurable_const
      · exact measurable_const
    · simp [hend]
  · simp [hstart]

-- @node: estimationCount_measurable
@[fun_prop] lemma estimationCount_measurable (n u v : ℕ) (a : Bool) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => estimationCount n sample u v a k) := by
  classical
  unfold estimationCount
  apply Finset.measurable_sum
  intro i hi
  by_cases hstart : pilotSize n + u ≤ i.val
  · by_cases hend : i.val < pilotSize n + u + v
    · simp only [hstart, hend, true_and]
      apply Measurable.ite
      · exact ((measurableSet_singleton k).preimage (measurable_sample_x n i)).inter
          ((measurableSet_singleton a).preimage (measurable_sample_a n i))
      · exact measurable_const
      · exact measurable_const
    · simp [hend]
  · simp [hstart]

-- @node: estimationSum_measurable
@[fun_prop] lemma estimationSum_measurable (n u v : ℕ) (a : Bool) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n => estimationSum n sample u v a k) := by
  classical
  unfold estimationSum
  apply Finset.measurable_sum
  intro i hi
  by_cases hstart : pilotSize n + u ≤ i.val
  · by_cases hend : i.val < pilotSize n + u + v
    · simp only [hstart, hend, true_and]
      apply Measurable.ite
      · exact ((measurableSet_singleton k).preimage (measurable_sample_x n i)).inter
          ((measurableSet_singleton a).preimage (measurable_sample_a n i))
      · exact measurable_sample_y n i
      · exact measurable_const
    · simp [hend]
  · simp [hstart]

-- @node: centeredNumerator_measurable
@[fun_prop] lemma centeredNumerator_measurable (n : ℕ) (M : ℝ)
    (u v : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n =>
      centeredNumerator n M sample u v k) := by
  unfold centeredNumerator
  fun_prop

-- @node: lightIndicator_measurable
@[fun_prop] lemma lightIndicator_measurable (n : ℕ) (rho : ℝ)
    (u : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n =>
      lightIndicator n rho sample u k) := by
  unfold lightIndicator
  apply Measurable.ite
  · exact measurableSet_le (classifierCount_measurable n u k) measurable_const
  · exact measurable_const
  · exact measurable_const

-- @node: lightCorrection_measurable
@[fun_prop] lemma lightCorrection_measurable (n : ℕ) (M rho : ℝ)
    (u v : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n =>
      lightCorrection n M rho sample u v k) := by
  unfold lightCorrection
  apply Measurable.ite
  · exact ((measurableSet_singleton 0).preimage
        (estimationCount_measurable n u v false k)).union
      ((measurableSet_singleton 0).preimage
        (estimationCount_measurable n u v true k))
  · exact measurable_const
  · fun_prop

-- @node: heavyCorrection_measurable
@[fun_prop] lemma heavyCorrection_measurable (n : ℕ) (M : ℝ)
    (u v : ℕ) (k : Fin n) :
    Measurable (fun sample : Fin n → SampleObs n =>
      heavyCorrection n M sample u v k) := by
  unfold heavyCorrection
  apply Measurable.ite
  · exact ((measurableSet_singleton 0).preimage
        (estimationCount_measurable n u v false k)).union
      ((measurableSet_singleton 0).preimage
        (estimationCount_measurable n u v true k))
  · exact measurable_const
  · fun_prop

-- @node: conditionalEstimator_measurable
@[fun_prop] lemma conditionalEstimator_measurable (n : ℕ) (M rho : ℝ)
    (u v : ℕ) : Measurable (fun sample : Fin n → SampleObs n =>
      conditionalEstimator n M rho sample u v) := by
  unfold conditionalEstimator clipM
  by_cases h : u + v ≤ postPilotSize n
  · simp only [h, ↓reduceIte]
    fun_prop
  · simp only [h, ↓reduceIte]
    exact pilotTau_measurable n M

lemma knownRadiusEstimator_measurable (n : ℕ) (M rho : ℝ) :
    Measurable (knownRadiusEstimator n M rho) := by
  unfold knownRadiusEstimator
  fun_prop

-- @node: pilotTau_range
lemma pilotTau_range (n : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (sample : Fin n → SampleObs n) : pilotTau n M sample ∈ Icc (-M) M := by
  unfold pilotTau
  split_ifs
  · simp [Set.mem_Icc, hM]
  · simp only [clipM, Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)

-- @node: conditionalEstimator_range
lemma conditionalEstimator_range (n : ℕ) (M rho : ℝ) (hM : 0 ≤ M)
    (sample : Fin n → SampleObs n) (u v : ℕ) :
    conditionalEstimator n M rho sample u v ∈ Icc (-M) M := by
  unfold conditionalEstimator
  split_ifs
  · simp only [clipM, Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · exact pilotTau_range n M hM sample

-- @node: poissonWeight_nonneg
lemma poissonWeight_nonneg (n u v : ℕ) : 0 ≤ poissonWeight n u v := by
  unfold poissonWeight blockMean
  positivity

-- @node: poissonWeight_finite_mass_le_one
lemma poissonWeight_finite_mass_le_one (n : ℕ) :
    (∑ u ∈ Finset.range (postPilotSize n + 1),
      ∑ v ∈ Finset.range (postPilotSize n - u + 1), poissonWeight n u v) ≤ 1 := by
  let m := blockMean n
  let r := postPilotSize n
  let f : ℕ → ℝ := fun k => m ^ k / (Nat.factorial k : ℝ)
  have hm : 0 ≤ m := by dsimp [m, blockMean]; positivity
  have hf : ∀ k, 0 ≤ f k := by intro k; dsimp [f]; positivity
  have hs : (∑ k ∈ Finset.range (r + 1), f k) ≤ Real.exp m :=
    Real.sum_le_exp_of_nonneg hm (r + 1)
  have hsub (u : ℕ) : Finset.range (r - u + 1) ⊆ Finset.range (r + 1) := by
    intro v hv
    simp only [Finset.mem_range] at hv ⊢
    omega
  have htri :
      (∑ u ∈ Finset.range (r + 1),
        ∑ v ∈ Finset.range (r - u + 1), f u * f v) ≤
      (∑ u ∈ Finset.range (r + 1), f u) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u hu
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsub u)
      (by intro v hv hnv; exact mul_nonneg (hf u) (hf v))
  have hrewrite :
      (∑ u ∈ Finset.range (r + 1),
        ∑ v ∈ Finset.range (r - u + 1), poissonWeight n u v) =
      Real.exp (-2 * m) *
        (∑ u ∈ Finset.range (r + 1),
          ∑ v ∈ Finset.range (r - u + 1), f u * f v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [poissonWeight, f, m, pow_add, div_eq_mul_inv]
    ring
  have hexp : Real.exp (-2 * m) * Real.exp m * Real.exp m = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hzero : -2 * m + m + m = 0 := by ring
    rw [hzero, Real.exp_zero]
  rw [hrewrite]
  calc
    Real.exp (-2 * m) *
        (∑ u ∈ Finset.range (r + 1),
          ∑ v ∈ Finset.range (r - u + 1), f u * f v) ≤
        Real.exp (-2 * m) * (∑ k ∈ Finset.range (r + 1), f k) ^ 2 := by
          exact mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
    _ ≤ Real.exp (-2 * m) * (Real.exp m) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact pow_le_pow_left₀ (Finset.sum_nonneg (by intro k hk; exact hf k)) hs _
    _ = 1 := by nlinarith [hexp]

lemma knownRadiusEstimator_range (n : ℕ) (M rho : ℝ) (hM : 0 ≤ M) :
    ∀ sample, knownRadiusEstimator n M rho sample ∈ Icc (-M) M := by
  intro sample
  let s : ℝ := ∑ u ∈ Finset.range (postPilotSize n + 1),
    ∑ v ∈ Finset.range (postPilotSize n - u + 1), poissonWeight n u v
  let t : ℝ := ∑ u ∈ Finset.range (postPilotSize n + 1),
    ∑ v ∈ Finset.range (postPilotSize n - u + 1),
      poissonWeight n u v * conditionalEstimator n M rho sample u v
  have hs : s ≤ 1 := poissonWeight_finite_mass_le_one n
  have hs0 : 0 ≤ 1 - s := by linarith
  have hp := pilotTau_range n M hM sample
  rcases hp with ⟨hpL, hpU⟩
  have htL : -M * s ≤ t := by
    have heq : -M * s = ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v * (-M) := by
      dsimp [s]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    rw [heq]
    dsimp [t]
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (conditionalEstimator_range n M rho hM sample u v).1
      (poissonWeight_nonneg n u v)
  have htU : t ≤ M * s := by
    have heq : M * s = ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v * M := by
      dsimp [s]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    rw [heq]
    dsimp [t]
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (conditionalEstimator_range n M rho hM sample u v).2
      (poissonWeight_nonneg n u v)
  change t + (1 - s) * pilotTau n M sample ∈ Icc (-M) M
  constructor
  · have h := mul_le_mul_of_nonneg_left hpL hs0
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hpU hs0
    nlinarith

noncomputable def knownRadiusEstimatorAsEstimator (n : ℕ) (M rho : ℝ)
    (hM : 0 ≤ M) :
    DiscreteAteHeterogeneityFrontier.Estimator n n M :=
  ⟨knownRadiusEstimator n M rho,
    knownRadiusEstimator_measurable n M rho,
    knownRadiusEstimator_range n M rho hM⟩

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
