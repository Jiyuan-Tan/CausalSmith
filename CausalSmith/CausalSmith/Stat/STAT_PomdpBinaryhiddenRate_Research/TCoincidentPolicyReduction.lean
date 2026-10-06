module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.InterventionMoments
public import Mathlib.Probability.Moments.Variance

/-!
# Coincident-policy reduction

When target and behavior policies agree, intervention moments reduce to the
on-policy stationary reward mean and the empirical mean has parametric risk.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Coincident policies induce the same transition matrix and selected stationary law. [Under the listed formal conditions](hyp:heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_kernel_stationary
lemma coincidentPolicy_kernel_stationary {T : Nat}
    (M : RawPomdpExperiment T 2 2) (heq : M.e = M.b) :
    policyKernel M M.e = policyKernel M M.b ∧
    stationaryLaw (policyKernel M M.e) = stationaryLaw (policyKernel M M.b) := by
  constructor <;> simp only [heq]

/-- An action drawn from the behavior policy has positive behavior mass almost surely. [Under the listed formal conditions](hyp:hI), [the stated conclusion holds](goal).-/
-- @node: sequentialIgnorability_supported_action
lemma sequentialIgnorability_supported_action {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hI : SequentialIgnorability M) (t : Fin T) :
    ∀ᵐ tau ∂M.law, M.b (curState t tau).1 (actionAt t tau) ≠ 0 := by
  have hm : Measurable (histActionPair (nX := 2) (nH := 2) t) := by
    unfold histActionPair histStateView curState actionAt
    fun_prop
  have hp : MeasurableSet {h : ActionHistoryView T 2 2 t | M.b h.1.2.1 h.2 ≠ 0} := by
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  apply (ae_map_iff hm.aemeasurable hp).mp
  rw [hI.2 t]
  apply Measure.ae_compProd_of_ae_ae hp
  apply Filter.Eventually.of_forall
  intro h
  change ∀ᵐ a ∂(∑ a : Bool, ENNReal.ofReal (M.b h.2.1 a) • Measure.dirac a),
    M.b h.2.1 a ≠ 0
  rw [ae_finsetSum_measure_iff]
  intro a ha
  by_cases hb : M.b h.2.1 a = 0
  · simp [hb]
  · apply Measure.ae_smul_measure
    simpa using hb

/-- At coincident policies the zero-lag importance score equals the reward,
including when the behavior policy has zero cells. [Under the listed formal conditions](hyp:hI,heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_score_zero_ae
lemma coincidentPolicy_score_zero_ae {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hI : SequentialIgnorability M)
    (heq : M.e = M.b) (t : Fin T) :
    (fun tau => score 0 M.b M.e (obsProj tau) t) =ᵐ[M.law] rewardAt t := by
  have hfilter : Finset.univ.filter
      (fun j : Fin T => j.val ≤ t.val ∧ t.val - j.val ≤ 0) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      omega
    · intro hj
      subst j
      omega
  filter_upwards [sequentialIgnorability_supported_action M hI t] with tau ht
  unfold score
  rw [hfilter]
  simp [ratio, heq, obsProj, ht]

/-- The stationary reward mean is the causal target when policies coincide. [Under the listed formal conditions](hyp:ht0,hK,hI,hS,hB,heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_reward_mean
lemma coincidentPolicy_reward_mean {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2) (ht0 : 0 < t0)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) (t : Fin T) :
    (∫ tau, rewardAt t tau ∂M.law) = targetValue M := by
  calc
    _ = populationMoment M 0 t :=
      (integral_congr_ae (coincidentPolicy_score_zero_ae M hI heq t)).symm
    _ = _ := observable_intervention_moment_zero M ht0 hK hI hS hB heq t

/-- The observed sample mean is unbiased at coincident policies. [Under the listed formal conditions](hyp:ht0,hT,hK,hI,hS,hB,heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_sampleMean_unbiased
lemma coincidentPolicy_sampleMean_unbiased {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2) (ht0 : 0 < t0) (hT : 1 ≤ T)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) :
    (∫ tau, ((T : ℝ)⁻¹ * ∑ t : Fin T, rewardAt t tau) ∂M.law) =
      targetValue M := by
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [coincidentPolicy_reward_mean M ht0 hK hI hS hB heq]
    have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
    simp [hTne]
  · intro t _
    exact pomdp_reward_integrable M hK t

/-- Coincident policies supply overlap radius zero and the same contraction for both kernels. [Under the listed formal conditions](hyp:ht0,hK,hI,hS,hB,heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_binaryClass
lemma coincidentPolicy_binaryClass {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2) (ht0 : 0 < t0)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) : BinaryPomdpClass t0 0 M := by
  refine ⟨ht0, le_refl 0, hK, hI, hS, ?_, hB, ?_⟩
  · constructor
    · simpa only [heq] using hI.1
    · intro x a
      simp only [heq, policyFactor, Real.exp_zero, one_mul, le_refl]
  · simpa only [TargetContraction, BehaviorContraction, heq] using hB

/-- Separated rewards have the geometric covariance bound at coincident policies. [Under the listed formal conditions](hyp:ht0,hK,hI,hS,hB,heq,htu), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_reward_covariance
lemma coincidentPolicy_reward_covariance {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2) (ht0 : 0 < t0)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) (t u : Fin T) (htu : t < u) :
    |covariance (rewardAt t) (rewardAt u) M.law| ≤
      mixingAlpha t0 ^ (u.val - t.val - 1) := by
  have hClass := coincidentPolicy_binaryClass M ht0 hK hI hS hB heq
  have hc := (observable_intervention_moments M hClass
    (0 : Fin 7) t (Nat.zero_le _)).2.2 u (by change 1 ≤ u.val - t.val; omega)
  have he : scoreCovariance M 0 t u = covariance (rewardAt t) (rewardAt u) M.law := by
    unfold scoreCovariance covariance
    rw [observable_intervention_moment_zero M ht0 hK hI hS hB heq t,
      observable_intervention_moment_zero M ht0 hK hI hS hB heq u,
      coincidentPolicy_reward_mean M ht0 hK hI hS hB heq t,
      coincidentPolicy_reward_mean M ht0 hK hI hS hB heq u]
    apply integral_congr_ae
    filter_upwards [coincidentPolicy_score_zero_ae M hI heq t,
      coincidentPolicy_score_zero_ae M hI heq u] with tau ht hu
    rw [ht, hu]
  simpa only [Fin.val_zero, Nat.sub_zero, he] using hc

/-- A finite geometric tail is bounded by the infinite-series value. [Under the listed formal conditions](hyp:ha0,ha1), [the stated conclusion holds](goal).-/
-- @node: finiteGeometric_sum_le
lemma finiteGeometric_sum_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (n : Nat) :
    ∑ j ∈ Finset.range n, a ^ j ≤ 1 / (1 - a) := by
  have hgeom := geom_sum_mul a n
  have hp : 0 ≤ a ^ n := pow_nonneg ha0 n
  apply (le_div_iff₀ (sub_pos.mpr ha1)).mpr
  nlinarith

/-- An injectively indexed subset of a geometric tail satisfies the same bound. [Under the listed formal conditions](hyp:ha0,ha1,hf,hinj), [the stated conclusion holds](goal).-/
-- @node: finiteGeometric_sum_image_le
lemma finiteGeometric_sum_image_le {ι : Type*}
    (s : Finset ι) (f : ι → Nat) (n : Nat) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hf : ∀ i ∈ s, f i < n) (hinj : Set.InjOn f ↑s) :
    ∑ i ∈ s, a ^ f i ≤ 1 / (1 - a) := by
  classical
  apply le_trans _ (finiteGeometric_sum_le a ha0 ha1 n)
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hf i hi)
  · intro j _ _
    exact pow_nonneg ha0 j

/-- A symmetric covariance row with unit diagonal and geometric off-diagonal
bounds has total mass at most one plus two geometric tails. [Under the listed formal conditions](hyp:ha0,ha1,hsymm,hdiag,hupper), [the stated conclusion holds](goal).-/
-- @node: geometricCovariance_row_sum_le
lemma geometricCovariance_row_sum_le {T : Nat} (f : Fin T → Fin T → ℝ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hsymm : ∀ t u, f t u = f u t) (hdiag : ∀ t, f t t ≤ 1)
    (hupper : ∀ t u, t < u → f t u ≤ a ^ (u.val - t.val - 1)) (t : Fin T) :
    ∑ u, f t u ≤ 1 + 2 / (1 - a) := by
  have hsplit : (∑ u, f t u) = f t t +
      (∑ u ∈ Finset.univ.filter (fun u => u < t), f t u) +
      (∑ u ∈ Finset.univ.filter (fun u => t < u), f t u) := by
    calc
      _ = (∑ u : Fin T, if u = t then f t t else 0) +
          (∑ u : Fin T, if u < t then f t u else 0) +
          (∑ u : Fin T, if t < u then f t u else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        rcases lt_trichotomy u t with h | h | h
        · simp [h, ne_of_lt h, not_lt_of_gt h]
        · subst u
          simp
        · simp [h, ne_of_gt h, not_lt_of_gt h]
      _ = _ := by simp [Finset.sum_filter]
  have hpast : (∑ u ∈ Finset.univ.filter (fun u => u < t), f t u) ≤
      1 / (1 - a) := by
    calc
      _ ≤ ∑ u ∈ Finset.univ.filter (fun u => u < t), a ^ (t.val - u.val - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [hsymm]
        exact hupper u t (Finset.mem_filter.mp hu).2
      _ ≤ _ := by
        apply finiteGeometric_sum_image_le _ _ T a ha0 ha1
        · intro u hu
          have hut := (Finset.mem_filter.mp hu).2
          omega
        · intro u hu w hw heq
          have hut := (Finset.mem_filter.mp hu).2
          have hwt := (Finset.mem_filter.mp hw).2
          dsimp only at heq
          apply Fin.ext
          omega
  have hfuture : (∑ u ∈ Finset.univ.filter (fun u => t < u), f t u) ≤
      1 / (1 - a) := by
    calc
      _ ≤ ∑ u ∈ Finset.univ.filter (fun u => t < u), a ^ (u.val - t.val - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hupper t u (Finset.mem_filter.mp hu).2
      _ ≤ _ := by
        apply finiteGeometric_sum_image_le _ _ T a ha0 ha1
        · intro u hu
          have htu := (Finset.mem_filter.mp hu).2
          omega
        · intro u hu w hw heq
          have htu := (Finset.mem_filter.mp hu).2
          have htw := (Finset.mem_filter.mp hw).2
          dsimp only at heq
          apply Fin.ext
          omega
  rw [hsplit]
  simp only [div_eq_mul_inv, one_mul] at hpast hfuture ⊢
  linarith [hdiag t]

/-- Expanding the covariance sum gives the stated parametric on-policy risk bound. [Under the listed formal conditions](hyp:ht0,hT,hK,hI,hS,hB,heq), [the stated conclusion holds](goal).-/
-- @node: coincidentPolicy_sampleMean_mse
lemma coincidentPolicy_sampleMean_mse {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2) (ht0 : 0 < t0) (hT : 1 ≤ T)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) :
    (∫ tau, (((T : ℝ)⁻¹ * ∑ t : Fin T, rewardAt t tau) -
      targetValue M) ^ 2 ∂M.law) ≤
      (1 + 2 / (1 - mixingAlpha t0)) / T := by
  have hLp (t : Fin T) : MemLp (rewardAt t) 2 M.law :=
    memLp_of_bounded (pomdp_reward_mem_Icc_ae M hK t)
      (by unfold rewardAt; fun_prop) 2
  have ha0 : 0 ≤ mixingAlpha t0 := (Real.exp_pos _).le
  have ha1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr ht0))
  have hdiag (t : Fin T) : covariance (rewardAt t) (rewardAt t) M.law ≤ 1 := by
    rw [covariance_self (by unfold rewardAt; fun_prop), variance_eq_sub (hLp t)]
    have hs : (∫ tau, rewardAt t tau ^ 2 ∂M.law) ≤ 1 := by
      calc
        _ ≤ ∫ _tau, (1 : ℝ) ∂M.law := by
          apply integral_mono_ae (hLp t).integrable_sq (integrable_const _)
          filter_upwards [pomdp_reward_mem_Icc_ae M hK t] with tau ht
          nlinarith [ht.1, ht.2]
        _ = 1 := by simp
    change (∫ tau, rewardAt t tau ^ 2 ∂M.law) -
      (∫ tau, rewardAt t tau ∂M.law) ^ 2 ≤ 1
    linarith [sq_nonneg (∫ tau, rewardAt t tau ∂M.law)]
  have hsum : variance (fun tau => ∑ t : Fin T, rewardAt t tau) M.law ≤
      (T : ℝ) * (1 + 2 / (1 - mixingAlpha t0)) := by
    rw [variance_fun_sum hLp]
    calc
      _ ≤ ∑ _t : Fin T, (1 + 2 / (1 - mixingAlpha t0)) := by
        apply Finset.sum_le_sum
        intro t _
        apply geometricCovariance_row_sum_le
          (fun t u => covariance (rewardAt t) (rewardAt u) M.law) _ ha0 ha1 _ _ _ t
        · intro t u
          exact covariance_comm _ _
        · exact hdiag
        · intro t u htu
          exact (le_abs_self _).trans
            (coincidentPolicy_reward_covariance M ht0 hK hI hS hB heq t u htu)
      _ = _ := by simp; ring
  have hmean := coincidentPolicy_sampleMean_unbiased M ht0 hT hK hI hS hB heq
  have hmeas : AEMeasurable
      (fun tau => (T : ℝ)⁻¹ * ∑ t : Fin T, rewardAt t tau) M.law := by
    unfold rewardAt
    fun_prop
  rw [← hmean, ← variance_eq_integral hmeas, variance_const_mul]
  calc
    _ ≤ (T : ℝ)⁻¹ ^ 2 * ((T : ℝ) * (1 + 2 / (1 - mixingAlpha t0))) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
      field_simp

-- @node: prop:coincident-policy-reduction
/-- For [positive mixing time](hyp:ht0), a [nonempty horizon](hyp:hT), the
[POMDP kernel law](hyp:hK), [sequential ignorability](hyp:hI),
[stationary start](hyp:hS), [behavior contraction](hyp:hB), and
[coincident policies](hyp:heq), the [on-policy identity, unbiased sample mean,
and variance bound](goal) hold. -/
theorem coincidentPolicy_reduction {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2)
    (ht0 : 0 < t0) (hT : 1 ≤ T)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) :
    policyKernel M M.e = policyKernel M M.b ∧
    stationaryLaw (policyKernel M M.e) = stationaryLaw (policyKernel M M.b) ∧
    (∀ t : Fin T, populationMoment M 0 t = targetValue M) ∧
    (∫ tau, ((T : ℝ)⁻¹ * ∑ t : Fin T, rewardAt t tau) ∂M.law) =
      targetValue M ∧
    (∫ tau, (((T : ℝ)⁻¹ * ∑ t : Fin T, rewardAt t tau) -
      targetValue M) ^ 2 ∂M.law) ≤
      (1 + 2 / (1 - mixingAlpha t0)) / T := by
  obtain ⟨hP, hd⟩ := coincidentPolicy_kernel_stationary M heq
  refine ⟨hP, hd, ?_, ?_⟩
  · intro t
    exact observable_intervention_moment_zero M ht0 hK hI hS hB heq t
  constructor
  · exact coincidentPolicy_sampleMean_unbiased M ht0 hT hK hI hS hB heq
  · exact coincidentPolicy_sampleMean_mse M ht0 hT hK hI hS hB heq

end CausalSmith.Stat.PomdpBinaryhiddenRate
