module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepth
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
public import Causalean.Stat.Minimax.BretagnolleHuber
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Mathlib.InformationTheory.KLBind
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Mathlib.Probability.SignedTwoPoint
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule

set_option linter.style.longLine false

/-! # Explicit and existential two-point lower-bound wrappers -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Transport an observed law along equality of the revealed alphabet cardinality. -/
noncomputable def castObsLaw {T nX0 nX1 nH : Nat} (h : nX0 = nX1)
    (M : RawPomdpExperiment T nX1 nH) : Measure (ObsView T nX0) :=
  h.symm ▸ obsLaw M

/-- Explicit two-point risk floor with every analytic side condition visible. [the h X condition](hyp:hX); and [the hb condition](hyp:hb); and [the he condition](hyp:he); and [the h T condition](hyp:hT); and [the hs condition](hyp:hs); and [the h Knonneg condition](hyp:hKnonneg); and [the h KL condition](hyp:hKL); and [the hac condition](hyp:hac); and [the hfin condition](hyp:hfin); and [the hsep condition](hyp:hsep). [the stated conclusion](goal). -/
lemma two_point_floor_explicit {T : Nat} {t0 zeta C s K : ℝ}
    (M0 M1 : ModelIndex T t0 zeta C)
    (hX : M0.nX = M1.nX)
    (hb : HEq M0.raw.b M1.raw.b) (he : HEq M0.raw.e M1.raw.e)
    (hT : 1 ≤ T) (hs : 0 ≤ s)
    (hKnonneg : 0 ≤ K)
    (hKL : InformationTheory.klDiv (obsLaw M0.raw) (castObsLaw hX M1.raw) ≤ ENNReal.ofReal K)
    (hac : obsLaw M0.raw ≪ castObsLaw hX M1.raw)
    (hfin : InformationTheory.klDiv (obsLaw M0.raw) (castObsLaw hX M1.raw) ≠ ⊤)
    (hsep : 2 * s ≤ |targetValue M0.raw - targetValue M1.raw|) :
    (∀ est : RawEstimator T,
      (∀ nX b e, Measurable (est nX b e)) →
      Integrable (fun w ↦ (est M0.nX M0.raw.b M0.raw.e w - targetValue M0.raw) ^ 2)
        (obsLaw M0.raw) →
      Integrable (fun w ↦ (est M1.nX M1.raw.b M1.raw.e w - targetValue M1.raw) ^ 2)
        (obsLaw M1.raw) →
      s ^ 2 * Real.exp (-K) / 4 ≤
        max (rawObservedRisk est M0) (rawObservedRisk est M1)) ∧
    s ^ 2 * Real.exp (-K) / 4 ≤ minimaxRisk T t0 zeta C := by
  rcases M0 with ⟨_hT0, nX0, nH0, M0, hM0⟩
  rcases M1 with ⟨_hT1, nX1, nH1, M1, hM1⟩
  dsimp only at hX
  subst nX1
  have hb' : M0.b = M1.b := eq_of_heq hb
  have he' : M0.e = M1.e := eq_of_heq he
  dsimp only [castObsLaw] at hKL hac hfin ⊢
  letI : IsProbabilityMeasure (obsLaw M0) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by
      unfold obsProj curState actionAt rewardAt
      measurability)
  letI : IsProbabilityMeasure (obsLaw M1) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by
      unfold obsProj curState actionAt rewardAt
      measurability)
  have hkl_toReal :
      (InformationTheory.klDiv (obsLaw M0) (obsLaw M1)).toReal ≤ K := by
    calc
      (InformationTheory.klDiv (obsLaw M0) (obsLaw M1)).toReal ≤
          (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
      _ = K := ENNReal.toReal_ofReal hKnonneg
  have hexp : Real.exp (-K) ≤
      Real.exp (-(InformationTheory.klDiv (obsLaw M0) (obsLaw M1)).toReal) :=
    Real.exp_le_exp.mpr (neg_le_neg hkl_toReal)
  have hBH := Causalean.Stat.bretagnolle_huber_affinity
    (obsLaw M0) (obsLaw M1) hac hfin
  have pointwise : ∀ est : RawEstimator T,
      (∀ nX b e, Measurable (est nX b e)) →
      Integrable (fun w ↦ (est nX0 M0.b M0.e w - targetValue M0) ^ 2) (obsLaw M0) →
      Integrable (fun w ↦ (est nX0 M1.b M1.e w - targetValue M1) ^ 2) (obsLaw M1) →
      s ^ 2 * Real.exp (-K) / 4 ≤
        max (rawObservedRisk est ⟨_hT0, nX0, nH0, M0, hM0⟩)
          (rawObservedRisk est ⟨_hT1, nX0, nH1, M1, hM1⟩) := by
    intro est hmeas hint0 hint1
    have hint1' :
        Integrable (fun w ↦ (est nX0 M0.b M0.e w - targetValue M1) ^ 2) (obsLaw M1) := by
      simpa only [hb', he'] using hint1
    have htest := Causalean.Stat.real_two_point_lower_bound
      (P₀ := obsLaw M0) (P₁ := obsLaw M1) (hmeas nX0 M0.b M0.e) hsep
    have hset0 :
        {w : ObsView T nX0 | s ≤ |est nX0 M0.b M0.e w - targetValue M0|} =
          {w | s ^ 2 ≤ (est nX0 M0.b M0.e w - targetValue M0) ^ 2} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hw <;>
        nlinarith [hs, abs_nonneg (est nX0 M0.b M0.e w - targetValue M0),
          sq_abs (est nX0 M0.b M0.e w - targetValue M0)]
    have hset1 :
        {w : ObsView T nX0 | s ≤ |est nX0 M0.b M0.e w - targetValue M1|} =
          {w | s ^ 2 ≤ (est nX0 M0.b M0.e w - targetValue M1) ^ 2} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hw <;>
        nlinarith [hs, abs_nonneg (est nX0 M0.b M0.e w - targetValue M1),
          sq_abs (est nX0 M0.b M0.e w - targetValue M1)]
    have hmse0 : s ^ 2 * (obsLaw M0).real
          {w | s ≤ |est nX0 M0.b M0.e w - targetValue M0|} ≤
        ∫ w, (est nX0 M0.b M0.e w - targetValue M0) ^ 2 ∂obsLaw M0 := by
      rw [hset0]
      exact mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun w ↦ sq_nonneg
          (est nX0 M0.b M0.e w - targetValue M0)) hint0 (s ^ 2)
    have hmse1 : s ^ 2 * (obsLaw M1).real
          {w | s ≤ |est nX0 M0.b M0.e w - targetValue M1|} ≤
        ∫ w, (est nX0 M0.b M0.e w - targetValue M1) ^ 2 ∂obsLaw M1 := by
      rw [hset1]
      exact mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun w ↦ sq_nonneg
          (est nX0 M0.b M0.e w - targetValue M1)) hint1' (s ^ 2)
    have hprob : Real.exp (-K) / 4 ≤
        max ((obsLaw M0).real {w | s ≤ |est nX0 M0.b M0.e w - targetValue M0|})
          ((obsLaw M1).real {w | s ≤ |est nX0 M0.b M0.e w - targetValue M1|}) := by
      calc
        Real.exp (-K) / 4 ≤ (1 - Causalean.Stat.tvDist (obsLaw M0) (obsLaw M1)) / 2 := by
          nlinarith [hexp, hBH, Real.exp_pos (-K)]
        _ ≤ _ := htest
    unfold rawObservedRisk Causalean.Stat.sqRisk
    rw [← hb', ← he']
    by_cases h01 : (obsLaw M0).real
        {w | s ≤ |est nX0 M0.b M0.e w - targetValue M0|} ≤
      (obsLaw M1).real {w | s ≤ |est nX0 M0.b M0.e w - targetValue M1|}
    · rw [max_eq_right h01] at hprob
      calc
        s ^ 2 * Real.exp (-K) / 4 = s ^ 2 * (Real.exp (-K) / 4) := by ring
        _ ≤ s ^ 2 * (obsLaw M1).real
            {w | s ≤ |est nX0 M0.b M0.e w - targetValue M1|} :=
          mul_le_mul_of_nonneg_left hprob (sq_nonneg s)
        _ ≤ ∫ w, (est nX0 M0.b M0.e w - targetValue M1) ^ 2 ∂obsLaw M1 := hmse1
        _ ≤ max (∫ w, (est nX0 M0.b M0.e w - targetValue M0) ^ 2 ∂obsLaw M0)
            (∫ w, (est nX0 M0.b M0.e w - targetValue M1) ^ 2 ∂obsLaw M1) := le_max_right _ _
    · have h10 := le_of_not_ge h01
      rw [max_eq_left h10] at hprob
      calc
        s ^ 2 * Real.exp (-K) / 4 = s ^ 2 * (Real.exp (-K) / 4) := by ring
        _ ≤ s ^ 2 * (obsLaw M0).real
            {w | s ≤ |est nX0 M0.b M0.e w - targetValue M0|} :=
          mul_le_mul_of_nonneg_left hprob (sq_nonneg s)
        _ ≤ ∫ w, (est nX0 M0.b M0.e w - targetValue M0) ^ 2 ∂obsLaw M0 := hmse0
        _ ≤ max (∫ w, (est nX0 M0.b M0.e w - targetValue M0) ^ 2 ∂obsLaw M0)
            (∫ w, (est nX0 M0.b M0.e w - targetValue M1) ^ 2 ∂obsLaw M1) := le_max_left _ _
  constructor
  · exact pointwise
  · let zeroEst : ObservableEstimator T :=
      ⟨fun _ _ _ _ ↦ 0, ⟨by intros; constructor <;> norm_num, by intros; fun_prop⟩⟩
    letI : Nonempty (ObservableEstimator T) := ⟨zeroEst⟩
    apply Causalean.Stat.le_minimaxValue_of_two_point
      ⟨_hT0, nX0, nH0, M0, hM0⟩ ⟨_hT1, nX0, nH1, M1, hM1⟩
    · intro est
      exact bddAbove_range_observedRisk est
    · intro est
      have hint (M : RawPomdpExperiment T nX0 nH0) (theta : ℝ) :
          Integrable (fun w ↦ (est.1 nX0 M.b M.e w - theta) ^ 2) (obsLaw M) := by
        letI : IsProbabilityMeasure (obsLaw M) := by
          unfold obsLaw
          exact Measure.isProbabilityMeasure_map (by
            unfold obsProj curState actionAt rewardAt
            measurability)
        apply Integrable.of_bound
          ((est.2.2 nX0 M.b M.e).sub measurable_const |>.pow_const 2 |>.aestronglyMeasurable)
          ((1 + |theta|) ^ 2)
        filter_upwards with w
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hew := est.2.1 nX0 M.b M.e w
        have habs : |est.1 nX0 M.b M.e w| ≤ 1 := abs_le.mpr hew
        have habssub : |est.1 nX0 M.b M.e w - theta| ≤ 1 + |theta| :=
          (abs_sub _ _).trans (by linarith)
        calc
          (est.1 nX0 M.b M.e w - theta) ^ 2 =
              |est.1 nX0 M.b M.e w - theta| *
                |est.1 nX0 M.b M.e w - theta| := by rw [← sq_abs, pow_two]
          _ ≤ (1 + |theta|) * (1 + |theta|) :=
            mul_self_le_mul_self
              (abs_nonneg (est.1 nX0 M.b M.e w - theta)) habssub
          _ = (1 + |theta|) ^ 2 := by ring
      exact pointwise est.1 est.2.2 (hint M0 (targetValue M0))
        (by
          letI : IsProbabilityMeasure (obsLaw M1) := by
            unfold obsLaw
            exact Measure.isProbabilityMeasure_map (by
              unfold obsProj curState actionAt rewardAt
              measurability)
          apply Integrable.of_bound
            ((est.2.2 nX0 M1.b M1.e).sub measurable_const |>.pow_const 2 |>.aestronglyMeasurable)
            ((1 + |targetValue M1|) ^ 2)
          filter_upwards with w
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hew := est.2.1 nX0 M1.b M1.e w
          have habs : |est.1 nX0 M1.b M1.e w| ≤ 1 := abs_le.mpr hew
          have habssub : |est.1 nX0 M1.b M1.e w - targetValue M1| ≤
              1 + |targetValue M1| :=
            (abs_sub _ _).trans (by linarith)
          calc
            (est.1 nX0 M1.b M1.e w - targetValue M1) ^ 2 =
                |est.1 nX0 M1.b M1.e w - targetValue M1| *
                  |est.1 nX0 M1.b M1.e w - targetValue M1| := by
              rw [← sq_abs, pow_two]
            _ ≤ (1 + |targetValue M1|) * (1 + |targetValue M1|) :=
              mul_self_le_mul_self
                (abs_nonneg (est.1 nX0 M1.b M1.e w - targetValue M1)) habssub
            _ = (1 + |targetValue M1|) ^ 2 := by ring)

/-- The parametric amplitude `1/(4 sqrt T)`. -/
noncomputable def parametricAmplitude (T : Nat) : ℝ := 1 / (4 * Real.sqrt T)

/-- The equal-policy Rademacher finite witness. -/
noncomputable def parametricPairFinite (T : Nat) (v : Bool) :
    FiniteRewardModel T 1 1 2 :=
  let K : JointState 1 1 → Bool → PMF (Fin 2 × JointState 1 1) :=
    fun _ _ ↦ pmfOfRealWeight fun p ↦
      (1 + (if p.1 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2
  let init : PMF (JointState 1 1) := pmfOfRealWeight fun _ ↦ 1
  let p : Fin 1 → PMF Bool := fun _ ↦ pmfOfRealWeight fun _ ↦ 1 / 2
  { kernel := K
    rew := fun r ↦ if r = 0 then -1 else 1
    rew_mem := by
      intro r
      fin_cases r <;> norm_num
    init := init
    b := p
    e := p
    law := finitePathPMF K init p
    law_generated := finitePathPMF_apply K init p }

-- @node: parametricPair_stationaryStart
/-- The singleton-state parametric path starts from its stationary law. [the stated conclusion](goal). -/
lemma parametricPair_stationaryStart (T : Nat) (v : Bool) :
    StationaryStart (embed (parametricPairFinite T v)) := by
  let F := parametricPairFinite T v
  have hinit : (embed F).init (0, 0) = 1 := by
    change (F.init (0, 0)).toReal = 1
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_one] using
      sum_pmf_toReal_eq_one F.init
  have hb : PolicyVector (embed F).b := (embed_sequentialIgnorability F).1
  have hstat : IsStationary (policyKernel (embed F) (embed F).b) (embed F).init := by
    constructor
    · constructor
      · intro s
        exact ENNReal.toReal_nonneg
      · rw [Fintype.sum_prod_type]
        simpa only [Fin.sum_univ_one] using hinit
    · intro s'
      have hs' : s' = (0, 0) := Subsingleton.elim _ _
      subst s'
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_one, hinit, one_mul]
      have hrow := (policyKernel_probabilityVector (embed F) (embed_pomdpKernelLaw F)
        (embed F).b hb (0, 0)).2
      rw [Fintype.sum_prod_type] at hrow
      simpa only [Fin.sum_univ_one] using hrow
  have hsel : stationaryLaw (policyKernel (embed F) (embed F).b) = (embed F).init := by
    funext s
    have hs : s = (0, 0) := Subsingleton.elim _ _
    subst s
    have hselected :=
      (stationaryLaw_isStationary_of_exists (P := policyKernel (embed F) (embed F).b)
        ⟨(embed F).init, hstat⟩).1.2
    rw [Fintype.sum_prod_type] at hselected
    simpa only [Fin.sum_univ_one, hinit] using hselected
  exact embed_stationaryStart F hstat hsel

/-- Given [a positive time parameter](hyp:ht0), [a positive overlap parameter](hyp:hzeta), and
[a reward bound of at least one](hyp:hC), the [embedded parametric witness belongs to the
seven-predicate latent-overlap class](goal). -/
lemma parametricPair_mem (T : Nat) (t0 zeta C : ℝ) (v : Bool)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) :
    LatentOverlapClass t0 zeta C (embed (parametricPairFinite T v)) := by
    let F := parametricPairFinite T v
    have hbe : (embed F).b = (embed F).e := rfl
    refine
      { t0_pos := ht0
        zeta_pos := hzeta
        pomdp_kernel := embed_pomdpKernelLaw F
        sequential_ignorability := embed_sequentialIgnorability F
        stationary_start := parametricPair_stationaryStart T v
        bounded_reward := embed_boundedReward F
        policy_overlap := ?_
        uniform_contraction := ?_
        latent_stationary_overlap := ?_ }
    · constructor
      · simpa [hbe] using (embed_sequentialIgnorability F).1
      · intro x a
        rw [← hbe]
        have hnonneg : 0 ≤ (embed F).b x a :=
          ((embed_sequentialIgnorability F).1 x).1 a
        have hL : 1 ≤ policyFactor zeta := by
          rw [policyFactor]
          exact Real.one_le_exp hzeta.le
        nlinarith
    · intro p hp nu nu' hnu hnu'
      have hpv : PolicyVector p := by
        rcases hp with hp | hp
        · rw [hp]
          exact (embed_sequentialIgnorability F).1
        · rw [hp, ← hbe]
          exact (embed_sequentialIgnorability F).1
      have hkernel : policyKernel (embed F) p = fun _ _ ↦ 1 := by
        funext s s'
        unfold policyKernel
        have hp_sum : ∑ a : Bool, p s.1 a = 1 := (hpv s.1).2
        have hnext (a : Bool) :
            ((embed F).K s a {q | q.2 = s'}).toReal = 1 := by
          letI : IsProbabilityMeasure ((embed F).K s a) :=
            (embed_pomdpKernelLaw F).1 s a
          have hset : {q : Step 1 1 | q.2 = s'} = Set.univ := by
            ext q
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            exact Subsingleton.elim _ _
          rw [hset, measure_univ]
          norm_num
        simp_rw [hnext, mul_one]
        exact hp_sum
      rw [hkernel]
      have happ (q : JointState 1 1 → ℝ) (hq : ProbabilityVector q) :
          applyKernel q (fun _ _ ↦ (1 : ℝ)) = fun _ ↦ 1 := by
        funext s
        unfold applyKernel
        simpa using hq.2
      rw [happ nu hnu, happ nu' hnu']
      have htv : 0 ≤ tvNorm (nu - nu') := by
        unfold tvNorm
        positivity
      simp only [sub_self, tvNorm, Pi.zero_apply, abs_zero, Finset.sum_const_zero,
        mul_zero]
      exact mul_nonneg (Real.exp_nonneg _) htv
    · constructor
      · exact hC
      · intro s
        rw [hbe]
        have hstat : IsStationary (policyKernel (embed F) (embed F).b)
            (stationaryLaw (policyKernel (embed F) (embed F).b)) :=
          (parametricPair_stationaryStart T v).1
        have hprob := hstat.1.1 s
        exact le_mul_of_one_le_left hprob hC

/-- At [a positive horizon](hyp:hT), the embedded parametric witness is packaged as
[an indexed member of the paper class](goal). -/
noncomputable def parametricModel (T : Nat) (t0 zeta C : ℝ) (v : Bool)
    (hT : 1 ≤ T) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) :
    ModelIndex T t0 zeta C where
  horizon_pos := hT
  nX := 1
  nH := 1
  raw := embed (parametricPairFinite T v)
  mem := parametricPair_mem T t0 zeta C v ht0 hzeta hC

/-- Every finite observed word has positive mass under either parametric alternative. [the stated conclusion](goal). -/
lemma parametricPair_fullSupportObs {T : Nat} {v : Bool} :
    FullSupportPMF (parametricPairFinite T v).obsPMF := by
  classical
  letI : DecidableEq (FiniteObsView T 1 2) := Classical.decEq _
  intro w
  let tau : FiniteTrajectory T 1 1 2 :=
    (fun _ ↦ (0, 0), fun t ↦ ((w t).2.1, (w t).2.2))
  have hproj : finObsProj tau = w := by
    funext t
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  have hTamp : T = 0 ∨ parametricAmplitude T ≤ 1 / 4 := by
    by_cases hT0 : T = 0
    · exact Or.inl hT0
    · right
      have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
      have hsqrt : 1 ≤ Real.sqrt T := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hT1)
      unfold parametricAmplitude
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
  have hpmf_pos {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (a : A)
      (hfa : 0 < f a) : 0 < pmfOfRealWeight f a := by
    have hsum : ∑' x, ENNReal.ofReal (f x) ≠ 0 := by
      apply ne_of_gt
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hfa)
        (ENNReal.le_tsum a)
    rw [pmfOfRealWeight, dif_neg hsum, PMF.normalize_apply]
    apply ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hfa))
    rw [ENNReal.inv_ne_zero]
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun x _ ↦ ENNReal.ofReal_ne_top
  have hinit : 0 < (parametricPairFinite T v).init (tau.1 0) := by
    simp only [parametricPairFinite]
    apply hpmf_pos
    norm_num
  have hb : ∀ t : Fin T,
      0 < (parametricPairFinite T v).b (tau.1 t.castSucc).1 (tau.2 t).1 := by
    intro t
    simp only [parametricPairFinite]
    apply hpmf_pos
    norm_num
  have hkernel : ∀ t : Fin T,
      0 < (parametricPairFinite T v).kernel (tau.1 t.castSucc) (tau.2 t).1
        ((tau.2 t).2, tau.1 t.succ) := by
    intro t
    simp only [parametricPairFinite]
    apply hpmf_pos
    rcases hTamp with hT0 | hamp
    · exact (Fin.elim0 (hT0 ▸ t))
    · have hamp_nonneg : 0 ≤ parametricAmplitude T := by
        unfold parametricAmplitude
        positivity
      have hr : (tau.2 t).2 = 0 ∨ (tau.2 t).2 = 1 := by omega
      rcases hr with hr | hr <;> cases v <;>
        simp [signedValue, hr] <;> linarith
  have hlaw : 0 < (parametricPairFinite T v).law tau := by
    rw [(parametricPairFinite T v).law_generated tau]
    apply ENNReal.mul_pos (ne_of_gt hinit)
    rw [Finset.prod_ne_zero_iff]
    intro t _
    exact ne_of_gt (ENNReal.mul_pos (ne_of_gt (hb t)) (ne_of_gt (hkernel t)))
  unfold FiniteRewardModel.obsPMF
  rw [PMF.map_apply]
  have hle := ENNReal.le_tsum
    (f := fun a : FiniteTrajectory T 1 1 2 ↦
      if w = finObsProj a then (parametricPairFinite T v).law a else 0) tau
  have hle' : (parametricPairFinite T v).law tau ≤
      ∑' a, if w = finObsProj a then (parametricPairFinite T v).law a else 0 := by
    simpa [hproj] using hle
  exact lt_of_lt_of_le hlaw hle'

/-- Squared risk at a raw experiment, before packaging class membership at a
particular overlap radius. -/
noncomputable def rawExperimentRisk {T nX nH : Nat} (est : RawEstimator T)
    (M : RawPomdpExperiment T nX nH) : ℝ :=
  Causalean.Stat.sqRisk (obsLaw M) (est nX M.b M.e) (targetValue M)

-- @node: parametricAmplitude_mem
/-- The parametric amplitude is nonnegative and at most one quarter. [the stated conclusion](goal). -/
lemma parametricAmplitude_mem (T : Nat) : parametricAmplitude T ∈ Set.Icc (0 : ℝ) (1 / 4) := by
  by_cases hT : T = 0
  · subst T
    simp [parametricAmplitude]
  · have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
    have hsqrt : 1 ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hT1)
    constructor
    · unfold parametricAmplitude
      positivity
    · unfold parametricAmplitude
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith

-- @node: parametricPair_kernel_toReal
/-- The normalized parametric kernel is its displayed Rademacher weight. [the stated conclusion](goal). -/
lemma parametricPair_kernel_toReal {T : Nat} (v : Bool) (s : JointState 1 1) (a : Bool)
    (p : Fin 2 × JointState 1 1) :
    ((parametricPairFinite T v).kernel s a p).toReal =
      (1 + (if p.1 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2 := by
  rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
  let w : Fin 2 × JointState 1 1 → ℝ := fun q ↦
    (1 + (if q.1 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    cases q with
    | mk r s' =>
      fin_cases r <;> cases v <;> simp [w, signedValue] <;> linarith
  have hsum : ∑ q, w q = 1 := by
    simp only [w, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
      Fin.sum_univ_two]
    cases v <;> simp [signedValue] <;> ring
  simp only [parametricPairFinite]
  change (pmfOfRealWeight w p).toReal = w p
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one w hw hsum,
    ENNReal.toReal_ofReal (hw p)]

-- @node: parametricPair_policy_toReal
/-- Both revealed policies of the parametric witness are fair coins. [the stated conclusion](goal). -/
lemma parametricPair_policy_toReal {T : Nat} (v : Bool) (x : Fin 1) (a : Bool) :
    ((parametricPairFinite T v).b x a).toReal = 1 / 2 ∧
      ((parametricPairFinite T v).e x a).toReal = 1 / 2 := by
  have hw : ∀ _ : Bool, 0 ≤ (1 / 2 : ℝ) := by intro; positivity
  have hsum : ∑ _ : Bool, (1 / 2 : ℝ) = 1 := by norm_num
  simp only [parametricPairFinite]
  constructor <;>
    rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hw hsum,
      ENNReal.toReal_ofReal (by positivity)]

-- @node: parametricPair_obsPMF_toReal
/-- The finite observed parametric law is the product of fair actions and i.i.d. rewards. [the stated conclusion](goal). -/
lemma parametricPair_obsPMF_toReal {T : Nat} (v : Bool) (w : FiniteObsView T 1 2) :
    ((parametricPairFinite T v).obsPMF w).toReal =
      ∏ t : Fin T, (1 / 2 : ℝ) *
        ((1 + (if (w t).2.2 = 0 then -1 else 1) *
          signedValue v * parametricAmplitude T) / 2) := by
  classical
  unfold FiniteRewardModel.obsPMF
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype]
    simp only [apply_ite, ENNReal.toReal_zero]
    simp_rw [(parametricPairFinite T v).law_generated]
    simp_rw [ENNReal.toReal_mul, ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_mul]
    let sigma0 : Fin (T + 1) → JointState 1 1 := fun _ ↦ (0, 0)
    letI : Unique (Fin (T + 1) → JointState 1 1) :=
      ⟨⟨sigma0⟩, fun _ ↦ Subsingleton.elim _ _⟩
    let o : Fin T → Bool × Fin 2 := fun t ↦ ((w t).2.1, (w t).2.2)
    rw [Fintype.sum_prod_type]
    simp_rw [Subsingleton.elim _ sigma0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul]
    have hproj : w = finObsProj (sigma0, o) := by
      symm
      funext t
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
    rw [Finset.sum_eq_single o]
    · simp only [hproj, if_true]
      have hinit : ((parametricPairFinite T v).init (0, 0)).toReal = 1 := by
        simp only [parametricPairFinite]
        rw [pmfOfRealWeight_apply_of_nonneg_sum_one]
        · norm_num
        · intro; norm_num
        · simp
      rw [show sigma0 0 = (0, 0) by rfl, hinit, one_mul]
      apply Finset.prod_congr rfl
      intro t _
      rw [(parametricPair_policy_toReal v _ _).1,
        parametricPair_kernel_toReal]
      rfl
    · intro o' _ hne
      have hnot : w ≠ finObsProj (sigma0, o') := by
        intro heq
        apply hne
        funext t
        have ht := congrFun heq t
        simpa [finObsProj, o] using (congrArg Prod.snd ht).symm
      simp [hnot]
    · simp
  · intro tau
    split <;> simp [PMF.apply_ne_top]

-- @node: parametricEpochPMF
/-- One observed epoch of the singleton-state parametric experiment. -/
noncomputable def parametricEpochPMF (T : Nat) (v : Bool) : PMF (Fin 1 × Bool × Fin 2) :=
  pmfOfRealWeight fun z ↦ (1 / 2 : ℝ) *
    ((1 + (if z.2.2 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2)

-- @node: parametricEpochPMF_toReal
/-- The one-epoch PMF has exactly its displayed fair-action/Rademacher weights. [the stated conclusion](goal). -/
lemma parametricEpochPMF_toReal (T : Nat) (v : Bool) (z : Fin 1 × Bool × Fin 2) :
    (parametricEpochPMF T v z).toReal = (1 / 2 : ℝ) *
      ((1 + (if z.2.2 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2) := by
  rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
  let q : Fin 1 × Bool × Fin 2 → ℝ := fun z ↦ (1 / 2 : ℝ) *
    ((1 + (if z.2.2 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2)
  have hq : ∀ z, 0 ≤ q z := by
    intro z'
    rcases z' with ⟨x, a, r⟩
    fin_cases r <;> cases v <;> simp [q, signedValue] <;> linarith
  have hsum : ∑ z, q z = 1 := by
    simp only [q, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
      Fintype.sum_bool, Fin.sum_univ_two]
    cases v <;> simp [signedValue] <;> ring
  change (pmfOfRealWeight q z).toReal = q z
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one q hq hsum,
    ENNReal.toReal_ofReal (hq z)]

-- @node: parametricPair_obsPMF_eq_pi
/-- The entire finite observed law is the i.i.d. product of its one-epoch law. [the stated conclusion](goal). -/
lemma parametricPair_obsPMF_eq_pi (T : Nat) (v : Bool) :
    (parametricPairFinite T v).obsPMF.toMeasure =
      Measure.pi (fun _ : Fin T ↦ (parametricEpochPMF T v).toMeasure) := by
  apply Measure.ext_of_singleton
  intro w
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w), Measure.pi_singleton]
  have htop : (∏ i : Fin T, (parametricEpochPMF T v).toMeasure {w i}) ≠ ∞ := by
    apply ENNReal.prod_ne_top
    intro i hi
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact PMF.apply_ne_top _ _
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) htop]
  rw [parametricPair_obsPMF_toReal]
  rw [ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp_rw [parametricEpochPMF_toReal]

-- @node: parametricEpochEquiv
/-- Reorder a reward bit and action bit into the paper's observed triple. -/
def parametricEpochEquiv : Bool × Bool ≃ Fin 1 × Bool × Fin 2 where
  toFun z := (0, z.2, finTwoEquiv.symm z.1)
  invFun z := (finTwoEquiv z.2.2, z.2.1)
  left_inv z := by cases z with | mk r a => cases r <;> rfl
  right_inv z := by
    rcases z with ⟨x, a, r⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply Prod.ext
      · rfl
      · exact finTwoEquiv.symm_apply_apply r

-- @node: parametricEpochSource
/-- The equivalent product presentation: a reward Bernoulli followed by a fair action. -/
noncomputable def parametricEpochSource (T : Nat) (v : Bool) : Measure (Bool × Bool) :=
  (Causalean.Mathlib.Probability.bernoulliBool
      ((1 + signedValue v * parametricAmplitude T) / 2)).prod
    (Causalean.Mathlib.Probability.bernoulliBool (1 / 2))

-- @node: parametricEpochPMF_eq_map_source
/-- Reordering the product presentation gives the one-epoch observed PMF. [the stated conclusion](goal). -/
lemma parametricEpochPMF_eq_map_source (T : Nat) (v : Bool) :
    (parametricEpochPMF T v).toMeasure =
      Measure.map
        ({ toEquiv := parametricEpochEquiv
           measurable_toFun := measurable_of_finite _
           measurable_invFun := measurable_of_finite _ } :
          (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2))
        (parametricEpochSource T v) := by
  let e : (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2) :=
    { toEquiv := parametricEpochEquiv
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
  have hplus : 0 ≤ (1 + parametricAmplitude T) / 2 := by linarith
  have hminus : 0 ≤ (1 - parametricAmplitude T) / 2 := by linarith
  have hcompPlus : 0 ≤ 1 - (1 + parametricAmplitude T) / 2 := by linarith
  have hcompMinus : 0 ≤ 1 - (1 - parametricAmplitude T) / 2 := by linarith
  have hlinPlus : 0 ≤ 1 / 2 + parametricAmplitude T * (1 / 2) := by linarith
  have hlinMinus : 0 ≤ 1 / 2 + parametricAmplitude T * (-1 / 2) := by linarith
  letI : IsFiniteMeasure (Causalean.Mathlib.Probability.bernoulliBool
      ((1 + signedValue v * parametricAmplitude T) / 2)) := by
    constructor
    simp [Causalean.Mathlib.Probability.bernoulliBool]
  letI : IsFiniteMeasure (Causalean.Mathlib.Probability.bernoulliBool (1 / 2)) := by
    constructor
    simp [Causalean.Mathlib.Probability.bernoulliBool]
  apply Measure.ext_of_singleton
  intro z
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z),
    Measure.map_apply e.measurable (measurableSet_singleton z)]
  have hpre : e ⁻¹' {z} = {e.symm z} := by
    ext q
    exact e.toEquiv.apply_eq_iff_eq_symm_apply
  rw [hpre]
  rw [show ({e.symm z} : Set (Bool × Bool)) =
      { (e.symm z).1 } ×ˢ { (e.symm z).2 } by simp,
    parametricEpochSource, Measure.prod_prod]
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  rw [parametricEpochPMF_toReal, ENNReal.toReal_mul]
  rcases z with ⟨x, a, r⟩
  fin_cases x
  cases a <;> fin_cases r <;> cases v <;>
    simp [e, parametricEpochEquiv, Causalean.Mathlib.Probability.bernoulliBool,
      finTwoEquiv, signedValue]
  all_goals
    repeat' rw [ENNReal.toReal_ofReal (by linarith)]
    ring

-- @node: parametricEpoch_klDiv_le
/-- A single epoch of the parametric pair has KL at most four times the squared amplitude. [the stated conclusion](goal). -/
lemma parametricEpoch_klDiv_le (T : Nat) :
    InformationTheory.klDiv (parametricEpochPMF T false).toMeasure
        (parametricEpochPMF T true).toMeasure ≤
      ENNReal.ofReal (4 * parametricAmplitude T ^ 2) := by
  let e : (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2) :=
    { toEquiv := parametricEpochEquiv
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
  have hp0 : 0 ≤ (1 - parametricAmplitude T) / 2 := by linarith
  have hp1 : (1 - parametricAmplitude T) / 2 ≤ 1 := by linarith
  have hq0 : 0 ≤ (1 + parametricAmplitude T) / 2 := by linarith
  have hq1 : (1 + parametricAmplitude T) / 2 ≤ 1 := by linarith
  let P := Causalean.Mathlib.Probability.bernoulliBool
    ((1 - parametricAmplitude T) / 2)
  let Q := Causalean.Mathlib.Probability.bernoulliBool
    ((1 + parametricAmplitude T) / 2)
  let R := Causalean.Mathlib.Probability.bernoulliBool (1 / 2)
  letI : IsProbabilityMeasure P :=
    Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hp0 hp1
  letI : IsProbabilityMeasure Q :=
    Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hq0 hq1
  letI : IsProbabilityMeasure R :=
    Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)
  have hprod : InformationTheory.klDiv (P.prod R) (Q.prod R) =
      InformationTheory.klDiv P Q := by
    rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_left
      P Q (Kernel.const Bool R)
  let f : ℝ → Bool := fun x ↦ decide (x = 1)
  have hf : Measurable f := by
    apply measurable_to_countable'
    intro b
    cases b
    · have h := (measurableSet_singleton (1 : ℝ)).compl
      convert h using 1 <;> ext x <;> simp [f]
    · have h := measurableSet_singleton (1 : ℝ)
      convert h using 1 <;> ext x <;> simp [f]
  have hmap (p : ℝ) : Measure.map f
      (Causalean.Mathlib.Probability.bernoulliLaw p) =
      Causalean.Mathlib.Probability.bernoulliBool p := by
    rw [Causalean.Mathlib.Probability.bernoulliLaw,
      Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' hf, Measure.map_dirac' hf]
    simp [f, Causalean.Mathlib.Probability.bernoulliBool]
  have hbern := Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
    (p := (1 - parametricAmplitude T) / 2)
    (q := (1 + parametricAmplitude T) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.bernoulliLaw
      ((1 - parametricAmplitude T) / 2)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0 hp1
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.bernoulliLaw
      ((1 + parametricAmplitude T) / 2)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hq0 hq1
  have hbool : InformationTheory.klDiv P Q ≤
      ENNReal.ofReal (4 * parametricAmplitude T ^ 2) := by
    calc
      InformationTheory.klDiv P Q =
          InformationTheory.klDiv
            (Measure.map f (Causalean.Mathlib.Probability.bernoulliLaw
              ((1 - parametricAmplitude T) / 2)))
            (Measure.map f (Causalean.Mathlib.Probability.bernoulliLaw
              ((1 + parametricAmplitude T) / 2))) := by rw [hmap, hmap]
      _ ≤ InformationTheory.klDiv
            (Causalean.Mathlib.Probability.bernoulliLaw
              ((1 - parametricAmplitude T) / 2))
            (Causalean.Mathlib.Probability.bernoulliLaw
              ((1 + parametricAmplitude T) / 2)) :=
        InformationTheory.klDiv_map_le _ _ hf
      _ ≤ ENNReal.ofReal (4 * (((1 - parametricAmplitude T) / 2) -
            ((1 + parametricAmplitude T) / 2)) ^ 2) := hbern
      _ = ENNReal.ofReal (4 * parametricAmplitude T ^ 2) := by congr 1 <;> ring
  letI : IsFiniteMeasure (parametricEpochSource T false) := by
    rw [parametricEpochSource]
    simp only [signedValue]
    convert (inferInstance : IsFiniteMeasure (P.prod R)) using 1 <;> simp [P, R] <;> ring
  letI : IsFiniteMeasure (parametricEpochSource T true) := by
    simpa [parametricEpochSource, Q, R, signedValue] using
      (inferInstance : IsFiniteMeasure (Q.prod R))
  rw [parametricEpochPMF_eq_map_source T false,
    parametricEpochPMF_eq_map_source T true,
    Causalean.Mathlib.Probability.klDiv_map_measurableEquiv]
  simp only [parametricEpochSource, signedValue]
  convert hprod.trans_le hbool using 1 <;> simp [P, Q, R] <;> ring

-- @node: parametricEpoch_fullSupport
/-- Each one-epoch parametric law gives positive mass to all four action-reward cells. [the stated conclusion](goal). -/
lemma parametricEpoch_fullSupport (T : Nat) (v : Bool) :
    FullSupportPMF (parametricEpochPMF T v) := by
  intro z
  have hreal : 0 < (parametricEpochPMF T v z).toReal := by
    rw [parametricEpochPMF_toReal]
    rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
    rcases z with ⟨x, a, r⟩
    fin_cases r <;> cases v <;> simp [signedValue] <;> nlinarith
  exact (ENNReal.toReal_pos_iff.mp hreal).1

-- @node: parametricPair_finiteObs_klDiv_le
/-- Tensorization gives the fixed `1/4` KL budget for the finite observed trajectory. [the h T condition](hyp:hT). [the stated conclusion](goal). -/
lemma parametricPair_finiteObs_klDiv_le (T : Nat) (hT : 1 ≤ T) :
    InformationTheory.klDiv (parametricPairFinite T false).obsPMF.toMeasure
        (parametricPairFinite T true).obsPMF.toMeasure ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let μ := (parametricEpochPMF T false).toMeasure
  let ν := (parametricEpochPMF T true).toMeasure
  letI : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure _
  letI : IsProbabilityMeasure ν := PMF.toMeasure.isProbabilityMeasure _
  have hac : μ ≪ ν := absolutelyContinuous_of_fullSupport
    (parametricEpoch_fullSupport T false) (parametricEpoch_fullSupport T true)
  have hint : Integrable (llr μ ν) μ := Integrable.of_finite
  have htensor := Causalean.Mathlib.InformationTheory.productKL_tensorization T μ ν hac hint
  have hepoch := parametricEpoch_klDiv_le T
  have hepochReal : (InformationTheory.klDiv μ ν).toReal ≤
      4 * parametricAmplitude T ^ 2 := by
    calc
      (InformationTheory.klDiv μ ν).toReal ≤
          (ENNReal.ofReal (4 * parametricAmplitude T ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hepoch
      _ = 4 * parametricAmplitude T ^ 2 := ENNReal.toReal_ofReal (by positivity)
  have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hsqrt_sq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
  have hampEq : (T : ℝ) * (4 * parametricAmplitude T ^ 2) = 1 / 4 := by
    unfold parametricAmplitude
    field_simp [ne_of_gt hsqrt_pos]
    nlinarith
  rw [parametricPair_obsPMF_eq_pi, parametricPair_obsPMF_eq_pi]
  apply (ENNReal.toReal_le_toReal htensor.product_ne_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  calc
    (InformationTheory.klDiv (Measure.pi fun _ : Fin T ↦ μ)
        (Measure.pi fun _ : Fin T ↦ ν)).toReal ≤
        (T : ℝ) * (InformationTheory.klDiv μ ν).toReal := htensor.apply
    _ ≤ (T : ℝ) * (4 * parametricAmplitude T ^ 2) :=
      mul_le_mul_of_nonneg_left hepochReal (by positivity)
    _ = 1 / 4 := hampEq

-- @node: parametricPair_observed_klDiv_le
/-- Decoding the finite rewards preserves the required direction of the KL budget. [the h T condition](hyp:hT). [the stated conclusion](goal). -/
lemma parametricPair_observed_klDiv_le (T : Nat) (hT : 1 ≤ T) :
    InformationTheory.klDiv (obsLaw (embed (parametricPairFinite T false)))
        (obsLaw (embed (parametricPairFinite T true))) ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
  (embed_klDiv_le (F := parametricPairFinite T false)
    (G := parametricPairFinite T true) rfl).trans (parametricPair_finiteObs_klDiv_le T hT)

-- @node: parametricPair_kernelMean
/-- Every state-action cell of the parametric witness has reward mean `v*eta_T`. [the stated conclusion](goal). -/
lemma parametricPair_kernelMean {T : Nat} (v : Bool) (s : JointState 1 1) (a : Bool) :
    ∑ p : Fin 2 × JointState 1 1,
      ((parametricPairFinite T v).kernel s a p).toReal *
        (parametricPairFinite T v).rew p.1 = signedValue v * parametricAmplitude T := by
  have hamp := parametricAmplitude_mem T
  rcases hamp with ⟨hamp0, hamp1⟩
  let w : Fin 2 × JointState 1 1 → ℝ := fun p ↦
    (1 + (if p.1 = 0 then -1 else 1) * signedValue v * parametricAmplitude T) / 2
  have hw : ∀ p, 0 ≤ w p := by
    intro p
    cases p with
    | mk r s' =>
      fin_cases r <;> cases v <;> simp [w, signedValue] <;> linarith
  have hsum : ∑ p, w p = 1 := by
    simp only [w, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
      Fin.sum_univ_two]
    cases v <;> simp [signedValue] <;> ring
  simp only [parametricPairFinite]
  change ∑ p, (pmfOfRealWeight w p).toReal * (if p.1 = 0 then -1 else 1) = _
  simp_rw [pmfOfRealWeight_apply_of_nonneg_sum_one w hw hsum,
    ENNReal.toReal_ofReal (hw _)]
  simp only [w, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
    Fin.sum_univ_two]
  cases v <;> simp [signedValue] <;> ring

-- @node: parametricPair_targetValue
/-- The two singleton-state alternatives have target values `-eta_T` and `eta_T`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma parametricPair_targetValue {T : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (v : Bool) :
    targetValue (embed (parametricPairFinite T v)) =
      signedValue v * parametricAmplitude T := by
  let F := parametricPairFinite T v
  have hprob : ProbabilityVector (stationaryLaw (finitePolicyKernel F F.e)) := by
    rw [← embed_stationaryLaw_eq F F.e]
    exact (parametricPair_mem T t0 zeta C v ht0 hzeta hC).target_stationary_law.1
  rw [embed_targetValue_eq]
  unfold finiteTargetValue
  simp_rw [parametricPair_kernelMean]
  have he (s : JointState 1 1) :
      ∑ a : Bool, ((parametricPairFinite T v).e s.1 a).toReal = 1 :=
    sum_pmf_toReal_eq_one ((parametricPairFinite T v).e s.1)
  simp_rw [← Finset.sum_mul, he, one_mul]
  rw [← Finset.sum_mul, hprob.2, one_mul]

/-- The singleton-state equal-policy experiment gives the explicit `exp(-1/4)/(64T)`
floor uniformly over every latent-overlap radius, together with internal fixed-witness
membership and sSup-free pointwise certificates used by downstream proofs. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma uniform_parametric_floor_certificates {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∀ T : Nat,
      (∀ (C : ℝ), 1 ≤ C →
        LatentOverlapClass t0 zeta C (embed (parametricPairFinite T false)) ∧
        LatentOverlapClass t0 zeta C (embed (parametricPairFinite T true))) ∧
      (∀ (C : ℝ), 1 ≤ C →
        Real.exp (-(1 / 4 : ℝ)) / (64 * T) ≤ minimaxRisk T t0 zeta C) ∧
      ∀ est : RawEstimator T,
        (∀ nX b e, Measurable (est nX b e)) →
        Integrable (fun w ↦
          (est 1 (embed (parametricPairFinite T false)).b
              (embed (parametricPairFinite T false)).e w -
            targetValue (embed (parametricPairFinite T false))) ^ 2)
          (obsLaw (embed (parametricPairFinite T false))) →
        Integrable (fun w ↦
          (est 1 (embed (parametricPairFinite T true)).b
              (embed (parametricPairFinite T true)).e w -
            targetValue (embed (parametricPairFinite T true))) ^ 2)
          (obsLaw (embed (parametricPairFinite T true))) →
        Real.exp (-(1 / 4 : ℝ)) / (64 * T) ≤
          max (rawExperimentRisk est (embed (parametricPairFinite T false)))
            (rawExperimentRisk est (embed (parametricPairFinite T true))) := by
  intro T
  by_cases hT0 : T = 0
  · subst T
    constructor
    · intro C hC
      exact ⟨parametricPair_mem 0 t0 zeta C false ht0 hzeta hC,
        parametricPair_mem 0 t0 zeta C true ht0 hzeta hC⟩
    constructor
    · intro C hC
      simp
      exact Causalean.Stat.minimaxValue_nonneg fun est m ↦ observedRisk_nonneg est m
    · intro est hmeas hint0 hint1
      simp
      left
      unfold rawExperimentRisk Causalean.Stat.sqRisk
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun w ↦ sq_nonneg _)
  · have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
    have hclass : ∀ (C : ℝ), 1 ≤ C →
        LatentOverlapClass t0 zeta C (embed (parametricPairFinite T false)) ∧
        LatentOverlapClass t0 zeta C (embed (parametricPairFinite T true)) := by
      intro C hC
      exact ⟨(parametricModel T t0 zeta C false hT ht0 hzeta hC).mem,
        (parametricModel T t0 zeta C true hT ht0 hzeta hC).mem⟩
    refine ⟨hclass, ?_, ?_⟩
    · intro C hC
      let M0 := parametricModel T t0 zeta C false hT ht0 hzeta hC
      let M1 := parametricModel T t0 zeta C true hT ht0 hzeta hC
      have hKL := parametricPair_observed_klDiv_le T hT
      have hac : obsLaw (embed (parametricPairFinite T false)) ≪
          obsLaw (embed (parametricPairFinite T true)) :=
        embed_absolutelyContinuous
          (absolutelyContinuous_of_fullSupport parametricPair_fullSupportObs
            parametricPair_fullSupportObs) rfl
      have hfin : InformationTheory.klDiv
          (obsLaw (embed (parametricPairFinite T false)))
          (obsLaw (embed (parametricPairFinite T true))) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
      have hsep : 2 * parametricAmplitude T ≤
          |targetValue (embed (parametricPairFinite T false)) -
            targetValue (embed (parametricPairFinite T true))| := by
        rw [parametricPair_targetValue ht0 hzeta hC,
          parametricPair_targetValue ht0 hzeta hC]
        rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
        simp [signedValue]
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hb : HEq M0.raw.b M1.raw.b := by
        simp [M0, M1, parametricModel, parametricPairFinite, embed]
      have he : HEq M0.raw.e M1.raw.e := by
        simp [M0, M1, parametricModel, parametricPairFinite, embed]
      have hfloor := (two_point_floor_explicit M0 M1 rfl hb he hT
        (parametricAmplitude_mem T).1 (by norm_num) hKL hac hfin hsep).2
      have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
      have hsqrt_sq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
      have heq : parametricAmplitude T ^ 2 * Real.exp (-(1 / 4 : ℝ)) / 4 =
          Real.exp (-(1 / 4 : ℝ)) / (64 * T) := by
        unfold parametricAmplitude
        field_simp [ne_of_gt hsqrt_pos]
        nlinarith
      rwa [heq] at hfloor
    · intro est hmeas hint0 hint1
      have hC1 : (1 : ℝ) ≤ 1 := le_rfl
      let M0 := parametricModel T t0 zeta 1 false hT ht0 hzeta hC1
      let M1 := parametricModel T t0 zeta 1 true hT ht0 hzeta hC1
      have hKL := parametricPair_observed_klDiv_le T hT
      have hac : obsLaw (embed (parametricPairFinite T false)) ≪
          obsLaw (embed (parametricPairFinite T true)) :=
        embed_absolutelyContinuous
          (absolutelyContinuous_of_fullSupport parametricPair_fullSupportObs
            parametricPair_fullSupportObs) rfl
      have hfin : InformationTheory.klDiv
          (obsLaw (embed (parametricPairFinite T false)))
          (obsLaw (embed (parametricPairFinite T true))) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
      have hsep : 2 * parametricAmplitude T ≤
          |targetValue (embed (parametricPairFinite T false)) -
            targetValue (embed (parametricPairFinite T true))| := by
        rw [parametricPair_targetValue ht0 hzeta hC1,
          parametricPair_targetValue ht0 hzeta hC1]
        rcases parametricAmplitude_mem T with ⟨hamp0, hamp1⟩
        simp [signedValue]
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hb : HEq M0.raw.b M1.raw.b := by
        simp [M0, M1, parametricModel, parametricPairFinite, embed]
      have he : HEq M0.raw.e M1.raw.e := by
        simp [M0, M1, parametricModel, parametricPairFinite, embed]
      have hpoint := (two_point_floor_explicit M0 M1 rfl hb he hT
        (parametricAmplitude_mem T).1 (by norm_num) hKL hac hfin hsep).1 est hmeas hint0 hint1
      have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
      have heq : parametricAmplitude T ^ 2 * Real.exp (-(1 / 4 : ℝ)) / 4 =
          Real.exp (-(1 / 4 : ℝ)) / (64 * T) := by
        have hsqrt_sq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
        unfold parametricAmplitude
        field_simp [ne_of_gt hsqrt_pos]
        nlinarith
      rw [heq] at hpoint
      change Real.exp (-(1 / 4 : ℝ)) / (64 * T) ≤
        max (rawExperimentRisk est (embed (parametricPairFinite T false)))
          (rawExperimentRisk est (embed (parametricPairFinite T true))) at hpoint
      exact hpoint

-- @node: lem:uniform-parametric-floor
/-- The uniform parametric minimax floor, together with the common singleton-state,
equal-policy subexperiment on which the same floor already holds pointwise. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma uniform_parametric_floor {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∀ T : Nat, 1 ≤ T → ∀ C : ℝ, 1 ≤ C →
      (Real.exp (-(1 / 4 : ℝ)) / (64 * T) ≤ minimaxRisk T t0 zeta C) ∧
      LatentOverlapClass t0 zeta C (embed (parametricPairFinite T false)) ∧
      LatentOverlapClass t0 zeta C (embed (parametricPairFinite T true)) ∧
      (embed (parametricPairFinite T false)).b =
        (embed (parametricPairFinite T false)).e ∧
      (embed (parametricPairFinite T true)).b =
        (embed (parametricPairFinite T true)).e ∧
      (embed (parametricPairFinite T false)).b =
        (embed (parametricPairFinite T true)).b ∧
      (embed (parametricPairFinite T false)).e =
        (embed (parametricPairFinite T true)).e ∧
      ∀ est : RawEstimator T,
        (∀ nX b e, Measurable (est nX b e)) →
        Integrable (fun w ↦
          (est 1 (embed (parametricPairFinite T false)).b
              (embed (parametricPairFinite T false)).e w -
            targetValue (embed (parametricPairFinite T false))) ^ 2)
          (obsLaw (embed (parametricPairFinite T false))) →
        Integrable (fun w ↦
          (est 1 (embed (parametricPairFinite T true)).b
              (embed (parametricPairFinite T true)).e w -
            targetValue (embed (parametricPairFinite T true))) ^ 2)
          (obsLaw (embed (parametricPairFinite T true))) →
        Real.exp (-(1 / 4 : ℝ)) / (64 * T) ≤
          max (rawExperimentRisk est (embed (parametricPairFinite T false)))
            (rawExperimentRisk est (embed (parametricPairFinite T true))) := by
  intro T hT C hC
  have hcert := uniform_parametric_floor_certificates ht0 hzeta T
  refine ⟨hcert.2.1 C hC, (hcert.1 C hC).1, (hcert.1 C hC).2, ?_, ?_, ?_, ?_,
    hcert.2.2⟩
  all_goals simp [parametricPairFinite, embed]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
