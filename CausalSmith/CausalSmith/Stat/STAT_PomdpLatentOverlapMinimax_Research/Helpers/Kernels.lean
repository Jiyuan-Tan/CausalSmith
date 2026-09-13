import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Basic
import Causalean.Stat.Minimax.TotalVariation
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Contracting

set_option linter.style.longLine false

/-! # Kernel, stationary-law, support, and clipping lemmas -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The next-state marginal of a probabilistic reward-transition kernel sums to one. [the h K condition](hyp:hK). [the stated conclusion](goal). -/
lemma sum_kernel_nextState_eq_one {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (hK : PomdpKernelLaw M) (s : JointState nX nH) (a : Bool) :
    ∑ s' : JointState nX nH, (M.K s a {q | q.2 = s'}).toReal = 1 := by
  letI : IsProbabilityMeasure (M.K s a) := hK.1 s a
  have hsum : ∑ s' : JointState nX nH, M.K s a {q | q.2 = s'} = 1 := by
    have hpre : ∑ s' : JointState nX nH, M.K s a (Prod.snd ⁻¹' {s'}) =
        M.K s a (Prod.snd ⁻¹' (Set.univ : Set (JointState nX nH))) := by
      simpa using
        (MeasureTheory.sum_measure_preimage_singleton
          (s := Finset.univ) (f := Prod.snd) (μ := M.K s a)
          (fun y _ ↦ (measurableSet_singleton (x := y)).preimage measurable_snd))
    change ∑ s' : JointState nX nH, M.K s a (Prod.snd ⁻¹' {s'}) = 1
    simpa using hpre
  rw [← ENNReal.toReal_sum]
  · rw [hsum]
    simp
  · intro s' _
    exact measure_ne_top _ _

/-- A probability policy induces a stochastic finite joint-state kernel. [the h K condition](hyp:hK); and [the hp condition](hyp:hp). [the stated conclusion](goal). -/
lemma policyKernel_probabilityVector {T nX nH : Nat} (M : RawPomdpExperiment T nX nH)
    (hK : PomdpKernelLaw M) (p : Policy nX) (hp : PolicyVector p) (s : JointState nX nH) :
    ProbabilityVector (policyKernel M p s) := by
  constructor
  · intro s'
    unfold policyKernel
    exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg ((hp s.1).1 a) ENNReal.toReal_nonneg
  · unfold policyKernel
    rw [Finset.sum_comm]
    calc
      ∑ a : Bool, ∑ s' : JointState nX nH,
          p s.1 a * (M.K s a {q | q.2 = s'}).toReal =
          ∑ a : Bool, p s.1 a * ∑ s' : JointState nX nH,
            (M.K s a {q | q.2 = s'}).toReal := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
      _ = ∑ a : Bool, p s.1 a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [sum_kernel_nextState_eq_one M hK s a, mul_one]
      _ = 1 := (hp s.1).2

/-- Finite real vectors equipped with their `L¹` norm. -/
abbrev L1Vec (S : Type*) [Fintype S] := PiLp 1 (fun _ : S ↦ ℝ)

/-- The probability simplex inside the finite `L¹` vector space. -/
def probabilityL1Set (S : Type*) [Fintype S] : Set (L1Vec S) :=
  {x | ProbabilityVector (WithLp.ofLp x)}

/-- The row-kernel action transported to the finite `L¹` vector space. -/
noncomputable def applyKernelL1 {S : Type*} [Fintype S]
    (P : S → S → ℝ) (x : L1Vec S) : L1Vec S :=
  WithLp.toLp 1 (applyKernel (WithLp.ofLp x) P)

/-- The finite `L¹` norm is the sum of coordinate absolute values. [the stated conclusion](goal). -/
lemma norm_L1Vec_eq_sum {S : Type*} [Fintype S] (x : L1Vec S) :
    ‖x‖ = ∑ s, |x s| := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  simp

/-- The finite probability simplex is complete in the `L¹` metric. [the stated conclusion](goal). -/
lemma probabilityL1Set_isComplete {S : Type*} [Fintype S] :
    IsComplete (probabilityL1Set S) := by
  apply IsClosed.isComplete
  change IsClosed ((fun x : L1Vec S ↦ WithLp.ofLp x) ⁻¹' stdSimplex ℝ S)
  exact (isClosed_stdSimplex ℝ S).preimage
    (PiLp.continuous_ofLp 1 (fun _ : S ↦ ℝ))

/-- A stochastic row kernel maps the finite probability simplex into itself. [the h P condition](hyp:hP). [the stated conclusion](goal). -/
lemma applyKernelL1_mapsTo {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : ∀ s, ProbabilityVector (P s)) :
    Set.MapsTo (applyKernelL1 P) (probabilityL1Set S) (probabilityL1Set S) := by
  intro x hx
  change ProbabilityVector (applyKernel (WithLp.ofLp x) P)
  rcases hx with ⟨hxnonneg, hxsum⟩
  constructor
  · intro s'
    exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (hxnonneg s) ((hP s).1 s')
  · unfold applyKernel
    rw [Finset.sum_comm]
    calc
      ∑ s, ∑ s', WithLp.ofLp x s * P s s' =
          ∑ s, WithLp.ofLp x s * ∑ s', P s s' := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = ∑ s, WithLp.ofLp x s := by simp_rw [(hP _).2, mul_one]
      _ = 1 := hxsum

/-- A strict total-variation contraction on a finite stochastic kernel has a stationary law. [the h P condition](hyp:hP); and [the hp0 condition](hyp:hp0); and [the halpha0 condition](hyp:halpha0); and [the halpha1 condition](hyp:halpha1); and [the hcontract condition](hyp:hcontract). [the stated conclusion](goal). -/
lemma exists_stationary_of_contraction {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : ∀ s, ProbabilityVector (P s))
    (p0 : S → ℝ) (hp0 : ProbabilityVector p0)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hcontract : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ alpha * tvNorm (p - q)) :
    ∃ d, IsStationary P d := by
  let K : ℝ≥0 := ⟨alpha, halpha0⟩
  let s := probabilityL1Set S
  let f := applyKernelL1 P
  have hsf : Set.MapsTo f s s := applyKernelL1_mapsTo P hP
  have hf : ContractingWith K (hsf.restrict f s s) := by
    constructor
    · exact_mod_cast halpha1
    · rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      change dist (applyKernelL1 P x.1) (applyKernelL1 P y.1) ≤
        (K : ℝ) * dist x.1 y.1
      simp only [dist_eq_norm, ← WithLp.toLp_sub, applyKernelL1, norm_L1Vec_eq_sum]
      have hc := hcontract (WithLp.ofLp x.1) (WithLp.ofLp y.1) x.2 y.2
      unfold tvNorm at hc
      simp only [Pi.sub_apply] at hc ⊢
      change (∑ i, |applyKernel (WithLp.ofLp x.1) P i -
          applyKernel (WithLp.ofLp y.1) P i|) ≤
        alpha * ∑ i, |WithLp.ofLp x.1 i - WithLp.ofLp y.1 i|
      nlinarith [hc]
  have hx : WithLp.toLp 1 p0 ∈ s := hp0
  obtain ⟨d, hdmem, hdfix, -⟩ :=
    hf.exists_fixedPoint' (probabilityL1Set_isComplete (S := S)) hsf hx (edist_ne_top _ _)
  refine ⟨WithLp.ofLp d, hdmem, ?_⟩
  intro s'
  have heq : applyKernel (WithLp.ofLp d) P = WithLp.ofLp d := by
    exact congrArg WithLp.ofLp hdfix
  exact congrFun heq s'

/-- The target stationary law follows from stochasticity and the class's strict contraction. [the h M condition](hyp:hM). [the stated conclusion](goal). -/
lemma LatentOverlapClass.target_stationary_law {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M) :
    IsStationary (policyKernel M M.e) (stationaryLaw (policyKernel M M.e)) := by
  apply stationaryLaw_isStationary_of_exists
  apply exists_stationary_of_contraction
    (P := policyKernel M M.e)
    (p0 := stationaryLaw (policyKernel M M.b))
    (alpha := mixingAlpha t0)
  · exact policyKernel_probabilityVector M hM.pomdp_kernel M.e hM.policy_overlap.1
  · exact hM.behavior_stationary_law.1
  · exact Real.exp_nonneg _
  · rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  · exact hM.uniform_contraction M.e (Or.inr rfl)

/-- A stochastic finite matrix is nonexpansive in the half-`ℓ1` norm. [the h P condition](hyp:hP). [the stated conclusion](goal). -/
lemma tvNorm_applyKernel_le {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : ∀ s, ProbabilityVector (P s)) (v : S → ℝ) :
    tvNorm (applyKernel v P) ≤ tvNorm v := by
  unfold tvNorm applyKernel
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ∑ s', |∑ s, v s * P s s'| ≤ ∑ s', ∑ s, |v s * P s s'| := by
      exact Finset.sum_le_sum fun s' _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |v s| * ∑ s', P s s' := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      rw [abs_mul, abs_of_nonneg ((hP s).1 s')]
    _ = ∑ s, |v s| := by
      simp_rw [(hP _).2, mul_one]

/-- A common refresh component contracts total variation by the residual weight. [the halpha condition](hyp:halpha); and [the h R condition](hyp:hR). [the stated conclusion](goal). -/
lemma tvNorm_contraction_of_refresh {S : Type*} [Fintype S]
    (alpha : ℝ) (halpha : 0 ≤ alpha) (nu : S → ℝ) (R : S → S → ℝ)
    (hR : ∀ s, ProbabilityVector (R s)) :
    ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p (fun s s' ↦ (1 - alpha) * nu s' + alpha * R s s') -
        applyKernel q (fun s s' ↦ (1 - alpha) * nu s' + alpha * R s s')) ≤
      alpha * tvNorm (p - q) := by
  intro p q hp hq
  have hdiff :
      applyKernel p (fun s s' ↦ (1 - alpha) * nu s' + alpha * R s s') -
          applyKernel q (fun s s' ↦ (1 - alpha) * nu s' + alpha * R s s') =
        fun s' ↦ alpha * (applyKernel p R s' - applyKernel q R s') := by
    funext s'
    simp only [Pi.sub_apply, applyKernel, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hp.2, hq.2]
    have hpalpha : ∑ x, p x * (alpha * R x s') =
        alpha * ∑ x, p x * R x s' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    have hqalpha : ∑ x, q x * (alpha * R x s') =
        alpha * ∑ x, q x * R x s' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hpalpha, hqalpha]
    ring
  rw [hdiff]
  calc
    tvNorm (fun s' ↦ alpha * (applyKernel p R s' - applyKernel q R s')) =
        alpha * tvNorm (applyKernel p R - applyKernel q R) := by
      unfold tvNorm
      simp_rw [abs_mul, abs_of_nonneg halpha, ← Finset.mul_sum, Pi.sub_apply]
      ring
    _ = alpha * tvNorm (applyKernel (p - q) R) := by
      congr 1
      congr 1
      funext s'
      simp [applyKernel, Finset.sum_sub_distrib, sub_mul]
    _ ≤ alpha * tvNorm (p - q) :=
      mul_le_mul_of_nonneg_left (tvNorm_applyKernel_le R hR (p - q)) halpha

/-- Uniform contraction makes stationary probability vectors unique. [the halpha condition](hyp:halpha); and [the hcontract condition](hyp:hcontract); and [the hp condition](hyp:hp); and [the hq condition](hyp:hq). [the stated conclusion](goal). -/
lemma stationary_unique_of_contraction {S : Type*} [Fintype S]
    (P : S → S → ℝ) (alpha : ℝ) (halpha : alpha < 1)
    (hcontract : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ alpha * tvNorm (p - q))
    {p q : S → ℝ} (hp : IsStationary P p) (hq : IsStationary P q) : p = q := by
  have happ_p : applyKernel p P = p := by
    funext s
    exact hp.2 s
  have happ_q : applyKernel q P = q := by
    funext s
    exact hq.2 s
  have hc := hcontract p q hp.1 hq.1
  rw [happ_p, happ_q] at hc
  have htv_nonneg : 0 ≤ tvNorm (p - q) := by
    unfold tvNorm
    positivity
  have htv_zero : tvNorm (p - q) = 0 := by nlinarith
  have hsum : ∑ s, |p s - q s| = 0 := by
    unfold tvNorm at htv_zero
    norm_num at htv_zero
    simpa [Pi.sub_apply] using htv_zero
  funext s
  have habs : |p s - q s| = 0 := by
    apply le_antisymm
    · calc
        |p s - q s| ≤ ∑ i, |p i - q i| := by
          exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (p i - q i)) (Finset.mem_univ s)
        _ = 0 := hsum
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- The bounded-reward class predicate is the almost-sure bound at each observed epoch. [the h Y condition](hyp:hY). [the stated conclusion](goal). -/
lemma boundedReward_law_ae {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hY : BoundedReward M) (t : Fin T) :
    ∀ᵐ tau ∂M.law, |rewardAt t tau| ≤ 1 := by
  have hs : MeasurableSet {tau : FullTrajectory T nX nH | |rewardAt t tau| ≤ 1} := by
    apply measurableSet_le
    · exact continuous_abs.measurable.comp
        (measurable_snd.comp (measurable_pi_apply t |>.comp measurable_snd))
    · exact measurable_const
  rw [ae_iff]
  change M.law ({tau : FullTrajectory T nX nH | |rewardAt t tau| ≤ 1}ᶜ) = 0
  rw [measure_compl hs (measure_ne_top _ _), measure_univ, hY t]
  simp

/-- Under the seven model-class restrictions and a positive horizon, the stationary target value
lies in `[-1,1]`. -/
private lemma targetValue_mem_unit_of_class {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hT : 1 ≤ T)
    (hM : LatentOverlapClass t0 zeta C M) :
    targetValue M ∈ Set.Icc (-1 : ℝ) 1 := by
  let t : Fin T := ⟨0, hT⟩
  let J : StateHistoryView T nX nH t × Bool → ℝ :=
    fun z ↦ ∫ y, y.1 ∂(M.K z.1.2 z.2)
  have hJb : ∀ᵐ z ∂(M.law.map (histActionPair t)), |J z| ≤ 1 := by
    letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa ↦ hM.pomdp_kernel.1 sa.1 sa.2⟩
    have hs : MeasurableSet
        {z : ActionHistoryView T nX nH t × Step nX nH | |z.2.1| ≤ 1} :=
      measurableSet_le (continuous_abs.measurable.comp
        (measurable_fst.comp measurable_snd)) measurable_const
    have hpair : ∀ᵐ z ∂(M.law.map (histNextPair t)), |z.2.1| ≤ 1 := by
      have hm : Measurable (@histNextPair T nX nH t) := by
        unfold histNextPair histView histActionPair histStateView curState actionAt rewardAt nextState
        measurability
      apply (MeasureTheory.ae_map_iff hm.aemeasurable hs).2
      exact boundedReward_law_ae hM.bounded_reward t
    rw [hM.pomdp_kernel.2 t] at hpair
    have hsections := MeasureTheory.Measure.ae_ae_of_ae_compProd hpair
    filter_upwards [hsections] with z hz
    letI : IsProbabilityMeasure (M.K z.1.2 z.2) := hM.pomdp_kernel.1 z.1.2 z.2
    change ∀ᵐ y ∂(M.K z.1.2 z.2), |y.1| ≤ 1 at hz
    have hz' : ∀ᵐ y ∂(M.K z.1.2 z.2), ‖y.1‖ ≤ (1 : ℝ) := by
      simpa only [Real.norm_eq_abs] using hz
    simpa only [J, Real.norm_eq_abs, mul_one, probReal_univ] using
      (norm_integral_le_of_norm_le_const (μ := M.K z.1.2 z.2)
        (f := fun y : Step nX nH ↦ y.1) (C := (1 : ℝ)) hz')
  have hrow (s : JointState nX nH) (a : Bool)
      (hs : 0 < stationaryLaw (policyKernel M M.b) s) (ha : 0 < M.b s.1 a) :
      |∫ y, y.1 ∂(M.K s a)| ≤ 1 := by
    let z : StateHistoryView T nX nH t × Bool :=
      ((((fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)), s), a)
    have hz_mass : 0 < (M.law.map (histActionPair t)) {z} := by
      letI : IsMarkovKernel (behaviourKernel M) := by
        constructor
        intro x
        constructor
        change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
        simp
        rw [← ENNReal.ofReal_add ((hM.sequential_ignorability.1 x).1 true)
          ((hM.sequential_ignorability.1 x).1 false)]
        rw [show M.b x true + M.b x false = 1 by
          simpa using (hM.sequential_ignorability.1 x).2]
        norm_num
      rw [hM.sequential_ignorability.2 t]
      rw [show {z} = {z.1} ×ˢ {a} by ext x; simp [z]]
      change 0 < (M.law.map (histStateView t)).compProd
        (Kernel.comap (behaviourKernel M) (currentObsState t) (measurable_currentObsState t))
        ({z.1} ×ˢ {a})
      rw [Measure.compProd_apply_prod (MeasurableSet.singleton _) (MeasurableSet.singleton _)]
      simp only [Measure.restrict_singleton]
      have hm : Measurable (@histStateView T nX nH t) := by
        unfold histStateView curState
        measurability
      rw [Measure.map_apply hm (MeasurableSet.singleton _)]
      have hpre : histStateView t ⁻¹' {z.1} =
          stateAt (T := T) (nX := nX) (nH := nH) 0 ⁻¹' {s} := by
        ext tau
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hz'
          simpa [histStateView, curState, stateAt, t, z] using congrArg Prod.snd hz'
        · intro hs'
          change (((fun j : Fin 0 ↦ curState (prefixIndex t j) tau,
            fun j : Fin 0 ↦ tau.2 (prefixIndex t j)), curState t tau)) =
              (((fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)), s)
          congr 2
          · exact Subsingleton.elim _ _
          · exact Subsingleton.elim _ _
      have hm0 : Measurable (stateAt (T := T) (nX := nX) (nH := nH) 0) := by
        unfold stateAt
        measurability
      rw [hpre, ← Measure.map_apply hm0 (MeasurableSet.singleton _),
        hM.stationary_start.2 s]
      have hba : 0 < (behaviourKernel M s.1) {a} := by
        change 0 < (∑ a' : Bool, ENNReal.ofReal (M.b s.1 a') • Measure.dirac a') {a}
        cases a <;> simp [ENNReal.ofReal_pos.mpr ha]
      simpa [currentObsState, z, ENNReal.ofReal_pos.mpr hs] using hba
    have hz : |J z| ≤ 1 := by
      by_contra hn
      have hzero : (M.law.map (histActionPair t)) {z} = 0 := by
        have hcompl := ae_iff.mp hJb
        apply le_antisymm
        · apply le_trans (measure_mono ?_) (le_of_eq hcompl)
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          exact hn
        · exact bot_le
      exact (ne_of_gt hz_mass) hzero
    simpa [J, z] using hz
  let dE := stationaryLaw (policyKernel M M.e)
  have hdE : ProbabilityVector dE := hM.target_stationary_law.1
  have hmean (s : JointState nX nH) (a : Bool) (hdepos : 0 < dE s)
      (hepos : 0 < M.e s.1 a) : |∫ y, y.1 ∂(M.K s a)| ≤ 1 := by
    have hbehavior : 0 < stationaryLaw (policyKernel M M.b) s := by
      have hedom := hM.latent_stationary_overlap.2 s
      by_contra hn
      have hi0 : stationaryLaw (policyKernel M M.b) s = 0 :=
        le_antisymm (le_of_not_gt hn) (hM.behavior_stationary_law.1.1 s)
      rw [hi0, mul_zero] at hedom
      exact (not_lt_of_ge hedom) hdepos
    have hbpos : 0 < M.b s.1 a := by
      have hover := hM.policy_overlap.2 s.1 a
      by_contra hn
      have hb0 : M.b s.1 a = 0 := le_antisymm (le_of_not_gt hn)
        ((hM.sequential_ignorability.1 s.1).1 a)
      rw [hb0, mul_zero] at hover
      exact (not_lt_of_ge hover) hepos
    exact hrow s a hbehavior hbpos
  have hregr (s : JointState nX nH) (hdepos : 0 < dE s) :
      |rewardRegression M s| ≤ 1 := by
    unfold rewardRegression
    calc
      |∑ a : Bool, M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| ≤
          ∑ a : Bool, |M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Bool, M.e s.1 a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul, abs_of_nonneg ((hM.policy_overlap.1 s.1).1 a)]
        by_cases hea : M.e s.1 a = 0
        · simp [hea]
        · exact mul_le_mul_of_nonneg_left (hmean s a hdepos
            (lt_of_le_of_ne ((hM.policy_overlap.1 s.1).1 a) (Ne.symm hea)))
            ((hM.policy_overlap.1 s.1).1 a)
      _ = 1 := by simpa using (hM.policy_overlap.1 s.1).2
  have habs : |targetValue M| ≤ 1 := by
    unfold targetValue
    calc
      |∑ s, dE s * rewardRegression M s| ≤
          ∑ s, |dE s * rewardRegression M s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s, dE s * |rewardRegression M s| := by
        apply Finset.sum_congr rfl
        intro s _
        rw [abs_mul, abs_of_nonneg (hdE.1 s)]
      _ ≤ ∑ s, dE s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : dE s = 0
        · simp [hs]
        · exact mul_le_mul_of_nonneg_left
            (hregr s (lt_of_le_of_ne (hdE.1 s) (Ne.symm hs))) (hdE.1 s)
      _ = 1 := by simpa using hdE.2
  exact abs_le.mp habs
  -- @realizes \(\theta(K,e)\)(range pinned to [-1,1] under the full model class)

/-- For [an indexed model](hyp:m), the stationary target value [lies in `[-1,1]`](goal). -/
lemma targetValue_mem_unit {T : Nat} {t0 zeta C : ℝ}
    (m : ModelIndex T t0 zeta C) :
    targetValue m.raw ∈ Set.Icc (-1 : ℝ) 1 :=
  targetValue_mem_unit_of_class m.horizon_pos m.mem

/-! PRIOR PROOF (carry-over: auto; now retained by `targetValue_mem_unit_of_class`). Stage 3: replace the
   placeholder above with this body, run `lean_diagnostic_messages`, patch failures only.
   := by  have hkernelMean (s : JointState nX nH) (a : Bool) :
      |∫ p, p.1 ∂(M.K s a)| ≤ 1 := by
    letI : IsProbabilityMeasure (M.K s a) := hM.pomdp_kernel.1 s a
    have hs : MeasurableSet {p : Step nX nH | |p.1| ≤ 1} := by
      apply measurableSet_le
      · exact continuous_abs.measurable.comp measurable_fst
      · exact measurable_const
    have hae : ∀ᵐ p ∂(M.K s a), |p.1| ≤ 1 := by
      rw [ae_iff]
      calc
        (M.K s a) {p | ¬|p.1| ≤ 1} =
            (M.K s a) ({p | |p.1| ≤ 1}ᶜ) := by congr 1
        _ = (M.K s a) Set.univ - (M.K s a) {p | |p.1| ≤ 1} :=
          measure_compl hs (measure_ne_top _ _)
        _ = 0 := by rw [measure_univ, hM.bounded_reward.1 s a]; simp
    have hae' : ∀ᵐ p ∂(M.K s a), ‖p.1‖ ≤ (1 : ℝ) := by
      simpa only [Real.norm_eq_abs] using hae
    calc
      |∫ p, p.1 ∂(M.K s a)| ≤ (1 : ℝ) * (M.K s a).real Set.univ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_of_norm_le_const (μ := M.K s a)
            (f := fun p : Step nX nH ↦ p.1) (C := (1 : ℝ)) hae')
      _ = 1 := by rw [probReal_univ]; norm_num
  have hregr (s : JointState nX nH) : |rewardRegression M s| ≤ 1 := by
    unfold rewardRegression
    calc
      |∑ a : Bool, M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| ≤
          ∑ a : Bool, |M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : Bool, M.e s.1 a * |∫ p, p.1 ∂(M.K s a)| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul, abs_of_nonneg ((hM.policy_overlap.1 s.1).1 a)]
      _ ≤ ∑ a : Bool, M.e s.1 a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hkernelMean s a)
          ((hM.policy_overlap.1 s.1).1 a)
      _ = 1 := by simpa using (hM.policy_overlap.1 s.1).2
  have hd := hM.target_stationary_law.1
  have habs : |targetValue M| ≤ 1 := by
    unfold targetValue
    calc
      |∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s| ≤
          ∑ s, |stationaryLaw (policyKernel M M.e) s * rewardRegression M s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s, stationaryLaw (policyKernel M M.e) s * |rewardRegression M s| := by
        apply Finset.sum_congr rfl
        intro s _
        rw [abs_mul, abs_of_nonneg (hd.1 s)]
      _ ≤ ∑ s, stationaryLaw (policyKernel M M.e) s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hregr s) (hd.1 s)
      _ = 1 := by simpa using hd.2
  exact abs_le.mp habs
  -- @realizes \(\theta(K,e)\)(range pinned to [-1,1] under the full model class)

-/
/-- Clipping to `[-1,1]` cannot increase squared distance to a target in that interval. [the htheta condition](hyp:htheta). [the stated conclusion](goal). -/
lemma clipUnit_sq_sub_le {u theta : ℝ} (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    (clipUnit u - theta) ^ 2 ≤ (u - theta) ^ 2 := by
  rcases htheta with ⟨htheta_lower, htheta_upper⟩
  by_cases hu_lower : u < -1
  · rw [clipUnit, min_eq_right (by linarith), max_eq_left (le_of_lt hu_lower)]
    nlinarith
  by_cases hu_upper : 1 < u
  · rw [clipUnit, min_eq_left (le_of_lt hu_upper), max_eq_right (by norm_num)]
    nlinarith
  rw [clipUnit, min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Risk is nonnegative on the admissible estimator carrier. [the stated conclusion](goal). -/
lemma observedRisk_nonneg {T : Nat} {t0 zeta C : ℝ}
    (est : ObservableEstimator T) (m : ModelIndex T t0 zeta C) :
    0 ≤ observedRisk est m := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

/-- Bounded estimators and bounded targets have [squared risk at most four](goal) at
[an indexed model](hyp:m). -/
lemma observedRisk_le_four {T : Nat} {t0 zeta C : ℝ}
    (est : ObservableEstimator T) (m : ModelIndex T t0 zeta C) :
    observedRisk est m ≤ 4 := by
  have hbound (w : ObsView T m.nX) :
      (est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw) ^ 2 ≤ 4 := by
    rcases est.2.1 m.nX m.raw.b m.raw.e w with ⟨he_lower, he_upper⟩
    rcases targetValue_mem_unit m with ⟨ht_lower, ht_upper⟩
    have hlo : 0 ≤ est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw + 2 := by linarith
    have hhi : 0 ≤ 2 - (est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw) := by linarith
    nlinarith [mul_nonneg hlo hhi]
  have hmeas : Measurable (fun w : ObsView T m.nX ↦
      (est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw) ^ 2) := by
    exact ((est.2.2 m.nX m.raw.b m.raw.e).sub measurable_const).pow_const 2
  have hobs : Measurable (@obsProj T m.nX m.nH) := by
    unfold obsProj curState actionAt rewardAt
    measurability
  letI : IsProbabilityMeasure (obsLaw m.raw) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hint : Integrable (fun w : ObsView T m.nX ↦
      (est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw) ^ 2) (obsLaw m.raw) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 4
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound w
  unfold observedRisk rawObservedRisk Causalean.Stat.sqRisk
  calc
    (∫ w, (est.1 m.nX m.raw.b m.raw.e w - targetValue m.raw) ^ 2 ∂obsLaw m.raw) ≤
        ∫ _w : ObsView T m.nX, (4 : ℝ) ∂obsLaw m.raw := by
      exact integral_mono hint (integrable_const 4) hbound
    _ = 4 := by simp

/-- For [an admissible estimator](hyp:est), its risk range [is bounded above](goal). -/
lemma bddAbove_range_observedRisk {T : Nat} {t0 zeta C : ℝ}
    (est : ObservableEstimator T) :
    BddAbove (Set.range (observedRisk (t0 := t0) (zeta := zeta) (C := C) est)) := by
  refine ⟨4, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact observedRisk_le_four est m

/-- Strict support of a finite PMF. -/
def FullSupportPMF {W : Type*} [Fintype W] (p : PMF W) : Prop := ∀ w, 0 < p w

/-- Two strictly positive finite PMFs induce mutually absolutely continuous measures. [the hp condition](hyp:hp); and [the hq condition](hyp:hq). [the stated conclusion](goal). -/
lemma absolutelyContinuous_of_fullSupport {W : Type*} [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W] {p q : PMF W}
    (hp : FullSupportPMF p) (hq : FullSupportPMF q) : p.toMeasure ≪ q.toMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro s _ hqs
  have hs_empty : s = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    have hle : q.toMeasure {w} ≤ q.toMeasure s :=
      measure_mono (Set.singleton_subset_iff.mpr hw)
    rw [hqs] at hle
    have hzero : q.toMeasure {w} = 0 := bot_unique hle
    rw [q.toMeasure_apply_singleton w (MeasurableSet.singleton w)] at hzero
    exact (ne_of_gt (hq w)) hzero
  simp [hs_empty]

/-- The normalized overlap radius belongs to `[0,1)` when `C ≥ 1`. [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma overlapRadius_mem {C : ℝ} (hC : 1 ≤ C) : overlapRadius C ∈ Set.Ico 0 1 := by
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  constructor
  · exact div_nonneg (sub_nonneg.mpr hC) hC_pos.le
  · exact (div_lt_one hC_pos).2 (by linarith)


end CausalSmith.Stat.PomdpLatentOverlapMinimax
