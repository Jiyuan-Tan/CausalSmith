module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Full and observed history factorization for finite POMDP trajectories. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The unique path law selected by an initial stationary law and the complete-history
behavior-action and joint reward-transition kernels. -/
def GeneratedPathLaw {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (μ : Measure (FullPath T nX nH k)) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ s, (μ.map (fun w => stateAt w 0)) {s} =
    ENNReal.ofReal (stationaryLaw (policyKernel M M.b) s)) ∧
  (∀ t : Fin T, μ.map (fun w => (preHist t w, actionAt w t)) =
    (μ.map (preHist t)).compProd
      (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop))) ∧
  (∀ t : Fin T, μ.map (fun w => (postHist t w, (rewardAt w t, nextState w t))) =
    (μ.map (postHist t)).compProd
      (Kernel.comap (kernelOfK M) (fun h => (h.1.2.2, h.2)) (by fun_prop)))

noncomputable def generatedPathLaw {T nX nH k : Nat} (M : PomdpModel T nX nH k) :
    Measure (FullPath T nX nH k) := Classical.epsilon (GeneratedPathLaw M)

-- @node: full_history_generated_law
/-- The full-history assumptions and stationary initialization certify the given
behavior law as a generated path law. -/
lemma full_history_generated_law {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hK : FullFiltrationPomdp M) (hA : FullFiltrationRandomization M)
    (hStart : StationaryStart M) : GeneratedPathLaw M M.law := by
  exact ⟨M.law_prob, hStart.2, hA.2, hK.2⟩

-- @node: generated_path_law_preHist_unique
/-- Two generated path laws have the same complete pre-action history marginal at
every time. -/
lemma generated_path_law_preHist_unique {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) {μ ν : Measure (FullPath T nX nH k)}
    (hμ : GeneratedPathLaw M μ) (hν : GeneratedPathLaw M ν) :
    ∀ t : Fin T, μ.map (preHist t) = ν.map (preHist t) := by
  have go : ∀ m, ∀ t : Fin T, t.val = m →
      μ.map (preHist t) = ν.map (preHist t) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro t ht
      cases m with
      | zero =>
          have ht' : t = ⟨0, ht ▸ t.isLt⟩ := Fin.ext ht
          have hstate : μ.map (fun w => stateAt w 0) =
              ν.map (fun w => stateAt w 0) := by
            apply Measure.ext_of_singleton
            intro s
            rw [hμ.2.1 s, hν.2.1 s]
          let embed : JointState nX nH → PreHistory T nX nH k t :=
            fun s => (fun i => (Fin.cast ht i).elim0,
              fun i => (Fin.cast ht i).elim0, s)
          have hembed : Measurable embed := by
            unfold embed
            fun_prop
          have hpre (w : FullPath T nX nH k) :
              embed (stateAt w 0) = preHist t w := by
            unfold embed preHist currentState pastIndex stateAt
            apply Prod.ext
            · funext i
              exact (Fin.cast ht i).elim0
            · apply Prod.ext
              · funext i
                exact (Fin.cast ht i).elim0
              · apply congrArg w.1
                apply Fin.ext
                simp [ht]
          rw [show μ.map (preHist t) = (μ.map (fun w => stateAt w 0)).map embed by
                rw [Measure.map_map hembed (by unfold stateAt; fun_prop)]
                apply Measure.map_congr
                filter_upwards [] with w
                exact (hpre w).symm,
            show ν.map (preHist t) = (ν.map (fun w => stateAt w 0)).map embed by
                rw [Measure.map_map hembed (by unfold stateAt; fun_prop)]
                apply Measure.map_congr
                filter_upwards [] with w
                exact (hpre w).symm,
            hstate]
      | succ m =>
          have hmt : m + 1 < T := by simpa [ht] using t.isLt
          have ht' : t = ⟨m + 1, hmt⟩ := Fin.ext ht
          rw [ht']
          let u : Fin T := ⟨m, Nat.lt_of_succ_lt hmt⟩
          have hpre_u : μ.map (preHist u) = ν.map (preHist u) :=
            ih m (Nat.lt_succ_self m) u rfl
          have hpost : μ.map (postHist u) = ν.map (postHist u) := by
            rw [show μ.map (postHist u) =
                  (μ.map (preHist u)).compProd
                    (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop)) by
                  exact hμ.2.2.1 u,
                show ν.map (postHist u) =
                  (ν.map (preHist u)).compProd
                    (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop)) by
                  exact hν.2.2.1 u,
                hpre_u]
          have hjoint :
              μ.map (fun w => (postHist u w, (rewardAt w u, nextState w u))) =
                ν.map (fun w => (postHist u w, (rewardAt w u, nextState w u))) := by
            rw [hμ.2.2.2 u, hν.2.2.2 u, hpost]
          let advance : PostHistory T nX nH k u × (ℝ × JointState nX nH) →
              PreHistory T nX nH k ⟨m + 1, hmt⟩ := fun q =>
            (Fin.snoc q.1.1.1 q.1.1.2.2,
              Fin.snoc q.1.1.2.1 (q.1.2, q.2.1), q.2.2)
          have hadvance : Measurable advance := by
            unfold advance
            fun_prop
          have hadvance_path (w : FullPath T nX nH k) :
              advance (postHist u w, (rewardAt w u, nextState w u)) =
                preHist ⟨m + 1, hmt⟩ w := by
            unfold advance postHist preHist currentState pastIndex actionAt rewardAt nextState
            apply Prod.ext
            · let f : Fin (m + 1) → JointState nX nH :=
                fun j => w.1 ⟨j.val,
                  lt_trans (lt_trans j.isLt hmt) (Nat.lt_succ_self T)⟩
              change Fin.snoc (Fin.init f) (f (Fin.last m)) = f
              exact Fin.snoc_init_self f
            · apply Prod.ext
              · let f : Fin (m + 1) → Fin k × ℝ :=
                  fun j => w.2 ⟨j.val, lt_trans j.isLt hmt⟩
                change Fin.snoc (Fin.init f) (f (Fin.last m)) = f
                exact Fin.snoc_init_self f
              · apply congrArg w.1
                apply Fin.ext
                rfl
          rw [show μ.map (preHist ⟨m + 1, hmt⟩) =
                (μ.map (fun w => (postHist u w, (rewardAt w u, nextState w u)))).map
                  advance by
                rw [Measure.map_map hadvance (by
                  unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
                  fun_prop)]
                apply Measure.map_congr
                filter_upwards [] with w
                exact (hadvance_path w).symm,
            show ν.map (preHist ⟨m + 1, hmt⟩) =
                (ν.map (fun w => (postHist u w, (rewardAt w u, nextState w u)))).map
                  advance by
                rw [Measure.map_map hadvance (by
                  unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
                  fun_prop)]
                apply Measure.map_congr
                filter_upwards [] with w
                exact (hadvance_path w).symm,
            hjoint]
  intro t
  exact go t.val t rfl

-- @node: generated_path_law_unique
/-- The initial marginal and the sequential action and reward-transition
factorizations uniquely determine a generated finite path law. -/
lemma generated_path_law_unique {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) {μ ν : Measure (FullPath T nX nH k)}
    (hμ : GeneratedPathLaw M μ) (hν : GeneratedPathLaw M ν) : μ = ν := by
  cases T with
  | zero =>
      have hstate : μ.map (fun w => stateAt w 0) =
          ν.map (fun w => stateAt w 0) := by
        apply Measure.ext_of_singleton
        intro s
        rw [hμ.2.1 s, hν.2.1 s]
      let decode : JointState nX nH → FullPath 0 nX nH k :=
        fun s => (fun _ => s, fun i => i.elim0)
      have hdecode : Measurable decode := by unfold decode; fun_prop
      have hleft (w : FullPath 0 nX nH k) : decode (stateAt w 0) = w := by
        apply Prod.ext
        · funext i
          exact Fin.eq_zero i ▸ rfl
        · funext i
          exact i.elim0
      have hencode : Measurable (fun w : FullPath 0 nX nH k => stateAt w 0) := by
        unfold stateAt
        fun_prop
      have hcomp : decode ∘ (fun w : FullPath 0 nX nH k => stateAt w 0) = id := by
        funext w
        exact hleft w
      have := congrArg (Measure.map decode) hstate
      rw [Measure.map_map hdecode hencode, Measure.map_map hdecode hencode,
        hcomp, Measure.map_id] at this
      simpa using this
  | succ m =>
      let t : Fin (m + 1) := Fin.last m
      have hpre := generated_path_law_preHist_unique M hμ hν t
      have hpost : μ.map (postHist t) = ν.map (postHist t) := by
        rw [show μ.map (postHist t) =
              (μ.map (preHist t)).compProd
                (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop)) by
              exact hμ.2.2.1 t,
            show ν.map (postHist t) =
              (ν.map (preHist t)).compProd
                (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop)) by
              exact hν.2.2.1 t,
            hpre]
      have hjoint :
          μ.map (fun w => (postHist t w, (rewardAt w t, nextState w t))) =
            ν.map (fun w => (postHist t w, (rewardAt w t, nextState w t))) := by
        rw [hμ.2.2.2 t, hν.2.2.2 t, hpost]
      let decode : PostHistory (m + 1) nX nH k t × (ℝ × JointState nX nH) →
          FullPath (m + 1) nX nH k := fun q =>
        (Fin.snoc (Fin.snoc q.1.1.1 q.1.1.2.2) q.2.2,
          Fin.snoc q.1.1.2.1 (q.1.2, q.2.1))
      have hdecode : Measurable decode := by unfold decode; fun_prop
      have hleft (w : FullPath (m + 1) nX nH k) :
          decode (postHist t w, (rewardAt w t, nextState w t)) = w := by
        change (Fin.snoc (Fin.snoc (Fin.init (Fin.init w.1))
            ((Fin.init w.1) (Fin.last m))) (w.1 (Fin.last (m + 1))),
          Fin.snoc (Fin.init w.2) (w.2 (Fin.last m))) = w
        rw [Fin.snoc_init_self, Fin.snoc_init_self, Fin.snoc_init_self]
      have hencode : Measurable
          (fun w : FullPath (m + 1) nX nH k =>
            (postHist t w, (rewardAt w t, nextState w t))) := by
        unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
        fun_prop
      have hcomp : decode ∘
          (fun w : FullPath (m + 1) nX nH k =>
            (postHist t w, (rewardAt w t, nextState w t))) = id := by
        funext w
        exact hleft w
      have := congrArg (Measure.map decode) hjoint
      rw [Measure.map_map hdecode hencode, Measure.map_map hdecode hencode,
        hcomp, Measure.map_id] at this
      simpa using this

noncomputable def targetStep {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (f : JointState nX nH → ℝ) : JointState nX nH → ℝ :=
  fun s => ∑ s', policyKernel M M.e s s' * f s'

noncomputable def windowScore {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j t : Fin T) (w : FullPath T nX nH k) : ℝ :=
  rewardAt w t * ∏ q ∈ Finset.univ.filter
    (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val),
      ratio M.b M.e (currentState w q).1 (actionAt w q)

-- @node: policy_change_finite
/-- A one-step importance ratio changes a finite behavior-action sum to the
target-action sum, including behavior-null actions. -/
lemma policy_change_finite {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hOverlap : PolicyOverlap zeta M)
    (x : Fin nX) (f : Fin k → ℝ) :
    (∑ a : Fin k, M.b x a * ratio M.b M.e x a * f a) =
      ∑ a : Fin k, M.e x a * f a := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases hb : M.b x a = 0
  · have he : M.e x a = 0 := by
      have he0 := (hOverlap.1 x).1 a
      have he1 := hOverlap.2 x a
      rw [hb, mul_zero] at he1
      exact le_antisymm he1 he0
    simp [ratio, hb, he]
  · simp only [ratio, if_neg hb]
    field_simp

-- @node: policy_ratio_bounds
/-- The policy ratio is nonnegative and bounded by the overlap factor, also on
behavior-null cells. -/
lemma policy_ratio_bounds {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hOverlap : PolicyOverlap zeta M)
    (hBehavior : PolicyVector M.b) (x : Fin nX) (a : Fin k) :
    0 ≤ ratio M.b M.e x a ∧ ratio M.b M.e x a ≤ policyFactor zeta := by
  by_cases hb : M.b x a = 0
  · simp [ratio, hb, policyFactor, Real.exp_nonneg]
  · have hbpos : 0 < M.b x a := lt_of_le_of_ne ((hBehavior x).1 a) (Ne.symm hb)
    have he := (hOverlap.1 x).1 a
    constructor
    · simpa [ratio, hb] using div_nonneg he (le_of_lt hbpos)
    · simpa [ratio, hb] using (div_le_iff₀ hbpos).2 (hOverlap.2 x a)

-- @node: full_history_integral_ratio_step
/-- Integrating one likelihood ratio against the behavior-action factorization
replaces the behavior action weights by target-policy weights. -/
lemma full_history_integral_ratio_step {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (t : Fin T)
    (f : PreHistory T nX nH k t × Fin k → ℝ)
    (hf : Integrable f (M.law.map (fun w => (preHist t w, actionAt w t)))) :
    ∫ z, ratio M.b M.e z.1.2.2.1 z.2 * f z
        ∂(M.law.map (fun w => (preHist t w, actionAt w t))) =
      ∫ h, ∑ a : Fin k, M.e h.2.2.1 a * f (h, a)
        ∂(M.law.map (preHist t)) := by
  letI : IsMarkovKernel (actionKernel M) := by
    refine ⟨fun x => ⟨?_⟩⟩
    change (∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact (hA.1 x).1 a)]
    simp [(hA.1 x).2]
  rw [hA.2 t] at hf ⊢
  have hratio : Measurable (fun z : PreHistory T nX nH k t × Fin k =>
      ratio M.b M.e z.1.2.2.1 z.2) := by
    exact (measurable_of_countable fun xa : Fin nX × Fin k => ratio M.b M.e xa.1 xa.2).comp
      (((by fun_prop : Measurable fun z : PreHistory T nX nH k t × Fin k =>
        z.1.2.2.1)).prodMk measurable_snd)
  have hg : Integrable (fun z : PreHistory T nX nH k t × Fin k =>
      ratio M.b M.e z.1.2.2.1 z.2 * f z)
      ((M.law.map (preHist t)).compProd
        (Kernel.comap (actionKernel M) (fun h => h.2.2.1) (by fun_prop))) := by
    apply hf.bdd_mul hratio.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
    exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
  rw [Measure.integral_compProd hg]
  apply integral_congr_ae
  filter_upwards with h
  change (∫ a, ratio M.b M.e h.2.2.1 a * f (h, a) ∂
      ∑ a : Fin k, ENNReal.ofReal (M.b h.2.2.1 a) • Measure.dirac a) = _
  rw [integral_finsetSum_measure (fun a _ =>
    (integrable_dirac (f := fun b : Fin k => ratio M.b M.e h.2.2.1 b * f (h, b))
      enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal ((hA.1 _).1 _), smul_eq_mul]
  simpa only [mul_assoc] using
    policy_change_finite M hOverlap h.2.2.1 (fun a => f (h, a))

-- @node: full_history_integral_kernel_step
/-- Integrating a reward-transition function against the joint-history law
integrates it first against the model kernel. -/
lemma full_history_integral_kernel_step {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M) (t : Fin T)
    (f : PostHistory T nX nH k t × (ℝ × JointState nX nH) → ℝ)
    (hf : Integrable f
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t))))) :
    ∫ z, f z ∂(M.law.map (fun w =>
        (postHist t w, (rewardAt w t, nextState w t)))) =
      ∫ h, ∫ y, f (h, y) ∂(M.K h.1.2.2 h.2)
        ∂(M.law.map (postHist t)) := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  rw [hK.2 t] at hf ⊢
  rw [Measure.integral_compProd hf]
  rfl

-- @node: restrictPreHist
/-- Restrict a complete pre-action history to an earlier epoch. -/
def restrictPreHist {T nX nH k : Nat} (j r : Fin T) (hjr : j.val ≤ r.val) :
    PreHistory T nX nH k r → PreHistory T nX nH k j := fun h =>
  (fun i => h.1 (Fin.castLE hjr i),
    fun i => h.2.1 (Fin.castLE hjr i),
    if heq : j.val = r.val then h.2.2 else
      h.1 ⟨j.val, lt_of_le_of_ne hjr heq⟩)

-- @node: restrictPreHist_measurable
/-- Restriction of complete pre-action histories is measurable. -/
lemma restrictPreHist_measurable {T nX nH k : Nat} (j r : Fin T)
    (hjr : j.val ≤ r.val) : Measurable (restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr) := by
  by_cases heq : j.val = r.val
  · unfold restrictPreHist
    simp only [dif_pos heq]
    fun_prop
  · unfold restrictPreHist
    simp only [dif_neg heq]
    fun_prop

-- @node: restrictPreHist_preHist
/-- Restricting a path's later prehistory recovers its earlier prehistory. -/
lemma restrictPreHist_preHist {T nX nH k : Nat} (j r : Fin T)
    (hjr : j.val ≤ r.val) (w : FullPath T nX nH k) :
    restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr (preHist r w) =
      preHist j w := by
  unfold restrictPreHist preHist currentState pastIndex
  apply Prod.ext
  · funext i
    rfl
  · apply Prod.ext
    · funext i
      rfl
    · split_ifs with heq
      · apply congrArg w.1
        apply Fin.ext
        exact heq.symm
      · rfl

-- @node: nextPreHistory
/-- Append the current action, reward, and successor state to a complete prehistory. -/
def nextPreHistory {T nX nH k : Nat} (r : Fin T) (hr : r.val + 1 < T) :
    PostHistory T nX nH k r × (ℝ × JointState nX nH) →
      PreHistory T nX nH k ⟨r.val + 1, hr⟩ := fun q =>
  (Fin.snoc q.1.1.1 q.1.1.2.2,
    Fin.snoc q.1.1.2.1 (q.1.2, q.2.1), q.2.2)

-- @node: nextPreHistory_measurable
/-- Appending one complete transition to a prehistory is measurable. -/
lemma nextPreHistory_measurable {T nX nH k : Nat} (r : Fin T) (hr : r.val + 1 < T) :
    Measurable (nextPreHistory (nX := nX) (nH := nH) (k := k) r hr) := by
  unfold nextPreHistory
  fun_prop

-- @node: nextPreHistory_path
/-- Appending the transition encoded by a path produces its next prehistory. -/
lemma nextPreHistory_path {T nX nH k : Nat} (r : Fin T) (hr : r.val + 1 < T)
    (w : FullPath T nX nH k) :
    nextPreHistory (nX := nX) (nH := nH) (k := k) r hr
        (postHist r w, (rewardAt w r, nextState w r)) =
      preHist ⟨r.val + 1, hr⟩ w := by
  unfold nextPreHistory postHist preHist currentState pastIndex actionAt rewardAt nextState
  apply Prod.ext
  · let f : Fin (r.val + 1) → JointState nX nH :=
      fun i => w.1 ⟨i.val, lt_trans (lt_trans i.isLt hr) (Nat.lt_succ_self T)⟩
    change Fin.snoc (Fin.init f) (f (Fin.last r.val)) = f
    exact Fin.snoc_init_self f
  · apply Prod.ext
    · let f : Fin (r.val + 1) → Fin k × ℝ :=
        fun i => w.2 ⟨i.val, lt_trans i.isLt hr⟩
      change Fin.snoc (Fin.init f) (f (Fin.last r.val)) = f
      exact Fin.snoc_init_self f
    · apply congrArg w.1
      apply Fin.ext
      rfl

-- @node: historyRatioCarrier
/-- The event indicator at epoch `j`, multiplied by all likelihood ratios from
`j` through the epoch immediately preceding `r`, as a function of the prehistory at `r`. -/
noncomputable def historyRatioCarrier {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j r : Fin T) (hjr : j.val ≤ r.val) (B : Set (PreHistory T nX nH k j))
    (h : PreHistory T nX nH k r) : ℝ :=
  B.indicator (fun _ =>
    ∏ q : Fin r.val, if j.val ≤ q.val then
      ratio M.b M.e (h.1 q).1 (h.2.1 q).1 else 1)
    (restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr h)

-- @node: historyRatioCarrier_measurable
/-- The finite likelihood-ratio history carrier is measurable. -/
lemma historyRatioCarrier_measurable {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j r : Fin T) (hjr : j.val ≤ r.val) (B : Set (PreHistory T nX nH k j))
    (hB : MeasurableSet B) :
    Measurable (historyRatioCarrier M j r hjr B) := by
  unfold historyRatioCarrier
  apply Measurable.indicator _ (hB.preimage (restrictPreHist_measurable j r hjr))
  apply Finset.measurable_prod
  intro q _
  by_cases hq : j.val ≤ q.val
  · simp only [if_pos hq]
    exact (measurable_of_countable fun xa : Fin nX × Fin k => ratio M.b M.e xa.1 xa.2).comp
      (((by fun_prop : Measurable fun h : PreHistory T nX nH k r => (h.1 q).1)).prodMk
        (by fun_prop : Measurable fun h : PreHistory T nX nH k r => (h.2.1 q).1))
  · simp only [if_neg hq]
    fun_prop

-- @node: historyRatioCarrier_preHist
/-- On a path, the history carrier is the original event indicator times the
ratio product over all epochs before `r`. -/
lemma historyRatioCarrier_preHist {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j r : Fin T) (hjr : j.val ≤ r.val) (B : Set (PreHistory T nX nH k j))
    (w : FullPath T nX nH k) :
    historyRatioCarrier M j r hjr B (preHist r w) =
      B.indicator (fun _ =>
        ∏ q : Fin r.val, if j.val ≤ q.val then
          ratio M.b M.e (currentState w (pastIndex r q)).1
            (actionAt w (pastIndex r q)) else 1) (preHist j w) := by
  rw [historyRatioCarrier, restrictPreHist_preHist]
  rfl

-- @node: historyRatioCarrier_self
/-- At its starting epoch, the carrier is exactly the event indicator. -/
lemma historyRatioCarrier_self {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j : Fin T) (B : Set (PreHistory T nX nH k j)) (h : PreHistory T nX nH k j) :
    historyRatioCarrier M j j (le_refl _) B h = B.indicator (fun _ => 1) h := by
  unfold historyRatioCarrier restrictPreHist
  have hq : ∀ q : Fin j.val, ¬j.val ≤ q.val := by intro q; omega
  simp [hq]

-- @node: restrictPreHist_nextPreHistory
/-- Restricting an appended prehistory to an epoch no later than the old endpoint
agrees with restricting the old prehistory directly. -/
lemma restrictPreHist_nextPreHistory {T nX nH k : Nat}
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (q : PostHistory T nX nH k r × (ℝ × JointState nX nH)) :
    restrictPreHist (nX := nX) (nH := nH) (k := k) j ⟨r.val + 1, hr⟩
        (Nat.le_succ_of_le hjr) (nextPreHistory r hr q) =
      restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr q.1.1 := by
  unfold restrictPreHist nextPreHistory
  apply Prod.ext
  · funext i
    change (Fin.snoc q.1.1.1 q.1.1.2.2 : Fin (r.val + 1) → JointState nX nH)
        (Fin.castLE (Nat.le_succ_of_le hjr) i) =
      q.1.1.1 (Fin.castLE hjr i)
    have hi : Fin.castLE (Nat.le_succ_of_le hjr) i =
        Fin.castSucc (Fin.castLE hjr i) := by apply Fin.ext; rfl
    rw [hi, Fin.snoc_castSucc]
  · apply Prod.ext
    · funext i
      change (Fin.snoc q.1.1.2.1 (q.1.2, q.2.1) : Fin (r.val + 1) → Fin k × ℝ)
          (Fin.castLE (Nat.le_succ_of_le hjr) i) = q.1.1.2.1 (Fin.castLE hjr i)
      have hi : Fin.castLE (Nat.le_succ_of_le hjr) i =
          Fin.castSucc (Fin.castLE hjr i) := by apply Fin.ext; rfl
      rw [hi, Fin.snoc_castSucc]
    · by_cases heq : j.val = r.val
      · dsimp only [Prod.fst, Prod.snd]
        rw [dif_pos heq]
        have hjs : j.val < r.val + 1 := by omega
        change (if h : j.val = r.val + 1 then q.2.2 else
            (Fin.snoc q.1.1.1 q.1.1.2.2 : Fin (r.val + 1) → JointState nX nH)
              ⟨j.val, hjs⟩) = q.1.1.2.2
        rw [dif_neg (by omega)]
        have hi : (⟨j.val, hjs⟩ : Fin (r.val + 1)) = Fin.last r.val := by
          apply Fin.ext
          exact heq
        rw [hi, Fin.snoc_last]
      · dsimp only [Prod.fst, Prod.snd]
        rw [dif_neg heq]
        have hjr' : j.val < r.val := lt_of_le_of_ne hjr heq
        have hjs : j.val < r.val + 1 := by omega
        change (if h : j.val = r.val + 1 then q.2.2 else
            (Fin.snoc q.1.1.1 q.1.1.2.2 : Fin (r.val + 1) → JointState nX nH)
              ⟨j.val, hjs⟩) = q.1.1.1 ⟨j.val, hjr'⟩
        rw [dif_neg (by omega)]
        have hi : (⟨j.val, hjs⟩ : Fin (r.val + 1)) =
            Fin.castSucc (⟨j.val, hjr'⟩ : Fin r.val) := by apply Fin.ext; rfl
        rw [hi, Fin.snoc_castSucc]

-- @node: historyRatioCarrier_next
/-- Appending epoch `r` multiplies the history carrier by the likelihood ratio
of the appended action. -/
lemma historyRatioCarrier_next {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (B : Set (PreHistory T nX nH k j))
    (q : PostHistory T nX nH k r × (ℝ × JointState nX nH)) :
    historyRatioCarrier M j ⟨r.val + 1, hr⟩ (Nat.le_succ_of_le hjr) B
        (nextPreHistory r hr q) =
      historyRatioCarrier M j r hjr B q.1.1 *
        ratio M.b M.e q.1.1.2.2.1 q.1.2 := by
  unfold historyRatioCarrier
  rw [restrictPreHist_nextPreHistory j r hjr hr q]
  by_cases hB : restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr q.1.1 ∈ B
  · simp only [Set.indicator_of_mem hB, nextPreHistory]
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, hjr]
  · simp [hB]

-- @node: integral_nextState_eq_sum
/-- Integrating a function of the successor state against a transition kernel is
the corresponding finite marginal sum. -/
lemma integral_nextState_eq_sum {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hK : FullFiltrationPomdp M) (s : JointState nX nH) (a : Fin k)
    (F : JointState nX nH → ℝ) :
    ∫ y, F y.2 ∂(M.K s a) =
      ∑ s', (M.K s a {y | y.2 = s'}).toReal * F s' := by
  letI : IsProbabilityMeasure (M.K s a) := hK.1 s a
  have hm : Measurable (fun y : ℝ × JointState nX nH => y.2) := measurable_snd
  haveI : IsProbabilityMeasure ((M.K s a).map (fun y => y.2)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hF : Integrable F ((M.K s a).map (fun y => y.2)) := Integrable.of_finite
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable,
    MeasureTheory.integral_fintype hF]
  apply Finset.sum_congr rfl
  intro s' _
  change ((M.K s a).map (fun y => y.2) {s'}).toReal * F s' = _
  rw [Measure.map_apply hm (measurableSet_singleton s')]
  rfl

-- @node: targetStep_eq_action_integral
/-- A target-policy action average of successor-state integrals is one
application of the target transition operator. -/
lemma targetStep_eq_action_integral {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hK : FullFiltrationPomdp M) (s : JointState nX nH)
    (F : JointState nX nH → ℝ) :
    ∑ a : Fin k, M.e s.1 a * ∫ y, F y.2 ∂(M.K s a) = targetStep M F s := by
  simp_rw [integral_nextState_eq_sum M hK]
  unfold targetStep policyKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s' _
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

-- @node: historyRatioCarrier_norm_bound
/-- The history carrier is uniformly bounded by the overlap factor raised to
the number of preceding epochs. -/
lemma historyRatioCarrier_norm_bound {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (B : Set (PreHistory T nX nH k j)) (h : PreHistory T nX nH k r) :
    ‖historyRatioCarrier M j r hjr B h‖ ≤ max 1 (policyFactor zeta) ^ r.val := by
  unfold historyRatioCarrier
  by_cases hmem : restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr h ∈ B
  · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun q _ => by
        split_ifs
        · exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
        · exact zero_le_one)]
    calc
      (∏ q : Fin r.val, if j.val ≤ q.val then
          ratio M.b M.e (h.1 q).1 (h.2.1 q).1 else 1) ≤
          ∏ _q : Fin r.val, max 1 (policyFactor zeta) := by
            apply Finset.prod_le_prod
            · intro q _
              split_ifs
              · exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
              · exact zero_le_one
            · intro q _
              split_ifs
              · exact (policy_ratio_bounds M hOverlap hA.1 _ _).2.trans (le_max_right _ _)
              · exact le_max_left _ _
      _ = _ := by simp
  · simp only [Set.indicator, hmem, if_false, norm_zero]
    exact pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

-- @node: terminalCarrier_integrable
/-- The terminal weighted reward is integrable under the joint history law. -/
lemma terminalCarrier_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (B : Set (PreHistory T nX nH k j)) (hB : MeasurableSet B) :
    Integrable (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
      historyRatioCarrier M j t hjt B z.1.1 *
        ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  rw [hK.2 t]
  let κ := Kernel.comap (kernelOfK M)
    (fun h : PostHistory T nX nH k t => (h.1.2.2, h.2)) (by fun_prop)
  have hratio : Measurable (fun z : PostHistory T nX nH k t ×
      (ℝ × JointState nX nH) => ratio M.b M.e z.1.1.2.2.1 z.1.2) := by
    exact (measurable_of_countable fun xa : Fin nX × Fin k => ratio M.b M.e xa.1 xa.2).comp
      ((by fun_prop : Measurable fun z : PostHistory T nX nH k t ×
        (ℝ × JointState nX nH) => (z.1.1.2.2.1, z.1.2)))
  have hm : Measurable (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
      historyRatioCarrier M j t hjt B z.1.1 *
        ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1) := by
    exact (((historyRatioCarrier_measurable M j t hjt B hB).comp
      (by fun_prop)).mul hratio).mul (by fun_prop)
  rw [Measure.integrable_compProd_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards with h
    change Integrable (fun y =>
      (historyRatioCarrier M j t hjt B h.1 * ratio M.b M.e h.1.2.2.1 h.2) * y.1)
      (M.K h.1.2.2 h.2)
    exact (hY h.1.2.2 h.2).1.const_mul _
  · obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k =>
        ∫ y, ‖y.1‖ ∂(M.K sa.1 sa.2))
    have hout : StronglyMeasurable (fun x : PostHistory T nX nH k t =>
        ∫ y, ‖historyRatioCarrier M j t hjt B x.1 *
          ratio M.b M.e x.1.2.2.1 x.2 * y.1‖ ∂κ x) :=
      hm.norm.stronglyMeasurable.integral_kernel_prod_right'
    apply Integrable.of_bound hout.aestronglyMeasurable
      (max 1 (policyFactor zeta) ^ t.val * policyFactor zeta * C)
    filter_upwards with h
    change ‖∫ y, ‖historyRatioCarrier M j t hjt B h.1 *
      ratio M.b M.e h.1.2.2.1 h.2 * y.1‖ ∂(M.K h.1.2.2 h.2)‖ ≤ _
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc
      (∫ y, ‖historyRatioCarrier M j t hjt B h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * y.1‖ ∂(M.K h.1.2.2 h.2)) =
          ‖historyRatioCarrier M j t hjt B h.1‖ *
            ‖ratio M.b M.e h.1.2.2.1 h.2‖ *
              ∫ y, ‖y.1‖ ∂(M.K h.1.2.2 h.2) := by
            simp_rw [norm_mul]
            rw [MeasureTheory.integral_const_mul]
      _ ≤ _ := by
        have hc := historyRatioCarrier_norm_bound M hA hOverlap j t hjt B h.1
        have hr : ‖ratio M.b M.e h.1.2.2.1 h.2‖ ≤ policyFactor zeta := by
          rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
        have hi : 0 ≤ ∫ y, ‖y.1‖ ∂(M.K h.1.2.2 h.2) :=
          integral_nonneg fun _ => norm_nonneg _
        exact mul_le_mul (mul_le_mul hc hr (norm_nonneg _) (pow_nonneg (by positivity) _))
          (hC (h.1.2.2, h.2)) hi (mul_nonneg (pow_nonneg (by positivity) _)
            (Real.exp_nonneg _))

-- @node: terminalCarrierAction_integrable
/-- The carrier times the conditional reward mean is integrable under the
prehistory-action law. -/
lemma terminalCarrierAction_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hY : RewardMomentEnvelope M) (hOverlap : PolicyOverlap zeta M)
    (j t : Fin T) (hjt : j.val ≤ t.val) (B : Set (PreHistory T nX nH k j))
    (hB : MeasurableSet B) :
    Integrable (fun z : PreHistory T nX nH k t × Fin k =>
      historyRatioCarrier M j t hjt B z.1 * ∫ y, y.1 ∂(M.K z.1.2.2 z.2))
      (M.law.map (fun w => (preHist t w, actionAt w t))) := by
  have hm : Measurable (fun z : PreHistory T nX nH k t × Fin k =>
      historyRatioCarrier M j t hjt B z.1 * ∫ y, y.1 ∂(M.K z.1.2.2 z.2)) := by
    apply Measurable.mul ((historyRatioCarrier_measurable M j t hjt B hB).comp measurable_fst)
    exact (measurable_of_countable fun sa : JointState nX nH × Fin k =>
      ∫ y, y.1 ∂(M.K sa.1 sa.2)).comp
        (by fun_prop : Measurable fun z : PreHistory T nX nH k t × Fin k =>
          (z.1.2.2, z.2))
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k =>
    ‖∫ y, y.1 ∂(M.K sa.1 sa.2)‖)
  have hmap : Measurable (fun w : FullPath T nX nH k => (preHist t w, actionAt w t)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  haveI : IsProbabilityMeasure (M.law.map (fun w => (preHist t w, actionAt w t))) :=
    Measure.isProbabilityMeasure_map hmap.aemeasurable
  apply Integrable.of_bound hm.aestronglyMeasurable
    (max 1 (policyFactor zeta) ^ t.val * C)
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_mul (historyRatioCarrier_norm_bound M hA hOverlap j t hjt B z.1)
    (hC (z.1.2.2, z.2)) (norm_nonneg _) (pow_nonneg (by positivity) _)

-- @node: terminalCarrier_peeling
/-- Peeling the terminal weighted reward replaces it by the target-policy
reward regression at the terminal current state. -/
lemma terminalCarrier_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (B : Set (PreHistory T nX nH k j)) (hB : MeasurableSet B) :
    ∫ w, historyRatioCarrier M j t hjt B (preHist t w) *
        ratio M.b M.e (currentState w t).1 (actionAt w t) * rewardAt w t ∂M.law =
      ∫ w, historyRatioCarrier M j t hjt B (preHist t w) *
        rewardRegression M (currentState w t) ∂M.law := by
  have hfull := terminalCarrier_integrable M hK hA hY hOverlap j t hjt B hB
  have haction := terminalCarrierAction_integrable M hA hY hOverlap j t hjt B hB
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpreact : Measurable (fun w : FullPath T nX nH k =>
      (preHist t w, actionAt w t)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  have hpre : Measurable (preHist t : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, historyRatioCarrier M j t hjt B z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1
          ∂(M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
        rw [integral_map henc.aemeasurable hfull.aestronglyMeasurable]
        rfl
    _ = ∫ h, ∫ y, historyRatioCarrier M j t hjt B h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * y.1 ∂(M.K h.1.2.2 h.2)
          ∂(M.law.map (postHist t)) :=
      full_history_integral_kernel_step M hK t _ hfull
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (historyRatioCarrier M j t hjt B z.1 *
            ∫ y, y.1 ∂(M.K z.1.2.2 z.2))
          ∂(M.law.map (fun w => (preHist t w, actionAt w t))) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (historyRatioCarrier M j t hjt B h * ∫ y, y.1 ∂(M.K h.2.2 a))
          ∂(M.law.map (preHist t)) :=
      full_history_integral_ratio_step M hA hOverlap t _ haction
    _ = ∫ h, historyRatioCarrier M j t hjt B h * rewardRegression M h.2.2
          ∂(M.law.map (preHist t)) := by
        apply integral_congr_ae
        filter_upwards with h
        unfold rewardRegression
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((historyRatioCarrier_measurable M j t hjt B hB).mul
          ((measurable_of_finite (rewardRegression M)).comp (by fun_prop))).aestronglyMeasurable

-- @node: continuationCarrier_integrable
lemma continuationCarrier_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (B : Set (PreHistory T nX nH k j)) (hB : MeasurableSet B)
    (F : JointState nX nH → ℝ) :
    Integrable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
      historyRatioCarrier M j r hjr B z.1.1 *
        ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun s : JointState nX nH => ‖F s‖)
  have hm : Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
      historyRatioCarrier M j r hjr B z.1.1 *
        ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2) := by
    exact ((((historyRatioCarrier_measurable M j r hjr B hB).comp
      (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        z.1.1) by fun_prop)).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k => ratio M.b M.e xa.1 xa.2).comp
        (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
          (z.1.1.2.2.1, z.1.2)) by fun_prop))).mul
      ((measurable_of_finite F).comp
        (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
          z.2.2) by fun_prop)))
  have hmap : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  letI : IsProbabilityMeasure (M.law.map (fun w =>
      (postHist r w, (rewardAt w r, nextState w r)))) :=
    Measure.isProbabilityMeasure_map hmap.aemeasurable
  apply Integrable.of_bound hm.aestronglyMeasurable
    (max 1 (policyFactor zeta) ^ r.val * policyFactor zeta * C)
  filter_upwards with z
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (historyRatioCarrier_norm_bound M hA hOverlap j r hjr B z.1.1)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).2)
      (norm_nonneg _) (pow_nonneg (by positivity) _)) (hC z.2.2) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_nonneg _))

-- @node: continuationCarrierAction_integrable
lemma continuationCarrierAction_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val) (B : Set (PreHistory T nX nH k j))
    (hB : MeasurableSet B) (F : JointState nX nH → ℝ) :
    Integrable (fun z : PreHistory T nX nH k r × Fin k =>
      historyRatioCarrier M j r hjr B z.1 * ∫ y, F y.2 ∂(M.K z.1.2.2 z.2))
      (M.law.map (fun w => (preHist r w, actionAt w r))) := by
  have hm : Measurable (fun z : PreHistory T nX nH k r × Fin k =>
      historyRatioCarrier M j r hjr B z.1 * ∫ y, F y.2 ∂(M.K z.1.2.2 z.2)) := by
    exact ((historyRatioCarrier_measurable M j r hjr B hB).comp measurable_fst).mul
      ((measurable_of_countable fun sa : JointState nX nH × Fin k =>
        ∫ y, F y.2 ∂(M.K sa.1 sa.2)).comp
          (show Measurable (fun z : PreHistory T nX nH k r × Fin k =>
            (z.1.2.2, z.2)) by fun_prop))
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k =>
    ‖∫ y, F y.2 ∂(M.K sa.1 sa.2)‖)
  have hmap : Measurable (fun w : FullPath T nX nH k => (preHist r w, actionAt w r)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  letI : IsProbabilityMeasure (M.law.map (fun w => (preHist r w, actionAt w r))) :=
    Measure.isProbabilityMeasure_map hmap.aemeasurable
  apply Integrable.of_bound hm.aestronglyMeasurable (max 1 (policyFactor zeta) ^ r.val * C)
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_mul (historyRatioCarrier_norm_bound M hA hOverlap j r hjr B z.1)
    (hC (z.1.2.2, z.2)) (norm_nonneg _) (pow_nonneg (by positivity) _)

-- @node: continuationCarrier_peeling
lemma continuationCarrier_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (B : Set (PreHistory T nX nH k j)) (hB : MeasurableSet B)
    (F : JointState nX nH → ℝ) :
    ∫ w, historyRatioCarrier M j ⟨r.val + 1, hr⟩ (Nat.le_succ_of_le hjr) B
          (preHist ⟨r.val + 1, hr⟩ w) * F (currentState w ⟨r.val + 1, hr⟩) ∂M.law =
      ∫ w, historyRatioCarrier M j r hjr B (preHist r w) *
          targetStep M F (currentState w r) ∂M.law := by
  have hjoint := continuationCarrier_integrable M hA hOverlap j r hjr B hB F
  have haction := continuationCarrierAction_integrable M hK hA hOverlap j r hjr B hB F
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist r : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, historyRatioCarrier M j r hjr B z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2
          ∂(M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
        rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
        apply integral_congr_ae
        filter_upwards with w
        rw [← nextPreHistory_path r hr w]
        rw [historyRatioCarrier_next M j r hjr hr B]
        rfl
    _ = ∫ h, ∫ y, historyRatioCarrier M j r hjr B h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * F y.2 ∂(M.K h.1.2.2 h.2)
          ∂(M.law.map (postHist r)) :=
      full_history_integral_kernel_step M hK r _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (historyRatioCarrier M j r hjr B z.1 * ∫ y, F y.2 ∂(M.K z.1.2.2 z.2))
          ∂(M.law.map (fun w => (preHist r w, actionAt w r))) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (historyRatioCarrier M j r hjr B h * ∫ y, F y.2 ∂(M.K h.2.2 a))
          ∂(M.law.map (preHist r)) :=
      full_history_integral_ratio_step M hA hOverlap r _ haction
    _ = ∫ h, historyRatioCarrier M j r hjr B h * targetStep M F h.2.2
          ∂(M.law.map (preHist r)) := by
        apply integral_congr_ae
        filter_upwards with h
        rw [← targetStep_eq_action_integral M hK]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((historyRatioCarrier_measurable M j r hjr B hB).mul
          ((measurable_of_finite (targetStep M F)).comp (by fun_prop))).aestronglyMeasurable

-- @node: terminalCarrier_windowScore
lemma terminalCarrier_windowScore {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (j t : Fin T) (hjt : j.val ≤ t.val) (B : Set (PreHistory T nX nH k j))
    (w : FullPath T nX nH k) :
    historyRatioCarrier M j t hjt B (preHist t w) *
        ratio M.b M.e (currentState w t).1 (actionAt w t) * rewardAt w t =
      B.indicator (fun _ => windowScore M j t w) (preHist j w) := by
  rw [historyRatioCarrier_preHist]
  by_cases hw : preHist j w ∈ B
  · simp only [Set.indicator_of_mem hw]
    unfold windowScore
    have hp : (∏ q : Fin t.val, if j.val ≤ q.val then
        ratio M.b M.e (currentState w (pastIndex t q)).1
          (actionAt w (pastIndex t q)) else 1) *
        ratio M.b M.e (currentState w t).1 (actionAt w t) =
        ∏ q ∈ Finset.univ.filter
          (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val),
          ratio M.b M.e (currentState w q).1 (actionAt w q) := by
      have hbefore : (∏ q : Fin t.val, if j.val ≤ q.val then
          ratio M.b M.e (currentState w (pastIndex t q)).1
            (actionAt w (pastIndex t q)) else 1) =
          ∏ q ∈ Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val),
            ratio M.b M.e (currentState w q).1 (actionAt w q) := by
        rw [← Finset.prod_filter]
        apply Finset.prod_bij (fun q _ => (⟨q.val, lt_trans q.isLt t.isLt⟩ : Fin T))
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          exact ⟨hq, q.isLt⟩
        · intro a _ b _ hab
          apply Fin.ext
          simpa using congrArg Fin.val hab
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          refine ⟨⟨q.val, hq.2⟩, ?_, ?_⟩
          · simpa using hq.1
          apply Fin.ext
          rfl
        · intro q _
          rfl
      rw [hbefore, mul_comm]
      have hsets : insert t (Finset.univ.filter
          (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val)) =
          Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          rcases h with h | h
          · subst q; exact ⟨hjt, le_rfl⟩
          · exact ⟨h.1, Nat.le_of_lt h.2⟩
        · intro h
          by_cases hqt : q = t
          · exact Or.inl hqt
          · have hv : q.val ≠ t.val := fun hv => hqt (Fin.ext hv)
            exact Or.inr ⟨h.1, lt_of_le_of_ne h.2 hv⟩
      rw [← hsets]
      have hnot : t ∉ Finset.univ.filter
          (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val) := by simp
      exact (Finset.prod_insert (f := fun q : Fin T =>
        ratio M.b M.e (currentState w q).1 (actionAt w q)) hnot).symm
    rw [hp]
    ring
  · simp [hw]

-- @node: continuationCarrier_iteration
lemma continuationCarrier_iteration {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j : Fin T) (B : Set (PreHistory T nX nH k j)) (hB : MeasurableSet B)
    (n : Nat) (hjn : j.val ≤ n) (hnT : n < T) (F : JointState nX nH → ℝ) :
    ∫ w, historyRatioCarrier M j ⟨n, hnT⟩ hjn B (preHist ⟨n, hnT⟩ w) *
        F (currentState w ⟨n, hnT⟩) ∂M.law =
      ∫ w, historyRatioCarrier M j j le_rfl B (preHist j w) *
        ((targetStep M)^[n - j.val] F) (currentState w j) ∂M.law := by
  induction n, hjn using Nat.le_induction generalizing F with
  | base =>
      have he : (⟨j.val, hnT⟩ : Fin T) = j := by apply Fin.ext; rfl
      cases he
      simp
  | succ n hjn ih =>
      have hnT' : n < T := lt_trans (Nat.lt_succ_self n) hnT
      calc
        _ = ∫ w, historyRatioCarrier M j ⟨n, hnT'⟩ hjn B (preHist ⟨n, hnT'⟩ w) *
              targetStep M F (currentState w ⟨n, hnT'⟩) ∂M.law :=
          continuationCarrier_peeling M hK hA hOverlap j ⟨n, hnT'⟩ hjn hnT B hB F
        _ = ∫ w, historyRatioCarrier M j j le_rfl B (preHist j w) *
              ((targetStep M)^[n - j.val] (targetStep M F)) (currentState w j) ∂M.law :=
          ih hnT' (targetStep M F)
        _ = _ := by
          have hd : n + 1 - j.val = (n - j.val) + 1 := by omega
          have hc : ((targetStep M)^[n - j.val] (targetStep M F)) =
              targetStep M ((targetStep M)^[n - j.val] F) := by
            exact (Function.iterate_succ_apply (targetStep M) (n - j.val) F).symm.trans
              (Function.iterate_succ_apply' (targetStep M) (n - j.val) F)
          rw [hd, Function.iterate_succ_apply', hc]

-- @node: compProd_map_comap_history
/-- Pushing a joint kernel law through a function of its conditioning coordinate
preserves the conditional kernel when the latter already factors through that function. -/
lemma compProd_map_comap_history {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (κ : Kernel β γ) [SFinite μ] [IsSFiniteKernel κ]
    (f : α → β) (hf : Measurable f) :
    (μ.compProd (κ.comap f hf)).map (fun p => (f p.1, p.2)) =
      (μ.map f).compProd κ := by
  have hpair : Measurable (fun p : α × γ => (f p.1, p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hpair hs,
    Measure.compProd_apply (hs.preimage hpair), Measure.compProd_apply hs]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply]
  rfl

-- @node: observed_history_randomization
/-- Full-history randomization descends to the observed pre-action history. -/
lemma observed_history_randomization {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hA : FullFiltrationRandomization M) (t : Fin T) :
    M.law.map (fun w => (obsHist t w, actionAt w t)) =
      (M.law.map (obsHist t)).compProd
        (Kernel.comap (actionKernel M) (fun h => h.2.2) (by fun_prop)) := by
  let f : PreHistory T nX nH k t → ObsHistory T nX k t :=
    fun h => (fun j => (h.1 j).1, h.2.1, h.2.2.1)
  have hf : Measurable f := by fun_prop
  have hobs : ∀ w : FullPath T nX nH k, f (preHist t w) = obsHist t w := by
    intro w
    rfl
  have hpre : Measurable (preHist t : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  have hact : Measurable (actionAt : FullPath T nX nH k → Fin T → Fin k) := by
    unfold actionAt
    fun_prop
  have hactt : Measurable (actionAt · t : FullPath T nX nH k → Fin k) := by
    unfold actionAt
    fun_prop
  have : IsMarkovKernel (actionKernel M) := by
    refine ⟨fun x => ⟨?_⟩⟩
    change (∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact (hA.1 x).1 a)]
    simp [(hA.1 x).2]
  have hk :
      Kernel.comap (actionKernel M) (fun h : PreHistory T nX nH k t => h.2.2.1)
        (by fun_prop) =
      (Kernel.comap (actionKernel M) (fun h : ObsHistory T nX k t => h.2.2)
        (by fun_prop)).comap f hf := by
    ext h s hs
    rfl
  rw [show M.law.map (fun w => (obsHist t w, actionAt w t)) =
      (M.law.map (fun w => (preHist t w, actionAt w t))).map
        (fun p => (f p.1, p.2)) from by
      rw [Measure.map_map (by fun_prop) (hpre.prodMk hactt)]
      congr 1]
  rw [hA.2 t, hk, compProd_map_comap_history _ _ f hf]
  congr 1
  rw [Measure.map_map hf hpre]
  congr 1

-- @node: lem:full-history-factorization
/-- Full-history kernel and randomization assumptions determine the stationary path law,
its observed projection, observed-history randomization, and the windowed likelihood
ratio integral identity for every measurable complete pre-action history event. -/
lemma full_history_factorization {T nX nH k : Nat} {zeta : ℝ} (M : PomdpModel T nX nH k)
    (hK : FullFiltrationPomdp M) (hA : FullFiltrationRandomization M)
    (hY : RewardMomentEnvelope M) (hOverlap : PolicyOverlap zeta M)
    (hStart : StationaryStart M) :
    M.law = generatedPathLaw M ∧
    (∀ t : Fin T, M.law.map (fun w => (obsHist t w, actionAt w t)) =
      (M.law.map (obsHist t)).compProd
        (Kernel.comap (actionKernel M) (fun h => h.2.2) (by fun_prop))) ∧
    (∀ (j t : Fin T), j.val ≤ t.val →
      ∀ B : Set (PreHistory T nX nH k j), MeasurableSet B →
        ∫ w in (preHist j) ⁻¹' B, windowScore M j t w ∂M.law =
        ∫ w in (preHist j) ⁻¹' B,
          ((targetStep M)^[t.val - j.val] (rewardRegression M)) (currentState w j)
          ∂M.law) := by
  refine ⟨?_, observed_history_randomization M hA, ?_⟩
  · have hLaw := full_history_generated_law M hK hA hStart
    have hGenerated : GeneratedPathLaw M (generatedPathLaw M) := by
      exact Classical.epsilon_spec (show ∃ μ, GeneratedPathLaw M μ from ⟨M.law, hLaw⟩)
    exact generated_path_law_unique M hLaw hGenerated
  · intro j t hjt B hB
    have hprej : Measurable (preHist j : FullPath T nX nH k → _) := by
      unfold preHist currentState pastIndex
      fun_prop
    have hset : MeasurableSet ((preHist j) ⁻¹' B) := hB.preimage hprej
    calc
      ∫ w in (preHist j) ⁻¹' B, windowScore M j t w ∂M.law =
          ∫ w, historyRatioCarrier M j t hjt B (preHist t w) *
            ratio M.b M.e (currentState w t).1 (actionAt w t) * rewardAt w t ∂M.law := by
        rw [← integral_indicator hset]
        apply integral_congr_ae
        filter_upwards with w
        rw [terminalCarrier_windowScore M j t hjt B w]
        rfl
      _ = ∫ w, historyRatioCarrier M j t hjt B (preHist t w) *
            rewardRegression M (currentState w t) ∂M.law :=
        terminalCarrier_peeling M hK hA hY hOverlap j t hjt B hB
      _ = ∫ w, historyRatioCarrier M j j le_rfl B (preHist j w) *
            ((targetStep M)^[t.val - j.val] (rewardRegression M))
              (currentState w j) ∂M.law :=
        continuationCarrier_iteration M hK hA hOverlap j B hB t.val hjt t.isLt
          (rewardRegression M)
      _ = ∫ w in (preHist j) ⁻¹' B,
            ((targetStep M)^[t.val - j.val] (rewardRegression M))
              (currentState w j) ∂M.law := by
        rw [← integral_indicator hset]
        apply integral_congr_ae
        filter_upwards with w
        rw [historyRatioCarrier_self]
        by_cases hw : preHist j w ∈ B <;> simp [Set.indicator, hw]

end CausalSmith.Stat.PomdpStateauditMinimax
