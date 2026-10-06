module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteHistoryFactorization

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Assuming [the hf condition](hyp:hf), [the hg condition](hyp:hg), [the hκ condition](hyp:hκ), [the map comp Prod of fiber assertion holds](goal). -/
lemma map_compProd_of_fiber
    {A A' B B' : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B']
    (ν : Measure A) [SFinite ν]
    (κ : Kernel A B) [IsSFiniteKernel κ]
    (κ' : Kernel A' B') [IsSFiniteKernel κ']
    (f : A → A') (hf : Measurable f) (g : B → B') (hg : Measurable g)
    (hκ : ∀ a, κ' (f a) = Measure.map g (κ a)) :
    (Measure.map f ν).compProd κ' =
      Measure.map (Prod.map f g) (ν.compProd κ) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf,
    Measure.map_apply (hf.prodMap hg) hs,
    Measure.compProd_apply (hs.preimage (hf.prodMap hg))]
  apply lintegral_congr
  intro a
  rw [hκ a, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

open scoped BigOperators ENNReal

/-- For [the h input](hyp:h), [the a input](hyp:a), [the r input](hyp:r), [this defines the finite History Observed Snoc object](goal). -/
def finiteHistoryObservedSnoc {k nX nH nR : Nat}
    (h : ((Fin k → JointState nX nH) × (Fin k → Bool × Fin nR)) ×
      JointState nX nH) (a : Bool) (r : Fin nR) :
    Fin (k + 1) → Bool × Fin nR :=
  Fin.lastCases (a, r) h.1.2

/-- For [the h input](hyp:h), [the s' input](hyp:s'), [this defines the finite History States Snoc object](goal). -/
def finiteHistoryStatesSnoc {k nX nH nR : Nat}
    (h : ((Fin k → JointState nX nH) × (Fin k → Bool × Fin nR)) ×
      JointState nX nH) (s' : JointState nX nH) :
    Fin (k + 2) → JointState nX nH :=
  Fin.lastCases s' (finiteHistoryStates h)

/-- [the finite Hist Next Pair mass to Real assertion holds](goal). -/
lemma finiteHistNextPair_mass_toReal {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T)
    (h : ((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH)
    (a : Bool) (r : Fin nR) (s' : JointState nX nH) :
    ((F.law.map (finiteHistNextPair t)) ((h, a), (r, s'))).toReal =
      finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
        h.1.2 (finiteHistoryStates h) *
        (F.b h.2.1 a).toReal * (F.kernel h.2 a (r, s')).toReal := by
  classical
  rcases t with ⟨k, hk⟩
  obtain ⟨U, hTU⟩ : ∃ U, T = (k + 1) + U := ⟨T - (k + 1), by omega⟩
  subst T
  obtain ⟨s, -⟩ := F.init.support_nonempty
  letI : NeZero nX := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt s.1.isLt)⟩
  letI : NeZero nH := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt s.2.isLt)⟩
  obtain ⟨q, -⟩ := (F.kernel s false).support_nonempty
  letI : NeZero nR := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt q.1.isLt)⟩
  have hlaw (tau : FiniteTrajectory ((k + 1) + U) nX nH nR) :
      (F.law tau).toReal =
        finitePathWeightFrom F.kernel (fun s ↦ (F.init s).toReal) F.b tau := by
    rw [F.law_generated tau, ENNReal.toReal_mul, ENNReal.toReal_prod]
    unfold finitePathWeightFrom
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [ENNReal.toReal_mul]
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero, hlaw]
    have hm := sum_finitePathWeightFrom_exactPrefix F.kernel F.b (k + 1)
      (fun s ↦ (F.init s).toReal) (finiteHistoryObservedSnoc h a r)
      (finiteHistoryStatesSnoc h s') U
    calc
      (∑ tau,
          if ((h, a), (r, s')) =
              finiteHistNextPair (⟨k, by omega⟩ : Fin ((k + 1) + U)) tau then
            finitePathWeightFrom F.kernel (fun s ↦ (F.init s).toReal) F.b tau
          else 0) =
          ∑ tau,
            if finiteObservedPrefixTrailing (k + 1) U tau =
                finiteHistoryObservedSnoc h a r ∧
              finiteStatePrefixTrailing (k + 1) U tau =
                finiteHistoryStatesSnoc h s' then
              finitePathWeightFrom F.kernel (fun s ↦ (F.init s).toReal) F.b tau
            else 0 := by
        apply Finset.sum_congr rfl
        intro tau _
        have heq : ((h, a), (r, s')) =
              finiteHistNextPair (⟨k, by omega⟩ : Fin ((k + 1) + U)) tau ↔
            finiteObservedPrefixTrailing (k + 1) U tau =
                finiteHistoryObservedSnoc h a r ∧
              finiteStatePrefixTrailing (k + 1) U tau =
                finiteHistoryStatesSnoc h s' := by
          constructor
          · intro hh
            have hhH : h = finiteHistStateView (⟨k, hk⟩ : Fin ((k + 1) + U)) tau :=
              congrArg (fun z ↦ z.1.1) hh
            have hhA : a = (tau.2 (⟨k, hk⟩ : Fin ((k + 1) + U))).1 :=
              congrArg (fun z ↦ z.1.2) hh
            have hhR : r = (tau.2 (⟨k, hk⟩ : Fin ((k + 1) + U))).2 :=
              congrArg (fun z ↦ z.2.1) hh
            have hhS : s' = tau.1 (⟨k + 1, by omega⟩ : Fin (((k + 1) + U) + 1)) :=
              congrArg (fun z ↦ z.2.2) hh
            rw [hhH, hhA, hhR, hhS]
            constructor <;> funext j
            · refine Fin.lastCases ?_ (fun i ↦ ?_) j
              · simp [finiteObservedPrefixTrailing, finiteHistoryObservedSnoc]
                congr 1
              · simp [finiteObservedPrefixTrailing, finiteHistoryObservedSnoc,
                  finiteHistStateView, prefixIndex]
                congr 1
            · refine Fin.lastCases ?_ (fun i ↦ ?_) j
              · simp [finiteStatePrefixTrailing, finiteHistoryStatesSnoc]
              · refine Fin.lastCases ?_ (fun i ↦ ?_) i
                · simp [finiteStatePrefixTrailing, finiteHistoryStatesSnoc,
                    finiteHistoryStates, finiteHistStateView]
                · simp [finiteStatePrefixTrailing, finiteHistoryStatesSnoc,
                    finiteHistoryStates, finiteHistStateView, prefixIndex]
          · rintro ⟨ho, hs⟩
            have hStates : h.1.1 = fun j ↦
                tau.1 (prefixIndex (⟨k, hk⟩ : Fin ((k + 1) + U)) j).castSucc := by
              funext j
              calc
                h.1.1 j = finiteHistoryStatesSnoc h s' j.castSucc.castSucc := by
                  simp [finiteHistoryStatesSnoc, finiteHistoryStates]
                _ = finiteStatePrefixTrailing (k + 1) U tau j.castSucc.castSucc :=
                  (congrFun hs j.castSucc.castSucc).symm
                _ = _ := by congr
            have hObs : h.1.2 = fun j ↦
                tau.2 (prefixIndex (⟨k, hk⟩ : Fin ((k + 1) + U)) j) := by
              funext j
              calc
                h.1.2 j = finiteHistoryObservedSnoc h a r j.castSucc := by
                  simp [finiteHistoryObservedSnoc]
                _ = finiteObservedPrefixTrailing (k + 1) U tau j.castSucc :=
                  (congrFun ho j.castSucc).symm
                _ = _ := by congr
            have hCur : h.2 = tau.1
                (⟨k, by omega⟩ : Fin ((k + 1) + U + 1)) := by
              calc
                h.2 = finiteHistoryStatesSnoc h s' (Fin.last k).castSucc := by
                  simp [finiteHistoryStatesSnoc, finiteHistoryStates]
                _ = finiteStatePrefixTrailing (k + 1) U tau (Fin.last k).castSucc :=
                  (congrFun hs (Fin.last k).castSucc).symm
                _ = _ := by congr
            have hAR : (a, r) = tau.2 (⟨k, by omega⟩ : Fin ((k + 1) + U)) := by
              calc
                (a, r) = finiteHistoryObservedSnoc h a r (Fin.last k) := by
                  simp [finiteHistoryObservedSnoc]
                _ = finiteObservedPrefixTrailing (k + 1) U tau (Fin.last k) :=
                  (congrFun ho (Fin.last k)).symm
                _ = _ := by congr
            have hNext : s' = tau.1 (⟨k + 1, by omega⟩ : Fin ((k + 1) + U + 1)) := by
              calc
                s' = finiteHistoryStatesSnoc h s' (Fin.last (k + 1)) := by
                  simp [finiteHistoryStatesSnoc]
                _ = finiteStatePrefixTrailing (k + 1) U tau (Fin.last (k + 1)) :=
                  (congrFun hs (Fin.last (k + 1))).symm
                _ = _ := by congr
            have hH : h = finiteHistStateView
                (⟨k, by omega⟩ : Fin ((k + 1) + U)) tau := by
              apply Prod.ext
              · exact Prod.ext hStates hObs
              · exact hCur
            have hA : a = (tau.2 (⟨k, hk⟩ : Fin ((k + 1) + U))).1 :=
              congrArg Prod.fst hAR
            have hR : r = (tau.2 (⟨k, hk⟩ : Fin ((k + 1) + U))).2 :=
              congrArg Prod.snd hAR
            rw [hH, hA, hR, hNext]
            simp [finiteHistNextPair, finiteHistActionPair]
        by_cases hx : ((h, a), (r, s')) =
            finiteHistNextPair (⟨k, by omega⟩ : Fin ((k + 1) + U)) tau
        · simp [hx, heq.mp hx]
        · rw [if_neg hx, if_neg (fun hp ↦ hx (heq.mpr hp))]
      _ = finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
          (finiteHistoryObservedSnoc h a r) (finiteHistoryStatesSnoc h s') := hm
      _ = _ := by
        have hcast (i : Fin (k + 1)) :
            finiteHistoryStatesSnoc h s' i.castSucc = finiteHistoryStates h i := by
          simp [finiteHistoryStatesSnoc]
        have hzero : finiteHistoryStatesSnoc h s' 0 = finiteHistoryStates h 0 := by
          rw [show (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc by
            apply Fin.ext; rfl]
          exact hcast 0
        have hnext (j : Fin k) : finiteHistoryStatesSnoc h s' j.castSucc.succ =
            finiteHistoryStates h j.succ := by
          rw [show (j.castSucc.succ : Fin (k + 2)) =
              (j.succ : Fin (k + 1)).castSucc by apply Fin.ext; rfl]
          exact hcast j.succ
        have hlast : finiteHistoryStates h (Fin.last k) = h.2 := by
          simp [finiteHistoryStates]
        unfold finiteFixedPrefixWeight
        rw [Fin.prod_univ_castSucc, hzero]
        simp_rw [hnext]
        simp [finiteHistoryObservedSnoc, finiteHistoryStatesSnoc, hlast]
        ring
  · intro tau _
    by_cases hh : ((h, a), (r, s')) =
        finiteHistNextPair (⟨k, by omega⟩ : Fin ((k + 1) + U)) tau
    · simpa [hh] using F.law.apply_ne_top tau
    · simp [hh]

/-- [the finite Hist Action Pair mass to Real assertion holds](goal). -/
lemma finiteHistActionPair_mass_toReal {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T)
    (h : ((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH)
    (a : Bool) :
    ((F.law.map (finiteHistActionPair t)) (h, a)).toReal =
      finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
        h.1.2 (finiteHistoryStates h) * (F.b h.2.1 a).toReal := by
  classical
  let pn := F.law.map (finiteHistNextPair t)
  have hmap : pn.map Prod.fst =
      F.law.map (finiteHistActionPair t) := by
    rw [show pn = F.law.map (finiteHistNextPair t) by rfl, PMF.map_comp]
    congr 1
  rw [← hmap, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have hselect (q : Fin nR × JointState nX nH) :
        (∑ x, @ite ℝ ((h, a) = (x, q).1) (Classical.propDecidable _)
          (pn (x, q)).toReal 0) =
          (pn ((h, a), q)).toReal := by
      let f := fun x ↦ @ite ℝ ((h, a) = (x, q).1) (Classical.propDecidable _)
        (pn (x, q)).toReal 0
      have hs : (∑ x ∈ Finset.univ, f x) = f (h, a) := by
        apply Finset.sum_eq_single (h, a)
        · intro x _ hne
          have hx : (h, a) ≠ (x, q).1 := by simpa using Ne.symm hne
          simp [f, hx]
        · simp
      simpa [f] using hs
    have houter : (∑ q, ∑ x,
        @ite ℝ ((h, a) = (x, q).1) (Classical.propDecidable _)
          (pn (x, q)).toReal 0) =
        ∑ q, (pn ((h, a), q)).toReal := by
      apply Finset.sum_congr rfl
      intro q _
      exact hselect q
    rw [houter]
    change (∑ q,
      ((F.law.map (finiteHistNextPair t)) ((h, a), q)).toReal) = _
    rw [Fintype.sum_prod_type]
    simp_rw [finiteHistNextPair_mass_toReal]
    let c := finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
      h.1.2 (finiteHistoryStates h) * (F.b h.2.1 a).toReal
    change (∑ r, ∑ s', c * (F.kernel h.2 a (r, s')).toReal) = c
    calc
      _ = c * (∑ r, ∑ s', (F.kernel h.2 a (r, s')).toReal) := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = c := by
        rw [show (∑ r, ∑ s', (F.kernel h.2 a (r, s')).toReal) = 1 by
          simpa only [Fintype.sum_prod_type] using
            sum_pmf_toReal_eq_one (F.kernel h.2 a), mul_one]
  · intro q _
    by_cases hq : (h, a) = q.1
    · simpa [pn, hq] using pn.apply_ne_top q
    · simp [hq]

/-- For [the F input](hyp:F), [the t input](hyp:t), [this defines the finite Behaviour Kernel object](goal). -/
noncomputable def finiteBehaviourKernel {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    Kernel (((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH) Bool :=
  Kernel.ofFunOfCountable fun h ↦ (F.b h.2.1).toMeasure

/-- For [the F input](hyp:F), [the t input](hyp:t), [this defines the finite Reward Transition Kernel object](goal). -/
noncomputable def finiteRewardTransitionKernel {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    Kernel ((((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH) × Bool)
      (Fin nR × JointState nX nH) :=
  Kernel.ofFunOfCountable fun h ↦ (F.kernel h.1.2 h.2).toMeasure

/-- [the finite action factorization assertion holds](goal). -/
lemma finite_action_factorization {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    (F.law.map (finiteHistActionPair t)).toMeasure =
      (F.law.map (finiteHistStateView t)).toMeasure.compProd
        (finiteBehaviourKernel F t) := by
  letI : IsMarkovKernel (finiteBehaviourKernel F t) :=
    ⟨fun h ↦ by change IsProbabilityMeasure (F.b h.2.1).toMeasure; infer_instance⟩
  apply Measure.ext_of_singleton
  rintro ⟨h, a⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [show ({(h, a)} : Set (_ × Bool)) = {h} ×ˢ {a} by simp,
    Measure.compProd_apply_prod (measurableSet_singleton h) (measurableSet_singleton a),
    lintegral_singleton]
  have hk : finiteBehaviourKernel F t h = (F.b h.2.1).toMeasure := rfl
  rw [hk, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change F.law.map (finiteHistActionPair t) (h, a) =
    F.b h.2.1 a * F.law.map (finiteHistStateView t) h
  apply (ENNReal.toReal_eq_toReal_iff'
    ((F.law.map (finiteHistActionPair t)).apply_ne_top (h, a))
    (ENNReal.mul_ne_top ((F.b h.2.1).apply_ne_top a)
      ((F.law.map (finiteHistStateView t)).apply_ne_top h))).mp
  rw [finiteHistActionPair_mass_toReal, ENNReal.toReal_mul,
    finiteHistStateView_mass_toReal, mul_comm]

/-- [the finite next factorization assertion holds](goal). -/
lemma finite_next_factorization {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    (F.law.map (finiteHistNextPair t)).toMeasure =
      (F.law.map (finiteHistActionPair t)).toMeasure.compProd
        (finiteRewardTransitionKernel F t) := by
  letI : IsMarkovKernel (finiteRewardTransitionKernel F t) :=
    ⟨fun h ↦ by change IsProbabilityMeasure (F.kernel h.1.2 h.2).toMeasure; infer_instance⟩
  apply Measure.ext_of_singleton
  rintro ⟨ha, q⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [show ({(ha, q)} : Set (_ × (Fin nR × JointState nX nH))) =
      {ha} ×ˢ {q} by simp,
    Measure.compProd_apply_prod (measurableSet_singleton ha) (measurableSet_singleton q),
    lintegral_singleton]
  have hk : finiteRewardTransitionKernel F t ha = (F.kernel ha.1.2 ha.2).toMeasure := rfl
  rw [hk, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change F.law.map (finiteHistNextPair t) (ha, q) =
    F.kernel ha.1.2 ha.2 q * F.law.map (finiteHistActionPair t) ha
  apply (ENNReal.toReal_eq_toReal_iff'
    ((F.law.map (finiteHistNextPair t)).apply_ne_top (ha, q))
    (ENNReal.mul_ne_top ((F.kernel ha.1.2 ha.2).apply_ne_top q)
      ((F.law.map (finiteHistActionPair t)).apply_ne_top ha))).mp
  rcases ha with ⟨h, a⟩
  rcases q with ⟨r, s'⟩
  rw [finiteHistNextPair_mass_toReal, ENNReal.toReal_mul,
    finiteHistActionPair_mass_toReal]
  ring

/-- For [the t input](hyp:t), [the rew input](hyp:rew), [the h input](hyp:h), [this defines the decode Finite State History object](goal). -/
def decodeFiniteStateHistory {T nX nH nR : Nat} (t : Fin T) (rew : Fin nR → ℝ)
    (h : ((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH) :
    StateHistoryView T nX nH t :=
  ((h.1.1, fun j ↦ ((h.1.2 j).1, rew (h.1.2 j).2)), h.2)

/-- For [the t input](hyp:t), [the rew input](hyp:rew), [the h input](hyp:h), [this defines the decode Finite Action History object](goal). -/
def decodeFiniteActionHistory {T nX nH nR : Nat} (t : Fin T) (rew : Fin nR → ℝ)
    (h : (((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH) × Bool) :
    ActionHistoryView T nX nH t :=
  (decodeFiniteStateHistory t rew h.1, h.2)

/-- For [the rew input](hyp:rew), [the q input](hyp:q), [this defines the decode Finite Step object](goal). -/
def decodeFiniteStep {nX nH nR : Nat} (rew : Fin nR → ℝ)
    (q : Fin nR × JointState nX nH) : Step nX nH :=
  (rew q.1, q.2)

/-- [the behaviour Kernel embed apply assertion holds](goal). -/
lemma behaviourKernel_embed_apply {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (x : Fin nX) :
    behaviourKernel (embed F) x = (F.b x).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  change (∑ z : Bool, ENNReal.ofReal ((F.b x z).toReal) • Measure.dirac z) {a} =
    (F.b x).toMeasure {a}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  fin_cases a <;> simp [ENNReal.ofReal_toReal, PMF.apply_ne_top]

/-- [the real Kernel embed apply assertion holds](goal). -/
lemma realKernel_embed_apply {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (s : JointState nX nH) (a : Bool) :
    kernelOfK (embed F) (s, a) =
      Measure.map (decodeFiniteStep F.rew) (F.kernel s a).toMeasure := by
  change ((F.kernel s a).map (decodeFiniteStep F.rew)).toMeasure = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]

/-- [the law map state decode assertion holds](goal). -/
lemma law_map_state_decode {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    (embed F).law.map (histStateView t) =
      Measure.map (decodeFiniteStateHistory t F.rew)
        (F.law.map (finiteHistStateView t)).toMeasure := by
  have hm : Measurable (@histStateView T nX nH t) := by
    unfold histStateView curState
    measurability
  change Measure.map (histStateView t) ((F.law.map (decodeTraj F.rew)).toMeasure) = _
  rw [← PMF.toMeasure_map (decodeTraj F.rew) F.law (measurable_of_finite _),
    Measure.map_map hm (measurable_of_finite _),
    ← PMF.toMeasure_map (finiteHistStateView t) F.law (measurable_of_finite _),
    Measure.map_map (by measurability) (measurable_of_finite _)]
  congr 1

/-- [the law map action decode assertion holds](goal). -/
lemma law_map_action_decode {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    (embed F).law.map (histActionPair t) =
      Measure.map (decodeFiniteActionHistory t F.rew)
        (F.law.map (finiteHistActionPair t)).toMeasure := by
  have hm : Measurable (@histActionPair T nX nH t) := by
    unfold histActionPair histStateView curState actionAt
    measurability
  change Measure.map (histActionPair t) ((F.law.map (decodeTraj F.rew)).toMeasure) = _
  rw [← PMF.toMeasure_map (decodeTraj F.rew) F.law (measurable_of_finite _),
    Measure.map_map hm (measurable_of_finite _),
    ← PMF.toMeasure_map (finiteHistActionPair t) F.law (measurable_of_finite _),
    Measure.map_map (by measurability) (measurable_of_finite _)]
  congr 1

/-- [the law map next decode assertion holds](goal). -/
lemma law_map_next_decode {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T) :
    (embed F).law.map (histNextPair t) =
      Measure.map (Prod.map (decodeFiniteActionHistory t F.rew)
        (decodeFiniteStep F.rew))
        (F.law.map (finiteHistNextPair t)).toMeasure := by
  have hm : Measurable (@histNextPair T nX nH t) := by
    unfold histNextPair histView histActionPair histStateView curState actionAt rewardAt nextState
    measurability
  change Measure.map (histNextPair t) ((F.law.map (decodeTraj F.rew)).toMeasure) = _
  rw [← PMF.toMeasure_map (decodeTraj F.rew) F.law (measurable_of_finite _),
    Measure.map_map hm (measurable_of_finite _),
    ← PMF.toMeasure_map (finiteHistNextPair t) F.law (measurable_of_finite _),
    Measure.map_map (by measurability) (measurable_of_finite _)]
  congr 1


end CausalSmith.Stat.PomdpLatentOverlapMinimax
