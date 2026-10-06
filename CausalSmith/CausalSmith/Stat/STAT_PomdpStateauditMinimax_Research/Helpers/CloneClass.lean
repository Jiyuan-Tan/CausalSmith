module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.ClonePreservation

/-! # Class membership of fixed-permutation clones. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

-- @node: clone_map_compProd_dependent
lemma map_compProd_dependent
    {A A' B B' : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B']
    (ν : Measure A) [SFinite ν]
    (κ : Kernel A B) [IsSFiniteKernel κ]
    (κ' : Kernel A' B') [IsSFiniteKernel κ']
    (f : A → A') (hf : Measurable f)
    (g : A → B → B') (hg : Measurable (fun q : A × B => g q.1 q.2))
    (hκ : ∀ a, κ' (f a) = Measure.map (g a) (κ a)) :
    (ν.compProd κ).map (fun q => (f q.1, g q.1 q.2)) =
      (ν.map f).compProd κ' := by
  have hfg : Measurable (fun q : A × B => (f q.1, g q.1 q.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hfg hs,
    Measure.compProd_apply (hs.preimage hfg),
    Measure.compProd_apply hs,
    MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  rw [hκ a, Measure.map_apply]
  · rfl
  · exact hg.comp measurable_prodMk_left
  · exact measurable_prodMk_left hs

-- @node: clone_compProd_prod_reassoc
lemma compProd_prod_reassoc
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ν : Measure A) [SFinite ν] (κ : Kernel A B) [IsSFiniteKernel κ]
    (ρ : Measure C) [SFinite ρ] :
    ((ν.compProd κ).prod ρ).map (fun q => ((q.1.1, q.2), q.1.2)) =
      (ν.prod ρ).compProd (Kernel.comap κ Prod.fst measurable_fst) := by
  let η : Kernel (A × B) C := Kernel.const (A × B) ρ
  let θ : Kernel A C := Kernel.const A ρ
  let κ' : Kernel (A × C) B := Kernel.comap κ Prod.fst measurable_fst
  have hker : (κ.compProd η).map Prod.swap = θ.compProd κ' := by
    ext a s hs
    rw [Kernel.map_apply _ measurable_swap]
    have hleft : (κ.compProd η) a = (κ a).prod ρ := by
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.prod_apply hs]
      rfl
    have hright : (θ.compProd κ') a = ρ.prod (κ a) := by
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.prod_apply hs]
      rfl
    rw [hleft, hright]
    exact congrArg (fun μ : Measure (C × B) => μ s) Measure.prod_swap
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  change ((ν.compProd κ).compProd η).map _ = (ν.compProd θ).compProd κ'
  calc
    ((ν.compProd κ).compProd η).map (fun q => ((q.1.1, q.2), q.1.2)) =
        ((((ν.compProd κ).compProd η).map MeasurableEquiv.prodAssoc).map
          (Prod.map id Prod.swap)).map MeasurableEquiv.prodAssoc.symm := by
            symm
            rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
              (measurable_id.prodMap measurable_swap),
              Measure.map_map
                (MeasurableEquiv.prodAssoc.symm.measurable.comp
                  (measurable_id.prodMap measurable_swap))
                MeasurableEquiv.prodAssoc.measurable]
            rfl
    _ = ((ν.compProd (κ.compProd η)).map (Prod.map id Prod.swap)).map
          MeasurableEquiv.prodAssoc.symm := by rw [Measure.compProd_assoc']
    _ = (ν.compProd ((κ.compProd η).map Prod.swap)).map
          MeasurableEquiv.prodAssoc.symm := by
            rw [Measure.compProd_map (μ := ν) (κ := κ.compProd η)
              (f := Prod.swap) measurable_swap]
    _ = (ν.compProd (θ.compProd κ')).map MeasurableEquiv.prodAssoc.symm := by rw [hker]
    _ = (ν.compProd θ).compProd κ' := Measure.compProd_assoc

-- @node: clone_map_prod_of_compProd_dependent
lemma map_prod_of_compProd_dependent
    {W A A' B B' C : Type*} [MeasurableSpace W] [MeasurableSpace A]
    [MeasurableSpace A'] [MeasurableSpace B] [MeasurableSpace B'] [MeasurableSpace C]
    (μ : Measure W) [SFinite μ] (ρ : Measure C) [SFinite ρ]
    (a : W → A) (ha : Measurable a) (b : W → B) (hb : Measurable b)
    (κ : Kernel A B) [IsSFiniteKernel κ]
    (hfac : μ.map (fun w => (a w, b w)) = (μ.map a).compProd κ)
    (κ' : Kernel A' B') [IsSFiniteKernel κ']
    (f : A × C → A') (hf : Measurable f)
    (g : A × C → B → B') (hg : Measurable (fun q : (A × C) × B => g q.1 q.2))
    (hκ : ∀ ac, κ' (f ac) = Measure.map (g ac) (κ ac.1)) :
    (μ.prod ρ).map (fun q : W × C =>
      (f (a q.1, q.2), g (a q.1, q.2) (b q.1))) =
      (((μ.map a).prod ρ).map f).compProd κ' := by
  have hj : Measurable (fun w : W => (a w, b w)) := ha.prodMk hb
  have hsource : (μ.prod ρ).map (fun q : W × C => ((a q.1, b q.1), q.2)) =
      (μ.map (fun w => (a w, b w))).prod ρ := by
    change (μ.prod ρ).map (Prod.map (fun w => (a w, b w)) id) = _
    rw [← Measure.map_prod_map μ ρ hj measurable_id, Measure.map_id]
  let baseκ : Kernel (A × C) B := Kernel.comap κ Prod.fst measurable_fst
  have hdep := map_compProd_dependent ((μ.map a).prod ρ) baseκ κ'
    f hf g hg (by
      intro ac
      simpa only [baseκ, Kernel.comap_apply] using hκ ac)
  rw [← hdep]
  have hre := compProd_prod_reassoc (μ.map a) κ ρ
  rw [← hre, ← hfac, ← hsource]
  have hR : Measurable (fun q : (A × B) × C => ((q.1.1, q.2), q.1.2)) := by
    fun_prop
  have hFG : Measurable (fun q : (A × C) × B => (f q.1, g q.1 q.2)) :=
    (hf.comp measurable_fst).prodMk hg
  have hJ : Measurable (fun q : W × C => ((a q.1, b q.1), q.2)) := by
    fun_prop
  rw [Measure.map_map hFG hR, Measure.map_map (hFG.comp hR) hJ]
  rfl

-- @node: clone_map_prod_of_compProd_output
lemma map_prod_of_compProd_output
    {W A A' B B' C : Type*} [MeasurableSpace W] [MeasurableSpace A]
    [MeasurableSpace A'] [MeasurableSpace B] [MeasurableSpace B'] [MeasurableSpace C]
    (μ : Measure W) [SFinite μ] (ρ : Measure C) [SFinite ρ]
    (a : W → A) (ha : Measurable a) (b : W → B) (hb : Measurable b)
    (κ : Kernel A B) [IsSFiniteKernel κ]
    (hfac : μ.map (fun w => (a w, b w)) = (μ.map a).compProd κ)
    (κ' : Kernel A' B') [IsSFiniteKernel κ']
    (f : A → A') (hf : Measurable f)
    (g : A → B × C → B') (hg : Measurable (fun q : A × (B × C) => g q.1 q.2))
    (hκ : ∀ x, κ' (f x) = Measure.map (g x) ((κ x).prod ρ)) :
    (μ.prod ρ).map (fun q : W × C => (f (a q.1), g (a q.1) (b q.1, q.2))) =
      ((μ.map a).map f).compProd κ' := by
  have hj : Measurable (fun w : W => (a w, b w)) := ha.prodMk hb
  have hsource : (μ.prod ρ).map (fun q : W × C => ((a q.1, b q.1), q.2)) =
      (μ.map (fun w => (a w, b w))).prod ρ := by
    change (μ.prod ρ).map (Prod.map (fun w => (a w, b w)) id) = _
    rw [← Measure.map_prod_map μ ρ hj measurable_id, Measure.map_id]
  let η : Kernel (A × B) C := Kernel.const (A × B) ρ
  have hassoc : (((μ.map a).compProd κ).prod ρ).map
      (fun q => (q.1.1, (q.1.2, q.2))) =
      (μ.map a).compProd (κ.compProd η) := by
    rw [← Measure.compProd_const]
    exact Measure.compProd_assoc'
  let κout := κ.compProd η
  have hdep := map_compProd_dependent (μ.map a) κout κ' f hf g hg (by
    intro x
    have hout : κout x = (κ x).prod ρ := by
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.prod_apply hs]
      rfl
    rw [hout]
    exact hκ x)
  rw [← hdep, ← hassoc, ← hfac, ← hsource]
  have hA : Measurable (fun q : (A × B) × C => (q.1.1, (q.1.2, q.2))) := by fun_prop
  have hFG : Measurable (fun q : A × (B × C) => (f q.1, g q.1 q.2)) :=
    (hf.comp measurable_fst).prodMk hg
  have hJ : Measurable (fun q : W × C => ((a q.1, b q.1), q.2)) := by fun_prop
  rw [Measure.map_map hFG hA, Measure.map_map (hFG.comp hA) hJ]
  rfl

-- @node: clonePreHist
@[no_expose]
def clonePreHist {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (t : Fin T) (h : PreHistory T 1 n k t) (c : Fin (T + 1) → Fin m) :
    PreHistory T 1 (n * m) k t :=
  (fun j => ((h.1 j).1, π ((h.1 j).2, c (pastIndex t j).castSucc)), h.2.1,
    ((h.2.2).1, π ((h.2.2).2, c t.castSucc)))

-- @node: clonePostHist
@[no_expose]
def clonePostHist {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (t : Fin T) (h : PostHistory T 1 n k t) (c : Fin (T + 1) → Fin m) :
    PostHistory T 1 (n * m) k t := (clonePreHist π t h.1 c, h.2)

-- @node: clonePostRest
@[no_expose]
def clonePostRest {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (i0 : Fin m) (t : Fin T) (h : PostHistory T 1 n k t) (r : Fin T → Fin m) :
    PostHistory T 1 (n * m) k t :=
  clonePostHist π t h
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ).symm (i0, r))

-- @node: clonePath_preHist
lemma clonePath_preHist {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (t : Fin T) (w : FullPath T 1 n k) (c : Fin (T + 1) → Fin m) :
    preHist t (clonePath π w c) = clonePreHist π t (preHist t w) c := by rfl

-- @node: clonePath_postHist
lemma clonePath_postHist {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (t : Fin T) (w : FullPath T 1 n k) (c : Fin (T + 1) → Fin m) :
    postHist t (clonePath π w c) = clonePostHist π t (postHist t w) c := by rfl

-- @node: clonePostHist_split
lemma clonePostHist_split {T n k m : Nat} (π : Fin n × Fin m ≃ Fin (n * m))
    (i0 : Fin m) (t : Fin T) (h : PostHistory T 1 n k t)
    (c : Fin (T + 1) → Fin m) :
    clonePostHist π t h c = clonePostRest π i0 t h
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ c).2 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ
  have hcoord (j : Fin (T + 1)) (hj : j ≠ t.succ) :
      e.symm (i0, (e c).2) j = c j := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth, Function.update, hj]
  unfold clonePostRest clonePostHist clonePreHist
  symm
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change ((h.1.1 j).1, π ((h.1.1 j).2,
          e.symm (i0, (e c).2) (pastIndex t j).castSucc)) =
        ((h.1.1 j).1, π ((h.1.1 j).2, c (pastIndex t j).castSucc))
      rw [hcoord]
      intro heq
      have hv := congrArg Fin.val heq
      simp [pastIndex] at hv
      omega
    · apply Prod.ext
      · rfl
      · change ((h.1.2.2).1, π ((h.1.2.2).2,
          e.symm (i0, (e c).2) t.castSucc)) =
        ((h.1.2.2).1, π ((h.1.2.2).2, c t.castSucc))
        rw [hcoord]
        exact Fin.ne_of_val_ne (by simp)
  · rfl

-- @node: uniformFin_pi_rebuild
lemma uniformFin_pi_rebuild {T m : Nat} (hm : 1 ≤ m) (t : Fin T) :
    ((Measure.pi (fun _ : Fin T => uniformFin m)).prod (uniformFin m)).map
        (fun q =>
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ).symm
            (q.2, q.1)) =
      Measure.pi (fun _ : Fin (T + 1) => uniformFin m) := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (T + 1) => uniformFin m) t.succ).symm.map_eq
  calc
    _ = (((Measure.pi (fun _ : Fin T => uniformFin m)).prod (uniformFin m)).map
        Prod.swap).map e.symm := by
          rw [Measure.map_map e.symm.measurable measurable_swap]
          rfl
    _ = ((uniformFin m).prod (Measure.pi (fun _ : Fin T => uniformFin m))).map
        e.symm := by rw [Measure.prod_swap]
    _ = _ := he

-- @node: cloneKernel_eq_map_prod_uniform
lemma cloneKernel_eq_map_prod_uniform {T n k m : Nat}
    (M : PomdpModel T 1 n k) (π : Fin n × Fin m ≃ Fin (n * m))
    (s : JointState 1 (n * m)) (a : Fin k)
    (hK : IsProbabilityMeasure (M.K (s.1, (π.symm s.2).1) a)) :
    ((M.K (s.1, (π.symm s.2).1) a).prod (uniformFin m)).map
        (fun q => (q.1.1, (q.1.2.1, π (q.1.2.2, q.2)))) =
      cloneKernel M π s a := by
  letI : IsProbabilityMeasure (M.K (s.1, (π.symm s.2).1) a) := hK
  let μ := M.K (s.1, (π.symm s.2).1) a
  let F : (ℝ × JointState 1 n) × Fin m → ℝ × JointState 1 (n * m) :=
    fun q => (q.1.1, (q.1.2.1, π (q.1.2.2, q.2)))
  have hF : Measurable F := by unfold F; fun_prop
  have hsum (u : Finset (Fin m)) :
      (μ.prod (∑ i ∈ u, ENNReal.ofReal (1 / (m : ℝ)) • Measure.dirac i)).map F =
        ∑ i ∈ u, ENNReal.ofReal (1 / (m : ℝ)) •
          μ.map (fun q => (q.1, (q.2.1, π (q.2.2, i)))) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.prod_add,
          Measure.map_add _ _ hF, ih, Measure.prod_smul_right, Measure.map_smul,
          Measure.prod_dirac, Measure.map_map (by unfold F; fun_prop) (by fun_prop)]
        rfl
  simpa only [uniformFin, cloneKernel, μ, F] using hsum Finset.univ

-- @node: prod_pi_rebuild
lemma prod_pi_rebuild {W : Type*} [MeasurableSpace W] (μ : Measure W) [SFinite μ]
    {T m : Nat} (hm : 1 ≤ m) (t : Fin T) :
    (((μ.prod (Measure.pi (fun _ : Fin T => uniformFin m))).prod (uniformFin m)).map
      (fun q => (q.1.1,
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ).symm
          (q.2, q.1.2)))) =
      μ.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m)) := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  let ρ := Measure.pi (fun _ : Fin T => uniformFin m)
  let u := uniformFin m
  let rebuild : (Fin T → Fin m) × Fin m → (Fin (T + 1) → Fin m) := fun q =>
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ).symm
      (q.2, q.1)
  have hr : (ρ.prod u).map rebuild = Measure.pi (fun _ : Fin (T + 1) => uniformFin m) :=
    uniformFin_pi_rebuild hm t
  calc
    _ = (((μ.prod ρ).prod u).map MeasurableEquiv.prodAssoc).map
        (Prod.map id rebuild) := by
          rw [Measure.map_map (measurable_id.prodMap (by unfold rebuild; fun_prop))
            MeasurableEquiv.prodAssoc.measurable]
          rfl
    _ = (μ.prod (ρ.prod u)).map (Prod.map id rebuild) := by
      rw [Measure.prodAssoc_prod]
    _ = (μ.map id).prod ((ρ.prod u).map rebuild) := by
      rw [Measure.map_prod_map μ (ρ.prod u) measurable_id (by unfold rebuild; fun_prop)]
    _ = _ := by rw [Measure.map_id, hr]

-- @node: clone_fullFiltrationPomdp
lemma clone_fullFiltrationPomdp {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (hK : FullFiltrationPomdp M) :
    FullFiltrationPomdp (cloneModel M hm π) := by
  constructor
  · exact clone_kernel_probability M hm π hK
  intro t
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  letI : IsMarkovKernel (kernelOfK (cloneModel M hm π)) :=
    ⟨fun sa => clone_kernel_probability M hm π hK sa.1 sa.2⟩
  let ρ := Measure.pi (fun _ : Fin T => uniformFin m)
  let u := uniformFin m
  let i0 : Fin m := ⟨0, hm⟩
  let draw := fun w : FullPath T 1 n k => (rewardAt w t, nextState w t)
  let κ := Kernel.comap (kernelOfK M)
    (fun h : PostHistory T 1 n k t => (h.1.2.2, h.2)) (by fun_prop)
  let κr : Kernel (PostHistory T 1 n k t × (Fin T → Fin m))
      (ℝ × JointState 1 n) := Kernel.comap κ Prod.fst measurable_fst
  let κ' := Kernel.comap (kernelOfK (cloneModel M hm π))
    (fun h : PostHistory T 1 (n * m) k t => (h.1.2.2, h.2)) (by fun_prop)
  have hrest := map_prod_of_compProd_dependent M.law ρ
    (postHist t) (by unfold postHist preHist currentState pastIndex actionAt; fun_prop)
    draw (by unfold draw rewardAt nextState; fun_prop) κ (hK.2 t) κr
    (fun hr => (hr.1, hr.2)) (by fun_prop) (fun _ q => q) (by fun_prop) (by
      intro hr
      unfold κ κr
      rw [Kernel.comap_apply, Kernel.comap_apply]
      change (kernelOfK M) _ = Measure.map id ((kernelOfK M) _)
      rw [Measure.map_id])
  have hmarg :
      (M.law.prod ρ).map (fun wr => (postHist t wr.1, wr.2)) =
        ((M.law.map (postHist t)).prod ρ) := by
    change (M.law.prod ρ).map (Prod.map (postHist t) id) = _
    rw [← Measure.map_prod_map M.law ρ
      (by unfold postHist preHist currentState pastIndex actionAt; fun_prop) measurable_id,
      Measure.map_id]
  have hrest' :
      (M.law.prod ρ).map
          (fun wr => ((postHist t wr.1, wr.2), draw wr.1)) =
        ((M.law.prod ρ).map (fun wr => (postHist t wr.1, wr.2))).compProd κr := by
    rw [hmarg]
    simpa using hrest
  have hout := map_prod_of_compProd_output (M.law.prod ρ) u
    (fun wr => (postHist t wr.1, wr.2)) (by
      unfold postHist preHist currentState pastIndex actionAt
      fun_prop)
    (fun wr => draw wr.1) (by unfold draw rewardAt nextState; fun_prop)
    κr hrest' κ'
    (fun hr => clonePostRest π i0 t hr.1 hr.2) (by
      unfold clonePostRest clonePostHist clonePreHist
      fun_prop)
    (fun _ qi => (qi.1.1, (qi.1.2.1, π (qi.1.2.2, qi.2)))) (by fun_prop) (by
      intro hr
      unfold κ' κr κ
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply]
      change cloneKernel M π (clonePostRest π i0 t hr.1 hr.2).1.2.2 hr.1.2 = _
      have hs : (clonePostRest π i0 t hr.1 hr.2).1.2.2 =
          ((hr.1.1.2.2).1, π ((hr.1.1.2.2).2,
            ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (T + 1) => Fin m) t.succ).symm (i0, hr.2)) t.castSucc)) := rfl
      rw [hs]
      change cloneKernel M π _ hr.1.2 =
        Measure.map (fun qi => (qi.1.1, (qi.1.2.1, π (qi.1.2.2, qi.2))))
          ((M.K hr.1.1.2.2 hr.1.2).prod (uniformFin m))
      let sc : JointState 1 (n * m) :=
        ((hr.1.1.2.2).1, π ((hr.1.1.2.2).2,
          ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (T + 1) => Fin m) t.succ).symm (i0, hr.2)) t.castSucc))
      have hfiber := cloneKernel_eq_map_prod_uniform M π sc hr.1.2
        (hK.1 (sc.1, (π.symm sc.2).1) hr.1.2)
      simpa only [sc, π.symm_apply_apply] using hfiber.symm)
  let rebuild : (Fin T → Fin m) × Fin m → (Fin (T + 1) → Fin m) := fun q =>
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Fin m) t.succ).symm
      (q.2, q.1)
  have hsrc := prod_pi_rebuild M.law hm t
  change (clonePathLaw M π).map
      (fun w => (postHist t w, (rewardAt w t, nextState w t))) =
    ((clonePathLaw M π).map (postHist t)).compProd κ'
  unfold clonePathLaw
  rw [Measure.map_map (by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop) (by unfold clonePath; fun_prop)]
  rw [Measure.map_map (by unfold postHist preHist currentState pastIndex actionAt; fun_prop)
    (by unfold clonePath; fun_prop)]
  rw [← hsrc]
  rw [Measure.map_map (by
      unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
      fun_prop) (by fun_prop),
    Measure.map_map (by unfold postHist preHist currentState pastIndex actionAt; fun_prop)
      (by fun_prop)]
  have hj : (fun q : (FullPath T 1 n k × (Fin T → Fin m)) × Fin m =>
      ((postHist t (clonePath π q.1.1 (rebuild (q.1.2, q.2))),
        (rewardAt (clonePath π q.1.1 (rebuild (q.1.2, q.2))) t,
          nextState (clonePath π q.1.1 (rebuild (q.1.2, q.2))) t)))) =
      fun q => (clonePostRest π i0 t (postHist t q.1.1) q.1.2,
        (rewardAt q.1.1 t,
          ((nextState q.1.1 t).1, π ((nextState q.1.1 t).2, q.2)))) := by
    funext q
    rw [clonePath_postHist, clonePostHist_split π i0]
    dsimp only [rebuild]
    simp only [MeasurableEquiv.apply_symm_apply]
    unfold rewardAt nextState clonePath
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hp : (fun q : (FullPath T 1 n k × (Fin T → Fin m)) × Fin m =>
      postHist t (clonePath π q.1.1 (rebuild (q.1.2, q.2)))) =
      fun q => clonePostRest π i0 t (postHist t q.1.1) q.1.2 := by
    funext q
    rw [clonePath_postHist, clonePostHist_split π i0]
    dsimp only [rebuild]
    simp only [MeasurableEquiv.apply_symm_apply]
  change Measure.map (fun q : (FullPath T 1 n k × (Fin T → Fin m)) × Fin m =>
      (postHist t (clonePath π q.1.1 (rebuild (q.1.2, q.2))),
        (rewardAt (clonePath π q.1.1 (rebuild (q.1.2, q.2))) t,
          nextState (clonePath π q.1.1 (rebuild (q.1.2, q.2))) t))) _ =
    (Measure.map (fun q : (FullPath T 1 n k × (Fin T → Fin m)) × Fin m => postHist t
      (clonePath π q.1.1 (rebuild (q.1.2, q.2)))) _).compProd κ'
  rw [hj, hp]
  have hmargClone :
      Measure.map
          (fun q : (FullPath T 1 n k × (Fin T → Fin m)) × Fin m =>
            clonePostRest π i0 t (postHist t q.1.1) q.1.2)
          ((M.law.prod ρ).prod u) =
        Measure.map (fun hr => clonePostRest π i0 t hr.1 hr.2)
          (Measure.map (fun wr => (postHist t wr.1, wr.2)) (M.law.prod ρ)) := by
    let f := fun wr : FullPath T 1 n k × (Fin T → Fin m) =>
      clonePostRest π i0 t (postHist t wr.1) wr.2
    have hf : Measurable f := by
      unfold f clonePostRest clonePostHist clonePreHist postHist preHist currentState
        pastIndex actionAt
      fun_prop
    calc
      _ = (((M.law.prod ρ).prod u).map Prod.fst).map f := by
        rw [Measure.map_map hf measurable_fst]
        rfl
      _ = (M.law.prod ρ).map f := by simp [u]
      _ = _ := by
        rw [Measure.map_map (by unfold clonePostRest clonePostHist clonePreHist; fun_prop)
          (by unfold postHist preHist currentState pastIndex actionAt; fun_prop)]
        rfl
  rw [hmargClone]
  simpa only [ρ, u, draw, κ, κr, κ', i0] using hout

-- @node: clone_fullFiltrationRandomization
lemma clone_fullFiltrationRandomization {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hA : FullFiltrationRandomization M) :
    FullFiltrationRandomization (cloneModel M hm π) := by
  constructor
  · exact hA.1
  intro t
  letI : IsMarkovKernel (actionKernel M) := by
    refine ⟨fun x => ⟨?_⟩⟩
    change (∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact (hA.1 x).1 a)]
    simp [(hA.1 x).2]
  letI : IsMarkovKernel (actionKernel (cloneModel M hm π)) := by
    change IsMarkovKernel (actionKernel M)
    infer_instance
  let ρ := Measure.pi (fun _ : Fin (T + 1) => uniformFin m)
  let κ := Kernel.comap (actionKernel M) (fun h : PreHistory T 1 n k t => h.2.2.1)
    (by fun_prop)
  let κ' := Kernel.comap (actionKernel (cloneModel M hm π))
    (fun h : PreHistory T 1 (n * m) k t => h.2.2.1) (by fun_prop)
  have htransport := map_prod_of_compProd_dependent M.law ρ
    (preHist t) (by unfold preHist currentState pastIndex; fun_prop)
    (actionAt · t) (by unfold actionAt; fun_prop) κ (hA.2 t) κ'
    (fun hc => clonePreHist π t hc.1 hc.2) (by unfold clonePreHist; fun_prop)
    (fun _ a => a) (by fun_prop) (by
      intro hc
      unfold κ κ'
      rw [Kernel.comap_apply, Kernel.comap_apply]
      change (actionKernel M) hc.1.2.2.1 =
        Measure.map id ((actionKernel M) hc.1.2.2.1)
      rw [Measure.map_id])
  change (clonePathLaw M π).map (fun w => (preHist t w, actionAt w t)) =
    ((clonePathLaw M π).map (preHist t)).compProd κ'
  unfold clonePathLaw
  rw [Measure.map_map (by unfold preHist currentState pastIndex actionAt; fun_prop)
    (by unfold clonePath; fun_prop)]
  rw [Measure.map_map (by unfold preHist currentState pastIndex; fun_prop)
    (by unfold clonePath; fun_prop)]
  have hj : ((fun w : FullPath T 1 (n * m) k => (preHist t w, actionAt w t)) ∘
      fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) => clonePath π q.1 q.2) =
      fun q => (clonePreHist π t (preHist t q.1) q.2, actionAt q.1 t) := by
    funext q
    rw [Function.comp_apply, clonePath_preHist]
    rfl
  have hp : ((preHist t : FullPath T 1 (n * m) k → _) ∘
      fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) => clonePath π q.1 q.2) =
      fun q => clonePreHist π t (preHist t q.1) q.2 := by
    funext q
    rw [Function.comp_apply, clonePath_preHist]
  rw [hj, hp]
  have hmarg :
      (M.law.prod ρ).map
          (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) =>
            clonePreHist π t (preHist t q.1) q.2) =
        (((M.law.map (preHist t)).prod ρ).map
          (fun hc => clonePreHist π t hc.1 hc.2)) := by
    have hpre : Measurable (preHist t : FullPath T 1 n k → _) := by
      unfold preHist currentState pastIndex
      fun_prop
    have hf : Measurable (fun hc : PreHistory T 1 n k t ×
        (Fin (T + 1) → Fin m) => clonePreHist π t hc.1 hc.2) := by
      unfold clonePreHist
      fun_prop
    calc
      _ = (M.law.prod ρ).map
          ((fun hc => clonePreHist π t hc.1 hc.2) ∘ Prod.map (preHist t) id) := by rfl
      _ = ((M.law.prod ρ).map (Prod.map (preHist t) id)).map
          (fun hc => clonePreHist π t hc.1 hc.2) := by
            rw [Measure.map_map hf (hpre.prodMap measurable_id)]
      _ = _ := by
        rw [← Measure.map_prod_map M.law ρ hpre measurable_id, Measure.map_id]
  rw [hmarg]
  simpa only [ρ, κ, κ'] using htransport



-- @node: uniformFin_singleton
/-- Each clone coordinate has mass `1 / m` under the uniform coordinate law. -/
lemma uniformFin_singleton (m : Nat) (i : Fin m) :
    uniformFin m {i} = ENNReal.ofReal (1 / (m : ℝ)) := by
  simp [uniformFin, Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply]

-- @node: clone_initial_mass
/-- A fixed relabeling lifts the initial base-state distribution uniformly. -/
lemma clone_initial_mass {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (h : Fin n) (i : Fin m) :
    ((cloneModel M hm π).law.map (fun w => stateAt w 0)) {(0, π (h, i))} =
      (M.law.map (fun w => stateAt w 0)) {(0, h)} *
        ENNReal.ofReal (1 / (m : ℝ)) := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  have hcoord :
      (Measure.pi (fun _ : Fin (T + 1) => uniformFin m)).map
        (fun c => c 0) = uniformFin m := by
    simpa using (Measure.pi_map_eval (fun _ : Fin (T + 1) => uniformFin m) 0)
  have hpath : Measurable (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) =>
      clonePath π q.1 q.2) := by
    unfold clonePath
    fun_prop
  rw [show (cloneModel M hm π).law = clonePathLaw M π by rfl]
  unfold clonePathLaw
  rw [Measure.map_map (by unfold stateAt; fun_prop) hpath]
  have hset : (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) =>
      stateAt (clonePath π q.1 q.2) 0) ⁻¹' {(0, π (h, i))} =
      ((fun w : FullPath T 1 n k => stateAt w 0) ⁻¹' {(0, h)}) ×ˢ
        ((fun c : Fin (T + 1) → Fin m => c 0) ⁻¹' {i}) := by
    ext ⟨w, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, stateAt, clonePath]
    constructor
    · intro heq
      have hp := π.injective (congrArg Prod.snd heq)
      constructor
      · apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
    · rintro ⟨hb, hc⟩
      have hh : (w.1 0).2 = h := congrArg Prod.snd hb
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rw [hh, hc]
  rw [Measure.map_apply (by unfold stateAt clonePath; fun_prop) (measurableSet_singleton _)]
  change (M.law.prod (Measure.pi (fun _ : Fin (T + 1) => uniformFin m)))
    ((fun q => stateAt (clonePath π q.1 q.2) 0) ⁻¹' {(0, π (h, i))}) = _
  rw [hset, Measure.prod_prod]
  rw [← Measure.map_apply (by unfold stateAt; fun_prop) (measurableSet_singleton _)]
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  rw [hcoord, uniformFin_singleton]

-- @node: clone_stationaryOverlap_of_lift
/-- The pointwise stationary overlap bound survives uniform cloning. -/
lemma clone_stationaryOverlap_of_lift {T n k m : Nat} {C : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hbase : StationaryOverlap C M)
    (hlift : ∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (0, π (h, i)) =
        stationaryLaw (policyKernel M p) (0, h) / (m : ℝ)) :
    StationaryOverlap C (cloneModel M hm π) := by
  constructor
  · exact hbase.1
  intro s
  rcases s with ⟨x, j⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  have he := hlift M.e (Or.inr rfl) (π.symm j).1 (π.symm j).2
  have hb := hlift M.b (Or.inl rfl) (π.symm j).1 (π.symm j).2
  simp only [π.apply_symm_apply] at he hb
  change stationaryLaw (policyKernel (cloneModel M hm π) M.e) (0, j) ≤
    C * stationaryLaw (policyKernel (cloneModel M hm π) M.b) (0, j)
  rw [he, hb]
  calc
    stationaryLaw (policyKernel M M.e) (0, (π.symm j).1) / (m : ℝ) ≤
        (C * stationaryLaw (policyKernel M M.b) (0, (π.symm j).1)) /
          (m : ℝ) :=
      div_le_div_of_nonneg_right (hbase.2 (0, (π.symm j).1)) (Nat.cast_nonneg m)
    _ = C * (stationaryLaw (policyKernel M M.b) (0, (π.symm j).1) /
        (m : ℝ)) := by ring

-- @node: sum_kernel_nextState_eq_one
/-- The next-state marginal of a joint probability kernel has total mass one. -/
lemma sum_kernel_nextState_eq_one {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (hK : FullFiltrationPomdp M) (s : JointState nX nH) (a : Fin k) :
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

-- @node: policyKernel_probabilityVector
/-- A finite probability policy induces a stochastic state kernel. -/
lemma policyKernel_probabilityVector {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (p : Policy nX k) (hp : PolicyVector p) (s : JointState nX nH) :
    ProbabilityVector (policyKernel M p s) := by
  constructor
  · intro s'
    unfold policyKernel
    exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg ((hp s.1).1 a) ENNReal.toReal_nonneg
  · unfold policyKernel
    rw [Finset.sum_comm]
    calc
      ∑ a : Fin k, ∑ s' : JointState nX nH,
          p s.1 a * (M.K s a {q | q.2 = s'}).toReal =
          ∑ a : Fin k, p s.1 a * ∑ s' : JointState nX nH,
            (M.K s a {q | q.2 = s'}).toReal := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
      _ = ∑ a : Fin k, p s.1 a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [sum_kernel_nextState_eq_one M hK s a, mul_one]
      _ = 1 := (hp s.1).2

-- @node: target_stationary_law_of_class
/-- The target kernel's selected law is stationary under finite-state contraction. -/
lemma target_stationary_law_of_class {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (ht0 : 0 < t0)
    (hM : HuWagerClass t0 zeta M) :
    IsStationary (policyKernel M M.e) (stationaryLaw (policyKernel M M.e)) := by
  have hα : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hex : ∃ d, IsStationary (policyKernel M M.e) d := by
    apply CausalSmith.Stat.PomdpLatentOverlapMinimax.exists_stationary_of_contraction
      (P := policyKernel M M.e)
      (p0 := stationaryLaw (policyKernel M M.b))
      (alpha := mixingAlpha t0)
    · exact policyKernel_probabilityVector M hM.pomdp M.e hM.overlap.1
    · exact hM.start.1.1
    · exact Real.exp_nonneg _
    · exact hα
    · exact hM.contraction M.e (Or.inr rfl)
  exact Classical.epsilon_spec hex

-- @node: clone_stationary_data
/-- The contraction argument identifies both cloned stationary laws and hence
preserves the target value, stationary ratio, and stationary overlap bound. -/
lemma clone_stationary_data {T n k m : Nat} {t0 zeta C : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hM : FixedOverlapClass t0 zeta C M) :
    UniformContraction t0 (cloneModel M hm π) ∧
    (∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (0, π (h, i)) =
        stationaryLaw (policyKernel M p) (0, h) / (m : ℝ)) ∧
    targetValue (cloneModel M hm π) = targetValue M ∧
    (∀ h i, stationaryRatio (cloneModel M hm π) (0, π (h, i)) =
      stationaryRatio M (0, h)) ∧
    StationaryOverlap C (cloneModel M hm π) := by
  have hc := clone_uniformContraction M hm π hM.1.contraction
  have hlift : ∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (0, π (h, i)) =
        stationaryLaw (policyKernel M p) (0, h) / (m : ℝ) := by
    intro p hp h i
    have hbase : IsStationary (policyKernel M p)
        (stationaryLaw (policyKernel M p)) := by
      rcases hp with rfl | rfl
      · exact hM.1.start.1
      · exact target_stationary_law_of_class M hM.1.t0_pos hM.1
    exact clone_stationaryLaw_uniformLift M hm π p hM.1.t0_pos hc hp hbase h i
  exact ⟨hc, hlift, clone_targetValue_of_lift M hm π (hlift M.e (Or.inr rfl)),
    clone_stationaryRatio_of_lift M hm π hlift,
    clone_stationaryOverlap_of_lift M hm π hM.2 hlift⟩

-- @node: clone_stationaryStart
/-- Uniform clone initialization agrees with the selected stationary behavior law. -/
lemma clone_stationaryStart {T n k m : Nat} {t0 zeta C : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hM : FixedOverlapClass t0 zeta C M) :
    StationaryStart (cloneModel M hm π) := by
  have hd := clone_stationary_data M hm π hM
  have hlift := hd.2.1 M.b (Or.inl rfl)
  have heq : stationaryLaw (policyKernel (cloneModel M hm π) M.b) =
      fun s => stationaryLaw (policyKernel M M.b)
        (s.1, (π.symm s.2).1) / (m : ℝ) := by
    funext s
    rcases s with ⟨x, j⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simpa using hlift (π.symm j).1 (π.symm j).2
  constructor
  · change IsStationary (policyKernel (cloneModel M hm π) M.b)
      (stationaryLaw (policyKernel (cloneModel M hm π) M.b))
    rw [heq]
    exact clone_uniformLift_stationary M hm π M.b _ hM.1.start.1
  · intro s
    rcases s with ⟨x, j⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have hinit := clone_initial_mass M hm π (π.symm j).1 (π.symm j).2
    simp only [π.apply_symm_apply] at hinit
    rw [hinit, hM.1.start.2]
    change _ = ENNReal.ofReal
      (stationaryLaw (policyKernel (cloneModel M hm π) M.b) (0, j))
    rw [heq]
    simp only [ENNReal.ofReal_one, one_mul, one_div]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.mpr (Nat.cast_nonneg m))]

-- @node: clone_preservation_regularities
/-- The clone construction preserves all class conditions that concern one-step
moments, policies, contraction, and stationary distributions. -/
lemma clone_preservation_regularities {T n k m : Nat} {t0 zeta C : ℝ}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m))
    (hM : FixedOverlapClass t0 zeta C M) :
    RewardMomentEnvelope (cloneModel M hm π) ∧
    PolicyOverlap zeta (cloneModel M hm π) ∧
    UniformContraction t0 (cloneModel M hm π) ∧
    StationaryStart (cloneModel M hm π) ∧
    StationaryOverlap C (cloneModel M hm π) ∧
    targetValue (cloneModel M hm π) = targetValue M ∧
    (∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (0, π (h, i)) =
        stationaryLaw (policyKernel M p) (0, h) / (m : ℝ)) ∧
    (∀ h i, stationaryRatio (cloneModel M hm π) (0, π (h, i)) =
      stationaryRatio M (0, h)) := by
  have hd := clone_stationary_data M hm π hM
  exact ⟨clone_reward_moment_envelope M hm π hM.1.moment,
    clone_policyOverlap M hm π hM.1.overlap,
    hd.1, clone_stationaryStart M hm π hM, hd.2.2.2.2,
    hd.2.2.1, hd.2.1, hd.2.2.2.1⟩

-- @node: lem:clone-preservation
/-- A fixed relabeling and uniform clone refresh preserve class membership, target
value, both stationary vectors, stationary density ratio, and full-history laws. -/
lemma clone_preservation {T n k m : Nat} {t0 zeta C : ℝ}
    (M : PomdpModel T 1 n k) (ht0 : 0 < t0) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (π : Fin n × Fin m ≃ Fin (n * m)) (hM : FixedOverlapClass t0 zeta C M) :
    FixedOverlapClass t0 zeta C (cloneModel M hm π) ∧
    targetValue (cloneModel M hm π) = targetValue M ∧
    (∀ p, (p = M.b ∨ p = M.e) → ∀ h i,
      stationaryLaw (policyKernel (cloneModel M hm π) p) (⟨0, by decide⟩, π (h, i)) =
        stationaryLaw (policyKernel M p) (⟨0, by decide⟩, h) / (m : ℝ)) ∧
    (∀ h i, stationaryRatio (cloneModel M hm π) (⟨0, by decide⟩, π (h, i)) =
      stationaryRatio M (⟨0, by decide⟩, h)) ∧
    FullFiltrationPomdp (cloneModel M hm π) ∧
    FullFiltrationRandomization (cloneModel M hm π) ∧
    UniformContraction t0 (cloneModel M hm π) := by
  have hr := clone_preservation_regularities M hm π hM
  have hHistory : FullFiltrationPomdp (cloneModel M hm π) ∧
      FullFiltrationRandomization (cloneModel M hm π) := by
    exact ⟨clone_fullFiltrationPomdp M hm π hM.1.pomdp,
      clone_fullFiltrationRandomization M hm π hM.1.randomization⟩
  constructor
  · refine ⟨?_, hr.2.2.2.2.1⟩
    exact ⟨hM.1.t0_pos, hM.1.zeta_pos, hHistory.1, hHistory.2,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩
  exact ⟨hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2, hHistory.1, hHistory.2, hr.2.2.1⟩

end CausalSmith.Stat.PomdpStateauditMinimax
