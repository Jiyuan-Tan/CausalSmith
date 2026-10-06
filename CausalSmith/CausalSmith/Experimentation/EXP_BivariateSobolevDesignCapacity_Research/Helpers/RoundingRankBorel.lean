module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingBorel

/-! # Borel elimination of changing Gram--Schmidt bases

Finite branching at zero residuals preserves measurability for every consumer
of a basis. This proves the rank-stratum step without imposing a fixed rank.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ A measurable consumer of every fixed measurable basis family remains measurable
through the finite Gram--Schmidt branching, including discarded residuals.](goal) Under [the stated conditions](hyp:hvs,hbs,hF). -/
-- @node: orderedOrtho_foldl_consumer_measurable
lemma orderedOrtho_foldl_consumer_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (vs bs : List (Ω → Fin n → ℝ))
    (hvs : ∀ v ∈ vs, Measurable v) (hbs : ∀ b ∈ bs, Measurable b)
    (F : Ω → List (Fin n → ℝ) → β)
    (hF : ∀ cs : List (Ω → Fin n → ℝ), (∀ c ∈ cs, Measurable c) →
      Measurable (fun x => F x (cs.map (fun c => c x)))) :
    Measurable (fun x => F x
      ((vs.map (fun v => v x)).foldl insertOrtho (bs.map (fun b => b x)))) := by
  classical
  induction vs generalizing bs with
  | nil => exact hF bs hbs
  | cons v vs ih =>
    have hv := hvs v (by simp)
    have htail : ∀ w ∈ vs, Measurable w := fun w hw => hvs w (by simp [hw])
    let w (x : Ω) := removeProjections (bs.map (fun b => b x)) (v x)
    let r (x : Ω) := Real.sqrt (rowDot (w x) (w x))
    have hw : Measurable w := by
      apply measurable_pi_lambda
      intro j
      have hs : Measurable (fun x =>
          (bs.map (fun b => rowDot (v x) (b x) * b x j)).sum) := by
        induction bs with
        | nil => exact measurable_const
        | cons b bs ih =>
          have hb := hbs b (by simp)
          have ht : ∀ c ∈ bs, Measurable c := fun c hc => hbs c (by simp [hc])
          simp only [List.map_cons, List.sum_cons]
          exact ((rowDot_measurable.comp (hv.prodMk hb)).mul
            ((measurable_pi_apply j).comp hb)).add (ih ht)
      exact ((measurable_pi_apply j).comp hv).sub (by
        simpa only [List.map_map, Function.comp_def] using hs)
    have hr : Measurable r := (rowDot_measurable.comp (hw.prodMk hw)).sqrt
    let c (x : Ω) : Fin n → ℝ := fun i => w x i / r x
    have hc : Measurable c := by
      apply measurable_pi_lambda
      intro i
      exact ((measurable_pi_apply i).comp hw).div hr
    have hyes := ih (bs ++ [c]) htail (by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hbs b hb
      · have he : b = c := List.mem_singleton.mp hb
        exact he ▸ hc)
    have hno := ih bs htail hbs
    have hout : Measurable (fun x => if 0 < r x
      then F x ((vs.map (fun v => v x)).foldl insertOrtho ((bs ++ [c]).map (fun b => b x)))
      else F x ((vs.map (fun v => v x)).foldl insertOrtho (bs.map (fun b => b x)))) :=
      Measurable.ite (measurableSet_lt (measurable_const (a := (0 : ℝ))) hr) hyes hno
    convert hout using 1
    ext x
    simp only [List.map_cons, List.foldl_cons, insertOrtho]
    change F x ((vs.map (fun v => v x)).foldl insertOrtho
      (if 0 < r x then (bs.map (fun b => b x)) ++ [c x]
       else bs.map (fun b => b x))) = _
    split_ifs <;> simp only [List.map_append, List.map_cons, List.map_nil]

/-- [ Ordered orthonormalization admits measurable consumers with no rank premise.](goal) Under [the stated conditions](hyp:hvs,hF). -/
-- @node: orderedOrtho_consumer_measurable
lemma orderedOrtho_consumer_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (vs : List (Ω → Fin n → ℝ)) (hvs : ∀ v ∈ vs, Measurable v)
    (F : Ω → List (Fin n → ℝ) → β)
    (hF : ∀ cs : List (Ω → Fin n → ℝ), (∀ c ∈ cs, Measurable c) →
      Measurable (fun x => F x (cs.map (fun c => c x)))) :
    Measurable (fun x => F x (orderedOrtho (vs.map (fun v => v x)))) := by
  exact orderedOrtho_foldl_consumer_measurable vs [] hvs (by simp) F hF

/-- [ Finite projection subtraction is Borel for a list of measurable vectors.](goal) Under [the stated conditions](hyp:hbs,hv). -/
-- @node: removeProjections_list_measurable
lemma removeProjections_list_measurable {Ω : Type*} [MeasurableSpace Ω]
    (bs : List (Ω → Fin n → ℝ)) (v : Ω → Fin n → ℝ)
    (hbs : ∀ b ∈ bs, Measurable b) (hv : Measurable v) :
    Measurable (fun x => removeProjections (bs.map (fun b => b x)) (v x)) := by
  apply measurable_pi_lambda
  intro j
  have hs : Measurable (fun x =>
      (bs.map (fun b => rowDot (v x) (b x) * b x j)).sum) := by
    induction bs with
    | nil => exact measurable_const
    | cons b bs ih =>
      have hb := hbs b (by simp)
      simp only [List.map_cons, List.sum_cons]
      exact ((rowDot_measurable.comp (hv.prodMk hb)).mul
        ((measurable_pi_apply j).comp hb)).add
        (ih (fun c hc => hbs c (by simp [hc])))
  exact ((measurable_pi_apply j).comp hv).sub (by
    simpa only [removeProjections, List.map_map, Function.comp_def] using hs)

/-- [ At any fixed retained prefix length, the actual constraint projection is Borel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: constraintProjection_measurable
lemma constraintProjection_measurable (q : ℕ) :
    Measurable (fun x : (Fin (n / 4) → Fin n → ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) =>
      constraintProjection x.1 q x.2.1 x.2.2) := by
  classical
  let vs := (List.range q).map (fun h => fun x :
      (Fin (n / 4) → Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      activeMask x.2.1 (if hh : h < n / 4 then x.1 ⟨h, hh⟩ else 0))
  have hvs : ∀ v ∈ vs, Measurable v := by
    intro v hv
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hv
    split <;> fun_prop
  have hout := orderedOrtho_consumer_measurable vs hvs
    (fun x bs => removeProjections bs (activeMask x.2.1 x.2.2))
    (fun cs hcs => removeProjections_list_measurable cs _ hcs
      (activeMask_measurable.comp (by fun_prop)))
  simpa only [vs, List.map_map, Function.comp_def, constraintProjection,
    constraintBasis] using hout

/-- Consumers of the actual nullspace basis are measurable for each retained prefix.](goal) Under [the stated conditions](hyp:ha,hu,hF). This uses [the stated conclusion](goal). -/
-- @node: nullspaceBasis_consumer_measurable
lemma nullspaceBasis_consumer_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] (q : ℕ)
    (a : Ω → Fin (n / 4) → Fin n → ℝ) (u : Ω → Fin n → ℝ)
    (ha : Measurable a) (hu : Measurable u)
    (F : Ω → List (Fin n → ℝ) → β)
    (hF : ∀ cs : List (Ω → Fin n → ℝ), (∀ c ∈ cs, Measurable c) →
      Measurable (fun x => F x (cs.map (fun c => c x)))) :
    Measurable (fun x => F x (nullspaceBasis (a x) q (u x))) := by
  let vs := (List.finRange n).map (fun j => fun x =>
    constraintProjection (a x) q (u x) (fun i => if i = j then 1 else 0))
  have hvs : ∀ v ∈ vs, Measurable v := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    fun_prop
  have hout := orderedOrtho_consumer_measurable vs hvs F hF
  simpa only [vs, List.map_map, Function.comp_def, nullspaceBasis] using hout

/-- [ Inverse-CDF selection is measurable for lists indexed by their measurable members.](goal) Under [the stated conditions](hyp:hcs,hw,ht). -/
-- @node: inverseCDF_list_measurable
lemma inverseCDF_list_measurable {Ω : Type*} [MeasurableSpace Ω]
    (cs : List (Ω → Fin n → ℝ)) (w : (Ω → Fin n → ℝ) → Ω → ℝ)
    (t : Ω → ℝ) (hcs : ∀ c ∈ cs, Measurable c)
    (hw : ∀ c ∈ cs, Measurable (w c)) (ht : Measurable t) :
    Measurable (fun x => inverseCDF (cs.map (fun c => (c x, w c x))) (t x)) := by
  have h := inverseCDF_family_measurable cs.attach (fun c x => c.val x)
    (fun c x => w c.val x) t (fun c => hcs c.val c.property)
    (fun c => hw c.val c.property) ht
  convert h using 1
  funext x
  have he := List.attach_map_val (l := cs) (f := fun c => (c x, w c x))
  rw [he]

/-- [ The specified basis sampling and asymmetric boundary move form a Borel consumer.](goal) Under [the stated conditions](hyp:hcs,hu,ht₁,ht₂). -/
-- @node: boundaryBasisMove_list_measurable
lemma boundaryBasisMove_list_measurable {Ω : Type*} [MeasurableSpace Ω]
    (cs : List (Ω → Fin n → ℝ)) (u : Ω → Fin n → ℝ) (t₁ t₂ : Ω → ℝ)
    (hcs : ∀ c ∈ cs, Measurable c) (hu : Measurable u)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂) :
    Measurable (fun x =>
      let bs := cs.map (fun c => c x)
      let ws := bs.map (fun v => (boundaryPlus (u x) v * boundaryMinus (u x) v)⁻¹)
      let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) (t₁ x)
      if t₂ x < boundaryMinus (u x) v / (boundaryPlus (u x) v + boundaryMinus (u x) v)
      then u x + boundaryPlus (u x) v • v else u x - boundaryMinus (u x) v • v) := by
  let w (c : Ω → Fin n → ℝ) (x : Ω) :=
    (boundaryPlus (u x) (c x) * boundaryMinus (u x) (c x))⁻¹
  have hw (c) (hc : c ∈ cs) : Measurable (w c) := by
    have hcm := hcs c hc
    dsimp [w]
    fun_prop
  let S (x : Ω) := (cs.map (fun c => w c x)).sum
  have hS : Measurable S := by
    dsimp [S]
    have hm := List.measurable_fun_sum (cs.map w) (by
      intro f hf
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      exact hw c hc)
    simpa only [List.map_map, Function.comp_def] using hm
  let v (x : Ω) := inverseCDF (cs.map (fun c => (c x, w c x / S x))) (t₁ x)
  have hv : Measurable v := inverseCDF_list_measurable cs
    (fun c x => w c x / S x) t₁ hcs (fun c hc => (hw c hc).div hS) ht₁
  have hout := boundaryMove_measurable u v t₂ hu hv ht₂
  convert hout using 1
  ext x
  have hz (ls : List (Ω → Fin n → ℝ)) :
      (ls.map (fun c => c x)).zip ((ls.map (fun c => w c x)).map (fun z => z / S x)) =
      ls.map (fun c => (c x, w c x / S x)) := by
    induction ls with
    | nil => rfl
    | cons c ls ih => simp only [List.map_cons, List.zip_cons_cons, ih]
  simp only [List.map_map, Function.comp_def]
  dsimp only [v, S, w] at hz ⊢
  simp only [List.map_map, Function.comp_def] at hz
  rw [hz cs]

/-- [ The actual nonterminal move is Borel for a fixed number of retained constraints. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingStep_measurable
lemma roundingStep_measurable (q : ℕ) :
    Measurable (fun x : (Fin (n / 4) → Fin n → ℝ) ×
      ((Fin n → ℝ) × (ℝ × ℝ)) => roundingStep x.1 q x.2.1 x.2.2.1 x.2.2.2) := by
  let F (x : (Fin (n / 4) → Fin n → ℝ) × ((Fin n → ℝ) × (ℝ × ℝ)))
      (bs : List (Fin n → ℝ)) :=
    let ws := bs.map (fun v => (boundaryPlus x.2.1 v * boundaryMinus x.2.1 v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) x.2.2.1
    if x.2.2.2 < boundaryMinus x.2.1 v / (boundaryPlus x.2.1 v + boundaryMinus x.2.1 v)
    then x.2.1 + boundaryPlus x.2.1 v • v else x.2.1 - boundaryMinus x.2.1 v • v
  have hF (cs : List (((Fin (n / 4) → Fin n → ℝ) ×
      ((Fin n → ℝ) × (ℝ × ℝ))) → Fin n → ℝ)) (hcs : ∀ c ∈ cs, Measurable c) :
      Measurable (fun x => F x (cs.map (fun c => c x))) := by
    exact boundaryBasisMove_list_measurable cs
      (fun x => x.2.1) (fun x => x.2.2.1) (fun x => x.2.2.2) hcs
      (measurable_fst.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hout := nullspaceBasis_consumer_measurable q (fun x => x.1) (fun x => x.2.1)
    measurable_fst (measurable_fst.comp measurable_snd) F hF
  exact hout

/-- Discrete retained-count choices can be combined with the Borel step family.](goal) Under [the stated conditions](hyp:ha,hq,hu,ht₁,ht₂). This uses [the stated conclusion](goal). -/
-- @node: roundingStep_family_measurable
lemma roundingStep_family_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin (n / 4) → Fin n → ℝ) (q : Ω → ℕ)
    (u : Ω → Fin n → ℝ) (t₁ t₂ : Ω → ℝ)
    (ha : Measurable a) (hq : Measurable q) (hu : Measurable u)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂) :
    Measurable (fun x => roundingStep (a x) (q x) (u x) (t₁ x) (t₂ x)) := by
  have h : Measurable (fun x : ((Fin (n / 4) → Fin n → ℝ) ×
      ((Fin n → ℝ) × (ℝ × ℝ))) × ℕ =>
      roundingStep x.1.1 x.2 x.1.2.1 x.1.2.2.1 x.1.2.2.2) :=
    measurable_from_prod_countable_left roundingStep_measurable
  exact h.comp ((ha.prodMk (hu.prodMk (ht₁.prodMk ht₂))).prodMk hq)

/-- [ Filtering a finite index list by active tests preserves measurable consumers.](goal) Under [the stated conditions](hyp:hu,hF). -/
-- @node: activeFilter_consumer_measurable
lemma activeFilter_consumer_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (l : List (Fin n)) (u : Ω → Fin n → ℝ) (hu : Measurable u)
    (F : Ω → List (Fin n) → β) (hF : ∀ cs, Measurable (fun x => F x cs)) :
    Measurable (fun x => F x (l.filter (fun i => decide (|u x i| < 1)))) := by
  classical
  induction l generalizing F with
  | nil => exact hF []
  | cons i l ih =>
    have hp : MeasurableSet {x | |u x i| < 1} := by
      apply measurableSet_lt <;> fun_prop
    have hyes := ih (fun x cs => F x (i :: cs)) (fun cs => hF (i :: cs))
    have hno := ih F hF
    have hout : Measurable (fun x => if |u x i| < 1
        then F x (i :: l.filter (fun i => decide (|u x i| < 1)))
        else F x (l.filter (fun i => decide (|u x i| < 1)))) :=
      Measurable.ite hp hyes hno
    convert hout using 1
    ext x
    by_cases hx : |u x i| < 1 <;> simp [hx]

/-- [ The actual active list has measurable consumers, including changing lengths and heads.](goal) Under [the stated conditions](hyp:hu,hF). -/
-- @node: activeIndices_consumer_measurable
lemma activeIndices_consumer_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (u : Ω → Fin n → ℝ) (hu : Measurable u)
    (F : Ω → List (Fin n) → β) (hF : ∀ cs, Measurable (fun x => F x cs)) :
    Measurable (fun x => F x (activeIndices (u x))) := by
  exact activeFilter_consumer_measurable (List.finRange n) u hu F hF

/-- [ Phase transitions, including terminal head selection, are Borel.](goal) Under [the stated conditions](hyp:ha,hst,ht₁,ht₂). -/
-- @node: phaseMove_family_measurable
lemma phaseMove_family_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin (n / 4) → Fin n → ℝ) (st : Ω → RoundingState n)
    (t₁ t₂ : Ω → ℝ) (ha : Measurable a) (hst : Measurable st)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂) :
    Measurable (fun x => phaseMove (a x) (st x) (t₁ x) (t₂ x)) := by
  classical
  let F (x : Ω) (active : List (Fin n)) : RoundingState n :=
    if active.length ≤ (st x).2.1 ∧ active.length ≤ 3 then
      match active with
      | [] => st x
      | i :: _ => (Function.update (st x).1 i
          (if t₂ x < (1 + (st x).1 i) / 2 then 1 else -1), n, 0)
    else
      (roundingStep (a x)
        (if active.length ≤ (st x).2.1 then active.length / 4 else (st x).2.2)
        (st x).1 (t₁ x) (t₂ x),
        (if active.length ≤ (st x).2.1 then active.length / 2 else (st x).2.1),
        (if active.length ≤ (st x).2.1 then active.length / 4 else (st x).2.2))
  have hu : Measurable (fun x => (st x).1) := by fun_prop
  have hF (active : List (Fin n)) : Measurable (fun x => F x active) := by
    have hp : MeasurableSet {x | active.length ≤ (st x).2.1} := by
      apply measurableSet_le <;> fun_prop
    have hq : Measurable (fun x => if active.length ≤ (st x).2.1
        then active.length / 4 else (st x).2.2) :=
      Measurable.ite hp measurable_const (by fun_prop)
    have hs : Measurable (fun x => if active.length ≤ (st x).2.1
        then active.length / 2 else (st x).2.1) :=
      Measurable.ite hp measurable_const (by fun_prop)
    have hm := roundingStep_family_measurable a _ _ t₁ t₂ ha hq hu ht₁ ht₂
    have hnon := hm.prodMk (hs.prodMk hq)
    have hterm : Measurable (fun x => match active with
        | [] => st x
        | i :: _ => (Function.update (st x).1 i
          (if t₂ x < (1 + (st x).1 i) / 2 then (1 : ℝ) else -1), n, 0)) := by
      cases active with
      | nil => exact hst
      | cons i is =>
        exact (terminalMove_measurable _ t₂ i hu ht₂).prodMk
          (measurable_const.prodMk measurable_const)
    by_cases hsmall : active.length ≤ 3
    · simpa only [F, hsmall, and_true] using Measurable.ite hp hterm hnon
    · simpa only [F, hsmall, and_false, if_false] using hnon
  exact activeIndices_consumer_measurable _ hu F hF

/-- Every fractional iteration is jointly Borel in input rows and all seeds. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingIteration_measurable
lemma roundingIteration_measurable (k : ℕ) :
    Measurable (fun x : (Fin (n / 4) → Fin n → ℝ) × RoundingSeeds n =>
      roundingIteration x.1 x.2 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact phaseMove_family_measurable _ _ _ _ measurable_fst ih
      ((roundingSeed_measurable (2 * k)).comp measurable_snd)
      ((roundingSeed_measurable (2 * k + 1)).comp measurable_snd)

/-- The full signing map is Borel, without any rank or row-bound premise. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: orderedBoundaryRounding_measurable
lemma orderedBoundaryRounding_measurable (n : ℕ) :
    Measurable (fun x : (Fin (n / 4) → Fin n → ℝ) × RoundingSeeds n =>
      orderedBoundaryRounding n x.1 x.2) := by
  unfold orderedBoundaryRounding
  apply measurable_pi_lambda
  intro i
  apply measurable_to_bool
  have h : MeasurableSet {x : (Fin (n / 4) → Fin n → ℝ) × RoundingSeeds n |
      0 < (roundingIteration x.1 x.2 n).1 i} := by
    apply measurableSet_lt <;> fun_prop
  convert h using 1
  ext x
  simp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
