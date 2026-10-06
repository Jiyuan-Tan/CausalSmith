module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.OrderedRoundingCore

/-! # Borel arithmetic for ordered boundary rounding

The active-coordinate masks, sign-guarded finite boundary minima, and finite
inverse-CDF selections are measurable without rank or nondegeneracy assumptions.
These are the arithmetic ingredients of the roadmap's Borel-stratum argument.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ Adding an entry to a nonempty finite minimum takes the minimum of the two values.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: finiteMin_cons_of_ne_nil
lemma finiteMin_cons_of_ne_nil (a : ℝ) (xs : List ℝ) (hne : xs ≠ []) :
    finiteMin (a :: xs) = min a (finiteMin xs) := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons b bs => simp [finiteMin, List.foldl_assoc]

/-- [ A sign-guarded list is empty on a measurable set and its finite minimum is measurable.](goal) Under [the stated conditions](hyp:hp,hf). -/
-- @node: finiteMin_guarded_measurable
lemma finiteMin_guarded_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (p : ι → Ω → Prop) [∀ i, DecidablePred (p i)]
    (f : ι → Ω → ℝ) (hp : ∀ i, MeasurableSet {x | p i x})
    (hf : ∀ i, Measurable (f i)) :
    MeasurableSet {x | l.filterMap (fun i => if p i x then some (f i x) else none) = []} ∧
    Measurable (fun x => finiteMin
      (l.filterMap (fun i => if p i x then some (f i x) else none))) := by
  classical
  induction l with
  | nil => exact ⟨by simp, measurable_const⟩
  | cons i l ih =>
    have he : MeasurableSet {x | ¬p i x ∧
        l.filterMap (fun j => if p j x then some (f j x) else none) = []} :=
      (hp i).compl.inter ih.1
    constructor
    · convert he using 1
      ext x
      by_cases h : p i x <;> simp [h]
    · have hm := (hf i).min ih.2
      have ht : Measurable (fun x =>
          if l.filterMap (fun j => if p j x then some (f j x) else none) = []
          then f i x else min (f i x)
            (finiteMin (l.filterMap (fun j => if p j x then some (f j x) else none)))) :=
        (hf i).ite ih.1 hm
      have hout : Measurable (fun x => if p i x then
          (if l.filterMap (fun j => if p j x then some (f j x) else none) = []
          then f i x else min (f i x)
            (finiteMin (l.filterMap (fun j => if p j x then some (f j x) else none))))
          else finiteMin (l.filterMap (fun j => if p j x then some (f j x) else none))) :=
        ht.ite (hp i) ih.2
      convert hout using 1
      ext x
      by_cases h : p i x
      · simp only [List.filterMap_cons, if_pos h]
        by_cases hl : l.filterMap (fun j => if p j x then some (f j x) else none) = []
        · simp [hl, finiteMin]
        · simp [hl, finiteMin_cons_of_ne_nil _ _ hl]
      · simp [h]

/-- [ Finite row inner products are Borel in both vectors. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: rowDot_measurable
lemma rowDot_measurable :
    Measurable (fun vw : (Fin n → ℝ) × (Fin n → ℝ) => rowDot vw.1 vw.2) := by
  unfold rowDot
  fun_prop

/-- Restriction to the active coordinates is Borel even at boundary states. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: activeMask_measurable
lemma activeMask_measurable :
    Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => activeMask uv.1 uv.2) := by
  unfold activeMask
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_lt (show Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => |uv.1 i|) by fun_prop)
      measurable_const) (by fun_prop) measurable_const

/-- The boundary minimum is Borel in state and direction, including empty-candidate strata. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: boundaryPlus_measurable
lemma boundaryPlus_measurable :
    Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => boundaryPlus uv.1 uv.2) := by
  classical
  let p (i : Fin n) (uv : (Fin n → ℝ) × (Fin n → ℝ)) :=
    |uv.1 i| < 1 ∧ uv.2 i ≠ 0
  let f (i : Fin n) (uv : (Fin n → ℝ) × (Fin n → ℝ)) :=
    if 0 < uv.2 i then (1 - uv.1 i) / uv.2 i else (1 + uv.1 i) / (-uv.2 i)
  have hp (i : Fin n) : MeasurableSet {uv | p i uv} := by
    dsimp [p]
    exact (measurableSet_lt
      (show Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => |uv.1 i|) by fun_prop)
      measurable_const).inter
      (measurableSet_eq_fun
        (show Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => uv.2 i) by fun_prop)
        measurable_const).compl
  have hf (i : Fin n) : Measurable (f i) := by
    dsimp [f]
    apply Measurable.ite
      (measurableSet_lt measurable_const
        (show Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => uv.2 i) by fun_prop))
      <;> fun_prop
  have hm := (finiteMin_guarded_measurable (List.finRange n) p f hp hf).2
  convert hm using 1
  ext uv
  unfold boundaryPlus activeIndices
  congr 1
  rw [List.filterMap_filter]
  apply List.filterMap_congr
  intro i hi
  dsimp [p, f]
  by_cases ha : |uv.1 i| < 1
  · by_cases hv : 0 < uv.2 i
    · simp [ha, hv, ne_of_gt hv]
    · by_cases hn : uv.2 i < 0
      · simp [ha, hv, hn, ne_of_lt hn]
      · have hz : uv.2 i = 0 := le_antisymm (le_of_not_gt hv) (le_of_not_gt hn)
        simp [ha, hz]
  · simp [ha]

/-- The opposite boundary distance is Borel by negating the direction. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: boundaryMinus_measurable
lemma boundaryMinus_measurable :
    Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) => boundaryMinus uv.1 uv.2) := by
  unfold boundaryMinus
  exact boundaryPlus_measurable.comp (measurable_fst.prodMk (by fun_prop))

/-- Every padded seed read is measurable. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingSeed_measurable
lemma roundingSeed_measurable (h : ℕ) : Measurable (fun seeds : RoundingSeeds n =>
    roundingSeed seeds h) := by
  unfold roundingSeed
  split <;> fun_prop

/-- Removing a fixed finite family of measurable rank-one projections is Borel. This uses [the hb hypothesis](hyp:hb), [the hv hypothesis](hyp:hv), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: removeProjections_family_measurable
lemma removeProjections_family_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (b : ι → Ω → Fin n → ℝ) (v : Ω → Fin n → ℝ)
    (hb : ∀ i, Measurable (b i)) (hv : Measurable v) :
    Measurable (fun x => removeProjections (l.map (fun i => b i x)) (v x)) := by
  apply measurable_pi_lambda
  intro j
  unfold removeProjections
  simp only [List.map_map]
  have hs : Measurable (fun x =>
      (l.map (fun i => rowDot (v x) (b i x) * b i x j)).sum) := by
    induction l with
    | nil => exact measurable_const
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((rowDot_measurable.comp (hv.prodMk (hb i))).mul
        ((measurable_pi_apply j).comp (hb i))).add ih
  exact ((measurable_pi_apply j).comp hv).sub hs

/-- The Gram--Schmidt residual norm is Borel for each fixed family of preceding vectors. This uses [the hb hypothesis](hyp:hb), [the hv hypothesis](hyp:hv), [the stated conclusion](goal). -/
-- Generic arithmetic head: invoke this lemma explicitly.
-- @node: residualNorm_family_measurable
lemma residualNorm_family_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (b : ι → Ω → Fin n → ℝ) (v : Ω → Fin n → ℝ)
    (hb : ∀ i, Measurable (b i)) (hv : Measurable v) :
    Measurable (fun x =>
      let w := removeProjections (l.map (fun i => b i x)) (v x)
      Real.sqrt (rowDot w w)) := by
  have hw := removeProjections_family_measurable l b v hb hv
  exact (rowDot_measurable.comp (hw.prodMk hw)).sqrt

/-- The zero-residual branch of Gram--Schmidt is a Borel stratum.](goal) Under [the stated conditions](hyp:hb,hv). This uses [the stated conclusion](goal). -/
-- @node: residualNorm_positive_measurableSet
lemma residualNorm_positive_measurableSet {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (b : ι → Ω → Fin n → ℝ) (v : Ω → Fin n → ℝ)
    (hb : ∀ i, Measurable (b i)) (hv : Measurable v) :
    MeasurableSet {x | 0 < Real.sqrt (rowDot
      (removeProjections (l.map (fun i => b i x)) (v x))
      (removeProjections (l.map (fun i => b i x)) (v x)))} := by
  exact measurableSet_lt measurable_const (residualNorm_family_measurable l b v hb hv)

/-- [ Finite inverse-CDF selection is Borel for measurable candidates, weights, and seed.
Neither positivity nor distinct interval boundaries are needed for this arithmetic fact. This uses [the hv hypothesis](hyp:hv), [the hw hypothesis](hyp:hw), [the ht hypothesis](hyp:ht), [the stated conclusion](goal). -/
@[fun_prop]
-- @node: inverseCDF_family_measurable
lemma inverseCDF_family_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (v : ι → Ω → Fin n → ℝ) (w : ι → Ω → ℝ)
    (t : Ω → ℝ) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (ht : Measurable t) :
    Measurable (fun x => inverseCDF (l.map (fun i => (v i x, w i x))) (t x)) := by
  induction l generalizing t with
  | nil => exact measurable_const
  | cons i l ih =>
    cases l with
    | nil => simpa [inverseCDF] using hv i
    | cons j l =>
      simp only [List.map_cons, inverseCDF]
      exact Measurable.ite (measurableSet_lt ht (hw i)) (hv i)
        (ih (fun x => t x - w i x) (ht.sub (hw i)))

/-- The asymmetric boundary coin probability is Borel in the state and direction. This uses [the stated conclusion](goal). -/
-- Generic arithmetic head: invoke this lemma explicitly.
-- @node: boundaryCoin_probability_measurable
lemma boundaryCoin_probability_measurable :
    Measurable (fun uv : (Fin n → ℝ) × (Fin n → ℝ) =>
      boundaryMinus uv.1 uv.2 / (boundaryPlus uv.1 uv.2 + boundaryMinus uv.1 uv.2)) := by
  exact boundaryMinus_measurable.div (boundaryPlus_measurable.add boundaryMinus_measurable)

/-- A boundary move with a supplied measurable direction and fresh seed is Borel. This uses [the hu hypothesis](hyp:hu), [the hv hypothesis](hyp:hv), [the ht hypothesis](hyp:ht), [the stated conclusion](goal). -/
-- Generic arithmetic head: invoke this lemma explicitly.
-- @node: boundaryMove_measurable
lemma boundaryMove_measurable {Ω : Type*} [MeasurableSpace Ω]
    (u v : Ω → Fin n → ℝ) (t : Ω → ℝ)
    (hu : Measurable u) (hv : Measurable v) (ht : Measurable t) :
    Measurable (fun x =>
      if t x < boundaryMinus (u x) (v x) /
          (boundaryPlus (u x) (v x) + boundaryMinus (u x) (v x))
      then u x + boundaryPlus (u x) (v x) • v x
      else u x - boundaryMinus (u x) (v x) • v x) := by
  have hp := boundaryPlus_measurable.comp (hu.prodMk hv)
  have hm := boundaryMinus_measurable.comp (hu.prodMk hv)
  exact Measurable.ite (measurableSet_lt ht (hm.div (hp.add hm)))
    (hu.add (hp.smul hv)) (hu.sub (hm.smul hv))

/-- A terminal single-coordinate round is Borel, including the threshold tie. This uses [the hu hypothesis](hyp:hu), [the ht hypothesis](hyp:ht), [the stated conclusion](goal). -/
-- Generic arithmetic head: invoke this lemma explicitly.
-- @node: terminalMove_measurable
lemma terminalMove_measurable {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → Fin n → ℝ) (t : Ω → ℝ) (i : Fin n)
    (hu : Measurable u) (ht : Measurable t) :
    Measurable (fun x => Function.update (u x) i
      (if t x < (1 + u x i) / 2 then (1 : ℝ) else -1)) := by
  have hc : Measurable (fun x => (1 + u x i) / 2) := by fun_prop
  have hb : Measurable (fun x => if t x < (1 + u x i) / 2 then (1 : ℝ) else -1) :=
    Measurable.ite (measurableSet_lt ht hc) measurable_const measurable_const
  exact (measurable_update' (a := i)).comp (hu.prodMk hb)

/-- On a stratum with a fixed measurable basis family, the complete nonterminal move is Borel.
The list representation is a local description of a rank stratum, not a rank assumption.](goal) Under [the stated conditions](hyp:hb,hu,ht₁,ht₂,hbs). This uses [the stated conclusion](goal). -/
-- @node: roundingStep_measurable_of_basis_family
lemma roundingStep_measurable_of_basis_family {Ω ι : Type*} [MeasurableSpace Ω]
    (l : List ι) (b : ι → Ω → Fin n → ℝ)
    (a : Ω → Fin (n / 4) → Fin n → ℝ) (q : Ω → ℕ)
    (u : Ω → Fin n → ℝ) (t₁ t₂ : Ω → ℝ)
    (hb : ∀ i, Measurable (b i)) (hu : Measurable u)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂)
    (hbs : ∀ x, nullspaceBasis (a x) (q x) (u x) = l.map (fun i => b i x)) :
    Measurable (fun x => roundingStep (a x) (q x) (u x) (t₁ x) (t₂ x)) := by
  let w (i : ι) (x : Ω) := (boundaryPlus (u x) (b i x) * boundaryMinus (u x) (b i x))⁻¹
  have hw (i : ι) : Measurable (w i) :=
    ((boundaryPlus_measurable.comp (hu.prodMk (hb i))).mul
      (boundaryMinus_measurable.comp (hu.prodMk (hb i)))).inv
  let S (x : Ω) := (l.map (fun i => w i x)).sum
  have hS : Measurable S := by
    dsimp [S]
    clear S hbs
    induction l with
    | nil => exact measurable_const
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hw i).add ih
  let v (x : Ω) := inverseCDF (l.map (fun i => (b i x, w i x / S x))) (t₁ x)
  have hv : Measurable v := inverseCDF_family_measurable l b
    (fun i x => w i x / S x) t₁ hb (fun i => (hw i).div hS) ht₁
  have hmove := boundaryMove_measurable u v t₂ hu hv ht₂
  convert hmove using 1
  ext x
  unfold roundingStep
  rw [hbs]
  have hzip : (l.map (fun i => b i x)).zip
      ((l.map (fun i => w i x)).map (fun z => z / S x)) =
      l.map (fun i => (b i x, w i x / S x)) := by
    have hz (ls : List ι) : (ls.map (fun i => b i x)).zip
        ((ls.map (fun i => w i x)).map (fun z => z / S x)) =
        ls.map (fun i => (b i x, w i x / S x)) := by
      induction ls with
      | nil => rfl
      | cons i ls ih => simp only [List.map_cons, List.zip_cons_cons, ih]
    exact hz l
  simp only [List.map_map, Function.comp_def]
  simp only [List.map_map, S, w, Function.comp_def] at hzip
  rw [hzip]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
