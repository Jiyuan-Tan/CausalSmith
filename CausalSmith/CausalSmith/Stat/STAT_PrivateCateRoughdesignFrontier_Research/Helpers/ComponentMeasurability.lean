module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentCoupling
/-! Borel regularity of finite common-mass arrays, fixed-component couplings and the full
conditional dataset coupling, using finitely many labeled-graph strata. These certificates
include the overlap-one branch and require no radius restrictions. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (n : ℕ)

/-- Fixing the two marks leaves a Borel conditional likelihood in the covariate. [The displayed conclusion](goal) follows. -/
-- @node: measurable_conditionalLikelihood_covariate
@[fun_prop] lemma measurable_conditionalLikelihood_covariate (lam : SignVector hL)
    (a y : Bool) : Measurable (fun x : Covariate => conditionalLikelihood hL lam x a y) := by
  cases a <;> cases y <;> simp only [conditionalLikelihood, bernoulliMass,
    Bool.false_eq_true, if_false, if_true] <;> fun_prop

/-- Each fixed-component alternative mass is Borel in the full covariate vector. [The displayed conclusion](goal) follows. -/
-- @node: measurable_alternativeMass
@[fun_prop] lemma measurable_alternativeMass (C : Finset (Fin n)) (z : Marks C) :
    Measurable (fun x => alternativeMass hL n x C z) := by
  unfold alternativeMass
  fun_prop

/-- Taking the pointwise common part preserves Borel regularity. [The displayed conclusion](goal) follows. -/
-- @node: measurable_commonMass
@[fun_prop] lemma measurable_commonMass (C : Finset (Fin n)) (z : Marks C) :
    Measurable (fun x => commonMass hL n x C z) := by
  unfold commonMass
  fun_prop

/-- The finite sum of common masses is Borel in the covariates. [The displayed conclusion](goal) follows. -/
-- @node: measurable_overlapMass
@[fun_prop] lemma measurable_overlapMass (C : Finset (Fin n)) :
    Measurable (fun x => overlapMass hL n x C) := by
  unfold overlapMass
  fun_prop

/-- The explicit joint mass is Borel, including the branch where overlap is one. [The displayed conclusion](goal) follows. -/
-- @node: measurable_componentCouplingMass
@[fun_prop] lemma measurable_componentCouplingMass (C : Finset (Fin n)) (z w : Marks C) :
    Measurable (fun x => componentCouplingMass hL n x C z w) := by
  classical
  dsimp only [componentCouplingMass]
  have hd : Measurable (fun x : Fin n → Covariate =>
      if z = w then commonMass hL n x C z else 0) := by
    by_cases hzw : z = w <;> simp only [hzw, if_true, if_false] <;> fun_prop
  apply Measurable.ite
    (measurableSet_lt (measurable_overlapMass hL n C) measurable_const) _ hd
  exact hd.add (((measurable_alternativeMass hL n C z).sub
    (measurable_commonMass hL n C z)).mul
    (measurable_const.sub (measurable_commonMass hL n C w)) |>.div
    (measurable_const.sub (measurable_overlapMass hL n C)))

/-- The full sign-mixture conditional mass is Borel for each fixed dataset mark vector. [The displayed conclusion](goal) follows. -/
-- @node: measurable_fullAlternativeMass
@[fun_prop] lemma measurable_fullAlternativeMass (z : Fin n → Bool × Bool) :
    Measurable (fun x => fullAlternativeMass hL n x z) := by
  unfold fullAlternativeMass
  fun_prop

/-- Attaching fixed marks to covariates is a Borel map into the dataset space. [The displayed conclusion](goal) follows. -/
-- @node: measurable_attachMarks
@[fun_prop] lemma measurable_attachMarks (z : Fin n → Bool × Bool) :
    Measurable (fun x => attachMarks n x z) := by
  unfold attachMarks
  fun_prop

/-- The alternative finite component measure varies measurably with the covariates. [The displayed conclusion](goal) follows. -/
-- @node: measurable_alternativeComponentLaw
@[fun_prop] lemma measurable_alternativeComponentLaw (C : Finset (Fin n)) :
    Measurable (fun x => alternativeComponentLaw hL n x C) := by
  unfold alternativeComponentLaw
  fun_prop

/-- The common-mass coupling of a fixed component varies measurably with the covariates. [The displayed conclusion](goal) follows. -/
-- @node: measurable_componentCoupling
@[fun_prop] lemma measurable_componentCoupling (C : Finset (Fin n)) :
    Measurable (fun x => componentCoupling hL n x C) := by
  unfold componentCoupling
  fun_prop

/-- Sharing an active sign is a Borel predicate, including all support boundaries. [The displayed conclusion](goal) follows. -/
-- @node: measurableSet_sharedAdj
lemma measurableSet_sharedAdj (i l : Fin n) :
    MeasurableSet {x : Fin n → Covariate | sharedAdj hL n x i l} := by
  classical
  change MeasurableSet {x : Fin n → Covariate | i ≠ l ∧ ∃ j ∈ activeSigns hL,
    envelope hL (x i)*frame hL j (x i) ≠ 0 ∧
    envelope hL (x l)*frame hL j (x l) ≠ 0}
  have hc : MeasurableSet {x : Fin n → Covariate | i ≠ l} := by
    by_cases h : i = l
    · convert MeasurableSet.empty (α := Fin n → Covariate) using 1; ext x; simp [h]
    · convert MeasurableSet.univ (α := Fin n → Covariate) using 1; ext x; simp [h]
  apply hc.inter
  change MeasurableSet {x : Fin n → Covariate | ∃ j ∈ activeSigns hL,
    envelope hL (x i)*frame hL j (x i) ≠ 0 ∧
    envelope hL (x l)*frame hL j (x l) ≠ 0}
  rw [show {x : Fin n → Covariate | ∃ j ∈ activeSigns hL,
    envelope hL (x i)*frame hL j (x i) ≠ 0 ∧
    envelope hL (x l)*frame hL j (x l) ≠ 0} =
    ⋃ j : (activeSigns hL), {x | envelope hL (x i)*frame hL j (x i) ≠ 0 ∧
      envelope hL (x l)*frame hL j (x l) ≠ 0} by
        ext x
        constructor
        · rintro ⟨j, hj, hi, hl⟩
          exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hi, hl⟩
        · intro hx
          obtain ⟨j, hi, hl⟩ := Set.mem_iUnion.mp hx
          exact ⟨j, j.property, hi, hl⟩]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.inter <;>
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl

/-- Each labeled graph occupies a Borel stratum of the covariate-vector space. [The displayed conclusion](goal) follows. -/
-- @node: measurableSet_sharedGraph_eq
lemma measurableSet_sharedGraph_eq (G : SimpleGraph (Fin n)) :
    MeasurableSet {x : Fin n → Covariate | sharedGraph hL n x = G} := by
  have heq : {x : Fin n → Covariate | sharedGraph hL n x = G} =
      {x | ∀ i l, sharedAdj hL n x i l ↔ G.Adj i l} := by
    ext x
    constructor
    · intro h i l
      change (sharedGraph hL n x).Adj i l ↔ G.Adj i l
      rw [h]
    · intro h
      exact SimpleGraph.ext (funext fun i => funext fun l => propext (h i l))
  rw [heq]
  rw [show {x : Fin n → Covariate | ∀ i l, sharedAdj hL n x i l ↔ G.Adj i l} =
    ⋂ i, ⋂ l, {x | sharedAdj hL n x i l ↔ G.Adj i l} by ext x; simp]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro l
  by_cases h : G.Adj i l
  · simpa only [h, iff_true] using measurableSet_sharedAdj hL n i l
  · simp only [h, iff_false]
    convert (measurableSet_sharedAdj hL n i l).compl using 1
    ext x
    rfl

open Classical in
/-- The deterministic ordered components of a fixed graph use increasing least vertices. -/
-- @node: componentsOfGraph
def componentsOfGraph (G : SimpleGraph (Fin n)) : List (Finset (Fin n)) :=
  ((Finset.univ.filter (fun i => ∀ l, G.Reachable i l → i ≤ l)).sort (· ≤ ·)).map
    (fun i => Finset.univ.filter (fun l => G.Reachable i l))

/-- Freezing the shared-sign graph also freezes its ordered vertex lists.  [the theorem's stated inputs and assumptions](hyp:G,hx), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_eq_of_sharedGraph_eq
lemma orderedComponents_eq_of_sharedGraph_eq (x : Fin n → Covariate)
    (G : SimpleGraph (Fin n)) (hx : sharedGraph hL n x = G) :
    orderedComponents hL n x = componentsOfGraph n G := by
  subst G
  rfl

/-- A product over any fixed list of components is a Borel joint mark mass.  [the theorem's stated inputs and assumptions](hyp:z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:Cs). -/
-- @node: measurable_fixedComponentProduct
lemma measurable_fixedComponentProduct (Cs : List (Finset (Fin n)))
    (z w : Fin n → Bool × Bool) :
    Measurable (fun x => (Cs.map (fun C =>
      componentCouplingMass hL n x C (fun i => z i) (fun i => w i))).prod) := by
  induction Cs with
  | nil => simpa using (measurable_const : Measurable (fun _ : Fin n → Covariate => (1 : ℝ)))
  | cons C Cs ih =>
    convert (measurable_componentCouplingMass hL n C
      (fun i => z i) (fun i => w i)).mul ih using 1
    funext x
    simp only [List.map_cons, List.prod_cons, Pi.mul_apply]

/-- The varying-graph joint array is Borel by its finite decomposition into graph strata. [The displayed conclusion](goal) follows. -/
-- @node: measurable_jointMarkMass
@[fun_prop] lemma measurable_jointMarkMass (z w : Fin n → Bool × Bool) :
    Measurable (fun x => jointMarkMass hL n x z w) := by
  classical
  have hm : Measurable (fun x => ∑ G : SimpleGraph (Fin n),
      {x | sharedGraph hL n x = G}.indicator (fun x =>
        ((componentsOfGraph n G).map (fun C =>
          componentCouplingMass hL n x C (fun i => z i) (fun i => w i))).prod) x) := by
    apply Finset.measurable_sum
    intro G _
    exact (measurable_fixedComponentProduct hL n (componentsOfGraph n G) z w).indicator
      (measurableSet_sharedGraph_eq hL n G)
  convert hm using 1
  funext x
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp only [jointMarkMass,
    orderedComponents_eq_of_sharedGraph_eq hL n x (sharedGraph hL n x) rfl]

/-- The explicit conditional dataset coupling is Borel on every covariate vector. [The displayed conclusion](goal) follows. -/
-- @node: measurable_conditionalDatasetCoupling
@[fun_prop] lemma measurable_conditionalDatasetCoupling :
    Measurable (conditionalDatasetCoupling hL n) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [conditionalDatasetCoupling, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.measurable_sum
  intro zw _
  apply Measurable.mul ((measurable_jointMarkMass hL n zw.1 zw.2).ennreal_ofReal)
  simp only [Measure.dirac_apply' _ hE]
  exact measurable_const.indicator (hE.preimage
    ((measurable_attachMarks n zw.1).prodMk (measurable_attachMarks n zw.2)))

end CausalSmith.Stat.PrivateCateRoughdesign
