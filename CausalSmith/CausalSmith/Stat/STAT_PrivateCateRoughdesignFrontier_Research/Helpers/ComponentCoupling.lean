module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineCertificate
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PrivateComparison
public import Causalean.Stat.Minimax.OverlapCoupling
/-! Shared-sign graphs, ordered finite components, explicit common-mass couplings and
conditional sparse Hamming/private-output contraction. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ)

/-- Distinct records are adjacent exactly when they share a nonzero active sign contribution. -/
def sharedAdj (x : Fin n → Covariate) (i l : Fin n) : Prop :=
  i ≠ l ∧ ∃ j ∈ activeSigns hL,
    envelope hL (x i)*frame hL j (x i) ≠ 0 ∧
      envelope hL (x l)*frame hL j (x l) ≠ 0
/-- Shared-sign adjacency is symmetric.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: sharedAdj_symm
lemma sharedAdj_symm (x : Fin n → Covariate) : Std.Symm (sharedAdj hL n x) := by
  constructor
  intro i l hil
  rcases hil with ⟨hne, j, hj, hi, hl⟩
  exact ⟨hne.symm, j, hj, hl, hi⟩
/-- Shared-sign adjacency has no loops.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal). -/
-- @node: sharedAdj_irrefl
lemma sharedAdj_irrefl (x : Fin n → Covariate) : Std.Irrefl (sharedAdj hL n x) := by
  constructor
  intro i hii
  exact hii.1 rfl
-- @realizes graph(shared nonzero sign support graph)
/-- The shared-sign graph has the specified adjacency relation on dataset indices. -/
def sharedGraph (x : Fin n → Covariate) : SimpleGraph (Fin n) where
  Adj := sharedAdj hL n x
  symm := sharedAdj_symm hL n x
  loopless := sharedAdj_irrefl hL n x
-- @realizes component(reachable vertex set of a component)
open Classical in
/-- A graph component contains exactly the vertices reachable from its selected vertex. -/
def componentVertices (x : Fin n → Covariate) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l => (sharedGraph hL n x).Reachable i l)
open Classical in
/-- Each component is represented by its least vertex. -/
def componentRoots (x : Fin n → Covariate) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ l, (sharedGraph hL n x).Reachable i l → i ≤ l)
/-- Components are selected by increasing least vertex, so the construction is deterministic. -/
def orderedComponents (x : Fin n → Covariate) : List (Finset (Fin n)) :=
  ((componentRoots hL n x).sort (· ≤ ·)).map (componentVertices hL n x)
-- @realizes m(component cardinality)
/-- Component size is its vertex cardinality. -/
def componentSize (C : Finset (Fin n)) : ℕ := C.card
/-- Component marks are binary treatment-outcome pairs indexed by the component vertices. -/
abbrev Marks {n : ℕ} (C : Finset (Fin n)) := C → Bool × Bool
-- @realizes bmass(null component mark mass array)
/-- The fair component mark law gives every configuration mass four to the power minus component
size. -/
def nullMass (C : Finset (Fin n)) (_z : Marks C) : ℝ := (4 : ℝ)^(-(C.card : ℤ))
-- @realizes amass(alternative component mark mass array from the uniform sign mixture)
/-- The alternative component mark mass averages the conditional Bernoulli products over the
latent signs. -/
def alternativeMass (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) : ℝ :=
  (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam : SignVector hL,
    ∏ i : C, (conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4)
-- @realizes cmass(common component mass array)
/-- The common mass is the pointwise minimum of the alternative and null component masses. -/
def commonMass (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) : ℝ :=
  min (alternativeMass hL n x C z) (nullMass n C z)
-- @realizes alpha(total common component mass)
/-- Total overlap sums the common component masses. -/
def overlapMass (x : Fin n → Covariate) (C : Finset (Fin n)) : ℝ :=
  ∑ z : Marks C, commonMass hL n x C z
-- @realizes QC(conditional alternative component law)
/-- The alternative component measure is the finite measure with the specified alternative mark
masses. -/
def alternativeComponentLaw (x : Fin n → Covariate) (C : Finset (Fin n)) : Measure (Marks C) :=
  ∑ z : Marks C, ENNReal.ofReal (alternativeMass hL n x C z) • Measure.dirac z
-- @realizes PC(conditional null component law)
/-- The null component measure is the finite measure with the specified fair mark masses. -/
def nullComponentLaw (C : Finset (Fin n)) : Measure (Marks C) :=
  ∑ z : Marks C, ENNReal.ofReal (nullMass n C z) • Measure.dirac z

open Classical in
/-- The common-mass coupling combines diagonal common mass with the normalized product of the two
residual masses, omitting the residual when overlap is one. -/
def componentCouplingMass (x : Fin n → Covariate) (C : Finset (Fin n))
    (z w : Marks C) : ℝ :=
  let cz := commonMass hL n x C z
  let cw := commonMass hL n x C w
  let diagonal := if z = w then cz else 0
  if overlapMass hL n x C < 1 then
    diagonal + (alternativeMass hL n x C z-cz)*(nullMass n C w-cw)/
      (1-overlapMass hL n x C)
  else diagonal

/-- The finite component coupling measure has the explicit common-mass joint array. -/
def componentCoupling (x : Fin n → Covariate) (C : Finset (Fin n)) :
    Measure (Marks C × Marks C) :=
  ∑ zw : Marks C × Marks C,
    ENNReal.ofReal (componentCouplingMass hL n x C zw.1 zw.2) • Measure.dirac zw

/-- The joint mark array is the product of the common-mass couplings across the ordered graph
components. -/
def jointMarkMass (x : Fin n → Covariate) (z w : Fin n → Bool × Bool) : ℝ :=
  ((orderedComponents hL n x).map (fun C =>
    componentCouplingMass hL n x C (fun i => z i) (fun i => w i))).prod

/-- The same covariate vector is attached to a vector of treatment-outcome marks. -/
def attachMarks (x : Fin n → Covariate) (z : Fin n → Bool × Bool) : Dataset n :=
  fun i => (x i, (z i).1, (z i).2)

/-- The conditional dataset coupling attaches the same covariates to both sides of the product
component coupling. -/
def conditionalDatasetCoupling (x : Fin n → Covariate) : Measure (Dataset n × Dataset n) :=
  ∑ zw : (Fin n → Bool × Bool) × (Fin n → Bool × Bool),
    ENNReal.ofReal (jointMarkMass hL n x zw.1 zw.2) •
      Measure.dirac (attachMarks n x zw.1, attachMarks n x zw.2)
-- @node: def:common-mass-coupling
-- @realizes Gamma(product common-mass component coupling with shared uniform covariates)
/-- The dataset coupling integrates the ordered product of explicit component couplings over
shared uniform covariates. -/
def commonMassCoupling : Measure (Dataset n × Dataset n) :=
  (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
    (conditionalDatasetCoupling hL n)

/-- The full conditional mark mass averages the dataset Bernoulli likelihood product uniformly
over all latent signs. -/
def fullAlternativeMass (x : Fin n → Covariate) (z : Fin n → Bool × Bool) : ℝ :=
  (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam : SignVector hL,
    ∏ i : Fin n, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4

/-- The four conditional mark masses sum to one at every covariate and sign vector. [The displayed conclusion](goal) follows. -/
-- @node: conditionalLikelihood_mark_sum
lemma conditionalLikelihood_mark_sum (lam : SignVector hL) (x : Covariate) :
    (∑ z : Bool × Bool, conditionalLikelihood hL lam x z.1 z.2 / 4) = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, conditionalLikelihood,
    bernoulliMass, Bool.false_eq_true, if_true, if_false]
  ring

include hhL in
/-- Every alternative component mass is nonnegative.  [the theorem's stated inputs and assumptions](hyp:z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: alternativeMass_nonneg
lemma alternativeMass_nonneg (x : Fin n → Covariate) (C : Finset (Fin n))
    (z : Marks C) : 0 ≤ alternativeMass hL n x C z := by
  apply mul_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _))
  apply Finset.sum_nonneg
  intro lam _
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (conditionalLikelihood_nonneg hL hhL lam (x i) (z i).1 (z i).2)
    (by norm_num)

/-- Summing the finite component array gives total mass one, including the empty component. [The displayed conclusion](goal) follows. -/
-- @node: alternativeMass_sum
lemma alternativeMass_sum (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ z : Marks C, alternativeMass hL n x C z) = 1 := by
  classical
  simp only [alternativeMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hp (lam : SignVector hL) :
      (∑ z : Marks C, ∏ i : C, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4) = 1 := by
    rw [← Fintype.prod_sum (fun (i : C) (z : Bool × Bool) =>
      conditionalLikelihood hL lam (x i) z.1 z.2 / 4)]
    simp only [conditionalLikelihood_mark_sum, Finset.prod_const_one]
  simp_rw [hp]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact sign_weight_real_normalization hL

/-- Every fair component mass is positive. [The displayed conclusion](goal) follows. -/
-- @node: nullMass_pos
lemma nullMass_pos (C : Finset (Fin n)) (z : Marks C) : 0 < nullMass n C z := by
  exact zpow_pos (by norm_num : (0 : ℝ) < 4) _

include hhL in
/-- A singleton alternative array equals the fair array by the exact sign cancellations.  [the theorem's stated inputs and assumptions](hyp:x,C,hc,z), and [the asserted conclusion follows](goal). -/
-- @node: alternativeMass_eq_nullMass_of_card_one
lemma alternativeMass_eq_nullMass_of_card_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hc : C.card = 1) (z : Marks C) :
    alternativeMass hL n x C z = nullMass n C z := by
  classical
  rcases Finset.card_eq_one.mp hc with ⟨i, rfl⟩
  let j : ({i} : Finset (Fin n)) := ⟨i, Finset.mem_singleton_self i⟩
  let : Subsingleton ({i} : Finset (Fin n)) := ⟨by
    intro a b
    apply Subtype.ext
    exact (Finset.mem_singleton.mp a.property).trans
      (Finset.mem_singleton.mp b.property).symm⟩
  have hp (lam : SignVector hL) :
      (∏ a : ({i} : Finset (Fin n)), conditionalLikelihood hL lam (x a) (z a).1 (z a).2 / 4) =
        conditionalLikelihood hL lam (x j) (z j).1 (z j).2 / 4 :=
    Fintype.prod_subsingleton _ j
  simp only [alternativeMass, hp, ← Finset.sum_div,
    conditionalLikelihood_sign_sum_exact hL hhL, nullMass, Finset.card_singleton]
  rw [← mul_div_assoc, sign_weight_real_normalization]
  norm_num

include hhL in
/-- Singleton component measures coincide pointwise, including at support boundaries.  [the theorem's stated inputs and assumptions](hyp:C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: alternativeComponentLaw_eq_null_of_card_one
lemma alternativeComponentLaw_eq_null_of_card_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hc : C.card = 1) :
    alternativeComponentLaw hL n x C = nullComponentLaw n C := by
  simp only [alternativeComponentLaw, nullComponentLaw,
    alternativeMass_eq_nullMass_of_card_one hL hhL n x C hc]

include hhL in
/-- Common component mass lies between zero and each marginal array.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C,z). -/
-- @node: commonMass_bounds
lemma commonMass_bounds (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) :
    0 ≤ commonMass hL n x C z ∧
      commonMass hL n x C z ≤ alternativeMass hL n x C z ∧
      commonMass hL n x C z ≤ nullMass n C z := by
  exact ⟨le_min (alternativeMass_nonneg hL hhL n x C z) (nullMass_pos n C z).le,
    min_le_left _ _, min_le_right _ _⟩

include hhL in
/-- The total common component mass is a probability overlap between zero and one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: overlapMass_range
lemma overlapMass_range (x : Fin n → Covariate) (C : Finset (Fin n)) :
    overlapMass hL n x C ∈ Icc 0 1 := by
  constructor
  · exact Finset.sum_nonneg (fun z _ => (commonMass_bounds hL hhL n x C z).1)
  · calc
      _ ≤ ∑ z : Marks C, alternativeMass hL n x C z :=
        Finset.sum_le_sum (fun z _ => (commonMass_bounds hL hhL n x C z).2.1)
      _ = 1 := alternativeMass_sum hL n x C

/-- The fair component array sums to one for every finite component.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:C). -/
-- @node: nullMass_sum
lemma nullMass_sum (C : Finset (Fin n)) : (∑ z : Marks C, nullMass n C z) = 1 := by
  classical
  simp only [nullMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]

/-- The first residual array has mass one minus the overlap.  [the theorem's stated inputs and assumptions](hyp:x,C), and [the asserted conclusion follows](goal). -/
-- @node: alternativeResidual_sum
lemma alternativeResidual_sum (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ z : Marks C, (alternativeMass hL n x C z-commonMass hL n x C z)) =
      1-overlapMass hL n x C := by
  rw [Finset.sum_sub_distrib, alternativeMass_sum]
  rfl

/-- The second residual array has the same mass one minus the overlap. [The displayed conclusion](goal) follows. -/
-- @node: nullResidual_sum
lemma nullResidual_sum (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ z : Marks C, (nullMass n C z-commonMass hL n x C z)) =
      1-overlapMass hL n x C := by
  rw [Finset.sum_sub_distrib, nullMass_sum]
  rfl

include hhL in
/-- At full overlap the alternative array equals the common array.  [the theorem's stated inputs and assumptions](hyp:C,ha,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: alternativeMass_eq_common_of_overlap_one
lemma alternativeMass_eq_common_of_overlap_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (ha : overlapMass hL n x C = 1) (z : Marks C) :
    alternativeMass hL n x C z = commonMass hL n x C z := by
  have hs : (∑ w : Marks C, (alternativeMass hL n x C w-commonMass hL n x C w)) = 0 := by
    rw [alternativeResidual_sum, ha, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sub_nonneg.mpr
    (commonMass_bounds hL hhL n x C w).2.1)).mp hs z (Finset.mem_univ z)
  exact sub_eq_zero.mp hz

include hhL in
/-- At full overlap the null array equals the common array.  [the theorem's stated inputs and assumptions](hyp:C,ha,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: nullMass_eq_common_of_overlap_one
lemma nullMass_eq_common_of_overlap_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (ha : overlapMass hL n x C = 1) (z : Marks C) :
    nullMass n C z = commonMass hL n x C z := by
  have hs : (∑ w : Marks C, (nullMass n C w-commonMass hL n x C w)) = 0 := by
    rw [nullResidual_sum, ha, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sub_nonneg.mpr
    (commonMass_bounds hL hhL n x C w).2.2)).mp hs z (Finset.mem_univ z)
  exact sub_eq_zero.mp hz

include hhL in
/-- The explicit common-mass joint array is nonnegative in both overlap branches.  [the theorem's stated inputs and assumptions](hyp:C,z,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCouplingMass_nonneg
lemma componentCouplingMass_nonneg (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z w : Marks C) : 0 ≤ componentCouplingMass hL n x C z w := by
  classical
  have hz := commonMass_bounds hL hhL n x C z
  have hw := commonMass_bounds hL hhL n x C w
  dsimp [componentCouplingMass]
  split_ifs with ha he he
  · exact add_nonneg hz.1 (div_nonneg
      (mul_nonneg (sub_nonneg.mpr hz.2.1) (sub_nonneg.mpr hw.2.2)) (by linarith))
  · rw [zero_add]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hz.2.1) (sub_nonneg.mpr hw.2.2)) (by linarith)
  · exact hz.1
  · exact le_rfl

include hhL in
/-- Summing a row of the explicit coupling recovers the alternative component mass.  [the theorem's stated inputs and assumptions](hyp:C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCouplingMass_row_sum
lemma componentCouplingMass_row_sum (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) :
    (∑ w : Marks C, componentCouplingMass hL n x C z w) = alternativeMass hL n x C z := by
  classical
  by_cases ha : overlapMass hL n x C < 1
  · have hd : 1-overlapMass hL n x C ≠ 0 := by linarith
    simp only [componentCouplingMass, if_pos ha, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.mul_sum]
    rw [nullResidual_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    field_simp
    ring
  · have he : overlapMass hL n x C = 1 :=
      le_antisymm (overlapMass_range hL hhL n x C).2 (le_of_not_gt ha)
    simp only [componentCouplingMass, if_neg ha, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact (alternativeMass_eq_common_of_overlap_one hL hhL n x C he z).symm

include hhL in
/-- Summing a column of the explicit coupling recovers the null component mass.  [the theorem's stated inputs and assumptions](hyp:C,w), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCouplingMass_column_sum
lemma componentCouplingMass_column_sum (x : Fin n → Covariate)
    (C : Finset (Fin n)) (w : Marks C) :
    (∑ z : Marks C, componentCouplingMass hL n x C z w) = nullMass n C w := by
  classical
  by_cases ha : overlapMass hL n x C < 1
  · have hd : 1-overlapMass hL n x C ≠ 0 := by linarith
    simp only [componentCouplingMass, if_pos ha, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_mul]
    rw [alternativeResidual_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
    ring
  · have he : overlapMass hL n x C = 1 :=
      le_antisymm (overlapMass_range hL hhL n x C).2 (le_of_not_gt ha)
    simp only [componentCouplingMass, if_neg ha, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact (nullMass_eq_common_of_overlap_one hL hhL n x C he w).symm

include hhL in
/-- The explicit finite coupling has the alternative component law as first marginal.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: componentCoupling_map_fst
lemma componentCoupling_map_fst (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (componentCoupling hL n x C).map Prod.fst = alternativeComponentLaw hL n x C := by
  classical
  have hr (z : Marks C) :
      (∑ w : Marks C, ENNReal.ofReal (componentCouplingMass hL n x C z w)) =
        ENNReal.ofReal (alternativeMass hL n x C z) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun w _ => componentCouplingMass_nonneg hL hhL n x C z w),
      componentCouplingMass_row_sum hL hhL]
  ext S hS
  rw [Measure.map_apply measurable_fst hS]
  simp only [componentCoupling, alternativeComponentLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ w : Marks C, ENNReal.ofReal (componentCouplingMass hL n x C z w) *
      S.indicator 1 z) = ENNReal.ofReal (alternativeMass hL n x C z) * S.indicator 1 z
  rw [← Finset.sum_mul, hr]

include hhL in
/-- The explicit finite coupling has the fair component law as second marginal.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: componentCoupling_map_snd
lemma componentCoupling_map_snd (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (componentCoupling hL n x C).map Prod.snd = nullComponentLaw n C := by
  classical
  have hc (w : Marks C) :
      (∑ z : Marks C, ENNReal.ofReal (componentCouplingMass hL n x C z w)) =
        ENNReal.ofReal (nullMass n C w) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun z _ => componentCouplingMass_nonneg hL hhL n x C z w),
      componentCouplingMass_column_sum hL hhL]
  ext S hS
  rw [Measure.map_apply measurable_snd hS]
  simp only [componentCoupling, nullComponentLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ z : Marks C, ENNReal.ofReal (componentCouplingMass hL n x C z w) *
      S.indicator 1 w) = ENNReal.ofReal (nullMass n C w) * S.indicator 1 w
  rw [← Finset.sum_mul, hc]

/-- The fair finite component measure is a probability measure.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:C). -/
-- @node: nullComponentLaw_isProbabilityMeasure
lemma nullComponentLaw_isProbabilityMeasure (C : Finset (Fin n)) :
    IsProbabilityMeasure (nullComponentLaw n C) := by
  constructor
  simp only [nullComponentLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => (nullMass_pos n C z).le), nullMass_sum]
  exact ENNReal.ofReal_one

include hhL in
/-- The common-mass component construction is a probability coupling of its two mark laws.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: componentCoupling_isCoupling
lemma componentCoupling_isCoupling (x : Fin n → Covariate) (C : Finset (Fin n)) :
    Causalean.Stat.IsCoupling (componentCoupling hL n x C)
      (alternativeComponentLaw hL n x C) (nullComponentLaw n C) := by
  have hs := componentCoupling_map_snd hL hhL n x C
  have hprob : IsProbabilityMeasure (componentCoupling hL n x C) := by
    constructor
    have hm := congrArg (fun mu : Measure (Marks C) => mu Set.univ) hs
    rw [Measure.map_apply measurable_snd MeasurableSet.univ] at hm
    let := nullComponentLaw_isProbabilityMeasure n C
    simpa using hm
  exact ⟨hprob, componentCoupling_map_fst hL hhL n x C, hs⟩

/-- At any mark vector one of the two residual masses is zero.  [the theorem's stated inputs and assumptions](hyp:C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentResidual_diagonal_zero
lemma componentResidual_diagonal_zero (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) :
    (alternativeMass hL n x C z-commonMass hL n x C z) *
      (nullMass n C z-commonMass hL n x C z) = 0 := by
  dsimp [commonMass]
  rcases le_total (alternativeMass hL n x C z) (nullMass n C z) with h | h
  · rw [min_eq_left h, sub_self, zero_mul]
  · rw [min_eq_right h, sub_self, mul_zero]

/-- The diagonal entry of the joint array is exactly the common mass in either branch.  [the theorem's stated inputs and assumptions](hyp:C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCouplingMass_diagonal
lemma componentCouplingMass_diagonal (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) :
    componentCouplingMass hL n x C z z = commonMass hL n x C z := by
  classical
  simp only [componentCouplingMass, if_true, componentResidual_diagonal_zero,
    zero_div, add_zero, ite_self]

include hhL in
/-- The component coupling's agreement probability is precisely its common mass overlap.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: componentCoupling_diagonal_mass
lemma componentCoupling_diagonal_mass (x : Fin n → Covariate) (C : Finset (Fin n)) :
    componentCoupling hL n x C {zw | zw.1 = zw.2} = ENNReal.ofReal (overlapMass hL n x C) := by
  classical
  simp only [componentCoupling, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply, Fintype.sum_prod_type, Set.indicator,
    Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, componentCouplingMass_diagonal]
  exact (ENNReal.ofReal_sum_of_nonneg
    (fun z _ => (commonMass_bounds hL hhL n x C z).1)).symm

/-- The absolute array difference is twice the mass outside their pointwise overlap. [The displayed conclusion](goal) follows. -/
-- @node: componentMass_abs_sum
lemma componentMass_abs_sum (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ z : Marks C, |alternativeMass hL n x C z-nullMass n C z|) =
      2*(1-overlapMass hL n x C) := by
  have hp (z : Marks C) :
      |alternativeMass hL n x C z-nullMass n C z| =
        alternativeMass hL n x C z + nullMass n C z - 2*commonMass hL n x C z := by
    dsimp [commonMass]
    rcases le_total (alternativeMass hL n x C z) (nullMass n C z) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    alternativeMass_sum, nullMass_sum]
  dsimp [overlapMass]
  ring

include hhL in
/-- Singleton components have full common-mass overlap.  [the theorem's stated inputs and assumptions](hyp:C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: overlapMass_eq_one_of_card_one
lemma overlapMass_eq_one_of_card_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hc : C.card = 1) : overlapMass hL n x C = 1 := by
  simp only [overlapMass, commonMass,
    alternativeMass_eq_nullMass_of_card_one hL hhL n x C hc, min_self]
  exact nullMass_sum n C

include hhL in
/-- The explicit component coupling fails with probability exactly one minus its overlap.  [the theorem's stated inputs and assumptions](hyp:C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCoupling_disagreement_mass
lemma componentCoupling_disagreement_mass (x : Fin n → Covariate)
    (C : Finset (Fin n)) :
    componentCoupling hL n x C {zw | zw.1 ≠ zw.2} =
      ENNReal.ofReal (1-overlapMass hL n x C) := by
  letI := (componentCoupling_isCoupling hL hhL n x C).isProbabilityMeasure
  have hD : MeasurableSet {zw : Marks C × Marks C | zw.1 = zw.2} := measurableSet_eq_fun measurable_fst measurable_snd
  change componentCoupling hL n x C ({zw | zw.1 = zw.2}ᶜ) = _
  rw [measure_compl hD (measure_ne_top _ _), measure_univ,
    componentCoupling_diagonal_mass hL hhL]
  simpa only [ENNReal.ofReal_one] using
    (ENNReal.ofReal_sub 1 (overlapMass_range hL hhL n x C).1).symm

include hhL in
/-- Singleton couplings agree almost surely, including support-boundary singletons.  [the theorem's stated inputs and assumptions](hyp:C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCoupling_disagreement_zero_of_card_one
lemma componentCoupling_disagreement_zero_of_card_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hc : C.card = 1) :
    componentCoupling hL n x C {zw | zw.1 ≠ zw.2} = 0 := by
  rw [componentCoupling_disagreement_mass hL hhL,
    overlapMass_eq_one_of_card_one hL hhL n x C hc, sub_self, ENNReal.ofReal_zero]

include hhL in
/-- A component can change at most its cardinality on the coupling's failure event.  [the theorem's stated inputs and assumptions](hyp:C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCoupling_hamming_cost_le
lemma componentCoupling_hamming_cost_le (x : Fin n → Covariate)
    (C : Finset (Fin n)) :
    (∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C) ≤
      (C.card : ℝ≥0∞) * ENNReal.ofReal (1-overlapMass hL n x C) := by
  classical
  calc
    _ ≤ ∫⁻ zw, ({zw : Marks C × Marks C | zw.1 ≠ zw.2}.indicator
        (fun _ => (C.card : ℝ≥0∞))) zw ∂componentCoupling hL n x C := by
      apply lintegral_mono
      intro zw
      by_cases heq : zw.1 = zw.2
      · simp [heq]
      · rw [Set.indicator_of_mem heq]
        exact Nat.cast_le.mpr (by simpa using
          (hammingDist_le_card_fintype (x := zw.1) (y := zw.2)))
    _ = _ := by
      rw [lintegral_indicator (show MeasurableSet {zw : Marks C × Marks C | zw.1 ≠ zw.2} from
        (measurableSet_eq_fun measurable_fst measurable_snd).compl), lintegral_const,
        Measure.restrict_apply_univ, componentCoupling_disagreement_mass hL hhL]

include hhL in
/-- The component transport cost is at most half its size times the absolute array difference.  [the theorem's stated inputs and assumptions](hyp:C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCoupling_hamming_cost_le_abs_sum
lemma componentCoupling_hamming_cost_le_abs_sum (x : Fin n → Covariate)
    (C : Finset (Fin n)) :
    (∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C) ≤
      ENNReal.ofReal ((C.card : ℝ)/2 *
        ∑ z : Marks C, |alternativeMass hL n x C z-nullMass n C z|) := by
  rw [componentMass_abs_sum]
  have heq : (C.card : ℝ)/2 * (2*(1-overlapMass hL n x C)) =
      (C.card : ℝ)*(1-overlapMass hL n x C) := by ring
  rw [heq, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact componentCoupling_hamming_cost_le hL hhL n x C

include hhL in
/-- Singleton components contribute no expected changed marks to the dataset coupling.  [the theorem's stated inputs and assumptions](hyp:C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentCoupling_hamming_cost_zero_of_card_one
lemma componentCoupling_hamming_cost_zero_of_card_one (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hc : C.card = 1) :
    (∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C) = 0 := by
  apply le_antisymm _ bot_le
  have hcost := componentCoupling_hamming_cost_le hL hhL n x C
  rw [overlapMass_eq_one_of_card_one hL hhL n x C hc, sub_self,
    ENNReal.ofReal_zero, mul_zero] at hcost
  exact hcost

end CausalSmith.Stat.PrivateCateRoughdesign
