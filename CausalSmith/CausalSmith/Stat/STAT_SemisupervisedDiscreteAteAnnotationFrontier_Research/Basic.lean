module
public import Causalean.Stat.Sample
public import Causalean.Stat.Sample.PiTransport
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Semi-supervised discrete ATE annotation frontier

This file defines the finite two-sample experiment, its potential-outcome
overlay, the observed-data ATE functional, and the two minimax risks used by
the annotation-frontier results.  The finite PMF presentation is intentional:
the Causalean PO and minimax APIs are measure-theoretic and kernel-indexed,
whereas this paper needs an explicit finite labeled/auxiliary product law.
-/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- One complete record `(X,A,Y)` on the finite alphabet.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev Obs (d : Nat) := Fin d × Bool × Bool
  -- @realizes X(carrier Fin d)
  -- @realizes A(carrier Bool)
  -- @realizes Y(carrier Bool)

/-- One outcome-unlabeled record `(X,A)`.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev AuxObs (d : Nat) := Fin d × Bool

/-- A law of a complete finite record. -/
structure DiscreteLaw (d : Nat) where
  pmf : PMF (Obs d) -- @realizes P(probability law on Fin d × Bool × Bool)

/-- The measure associated with a finite observed-data law.  [the stated conditions](hyp:P) [the stated conclusion](goal). -/
noncomputable def obsLaw {d : Nat} (P : DiscreteLaw d) : Measure (Obs d) :=
  P.pmf.toMeasure
/-- [the stated conditions](hyp:P) defines [the specified object](goal). -/

instance {d : Nat} (P : DiscreteLaw d) : IsProbabilityMeasure (obsLaw P) := by
  unfold obsLaw
  infer_instance

/-- The probability mass of one complete atom.  [the stated conditions](hyp:P,x,a,y) [the stated conclusion](goal). -/
noncomputable def jointMass {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a y : Bool) : Real :=
  (P.pmf (x, a, y)).toReal

/-- The covariate-cell mass `P(X=x)`.  [the stated conditions](hyp:P,x) [the stated conclusion](goal). -/
noncomputable def cellMass {d : Nat} (P : DiscreteLaw d) (x : Fin d) : Real :=
  ∑ a : Bool, ∑ y : Bool, jointMass P x a y
  -- @realizes p_x(p_x = P(X=x); range [0,1] inherited from PMF)

/-- The treatment-covariate cell mass `P(X=x,A=a)`.  [the stated conditions](hyp:P,x,a) [the stated conclusion](goal). -/
noncomputable def armMass {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) : Real :=
  ∑ y : Bool, jointMass P x a y
  -- @realizes s_{ax}(s_ax = P(X=x,A=a); range [0,1] inherited from PMF)

/-- The propensity, totalized to zero when `P(X=x)=0`.  [the stated conditions](hyp:P,x) [the stated conclusion](goal). -/
noncomputable def propensity {d : Nat} (P : DiscreteLaw d) (x : Fin d) : Real :=
  armMass P x true / cellMass P x
  -- @realizes e_x(e_x = P(A=1|X=x); null cells use total division)

/-- The binary outcome regression, totalized to zero on a null arm-cell.  [the stated conditions](hyp:P,a,x) [the stated conclusion](goal). -/
noncomputable def outcomeMean {d : Nat} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) : Real :=
  jointMass P x a true / armMass P x a
  -- @realizes mu_{ax}(mu_ax = E[Y|A=a,X=x]; null cells use total division)

-- @node: jointMass_mem_unitInterval
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma jointMass_mem_unitInterval {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a y : Bool) : jointMass P x a y ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_le_coe_of_le_coe (P.pmf.coe_le_one (x, a, y))

-- @node: cellMass_mem_unitInterval
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma cellMass_mem_unitInterval {d : Nat} (P : DiscreteLaw d) (x : Fin d) :
    cellMass P x ∈ Set.Icc (0 : Real) 1 := by
  have hsum : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : Real))).symm
  constructor
  · exact Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P x a y).1
  · calc
      cellMass P x ≤ ∑ x' : Fin d, cellMass P x' := by
        exact Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P i a y).1)
          (Finset.mem_univ x)
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := hsum

-- @node: outcomeMean_mem_unitInterval
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma outcomeMean_mem_unitInterval {d : Nat} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) : outcomeMean P a x ∈ Set.Icc (0 : Real) 1 := by
  have hj_nonneg : 0 ≤ jointMass P x a true :=
    (jointMass_mem_unitInterval P x a true).1
  have harm_nonneg : 0 ≤ armMass P x a := by
    exact Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P x a y).1
  have hj_le : jointMass P x a true ≤ armMass P x a := by
    simp [armMass]
    exact (jointMass_mem_unitInterval P x a false).1
  constructor
  · exact div_nonneg hj_nonneg harm_nonneg
  · exact div_le_one_of_le₀ hj_le harm_nonneg

/-- The outcome-marked cell mass `P(X=x,A=a,Y=1)`.  [the stated conditions](hyp:P,x,a) [the stated conclusion](goal). -/
noncomputable def markedMass {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) : Real :=
  jointMass P x a true
  -- @realizes q_{ax}(q_ax = s_ax * mu_ax)

-- @node: def:aux-marginal
/-- The treatment-covariate marginal PMF.  [the stated conditions](hyp:P) [the stated conclusion](goal). -/
noncomputable def auxMarginal {d : Nat} (P : DiscreteLaw d) : PMF (AuxObs d) :=
  P.pmf.map (fun z => (z.1, z.2.1))
  -- @realizes P_{XA}((X,A)-marginal of P)

/-- The canonical labeled product law.  [the stated conditions](hyp:P,n) [the stated conclusion](goal). -/
noncomputable def labeledProductLaw {d : Nat} (P : DiscreteLaw d) (n : Nat) :
    Measure (Fin n → Obs d) :=
  Measure.pi (fun _ : Fin n => obsLaw P)
  -- @realizes \mathcal L_n(n complete iid records)

/-- The canonical auxiliary product law.  [the stated conditions](hyp:P,m) [the stated conclusion](goal). -/
noncomputable def auxProductLaw {d : Nat} (P : DiscreteLaw d) (m : Nat) :
    Measure (Fin m → AuxObs d) :=
  Measure.pi (fun _ : Fin m => (auxMarginal P).toMeasure)
  -- @realizes \mathcal U_m(m iid outcome-unlabeled records)

/-- The joint sample space.  [the stated conditions](hyp:n,m,d) [the stated conclusion](goal). -/
abbrev Sample (n m d : Nat) := (Fin n → Obs d) × (Fin m → AuxObs d)
  -- @realizes \mathcal T_{n,m,d}(estimators have domain Sample n m d and codomain Real)

-- @env: S1
variable (n m d : Nat)
  -- @realizes n(labeled sample size in Nat)
  -- @realizes m(auxiliary sample size in Nat)
  -- @realizes d(covariate alphabet size in Nat; range constrained by ModelClass)
variable (eps : Real)
  -- @realizes \epsilon(overlap constant in Real; range constrained by ModelClass)
variable (x : Fin d) -- @realizes x(covariate-cell index in Fin d)
variable (a : Bool) -- @realizes a(treatment arm in Bool)

-- @node: ass:overlap
/-- Positive-mass cells have propensity in the fixed overlap band.  [the stated conditions](hyp:eps,P) [the stated conclusion](goal). -/
def Overlap {d : Nat} (eps : Real) (P : DiscreteLaw d) : Prop :=
  ∀ x, 0 < cellMass P x →
    eps ≤ propensity P x ∧ propensity P x ≤ 1 - eps
    -- @realizes e_x(propensity constrained to [epsilon,1-epsilon] on occupied cells)
    -- @realizes p_x(overlap restriction applies exactly when p_x > 0)

-- @node: ass:labeled-iid
/-- The supplied labeled sample law is the iid product generated by `P`.  [the stated conditions](hyp:P,n,mu) [the stated conclusion](goal). -/
def LabeledIid {d : Nat} (P : DiscreteLaw d) (n : Nat)
    (mu : Measure (Fin n → Obs d)) : Prop :=
  mu = labeledProductLaw P n

-- @node: ass:auxiliary-iid
/-- The supplied auxiliary law is iid from the same population's `(X,A)` marginal.  [the stated conditions](hyp:P,m,nu) [the stated conclusion](goal). -/
def AuxiliaryIid {d : Nat} (P : DiscreteLaw d) (m : Nat)
    (nu : Measure (Fin m → AuxObs d)) : Prop :=
  nu = auxProductLaw P m

-- @node: ass:sample-independence
/-- The supplied joint probability law factorizes into its labeled and auxiliary marginals.  [the stated conditions](hyp:mu) [the stated conclusion](goal). -/
def SampleIndependence {n m d : Nat} (mu : Measure (Sample n m d)) : Prop :=
  IsProbabilityMeasure mu ∧
    mu = (mu.map Prod.fst).prod (mu.map Prod.snd)

/-- The canonical independent annotation law.  [the stated conditions](hyp:P,n,m) [the stated conclusion](goal). -/
noncomputable def annotationLaw {d : Nat} (P : DiscreteLaw d) (n m : Nat) :
    Measure (Sample n m d) :=
  (labeledProductLaw P n).prod (auxProductLaw P m)

/-- Full-data atom `(X,A,Y,Y(0),Y(1))`.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev FullObs (d : Nat) := Fin d × Bool × Bool × Bool × Bool

-- @env: S2
variable (Q : Type) -- The concrete finite potential law is introduced below.

/-- A finite potential-outcome law. -/
structure PotentialLaw (d : Nat) where
  pmf : PMF (FullObs d) -- @realizes Y(a)(binary potential outcomes in the final two coordinates)

/-- The mass of a full-data atom.  [the stated conditions](hyp:Q,z) [the stated conclusion](goal). -/
noncomputable def fullMass {d : Nat} (Q : PotentialLaw d) (z : FullObs d) : Real :=
  (Q.pmf z).toReal

-- @node: ass:consistency
/-- Consistency: atoms violating `Y=Y(A)` have zero mass.  [the stated conditions](hyp:Q) [the stated conclusion](goal). -/
def Consistency {d : Nat} (Q : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → fullMass Q z = 0
  -- @realizes Y(observed Y equals the selected potential outcome)
  -- @realizes A(observed treatment selects Y(a))
  -- @realizes Y(a)(Y(A) in the consistency identity)

/-- The `(X,A,Y(0),Y(1))` atom mass after summing out observed `Y`.  [the stated conditions](hyp:Q,x,a,y0,y1) [the stated conclusion](goal). -/
noncomputable def poAtom {d : Nat} (Q : PotentialLaw d)
    (x : Fin d) (a y0 y1 : Bool) : Real :=
  ∑ y : Bool, fullMass Q (x, a, y, y0, y1)

-- @node: ass:conditional-exchangeability
/-- The finite cross-multiplied form of `(Y(0),Y(1))` independent of `A` given `X`.  [the stated conditions](hyp:Q) [the stated conclusion](goal). -/
def ConditionalExchangeability {d : Nat} (Q : PotentialLaw d) : Prop :=
  ∀ x a y0 y1,
    poAtom Q x a y0 y1 *
        (∑ a' : Bool, ∑ y0' : Bool, ∑ y1' : Bool, poAtom Q x a' y0' y1') =
      (∑ a' : Bool, poAtom Q x a' y0 y1) *
        (∑ y0' : Bool, ∑ y1' : Bool, poAtom Q x a y0' y1')
  -- @realizes Y(a)(potential-outcome pair in conditional exchangeability)
  -- @realizes A(treatment in conditional exchangeability)
  -- @realizes X(conditioning variable in conditional exchangeability)

/-- The observed `(X,A,Y)` marginal of a potential-outcome law.  [the stated conditions](hyp:Q) [the stated conclusion](goal). -/
noncomputable def observedMarginal {d : Nat} (Q : PotentialLaw d) : DiscreteLaw d :=
  ⟨Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))⟩

-- @node: def:model-class
/-- Membership in the unrestricted finite law class includes the paper's full parameter domain. -/
structure ModelClass (d : Nat) (eps : Real) (P : DiscreteLaw d) : Prop where
  alphabet : 2 ≤ d -- @realizes d(alphabet size satisfies 2 ≤ d)
  eps_pos : 0 < eps -- @realizes \epsilon(positive overlap constant)
  eps_lt_half : eps < 1 / 2 -- @realizes \epsilon(overlap constant below 1/2)
  overlap : Overlap eps P
  -- @realizes \mathcal M_{d,\epsilon}(laws satisfying occupied-cell overlap)

/-- A law bundled with membership in the overlap class.  [the stated conditions](hyp:d,eps) [the stated conclusion](goal). -/
abbrev ClassLaw (d : Nat) (eps : Real) := {P : DiscreteLaw d // ModelClass d eps P}

-- @node: def:ate-functional
/-- The observed-data ATE functional `sum_x p_x (mu_1x-mu_0x)`.  [the stated conditions](hyp:P) [the stated conclusion](goal). -/
noncomputable def ateFunctional {d : Nat} (P : DiscreteLaw d) : Real :=
  ∑ x : Fin d, cellMass P x * (outcomeMean P true x - outcomeMean P false x)
  -- @realizes \tau(P)(sum_x p_x(mu_1x-mu_0x); range [-1,1] under overlap)

/-- Under overlap the ATE functional is in `[-1,1]`.  [the stated conditions](hyp:hP) [the stated conclusion](goal). -/
lemma ateFunctional_mem_Icc_neg_one_one {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : Overlap eps P) :
    ateFunctional P ∈ Set.Icc (-1 : Real) 1 := by
  have hsum : ∑ x : Fin d, cellMass P x = 1 := by
    have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
      simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : Real))).symm
    calc
      ∑ x : Fin d, cellMass P x = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := htotal
  have habs : |ateFunctional P| ≤ 1 := by
    rw [ateFunctional]
    calc
      |∑ x : Fin d, cellMass P x *
          (outcomeMean P true x - outcomeMean P false x)| ≤
          ∑ x : Fin d, |cellMass P x *
            (outcomeMean P true x - outcomeMean P false x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin d, cellMass P x := by
        apply Finset.sum_le_sum
        intro x _
        have hp := cellMass_mem_unitInterval P x
        have hm1 := outcomeMean_mem_unitInterval P true x
        have hm0 := outcomeMean_mem_unitInterval P false x
        rcases hm1 with ⟨hm1lo, hm1hi⟩
        rcases hm0 with ⟨hm0lo, hm0hi⟩
        rw [abs_mul, abs_of_nonneg hp.1]
        apply mul_le_of_le_one_right hp.1
        rw [abs_le]
        constructor <;> linarith
      _ = 1 := hsum
  exact abs_le.mp habs

-- @node: observedMarginal_jointMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma observedMarginal_jointMass {d : Nat} (Q : PotentialLaw d)
    (x : Fin d) (a y : Bool) :
    jointMass (observedMarginal Q) x a y =
      ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (x, a, y, y0, y1) := by
  classical
  unfold jointMass observedMarginal fullMass
  rw [PMF.map_apply, tsum_fintype]
  cases a <;> cases y <;>
    simp only [Fintype.sum_prod_type] <;>
    simp
  all_goals
    rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨Q.pmf.apply_ne_top _, Q.pmf.apply_ne_top _⟩)
        (ENNReal.add_ne_top.mpr ⟨Q.pmf.apply_ne_top _, Q.pmf.apply_ne_top _⟩),
      ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
      ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]

/-- Consistency, exchangeability and overlap identify the observed functional. [the stated conditions](hyp:heps,hCons,hExch,hOv) establishes [the stated conclusion](goal). -/
-- @node: ateFunctional_observedMarginal_eq_po_contrast
lemma ateFunctional_observedMarginal_eq_po_contrast {d : Nat} {eps : Real}
    (Q : PotentialLaw d) (heps : 0 < eps) (hCons : Consistency Q)
    (hExch : ConditionalExchangeability Q) (hOv : Overlap eps (observedMarginal Q)) :
    ateFunctional (observedMarginal Q) =
      ∑ z : FullObs d, fullMass Q z *
        ((if z.2.2.2.2 then (1 : Real) else 0) -
          (if z.2.2.2.1 then (1 : Real) else 0)) := by
  classical
  rw [ateFunctional]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have hc_tf (y0 : Bool) : fullMass Q (x, true, false, y0, true) = 0 :=
    hCons _ (by simp)
  have hc_tt (y0 : Bool) : fullMass Q (x, true, true, y0, false) = 0 :=
    hCons _ (by simp)
  have hc_ff (y1 : Bool) : fullMass Q (x, false, false, true, y1) = 0 :=
    hCons _ (by simp)
  have hc_ft (y1 : Bool) : fullMass Q (x, false, true, false, y1) = 0 :=
    hCons _ (by simp)
  have hcellarm : cellMass (observedMarginal Q) x =
      armMass (observedMarginal Q) x false + armMass (observedMarginal Q) x true := by
    simp [cellMass, armMass, Fintype.sum_bool]
    ring
  by_cases hcx : cellMass (observedMarginal Q) x = 0
  · have htotal :
        (∑ a : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
          fullMass Q (x, a, (if a then y1 else y0), y0, y1)) = 0 := by
      rw [← hcx]
      simp only [cellMass, armMass, observedMarginal_jointMass,
        Fintype.sum_bool]
      simp [hc_tf, hc_tt, hc_ff, hc_ft]
      ring
    have hn (a y y0 y1 : Bool) : 0 ≤ fullMass Q (x, a, y, y0, y1) :=
      ENNReal.toReal_nonneg
    simp only [cellMass, outcomeMean, armMass, observedMarginal_jointMass,
      Fintype.sum_bool]
    simp [hc_tf, hc_tt, hc_ff, hc_ft]
    simp only [Fintype.sum_bool] at htotal
    simp at htotal
    have h00 := hn false false false false
    have h01 := hn false false false true
    have h10 := hn false true true false
    have h11 := hn false true true true
    have ht00 := hn true false false false
    have ht01 := hn true true false true
    have ht10 := hn true false true false
    have ht11 := hn true true true true
    have hz00 : fullMass Q (x, false, false, false, false) = 0 := by nlinarith [htotal]
    have hz01 : fullMass Q (x, false, false, false, true) = 0 := by nlinarith [htotal]
    have hz10 : fullMass Q (x, false, true, true, false) = 0 := by nlinarith [htotal]
    have hz11 : fullMass Q (x, false, true, true, true) = 0 := by nlinarith [htotal]
    have hzt00 : fullMass Q (x, true, false, false, false) = 0 := by nlinarith [htotal]
    have hzt01 : fullMass Q (x, true, true, false, true) = 0 := by nlinarith [htotal]
    have hzt10 : fullMass Q (x, true, false, true, false) = 0 := by nlinarith [htotal]
    have hzt11 : fullMass Q (x, true, true, true, true) = 0 := by nlinarith [htotal]
    simp [hz00, hz01, hz10, hz11, hzt00, hzt01, hzt10, hzt11]
  · have hcxpos : 0 < cellMass (observedMarginal Q) x :=
      lt_of_le_of_ne (cellMass_mem_unitInterval _ _).1 (Ne.symm hcx)
    have hprop := hOv x hcxpos
    have htpos : 0 < armMass (observedMarginal Q) x true := by
      have hr : 0 < propensity (observedMarginal Q) x := lt_of_lt_of_le heps hprop.1
      rw [propensity] at hr
      rcases (div_pos_iff.mp hr) with h | h
      · exact h.1
      · linarith
    have hfpos : 0 < armMass (observedMarginal Q) x false := by
      have hr : propensity (observedMarginal Q) x < 1 := lt_of_le_of_lt hprop.2 (by linarith)
      rw [propensity, div_lt_one hcxpos] at hr
      linarith [hcellarm]
    have he_t0 := hExch x true false true
    have he_t1 := hExch x true true true
    have he_f0 := hExch x false true false
    have he_f1 := hExch x false true true
    simp only [poAtom, Fintype.sum_bool] at he_t0 he_t1 he_f0 he_f1
    simp [hc_tf, hc_tt, hc_ff, hc_ft] at he_t0 he_t1 he_f0 he_f1
    have htne :
        fullMass Q (x, true, true, true, true) +
            fullMass Q (x, true, true, false, true) +
          (fullMass Q (x, true, false, true, false) +
            fullMass Q (x, true, false, false, false)) ≠ 0 := by
      simpa [armMass, observedMarginal_jointMass, Fintype.sum_bool,
        hc_tf, hc_tt] using ne_of_gt htpos
    have hfne :
        fullMass Q (x, false, true, true, true) +
            fullMass Q (x, false, true, true, false) +
          (fullMass Q (x, false, false, false, true) +
            fullMass Q (x, false, false, false, false)) ≠ 0 := by
      simpa [armMass, observedMarginal_jointMass, Fintype.sum_bool,
        hc_ff, hc_ft] using ne_of_gt hfpos
    simp only [cellMass, outcomeMean, armMass, observedMarginal_jointMass,
      Fintype.sum_bool]
    simp [hc_tf, hc_tt, hc_ff, hc_ft]
    field_simp [htne, hfne]
    linear_combination
      (fullMass Q (x, false, true, true, true) +
          fullMass Q (x, false, true, true, false) +
          (fullMass Q (x, false, false, false, true) +
            fullMass Q (x, false, false, false, false))) * (he_t0 + he_t1) -
      (fullMass Q (x, true, true, true, true) +
          fullMass Q (x, true, false, true, false) +
          (fullMass Q (x, true, true, false, true) +
            fullMass Q (x, true, false, false, false))) * (he_f0 + he_f1)

-- @node: def:annotation-experiment
/-- Laws in the two-sample experiment, with all three sampling atoms explicit.  [the stated conditions](hyp:n,m,d,eps) [the stated conclusion](goal). -/
def annotationExperiment (n m d : Nat) (eps : Real) :
    Set (Measure (Sample n m d)) :=
  {mu | 1 ≤ n ∧ 2 ≤ d ∧ ∃ P : DiscreteLaw d,
    ModelClass d eps P ∧
    LabeledIid P n (mu.map Prod.fst) ∧
    AuxiliaryIid P m (mu.map Prod.snd) ∧
    SampleIndependence mu}
  -- @realizes \mathcal E_{n,m,d,\epsilon}(independent labeled and auxiliary experiment)

/-- The canonical product law belongs to the annotation experiment. [the stated conditions](hyp:hn,hP) establishes [the stated conclusion](goal). -/
-- keep: canonical law membership certificate explicitly promised by the F1 plan and public experiment API
lemma annotationLaw_mem_annotationExperiment {n m d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hn : 1 ≤ n) (hP : ModelClass d eps P) :
    annotationLaw P n m ∈ annotationExperiment n m d eps := by
  letI : IsProbabilityMeasure (labeledProductLaw P n) := by
    unfold labeledProductLaw
    infer_instance
  letI : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw
    infer_instance
  refine ⟨hn, hP.alphabet, P, hP, ?_, ?_, ?_⟩
  · unfold LabeledIid annotationLaw
    simp
  · unfold AuxiliaryIid annotationLaw
    simp
  · constructor
    · unfold annotationLaw
      infer_instance
    · unfold annotationLaw
      simp

/-- Mean squared error under a supplied two-sample law.  [the stated conditions](hyp:mu,est,target) [the stated conclusion](goal). -/
noncomputable def twoSampleMSE {n m d : Nat} (mu : Measure (Sample n m d))
    (est : Sample n m d → Real) (target : Real) : Real :=
  ∫ z, (est z - target) ^ 2 ∂mu

-- @node: def:minimax-risk
/-- Infimum measurable-estimator, supremum overlap-law MSE in the canonical annotation experiment.  [the stated conditions](hyp:n,m,d,eps) [the stated conclusion](goal). -/
noncomputable def minimaxRisk (n m d : Nat) (eps : Real) : Real :=
  ⨅ est : {f : Sample n m d → Real // Measurable f},
    ⨆ P : ClassLaw d eps,
      twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1)
  -- @realizes R_\epsilon(n,m,d)(minimax MSE; range [0,1] for the canonical experiment)

/-- The canonical minimax risk has the paper's stated range.  [the stated conclusion](goal). -/
lemma minimaxRisk_mem_Icc_zero_one (n m d : Nat) (eps : Real) :
    minimaxRisk n m d eps ∈ Set.Icc (0 : Real) 1 := by
  have hnonneg (est : {f : Sample n m d → Real // Measurable f}) :
      0 ≤ ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1) := by
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hbounded : BddAbove (Set.range (fun P : ClassLaw d eps =>
            twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1)))
        · have hmse : 0 ≤ twoSampleMSE
              (annotationLaw (Classical.arbitrary (ClassLaw d eps)).1 n m)
              est.1 (ateFunctional (Classical.arbitrary (ClassLaw d eps)).1) := by
            exact integral_nonneg (fun z => sq_nonneg
              (est.1 z - ateFunctional (Classical.arbitrary (ClassLaw d eps)).1))
          exact hmse.trans (le_ciSup hbounded (Classical.arbitrary _))
        · rw [show (⨆ P : ClassLaw d eps,
              twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1)) =
              sSup ∅ from csSup_of_not_bddAbove hbounded]
          simp
  have hb : BddBelow (Set.range (fun est :
      {f : Sample n m d → Real // Measurable f} =>
        ⨆ P : ClassLaw d eps,
          twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact hnonneg est
  letI : Nonempty {f : Sample n m d → Real // Measurable f} :=
    ⟨⟨fun _ => 0, measurable_const⟩⟩
  constructor
  · apply le_ciInf
    exact hnonneg
  · have hzero : Measurable (fun _ : Sample n m d => (0 : Real)) := measurable_const
    refine (ciInf_le hb ⟨fun _ => 0, hzero⟩).trans ?_
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        apply ciSup_le
        intro P
        have ht := ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap
        have hs : ateFunctional P.1 ^ 2 ≤ 1 :=
          (sq_le_one_iff_abs_le_one (ateFunctional P.1)).2 (abs_le.mpr ht)
        letI : IsProbabilityMeasure (annotationLaw P.1 n m) := by
          unfold annotationLaw labeledProductLaw auxProductLaw
          infer_instance
        simpa [twoSampleMSE] using hs

/-- The logarithmic scale `log(e n)`.  [the stated conditions](hyp:n) [the stated conclusion](goal). -/
noncomputable def logEN (n : Nat) : Real := Real.log (Real.exp 1 * n)

-- @node: def:frontier-rate-handle
/-- The explicit unequal-information annotation-frontier rate.  [the stated conditions](hyp:n,m,d) [the stated conclusion](goal). -/
noncomputable def frontierRate (n m d : Nat) : Real :=
  min 1 (1 / (n : Real) + (d : Real) ^ 2 /
    (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2))
  -- @realizes N(N = n + m)
  -- @realizes r_\epsilon(n,m,d)(min{1,1/n+d^2/(N^2 log^2(en))})
/-- [the stated conditions](hyp:hn) establishes [the stated conclusion](goal). -/

lemma frontierRate_mem_Ioc_zero_one (n m d : Nat) (hn : 1 ≤ n) :
    frontierRate n m d ∈ Set.Ioc (0 : Real) 1 := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  constructor
  · rw [frontierRate]
    apply lt_min (by norm_num)
    have hdim : 0 ≤ (d : Real) ^ 2 /
        (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2) := by positivity
    exact lt_of_lt_of_le (one_div_pos.mpr hnpos) (le_add_of_nonneg_right hdim)
  · exact min_le_left _ _
/-- [the stated conditions](hyp:hn) establishes [the stated conclusion](goal). -/

lemma inv_n_le_frontierRate (n m d : Nat) (hn : 1 ≤ n) :
    1 / (n : Real) ≤ frontierRate n m d := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [frontierRate]
  apply le_min
  · rw [div_le_iff₀ hnpos]
    have hnreal : (1 : Real) ≤ n := by exact_mod_cast hn
    simpa using hnreal
  · exact le_add_of_nonneg_right (by positivity)

/-- The exact treatment-covariate probability table.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev AuxTable (d : Nat) := AuxObs d → Real
  -- @realizes P_{XA}(exact 2d-cell table)

/-- The known-marginal observation space.  [the stated conditions](hyp:n,d) [the stated conclusion](goal). -/
abbrev KnownSample (n d : Nat) := (Fin n → Obs d) × AuxTable d

/-- The exact table associated with `P`.  [the stated conditions](hyp:P) [the stated conclusion](goal). -/
noncomputable def auxTableOf {d : Nat} (P : DiscreteLaw d) : AuxTable d :=
  fun z => armMass P z.1 z.2

-- @env: S3
variable (n d : Nat) (eps : Real)

-- @node: def:known-marginal-experiment
/-- The benchmark experiment supplying labeled data and the exact `(X,A)` table.  [the stated conditions](hyp:n,d,eps) [the stated conclusion](goal). -/
def knownMarginalExperiment (n d : Nat) (eps : Real) :
    Set (Measure (Fin n → Obs d) × AuxTable d) :=
  {q | 1 ≤ n ∧ 2 ≤ d ∧ ∃ P : DiscreteLaw d,
    ModelClass d eps P ∧ LabeledIid P n q.1 ∧ q.2 = auxTableOf P}
  -- @realizes \mathcal E^{\mathrm{known}}_{n,d,\epsilon}(canonical labeled law + exact table)

/-- Projection of a real decision into the target's known range `[-1,1]`.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def clipAte (z : Real) : Real := max (-1) (min 1 z)

/-- Clipping any measurable known-marginal estimator is measurable, remains in
`[-1,1]`, and cannot increase squared loss against any legal ATE target.  [the stated conditions](hyp:hest) [the stated conclusion](goal). -/
lemma exists_clipped_knownMarginalEstimator (n d : Nat)
    (est : KnownSample n d → Real) (hest : Measurable est) :
    ∃ clipped : {f : KnownSample n d → Real //
        Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1},
      ∀ z (target : Real), target ∈ Set.Icc (-1 : Real) 1 →
        (clipped.1 z - target) ^ 2 ≤ (est z - target) ^ 2 := by
  let hbounds : (-1 : Real) ≤ 1 := by norm_num
  let clipped : KnownSample n d → Real := fun z => clipAte (est z)
  have hclipped_measurable : Measurable clipped := by
    dsimp [clipped, clipAte]
    fun_prop
  have hclipped_mem : ∀ z, clipped z ∈ Set.Icc (-1 : Real) 1 := by
    intro z
    exact (Set.projIcc (-1 : Real) 1 hbounds (est z)).property
  refine ⟨⟨clipped, hclipped_measurable, hclipped_mem⟩, ?_⟩
  intro z target htarget
  have habs : |clipped z - target| ≤ |est z - target| := by
    simpa [clipped, clipAte, Set.coe_projIcc,
      Set.projIcc_of_mem hbounds htarget] using
      (Set.abs_projIcc_sub_projIcc (a := (-1 : Real)) (b := 1)
        (c := est z) (d := target) hbounds)
  exact sq_le_sq.mpr habs

-- @node: def:known-marginal-risk
/-- Minimax MSE when the exact treatment-covariate table is supplied.  [the stated conditions](hyp:n,d,eps) [the stated conclusion](goal). -/
noncomputable def knownMarginalRisk (n d : Nat) (eps : Real)
    : Real :=
  ⨅ est : {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1},
    ⨆ P : ClassLaw d eps,
      ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂(labeledProductLaw P.1 n)
  -- @realizes \mathcal T^{\mathrm{known}}_{n,d}(estimators measurable with respect to the labeled sample \mathcal L_n together with the exact marginal table P_{XA})
  -- @realizes R_\epsilon^{\mathrm{known}}(n,d)(known-marginal minimax MSE in [0,1])

-- keep: public bounded-risk range API explicitly promised by the F1 plan
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma knownMarginalRisk_mem_Icc_zero_one (n d : Nat) (eps : Real) :
    knownMarginalRisk n d eps ∈ Set.Icc (0 : Real) 1 := by
  have hnonneg (est : {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1}) :
      0 ≤ ⨆ P : ClassLaw d eps,
        ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2
          ∂(labeledProductLaw P.1 n) := by
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hbounded : BddAbove (Set.range (fun P : ClassLaw d eps =>
            ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2
              ∂(labeledProductLaw P.1 n)))
        · have hint : 0 ≤ ∫ x,
              (est.1 (x, auxTableOf (Classical.arbitrary (ClassLaw d eps)).1) -
                ateFunctional (Classical.arbitrary (ClassLaw d eps)).1) ^ 2
              ∂(labeledProductLaw (Classical.arbitrary (ClassLaw d eps)).1 n) :=
            integral_nonneg (fun x => sq_nonneg _)
          exact hint.trans (le_ciSup hbounded (Classical.arbitrary _))
        · rw [show (⨆ P : ClassLaw d eps,
              ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2
                ∂(labeledProductLaw P.1 n)) = sSup ∅ from
              csSup_of_not_bddAbove hbounded]
          simp
  have hb : BddBelow (Set.range (fun est : {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1} =>
        ⨆ P : ClassLaw d eps,
          ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2
            ∂(labeledProductLaw P.1 n))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact hnonneg est
  let zeroEst : {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1} :=
    ⟨fun _ => 0, measurable_const, by intro z; norm_num⟩
  letI : Nonempty {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1} := ⟨zeroEst⟩
  constructor
  · apply le_ciInf
    exact hnonneg
  · refine (ciInf_le hb zeroEst).trans ?_
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        apply ciSup_le
        intro P
        have ht := ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap
        have hs : ateFunctional P.1 ^ 2 ≤ 1 :=
          (sq_le_one_iff_abs_le_one (ateFunctional P.1)).2 (abs_le.mpr ht)
        letI : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
          unfold labeledProductLaw
          infer_instance
        simpa [zeroEst] using hs

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
