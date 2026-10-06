module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite randomized MAR experiment

The full law retains observed and potential coordinates separately, making consistency a
substantive condition. The finite PMF model is used because the paper's risks range over
explicit observed-data laws, rather than regime-indexed potential-outcome kernels.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

set_option maxRecDepth 512

/-- Baseline and potential coordinates. -/
structure PotentialAtom (d : ℕ) where
  X : Fin d -- @realizes X(carrier Fin d)
  S0 : Bool -- @realizes S0(carrier Bool)
  S1 : Bool -- @realizes S1(carrier Bool)
  Y0 : Bool -- @realizes Y0(carrier Bool)
  Y1 : Bool -- @realizes Y1(carrier Bool)
  deriving DecidableEq, Fintype

/-- [Potential-data atoms have decidable equality](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instDecidableEqPotentialAtom

/-- [Potential-data atoms have a finite enumeration](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instFintypePotentialAtom

/-- Full-data atom with separate observed and potential outcomes. -/
structure FullAtom (d : ℕ) where
  potential : PotentialAtom d
  A : Bool -- @realizes A(carrier Bool)
  S : Bool -- @realizes S(carrier Bool)
  Y : Bool -- @realizes Y(carrier Bool)
  R : Bool -- @realizes R(carrier Bool)
  deriving DecidableEq, Fintype

/-- [Full-data atoms have decidable equality](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instDecidableEqFullAtom

/-- [Full-data atoms have a finite enumeration](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instFintypeFullAtom

/-- [The baseline covariate of a full-data atom](goal) is inherited from [the supplied atom](hyp:w). -/
abbrev FullAtom.X {d : ℕ} (w : FullAtom d) := w.potential.X
/-- [The control-arm arrival indicator of a full-data atom](goal) is inherited from [the supplied atom](hyp:w). -/
abbrev FullAtom.S0 {d : ℕ} (w : FullAtom d) := w.potential.S0
/-- [The treated-arm arrival indicator of a full-data atom](goal) is inherited from [the supplied atom](hyp:w). -/
abbrev FullAtom.S1 {d : ℕ} (w : FullAtom d) := w.potential.S1
/-- [The control potential outcome of a full-data atom](goal) is inherited from [the supplied atom](hyp:w). -/
abbrev FullAtom.Y0 {d : ℕ} (w : FullAtom d) := w.potential.Y0
/-- [The treated potential outcome of a full-data atom](goal) is inherited from [the supplied atom](hyp:w). -/
abbrev FullAtom.Y1 {d : ℕ} (w : FullAtom d) := w.potential.Y1

/-- The record visible to the statistician; the last coordinate is `R Y`. -/
structure Obs (d : ℕ) where
  X : Fin d -- @realizes O(first coordinate X)
  A : Bool -- @realizes O(second coordinate A)
  S : Bool -- @realizes O(third coordinate S)
  R : Bool -- @realizes O(fourth coordinate R)
  RY : Bool -- @realizes O(fifth coordinate RY)
  deriving DecidableEq, Fintype

/-- [Observed-data atoms have decidable equality](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instDecidableEqObs

/-- [Observed-data atoms have a finite enumeration](goal) for [the given covariate dimension](hyp:d). -/
add_decl_doc instFintypeObs

/-- [The measurable structure on observed atoms](goal) is the discrete structure for [the given covariate dimension](hyp:d). -/
instance (d : ℕ) : MeasurableSpace (Obs d) := ⊤
/-- [Every singleton observed atom is measurable](goal) for [the given covariate dimension](hyp:d). -/
instance (d : ℕ) : MeasurableSingletonClass (Obs d) := ⟨fun _ => trivial⟩

/-- Superpopulation distribution on full-data atoms. -/
structure FullLaw (d : ℕ) where
  pmf : PMF (FullAtom d) -- @realizes P(full-data PMF; S,Y pinned a.s. by Consistency)

/-- Deterministic observation, with a zero outcome mark when the outcome does not arrive. -/
def observe {d : ℕ} (w : FullAtom d) : Obs d :=
  ⟨w.X, w.A, w.S, w.R, w.R && w.Y⟩
  -- @realizes O(observation map O=(X,A,S,R,RY))

/-- Observed-data marginal of the superpopulation law. -/
noncomputable def observedLaw {d : ℕ} (P : FullLaw d) : PMF (Obs d) :=
  P.pmf.map observe

/-- Real mass of a full-data atom. -/
noncomputable def fullMass {d : ℕ} (P : FullLaw d) (w : FullAtom d) : ℝ :=
  (P.pmf w).toReal

/-- Probability of a full-data event. -/
noncomputable def massOf {d : ℕ} (P : FullLaw d) (E : FullAtom d → Prop) : ℝ := by
  classical
  exact ∑ w : FullAtom d, if E w then fullMass P w else 0

/-- Probability of an observed atom. -/
noncomputable def obsMass {d : ℕ} (p : PMF (Obs d)) (o : Obs d) : ℝ :=
  (p o).toReal

/-- Marginal mass of a treatment arm. -/
noncomputable def armMass {d : ℕ} (P : FullLaw d) (a : Bool) : ℝ :=
  massOf P (fun w => w.A = a)

/-- Mass of an occupied `(X,A,S)` cell. -/
noncomputable def cellMass {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s)

/-- The arrival probability, totalized to zero on null cells. -/
noncomputable def arrivalProb {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) /
    cellMass P x a s
  -- @realizes rho(P(R=1|X=x,A=a,S=s); zero on null cells)

/-- Arrived-outcome regression calculated solely from the observed distribution. -/
noncomputable def outcomeMean {d : ℕ} (p : PMF (Obs d))
    (x : Fin d) (a s : Bool) : ℝ :=
  (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true
      then obsMass p o else 0) /
    (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true
      then obsMass p o else 0)
  -- @realizes mu(E[Y|X,A,S,R=1]; zero on null arrived cells)

/-- Superpopulation ATE. -/
noncomputable def tau {d : ℕ} (P : FullLaw d) : ℝ :=
  ∑ w : FullAtom d, fullMass P w * ((if w.Y1 then 1 else 0) -
    (if w.Y0 then 1 else 0))
  -- @realizes tau(E[Y1-Y0])

-- @env: S1
variable {d n : ℕ} {q : ℝ}

-- @node: ass:randomized-independence
/-- Randomization factors the treatment from all baseline and potential coordinates. Given [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
def RandomizedIndependence (P : FullLaw d) : Prop :=
  ∀ a x s0 s1 y0 y1,
    massOf P (fun w => w.A = a ∧ w.X = x ∧ w.S0 = s0 ∧ w.S1 = s1 ∧
      w.Y0 = y0 ∧ w.Y1 = y1) =
    armMass P a * massOf P (fun w => w.X = x ∧ w.S0 = s0 ∧ w.S1 = s1 ∧
      w.Y0 = y0 ∧ w.Y1 = y1)

-- @node: ass:balanced-randomization
/-- Balanced Bernoulli treatment allocation. Given [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
def BalancedRandomization (P : FullLaw d) : Prop :=
  armMass P true = (1 : ℝ) / 2

-- @node: ass:consistency
/-- Observed outcomes equal their treatment-selected potential outcomes almost surely. Given [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
def Consistency (P : FullLaw d) : Prop :=
  ∀ w, w.S ≠ (if w.A then w.S1 else w.S0) ∨
    w.Y ≠ (if w.A then w.Y1 else w.Y0) → fullMass P w = 0
  -- @realizes P(zero mass unless S=S(A) and Y=Y(A); seven free coordinates)
  -- @realizes S(almost surely S=S(A))
  -- @realizes Y(almost surely Y=Y(A))

-- @node: ass:mar
/-- Cross-multiplied conditional independence of arrival and realized outcome. Given [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
def MissingAtRandom (P : FullLaw d) : Prop :=
  ∀ x a s r y,
    massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = r ∧ w.Y = y) *
      cellMass P x a s =
    massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = r) *
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = y)

-- @node: ass:arrival-floor
/-- Uniform arrival floor on occupied cells. Given [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
def ArrivalFloor (q : ℝ) (P : FullLaw d) : Prop :=
  ∀ x a s, 0 < cellMass P x a s → q ≤ arrivalProb P x a s
  -- @realizes rho(arrival probability at least q on occupied cells)

-- @node: def:law-class
/-- The randomized finite-cell MAR law class. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
structure LawClass (d : ℕ) (q : ℝ) (P : FullLaw d) : Prop where
  randomized : RandomizedIndependence P
  balanced : BalancedRandomization P
  consistency : Consistency P -- @realizes P(law-class enforces the a.s. consistency restriction)
  mar : MissingAtRandom P
  floor : ArrivalFloor q P
  -- @realizes M_dq(laws satisfying randomization, consistency, MAR, arrival floor)

/-- A law with its certificate of membership in the MAR class. -/
abbrev ClassLaw (d : ℕ) (q : ℝ) := {P : FullLaw d // LawClass d q P}

/-- Treatment-conditional `(X,S)` mass computed from the observed law. -/
noncomputable def condCellMass {d : ℕ} (p : PMF (Obs d))
    (x : Fin d) (a s : Bool) : ℝ :=
  (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s then obsMass p o else 0) /
    (∑ o : Obs d, if o.A = a then obsMass p o else 0)

-- @node: def:identified-functional
/-- Observed-data MAR identifying functional, with totalized null-cell terms. Given [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). Given [the specified input `p`](hyp:p). -/
noncomputable def psi {d : ℕ} (p : PMF (Obs d)) : ℝ :=
  ∑ x : Fin d, ∑ s : Bool,
    (condCellMass p x true s * outcomeMean p x true s -
    condCellMass p x false s * outcomeMean p x false s)
  -- @realizes Psi(sum of treated minus control conditional-cell outcome means)

/-- The missingness envelope. -/
def delta (q : ℝ) : ℝ := 1 - q -- @realizes delta(1-q)

/-- Logarithmic moment scale. -/
noncomputable def ell (n : ℕ) : ℝ := Real.log (Real.exp 1 + n)
  -- @realizes ell(log(e+n))

/-- Half-separation scale. -/
noncomputable def gScale (n d : ℕ) (q : ℝ) : ℝ :=
  delta q * min 1 ((d : ℝ) / ((n : ℝ) * ell n))
  -- @realizes g_ndq((1-q) min{1,d/(n ell)})

-- @node: def:rate
/-- Near-complete minimax squared-error rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). -/
noncomputable def rate (n d : ℕ) (q : ℝ) : ℝ :=
  1 / (n : ℝ) + gScale n d q ^ 2
  -- @realizes r_ndq(n⁻¹+g_ndq²)

-- @env: S2
variable (n d : ℕ) (q : ℝ)

/-- Canonical iid law of the observed sample. -/
noncomputable def samplePi {d : ℕ} (P : FullLaw d) (n : ℕ) : Measure (Fin n → Obs d) :=
  Measure.pi (fun _ : Fin n => (observedLaw P).toMeasure)

-- @node: ass:iid
/-- A supplied sample law equals the iid observed-data product law. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `μ`](hyp:μ). -/
def IidSample {d : ℕ} (P : FullLaw d) (n : ℕ) (μ : Measure (Fin n → Obs d)) : Prop :=
  μ = samplePi P n

/-- Total measurable observed-data estimator with range in `[-1,1]`. -/
structure Estimator (n d : ℕ) where
  toFun : (Fin n → Obs d) → ℝ -- @realizes T_n(measurable sample-to-real map)
  measurable : Measurable toFun
  range : ∀ o, toFun o ∈ Set.Icc (-1) 1 -- @realizes T_n(range [-1,1])

/-- [An estimator acts as its sample-to-real function](goal) for [the sample size](hyp:n) and [covariate dimension](hyp:d). -/
instance (n d : ℕ) : CoeFun (Estimator n d) (fun _ => (Fin n → Obs d) → ℝ) :=
  ⟨Estimator.toFun⟩

-- @node: def:point-risk
/-- All-procedure finite-sample minimax squared risk. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). -/
noncomputable def pointMinimaxRisk (n d : ℕ) (q : ℝ) : ℝ :=
  ⨅ T : Estimator n d, ⨆ P : ClassLaw d q,
    ∫ o, (T o - tau P.val) ^ 2 ∂ samplePi P.val n
  -- @realizes Rstar(inf estimator sup legal laws mean squared error)

/-- A measurable closed interval inside `[-1,1]`. -/
structure IntervalProc (n d : ℕ) where
  lo : (Fin n → Obs d) → ℝ
  hi : (Fin n → Obs d) → ℝ
  lo_measurable : Measurable lo
  hi_measurable : Measurable hi
  bounds : ∀ o, -1 ≤ lo o ∧ lo o ≤ hi o ∧ hi o ≤ 1

/-- Uniform coverage over the legal law class. -/
def Honest (n d : ℕ) (q α : ℝ) (I : IntervalProc n d) : Prop :=
  ∀ P : ClassLaw d q,
    1 - α ≤ (samplePi P.val n).real
      {o | tau P.val ∈ Set.Icc (I.lo o) (I.hi o)}

-- @node: def:interval-class
/-- Honest connected confidence intervals at noncoverage level `α`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). -/
def HonestIntervalClass (n d : ℕ) (q α : ℝ) :=
  {I : IntervalProc n d // Honest n d q α I}
  -- @realizes C_alpha(honest measurable closed intervals in [-1,1])

-- @node: def:length-risk
/-- Minimax worst-law expected interval length. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). -/
noncomputable def lengthMinimaxRisk (n d : ℕ) (q α : ℝ) : ℝ :=
  ⨅ I : HonestIntervalClass n d q α, ⨆ P : ClassLaw d q,
    ∫ o, (I.val.hi o - I.val.lo o) ∂ samplePi P.val n
  -- @realizes Lstar(inf honest interval sup legal laws expected length)

/-- Observed event masses are the pushforwards of their full-data preimages. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: obsMass_sum_event
lemma obsMass_sum_event {d : ℕ} (P : FullLaw d) (E : Obs d → Prop)
    [DecidablePred E] :
      (∑ o : Obs d, if E o then obsMass (observedLaw P) o else 0) =
        massOf P (fun w => E (observe w)) := by
  classical
  have hmass (o : Obs d) :
      obsMass (observedLaw P) o =
        ∑ w : FullAtom d, if observe w = o then fullMass P w else 0 := by
    simp only [obsMass, observedLaw, PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum]
    · simp only [fullMass, apply_ite, ENNReal.toReal_zero]
      apply Finset.sum_congr rfl
      intro w hw
      split_ifs <;> simp_all [eq_comm]
    · intro w hw
      split
      · exact PMF.apply_ne_top P.pmf w
      · simp
  simp only [hmass, massOf]
  calc
    (∑ o : Obs d, if E o then
        ∑ w : FullAtom d, if observe w = o then fullMass P w else 0 else 0) =
      ∑ o : Obs d, ∑ w : FullAtom d,
        if E o ∧ observe w = o then fullMass P w else 0 := by
          apply Finset.sum_congr rfl
          intro o ho
          by_cases hE : E o <;> simp [hE]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hE : E (observe w)
      · rw [if_pos hE]
        conv_rhs => rw [← show (if E (observe w) ∧ observe w = observe w then
            fullMass P w else 0) = fullMass P w from by simp [hE]]
        apply Finset.sum_eq_single (observe w)
        · intro o ho hne
          simp [Ne.symm hne]
        · intro hn
          simp at hn
      · rw [if_neg hE]
        apply Finset.sum_eq_zero
        intro o ho
        by_cases heq : observe w = o
        · subst o
          simp [hE]
        · simp [heq]

-- @node: observed_arm_mass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma observed_arm_mass {d : ℕ} (P : FullLaw d) (a : Bool) :
    (∑ o : Obs d, if o.A = a then obsMass (observedLaw P) o else 0) =
      armMass P a := by
  classical
  simpa [armMass, observe] using
    (obsMass_sum_event P (fun o : Obs d => o.A = a))

-- @node: observed_cell_mass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma observed_cell_mass {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s then
      obsMass (observedLaw P) o else 0) = cellMass P x a s := by
  classical
  simpa [cellMass, observe] using
    (obsMass_sum_event P (fun o : Obs d => o.X = x ∧ o.A = a ∧ o.S = s))

-- @node: observed_arrived_mass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma observed_arrived_mass {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true then
      obsMass (observedLaw P) o else 0) =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) := by
  classical
  simpa [observe] using
    (obsMass_sum_event P
      (fun o : Obs d => o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true))

-- @node: observed_arrived_outcome_mass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma observed_arrived_outcome_mass {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    (∑ o : Obs d, if o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true then
      obsMass (observedLaw P) o else 0) =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true ∧ w.Y = true) := by
  classical
  simpa [observe, Bool.and_eq_true] using
    (obsMass_sum_event P
      (fun o : Obs d => o.X = x ∧ o.A = a ∧ o.S = s ∧ o.R = true ∧ o.RY = true))

-- @node: condCellMass_observed
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma condCellMass_observed {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    condCellMass (observedLaw P) x a s = cellMass P x a s / armMass P a := by
  simp only [condCellMass, observed_cell_mass, observed_arm_mass]

-- @node: outcomeMean_observed
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma outcomeMean_observed {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    outcomeMean (observedLaw P) x a s =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true ∧ w.Y = true) /
        massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) := by
  simp only [outcomeMean, observed_arrived_outcome_mass, observed_arrived_mass]

-- @node: arrivalMass_pos
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hc`](hyp:hc), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma arrivalMass_pos {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool) (hc : 0 < cellMass P x a s) :
    0 < massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) := by
  have hf := h.floor x a s hc
  have hq0 : 0 < q := by rcases hq with ⟨hl, _⟩; linarith
  simp only [arrivalProb] at hf
  exact (div_pos_iff_of_pos_right hc).mp (lt_of_lt_of_le hq0 hf)

-- @node: outcomeMean_identified_cell
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hc`](hyp:hc), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma outcomeMean_identified_cell {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool) (hc : 0 < cellMass P x a s) :
    outcomeMean (observedLaw P) x a s =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true) /
        cellMass P x a s := by
  rw [outcomeMean_observed]
  have hr := arrivalMass_pos P h hq x a s hc
  have hm := h.mar x a s true true
  apply (div_eq_div_iff (ne_of_gt hr) (ne_of_gt hc)).mpr
  simpa [mul_comm] using hm

-- @node: cellMass_nonneg
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma cellMass_nonneg {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    0 ≤ cellMass P x a s := by
  unfold cellMass massOf
  apply Finset.sum_nonneg
  intro w hw
  split_ifs <;> simp [fullMass]

-- @node: cellMass_le_armMass
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma cellMass_le_armMass {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    cellMass P x a s ≤ armMass P a := by
  unfold cellMass armMass massOf
  apply Finset.sum_le_sum
  intro w hw
  by_cases hc : w.X = x ∧ w.A = a ∧ w.S = s
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    split_ifs <;> simp [fullMass]

-- @node: cellOutcome_nonneg
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma cellOutcome_nonneg {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    0 ≤ massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true) := by
  unfold massOf
  apply Finset.sum_nonneg
  intro w hw
  split_ifs <;> simp [fullMass]

-- @node: cellOutcome_le_cell
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma cellOutcome_le_cell {d : ℕ} (P : FullLaw d) (x : Fin d) (a s : Bool) :
    massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true) ≤
      cellMass P x a s := by
  unfold cellMass massOf
  apply Finset.sum_le_sum
  intro w hw
  by_cases hc : w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    split_ifs <;> simp [fullMass]

-- @node: cellContribution_identified
/-- Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma cellContribution_identified {d : ℕ} {q : ℝ} (P : FullLaw d)
    (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool) :
    condCellMass (observedLaw P) x a s * outcomeMean (observedLaw P) x a s =
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true) / armMass P a := by
  rw [condCellMass_observed]
  have hc0 := cellMass_nonneg P x a s
  by_cases hc : cellMass P x a s = 0
  · have hy0 := cellOutcome_nonneg P x a s
    have hyle := cellOutcome_le_cell P x a s
    have hy : massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true) = 0 := by
      linarith
    simp [hc, hy]
  · have hcpos : 0 < cellMass P x a s := lt_of_le_of_ne hc0 (Ne.symm hc)
    have ha : 0 < armMass P a := lt_of_lt_of_le hcpos (cellMass_le_armMass P x a s)
    rw [outcomeMean_identified_cell P h hq x a s hcpos]
    field_simp

-- @node: cellOutcome_sum
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma cellOutcome_sum {d : ℕ} (P : FullLaw d) (a : Bool) :
    (∑ x : Fin d, ∑ s : Bool,
      massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = true)) =
      massOf P (fun w => w.A = a ∧ w.Y = true) := by
  classical
  rw [← Fintype.sum_prod_type']
  simp only [massOf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ha : w.A = a
  · by_cases hy : w.Y = true
    · simp only [ha, hy, and_true, true_and, ↓reduceIte]
      rw [Fintype.sum_prod_type' (fun x : Fin d => fun s : Bool =>
        if w.X = x ∧ w.S = s then fullMass P w else 0)]
      cases w.S <;> simp
    · simp [ha, hy]
  · simp [ha]

end CausalSmith.Stat.MarNearcompleteFrontier
