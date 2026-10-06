module
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Sample
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProductMeasure

/-!
Finite two-channel ATE experiment and its rare-overlap frontier.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Complete record with binary treatment and outcome](goal).
-/
abbrev Obs (d : Nat) := Fin d × Bool × Bool
  -- @realizes X(covariate coordinate Fin d)
  -- @realizes A(treatment coordinate Bool)
  -- @realizes Y(outcome coordinate Bool)

/--
[An auxiliary record retains covariates and treatment without the outcome](goal).
-/
abbrev AuxObs (d : Nat) := Fin d × Bool

/--
[The unknown observable population is a PMF on complete-record atoms](goal).
-/
structure DiscreteLaw (d : Nat) where
  pmf : PMF (Obs d) -- @realizes P(probability law of complete records)

/--
[The simplex carries its coordinate Borel sigma algebra](goal).
-/
instance {d : Nat} : MeasurableSpace (DiscreteLaw d) :=
  MeasurableSpace.comap (fun P => fun z => (P.pmf z).toReal) inferInstance

/--
[For a finite covariate dimension](hyp:d) and [an observable population law](hyp:P),
[the observed-data sampling law](goal) is the probability measure represented by that law's PMF.
-/
noncomputable def obsLaw {d : Nat} (P : DiscreteLaw d) : Measure (Obs d) := P.pmf.toMeasure
/--
[The real mass of one complete-record atom is read from the population PMF](goal).
-/
noncomputable def jointMass {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a y : Bool) : Real :=
  (P.pmf (j, a, y)).toReal
/--
[Covariate masses sum the complete-record probabilities over both binary coordinates](goal).
-/
noncomputable def cellMass {d : Nat} (P : DiscreteLaw d) (j : Fin d) : Real :=
  ∑ a : Bool, ∑ y : Bool, jointMass P j a y -- @realizes p(covariate probability in [0,1])
/--
[Arm-cell masses sum the two possible outcome marks](goal).
-/
noncomputable def armMass {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a : Bool) : Real :=
  ∑ y : Bool, jointMass P j a y -- @realizes s(arm-cell probability in [0,1])
/--
[The outcome-marked mass is the probability of a success in the specified arm and cell](goal).
-/
noncomputable def markedMass {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a : Bool) : Real :=
  jointMass P j a true -- @realizes q(success-marked probability in [0,1])
/--
[The occupied-cell treatment probability uses the arm-to-cell ratio; null cells use one
half](goal).
-/
noncomputable def propensity {d : Nat} (P : DiscreteLaw d) (j : Fin d) : Real :=
  if cellMass P j = 0 then 1 / 2 else armMass P j true / cellMass P j
  -- @realizes e(conditional treatment probability; null cells use 1/2)

/--
[Outcome regression is the success-to-arm ratio, with zero on null arm cells](goal).
-/
noncomputable def outcomeMean {d : Nat} (P : DiscreteLaw d) (a : Bool) (j : Fin d) : Real :=
  markedMass P j a / armMass P j a
  -- @realizes \mu(conditional success probability; zero on null arms)
/--
[Marginal PMFs carry the Borel sigma algebra of their real atom-mass coordinates](goal).
-/
instance {d : Nat} : MeasurableSpace (PMF (AuxObs d)) :=
  MeasurableSpace.comap (fun p => fun z => (p z).toReal) inferInstance

/--
[The auxiliary PMF is the actual treatment-covariate projection of the observed law](goal).
-/
noncomputable def auxMarginal {d : Nat} (P : DiscreteLaw d) : PMF (AuxObs d) :=
  P.pmf.map (fun z => (z.1, z.2.1)) -- @realizes P_{XA}(actual treatment-covariate marginal)
/--
[The ordered complete records have the iid product probability law](goal).
-/
noncomputable def labeledProductLaw {d : Nat} (P : DiscreteLaw d) (n : Nat) :
    Measure (Fin n → Obs d) := Measure.pi (fun _ => obsLaw P)
  -- @realizes \mathcal L(n ordered complete iid records)
/--
[The ordered auxiliary records have the iid law of the actual treatment-covariate
marginal](goal).
-/
noncomputable def auxProductLaw {d : Nat} (P : DiscreteLaw d) (m : Nat) :
    Measure (Fin m → AuxObs d) := Measure.pi (fun _ => (auxMarginal P).toMeasure)
  -- @realizes \mathcal V(m ordered auxiliary iid records)
/--
[For the complete-sample size](hyp:n), [the auxiliary-sample size](hyp:m), and [the covariate dimension](hyp:d),
[the experiment's sample space](goal) consists of an ordered complete-record array paired with an ordered auxiliary-record array.
-/
abbrev Sample (n m d : Nat) := (Fin n → Obs d) × (Fin m → AuxObs d)
  -- @realizes \mathcal D(ordered pair of complete and auxiliary arrays)
/--
[The two ordered iid arrays are independent and share the population marginal](goal).
-/
noncomputable def annotationLaw {d : Nat} (P : DiscreteLaw d) (n m : Nat) :
    Measure (Sample n m d) := (labeledProductLaw P n).prod (auxProductLaw P m)
/--
[The randomization seed is uniform on the closed unit interval](goal).
-/
noncomputable def seedLaw : Measure Real := volume.restrict (Set.Icc 0 1)
  -- @realizes U(uniform seed on [0,1]; independent through product law)

/--
[Original-record rules are jointly measurable and take values in the closed interval from minus
one to one](goal).
-/
abbrev Rule (n m d : Nat) :=
  {T : Sample n m d × Real → Real // Measurable T ∧ ∀ z, T z ∈ Set.Icc (-1) 1}
  -- @realizes T(Borel randomized rule clipped to [-1,1])
/--
[A data-only statistic becomes a randomized-domain rule by ignoring the independent seed](goal).
-/
def liftRule {n m d : Nat} (T : Sample n m d → Real) : Sample n m d × Real → Real :=
  fun z => T z.1

-- @env: S1
variable (n m d : Nat) (eps : Real)
variable (j : Fin d) -- @realizes j(finite covariate index)
variable (a : Bool) -- @realizes a(binary arm index)

-- @node: ass:overlap
/--
[Both arm probabilities exceed the public floor on occupied cells](goal).
-/
def Overlap {d : Nat} (eps : Real) (P : DiscreteLaw d) : Prop :=
  ∀ j, 0 < cellMass P j → eps ≤ propensity P j ∧ propensity P j ≤ 1 - eps
  -- @realizes e(occupied-cell range [epsilon,1-epsilon])

-- @node: ass:data-product
/--
[The sample law is the canonical independent product of the two channels](goal).
-/
def DataProduct {d : Nat} (P : DiscreteLaw d) (n m : Nat) (mu : Measure (Sample n m d)) : Prop :=
  mu = annotationLaw P n m
/--
[Under the stated inputs and conditions](hyp:d,P,n,m), [The canonical experiment realizes the structural independent-sampling atom](goal).
-/
-- @node: annotationLaw_dataProduct
lemma annotationLaw_dataProduct {d : Nat} (P : DiscreteLaw d) (n m : Nat) :
    DataProduct P n m (annotationLaw P n m) := by
  rfl
/--
[For a covariate dimension](hyp:d), [an overlap floor](hyp:eps), and [a population law](hyp:P),
[the model class](goal) is the proposition that the law satisfies the occupied-cell overlap condition.
-/
-- @node: def:model
structure ModelClass (d : Nat) (eps : Real) (P : DiscreteLaw d) : Prop where
  overlap : Overlap eps P -- @realizes \mathcal M(exactly the occupied-cell overlap class)
/--
[A model law pairs its population PMF with occupied-cell overlap membership](goal).
-/
abbrev ClassLaw (d : Nat) (eps : Real) := {P : DiscreteLaw d // ModelClass d eps P}
-- @node: def:target
/--
[The signed ATE sums cell mass times the treated-minus-control conditional outcome mean](goal).
-/
noncomputable def ateFunctional {d : Nat} (P : DiscreteLaw d) : Real :=
  ∑ j : Fin d, cellMass P j * (outcomeMean P true j - outcomeMean P false j)
  -- @realizes \tau(sum of cell mass times treated-minus-control regression)

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y), Every observable atom has nonnegative real mass.  This gives [the stated result](goal).-/
-- @node: jointMass_nonneg
lemma jointMass_nonneg {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a y : Bool) :
    0 ≤ jointMass P j a y := ENNReal.toReal_nonneg

/-- [Under the stated inputs and conditions](hyp:d,P,j,a), Arm masses are nonnegative, including on null cells.  This gives [the stated result](goal).-/
-- @node: armMass_nonneg
lemma armMass_nonneg {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a : Bool) :
    0 ≤ armMass P j a := Finset.sum_nonneg (fun y _ => jointMass_nonneg P j a y)

/-- [Under the stated inputs and conditions](hyp:d,P,j), Covariate masses are nonnegative.  This gives [the stated result](goal).-/
-- @node: cellMass_nonneg
lemma cellMass_nonneg {d : Nat} (P : DiscreteLaw d) (j : Fin d) :
    0 ≤ cellMass P j := Finset.sum_nonneg (fun a _ => armMass_nonneg P j a)

/-- [Under the stated inputs and conditions](hyp:d,P,a,j), Binary outcome regressions lie in the unit interval, with zero on null arms.  This gives [the stated result](goal).-/
-- @node: outcomeMean_mem_Icc
lemma outcomeMean_mem_Icc {d : Nat} (P : DiscreteLaw d) (a : Bool) (j : Fin d) :
    outcomeMean P a j ∈ Set.Icc (0 : Real) 1 := by
  have hq : 0 ≤ markedMass P j a := jointMass_nonneg P j a true
  have hs := armMass_nonneg P j a
  have hqs : markedMass P j a ≤ armMass P j a := by
    simp only [armMass, markedMass, Fintype.sum_bool]
    linarith [jointMass_nonneg P j a false]
  constructor
  · exact div_nonneg hq hs
  · by_cases hz : armMass P j a = 0
    · simp [outcomeMean, hz]
    · exact (div_le_one (lt_of_le_of_ne hs (Ne.symm hz))).mpr hqs

/-- [Under the stated inputs and conditions](hyp:d,P), The covariate masses exhaust the population probability.  This gives [the stated result](goal).-/
-- @node: sum_cellMass
lemma sum_cellMass {d : Nat} (P : DiscreteLaw d) : ∑ j, cellMass P j = 1 := by
  have hsum : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun z _ => P.pmf.apply_ne_top z)]
    have hprob : ∑ z : Obs d, P.pmf z = 1 := by
      simpa only [tsum_fintype] using P.pmf.tsum_coe
    rw [hprob, ENNReal.toReal_one]
  simpa only [cellMass, jointMass, Fintype.sum_prod_type] using hsum

/--
[Under the stated inputs and conditions](hyp:d,P), [The observable signed contrast lies between minus one and one, including null cells](goal).
-/
-- @node: ateFunctional_mem_Icc
lemma ateFunctional_mem_Icc {d : Nat} (P : DiscreteLaw d) :
    ateFunctional P ∈ Set.Icc (-1 : Real) 1 := by
  have hdiff (j : Fin d) :
      -1 ≤ outcomeMean P true j - outcomeMean P false j ∧
      outcomeMean P true j - outcomeMean P false j ≤ 1 := by
    have h1 := outcomeMean_mem_Icc P true j
    have h0 := outcomeMean_mem_Icc P false j
    constructor <;> linarith [h1.1, h1.2, h0.1, h0.2]
  constructor
  · calc
      -1 = ∑ j, cellMass P j * (-1) := by simp [sum_cellMass]
      _ ≤ ateFunctional P := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hdiff j).1 (cellMass_nonneg P j))
  · calc
      ateFunctional P ≤ ∑ j, cellMass P j * 1 := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hdiff j).2 (cellMass_nonneg P j))
      _ = 1 := by simp [sum_cellMass]
/--
[Squared-error risk integrates over both sample channels and the independent uniform
seed](goal).
-/
noncomputable def ruleRisk {n m d : Nat} (T : Sample n m d × Real → Real) (P : DiscreteLaw d) :
  Real :=
  ∫ z, (T z - ateFunctional P) ^ 2 ∂((annotationLaw P n m).prod seedLaw)
/--
[Worst-case squared-error risk takes the supremum over the overlap model class](goal).
-/
noncomputable def worstRisk {n m d : Nat} (T : Sample n m d × Real → Real) (eps : Real) : Real :=
  ⨆ P : ClassLaw d eps, ruleRisk T P.1
-- @node: def:risk
/--
[The original-experiment minimax risk infimizes worst-case risk over clipped Borel randomized
rules](goal).
-/
noncomputable def minimaxRisk (n m d : Nat) (eps : Real) : Real :=
  ⨅ T : Rule n m d, worstRisk T.1 eps -- @realizes R(canonical randomized infimum-supremum MSE)

/--
[A full atom augments the observed record with binary control and treated potential
outcomes](goal).
-/
abbrev FullObs (d : Nat) := Fin d × Bool × Bool × Bool × Bool
  -- @realizes Y_0(first potential-outcome coordinate Bool)
  -- @realizes Y_1(second potential-outcome coordinate Bool)
/--
[A potential-outcome law is a PMF on all five coordinates](goal).
-/
structure PotentialLaw (d : Nat) where
  pmf : PMF (FullObs d) -- @realizes H(joint probability law including both potential outcomes)
-- @env: S2
variable {dH : Nat} (H : PotentialLaw dH)
/--
[The real probability of a full potential-outcome atom is read from its PMF](goal).
-/
noncomputable def fullMass {d : Nat} (H : PotentialLaw d) (z : FullObs d) : Real := (H.pmf z).toReal
/--
[Marginal potential-outcome atom masses sum out the factual outcome](goal).
-/
noncomputable def poAtom {d : Nat} (H : PotentialLaw d) (j : Fin d) (a y0 y1 : Bool) : Real :=
  ∑ y : Bool, fullMass H (j, a, y, y0, y1)
/--
[A full law induces its observed complete-record marginal by coordinate projection](goal).
-/
noncomputable def observedMarginal {d : Nat} (H : PotentialLaw d) : DiscreteLaw d :=
  ⟨H.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))⟩
/--
[The causal contrast is the finite expectation of treated minus control potential
outcome](goal).
-/
noncomputable def poContrast {d : Nat} (H : PotentialLaw d) : Real :=
  ∑ z : FullObs d, fullMass H z *
    ((if z.2.2.2.2 then (1 : Real) else 0) - (if z.2.2.2.1 then (1 : Real) else 0))
-- @node: ass:consistency
/--
[Full atoms with factual outcome different from the selected potential outcome have zero
mass](goal).
-/
def Consistency {d : Nat} (H : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → fullMass H z = 0
  -- @realizes Y(observed outcome is the potential outcome selected by treatment)

-- @node: ass:exchangeability
/--
[The joint potential-outcome pair is independent of treatment given covariates, including null
cells](goal).
-/
def ConditionalExchangeability {d : Nat} (H : PotentialLaw d) : Prop :=
  ∀ j a y0 y1, poAtom H j a y0 y1 *
      (∑ a' : Bool, ∑ y0' : Bool, ∑ y1' : Bool, poAtom H j a' y0' y1') =
    (∑ y0' : Bool, ∑ y1' : Bool, poAtom H j a y0' y1') *
      (∑ a' : Bool, poAtom H j a' y0 y1)
  -- @realizes Y_0(joint conditional independence of the potential-outcome pair from A given X)
  -- @realizes Y_1(joint conditional independence of the potential-outcome pair from A given X)

/--
[Exact auxiliary tables use the product Borel space of real coordinate masses](goal).
-/
abbrev AuxTable (d : Nat) := AuxObs d → Real
/--
[The supplied side-information table is read from the actual auxiliary marginal PMF](goal).
-/
noncomputable def auxTable {d : Nat} (P : DiscreteLaw d) : AuxTable d :=
  fun z => ((auxMarginal P) z).toReal
/--
[Exact-table rules are jointly Borel in complete records, the supplied table, and the seed, with
clipped output](goal).
-/
abbrev KnownRule (n d : Nat) :=
  {T : (Fin n → Obs d) × AuxTable d × Real → Real // Measurable T ∧ ∀ z, T z ∈ Set.Icc (-1) 1}
  -- @realizes T^{\mathrm K}(jointly Borel clipped rule supplied the exact marginal and seed)
-- @env: S3
variable (TK : KnownRule n d)
/--
[An exact-table rule receives the true population marginal in its squared-error risk](goal).
-/
noncomputable def knownRuleRisk {n d : Nat}
    (T : (Fin n → Obs d) × AuxTable d × Real → Real) (P : DiscreteLaw d) : Real :=
  ∫ z, (T (z.1, auxTable P, z.2) - ateFunctional P) ^ 2 ∂((labeledProductLaw P n).prod seedLaw)
-- @node: def:known-risk
/--
[The exact-marginal minimax benchmark infimizes worst-case risk over all clipped jointly Borel
rules](goal).
-/
noncomputable def knownMarginalRisk (n d : Nat) (eps : Real) : Real :=
  ⨅ T : KnownRule n d, ⨆ P : ClassLaw d eps, knownRuleRisk T.1 P.1
  -- @realizes R^{\mathrm K}(canonical exact-table randomized minimax MSE)

/--
[Rare-label information is the complete-record budget multiplied by the overlap floor](goal).
-/
noncomputable def labelScale (n : Nat) (eps : Real) : Real := n * eps
  -- @realizes S(rare-label scale n epsilon)

/--
[The logarithmic diagnostic is the natural logarithm of exp one plus rare-label
information](goal).
-/
noncomputable def logScale (n : Nat) (eps : Real) : Real := Real.log (Real.exp 1 + labelScale n eps)
  -- @realizes \ell(natural logarithm of exp(1)+S)

/--
[The rare-label benchmark caps the inverse rare-label information at one](goal).
-/
noncomputable def labelBenchmark (n : Nat) (eps : Real) : Real := min 1 (labelScale n eps)⁻¹
  -- @realizes b(capped inverse rare-label scale)

/--
[The fixed-overlap benchmark combines inverse labeled size with the squared annotation
approximation term](goal).
-/
noncomputable def fixedOverlapBenchmark (n m d : Nat) : Real :=
  min 1 (1 / (n : Real) + (d : Real) ^ 2 / (((n : Real) + m) ^ 2 * (Real.log (Real.exp 1 * n)) ^ 2))
  -- @realizes f(fixed-floor annotation benchmark)

-- @node: def:rate-handle
/--
[The four-index frontier caps the sum of inverse rare-label scale and the squared marginal
approximation ratio](goal).
-/
noncomputable def frontierRate (n m d : Nat) (eps : Real) : Real :=
  min 1 (1 / labelScale n eps + ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
  -- @realizes r(exact evaluated four-index frontier)

/--
[Under the stated inputs and conditions](hyp:eps,hn,heps,n,m,d), [The evaluated frontier is strictly positive on the public experiment domain](goal).
-/
-- @node: frontierRate_pos
lemma frontierRate_pos (n m d : Nat) (eps : Real) (hn : 1 ≤ n) (heps : 0 < eps) :
    0 < frontierRate n m d eps := by
  have hnreal : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < labelScale n eps := mul_pos hnreal heps
  exact lt_min (by norm_num) (add_pos_of_pos_of_nonneg (one_div_pos.mpr hS) (sq_nonneg _))
/--
[Under the stated inputs and conditions](hyp:eps,n,m,d), [The evaluated frontier is capped at one](goal).
-/
-- @node: frontierRate_le_one
lemma frontierRate_le_one (n m d : Nat) (eps : Real) : frontierRate n m d eps ≤ 1 := by
  exact min_le_left _ _

/--
[Allowed public indices; scalar ranges are not additional model fields](goal).
-/
structure PublicIndex where
  n : Nat -- @realizes n(complete-record size; positive via n_pos)
  m : Nat -- @realizes m(auxiliary size in Nat, including zero)
  d : Nat -- @realizes d(alphabet size; at least two via d_ge)
  eps : Real -- @realizes \epsilon(public overlap floor)
  n_pos : 1 ≤ n -- @realizes n(range Nat at least 1)
  d_ge : 2 ≤ d -- @realizes d(range Nat at least 2)
  eps_pos : 0 < eps -- @realizes \epsilon(strictly positive)
  eps_le : eps ≤ 1 / 4 -- @realizes \epsilon(at most 1/4)
/--
[An experiment sequence is an arbitrary sequence of allowed public indices](goal).
-/
abbrev ExperimentSeq := Nat → PublicIndex
  -- @realizes \mathbf v(arbitrary sequences of allowed experiments)
-- @env: S4
variable (v : ExperimentSeq) (k : Nat) -- @realizes k(zero-based sequence index; same tails)
/--
[The risk of a public index evaluates the canonical original-experiment minimax value](goal).
-/
noncomputable def PublicIndex.risk (v : PublicIndex) : Real := minimaxRisk v.n v.m v.d v.eps
-- @node: def:phases
/--
[The consistency phase consists of sequences with minimax risk tending to zero](goal).
-/
def consistencyPhase : Set ExperimentSeq :=
  {v | Filter.Tendsto (fun k => (v k).risk) Filter.atTop (nhds 0)}
  -- @realizes \mathcal C(sequences with vanishing minimax risk)
/--
[The oracle phase requires diverging rare-label information and an eventually bounded
risk-to-benchmark ratio](goal).
-/
def oraclePhase : Set ExperimentSeq :=
  {v | Filter.Tendsto (fun k => labelScale (v k).n (v k).eps) Filter.atTop Filter.atTop ∧
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun k => (v k).risk / labelBenchmark (v k).n (v
      k).eps)}
  -- @realizes \mathcal O(diverging label scale and bounded risk-to-benchmark ratio)
/--
[Strict auxiliary improvement means risk divided by the supervised risk tends to zero](goal).
-/
def improvementPhase : Set ExperimentSeq :=
  {v | Filter.Tendsto (fun k => (v k).risk / minimaxRisk (v k).n 0 (v k).d (v k).eps)
    Filter.atTop (nhds 0)} -- @realizes \mathcal I(strict improvement over the supervised risk)

end CausalSmith.Stat.AnnotationRarearmFrontier
