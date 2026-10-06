module
public import Causalean.Experimentation.DesignBased.LocalDependenceVariance
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Fixed additive schedules and the complete thinned record

Raw directed coefficients are needed for the schedule class and the hidden-allocation prior.
The exposure-based potential-outcome substrate and superpopulation PO systems are therefore
bypassed. The out-degree predicate and extended minimax carrier reuse Causalean directly.
The design is Measure-valued to permit continuous baseline mixtures and an independent seed;
the finite Bernoulli design is used through the expectation bridge in Helpers/DesignBridge.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

-- @env: S1
variable {V : Type*} [Fintype V] [DecidableEq V]
-- @realizes n(Fintype.card V; n ≥ 4 in theorem regimes)
-- @realizes i(recipient index in V)
-- @realizes j(source index in V)

/-- The paper population has n units; the paper label of i is i.val + 1. -/
abbrev PopulationCarrier (n : ℕ) (_hn : 4 ≤ n) : Type := Fin n
-- @realizes V(Fin n, with paper labels i.val+1, under n ≥ 4)

/-- A fixed simple directed off-diagonal graph with additive coefficients. -/
structure Schedule (V : Type*) where
  edge : V → V → Prop -- @realizes G(directed arrows from source j to recipient i)
  decEdge : DecidableRel edge
  irrefl : ∀ i, ¬ edge i i -- @realizes G(off-diagonal graph)
  a : V → ℝ -- @realizes a(fixed real baseline vector)
  t : V → ℝ -- @realizes t(fixed real own-effect vector)
  b : V → V → ℝ -- @realizes b(real coefficients read only on graph arrows; zeros permitted)
-- @realizes theta(fixed graph and additive coefficient schedule)

/-- The off-diagonal treatment sources of a recipient. -/
def inNbhd (θ : Schedule V) (i : V) : Finset V :=
  Finset.univ.filter (fun j => θ.edge j i)

/-- The zero-one numeric value of a treatment coordinate. -/
def treatment (z : Bool) : ℝ := if z then 1 else 0

/-- The centered sign, twice treatment minus one. -/
def signOf (z : Bool) : ℝ := if z then 1 else - 1
-- @realizes X(centered signs 2Z_j-1)
-- @realizes sigma(Bool-coded sign in {-1,1})

/-- The additive potential outcome. -/
def potentialOutcome (θ : Schedule V) (i : V) (z : V → Bool) : ℝ :=
  θ.a i + θ.t i * treatment (z i) + ∑ j ∈ inNbhd θ i, θ.b i j * treatment (z j)
-- @realizes z(generic assignment in {0,1}^V)
-- @realizes Y(additive potential-outcome map)

/-- The all-treated minus all-control population average. -/
def tte (θ : Schedule V) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ * ∑ i,
    (potentialOutcome θ i (fun _ => true) - potentialOutcome θ i (fun _ => false))
-- @realizes tau(average all-treated minus all-control causal effect)

/-- Each recipient has at most d off-diagonal sources. -/
-- @node: ass:in-degree
def InDegreeLE (θ : Schedule V) (d : ℕ) : Prop := ∀ i, (inNbhd θ i).card ≤ d
-- @realizes d(common off-diagonal degree bound; admissibility in theorem binders)

/-- The row coefficient mass includes the baseline and own coordinate. -/
-- @node: ass:coefficient-mass
def CoefficientMassLE (θ : Schedule V) : Prop :=
  ∀ i, |θ.a i| + |θ.t i| + ∑ j ∈ inNbhd θ i, |θ.b i j| ≤ 1
-- @realizes a(baseline participates in the row absolute-coefficient envelope)
-- @realizes t(own effect participates in the row absolute-coefficient envelope)
-- @realizes b(on-graph spillovers participate in the row absolute-coefficient envelope)

/-- The additive fixed-schedule model class. -/
-- @node: def:model
structure ScheduleClass (θ : Schedule V) (d : ℕ) : Prop where
  inDegree : InDegreeLE θ d
  -- The imported predicate is the sole realization of the off-diagonal out-degree atom.
  outDegree : Causalean.Experimentation.DesignBased.BlockDegreeLE (inNbhd θ) d
  coeffMass : CoefficientMassLE θ
-- @realizes Mclass(both off-diagonal degrees ≤ d and row coefficient mass ≤ 1)

/-- Enlarging the degree bound preserves schedule membership.  [For the stated data and conditions](hyp:θ,d,d',h,hdd'), [the stated conclusion holds](goal). -/
-- @node: ScheduleClass.mono
lemma ScheduleClass.mono {θ : Schedule V} {d d' : ℕ}
    (h : ScheduleClass θ d) (hdd' : d ≤ d') : ScheduleClass θ d' := by
  exact ⟨fun i => (h.inDegree i).trans hdd',
    fun j => (h.outDegree j).trans hdd', h.coeffMass⟩

/-- The coefficient-mass envelope bounds every potential outcome by one.  [For the stated data and conditions](hyp:θ,d,h,i,z), [the stated conclusion holds](goal). -/
-- @node: abs_potentialOutcome_le_one
lemma abs_potentialOutcome_le_one {θ : Schedule V} {d : ℕ}
    (h : ScheduleClass θ d) (i : V) (z : V → Bool) :
    |potentialOutcome θ i z| ≤ 1 := by
  have hterm (c : ℝ) (b : Bool) : |c * treatment b| ≤ |c| := by
    cases b <;> simp [treatment]
  calc
    |potentialOutcome θ i z| ≤ |θ.a i| + |θ.t i * treatment (z i)| +
        |∑ j ∈ inNbhd θ i, θ.b i j * treatment (z j)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |θ.a i| + |θ.t i| + ∑ j ∈ inNbhd θ i, |θ.b i j| := by
      apply add_le_add
      · exact add_le_add le_rfl (hterm _ _)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hterm _ _)
    _ ≤ 1 := h.coeffMass i

/-- The coefficient-mass envelope bounds the total treatment effect by one.  [For the stated data and conditions](hyp:θ,d,h), [the stated conclusion holds](goal). -/
-- @node: abs_tte_le_one
lemma abs_tte_le_one {θ : Schedule V} {d : ℕ}
    (h : ScheduleClass θ d) : |tte θ| ≤ 1 := by
  have hcontrast (i : V) :
      |potentialOutcome θ i (fun _ => true) -
        potentialOutcome θ i (fun _ => false)| ≤ 1 := by
    have hmass := h.coeffMass i
    have hsum := Finset.abs_sum_le_sum_abs (fun j => θ.b i j) (inNbhd θ i)
    simp only [potentialOutcome, treatment, Bool.false_eq_true, ite_false, ite_true,
      mul_one, mul_zero, Finset.sum_const_zero, add_zero] at ⊢
    have heq : θ.a i + θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j - θ.a i =
        θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j := by ring
    rw [heq]
    calc
      |θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j| ≤
          |θ.t i| + |∑ j ∈ inNbhd θ i, θ.b i j| := abs_add_le _ _
      _ ≤ |θ.t i| + ∑ j ∈ inNbhd θ i, |θ.b i j| := add_le_add le_rfl hsum
      _ ≤ 1 := by linarith [abs_nonneg (θ.a i)]
  calc
    |tte θ| = (Fintype.card V : ℝ)⁻¹ *
        |∑ i, (potentialOutcome θ i (fun _ => true) -
          potentialOutcome θ i (fun _ => false))| := by
      rw [tte, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card V : ℝ)⁻¹)]
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => hcontrast i)
    _ ≤ 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      by_cases hn : (Fintype.card V : ℝ) = 0
      · simp [hn]
      · rw [inv_mul_cancel₀ hn]

-- @env: S2
variable (V)

/-- Ordered off-diagonal source-recipient labels. -/
abbrev OffDiag := {e : V × V // e.1 ≠ e.2}
/-- Complete treatment assignment. -/
abbrev Assign := V → Bool -- @realizes Z(all treatment coordinates)
/-- Latent independent audit marks, including marks on nonedges. -/
abbrev Audit := OffDiag V → Bool -- @realizes W(all ordered off-diagonal mark coordinates)
/-- The full graph, treatment, and noiseless outcome record. -/
abbrev Record := (OffDiag V → Bool) × (V → Bool) × (V → ℝ)
-- @realizes O(complete record H,Z,Y(Z))
-- @realizes H(off-diagonal labeled recorded graph indicator)

/-- A two-atom Bernoulli measure, total also outside the probability regime. -/
def bernoulliLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true

/-- Independent half-Bernoulli assignments. -/
def halfBernoulli : Measure (Assign V) := Measure.pi (fun _ : V => bernoulliLaw (1 / 2))

/-- Independent edge audit with retention q; endpoints are point masses. -/
def auditLaw (q : ℝ) : Measure (Audit V) :=
  Measure.pi (fun _ : OffDiag V => bernoulliLaw q)
-- @realizes q(retention parameter; constrained to [0,1] in AuditLaw and theorem regimes)

/-- The canonical independent assignment-audit product design. -/
def thinnedDesign (q : ℝ) : Measure (Assign V × Audit V) :=
  (halfBernoulli V).prod (auditLaw V q)

variable {V}
/-- Probability-design scope for the extended minimax risk. -/
def ProbabilityDesign (D : Measure (Assign V × Audit V)) : Prop := IsProbabilityMeasure D
-- @realizes R(probability-design restriction on the generic risk carrier)

/-- The finite Bernoulli marginal is a probability measure at admissible retention.  [For the stated data and conditions](hyp:p,hp), [the stated conclusion holds](goal). -/
-- @node: bernoulliLaw_probability
lemma bernoulliLaw_probability (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (bernoulliLaw p) := by
  simpa only [bernoulliLaw, Causalean.Mathlib.Probability.bernoulliBool, add_comm] using
    Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hp.1 hp.2

/-- Admissible retention makes the canonical experiment a probability design.  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: thinnedDesign_probabilityDesign
lemma thinnedDesign_probabilityDesign (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    ProbabilityDesign (thinnedDesign V q) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (bernoulliLaw q) := bernoulliLaw_probability q hq
  unfold ProbabilityDesign thinnedDesign halfBernoulli auditLaw
  infer_instance

/-- The assignment marginal is the product half-Bernoulli law. -/
-- @node: ass:assignment
def AssignmentLaw (D : Measure (Assign V × Audit V)) : Prop :=
  D.map Prod.fst = halfBernoulli V

/-- The audit marginal is the independent product law with admissible retention. -/
-- @node: ass:audit
def AuditLaw (D : Measure (Assign V × Audit V)) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ D.map Prod.snd = auditLaw V q
-- @realizes q(0 ≤ q ≤ 1)

/-- Assignment and audit coordinates are independent. -/
-- @node: ass:design-independence
def DesignIndependent (D : Measure (Assign V × Audit V)) : Prop :=
  ProbabilityTheory.IndepFun Prod.fst Prod.snd D

/-- The original record retains precisely the audited true arrows. -/
def recordOf (θ : Schedule V) (ω : Assign V × Audit V) : Record V :=
  (fun e => decide (θ.edge e.1.1 e.1.2) && ω.2 e,
   ω.1, fun i => potentialOutcome θ i ω.1)
-- @realizes H(true off-diagonal arrows intersected with retained audit marks)

/-- An independent uniform seed on the unit interval. -/
def seedLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)
-- @realizes xi(independent uniform randomization on [0,1])

/-- The fixed-schedule seeded original-record law. -/
def recordLaw (D : Measure (Assign V × Audit V)) (θ : Schedule V) :
    Measure (Record V × ℝ) :=
  (D.prod seedLaw).map (fun ω => (recordOf θ ω.1, ω.2))
-- @realizes P(law of complete original record and independent seed)

-- @env: S3
variable (V)
/-- All measurable real-valued randomized estimators of the complete record. -/
abbrev Estimator := {T : Record V × ℝ → ℝ // Measurable T}
-- @realizes T(Borel measurable seeded estimator, unrestricted use of outcomes)
variable {V}

/-- Extended nonnegative squared loss avoids nonintegrable-real-integral junk values. -/
def sqLoss (D : Measure (Assign V × Audit V)) (θ : Schedule V) (T : Estimator V) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((T.1 x - tte θ) ^ 2) ∂(recordLaw D θ)
-- @realizes L(expected squared loss in [0,∞])

/-- Worst-case risk over the fixed schedule class. -/
def worstRisk (D : Measure (Assign V × Audit V)) (d : ℕ) (T : Estimator V) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (T : Estimator V) (θ : {θ : Schedule V // ScheduleClass θ d}) => sqLoss D θ.1 T) T

/-- The unrestricted minimax risk, built on the substrate extended minimax value. -/
-- @node: def:risk
def minimaxRisk (D : Measure (Assign V × Audit V)) (d : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : Estimator V) (θ : {θ : Schedule V // ScheduleClass θ d}) => sqLoss D θ.1 T)
-- @realizes R(infimum over measurable randomized estimators of supremum schedule risk)

variable (V)

/-- The complete original record together with the true off-diagonal graph. -/
abbrev SuppliedRecord := Record V × (OffDiag V → Bool)

/-- All measurable randomized estimators when the true graph is supplied. -/
abbrev SuppliedEstimator := {T : SuppliedRecord V × ℝ → ℝ // Measurable T}

variable {V}

/-- The true off-diagonal graph as a labeled Boolean array. -/
def suppliedGraphOf (θ : Schedule V) : OffDiag V → Bool :=
  fun e => decide (θ.edge e.1.1 e.1.2)

/-- The original record and the supplied true graph under one design realization. -/
def suppliedRecordOf (θ : Schedule V) (ω : Assign V × Audit V) : SuppliedRecord V :=
  (recordOf θ ω, suppliedGraphOf θ)

/-- The fixed-schedule law of the supplied-graph record and an independent seed. -/
def suppliedRecordLaw (D : Measure (Assign V × Audit V)) (θ : Schedule V) :
    Measure (SuppliedRecord V × ℝ) :=
  (D.prod seedLaw).map (fun ω => (suppliedRecordOf θ ω.1, ω.2))

/-- Extended squared risk of an estimator that observes the true graph. -/
def suppliedSqLoss (D : Measure (Assign V × Audit V)) (θ : Schedule V)
    (T : SuppliedEstimator V) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((T.1 x - tte θ) ^ 2) ∂(suppliedRecordLaw D θ)

/-- Worst-case supplied-graph risk over the unchanged fixed schedule class. -/
def suppliedWorstRisk (D : Measure (Assign V × Audit V)) (d : ℕ)
    (T : SuppliedEstimator V) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (T : SuppliedEstimator V) (θ : {θ : Schedule V // ScheduleClass θ d}) =>
      suppliedSqLoss D θ.1 T) T

/-- Minimax squared risk when the complete original record and true graph are supplied. -/
-- @node: def:supplied-risk
def suppliedMinimaxRisk
    (D : Measure (Assign V × Audit V)) (d : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : SuppliedEstimator V) (θ : {θ : Schedule V // ScheduleClass θ d}) =>
      suppliedSqLoss D θ.1 T)

/-- The zero estimator bounds minimax risk by one on any probability design.  [For the stated data and conditions](hyp:D,hD,d), [the stated conclusion holds](goal). -/
-- @node: minimaxRisk_le_one
lemma minimaxRisk_le_one (D : Measure (Assign V × Audit V)) (hD : ProbabilityDesign D)
    (d : ℕ) : minimaxRisk D d ≤ 1 := by
  let : IsProbabilityMeasure D := hD
  let : IsProbabilityMeasure seedLaw := ⟨by simp [seedLaw, Real.volume_Icc]⟩
  let T : Estimator V := ⟨fun _ => 0, measurable_const⟩
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro θ
  have hm : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
      (recordOf θ.1 ω.1, ω.2)) := by
    have hr : Measurable (recordOf θ.1) := by
      fun_prop (disch := exact Measurable.of_discrete)
    exact (hr.comp measurable_fst).prodMk measurable_snd
  let : IsProbabilityMeasure (recordLaw D θ.1) :=
    (D.prod seedLaw).isProbabilityMeasure_map hm.aemeasurable
  have ht : (tte θ.1) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (abs_tte_le_one θ.2)
  unfold sqLoss
  calc
    (∫⁻ x, ENNReal.ofReal ((T.1 x - tte θ.1) ^ 2) ∂recordLaw D θ.1) ≤
        ∫⁻ _x, (1 : ℝ≥0∞) ∂recordLaw D θ.1 := by
      apply lintegral_mono
      intro x
      simpa [T] using (ENNReal.ofReal_le_ofReal ht)
    _ = 1 := by simp
-- @realizes R(finite ENNReal risk, at most one on probability designs)

/-- The paper's supplied-graph minimax risk at admissible population, degree and retention. -/
abbrev RG (n d : ℕ) (q : ℝ) (_hn : 4 ≤ n) (_hd : 1 ≤ d)
    (_hdu : d ≤ n - 1) (_hq : q ∈ Set.Icc 0 1) : ℝ≥0∞ :=
  suppliedMinimaxRisk (thinnedDesign (Fin n) q) d
-- @realizes RG(canonical probability-design infimum-supremum at admissible n,d,q)

/-- Canonical-design minimax risk. -/
abbrev R (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) (q : ℝ) : ℝ≥0∞ :=
  minimaxRisk (thinnedDesign V q) d

/-- The recorded sources of a recipient, read solely from the observed record. -/
def recordedNbhd (H : OffDiag V → Bool) (i : V) : Finset V :=
  Finset.univ.filter (fun j => ∃ hji : j ≠ i, H ⟨(j, i), hji⟩ = true)

/-- The observable inverse-edge-inclusion additive score. -/
-- @node: def:audit-score
def auditScore (q : ℝ) (o : Record V) : ℝ :=
  (2 / (Fintype.card V : ℝ)) * ∑ i,
    o.2.2 i * (signOf (o.2.1 i) + q⁻¹ * ∑ j ∈ recordedNbhd o.1 i, signOf (o.2.1 j))
-- @realizes Tq(inverse-inclusion score using only H,Z,Y(Z),n,q)

/-- [The finite observed graph and assignments give measurable score weights, with the outcome
coordinates entering by a finite linear combination](goal). -/
-- @node: auditScore_measurable
@[fun_prop] lemma auditScore_measurable (q : ℝ) :
    Measurable (auditScore (V := V) q) := by
  have hw (i : V) : Measurable (fun o : Record V =>
      signOf (o.2.1 i) + q⁻¹ * ∑ j ∈ recordedNbhd o.1 i, signOf (o.2.1 j)) := by
    exact (Measurable.of_discrete (f := fun hz : (OffDiag V → Bool) × Assign V =>
      signOf (hz.2 i) + q⁻¹ * ∑ j ∈ recordedNbhd hz.1 i, signOf (hz.2 j))).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  unfold auditScore
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_snd.comp measurable_snd).eval.mul (hw i))

/-- The additive supplied-graph score. -/
-- @node: def:oracle-score
def oracleScore (θ : Schedule V) (z : Assign V) : ℝ :=
  (2 / (Fintype.card V : ℝ)) * ∑ i,
    potentialOutcome θ i z * (signOf (z i) + ∑ j ∈ inNbhd θ i, signOf (z j))
-- @realizes TG(supplied-graph score)

/-- The risk envelope is infinite at zero retention. -/
-- @node: def:upper-envelope
def upperEnvelope (n d : ℕ) (q : ℝ) : ℝ≥0∞ :=
  if 0 < q then ENNReal.ofReal
    (5 * ((d : ℝ) + 1) ^ 2 / n + 4 * d * (1 - q) / (n * q)) else ⊤
-- @realizes upper(total extended risk envelope)

/-- The total clipped-or-zero observable rule. -/
-- @node: def:upper-rule
def upperRule (n d : ℕ) (q : ℝ) (o : Record V) : ℝ :=
  if 0 < q ∧ upperEnvelope n d q < 1 then max (-1) (min 1 (auditScore q o)) else 0
-- @realizes Tup(total rule with range [-1,1])

/-- [The clipped-or-zero rule is measurable on the entire record space](goal). -/
-- @node: upperRule_measurable
@[fun_prop]
lemma upperRule_measurable (n d : ℕ) (q : ℝ) :
    Measurable (upperRule (V := V) n d q) := by
  unfold upperRule
  split_ifs <;> fun_prop

/-- [Ignoring the independent seed preserves measurability of the upper rule](goal). -/
-- @node: upperRule_seeded_measurable
@[fun_prop]
lemma upperRule_seeded_measurable (n d : ℕ) (q : ℝ) :
    Measurable (fun x : Record V × ℝ => upperRule n d q x.1) := by
  fun_prop

/-- The measurable seeded representative of the total upper rule. -/
def upperEstimator (n d : ℕ) (q : ℝ) : Estimator V :=
  ⟨fun x => upperRule n d q x.1, upperRule_seeded_measurable n d q⟩

/-- The explicit positive finite precision scale on the admissible regime. -/
-- @node: def:frontier-scale
def frontierScale (n d : ℕ) (q : ℝ) : ℝ :=
  if 0 < q then min 1 ((d : ℝ) ^ 2 / (n * (1 - (1 - q) ^ d))) else 1
-- @realizes F(explicit scale min{1,d²/(np)}, with value one at zero retention)

/-- The attaining observable rule is the clipped-or-zero rule. -/
-- @node: def:frontier-rule
def frontierRule (n d : ℕ) (q : ℝ) : Record V → ℝ := upperRule n d q
-- @realizes Tstar(transparent alias of the total observable upper rule)

/-- The seeded measurable representative of the attaining frontier rule. -/
def frontierEstimator (n d : ℕ) (q : ℝ) : Estimator V := upperEstimator n d q

/-- Names the scale-rule pair without inserting any proved risk properties. -/
-- @node: def:frontier-handle
def frontierHandle (n d : ℕ) (q : ℝ) : ℝ × (Record (Fin n) → ℝ) :=
  (frontierScale n d q, frontierRule n d q)

/-- Admissible degree and retention sequences, with only the n ≥ 4 tail constrained. -/
def AdmissibleSequences (dseq : ℕ → ℕ) (qseq : ℕ → ℝ) : Prop :=
  ∀ n, 4 ≤ n → -- @realizes n(population sequence begins at n ≥ 4)
    1 ≤ dseq n ∧ dseq n ≤ n - 1 ∧ -- @realizes dseq(1 ≤ d_n ≤ n-1)
    qseq n ∈ Set.Icc 0 1 -- @realizes qseq(known retentions in [0,1])
-- @realizes dseq(degree sequence with 1 ≤ d_n ≤ n-1 for n ≥ 4)
-- @realizes qseq(retention sequence in [0,1] for n ≥ 4)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
