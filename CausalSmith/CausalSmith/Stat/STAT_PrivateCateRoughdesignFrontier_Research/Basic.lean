module
public import Causalean.Stat.Coupling.Basic
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Privacy.LaplaceMechanism
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Moments.Variance
/-! Concrete causal laws, selected observational versions, private kernels and extended-real
minimax criteria. Published inequalities are explicit conditional gates. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The covariate takes values in the closed unit interval. -/
abbrev Covariate := unitInterval -- @realizes X(carrier [0,1])
/-- Observed records consist of a covariate and two binary marks for treatment and outcome. -/
abbrev O := Covariate × Bool × Bool -- @realizes O(observed binary record)
/-- Full causal records also carry the two binary potential outcomes. -/
abbrev Record := Covariate × Bool × (Bool × Bool) × Bool
/-- A dataset is a finite tuple of observed records indexed by the public sample size. -/
abbrev Dataset (n : ℕ) := Fin n → O -- @realizes D(carrier O^n)
/-- A binary mark is represented numerically by zero or one. -/
def bit (a : Bool) : ℝ := if a then 1 else 0
/-- The covariate coordinate of a full causal record. -/
def X (z : Record) : Covariate := z.1 -- @realizes X(covariate projection)
/-- The binary treatment coordinate of a full causal record. -/
def A (z : Record) : Bool := z.2.1 -- @realizes A(binary treatment)
/-- The control and treated potential outcomes of a full causal record. -/
def Ypot (z : Record) : Bool × Bool := z.2.2.1 -- @realizes Ypot(binary potential pair)
/-- The observed binary outcome coordinate of a full causal record. -/
def Y (z : Record) : Bool := z.2.2.2 -- @realizes Y(binary observed outcome)
/-- Observation forgets the potential outcomes and retains covariate, treatment and outcome. -/
def observe (z : Record) : O := (X z, A z, Y z)
/-- The covariate coordinate is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_X
@[fun_prop] lemma measurable_X : Measurable X := by
  unfold X
  fun_prop

/-- The public regularity radius is fixed at three. -/
def L : ℝ := 3 -- @realizes L(fixed radius)
/-- The evaluation point one half belongs to the closed unit interval.  [the asserted conclusion follows](goal). -/
-- @node: half_mem_unitInterval
lemma half_mem_unitInterval : (1 / 2 : ℝ) ∈ Icc 0 1 := by
  constructor <;> norm_num
/-- The public evaluation point is one half. -/
def x0 : Covariate := ⟨1/2, half_mem_unitInterval⟩ -- @realizes x0(evaluation point)

/-- The version identities pin the density and the three observational regressions to the law.
The arm means are integrable for their arm-specific covariate measures, without interior bounds. -/
structure CausalLaw where
  law : Measure Record -- @realizes P(Borel measure on full records)
  probability : IsProbabilityMeasure law -- @realizes P(probability normalization)
  f : Covariate → ℝ -- @realizes f(selected density carrier)
  e : Covariate → ℝ -- @realizes e(selected propensity carrier)
  mu0 : Covariate → ℝ -- @realizes mu0(selected control regression carrier)
  mu1 : Covariate → ℝ -- @realizes mu1(selected treated regression carrier)
  f_measurable : Measurable f -- @realizes f(measurable version)
  e_measurable : Measurable e -- @realizes e(measurable version)
  mu0_measurable : Measurable mu0 -- @realizes mu0(measurable version)
  mu1_measurable : Measurable mu1 -- @realizes mu1(measurable version)
  density_version : law.map X ≪ volume →
    law.map X = volume.withDensity (fun x => ENNReal.ofReal (f x)) -- @realizes f(dP_X/dx)
  e_integrable : Integrable e (law.map X)
  mu0_integrable : Integrable mu0 ((law.restrict {z | A z = false}).map X)
  mu1_integrable : Integrable mu1 ((law.restrict {z | A z = true}).map X)
  e_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, e x ∂(law.map X) = -- @realizes e(conditional probability)
      law.real {z | X z ∈ s ∧ A z = true}
  mu0_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, mu0 x ∂((law.restrict {z | A z = false}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = false}, bit (Y z) ∂law -- @realizes mu0(arm conditional mean)
  mu1_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, mu1 x ∂((law.restrict {z | A z = true}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = true}, bit (Y z) ∂law -- @realizes mu1(arm conditional mean)

/-- The bundled causal law carries its probability-measure instance. -/
instance (P : CausalLaw) : IsProbabilityMeasure P.law := P.probability
/-- The observed marginal is the pushforward of the causal law by observation. -/
def Pobs (P : CausalLaw) : Measure O := P.law.map observe -- @realizes Pobs(observed marginal)
/-- The design marginal is the pushforward of the causal law by the covariate coordinate. -/
def PX (P : CausalLaw) : Measure Covariate := P.law.map X
/-- The selected observational contrast is the treated regression minus the control regression. -/
def tau (P : CausalLaw) (x : Covariate) : ℝ := P.mu1 x - P.mu0 x -- @realizes tau(mu1 - mu0)
/-- The point target evaluates the selected contrast at one half. -/
def theta (P : CausalLaw) : ℝ := tau P x0 -- @realizes theta(point target)
/-- The dataset law is the finite product of the observed marginal. -/
def dataLaw (n : ℕ) (P : CausalLaw) : Measure (Dataset n) :=
  Measure.pi (fun _ : Fin n => Pobs P)
-- @env: S1
variable (n : ℕ) -- @realizes n(public sample-size carrier)
variable (P : CausalLaw)
-- @node: ass:iid
/-- The sampling hypothesis identifies the dataset distribution with that observed product law. -/
def IIDSampling (Q : Measure (Dataset n)) : Prop := Q = dataLaw n P
-- @node: ass:consistency
/-- The observed outcome agrees almost surely with the potential outcome selected by treatment. -/
def Consistency : Prop := ∀ᵐ z ∂P.law, Y z = if A z then (Ypot z).2 else (Ypot z).1
-- @node: ass:exchangeability
/-- The potential-outcome pair and treatment are conditionally independent given the covariate. -/
def Exchangeability : Prop :=
  CondIndepFun (MeasurableSpace.comap X inferInstance) measurable_X.comap_le Ypot A P.law
-- @node: ass:density
/-- The design marginal is absolutely continuous and its selected density is between one half and
three halves almost everywhere for Lebesgue measure. -/
def DensityBounds : Prop :=
  PX P ≪ volume ∧ -- @realizes f(absolute continuity of covariate marginal)
  ∀ᵐ x ∂(volume : Measure Covariate), -- @realizes f(a.e. design bounds)
    1/2 ≤ P.f x ∧ P.f x ≤ 3/2
-- @node: ass:overlap
/-- The selected propensity is between one quarter and three quarters at every covariate. -/
def Overlap : Prop := ∀ x, 1/4 ≤ P.e x ∧ P.e x ≤ 3/4 -- @realizes e(everywhere overlap)
-- @node: ass:propensity-holder
/-- The selected propensity obeys the one-tenth Holder modulus with radius three. -/
def PropensityHolder : Prop :=
  ∀ x x', |P.e x - P.e x'| ≤ L * |(x : ℝ) - x'| ^ (1/10 : ℝ) -- @realizes e(Holder 1/10 radius 3)
-- @node: ass:control-holder
/-- The selected control regression obeys the one-tenth Holder modulus with radius three. -/
def ControlHolder : Prop :=
  ∀ x x', |P.mu0 x - P.mu0 x'| ≤ L * |(x : ℝ) - x'| ^ (1/10 : ℝ) -- @realizes mu0(Holder radius 3)
-- @node: ass:contrast-lipschitz
/-- The selected contrast obeys the Lipschitz modulus with radius three. -/
def ContrastLipschitz : Prop :=
  ∀ x x', |tau P x - tau P x'| ≤ L * |(x : ℝ) - x'| -- @realizes tau(Lipschitz radius 3)
-- @node: def:complete-model
/-- The complete law class bundles consistency, exchangeability, density, overlap and the three
specified regularity conditions. -/
structure CompleteModel : Prop where
  consistency : Consistency P
  exchangeability : Exchangeability P
  density : DensityBounds P
  overlap : Overlap P
  propensity_holder : PropensityHolder P
  control_holder : ControlHolder P
  contrast_lipschitz : ContrastLipschitz P

variable {B : Type*} [MeasurableSpace B] -- @realizes B(measurable output carrier)
-- @env: S2
variable (epsilon : ℝ) -- @realizes epsilon(public real privacy budget)
variable (M : Kernel (Dataset n) B) -- @realizes M(total measurable kernel)
-- @realizes dHam(replacement Hamming distance)
/-- The Hamming distance counts the records at which two datasets differ. -/
def dHam (D Dprime : Dataset n) : ℕ := hammingDist D Dprime
-- @node: ass:pure-privacy
/-- Replacement privacy bounds every measurable output event on every adjacent pair of input
datasets. -/
def PurePrivacy : Prop := ∀ D Dprime : Dataset n, -- @realizes Dprime(comparison dataset O^n)
  dHam n D Dprime = 1 → ∀ E, MeasurableSet E →
    (M D).real E ≤ Real.exp epsilon * (M Dprime).real E
-- @node: def:private-kernels
/-- The private-kernel predicate bundles Markov normalization and replacement privacy. -/
structure PrivateKernel : Prop where
  markov : IsMarkovKernel M
  pure_privacy : PurePrivacy n epsilon M

-- @realizes TV(total variation of probability laws; substrate primitive)
/-- Total variation is the substrate distance between probability measures on a common measurable
space. -/
abbrev TV {α : Type*} [MeasurableSpace α] (Q Q' : Measure α) : ℝ :=
  Causalean.Stat.tvDist Q Q'
-- @realizes WH(infimum of expected Hamming costs over couplings)
/-- Hamming transport is the extended-real infimum of expected dataset Hamming distance over all
couplings. -/
def WH (Q Q' : Measure (Dataset n)) : ℝ≥0∞ :=
  ⨅ (γ : Measure (Dataset n × Dataset n)) (_ : Causalean.Stat.IsCoupling γ Q Q'),
    ∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂γ
-- @realizes Ispace(endpoint and inclusion codes, including empty and unbounded intervals)
/-- Connected Borel intervals are represented by extended endpoints and inclusion flags, with a
separate empty code. -/
abbrev IntervalCode := Unit ⊕ (EReal × EReal × Bool × Bool)
/-- The empty-or-endpoints representation has the Borel sigma algebra of its sum topology.
This representation property is derived locally, rather than assumed by headline consumers.  [the asserted conclusion follows](goal). -/
-- @node: intervalCode_borelSpace
lemma intervalCode_borelSpace : BorelSpace IntervalCode := by
  constructor
  apply le_antisymm
  · intro s hs
    have hparts := measurableSet_sum_iff.mp hs
    letI : MeasurableSpace IntervalCode := borel IntervalCode
    letI : BorelSpace IntervalCode := ⟨rfl⟩
    have hel : MeasurableEmbedding (Sum.inl : Unit → IntervalCode) :=
      Topology.IsOpenEmbedding.inl.measurableEmbedding
    have her : MeasurableEmbedding (Sum.inr : EReal × EReal × Bool × Bool → IntervalCode) :=
      Topology.IsOpenEmbedding.inr.measurableEmbedding
    have hl := hel.measurableSet_image.mpr hparts.1
    have hr := her.measurableSet_image.mpr hparts.2
    simpa only [Set.image_preimage_inl_union_image_preimage_inr] using hl.union hr
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(hs.preimage continuous_inl).measurableSet,
        (hs.preimage continuous_inr).measurableSet⟩
/-- The interval representation carries its derived Borel-space instance. -/
instance : BorelSpace IntervalCode := intervalCode_borelSpace -- @realizes Ispace(Borel coding)
/-- An interval code denotes the corresponding connected subset of the real line. -/
def IntervalCode.toSet (c : IntervalCode) : Set ℝ := match c with
  | .inl _ => ∅
  | .inr (l,u,lc,uc) => {x | (if lc then l ≤ (x : EReal) else l < (x : EReal)) ∧
      (if uc then (x : EReal) ≤ u else (x : EReal) < u)}
/-- The length of a coded interval is its possibly infinite Lebesgue measure. -/
def IntervalCode.leb (c : IntervalCode) : ℝ≥0∞ := volume c.toSet

/-- Absolute risk integrates both the observed dataset distribution and randomized scalar output. -/
def scalarRisk (T : Kernel (Dataset n) ℝ) (P : CausalLaw) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal |u - theta P| ∂(T ∘ₘ dataLaw n P)
/-- Expected interval length integrates both the observed dataset distribution and randomized
interval output. -/
def expectedLength (I : Kernel (Dataset n) IntervalCode) (P : CausalLaw) : ℝ≥0∞ :=
  ∫⁻ c, c.leb ∂(I ∘ₘ dataLaw n P)
/-- Coverage is the probability that the randomized coded interval contains the law-specific point
target. -/
def coverage (I : Kernel (Dataset n) IntervalCode) (P : CausalLaw) : ℝ :=
  (I ∘ₘ dataLaw n P).real {c | theta P ∈ c.toSet}
/-- Maximal absolute risk is the extended-real supremum across the complete law class. -/
def worstRisk (T : Kernel (Dataset n) ℝ) : ℝ≥0∞ :=
  ⨆ P, ⨆ (_ : CompleteModel P), scalarRisk n T P
/-- Maximal expected length is the extended-real supremum across the complete law class. -/
def worstLength (I : Kernel (Dataset n) IntervalCode) : ℝ≥0∞ :=
  ⨆ P, ⨆ (_ : CompleteModel P), expectedLength n I P
/-- The same absolute-risk criterion without a privacy restriction. -/
def nonprivateMinimaxRisk : ℝ≥0∞ :=
  ⨅ (T : Kernel (Dataset n) ℝ) (_ : IsMarkovKernel T), worstRisk n T
-- @node: def:risk-criterion
-- @realizes R(private minimax absolute risk, with infinite losses allowed)
/-- Private minimax absolute risk takes the infimum of maximal risk over all total private Markov
scalar releases. -/
def privateMinimaxRisk : ℝ≥0∞ :=
  ⨅ (T : Kernel (Dataset n) ℝ) -- @realizes Tgeneric(all private scalar kernels)
    (_ : IsMarkovKernel T ∧ PrivateKernel n epsilon T),
    worstRisk n T
-- @node: def:interval-criterion
-- @realizes H(honest private minimax maximal expected length)
/-- The honest private length frontier takes the infimum of maximal expected length over private
Markov interval releases with class-wide coverage at least nine tenths. -/
def privateHonestLength : ℝ≥0∞ :=
  ⨅ (I : Kernel (Dataset n) IntervalCode) -- @realizes Igeneric(private interval kernel)
    (_ : IsMarkovKernel I ∧ PrivateKernel n epsilon I ∧
      ∀ P, CompleteModel P → 9/10 ≤ coverage n I P), worstLength n I

/-- Boucheron, Lugosi and Massart (2013), Theorem 3.1, printed p.54, replacement-copy form.
Source: https://math.hse.ru/data/2016/11/24/1113029206/Concentration%20inequalities.pdf
DOI: 10.1093/acprof:oso/9780199535255.001.0001. This published claim is an assumed gate. -/
-- @node: lem:efron-stein-replacement
def EfronSteinReplacement : Sort 0 :=
  ∀ (s : ℕ) (E : Fin s → Type) (mE : ∀ i, MeasurableSpace (E i))
    (μ : ∀ i, @Measure (E i) (mE i)),
  letI : ∀ i, MeasurableSpace (E i) := mE
  ∀ (_ : ∀ i, IsProbabilityMeasure (μ i)) (Ψ : (∀ i, E i) → ℝ),
    Measurable Ψ → MemLp Ψ 2 (Measure.pi μ) →
    variance Ψ (Measure.pi μ) ≤ 1/2 * ∑ i : Fin s,
      ∫ zz, (Ψ zz.1 - Ψ (Function.update zz.1 i zz.2)) ^ 2 ∂((Measure.pi μ).prod (μ i))

/-- Boucheron, Lugosi and Massart (2013), Theorem 6.2, displayed log-mgf bound in the
proof, printed p.167. Source: https://math.hse.ru/data/2016/11/24/1113029206/Concentration%20inequalities.pdf .
DOI: 10.1093/acprof:oso/9780199535255.001.0001. Positive parameters are
exponentiated and the zero parameter is included by equality. This is an assumed gate. -/
-- @node: lem:bounded-differences-mgf
def BoundedDifferencesMGF : Sort 0 :=
  ∀ (s : ℕ) (E : Fin s → Type) (mE : ∀ i, MeasurableSpace (E i))
    (μ : ∀ i, @Measure (E i) (mE i)),
  letI : ∀ i, MeasurableSpace (E i) := mE
  ∀ (_ : ∀ i, IsProbabilityMeasure (μ i)) (Ψ : (∀ i, E i) → ℝ),
    Measurable Ψ → (∃ C : ℝ, ∀ z, |Ψ z| ≤ C) →
    ∀ c : Fin s → ℝ, (∀ i, 0 ≤ c i) →
    (∀ i z b, |Ψ z - Ψ (Function.update z i b)| ≤ c i) →
    ∀ u : ℝ, 0 ≤ u →
      (∫ z, Real.exp (u * (Ψ z - ∫ w, Ψ w ∂Measure.pi μ)) ∂Measure.pi μ) ≤
        Real.exp (u^2 / 8 * ∑ i, (c i)^2)

/-- Keller and Trotter (2017), Applied Combinatorics, Section 5.6, Theorem 5.40.
Source: https://appliedcombinatorics.org/book/s_graphs_counting-trees.html .
Nat.card counts the finite subtype of undirected labeled trees. This is an assumed gate. -/
-- @node: lem:cayley-labeled-tree-count
def CayleyLabeledTreeCount : Sort 0 :=
  ∀ s : ℕ, 2 ≤ s → Nat.card {G : SimpleGraph (Fin s) // G.IsTree} = s^(s-2)

end CausalSmith.Stat.PrivateCateRoughdesign
