import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Separated
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.Partition.Finpartition
import Mathlib.Topology.Order.Compact

/-!
# Sampling, minimum-distance fit, and confidence unions
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set
open scoped BigOperators

abbrev Sample (p N : ℕ) := Fin N → Vec p

-- @env: S4
variable {Ω : Type*} [MeasurableSpace Ω] {p n r d q N : ℕ}
  (P : Measure (Vec p)) (sampleLaw : Measure (Sample p N))

-- @node: ass:iid-sampling
def IidObservationalSample (sampleLaw : Measure (Sample p N)) (P : Measure (Vec p)) : Prop :=
  sampleLaw = Measure.pi (fun _ : Fin N => P)
  -- @realizes Xsample(sample law is PX tensor-power N)

noncomputable def rawEmpiricalMoment (Xsample : Sample p N) (I : Fin r → Fin p)
    (B : Finset (Fin r)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ s, ∏ k ∈ B, Xsample s (I k)

def clip (B z : ℝ) : ℝ := max (-B) (min B z)

noncomputable def momentToCumulantPoly (Xsample : Sample p N) (Bmom : ℝ)
    (I : Fin r → Fin p) : ℝ :=
  ∑ pi : Finpartition (Finset.univ : Finset (Fin r)),
    (-1 : ℝ) ^ (pi.parts.card - 1) * (Nat.factorial (pi.parts.card - 1) : ℝ) *
      ∏ B ∈ pi.parts, clip Bmom (rawEmpiricalMoment Xsample I B)

-- @node: def:empirical-cumulant
noncomputable def clippedEmpiricalCumulantTensor (Xsample : Sample p N) (Bmom : ℝ) :
    (Fin r → Fin p) → ℝ :=
  momentToCumulantPoly Xsample Bmom
  -- @realizes That(clipped empirical cumulant tensor)

abbrev FactorPair (p n : ℕ) := MixingMatrix p n × (Fin n → ℝ)

noncomputable def tensorFrobeniusNorm {p r : ℕ} (T : (Fin r → Fin p) → ℝ) : ℝ :=
  Real.sqrt (∑ I, (T I) ^ 2)

noncomputable def tensorFitObjective (That : (Fin r → Fin p) → ℝ)
    (z : FactorPair p n) : ℝ :=
  tensorFrobeniusNorm fun I => That I - cumulantTensor z.1 z.2 I

/-- The numerical feasible restrictions used by the separated fit; no source law is attached to
the fitted pair. -/
def NumericalFeasible (z : FactorPair p n) (u v : Vec p) (r d q : ℕ)
    (a delta sigma kappa Lambda M : ℝ) : Prop :=
  ValidTensorOrders d q r ∧ n ≤ Nat.choose (p + d - 1) d ∧
  UnitNormalizedColumns z.1 ∧ CumulantMagnitudeMargin z.2 kappa Lambda ∧
  ProbeOrientationMargin z.1 u sigma ∧ LiftedRankMargin z.1 d sigma ∧
  PencilGap z.1 u v sigma ∧ MixingSingularMargin z.1 delta ∧
  LoadingSelectionMargin z.1 a ∧ DeletionRankMargin z.1 delta

noncomputable def factorPairCoordinates (z : FactorPair p n) : List ℝ :=
  ((Finset.univ : Finset (Fin p)).toList.flatMap fun i =>
    (Finset.univ : Finset (Fin n)).toList.map fun j => z.1 i j) ++
  (Finset.univ : Finset (Fin n)).toList.map z.2

noncomputable def LexLE (z w : FactorPair p n) : Prop :=
  factorPairCoordinates z = factorPairCoordinates w ∨
    List.Lex (· < ·) (factorPairCoordinates z) (factorPairCoordinates w)

def IsLexicographicMinimum (That : (Fin r → Fin p) → ℝ) (u v : Vec p)
    (d q : ℕ) (a delta sigma kappa Lambda M : ℝ) (z : FactorPair p n) : Prop :=
  NumericalFeasible z u v r d q a delta sigma kappa Lambda M ∧
  (∀ w : FactorPair p n, NumericalFeasible w u v r d q a delta sigma kappa Lambda M →
    tensorFitObjective That z ≤ tensorFitObjective That w) ∧
  (∀ w : FactorPair p n, NumericalFeasible w u v r d q a delta sigma kappa Lambda M →
    tensorFitObjective That w = tensorFitObjective That z → LexLE z w)

lemma existsUnique_lexicographicMinimum
    (That : (Fin r → Fin p) → ℝ) (u v : Vec p) (d q : ℕ)
    (a delta sigma kappa Lambda M : ℝ)
    (hne : ∃ z : FactorPair p n,
      NumericalFeasible z u v r d q a delta sigma kappa Lambda M) :
    ∃! z : FactorPair p n,
      IsLexicographicMinimum That u v d q a delta sigma kappa Lambda M z := by sorry

-- @node: def:minimum-distance-fit
noncomputable def minimumDistanceFit
    (That : (Fin r → Fin p) → ℝ) (u v : Vec p) (d q : ℕ)
    (a delta sigma kappa Lambda M : ℝ)
    (hne : ∃ z : FactorPair p n,
      NumericalFeasible z u v r d q a delta sigma kappa Lambda M) : FactorPair p n :=
  Classical.choose
    (existsUnique_lexicographicMinimum That u v d q a delta sigma kappa Lambda M hne)
  -- @realizes Chat(mixing component of lexicographically selected minimum-distance fit)

-- @node: def:estimated-index-set
noncomputable def estimatedAdmissibleSources (Chat : MixingMatrix p n) (x : Fin p) :
    Finset (Fin n) := admissibleSources Chat x
  -- @realizes Jhat(Jhat = Jx(Chat))

/-- Derived dimensions, envelopes, and radii used by both confidence sets. -/
def momentDimension (p r : ℕ) : ℕ := Nat.choose (p + r) r - 1
  -- @realizes momentdim(m = choose(p+r,r)-1)

noncomputable def rawMomentEnvelope (n r : ℕ) (M : ℝ) : ℝ := n ^ (2 * r) * max 1 M
  -- @realizes Hbound(H = n^(2r) max(1,M))

def momentClipLevel (H : ℝ) : ℝ := 1 + H
  -- @realizes Bmom(Bmom = 1 + Hbound)

def ValidSampleSize (N : ℕ) : Prop := 1 ≤ N
  -- @realizes N(sample size is positive where eN is defined)

noncomputable def rawMomentRadius (p r n N : ℕ) (_hN : ValidSampleSize N)
    (M alpha : ℝ) : ℝ :=
  Real.sqrt (momentDimension p r * (1 + rawMomentEnvelope n r M) / (N * alpha))
  -- @realizes eN(eN = sqrt(momentdim(1+Hbound)/(N alpha)))

noncomputable def momentCumulantLipschitz (p r : ℕ) (Bmom : ℝ) : ℝ :=
  p ^ ((r : ℝ) / 2) *
    ∑ pi : Finpartition (Finset.univ : Finset (Fin r)),
      (Nat.factorial (pi.parts.card - 1) : ℝ) * pi.parts.card * Bmom ^ (pi.parts.card - 1)
  -- @realizes Lmom(moment-to-cumulant Lipschitz coefficient)

noncomputable def cumulantRadius (p r n N : ℕ) (hN : ValidSampleSize N)
    (M alpha : ℝ) : ℝ :=
  momentCumulantLipschitz p r (momentClipLevel (rawMomentEnvelope n r M)) *
    rawMomentRadius p r n N hN M alpha
  -- @realizes tauN(tauN = Lmom eN)

def mixingRadius (LC tauN : ℝ) : ℝ := 2 * LC * tauN
  -- @realizes bN(bN = 2 LC tauN)

noncomputable def effectRadius (a bN : ℝ) : ℝ := (a⁻¹ + a⁻¹ ^ 2) * bN
  -- @realizes wN(wN = (a^-1+a^-2)bN)

noncomputable def vectorRadius (p : ℕ) (wN : ℝ) : ℝ := Real.sqrt (p - 1) * wN
  -- @realizes wvecN(wvecN = sqrt(p-1) wN)

-- @node: def:confidence-union
noncomputable def scalarConfidenceUnion (Chat : MixingMatrix p n) (x y : Fin p)
    (tauN eps0 bN a delta wN : ℝ) : Set ℝ :=
  if 2 * tauN < eps0 ∧ bN < min a delta / 2 then
    {z | ∃ j ∈ estimatedAdmissibleSources Chat x,
      z ∈ Set.Icc (Chat y j / Chat x j - wN) (Chat y j / Chat x j + wN)}
  else Set.Icc (-a⁻¹) a⁻¹
  -- @realizes Uxy(two-branch simultaneous scalar confidence union)

def l2ClosedBall {ι : Type*} [Fintype ι] (z : ι → ℝ) (rad : ℝ) : Set (ι → ℝ) :=
  {w | Real.sqrt (∑ i, (w i - z i) ^ 2) ≤ rad}

-- @node: def:vector-confidence-union
noncomputable def vectorConfidenceUnion (Chat : MixingMatrix p n) (x : Fin p)
    (tauN eps0 bN a delta wN : ℝ) : Set ({i : Fin p // i ≠ x} → ℝ) :=
  if 2 * tauN < eps0 ∧ bN < min a delta / 2 then
    {z | ∃ j ∈ estimatedAdmissibleSources Chat x,
      z ∈ l2ClosedBall (fun i => Chat i.1 j / Chat x j) (vectorRadius p wN)}
  else l2ClosedBall 0 (Real.sqrt (p - 1) / a)
  -- @realizes Uvec(union of vector balls indexed by one common source j)

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
