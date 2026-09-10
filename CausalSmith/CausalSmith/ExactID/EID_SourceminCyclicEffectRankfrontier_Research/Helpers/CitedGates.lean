import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.MultiOrder
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Disclosed cited gates

These declarations are explicit propositions (or, for the GVX scope record, closed metadata), not
proofs. Consumers take the relevant proposition as an `_of_gate` hypothesis.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

universe uICA vICA

/-- Goyal, Vempala, and Xiao (2014), *Fourier PCA and Robust Tensor Decomposition*,
arXiv:1306.5825v5, robust tensor-decomposition results. -/
-- @node: lem:gvx-robust-tensor-scope
def gvxRobustTensorScope : _root_.List _root_.String :=
  ["Goyal–Vempala–Xiao (2014), arXiv:1306.5825v5, is a robustness anchor for overcomplete \
tensor decomposition under quantitative nondegeneracy conditions.",
   "No uniform robustness theorem from that paper is imported into the unrestricted \
heterogeneous-order class here."]

noncomputable def rowPermuteNormalize {n : ℕ} (W : SquareMatrix n) (pi : Equiv.Perm (Fin n)) :
    SquareMatrix n :=
  fun i j => W (pi i) j / W (pi i) i

def IsSquareICAUnmixing {n : ℕ} (W : SquareMatrix n) : Prop :=
  W.det ≠ 0 ∧ ∃ (Ω : Type uICA) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (xi : Fin n → Ω → ℝ),
    IsIrreducibleICARepresentation μ W⁻¹ xi (observedLaw μ W⁻¹ xi)

def IsLiNGDNormalizedCandidate {n : ℕ} (W Q : SquareMatrix n) : Prop :=
  ∃ pi : Equiv.Perm (Fin n), (∀ i, W (pi i) i ≠ 0) ∧ Q = rowPermuteNormalize W pi

/-- Lacerda, Spirtes, Ramsey, and Hoyer (2008), Section 4, arXiv:1206.3273:
zero-free-diagonal row permutations of the ICA unmixing matrix are normalized rowwise to obtain
unit-diagonal cyclic candidate matrices. -/
-- @node: lem:lacerda-square-row-permutation
def LacerdaSquareRowPermutation : Sort 0 :=
  ∀ {n : ℕ} (W : SquareMatrix n) (pi : Equiv.Perm (Fin n)),
    IsSquareICAUnmixing.{uICA} W → (∀ i, W (pi i) i ≠ 0) →
    IsLiNGDNormalizedCandidate W (rowPermuteNormalize W pi) ∧
      Causalean.Discovery.LinearDisentanglement.Quantitative.UnitDiagonal
        (rowPermuteNormalize W pi)

/-- Lacerda, Spirtes, Ramsey, and Hoyer (2008), Theorem 1, arXiv:1206.3273:
the LiNG-D output comprises one full equivalence class under distribution entailment: output
candidates entail the same distribution, and every distribution-equivalent SEM is output. -/
noncomputable def rowPermuteAssignment {n : ℕ} (W : SquareMatrix n)
    (pi : Equiv.Perm (Fin n)) : SquareMatrix n :=
  fun i j => if pi i = j then (W (pi i) i)⁻¹ else 0

noncomputable def liNGDCandidateOutput {n : ℕ} (W : SquareMatrix n) :
    Set (SquareMatrix n × SquareMatrix n) :=
  {M | IsSquareICAUnmixing.{uICA} W ∧
    ∃ pi : Equiv.Perm (Fin n), (∀ i, W (pi i) i ≠ 0) ∧
    M = (rowPermuteNormalize W pi, rowPermuteAssignment W pi)}

/-- The normalized square linear non-Gaussian SEM domain used by LiNG-D.  This excludes arbitrary
matrix pairs from the exhaustiveness direction of the equivalence-class statement. -/
def NormalizedAdmissibleLiNGSEM {n : ℕ}
    (M : SquareMatrix n × SquareMatrix n) : Prop :=
  UnitStructuralDiagonal M.1 ∧ MonomialSourceAssignment M.2 ∧
    ObservationalSolvability M.1

/-- All observational laws entailed by a normalized SEM as its independent, nondegenerate,
non-Gaussian disturbance law varies.  Distribution entailment is a model-level notion, not equality
under one fixed choice of disturbance variables. -/
def SEMEntailedDistributions {n : ℕ} (M : SquareMatrix n × SquareMatrix n) :
    Set (Measure (Vec n)) :=
  {P | ∃ ν : Measure (Vec n),
    let xi : Fin n → Vec n → ℝ := fun j z => z j
    QualitativelyNondegenerateSources ν xi ∧ ProbabilityTheory.iIndepFun xi ν ∧
      NonGaussianSources ν xi ∧ P = observedLaw ν (M.1⁻¹ * M.2) xi}

/-- Two square SEMs are distribution-entailment equivalent when they entail exactly the same class
of observational laws. -/
def DistributionEntailmentEquivalent {n : ℕ}
    (M₁ M₂ : SquareMatrix n × SquareMatrix n) : Prop :=
  SEMEntailedDistributions M₁ = SEMEntailedDistributions M₂

-- @node: lem:lacerda-distribution-entailment-equivalence
def LacerdaDistributionEntailmentEquivalence : Sort 0 :=
  ∀ {n : ℕ} (W : SquareMatrix n), IsSquareICAUnmixing.{uICA} W →
    ∃ M₀ ∈ liNGDCandidateOutput.{uICA} W,
      liNGDCandidateOutput.{uICA} W =
        {M | NormalizedAdmissibleLiNGSEM M ∧ DistributionEntailmentEquivalent M M₀}

def kruskalRankAtLeast {R d : ℕ} (A : Fin R → Vec d) (k : ℕ) : Prop :=
  k ≤ R ∧ ∀ S : Finset (Fin R), S.card ≤ k →
    LinearIndependent ℝ (fun i : {i // i ∈ S} => A i.1)

def threeFactorTensor {R d₁ d₂ d₃ : ℕ} (gamma : Fin R → ℝ)
    (A : Fin R → Vec d₁) (B : Fin R → Vec d₂) (C : Fin R → Vec d₃) :
    Fin d₁ → Fin d₂ → Fin d₃ → ℝ :=
  fun i j k => ∑ h, gamma h * A h i * B h j * C h k

def EssentiallyEquivalent3 {R d₁ d₂ d₃ : ℕ}
    (gamma gamma' : Fin R → ℝ)
    (A A' : Fin R → Vec d₁) (B B' : Fin R → Vec d₂) (C C' : Fin R → Vec d₃) : Prop :=
  ∃ pi : Equiv.Perm (Fin R), ∃ sa sb sc : Fin R → ℝ,
    (∀ h, sa h ≠ 0 ∧ sb h ≠ 0 ∧ sc h ≠ 0 ∧
      gamma' h * sa h * sb h * sc h = gamma (pi h)) ∧
    (∀ h, A' h = sa h • A (pi h)) ∧
    (∀ h, B' h = sb h • B (pi h)) ∧
    (∀ h, C' h = sc h • C (pi h))

/-- Kruskal (1977), Theorem 4a, DOI 10.1016/0024-3795(77)90069-6:
the three-factor Kruskal-rank inequality forces rank `R` and essential uniqueness. -/
-- @node: lem:kruskal-three-factor-uniqueness
def KruskalThreeFactorUniqueness : Sort 0 :=
  ∀ {R d₁ d₂ d₃ : ℕ} (k₁ k₂ k₃ : ℕ) (gamma : Fin R → ℝ)
      (A : Fin R → Vec d₁) (B : Fin R → Vec d₂) (C : Fin R → Vec d₃),
    (∀ h, gamma h ≠ 0 ∧ A h ≠ 0 ∧ B h ≠ 0 ∧ C h ≠ 0) →
    kruskalRankAtLeast A k₁ → kruskalRankAtLeast B k₂ → kruskalRankAtLeast C k₃ →
    2 * R + 2 ≤ k₁ + k₂ + k₃ →
    (¬ ∃ S : ℕ, S < R ∧ ∃ (gamma' : Fin S → ℝ) (A' : Fin S → Vec d₁)
      (B' : Fin S → Vec d₂)
      (C' : Fin S → Vec d₃),
      threeFactorTensor gamma A B C = threeFactorTensor gamma' A' B' C') ∧
    ∀ gamma' A' B' C',
      threeFactorTensor gamma A B C = threeFactorTensor gamma' A' B' C' →
      EssentiallyEquivalent3 gamma gamma' A A' B B' C C'

/-- Marcinkiewicz (1939), *Sur une propriété de la loi de Gauss*,
DOI 10.1007/BF01210677: a nondegenerate all-moments law with only finitely many nonzero cumulants
is Gaussian. This is the moment-sequence formulation, not the exponential-polynomial corollary. -/
-- @node: lem:marcinkiewicz-cumulant-tail
def MarcinkiewiczCumulantTail : Sort 0 :=
  ∀ {Ω : Type*} (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : Ω → ℝ),
    IsProbabilityMeasure μ → AEMeasurable X μ →
    0 < ProbabilityTheory.variance X μ →
    (∀ k, 1 ≤ k → Integrable (fun ω => |X ω| ^ k) μ) →
    (∃ K, ∀ r, K < r → Causalean.Stat.MomentProblems.sourceCumulant μ X r = 0) →
    Causalean.Stat.MomentProblems.IsGaussianLaw (μ.map X)

noncomputable def rawMoment (ν : Measure ℝ) (k : ℕ) : ℝ := ∫ x, x ^ k ∂ν

def HasAllFiniteMoments (ν : Measure ℝ) : Prop :=
  ∀ k, Integrable (fun x : ℝ => |x| ^ k) ν

def MomentDeterminate (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ HasAllFiniteMoments ν ∧
    ∀ ξ : Measure ℝ, IsProbabilityMeasure ξ → HasAllFiniteMoments ξ →
      (∀ k, rawMoment ξ k = rawMoment ν k) → ξ = ν

/-- Shohat and Tamarkin (1943), *The Problem of Moments*, Chapter I: Carleman's
criterion for the Hamburger moment problem. -/
-- @node: lem:carleman-moment-determinacy
def CarlemanMomentDeterminacy : Sort 0 :=
  ∀ ν : Measure ℝ,
    IsProbabilityMeasure ν → HasAllFiniteMoments ν →
    (∑' s : ℕ, (ENNReal.ofReal |rawMoment ν (2 * (s + 1))|).rpow
      (-(1 : ℝ) / (2 * (s + 1)))) = ⊤ →
    MomentDeterminate ν

/-- Dai, Albrecht, Spirtes, and Zhang (2026), Appendix B.1, Lemma 11,
arXiv:2603.04780v1 (upstream Eriksson–Koivunen 2004, Theorem 3): irreducible ICA
representations of one law match in source count and projective columns. -/
def IsQualitativeIrreducibleICARepresentation {p m : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) (A : MixingMatrix p m) (xi : Fin m → Ξ → ℝ)
    (P : Measure (Vec p)) : Prop :=
  IsProbabilityMeasure ν ∧ (∀ j, AEMeasurable (xi j) ν) ∧
    NonzeroColumns A ∧ DistinctDirections A ∧ ProbabilityTheory.iIndepFun xi ν ∧
    QualitativelyNondegenerateSources ν xi ∧ observedLaw ν A xi = P

-- @node: lem:dai-irreducible-oica-uniqueness
def DaiIrreducibleOICAUniqueness : Sort 0 :=
  ∀ {p n m : ℕ} {Ω : Type uICA} {Ξ : Type vICA}
      (_ : MeasurableSpace Ω) (_ : MeasurableSpace Ξ)
      (μ : Measure Ω) (ν : Measure Ξ) (C : MixingMatrix p n) (A : MixingMatrix p m)
      (ε : Fin n → Ω → ℝ) (xi : Fin m → Ξ → ℝ),
    IsQualitativeIrreducibleICARepresentation μ C ε (observedLaw μ C ε) →
    NonGaussianSources μ ε →
    NonzeroColumns A → DistinctDirections A → ProbabilityTheory.iIndepFun xi ν →
    QualitativelyNondegenerateSources ν xi →
    observedLaw ν A xi = observedLaw μ C ε →
    n = m ∧
      {D | ∃ j, D = projectiveClass (C.col j)} =
        {D | ∃ j, D = projectiveClass (A.col j)} ∧
      NonGaussianSources ν xi

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
