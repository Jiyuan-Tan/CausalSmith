import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TSharpEffectFrontier
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.TensorPencil
import Causalean.Mathlib.Probability.IidMeanVariance
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Uniform common-order confidence frontiers
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set

universe u

lemma truePair_numericalFeasible {Ω : Type*} [MeasurableSpace Ω] {p n r d q : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ)
    (u v : Vec p) (a delta sigma kappa Lambda M : ℝ)
    (hclass : SeparatedOICAClass μ C ε lam u v r d q
      a delta sigma kappa Lambda M) :
    NumericalFeasible (C, lam) u v r d q a delta sigma kappa Lambda M := by
  exact ⟨⟨hclass.d_pos, hclass.q_pos, hclass.order_eq⟩, hclass.dimension_bound,
    hclass.unitNormalized, hclass.cumulantMargin, hclass.probeMargin,
    hclass.liftedMargin, hclass.pencilGap, hclass.mixingMargin,
    hclass.loadingMargin, hclass.deletionMargin⟩

noncomputable def fittedPairFromSample {Ω : Type*} [MeasurableSpace Ω]
    {p n r d q N : ℕ} (μ : Measure Ω) (C : MixingMatrix p n)
    (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ) (u v : Vec p)
    (a delta sigma kappa Lambda M : ℝ)
    (hclass : SeparatedOICAClass μ C ε lam u v r d q
      a delta sigma kappa Lambda M) (s : Sample p N) : FactorPair p n :=
  minimumDistanceFit
    (clippedEmpiricalCumulantTensor s
      (momentClipLevel (rawMomentEnvelope n r M))) u v d q
    a delta sigma kappa Lambda M ⟨(C, lam), truePair_numericalFeasible μ C ε lam u v
      a delta sigma kappa Lambda M hclass⟩

def ConfidenceEvent {Ω : Type*} [MeasurableSpace Ω] {p n r d q N : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ)
    (u v : Vec p) (a delta sigma kappa Lambda M alpha : ℝ)
    (hN : ValidSampleSize N)
    (hclass : SeparatedOICAClass μ C ε lam u v r d q
      a delta sigma kappa Lambda M) (s : Sample p N) : Prop :=
  let Chat := (fittedPairFromSample μ C ε lam u v a delta sigma kappa Lambda M hclass s).1
  let tau := cumulantRadius p r n N hN M alpha
  let eps0 := inverseEps0 p n q sigma kappa Lambda
  let b := mixingRadius (inverseLC p n q sigma kappa Lambda) tau
  let w := effectRadius a b
  (∀ x : Fin p, responseFrontier C x ⊆
    vectorConfidenceUnion Chat x tau eps0 b a delta w) ∧
  (∀ (x y : Fin p), x ≠ y → effectFrontier C x y ⊆
    scalarConfidenceUnion Chat x y tau eps0 b a delta w) ∧
  ((2 * tau < eps0 ∧ b < min a delta / 2) →
    ∃ pi : Equiv.Perm (Fin n),
      (∀ x : Fin p, estimatedAdmissibleSources (permuteColumns Chat pi) x =
        admissibleSources C x) ∧
      (∀ x : Fin p, Metric.hausdorffDist
        (vectorConfidenceUnion Chat x tau eps0 b a delta w)
        (responseFrontier C x) ≤ 2 * vectorRadius p w) ∧
      (∀ (x y : Fin p), x ≠ y → Metric.hausdorffDist
        (scalarConfidenceUnion Chat x y tau eps0 b a delta w)
        (effectFrontier C x y) ≤ 2 * w))

def RootNConfidenceRate (p n r q : ℕ) (a sigma kappa Lambda M alpha : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ hN : 0 < N,
    let tau := cumulantRadius p r n N (Nat.succ_le_iff.mpr hN) M alpha
    let b := mixingRadius (inverseLC p n q sigma kappa Lambda) tau
    let w := effectRadius a b
    2 * w ≤ K / Real.sqrt N ∧ 2 * vectorRadius p w ≤ K / Real.sqrt N

-- @node: thm:uniform-confidence-frontier
theorem uniform_confidence_frontier {Ω : Type u} [MeasurableSpace Ω]
    {p n r d q N : ℕ} -- @realizes N(sample size)
    (μ : Measure Ω)
    (u v : Vec p) (a delta sigma kappa Lambda M alpha : ℝ)
    (hp : 2 ≤ p) (hN : ValidSampleSize N)
    (hmargins : ValidInferenceMargins alpha a delta sigma kappa Lambda M)
    (hnonempty : SeparatedClassNonempty (n := n) μ u v r d q
      a delta sigma kappa Lambda M) :
    (∀ (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ)
      (hclass : SeparatedOICAClass μ C ε lam u v r d q
        a delta sigma kappa Lambda M) (sampleLaw : Measure (Sample p N)),
      IidObservationalSample sampleLaw (observedLaw μ C ε) →
      ENNReal.ofReal (1 - alpha) ≤
        sampleLaw {s | ConfidenceEvent μ C ε lam u v a delta sigma kappa Lambda M alpha
          hN hclass s}) ∧
    (∀ (C Chat : MixingMatrix p n) (x y : Fin p) (hy : y ≠ x)
        (tau eps0 b w : ℝ),
      effectFrontier C x y = (fun rho => rho ⟨y, hy⟩) '' responseFrontier C x ∧
      scalarConfidenceUnion Chat x y tau eps0 b a delta w ⊆
        (fun rho => rho ⟨y, hy⟩) ''
          vectorConfidenceUnion Chat x tau eps0 b a delta w) ∧
    (∀ (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (lam : Fin n → ℝ)
        (hclass : SeparatedOICAClass μ C ε lam u v r d q
          a delta sigma kappa Lambda M) (x : Fin p),
      {rho | ∃ Mlaw : LawCompletion.{u} p,
        ∃ hMlaw : LawCompletionFiber (observedLaw μ C ε) x Mlaw,
          rho = observedResponse Mlaw x hMlaw} = responseFrontier C x ∧
      ∀ (y : Fin p) (hy : y ≠ x),
        {theta | ∃ Mlaw : LawCompletion.{u} p,
          ∃ hMlaw : LawCompletionFiber (observedLaw μ C ε) x Mlaw,
            theta = observedResponse Mlaw x hMlaw ⟨y, hy⟩} = effectFrontier C x y) ∧
    RootNConfidenceRate p n r q a sigma kappa Lambda M alpha := by sorry

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
