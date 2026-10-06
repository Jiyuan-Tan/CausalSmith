module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PriorHandle

/-!
The shrinking-cone dual as a normalized atomic signed-moment certificate.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory
open scoped BigOperators ENNReal
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- Retain the nodes, weights, and matching moments of the paper's dual witness. -/
-- @node: ConeDual.toNormalizedCertificate
def ConeDual.toNormalizedCertificate {L : Nat} {B eps : Real} (sigma : ConeDual L B eps) :
    NormalizedFiniteSignedMomentCertificate (Fin (L + 2)) L where
  node := sigma.nodes
  weight := sigma.weights
  node_injective := sigma.strictMono.injective
  normalized := sigma.abs_sum
  moments_zero := sigma.moments

/-- [Under the stated inputs and conditions](hyp:L,sigma,B,eps), The certificate variation is supported on the original shrinking cone.  This gives [the stated result](goal).-/
-- @node: ConeDual.toNormalizedCertificate_support
lemma ConeDual.toNormalizedCertificate_support {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) :
    ∀ᵐ v ∂sigma.toNormalizedCertificate.signedMeasure.variation, v ∈ Set.Icc 0 B := by
  rw [NormalizedFiniteSignedMomentCertificate.variation_eq_absoluteMeasure,
    NormalizedFiniteSignedMomentCertificate.absoluteMeasure, ae_finsetSum_measure_iff]
  intro i hi
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff measurableSet_Icc).2 (sigma.mem i)

end CausalSmith.Stat.AnnotationRarearmFrontier
