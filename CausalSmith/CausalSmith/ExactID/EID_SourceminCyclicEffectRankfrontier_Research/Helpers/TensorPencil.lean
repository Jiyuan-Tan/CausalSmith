import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Sampling
import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Main
import Causalean.Mathlib.Analysis.SingularValueWeyl
import Causalean.Mathlib.Analysis.RectangularSignalSingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Numerical common-order tensor-pencil inverse
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open scoped BigOperators

noncomputable def matrixFrobeniusNorm {p n : ℕ} (C : MixingMatrix p n) : ℝ :=
  Causalean.Mathlib.Analysis.SymmetricTensorPencil.matrixFrobeniusNorm C

def permuteColumns {p n : ℕ} (C : MixingMatrix p n) (pi : Equiv.Perm (Fin n)) :
    MixingMatrix p n :=
  Causalean.Mathlib.Analysis.SymmetricTensorPencil.permuteColumns C pi

noncomputable def inverseEta (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).1

noncomputable def inverseChi (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).2.1

noncomputable def inverseH (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).2.2.1

noncomputable def inverseEps0 (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).2.2.2.1

noncomputable def inverseLz (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).2.2.2.2.1

noncomputable def inverseLC (p n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  (inverseConstants p n q sigma kappa Lambda).2.2.2.2.2

-- @node: lem:numerical-common-order-local-inverse
lemma numerical_common_order_local_inverse {p n r d q : ℕ}
    (C C' : MixingMatrix p n) (lam lam' : Fin n → ℝ) (u v : Vec p)
    (sigma kappa Lambda : ℝ)
    (hp : 2 ≤ p) (hpn : p ≤ n)
    (hsigma : 0 < sigma ∧ sigma ≤ 1) (hkappa : 0 < kappa)
    (hkappaLambda : kappa ≤ Lambda)
    (hu : euclideanNorm u = 1) (hv : euclideanNorm v = 1)
    (horders : ValidTensorOrders d q r)
    (hdim : n ≤ Nat.choose (p + d - 1) d)
    (hnorm : UnitNormalizedColumns C ∧ UnitNormalizedColumns C')
    (hlam : CumulantMagnitudeMargin lam kappa Lambda ∧
      CumulantMagnitudeMargin lam' kappa Lambda)
    (hprobe : ProbeOrientationMargin C u sigma ∧ ProbeOrientationMargin C' u sigma)
    (hlift : LiftedRankMargin C d sigma ∧ LiftedRankMargin C' d sigma)
    (hgap : PencilGap C u v sigma ∧ PencilGap C' u v sigma)
    (hclose : tensorFrobeniusNorm
      (fun I : Fin r → Fin p => cumulantTensor C' lam' I - cumulantTensor C lam I) <
      inverseEps0 p n q sigma kappa Lambda) :
    ∃ pi : Equiv.Perm (Fin n),
      matrixFrobeniusNorm (permuteColumns C' pi - C) ≤
        inverseLC p n q sigma kappa Lambda *
          tensorFrobeniusNorm
            (fun I : Fin r → Fin p =>
              cumulantTensor C' lam' I - cumulantTensor C lam I) := by
  rcases horders with ⟨hd, hq, hr⟩
  have hp' : 0 < p := by omega
  have hn : 0 < n := lt_of_lt_of_le hp' hpn
  subst r
  rw [show 2 * d + q = d + d + q by omega] at hclose ⊢
  have hclose' :
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm
        (Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor
            (d + d + q) C' lam' -
          Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor
            (d + d + q) C lam) <
        Causalean.Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius
          n q sigma kappa Lambda := by
    simpa [tensorFrobeniusNorm, cumulantTensor, inverseEps0, inverseConstants,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.rankOneTensor,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractedMargin,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedConditionEnvelope,
      Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilPerturbationConstant,
      Pi.sub_apply] using hclose
  simpa [euclideanNorm, finiteEuclideanNorm, UnitNormalizedColumns,
    CumulantMagnitudeMargin, ProbeOrientationMargin, LiftedRankMargin,
    euclideanLeastColumnSingularValue, PencilGap, dot, liftedDirections,
    tensorFrobeniusNorm, cumulantTensor, matrixFrobeniusNorm, permuteColumns,
    inverseEps0, inverseLC, inverseConstants,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.finiteFrobeniusNorm,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.decompositionTensor,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.rankOneTensor,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.localInverseRadius,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.factorRecoveryConstant,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.traceRecoveryConstant,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.contractedMargin,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.liftedConditionEnvelope,
    Causalean.Mathlib.Analysis.SymmetricTensorPencil.pencilPerturbationConstant,
    Nat.mul_comm] using
      (Causalean.Mathlib.Analysis.SymmetricTensorPencil.exists_permutation_factorMatrix_frobeniusNorm_le
          C C' lam lam' u v sigma kappa Lambda hp' hn hd hq hsigma hkappa
          hkappaLambda hu hv hnorm hlam hprobe hlift hgap hclose')

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
