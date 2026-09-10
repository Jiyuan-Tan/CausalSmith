import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FiniteSCM
import Mathlib.Data.Matrix.Mul

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! Compatible-model fibers, balancing systems, separators, and unconditional moments. -/

open scoped BigOperators
open Finset Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: def:compatible-fiber
/-- [The observed law and target proxy vector](hyp:PO,bvec) determine [their compatible-model
fiber](goal): models [satisfy the positive latent-shift conditions](step:1), [match the observed
law](step:2), and [match the target proxy distribution](step:3). -/
def compatibleFiber (PO : E → W → X → Y → ℝ) (bvec : W → ℝ) :
    Set (LatentShiftSCM E U W X Y) :=
  {Mdl | PositiveLatentShiftClass Mdl ∧ observedLaw Mdl = PO ∧ targetProxyVector Mdl = bvec}
-- @realizes \mathfrak F(\mathcal D)(models inducing supplied P_O and b)

-- @node: def:balancing-fiber
/-- [The proxy matrix, target proxy vector](hyp:Bx,bvec) determine [the set of source-environment weights whose proxy-moment image equals the target proxy vector](goal). -/
def balancingFiber (Bx : Matrix W E ℝ) (bvec : W → ℝ) : Set (E → ℝ) :=
  {lam | Bx.mulVec lam = bvec}
-- @realizes \Lambda_x(\mathcal D)(B_x lambda = b) @realizes \lambda(carrier E→ℝ)

-- @node: def:failure-separator
/-- [The proxy matrix and target proxy vector](hyp:Bx,bvec) determine [the failure-separator
set](goal): its vectors [annihilate the matrix on the left](step:1) but [have nonzero inner
product with the target vector](step:2). -/
def failureSeparator (Bx : Matrix W E ℝ) (bvec : W → ℝ) : Set (W → ℝ) :=
  {h | Bx.vecMul h = 0 ∧ dotProduct h bvec ≠ 0}
-- @realizes \mathcal H_x(\mathcal D)(left-null separators) @realizes h(carrier W→ℝ)

-- @node: def:unconditional-balancing-moments
/-- [The observed law, treatment, and outcome](hyp:PO,x,y) determine [the unconditional
balancing-moment pair](goal), consisting of [the proxy-by-environment treatment moments](step:1)
and [the environment-indexed treatment-and-outcome moments](step:2). -/
def unconditionalBalancingMoments (PO : E → W → X → Y → ℝ) (x : X) (y : Y) :
    Matrix W E ℝ × (E → ℝ) :=
  (fun w e => ∑ y', PO e w x y', fun e => ∑ w, PO e w x y)
-- @realizes H_x(unconditional proxy moments) @realizes z_{x,y}(unconditional outcome moments)

/-- [The model, treatment](hyp:Mdl,x) determine [the unconditional proxy-by-environment treatment-moment matrix](goal). -/
def proxyMomentMatrix (Mdl : LatentShiftSCM E U W X Y) (x : X) : Matrix W E ℝ :=
  fun w e => ∑ y, observedLaw Mdl e w x y
-- @realizes H_x(first projection of moment pair)

/-- [The model, treatment, outcome](hyp:Mdl,x,y) determine [the environment-indexed unconditional treatment-and-outcome moment vector](goal). -/
def outcomeMomentVector (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) : E → ℝ :=
  (unconditionalBalancingMoments (observedLaw Mdl) x y).2
-- @realizes z_{x,y}(second projection of moment pair)

/-- [The observed law, treatment](hyp:PO,x) determine [the conditional proxy-by-environment matrix obtained by normalizing the observed-law treatment cells](goal). -/
noncomputable def condProxyMatrixOfObservedLaw (PO : E → W → X → Y → ℝ) (x : X) :
    Matrix W E ℝ :=
  fun w e => (∑ y, PO e w x y) / (∑ w', ∑ y, PO e w' x y)
-- @realizes B_x(conditional proxy matrix derived from supplied P_O and x)

-- @node: def:unconditional-weight-map
/-- [The observed law, treatment, target proxy vector, balancing weights](hyp:PO,x,bvec,lam) determine [the unconditional source-environment weights obtained by rescaling conditional balancing weights by treatment probabilities](goal). -/
noncomputable def unconditionalWeightMap (PO : E → W → X → Y → ℝ) (x : X)
    (bvec : W → ℝ) (lam : balancingFiber (condProxyMatrixOfObservedLaw PO x) bvec) :
    E → ℝ :=
  fun e => lam.1 e / (∑ w, ∑ y, PO e w x y)
-- @realizes \kappa(weight from lambda in Lambda_x(P_O,b), divided by P_O(E=e,X=x))

/-- [The model, separator](hyp:Mdl,h) determine [the proxy-channel pullback of a separator to latent-state coordinates](goal). -/
def latentSeparator (Mdl : LatentShiftSCM E U W X Y) (h : W → ℝ) : U → ℝ :=
  Mdl.M.vecMul h
-- @realizes v(M^T h)

end CausalSmith.SCM.ProxyTargetspanTransport
