import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.unusedDecidableInType false

/-!
A finite, matrix-parametrized latent-shift SCM and its observable and target summaries.
This deliberately stays at the finite-algebraic level; the sampling file supplies the later
conversion to probability measures.
-/

open scoped BigOperators
open Finset Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @env: S1
variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
-- @realizes \mathcal E(finite carrier) @realizes E(values in environment carrier)
-- @realizes \mathcal U(finite carrier) @realizes U(values in latent carrier)
-- @realizes \mathcal W(finite carrier) @realizes W(values in proxy carrier)
-- @realizes \mathcal X(finite carrier) @realizes X(values in treatment carrier)
-- @realizes \mathcal Y(finite carrier) @realizes Y(values in outcome carrier)
-- @realizes e(element of E) @realizes u(element of U) @realizes w(element of W)
-- @realizes x(element of X) @realizes y(element of Y) @realizes y^{\circ}(element of Y)
-- @realizes r(cardinality of U) @realizes m(cardinality of W)
-- @realizes \mathcal G(fixed factorization graph encoded by the mechanism fields)

/-- A normalized finite latent-shift SCM. The full source and target laws remain explicit fields,
so their two factorization assumptions are substantive rather than definitional equalities. -/
structure LatentShiftSCM (E U W X Y : Type*)
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y] where
  environment_nonempty : Nonempty E -- @realizes \mathcal E(nonempty finite carrier)
  treatment_nonempty : Nonempty X -- @realizes \mathcal X(nonempty finite carrier)
  latent_card : 2 ≤ Fintype.card U -- @realizes \mathcal U(cardinality at least two)
    -- @realizes r(card U at least two)
  proxy_card : Fintype.card U ≤ Fintype.card W -- @realizes m(card W at least r)
  outcome_card : 2 ≤ Fintype.card Y -- @realizes \mathcal Y(at least two outcomes)
  pi : E → ℝ -- @realizes \pi(carrier E→ℝ)
  S : Matrix U E ℝ -- @realizes S(carrier U×E→ℝ)
  M : Matrix W U ℝ -- @realizes M(carrier W×U→ℝ)
  a : X → U → ℝ -- @realizes a(treatment kernel carrier)
  f : X → Y → U → W → ℝ -- @realizes f(outcome kernel carrier)
  q : U → ℝ -- @realizes q(carrier U→ℝ)
  PM : E → U → W → X → Y → ℝ -- @realizes P_{\mathcal M}(source full-law carrier)
  QM : U → W → X → Y → ℝ -- @realizes Q_{\mathcal M}(target full-law carrier)
  pi_nonneg : ∀ e, 0 ≤ pi e -- @realizes \pi(nonnegative)
  pi_sum : ∑ e, pi e = 1 -- @realizes \pi(unit mass)
  S_nonneg : ∀ u e, 0 ≤ S u e -- @realizes S(nonnegative)
  S_col : ∀ e, ∑ u, S u e = 1 -- @realizes S(column stochastic)
  M_nonneg : ∀ w u, 0 ≤ M w u -- @realizes M(nonnegative)
  M_col : ∀ u, ∑ w, M w u = 1 -- @realizes M(column stochastic)
  a_nonneg : ∀ x u, 0 ≤ a x u -- @realizes a(nonnegative)
  a_col : ∀ u, ∑ x, a x u = 1 -- @realizes a(stochastic kernel)
  f_nonneg : ∀ x y u w, 0 ≤ f x y u w -- @realizes f(nonnegative)
  f_col : ∀ x u w, ∑ y, f x y u w = 1 -- @realizes f(stochastic kernel)
  q_nonneg : ∀ u, 0 ≤ q u -- @realizes q(nonnegative)
  q_sum : ∑ u, q u = 1 -- @realizes q(unit mass)
  PM_nonneg : ∀ e u w x y, 0 ≤ PM e u w x y -- @realizes P_{\mathcal M}(nonnegative)
  PM_sum : ∑ e, ∑ u, ∑ w, ∑ x, ∑ y, PM e u w x y = 1 -- @realizes P_{\mathcal M}(unit mass)
  QM_nonneg : ∀ u w x y, 0 ≤ QM u w x y -- @realizes Q_{\mathcal M}(nonnegative)
  QM_sum : ∑ u, ∑ w, ∑ x, ∑ y, QM u w x y = 1 -- @realizes Q_{\mathcal M}(unit mass)

-- @realizes \mathcal M(finite latent-shift SCM carrier)

-- @node: ass:latent-shift-factorization
/-- [The model](hyp:Mdl) establish [the source joint law factors into the environment, latent-state, proxy, treatment, and outcome mechanisms](goal). -/
def LatentShiftFactorization (Mdl : LatentShiftSCM E U W X Y) : Prop :=
  ∀ e u w x y,
    Mdl.PM e u w x y = Mdl.pi e * Mdl.S u e * Mdl.M w u * Mdl.a x u * Mdl.f x y u w

-- @node: ass:target-mechanism-invariance
/-- [The model](hyp:Mdl) establish [the target full law uses the source proxy, treatment, and outcome mechanisms while changing only the latent distribution](goal). -/
def TargetMechanismInvariance (Mdl : LatentShiftSCM E U W X Y) : Prop :=
  ∀ u w x y, Mdl.QM u w x y = Mdl.q u * Mdl.M w u * Mdl.a x u * Mdl.f x y u w

-- @node: ass:strict-primitive-positivity
/-- [The model](hyp:Mdl) establish [all environment, latent, proxy, treatment, outcome, and target primitive probabilities are strictly positive](goal). -/
def StrictPrimitivePositivity (Mdl : LatentShiftSCM E U W X Y) : Prop :=
  (∀ e, 0 < Mdl.pi e) ∧ -- @realizes \pi(strictly positive)
  (∀ u e, 0 < Mdl.S u e) ∧ -- @realizes S(strictly positive)
  (∀ w u, 0 < Mdl.M w u) ∧ -- @realizes M(strictly positive)
  (∀ x u, 0 < Mdl.a x u) ∧ -- @realizes a(strictly positive)
  (∀ x y u w, 0 < Mdl.f x y u w) ∧ -- @realizes f(strictly positive)
  (∀ u, 0 < Mdl.q u) -- @realizes q(strictly positive)

-- @node: ass:proxy-channel-injectivity
/-- [The model](hyp:Mdl) establish [the proxy channel has column rank equal to the number of latent states](goal). -/
def ProxyChannelInjectivity (Mdl : LatentShiftSCM E U W X Y) : Prop :=
  Mdl.M.rank = Fintype.card U

-- @node: def:positive-latent-shift-class
/-- [The model](hyp:Mdl) belongs to [the positive latent-shift class](goal) when it satisfies
[source-law factorization](hyp:factorization), [target-mechanism invariance](hyp:target_invariance),
[strict primitive positivity](hyp:positivity), and [proxy-channel injectivity](hyp:proxy_injective). -/
structure PositiveLatentShiftClass (Mdl : LatentShiftSCM E U W X Y) : Prop where
  factorization : LatentShiftFactorization Mdl
  target_invariance : TargetMechanismInvariance Mdl
  positivity : StrictPrimitivePositivity Mdl
  proxy_injective : ProxyChannelInjectivity Mdl

/-- The observed source law after marginalizing the latent state. -/
def observedLaw (Mdl : LatentShiftSCM E U W X Y) : E → W → X → Y → ℝ :=
  fun e w x y => ∑ u, Mdl.PM e u w x y
-- @realizes P_O(sum_u P_M)

/-- The target proxy marginal, equivalently `M q` under the target factorization. -/
def targetProxyVector (Mdl : LatentShiftSCM E U W X Y) : W → ℝ :=
  fun w => ∑ u, Mdl.M w u * Mdl.q u
-- @realizes b(sum_u M_wu q_u)

/-- [The model, treatment](hyp:Mdl,x) establish [the source treatment probability in each environment](goal). -/
def sourceTreatmentProb (Mdl : LatentShiftSCM E U W X Y) (x : X) : E → ℝ :=
  fun e => ∑ u, Mdl.a x u * Mdl.S u e
-- @realizes \rho_x(sum_u a_x S)

/-- [The model, treatment](hyp:Mdl,x) establish [the latent-state posterior matrix given treatment and source environment](goal). -/
noncomputable def latentPosterior (Mdl : LatentShiftSCM E U W X Y) (x : X) : Matrix U E ℝ :=
  fun u e => Mdl.a x u * Mdl.S u e / sourceTreatmentProb Mdl x e
-- @realizes R_x(a_x S / rho_x)

/-- [The model, treatment](hyp:Mdl,x) establish [the conditional proxy-by-environment matrix](goal). -/
noncomputable def condProxyMatrix (Mdl : LatentShiftSCM E U W X Y) (x : X) : Matrix W E ℝ :=
  fun w e => (∑ y, observedLaw Mdl e w x y) / (∑ w', ∑ y, observedLaw Mdl e w' x y)
-- @realizes B_x(proxy conditional matrix)

/-- [The model, treatment, outcome](hyp:Mdl,x,y) establish [the latent-state response probability after averaging the outcome mechanism over proxies](goal). -/
def latentResponse (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) : U → ℝ :=
  fun u => ∑ w, Mdl.M w u * Mdl.f x y u w
-- @realizes g_{x,y}(sum_w M_wu f_xyuw)

/-- [The model, treatment, outcome](hyp:Mdl,x,y) establish [the conditional outcome-probability vector over source environments](goal). -/
noncomputable def condOutcomeVector (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) : E → ℝ :=
  fun e => (∑ w, observedLaw Mdl e w x y) / (∑ w, ∑ y', observedLaw Mdl e w x y')
-- @realizes c_{x,y}(conditional outcome vector)

/-- The graph-truncated target functional: the treatment mechanism is deleted at fixed `x`. -/
def interventionalProb (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) : ℝ :=
  ∑ u, ∑ w, Mdl.q u * Mdl.M w u * Mdl.f x y u w
-- @realizes \theta_{x,y}(target do functional)

/-- [every cell of the model-induced observed source law is nonnegative](goal). -/
lemma observedLaw_nonneg (Mdl : LatentShiftSCM E U W X Y) (e w x y) :
    0 ≤ observedLaw Mdl e w x y := by
  unfold observedLaw
  exact Finset.sum_nonneg fun u _ => Mdl.PM_nonneg e u w x y

/-- [the model-induced observed source law has total mass one](goal). -/
lemma observedLaw_sum (Mdl : LatentShiftSCM E U W X Y) :
    ∑ e, ∑ w, ∑ x, ∑ y, observedLaw Mdl e w x y = 1 := by
  unfold observedLaw
  rw [← Mdl.PM_sum]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ w, ∑ x, ∑ y, ∑ u, Mdl.PM e u w x y) =
        ∑ w, ∑ x, ∑ u, ∑ y, Mdl.PM e u w x y := by
          apply Finset.sum_congr rfl
          intro w _
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ w, ∑ u, ∑ x, ∑ y, Mdl.PM e u w x y := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.sum_comm]
    _ = ∑ u, ∑ w, ∑ x, ∑ y, Mdl.PM e u w x y := Finset.sum_comm

/-- [every coordinate of the model's target proxy distribution is nonnegative](goal). -/
lemma targetProxyVector_nonneg (Mdl : LatentShiftSCM E U W X Y) (w) :
    0 ≤ targetProxyVector Mdl w := by
  unfold targetProxyVector
  exact Finset.sum_nonneg fun u _ => mul_nonneg (Mdl.M_nonneg w u) (Mdl.q_nonneg u)

/-- [the model's target proxy distribution has total mass one](goal). -/
lemma targetProxyVector_sum (Mdl : LatentShiftSCM E U W X Y) :
    ∑ w, targetProxyVector Mdl w = 1 := by
  unfold targetProxyVector
  calc
    (∑ w, ∑ u, Mdl.M w u * Mdl.q u) = ∑ u, ∑ w, Mdl.M w u * Mdl.q u :=
      Finset.sum_comm
    _ = ∑ u, Mdl.q u * ∑ w, Mdl.M w u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 1 := by simp [Mdl.M_col, Mdl.q_sum]

end CausalSmith.SCM.ProxyTargetspanTransport
