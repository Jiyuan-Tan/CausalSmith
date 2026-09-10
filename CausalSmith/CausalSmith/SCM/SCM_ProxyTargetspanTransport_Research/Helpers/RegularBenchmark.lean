import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Fibers
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TruncatedSVD
import Causalean.Mathlib.Probability.StdNormalCDF
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The fixed-rank regular submodel, delta-method variance, and Wald benchmark. -/

open scoped BigOperators
open Finset Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @env: S4
variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

/-- [The observed law](hyp:PO) establish [the flattened vector of full observed-law cell probabilities](goal). -/
def sourceCellVector (PO : E → W → X → Y → ℝ) : (E × W × X × Y) → ℝ :=
  fun o => PO o.1 o.2.1 o.2.2.1 o.2.2.2

/-- [The probability vector](hyp:v) establish [the covariance matrix of a one-hot multinomial draw with the supplied cell-probability vector](goal). -/
def multinomialCov {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℝ) : Matrix I I ℝ :=
  let vv : Matrix I I ℝ := fun i j => v i * v j
  diagonal v - vv

/-- [The treatment, outcome, source observation](hyp:x,y,o) establish [the flattened source-cell indicator direction for the selected treatment and outcome](goal). -/
def sourceStatisticDirection (x : X) (y : Y) (o : E × W × X × Y) :
    (Matrix W E ℝ) × (E → ℝ) :=
  (fun w e => if o.1 = e ∧ o.2.1 = w ∧ o.2.2.1 = x then 1 else 0,
   fun e => if o.1 = e ∧ o.2.2.1 = x ∧ o.2.2.2 = y then 1 else 0)

/-- [The target coordinate](hyp:w) establish [the one-hot target-proxy coordinate direction](goal). -/
def targetDirection (w : W) : W → ℝ := fun w' => if w' = w then 1 else 0

/-- [The array, probability vector](hyp:A,v) establish [the scalar quadratic form obtained by multiplying the vector on both sides of the matrix](goal). -/
def quadForm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (v : I → ℝ) : ℝ := dotProduct v (A.mulVec v)

-- @node: multinomialCov_quadForm_nonneg
/-- [The hv, hsum](hyp:hv,hsum) establish [a normalized nonnegative multinomial covariance matrix has a nonnegative quadratic form in every direction](goal). -/
lemma multinomialCov_quadForm_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (v d : I → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = 1) :
    0 ≤ quadForm (multinomialCov v) d := by
  let m := ∑ i, v i * d i
  have hnonneg : 0 ≤ ∑ i, v i * (d i - m) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)
  have hleft : ∑ i, v i * (d i - m) ^ 2 = ∑ i, v i * d i ^ 2 - m ^ 2 := by
    calc
      _ = ∑ i, (v i * d i ^ 2 - 2 * m * (v i * d i) + m ^ 2 * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum, hsum]
        dsimp [m]
        ring
  suffices quadForm (multinomialCov v) d = ∑ i, v i * (d i - m) ^ 2 by
    rwa [this]
  change (∑ i, d i * ∑ j, ((if i = j then v i else 0) - v i * v j) * d j) = _
  simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub]
  simp [eq_comm, Finset.mul_sum]
  rw [show (∑ x, ∑ i, d x * (v x * v i * d i)) =
      (∑ x, v x * d x) * (∑ i, v i * d i) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [hleft]
  dsimp [m]
  have hsquares : (∑ i, v i * d i ^ 2) = ∑ i, d i ^ 2 * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsquares]
  ring_nf

/-- [The rank index, allocation fraction, observed law, treatment, outcome, target proxy vector](hyp:r0,p,PO,x,y,bvec) establish [the two-sample delta-method variance of the rank-truncated Wald functional](goal). -/
noncomputable def waldDeltaVariance (r0 : RankIndex E W) (p : ℝ)
    (PO : E → W → X → Y → ℝ) (x : X) (y : Y) (bvec : W → ℝ) : ℝ :=
  let Hz := unconditionalBalancingMoments PO x y
  let H := Hz.1
  let z := Hz.2
  let dSource := fderiv ℝ
    (fun hz : (Matrix W E ℝ) × (E → ℝ) => regularWaldFunctional r0 hz.1 hz.2 bvec)
    (H, z)
  let dTarget := fderiv ℝ (fun b : W → ℝ => regularWaldFunctional r0 H z b) bvec
  p⁻¹ * quadForm (multinomialCov (sourceCellVector PO))
      (fun o => dSource (sourceStatisticDirection x y o)) +
    (1 - p)⁻¹ * quadForm (multinomialCov bvec) (fun w => dTarget (targetDirection w))
-- @realizes V_{r_0,x,y}(\mathcal M;p)(true joint source-cell and target multinomial delta variance)

-- @node: ass:regular-fixed-rank
/-- [The model, treatment, rank index](hyp:Mdl,x,r0) establish [the selected conditional proxy matrix has exactly the specified rank](goal). -/
def RegularFixedRank (Mdl : LatentShiftSCM E U W X Y) (x : X) (r0 : ℕ) : Prop :=
  (proxyMomentMatrix Mdl x).rank = r0

-- @node: ass:regular-singular-gap
/-- [The model, treatment, rank index, singular gap](hyp:Mdl,x,r0,c) establish [the selected singular value is bounded below by the specified gap and is strictly separated from the next singular value](goal). -/
def RegularSingularGap (Mdl : LatentShiftSCM E U W X Y) (x : X)
    (r0 : ℕ) (c : ℝ) : Prop :=
  c ≤ sigmaAt r0 (proxyMomentMatrix Mdl x)
-- @realizes c(positive singular-value floor)

-- @node: ass:regular-target-span
/-- [The model, treatment](hyp:Mdl,x) establish [the target proxy vector lies in the selected conditional proxy matrix's column space](goal). -/
def RegularTargetSpan (Mdl : LatentShiftSCM E U W X Y) (x : X) : Prop :=
  ∃ kappa, (proxyMomentMatrix Mdl x).mulVec kappa = targetProxyVector Mdl

-- @node: ass:regular-cell-floor
/-- [The model, positive floor](hyp:Mdl,eta) establish [every observed-law cell is bounded below by the specified positive floor](goal). -/
def RegularCellFloor (Mdl : LatentShiftSCM E U W X Y) (eta : ℝ) : Prop :=
  (∀ e w x y, eta ≤ observedLaw Mdl e w x y) ∧
  (∀ w, eta ≤ targetProxyVector Mdl w)
-- @realizes \eta(uniform source and target cell floor)

-- @node: ass:regular-positive-variance
/-- [The model, treatment, outcome, rank index, allocation fraction, positive floor](hyp:Mdl,x,y,r0,p,eta) establish [the selected Wald delta-method variance exceeds the specified positive floor](goal). -/
def RegularPositiveVariance (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y)
    (r0 : RankIndex E W) (p eta : ℝ) : Prop :=
  eta ≤ waldDeltaVariance r0 p (observedLaw Mdl) x y (targetProxyVector Mdl)

-- @node: def:strongly-identified-submodel
/-- [The rank index, gap, floor, allocation fraction, treatment, outcome, and model](hyp:r0,c,eta,p,x,y,Mdl)
define [membership in the strongly identified submodel](goal): [the model is positive](hyp:model_positive),
[the gap is positive](hyp:c_pos), [the floor is positive](hyp:eta_pos), and the selected problem
has [fixed rank](hyp:fixed_rank), [a singular gap](hyp:singular_gap), [target-span balancing](hyp:target_span),
[uniform cell floors](hyp:cell_floor), and [positive Wald variance](hyp:positive_variance). -/
structure StronglyIdentifiedSubmodel (r0 : RankIndex E W) (c eta : ℝ)
    (p : Set.Ioo (0 : ℝ) 1) (x : X) (y : Y)
    (Mdl : LatentShiftSCM E U W X Y) : Prop where
  model_positive : PositiveLatentShiftClass Mdl
    -- @realizes \mathfrak M_{+}(model membership)
  c_pos : 0 < c -- @realizes c(strictly positive regularity constant)
  eta_pos : 0 < eta -- @realizes \eta(strictly positive regularity constant)
  fixed_rank : RegularFixedRank Mdl x r0.val
  singular_gap : RegularSingularGap Mdl x r0.val c
  target_span : RegularTargetSpan Mdl x
  cell_floor : RegularCellFloor Mdl eta
  positive_variance : RegularPositiveVariance Mdl x y r0 p eta

/-- [The rank index, singular gap, positive floor, allocation fraction, treatment, outcome](hyp:r0,c,eta,p,x,y) establish [the set of positive models satisfying the specified rank, singular-gap, target-span, cell-floor, and variance-floor restrictions](goal). -/
def stronglyIdentifiedSubmodelSet (r0 : RankIndex E W) (c eta : ℝ)
    (p : Set.Ioo (0 : ℝ) 1) (x : X) (y : Y) :
    Set (LatentShiftSCM E U W X Y) :=
  {Mdl | StronglyIdentifiedSubmodel r0 c eta p x y Mdl}
-- @realizes \mathcal R_{r_0,c,\eta}(strongly identified regular submodel)

-- @node: def:regular-wald-estimator
/-- [The rank index, empirical proxy matrix, empirical outcome vector, empirical target vector](hyp:r0,Hhat,zhat,bhat) establish [the rank-truncated Wald point estimator from empirical proxy, outcome, and target moments](goal). -/
noncomputable def regularWaldEstimator (r0 : RankIndex E W) (Hhat : Matrix W E ℝ)
    (zhat : E → ℝ) (bhat : W → ℝ) : ℝ :=
  regularWaldFunctional r0 Hhat zhat bhat
-- @realizes \widehat\theta^{\,W}_{x,y,n}(plug-in truncated-SVD estimator)

-- @node: def:regular-wald-variance
/-- [The rank index, allocation fraction, empirical observed law, treatment, outcome, empirical target vector](hyp:r0,p,Phat,x,y,bhat) establish [the totalized plug-in delta-method variance of the rank-truncated Wald estimator](goal). -/
noncomputable def regularWaldVariance (r0 : RankIndex E W) (p : Set.Ioo (0 : ℝ) 1)
    (Phat : E → W → X → Y → ℝ) (x : X) (y : Y) (bhat : W → ℝ) : ℝ :=
  let Hhat := (unconditionalBalancingMoments Phat x y).1
  if sigmaAt (r0.val + 1) Hhat < sigmaAt r0.val Hhat then
    waldDeltaVariance r0 p Phat x y bhat
  else 0
-- @realizes \widehat V_n(plug-in delta variance)

/-- [the two-sided normal-quantile argument lies strictly between zero and one](goal). -/
lemma waldQuantileArg_mem (alpha : Set.Ioo (0 : ℝ) 1) :
    1 - (alpha : ℝ) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> linarith [alpha.2.1, alpha.2.2]
-- @realizes z_{1-\alpha/2}(normal quantile argument lies in (0,1))
-- @realizes \Phi(Causalean standard-normal CDF)

-- @node: def:regular-wald-interval
/-- [The point estimate, variance estimate, row index, row-size certificate, nominal level](hyp:thetaHat,Vhat,n,_hn,alpha) establish [the closed normal-quantile Wald interval centered at the estimate with its totalized nonnegative standard-error half-width](goal). -/
noncomputable def regularWaldInterval (thetaHat Vhat : ℝ) (n : ℕ) (_hn : 2 ≤ n)
    (alpha : Set.Ioo (0 : ℝ) 1) : Set ℝ :=
  let zcrit := Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2)
  let halfWidth := zcrit * Real.sqrt (Vhat / n)
  Set.Icc (thetaHat - halfWidth) (thetaHat + halfWidth) ∩ Set.Icc (0 : ℝ) 1
-- @realizes I^W_{n,1-\alpha}(Wald interval intersected with [0,1])
-- @realizes \alpha(error level subtype (0,1))

end CausalSmith.SCM.ProxyTargetspanTransport
