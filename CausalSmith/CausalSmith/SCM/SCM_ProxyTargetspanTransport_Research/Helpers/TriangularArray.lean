import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Sampling
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.SetGeometry
import Causalean.Stat.Minimax.HonestConfidenceSet
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

/-! Finite-row triangular two-sample arrays, their admissible class, and arbitrary nonempty
confidence-set sequences on the row sample spaces. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @env: S3
variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
  [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass E] [MeasurableSingletonClass W]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

/-- [The environment, latent, proxy, treatment, and outcome types together with the two allocation
sequences](hyp:E,U,W,X,Y,ns,nt) define [a finite two-sample triangular array](goal), recording
[one latent-shift model per row](step:1), [its row sampling law](step:2), and [positivity of every
nontrivial row model](step:3). -/
structure TwoSampleArray (E U W X Y : Type*)
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    (ns nt : ℕ → ℕ) where
    -- @realizes n_s(n)(externally fixed source-size sequence)
    -- @realizes n_t(n)(externally fixed target-size sequence)
  Mn : ℕ → LatentShiftSCM E U W X Y
    -- @realizes \mathbb M(array of models) @realizes \mathcal M_n(row model)
  rowLaw : ∀ n, Measure (Omega E W X Y (ns n) (nt n))
    -- @realizes \mathbb P_{\mathcal M_n}^{\,n_s(n),n_t(n)}(ambient finite row law)
  rows_positive : ∀ n, 2 ≤ n → PositiveLatentShiftClass (Mn n)

-- @realizes n(triangular row index n≥2)
-- @realizes \Omega_n(Omega at the row sample sizes)

-- @node: ass:triangular-allocation
/-- [The source allocation, target allocation, allocation fraction](hyp:ns,nt,p) establish [every nontrivial row has positive source and target blocks summing to the row size, and the source fraction converges to the specified interior limit](goal). -/
def TriangularAllocation (ns nt : ℕ → ℕ) (p : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧
    (∀ n, 2 ≤ n → 1 ≤ ns n ∧ 1 ≤ nt n ∧ ns n + nt n = n) ∧
    Filter.Tendsto (fun n => (ns n : ℝ) / n) Filter.atTop (nhds p)
-- @realizes p(source allocation limit in (0,1))

-- @node: ass:triangular-source-iid-sampling
/-- [The model sequence, source allocation, target allocation, rowLaw](hyp:Mn,ns,nt,rowLaw) establish [every nontrivial row has the model's two-sample law and the corresponding independent source-block marginal](goal). -/
def TriangularSourceIidSampling (Mn : ℕ → LatentShiftSCM E U W X Y)
    (ns nt : ℕ → ℕ) (rowLaw : ∀ n, Measure (Omega E W X Y (ns n) (nt n))) : Prop :=
  ∀ n, 2 ≤ n →
    rowLaw n = twoSampleLaw (Mn n) (ns n) (nt n) ∧
      SourceIidSampling (Mn n) (ns n) (nt n) (rowLaw n)
-- @realizes O^s_{i,n}(finite row source block with externally fixed allocation)

-- @node: ass:triangular-target-iid-sampling
/-- [The model sequence, source allocation, target allocation, rowLaw](hyp:Mn,ns,nt,rowLaw) establish [every nontrivial row has the model's two-sample law and the corresponding independent target-block marginal](goal). -/
def TriangularTargetIidSampling (Mn : ℕ → LatentShiftSCM E U W X Y)
    (ns nt : ℕ → ℕ) (rowLaw : ∀ n, Measure (Omega E W X Y (ns n) (nt n))) : Prop :=
  ∀ n, 2 ≤ n →
    rowLaw n = twoSampleLaw (Mn n) (ns n) (nt n) ∧
      TargetIidSampling (Mn n) (ns n) (nt n) (rowLaw n)
-- @realizes W^t_{j,n}(finite row target block with externally fixed allocation)

-- @node: ass:array-target-span
/-- [The model sequence, treatment](hyp:Mn,x) establish [every nontrivial row has balancing weights that reproduce its target proxy distribution](goal). -/
def ArrayTargetSpan (Mn : ℕ → LatentShiftSCM E U W X Y) (x : X) : Prop :=
  ∀ n, 2 ≤ n →
    (balancingFiber (condProxyMatrix (Mn n) x) (targetProxyVector (Mn n))).Nonempty

-- @node: def:studentized-array-class
/-- [The limiting fraction, treatment, allocation sequences, and array](hyp:p,x,ns,nt,A) define
[membership in the studentized array class](goal) through [the allocation condition](hyp:allocation),
[source-block product sampling](hyp:source_iid), [target-block product sampling](hyp:target_iid),
and [row-wise target-span balancing](hyp:target_span). -/
structure StudentizedArrayClass (p : Set.Ioo (0 : ℝ) 1) (x : X)
    (ns nt : ℕ → ℕ) (A : TwoSampleArray E U W X Y ns nt) : Prop where
  allocation : TriangularAllocation ns nt p
  source_iid : TriangularSourceIidSampling A.Mn ns nt A.rowLaw
  target_iid : TriangularTargetIidSampling A.Mn ns nt A.rowLaw
  target_span : ArrayTargetSpan A.Mn x

/-- [The allocation fraction, treatment, source allocation, target allocation](hyp:p,x,ns,nt) establish [the class of positive two-sample arrays satisfying the specified allocation, row-law, sampling, and target-span conditions](goal). -/
def studentizedArrayClassSet (p : Set.Ioo (0 : ℝ) 1) (x : X) (ns nt : ℕ → ℕ) :
    Set (TwoSampleArray E U W X Y ns nt) :=
  {A | StudentizedArrayClass p x ns nt A}
-- @realizes \mathcal A_p(target-span triangular-array class)

/-- [The array, row index, treatment, outcome](hyp:A,n,x,y) establish [the selected interventional probability in the specified array row](goal). -/
def rowInterventionalProb {ns nt : ℕ → ℕ}
    (A : TwoSampleArray E U W X Y ns nt) (n : ℕ) (x : X) (y : Y) :=
  interventionalProb (A.Mn n) x y
-- @realizes \theta_{x,y,n}(row do functional)

/-- [The array, treatment, row index, omega](hyp:_A,x,n,omega) establish [the empirical proxy-by-environment treatment-moment matrix in the specified array row](goal). -/
noncomputable def rowEmpProxyMoment {ns nt : ℕ → ℕ}
    (_A : TwoSampleArray E U W X Y ns nt)
    (x : X) (n : ℕ) (omega : Omega E W X Y (ns n) (nt n)) : Matrix W E ℝ :=
  finEmpProxyMoment (ns n) x omega
-- @realizes \widehat H_{x,n}(row empirical proxy moment)

/-- [The array, treatment, outcome, row index, omega](hyp:_A,x,y,n,omega) establish [the empirical treatment-and-outcome moment vector in the specified array row](goal). -/
noncomputable def rowEmpOutcomeMoment {ns nt : ℕ → ℕ}
    (_A : TwoSampleArray E U W X Y ns nt)
    (x : X) (y : Y) (n : ℕ) (omega : Omega E W X Y (ns n) (nt n)) : E → ℝ :=
  finEmpOutcomeMoment (ns n) x y omega
-- @realizes \widehat z_{x,y,n}(row empirical outcome moment)

/-- [The array, row index, omega](hyp:_A,n,omega) establish [the empirical target-proxy frequency vector in the specified array row](goal). -/
noncomputable def rowEmpTargetProxy {ns nt : ℕ → ℕ}
    (_A : TwoSampleArray E U W X Y ns nt)
    (n : ℕ) (omega : Omega E W X Y (ns n) (nt n)) : W → ℝ :=
  finEmpTargetProxy (nt n) omega
-- @realizes \widehat b_n(row empirical target proxy)

-- keep: realizes the core symbol d_{x,n}, the minimum balancing-weight norm used to
-- define the unrestricted array class even though the theorem proof does not inspect it.
/-- [The array, treatment, row index](hyp:A,x,n) establish [the infimum ℓ² norm among row-specific balancing weights, with zero assigned to an empty fiber](goal). -/
noncomputable def minimumBalancingNorm {ns nt : ℕ → ℕ}
    (A : TwoSampleArray E U W X Y ns nt)
    (x : X) (n : ℕ) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | ∃ kappa : E → ℝ,
    (proxyMomentMatrix (A.Mn n) x).mulVec kappa = targetProxyVector (A.Mn n) ∧
      d = ENNReal.ofReal (Real.sqrt (∑ e, (kappa e) ^ 2))}
-- @realizes d_{x,n}(minimum balancing-weight l2 norm)

/-- [The observable types and source and target allocation sequences](hyp:E,W,X,Y,ns,nt) define
[a sequence of row confidence-set rules](goal), consisting of [one set-valued rule on each finite
row space](step:1), [nonemptiness of every reported set](step:2), and [containment of every reported
set in the closed unit interval](step:3). -/
structure ConfidenceSetSeq (E W X Y : Type*)
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    (ns nt : ℕ → ℕ) where
  set : ∀ n, Omega E W X Y (ns n) (nt n) → Set ℝ
    -- @realizes \mathcal C_n(row confidence rule)
  nonempty : ∀ n omega, (set n omega).Nonempty
  sub_unit : ∀ n omega, set n omega ⊆ Set.Icc (0 : ℝ) 1

set_option linter.unusedFintypeInType false in
omit [DecidableEq E] [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- [membership of a fixed value in a row confidence set is a measurable event on the finite row sample space](goal). -/
lemma confidenceSetSeq_measurableSet {ns nt : ℕ → ℕ}
    (C : ConfidenceSetSeq E W X Y ns nt)
    (n : ℕ) (theta : ℝ) : MeasurableSet {omega | theta ∈ C.set n omega} := by
  exact omega_measurableSet (E := E) (W := W) (X := X) (Y := Y) _ _ _

/-- Uniform coverage over arrays using the fixed allocation sequence indexing `C`. -/
noncomputable def UniformArrayCoverage {ns nt : ℕ → ℕ}
    (C : ConfidenceSetSeq E W X Y ns nt)
    (p : Set.Ioo (0 : ℝ) 1) (x : X) (y : Y) (alpha : Set.Ioo (0 : ℝ) 1) : Prop :=
  1 - (alpha : ℝ) ≤ Filter.liminf
    (fun n => Causalean.Stat.coverageInfOrOne
      (fun A : studentizedArrayClassSet (E := E) (U := U) (W := W) (Y := Y) p x ns nt =>
        (A.1.rowLaw n).real {omega |
          rowInterventionalProb A.1 n x y ∈
            C.set n omega})) Filter.atTop

/-- [The model, source allocation, target allocation, row index](hyp:Mdl,ns,nt,n) establish [the row-wise two-sample law obtained by repeating one fixed model with the supplied allocation](goal). -/
noncomputable def constRowLaw (Mdl : LatentShiftSCM E U W X Y)
    (ns nt : ℕ → ℕ) (n : ℕ) : Measure (Omega E W X Y (ns n) (nt n)) :=
  twoSampleLaw Mdl (ns n) (nt n)

end CausalSmith.SCM.ProxyTargetspanTransport
