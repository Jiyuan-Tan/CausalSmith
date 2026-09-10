import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Fibers
import Causalean.Stat.Sample.PiTransport
import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! Model-induced finite probability measures, finite two-sample block laws, empirical moments,
and the concentration projection set. Infinite i.i.d. sequences occur only inside the proof of
`pi_hoeffding_cell`, through Causalean's finite-prefix transport theorem. -/

open scoped BigOperators ENNReal
open Finset Matrix MeasureTheory ProbabilityTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @env: S2
variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
  [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass E] [MeasurableSingletonClass W]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

private lemma observedWeights_sum (Mdl : LatentShiftSCM E U W X Y) :
    ∑ o : E × W × X × Y,
      ENNReal.ofReal (observedLaw Mdl o.1 o.2.1 o.2.2.1 o.2.2.2) = 1 := by
  simp only [Fintype.sum_prod_type]
  have hY (e : E) (w : W) (x : X) :
      (∑ y, ENNReal.ofReal (observedLaw Mdl e w x y)) =
        ENNReal.ofReal (∑ y, observedLaw Mdl e w x y) :=
    (ENNReal.ofReal_sum_of_nonneg (fun y _ => observedLaw_nonneg Mdl e w x y)).symm
  have hX (e : E) (w : W) :
      (∑ x, ∑ y, ENNReal.ofReal (observedLaw Mdl e w x y)) =
        ENNReal.ofReal (∑ x, ∑ y, observedLaw Mdl e w x y) := by
    simp_rw [hY]
    exact (ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun y _ =>
      observedLaw_nonneg Mdl e w x y)).symm
  have hW (e : E) :
      (∑ w, ∑ x, ∑ y, ENNReal.ofReal (observedLaw Mdl e w x y)) =
        ENNReal.ofReal (∑ w, ∑ x, ∑ y, observedLaw Mdl e w x y) := by
    simp_rw [hX]
    exact (ENNReal.ofReal_sum_of_nonneg (fun w _ => Finset.sum_nonneg fun x _ =>
      Finset.sum_nonneg fun y _ => observedLaw_nonneg Mdl e w x y)).symm
  simp_rw [hW]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => Finset.sum_nonneg fun w _ =>
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => observedLaw_nonneg Mdl e w x y)]
  simp [observedLaw_sum]

/-- [The model](hyp:Mdl) determine [the finite probability mass function induced by the model's observed law](goal). -/
noncomputable def observedPMF (Mdl : LatentShiftSCM E U W X Y) : PMF (E × W × X × Y) :=
  PMF.ofFintype
    (fun o => ENNReal.ofReal (observedLaw Mdl o.1 o.2.1 o.2.2.1 o.2.2.2))
    (observedWeights_sum Mdl)

/-- [The model](hyp:Mdl) determine [the probability measure induced by the model's finite observed-data mass function](goal). -/
noncomputable def observedMeasure (Mdl : LatentShiftSCM E U W X Y) :
    Measure (E × W × X × Y) := (observedPMF Mdl).toMeasure
-- @realizes P_O(probability-measure realization)

/-- [The model](hyp:Mdl) determine [the probability-measure instance for the model-induced observed-data measure](goal). -/
noncomputable instance observedMeasure_isProbability (Mdl : LatentShiftSCM E U W X Y) :
    IsProbabilityMeasure (observedMeasure Mdl) := PMF.toMeasure.isProbabilityMeasure _

private lemma targetWeights_sum (Mdl : LatentShiftSCM E U W X Y) :
    ∑ w, ENNReal.ofReal (targetProxyVector Mdl w) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => targetProxyVector_nonneg Mdl w)]
  simp [targetProxyVector_sum]

/-- [The model](hyp:Mdl) determine [the finite probability mass function induced by the model's target proxy vector](goal). -/
noncomputable def targetProxyPMF (Mdl : LatentShiftSCM E U W X Y) : PMF W :=
  PMF.ofFintype (fun w => ENNReal.ofReal (targetProxyVector Mdl w)) (targetWeights_sum Mdl)

/-- [The model](hyp:Mdl) determine [the probability measure induced by the model's finite target-proxy mass function](goal). -/
noncomputable def targetProxyMeasure (Mdl : LatentShiftSCM E U W X Y) : Measure W :=
  (targetProxyPMF Mdl).toMeasure
-- @realizes b(probability-measure realization)

/-- [The model](hyp:Mdl) determine [the probability-measure instance for the model-induced target-proxy measure](goal). -/
noncomputable instance targetProxyMeasure_isProbability (Mdl : LatentShiftSCM E U W X Y) :
    IsProbabilityMeasure (targetProxyMeasure Mdl) := PMF.toMeasure.isProbabilityMeasure _

/-- [The proxy value](hyp:w) determine [the indicator of a specified target-proxy category](goal). -/
def targetCellIndicator (w : W) : W → ℝ := fun w' => if w' = w then 1 else 0

/-- [the target-law integral of a target-cell indicator equals the corresponding target proxy probability](goal). -/
lemma integral_targetCellIndicator (Mdl : LatentShiftSCM E U W X Y) (w) :
    ∫ w', targetCellIndicator w w' ∂targetProxyMeasure Mdl = targetProxyVector Mdl w := by
  rw [targetProxyMeasure, PMF.integral_eq_sum]
  simp [targetProxyPMF, targetCellIndicator,
    ENNReal.toReal_ofReal (targetProxyVector_nonneg Mdl w)]

/-- The core's finite two-sample product space with the discrete full power-set sigma-field. -/
abbrev Omega (E W X Y : Type*) (ns nt : ℕ) :=
  (Fin ns → E × W × X × Y) × (Fin nt → W)
-- @realizes \Omega(n_s,n_t)(finite product sample space)

/-- [The source sample size, target sample size](hyp:ns,nt) determine [the projection from the joint two-sample space onto its source-observation block](goal). -/
def sourceBlock (ns nt : ℕ) : Omega E W X Y ns nt → (Fin ns → E × W × X × Y) :=
  Prod.fst
-- @realizes O_i^s(source coordinate block) @realizes O^s_{i,n}(row-n source coordinates)

/-- [The source sample size, target sample size](hyp:ns,nt) determine [the projection from the joint two-sample space onto its target-proxy block](goal). -/
def targetBlock (ns nt : ℕ) : Omega E W X Y ns nt → (Fin nt → W) :=
  Prod.snd
-- @realizes W_j^t(target coordinate block) @realizes W^t_{j,n}(row-n target coordinates)

/-- [The model and block sizes](hyp:Mdl,ns,nt) determine [the finite two-sample law](goal),
whose factors are [independent source observations](step:1) and [independent target proxy
draws](step:2). -/
noncomputable def twoSampleLaw (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ) :
    Measure (Omega E W X Y ns nt) :=
  (Measure.pi (fun _ : Fin ns => observedMeasure Mdl)).prod
    (Measure.pi (fun _ : Fin nt => targetProxyMeasure Mdl))
-- @realizes \mathbb P_{\mathcal M}^{\,n_s,n_t}(finite product law)

/-- [The model, source sample size, target sample size](hyp:Mdl,ns,nt) determine [the probability-measure instance for the finite two-sample product law](goal). -/
noncomputable instance twoSampleLaw_isProbability
    (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ) :
    IsProbabilityMeasure (twoSampleLaw Mdl ns nt) := by
  unfold twoSampleLaw
  apply Measure.prod.instIsProbabilityMeasure

/-- [the source-block marginal of the two-sample law is the independent product of the observed-data law](goal). -/
lemma twoSampleLaw_sourceBlock (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ) :
    (twoSampleLaw Mdl ns nt).map (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) =
      Measure.pi (fun _ : Fin ns => observedMeasure Mdl) := by
  exact MeasureTheory.measurePreserving_fst.map_eq

/-- [the target-block marginal of the two-sample law is the independent product of the target-proxy law](goal). -/
lemma twoSampleLaw_targetBlock (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ) :
    (twoSampleLaw Mdl ns nt).map (targetBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) =
      Measure.pi (fun _ : Fin nt => targetProxyMeasure Mdl) := by
  exact MeasureTheory.measurePreserving_snd.map_eq

set_option linter.unusedFintypeInType false in
omit [DecidableEq E] [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- [every subset of the finite two-sample space is measurable](goal). -/
lemma omega_measurableSet (ns nt : ℕ) (s : Set (Omega E W X Y ns nt)) : MeasurableSet s := by
  exact s.toFinite.measurableSet

-- @node: ass:source-iid-sampling
/-- [The model, source sample size, target sample size, sampling law](hyp:Mdl,ns,nt,mu) determine [the condition that the source-block marginal is the independent product of the model's observed-data law](goal). -/
def SourceIidSampling (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ)
    (mu : Measure (Omega E W X Y ns nt)) : Prop :=
  mu.map (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) =
    Measure.pi (fun _ : Fin ns => observedMeasure Mdl)

-- @node: ass:target-iid-sampling
/-- [The model, source sample size, target sample size, sampling law](hyp:Mdl,ns,nt,mu) determine [the condition that the target-block marginal is the independent product of the model's target-proxy law](goal). -/
def TargetIidSampling (Mdl : LatentShiftSCM E U W X Y) (ns nt : ℕ)
    (mu : Measure (Omega E W X Y ns nt)) : Prop :=
  mu.map (targetBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) =
    Measure.pi (fun _ : Fin nt => targetProxyMeasure Mdl)

/-- [The source sample size, treatment, two-sample observation](hyp:ns,x,s) determine [the empirical proxy-by-environment treatment-moment matrix](goal). -/
noncomputable def finEmpProxyMoment {nt : ℕ} (ns : ℕ) (x : X)
    (s : Omega E W X Y ns nt) : Matrix W E ℝ :=
  fun w e => (ns : ℝ)⁻¹ * ∑ i : Fin ns,
    if (s.1 i).1 = e ∧ (s.1 i).2.1 = w ∧ (s.1 i).2.2.1 = x then 1 else 0
-- @realizes \widehat H_x(finite source cell-frequency matrix)

/-- [The source sample size, treatment, outcome, two-sample observation](hyp:ns,x,y,s) determine [the empirical environment-indexed treatment-and-outcome moment vector](goal). -/
noncomputable def finEmpOutcomeMoment {nt : ℕ} (ns : ℕ) (x : X) (y : Y)
    (s : Omega E W X Y ns nt) : E → ℝ :=
  fun e => (ns : ℝ)⁻¹ * ∑ i : Fin ns,
    if (s.1 i).1 = e ∧ (s.1 i).2.2.1 = x ∧ (s.1 i).2.2.2 = y then 1 else 0
-- @realizes \widehat z_{x,y}(finite source outcome frequency)

/-- [The target sample size, two-sample observation](hyp:nt,s) determine [the empirical target-proxy frequency vector](goal). -/
noncomputable def finEmpTargetProxy {ns : ℕ} (nt : ℕ)
    (s : Omega E W X Y ns nt) : W → ℝ :=
  fun w => (nt : ℝ)⁻¹ * ∑ j : Fin nt, if s.2 j = w then 1 else 0
-- @realizes \widehat b(finite target proxy frequency)

/-- [The source sample size, two-sample observation](hyp:ns,s) determine [the empirical mass function of the full source observations](goal). -/
noncomputable def finEmpObservedLaw {nt : ℕ} (ns : ℕ)
    (s : Omega E W X Y ns nt) : E → W → X → Y → ℝ :=
  fun e w x y => (ns : ℝ)⁻¹ * ∑ i : Fin ns,
    if s.1 i = (e, w, x, y) then 1 else 0
-- @realizes P_O(empirical full source-cell law for joint covariance)

/-- Given [the i.i.d. sampling identity, the boundedness condition, positivity of the sample size, positivity of the deviation radius](hyp:hg,hbound,hN,heps), [Hoeffding's inequality for a bounded cell statistic transfers from the canonical infinite i.i.d. sequence to the corresponding finite product measure](goal). -/
lemma pi_hoeffding_cell {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (g : Z → ℝ) (hg : Measurable g)
    (hbound : ∀ᵐ z ∂P, g z ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) (hN : 0 < N)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (Measure.pi (fun _ : Fin N => P)).real
      {s | eps ≤ |(N : ℝ)⁻¹ * ∑ k : Fin N, g (s k) - ∫ z, g z ∂P|} ≤
      2 * Real.exp (-2 * N * eps ^ 2) := by
  let S := Causalean.Stat.iidSample_infinitePi P
  let psi : (ℕ → Z) → (Fin N → Z) := fun omega k => S.Z k omega
  let A : Set (Fin N → Z) :=
    {s | eps ≤ |(N : ℝ)⁻¹ * ∑ k : Fin N, g (s k) - ∫ z, g z ∂P|}
  have hpsi : Measurable psi := Causalean.Stat.iidSample_finN_measurable S N
  have hA : MeasurableSet A := by
    dsimp [A]
    apply measurableSet_le measurable_const
    fun_prop
  have hpush : (Measure.infinitePi (fun _ : ℕ => P)).map psi =
      Measure.pi (fun _ : Fin N => P) := by
    exact Causalean.Stat.iidSample_finN_pushforward S N
  have hmeasure : (Measure.infinitePi (fun _ : ℕ => P)) (psi ⁻¹' A) =
      Measure.pi (fun _ : Fin N => P) A := by
    rw [← hpush, Measure.map_apply hpsi hA]
  have hevent : psi ⁻¹' A =
      {omega | eps ≤ |S.sampleMean g N omega - ∫ z, g z ∂P|} := by
    ext omega
    dsimp [A, psi, Causalean.Stat.IIDSample.sampleMean]
    rw [Fin.sum_univ_eq_sum_range (fun i => g (S.Z i omega)) N]
  have h := Causalean.Stat.Concentration.hoeffding_abs_ge S hg
    (by norm_num : (0 : ℝ) < 1)
    hbound N hN heps
  rw [show {s | eps ≤ |(N : ℝ)⁻¹ * ∑ k : Fin N, g (s k) - ∫ z, g z ∂P|} = A by rfl]
  change ENNReal.toReal (Measure.pi (fun _ : Fin N => P) A) ≤ _
  rw [← hmeasure]
  rw [hevent]
  rw [← MeasureTheory.measureReal_def]
  simpa using h

/-- [The environment type, proxy type](hyp:E,W) determine [the total number of proxy, outcome, and target coordinates controlled by the simultaneous concentration event](goal). -/
def coordinateCount (E W : Type*) [Fintype E] [Fintype W] : ℕ :=
  Fintype.card W * Fintype.card E + Fintype.card E + Fintype.card W
-- @realizes L(m|E|+|E|+m)

/-- [The environment type, proxy type, source sample size, nominal level](hyp:E,W,ns,alpha) determine [the Hoeffding radius for simultaneous source-coordinate control](goal). -/
noncomputable def sourceRadius (E W : Type*) [Fintype E] [Fintype W]
    (ns : ℕ) (alpha : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 * coordinateCount E W / alpha) / (2 * ns))
-- @realizes r_s(sqrt log radius)

/-- [The environment type, proxy type, target sample size, nominal level](hyp:E,W,nt,alpha) determine [the Hoeffding radius for simultaneous target-proxy-coordinate control](goal). -/
noncomputable def targetRadius (E W : Type*) [Fintype E] [Fintype W]
    (nt : ℕ) (alpha : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 * coordinateCount E W / alpha) / (2 * nt))
-- @realizes r_t(sqrt log radius)

/-- [The weight vector](hyp:kappa) determine [the finite coordinatewise ℓ¹ norm of a real vector](goal). -/
def l1Norm (kappa : E → ℝ) : ℝ := ∑ e, |kappa e|

-- @node: def:concentration-projection-set
/-- [The empirical proxy matrix, outcome vector, target vector, block sizes, and nominal
level](hyp:Hhat,zhat,bhat,ns,nt,alpha) determine [the concentration projection set](goal):
candidate values [lie in the closed unit interval](step:1) and [have weights satisfying both
the approximate balancing and outcome-moment inequalities at the stated radii](step:2). -/
noncomputable def concentrationProjectionSet (Hhat : Matrix W E ℝ) (zhat : E → ℝ)
    (bhat : W → ℝ) (ns nt : ℕ) (alpha : Set.Ioo (0 : ℝ) 1) : Set ℝ :=
  {theta | theta ∈ Set.Icc (0 : ℝ) 1 ∧ -- @realizes \vartheta(candidate in [0,1])
    ∃ kappa : E → ℝ,
      (∀ w, |(Hhat.mulVec kappa - bhat) w| ≤
        sourceRadius E W ns (alpha : ℝ) * l1Norm kappa +
          targetRadius E W nt (alpha : ℝ)) ∧
      |dotProduct zhat kappa - theta| ≤
        sourceRadius E W ns (alpha : ℝ) * l1Norm kappa}
-- @realizes \widehat C_{x,y,1-\alpha}(concentration projection set)
-- @realizes \alpha(error level in (0,1))

end CausalSmith.SCM.ProxyTargetspanTransport
