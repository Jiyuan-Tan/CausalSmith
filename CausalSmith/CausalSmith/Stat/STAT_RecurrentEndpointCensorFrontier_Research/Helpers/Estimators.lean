module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Observable recurrent-mean estimators

Finite risk sets, event sums, Kaplan–Meier products, conservative intervals,
martingale components, and the critical and subcritical studentizers.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

noncomputable def armSize {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) : ℕ :=
  (Finset.univ.filter (fun i => (s i).treatment = a)).card
  -- @realizes n_a(number assigned to arm)

noncomputable def riskSet {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => (s i).treatment = a ∧ t ≤ (s i).exit)).card
  -- @realizes Y_an(number still at risk)

noncomputable def invRisk {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  if riskSet a s t = 0 then 0 else (riskSet a s t : ℝ)⁻¹

noncomputable def recurAgg {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℕ :=
  ∑ i : Fin n, if (s i).treatment = a then
    ((s i).recur.times.filter (fun u => u ≤ t)).card else 0
  -- @realizes N_R_an(aggregate observed recurrence count)

noncomputable def deathAgg {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℕ :=
  ∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit ≤ t
    then 1 else 0
  -- @realizes N_D_an(aggregate death count)

noncomputable def deathJump {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (u : ℝ) : ℕ :=
  ∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧ (s i).exit = u
    then 1 else 0

noncomputable def censorJump {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (u : ℝ) : ℕ :=
  ∑ i : Fin n, if (s i).treatment = a ∧ ¬(s i).deathInd ∧
    (s i).exit = u ∧ u < 1 then 1 else 0

noncomputable def exitTimes {n : ℕ} (s : Fin n → ObsHistory) : Finset ℝ :=
  Finset.univ.image (fun i : Fin n => (s i).exit)

noncomputable def deathKM {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  ∏ u ∈ (exitTimes s).filter (fun u => u ≤ t),
    (1 - invRisk a s u * deathJump a s u)
  -- @realizes S_hat_an(death product-limit estimator)

noncomputable def deathKMLeft {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  ∏ u ∈ (exitTimes s).filter (fun u => u < t),
    (1 - invRisk a s u * deathJump a s u)

noncomputable def reverseKMLeft {n : ℕ} (a : Arm) (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  ∏ u ∈ (exitTimes s).filter (fun u => u < t),
    (1 - invRisk a s u * censorJump a s u)

noncomputable def projectArm (c : ClassConstants) (x : ℝ) : ℝ :=
  max 0 (min c.lambdaMax x)

noncomputable def muTildeAt (c : ClassConstants) {n : ℕ} (h : ℝ)
    (a : Arm) (s : Fin n → ObsHistory) : ℝ :=
  ∑ i : Fin n, if (s i).treatment = a then
    Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1 - h)).map
      (fun t => continuationWeight (holderOrder c) h t * deathKMLeft a s t * invRisk a s t))
    else 0
  -- @realizes mu_tilde_an(weighted recurrence sum)

noncomputable def muHatAt (c : ClassConstants) {n : ℕ} (h : ℝ)
    (a : Arm) (s : Fin n → ObsHistory) : ℝ :=
  projectArm c (muTildeAt c h a s)
  -- @realizes mu_hat_an(projected arm estimator)

-- @node: def:observable-estimator
noncomputable def observableEstimator (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  muHatAt c (bandwidth c n) true s - muHatAt c (bandwidth c n) false s
  -- @realizes theta_hat_n(continued contrast estimator)

noncomputable def ordinaryMuTilde (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) : ℝ :=
  ∑ i : Fin n, if (s i).treatment = a then
    Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
      (fun t => deathKMLeft a s t * invRisk a s t))
    else 0
  -- @realizes mu_tilde_an_0(unweighted recurrence sum)

noncomputable def ordinaryMuHat (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  projectArm c (ordinaryMuTilde a s)
  -- @realizes mu_hat_an_0(projected unweighted arm estimator)

-- @node: def:ordinary-observable-estimator
noncomputable def ordinaryEstimator (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  ordinaryMuHat c true s - ordinaryMuHat c false s
  -- @realizes theta_hat_n_0(ordinary contrast estimator)

-- @node: def:conservative-interval
noncomputable def conservativeInterval (c : ClassConstants) (K : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) : Set ℝ :=
  Set.Icc (observableEstimator c s - Real.sqrt (K * riskScale c n))
    (observableEstimator c s + Real.sqrt (K * riskScale c n)) ∩
    Set.Icc (-c.lambdaMax) c.lambdaMax
  -- @realizes I_n(conservative clipped interval)

noncomputable def truncatedMean (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(1 - h),
    continuationWeight (holderOrder c) h t * survival P a t * P.lam a t
  -- @realizes mu_a_h(continued truncated target)

noncomputable def remainingTarget (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h u : ℝ) : ℝ :=
  ∫ t in u..(1 - h),
    continuationWeight (holderOrder c) h t * survival P a t * P.lam a t
  -- @realizes H_ah(remaining weighted target)

noncomputable def recurMart (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  recurAgg a s t - ∫ u in (0 : ℝ)..t, (riskSet a s u : ℝ) * P.lam a u
  -- @realizes M_R_an(recurrence count minus compensator)

noncomputable def deathMart (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (t : ℝ) : ℝ :=
  deathAgg a s t - ∫ u in (0 : ℝ)..t, (riskSet a s u : ℝ) * P.hazard a u
  -- @realizes M_D_an(death count minus compensator)

noncomputable def extinction (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) : ℝ :=
  if armSize a s = 0 then 0 else
    sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧ 0 < riskSet a s t}
  -- @realizes zeta_an(last positive risk time; zero for empty arm)

-- @node: def:error-components
noncomputable def errorComponents (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) {n : ℕ} (s : Fin n → ObsHistory) (h u t : ℝ) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  (remainingTarget c P a h u, recurMart P a s t,
    deathMart P a s t, extinction a s, invRisk a s t)

noncomputable def armCriticalVariance (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  ∑ i : Fin n, if (s i).treatment = a then
    Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1 - bandwidth c n)).map
      (fun t => (continuationWeight (holderOrder c) (bandwidth c n) t) ^ 2 *
        (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2))
    else 0
  -- @realizes v_hat_an(arm optional variation)

-- @node: def:critical-variance-estimator
noncomputable def criticalVarianceEstimator (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  armCriticalVariance c false s + armCriticalVariance c true s
  -- @realizes v_hat_n(sum of arm optional variations)

noncomputable def nonFallback (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : Prop :=
  0 < armSize false s ∧ 0 < armSize true s ∧ 0 < criticalVarianceEstimator c s
  -- @realizes F_n(critical nonfallback event)

noncomputable def normalCDF (z : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Iic z)
  -- @realizes Phi(standard Gaussian distribution function)

noncomputable def normalQuantile (alpha : ℝ) : ℝ :=
  sInf {z : ℝ | 1 - alpha / 2 ≤ normalCDF z}
  -- @realizes z_alpha(two-sided standard Gaussian quantile)

-- @node: def:critical-studentized-interval
noncomputable def criticalInterval (c : ClassConstants) (alpha : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) : Set ℝ := by
  classical
  exact
  if nonFallback c s then
    Set.Icc (observableEstimator c s - normalQuantile alpha *
      Real.sqrt (criticalVarianceEstimator c s))
      (observableEstimator c s + normalQuantile alpha *
        Real.sqrt (criticalVarianceEstimator c s)) ∩
      Set.Icc (-c.lambdaMax) c.lambdaMax
  else Set.Icc (-c.lambdaMax) c.lambdaMax
  -- @realizes J_n(critical interval with full-range fallback)

noncomputable def criticalCoefficient (c : ClassConstants) : ℝ :=
  (2 * c.beta + 2)⁻¹ -- @realizes q_beta(critical multiplier)

noncomputable def criticalVariance (c : ClassConstants) (P : SubjectLaw) : ℝ :=
  criticalCoefficient c * ∑ a : Arm,
    survival P a 1 * P.lam a 1 / (P.p a * P.g a)
  -- @realizes V_star(critical variance functional)

noncomputable def subcriticalInfluence (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (o : ObsHistory) : ℝ :=
  (if o.treatment = a then
    Multiset.sum (o.recur.times.map (fun t => (retention P a t)⁻¹)) -
      ∫ t in (0 : ℝ)..o.exit, P.lam a t / retention P a t
    else 0) / P.p a -
  (if o.treatment = a then
    (if o.deathInd then
      remainingTarget c P a 0 o.exit /
        (survival P a o.exit * retention P a o.exit) else 0) -
      ∫ t in (0 : ℝ)..o.exit,
        remainingTarget c P a 0 t * P.hazard a t /
          (survival P a t * retention P a t)
    else 0) / P.p a
  -- @realizes xi_ai(one-subject arm martingale influence)

noncomputable def subcriticalVariance (c : ClassConstants) (P : SubjectLaw) : ℝ :=
  ∑ a : Arm, (P.p a)⁻¹ *
    ∫ t in (0 : ℝ)..1,
      survival P a t * P.lam a t / retention P a t +
      (remainingTarget c P a 0 t) ^ 2 * P.hazard a t /
        (survival P a t * retention P a t)
  -- @realizes sigma_sub_P(subcritical asymptotic variance)

noncomputable def remainingMeanHat (c : ClassConstants) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (u : ℝ) : ℝ :=
  max 0 (min (c.lambdaMax * (1 - u))
    (∑ i : Fin n, if (s i).treatment = a then
      Multiset.sum (((s i).recur.times.filter (fun t => u ≤ t ∧ t ≤ 1)).map
        (fun t => deathKMLeft a s t * invRisk a s t)) else 0))
  -- @realizes H_hat_an_0(projected remaining mean)

noncomputable def sigmaHatSq (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  ∑ a : Arm, (
    (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a then
      Multiset.sum (((s i).recur.times.filter (fun t => t ≤ 1)).map
        (fun t => (deathKMLeft a s t) ^ 2 * (invRisk a s t) ^ 2)) else 0) +
    (n : ℝ) * (∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd then
      (remainingMeanHat c a s (s i).exit) ^ 2 * (invRisk a s (s i).exit) ^ 2 else 0))
  -- @realizes sigma_hat_sub_n(observed optional variation)

noncomputable def nonFallbackSub (c : ClassConstants) {n : ℕ}
    (s : Fin n → ObsHistory) : Prop :=
  0 < armSize false s ∧ 0 < armSize true s ∧ 0 < sigmaHatSq c s
  -- @realizes F_sub_n(subcritical nonfallback event)

noncomputable def subcriticalInterval (c : ClassConstants) (alpha : ℝ) {n : ℕ}
    (s : Fin n → ObsHistory) : Set ℝ := by
  classical
  exact
  if nonFallbackSub c s then
    Set.Icc (ordinaryEstimator c s -
      normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n)
      (ordinaryEstimator c s +
        normalQuantile alpha * Real.sqrt (sigmaHatSq c s) / Real.sqrt n) ∩
      Set.Icc (-c.lambdaMax) c.lambdaMax
  else Set.Icc (-c.lambdaMax) c.lambdaMax
  -- @realizes J_sub_n(subcritical interval with full-range fallback)

-- @node: def:subcritical-inference
noncomputable def subcriticalConstruction (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (alpha : ℝ) {n : ℕ} (o : ObsHistory)
    (s : Fin n → ObsHistory) (u : ℝ) :=
  (subcriticalInfluence c P a o, subcriticalVariance c P,
    remainingMeanHat c a s u, sigmaHatSq c s,
    (fun s' : Fin n → ObsHistory => nonFallbackSub c s'),
    subcriticalInterval c alpha s)

def CriticalScope (c : ClassConstants) (P : SubjectLaw) : Prop :=
  (∀ n, IidSampling P n (sampleLaw P n)) ∧ RandomAssignment P ∧
  AssignmentLaw P ∧ TreatmentOverlap c P ∧ PoissonRecurrence P ∧
  DeathHazard P ∧ RecurrenceDeathIndependence P ∧
  IndependentCensoring P ∧ RecurrenceBounds c P ∧ DeathBounds c P ∧
  EndpointRetention c P ∧ TailEnvelopeSmall c ∧
  EndpointCoefficientBounds c P ∧ InteriorRetention c P ∧
  RecurrenceHolder c P ∧ DeathHolder c P

def SubcriticalScope (c : ClassConstants) (P : SubjectLaw) : Prop :=
  (∀ n, IidSampling P n (sampleLaw P n)) ∧ RandomAssignment P ∧
  AssignmentLaw P ∧ TreatmentOverlap c P ∧ PoissonRecurrence P ∧
  DeathHazard P ∧ RecurrenceDeathIndependence P ∧
  IndependentCensoring P ∧ RecurrenceBounds c P ∧ DeathBounds c P ∧
  EndpointRetention c P ∧ TailEnvelopeSmall c ∧
  EndpointCoefficientBounds c P ∧ InteriorRetention c P ∧
  RecurrenceHolder c P ∧ DeathHolder c P

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
