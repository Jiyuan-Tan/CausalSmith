import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.CitedGates
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.LocalPath
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitBernoulli
import Causalean.Stat.CLT.GaussianLimit
import Causalean.Stat.Limit.ConvergenceVec
import Causalean.Stat.Minimax.Pinsker

/-! # Bernoulli target-tangent LAN experiment -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

/-- Bernoulli target score. -/
def bernoulliTargetScore (P0 : Measure (Schedule n)) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (k : Fin K) (o : Record K n) : ℝ :=
  if k ∈ A ∧ o.2.1 ∈ exactSlice n (m k) then
    (recordWelfare n o - assignmentMean P0 o.2.1) / sliceVariance P0 (m k) else 0
-- @realizes \dot\ell_k^B(1{Z∈S_k}(W-mu_Z)/tau_k²)

/-- Bernoulli central sequence. -/
def bernoulliCentralSequence (P0 : Measure (Schedule n)) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (O : Fin C → Record K n) : Fin K → ℝ :=
  fun k => (Real.sqrt C)⁻¹ * ∑ c, bernoulliTargetScore P0 m A k (O c)
-- @realizes \Delta_C^B(C⁻¹/² sum_c dot-ell_A^B)

/-- Local-law part of the Bernoulli LAN statement, kept separate for reuse by
the oracle transfer theorem. -/
lemma target_tangent_lan_bernoulli_local {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ) (A : Finset (Fin K)) (tauLower : ℝ)
    (h : ActiveIndex A → ℝ)
    (h_iid : IidSchedules P0 sampleLaw) (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P0 labelLaw assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower) :
    bernoulliObservedLaw (leastFavourablePath P0 A m (extendActive A h) 0) p m =
      bernoulliObservedLaw P0 p m ∧
    (∀ k : ActiveIndex A, HasDerivAt
      (fun t => exactSliceWelfare (leastFavourablePath P0 A m (extendActive A h) t) m k.1)
        (h k) 0) := by sorry

/-- Active-coordinate Gaussian shift convergence, including its mean vector. -/
def BernoulliActiveGaussianShiftLimit (P0 : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (A : Finset (Fin K)) (h : ActiveIndex A → ℝ)
    (Sigma : ActiveIndex A → ActiveIndex A → ℝ) : Prop :=
  ∀ t : ActiveIndex A → ℝ,
    Tendsto (fun N => ∫ O : Fin N → Record K n,
      Real.cos (∑ k, t k * (Real.sqrt N *
        ((calibratedEstimator O m A).2 k - exactSliceWelfare P0 m k.1)))
        ∂(Measure.pi fun _ : Fin N => bernoulliObservedLaw
          (leastFavourablePath P0 A m (extendActive A h) (Real.sqrt N)⁻¹) p m)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)) *
        Real.cos (∑ i, t i * h i))) ∧
    Tendsto (fun N => ∫ O : Fin N → Record K n,
      Real.sin (∑ k, t k * (Real.sqrt N *
        ((calibratedEstimator O m A).2 k - exactSliceWelfare P0 m k.1)))
        ∂(Measure.pi fun _ : Fin N => bernoulliObservedLaw
          (leastFavourablePath P0 A m (extendActive A h) (Real.sqrt N)⁻¹) p m)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)) *
        Real.sin (∑ i, t i * h i)))

-- @node: thm:target-tangent-lan-bernoulli
/-- The explicit target path is LAN with information `diag(q_k/tau_k²)`, has the
shifted calibrated Gaussian law, and obeys the compact Gaussian minimax lower bound. -/
theorem target_tangent_lan_bernoulli {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ) (A : Finset (Fin K)) (tauLower M : ℝ)
    (h_iid : IidSchedules P0 sampleLaw) (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P0 labelLaw assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower)
    (hmenu : WellFormedMenu n K m) (hp : InSimplex p) (hA : 2 ≤ A.card)
    (hargmax : ∀ k, k ∈ A ↔ ∀ j, exactSliceWelfare P0 m j ≤ exactSliceWelfare P0 m k)
    (hseparated : ∃ gap > 0, ∀ k, k ∉ A →
      exactSliceWelfare P0 m k + gap ≤
        Finset.univ.sup' Finset.univ_nonempty (exactSliceWelfare P0 m))
    (hM : 0 < M) :
    let q := (hitMatrix n m p).2
    let information : ActiveIndex A → ActiveIndex A → ℝ :=
      fun i j => if i = j then q i.1 / sliceVariance P0 (m i.1) else 0
    let covariance : ActiveIndex A → ActiveIndex A → ℝ :=
      fun i j => if i = j then sliceVariance P0 (m i.1) / q i.1 else 0
    (∀ i j, information i j = if i = j then q i.1 / sliceVariance P0 (m i.1) else 0) ∧
    (∀ i j, covariance i j = if i = j then sliceVariance P0 (m i.1) / q i.1 else 0) ∧
    (∀ k : ActiveIndex A,
      InL2Zero (bernoulliObservedLaw P0 p m)
        (bernoulliTargetScore P0 m A k.1)) ∧
    (∀ h : ActiveIndex A → ℝ,
      let hFull := extendActive A h
      (∀ z, WellFormedAssignmentMarginal P0 z) ∧
      (∀ t z, WellFormedTiltedMarginal P0 A m hFull t z) ∧
      bernoulliObservedLaw (leastFavourablePath P0 A m hFull 0) p m =
        bernoulliObservedLaw P0 p m ∧
      (∀ k : ActiveIndex A, HasDerivAt
        (fun t => exactSliceWelfare (leastFavourablePath P0 A m hFull t) m k.1)
          (h k) 0) ∧
      LikelihoodLAN
        (fun N => Measure.pi fun _ : Fin N => bernoulliObservedLaw P0 p m)
        (fun N => Measure.pi fun _ : Fin N => bernoulliObservedLaw
          (leastFavourablePath P0 A m hFull (Real.sqrt N)⁻¹) p m)
        (fun _ O => ∑ k, h k * bernoulliCentralSequence P0 m A O k.1)
        (∑ i, ∑ j, h i * information i j * h j) ∧
      (∀ t : ActiveIndex A → ℝ,
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.cos (∑ k, t k * bernoulliCentralSequence P0 m A O k.1)
            ∂(Measure.pi fun _ : Fin N => bernoulliObservedLaw P0 p m)) atTop
          (nhds (Real.exp (-((∑ i, ∑ j, t i * information i j * t j) / 2)))) ∧
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.sin (∑ k, t k * bernoulliCentralSequence P0 m A O k.1)
            ∂(Measure.pi fun _ : Fin N => bernoulliObservedLaw P0 p m)) atTop (nhds 0)) ∧
      BernoulliActiveGaussianShiftLimit P0 p m A h covariance) ∧
    (∀ delta : ∀ N, (Fin N → Record K n) → Fin K → ℝ,
      (∀ N, RandomizedRule (delta N)) →
      gaussianCompactValueReal A (fun k => sliceVariance P0 (m k)) q M ≤
        Filter.liminf (fun (N : ℕ) => sSup {risk : ℝ | ∃ h : ActiveIndex A → ℝ,
          quotientNorm A (extendActive A h) ≤ M ∧ risk = Real.sqrt N *
            ∫ O, ∑ a, delta N O a * simpleRegret A
              (exactSliceWelfare (leastFavourablePath P0 A m (extendActive A h)
                (Real.sqrt N)⁻¹) m) a
              ∂(Measure.pi fun _ : Fin N => bernoulliObservedLaw
                (leastFavourablePath P0 A m (extendActive A h) (Real.sqrt N)⁻¹) p m)}) atTop) ∧
    Tendsto (fun N : ℕ => gaussianCompactValue A
      (fun k => sliceVariance P0 (m k)) q N) atTop
      (nhds (gaussianGlobalValue A (fun k => sliceVariance P0 (m k)) q)) := by sorry
-- @realizes I_B(diag(q_k/tau_k²))
-- @realizes \Sigma_{B,A}(diag(tau_k²/q_k) on A)

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
