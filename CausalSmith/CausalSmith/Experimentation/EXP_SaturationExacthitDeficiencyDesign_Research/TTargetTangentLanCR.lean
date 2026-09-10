import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.CitedGates
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.LocalPath
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.GaussianGame
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitCRFace

/-! # Fixed-count target-tangent LAN experiment -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

/-- Fixed-stratum target score. -/
def crTargetScore (P0 : Measure (Schedule n)) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (k : Fin K) (o : Record K n) : ℝ :=
  if k ∈ A ∧ o.1 = k then
    (recordWelfare n o - assignmentMean P0 o.2.1) / sliceVariance P0 (m k) else 0
-- @realizes \dot\ell_{c,k}^{CR}(1{L=k}(W-mu_Z)/tau_k²)

def crCentralSequence (P0 : Measure (Schedule n)) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (O : Fin C → Record K n) : Fin K → ℝ :=
  fun k => (Real.sqrt C)⁻¹ * ∑ c, crTargetScore P0 m A k (O c)
-- @realizes \Delta_C^{CR}(C⁻¹/² sum_c dot-ell_{c,A}^{CR})

/-- Local path identities used by the CR oracle transfer theorem. -/
lemma target_tangent_lan_cr_local {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (tauLower : ℝ) (h : ActiveIndex A → ℝ)
    (h_iid : IidSchedules P0 sampleLaw) (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : CrLabelVector (counts C) labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_shares : CrActiveShares counts alpha A)
    (h_slices : CrExactSlices m P0 labelLaw assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower) :
    crObservedLaw (C := C) (leastFavourablePath P0 A m (extendActive A h) 0) (counts C) m =
      crObservedLaw (C := C) P0 (counts C) m ∧
    ∀ k : ActiveIndex A, HasDerivAt
      (fun t => exactSliceWelfare (leastFavourablePath P0 A m (extendActive A h) t) m k.1)
        (h k) 0 := by sorry

/-- Conditional within-stratum centering of every active CR score coordinate. -/
def CrTargetScoresConditionallyCentered (P0 : Measure (Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (assignmentLaw : AssignmentKernel C K n) (m : Fin K → ℕ)
    (A : Finset (Fin K)) : Prop :=
  ∀ c k, k ∈ A → 0 < (labelLaw {labels | labels c = k}).toReal →
    (∫ Y, ∫ z, (welfare Y z - assignmentMean P0 z) / sliceVariance P0 (m k)
      ∂(assignmentLaw c k Y) ∂P0) = 0

/-- A fair real-valued target bit. -/
def halfBernoulliReal : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 1

/-- The explicit witness has one independent fair welfare bit per assignment,
copied across all units of that assignment. -/
def independentHalfTargetBitLaw (n : ℕ) : Measure (Schedule n) :=
  Measure.pi fun _ : Assignment n =>
    halfBernoulliReal.map fun (w : ℝ) (_ : Fin n) => w

-- @node: thm:target-tangent-lan-cr
/-- The fixed-count target path is LAN with information `diag(alpha_k/tau_k²)`
and satisfies the finite-prior Gaussian lower bound. -/
theorem target_tangent_lan_cr {C n K : ℕ} [NeZero n] [NeZero K]
    (P0 : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (tauLower M : ℝ)
    (h_iid : IidSchedules P0 sampleLaw) (h_isolated : IsolatedClusters sampleLaw)
    (h_labels : CrLabelVector (counts C) labelLaw)
    (h_indep : CrLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_shares : CrActiveShares counts alpha A)
    (h_slices : CrExactSlices m P0 labelLaw assignmentLaw)
    (h_nondegenerate : NondegenerateActiveSlices P0 m A tauLower)
    (hmenu : WellFormedMenu n K m) (hA : 2 ≤ A.card)
    (hargmax : ∀ k, k ∈ A ↔ ∀ j, exactSliceWelfare P0 m j ≤ exactSliceWelfare P0 m k)
    (hcounts : ∀ N, ∑ k, counts N k = N)
    (hM : 0 < M) :
    let information : ActiveIndex A → ActiveIndex A → ℝ :=
      fun i j => if i = j then alpha i.1 / sliceVariance P0 (m i.1) else 0
    let covariance : ActiveIndex A → ActiveIndex A → ℝ :=
      fun i j => if i = j then sliceVariance P0 (m i.1) / alpha i.1 else 0
    (∀ i j, information i j = if i = j then alpha i.1 / sliceVariance P0 (m i.1) else 0) ∧
    (∀ i j, covariance i j = if i = j then sliceVariance P0 (m i.1) / alpha i.1 else 0) ∧
    CrTargetScoresConditionallyCentered P0 labelLaw assignmentLaw m A ∧
    (∀ h : ActiveIndex A → ℝ,
      let hFull := extendActive A h
      (∀ z, WellFormedAssignmentMarginal P0 z) ∧
      (∀ t z, WellFormedTiltedMarginal P0 A m hFull t z) ∧
      crObservedLaw (C := C) (leastFavourablePath P0 A m hFull 0) (counts C) m =
        crObservedLaw (C := C) P0 (counts C) m ∧
      LikelihoodLAN (Omega := fun N => Fin N → Record K n)
        (fun N => crObservedLaw (C := N) P0 (counts N) m)
        (fun N => crObservedLaw (C := N)
          (leastFavourablePath P0 A m hFull (Real.sqrt N)⁻¹) (counts N) m)
        (fun N O => ∑ k, h k * crCentralSequence (C := N) P0 m A O k.1)
        (∑ i, ∑ j, h i * information i j * h j) ∧
      (∀ t : ActiveIndex A → ℝ,
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.cos (∑ k, t k * crCentralSequence (C := N) P0 m A O k.1)
            ∂(crObservedLaw (C := N) P0 (counts N) m)) atTop
          (nhds (Real.exp (-((∑ i, ∑ j, t i * information i j * t j) / 2)))) ∧
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.sin (∑ k, t k * crCentralSequence (C := N) P0 m A O k.1)
            ∂(crObservedLaw (C := N) P0 (counts N) m)) atTop (nhds 0)) ∧
      (∀ t : ActiveIndex A → ℝ,
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.cos (∑ k, t k * (Real.sqrt N *
            ((calibratedEstimator (C := N) O m A).2 k - exactSliceWelfare P0 m k.1)))
            ∂(crObservedLaw (C := N)
              (leastFavourablePath P0 A m hFull (Real.sqrt N)⁻¹) (counts N) m)) atTop
          (nhds (Real.exp (-((∑ i, ∑ j, t i * covariance i j * t j) / 2)) *
            Real.cos (∑ i, t i * h i))) ∧
        Tendsto (fun N => ∫ O : Fin N → Record K n,
          Real.sin (∑ k, t k * (Real.sqrt N *
            ((calibratedEstimator (C := N) O m A).2 k - exactSliceWelfare P0 m k.1)))
            ∂(crObservedLaw (C := N)
              (leastFavourablePath P0 A m hFull (Real.sqrt N)⁻¹) (counts N) m)) atTop
          (nhds (Real.exp (-((∑ i, ∑ j, t i * covariance i j * t j) / 2)) *
            Real.sin (∑ i, t i * h i)))) ∧
      ∀ c : Fin C, ∀ k ∈ A,
        Integrable (fun O => crTargetScore P0 m A k (O c)) (crObservedLaw P0 (counts C) m)) ∧
    (∀ delta : ∀ N, (Fin N → Record K n) → Fin K → ℝ,
      (∀ N, RandomizedRule (delta N)) →
      gaussianCompactValueReal A (fun k => sliceVariance P0 (m k)) alpha M ≤
        Filter.liminf (fun (N : ℕ) => sSup {risk : ℝ | ∃ h : ActiveIndex A → ℝ,
          quotientNorm A (extendActive A h) ≤ M ∧ risk = Real.sqrt N *
            ∫ O, ∑ a, delta N O a * simpleRegret A
              (exactSliceWelfare (leastFavourablePath P0 A m (extendActive A h)
                (Real.sqrt N)⁻¹) m) a
              ∂(crObservedLaw
                (leastFavourablePath P0 A m (extendActive A h) (Real.sqrt N)⁻¹)
                  (counts N) m)}) atTop) ∧
    Tendsto (fun N : ℕ => gaussianCompactValue A
      (fun k => sliceVariance P0 (m k)) alpha N) atTop
      (nhds (gaussianGlobalValue A (fun k => sliceVariance P0 (m k)) alpha)) ∧
    ∃ witnessP : Measure (Schedule n), witnessP = independentHalfTargetBitLaw n ∧
      WellFormedScheduleLaw witnessP ∧
      ∀ k ∈ A, sliceVariance witnessP (m k) = 1 / 4 ∧
        alpha k / sliceVariance witnessP (m k) = 4 * alpha k := by sorry
-- @realizes I_{CR}(diag(alpha_k/tau_k²))
-- @realizes \Sigma_{CR,A}(diag(tau_k²/alpha_k) on A)

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
