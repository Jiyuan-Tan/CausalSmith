import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.PermutationFibers

/-!
Exact finite-sum regrouping from the labeled experiment to the response-type
orbit experiment.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ} (c : Contrast ℝ K)

/-- [The labeled contrast target depends only on response-type counts.](goal) -/
lemma tauC_eq_tauCount_scheduleCounts (z : Schedule K n) :
    tauC c z = tauCount c (scheduleCounts z) := by
  unfold tauC tauCount
  congr 1
  rw [← Fintype.sum_fiberwise z (fun i => ∑ a, c a * if z i a then 1 else 0)]
  apply Finset.sum_congr rfl
  intro t _
  have hterm (i : {i : Unit n // z i = t}) :
      (∑ a, c a * if z i.1 a then 1 else 0) =
        ∑ a, c a * if t a then 1 else 0 := by
    rw [i.2]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  norm_cast
  rw [Fintype.card_subtype]
  rfl

/-- [the labeled design realizes the orbit design](hyp:hdesign), [the labeled estimator realizes the orbit estimator](hyp:hest), [Exact risk equality once a labeled procedure has the stated orbitwise design masses and estimator values.](goal) -/
lemma labeledRisk_eq_orbitRisk_of_realizes
    (p : Procedure K n c) (q : OrbitProcedure K n c)
    (hdesign : ∀ A, p.1.p A =
      q.1.p (assignmentCounts A) / allocationOrbitCard (assignmentCounts A))
    (hest : ∀ A y, (p.2 A y : ℝ) =
      (q.2 (assignmentCounts A) (observedCounts A y) : ℝ))
    (z : Schedule K n) :
    labeledRisk c p z = orbitRisk c q (scheduleCounts z) := by
  classical
  unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    Causalean.Experimentation.DesignBased.FiniteDesign.E orbitRisk
  rw [tauC_eq_tauCount_scheduleCounts]
  rw [← Fintype.sum_fiberwise assignmentCounts (fun A =>
    p.1.p A * ((p.2 A (obsOutcome z A) : ℝ) - tauCount c (scheduleCounts z)) ^ 2)]
  apply Finset.sum_congr rfl
  intro r _
  let F : ObsVec r → ℝ := fun x =>
    ((q.2 r x : ℝ) - tauCount c (scheduleCounts z)) ^ 2
  calc
    ∑ A : {A : Assign K n // assignmentCounts A = r},
        p.1.p A.1 * ((p.2 A.1 (obsOutcome z A.1) : ℝ) -
          tauCount c (scheduleCounts z)) ^ 2 =
      ∑ A : {A : Assign K n // assignmentCounts A = r},
        (q.1.p r / allocationOrbitCard r) * F (observedVecFor z r A) := by
          apply Finset.sum_congr rfl
          intro A _
          rcases A with ⟨A, hA⟩
          subst r
          rw [hdesign, hest]
          rfl
    _ = (q.1.p r / allocationOrbitCard r) *
        ∑ A : {A : Assign K n // assignmentCounts A = r},
          F (observedVecFor z r A) := by rw [Finset.mul_sum]
    _ = (q.1.p r / allocationOrbitCard r) *
        ∑ x : ObsVec r,
          Fintype.card (LabeledObservationAssignments z r x) * F x := by
          rw [sum_allocationFiber_by_observed]
    _ = q.1.p r * ∑ x : ObsVec r,
        (orbitLik (scheduleCounts z) r x : ℝ) * F x := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [← labeledObservation_card_ratio_eq_orbitLik_real z r x]
          ring

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
