module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridStability
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.InterventionMoments
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.ModelRegularity
public import Causalean.Mathlib.Probability.FiniteMarkovPerturbation
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Finite stable-grid approximation

Round the four-state initial distribution, transition rows, and reward vector
onto the rational simplex grid and mix with the uniform reset kernel.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
open Causalean.Mathlib.Probability.FiniteMarkovPerturbation

/-- Simplex rounding supplies an enumerated stable candidate with the telescoping error. [Under the listed formal conditions](hyp:hM,hα,hp,hP,hr,hc), [the stated conclusion holds](goal).-/
-- @node: grid_candidate_moment_approximation
lemma grid_candidate_moment_approximation {M : Nat} (hM : 0 < M)
    {alpha : ℝ} (hα : 0 < alpha) (p r : Fin 4 → ℝ)
    (P : Matrix (Fin 4) (Fin 4) ℝ) (hp : IsProbabilityVector p)
    (hP : IsStochasticMatrix P) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hc : ContractsL1 P alpha) :
    ∃ c ∈ gridCandidates M alpha, ∀ k : Nat,
      |(∑ i, (Matrix.vecMul p (P ^ k)) i * r i) -
        ∑ i, (Matrix.vecMul (gridNu c) ((stabilizedGridMatrix alpha c) ^ k)) i *
          gridReward c i| ≤ (4 + (k : ℝ) * (3 + 6 / alpha)) / M := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨nu, hnu, hnuerr⟩ := simplex_grid_rounding hM p hp
  have hrows : ∀ i, ∃ u ∈ simplexGrid M,
      (1 / 2 : ℝ) * ∑ j, |P i j - (u j).val / (M : ℝ)| ≤ 3 / M := by
    intro i
    exact simplex_grid_rounding hM (P i) ⟨hP.1 i, hP.2 i⟩
  choose R hR hRerr using hrows
  have hrew : ∀ i, ∃ u : Fin (M + 1),
      0 ≤ r i - (u.val : ℝ) / M ∧ r i - (u.val : ℝ) / M ≤ (M : ℝ)⁻¹ := by
    intro i
    exact reward_grid_rounding hM (hr i)
  choose rr hrr using hrew
  let c : GridCode M := (nu, R, rr)
  have hdecoded : IsStochasticMatrix (gridR c) := by
    constructor
    · intro i j; exact div_nonneg (Nat.cast_nonneg _) hMr.le
    · intro i
      have hsum : (∑ j : Fin 4, ((R i j).val : ℝ)) = M := by
        exact_mod_cast (Finset.mem_filter.mp (hR i)).2
      change (∑ j : Fin 4, ((R i j).val : ℝ) / M) = 1
      rw [← Finset.sum_div, hsum, div_self hMr.ne']
  have hν : IsProbabilityVector (gridNu c) := by
    constructor
    · intro i; exact div_nonneg (Nat.cast_nonneg _) hMr.le
    · have hsum : (∑ i : Fin 4, ((nu i).val : ℝ)) = M := by
        exact_mod_cast (Finset.mem_filter.mp hnu).2
      change (∑ i : Fin 4, ((nu i).val : ℝ) / M) = 1
      rw [← Finset.sum_div, hsum, div_self hMr.ne']
  have hmem : c ∈ gridCandidates M alpha := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      refine ⟨nu, hnu, Finset.mem_biUnion.mpr ⟨R, ?_, ?_⟩⟩
      · apply Finset.mem_image.mpr
        refine ⟨fun i _ => R i, ?_, rfl⟩
        exact Finset.mem_pi.mpr (fun i _ => hR i)
      · exact Finset.mem_image.mpr ⟨rr, Finset.mem_univ _, rfl⟩
    · have hh := gridDobrushin_perturbation P (gridR c) hRerr
      have hd := contractsL1_gridDobrushin P hα.le hc
      linear_combination hh + hd
  have hstable := stabilizedGridMatrix_row_error hM hα c hdecoded
  have htransition (i : Fin 4) : (1 / 2 : ℝ) * ∑ j,
      |P i j - stabilizedGridMatrix alpha c i j| ≤ (3 + 6 / alpha) / M := by
    have htri := row_tv_triangle (P i) (gridR c i) (stabilizedGridMatrix alpha c i)
    have hh := add_le_add (hRerr i) (hstable.2 i)
    calc
      _ ≤ 3 / (M : ℝ) + 6 / (alpha * M) := htri.trans hh
      _ = _ := by ring
  have hreward (i : Fin 4) : |r i - gridReward c i| ≤ (M : ℝ)⁻¹ := by
    exact (abs_of_nonneg (hrr i).1).le.trans (hrr i).2
  refine ⟨c, hmem, ?_⟩
  intro k
  have hh := stochastic_moment_error hP hstable.1 hp hν hr hnuerr htransition hreward k
  calc
    _ ≤ 3 / (M : ℝ) + (k : ℝ) * ((3 + 6 / alpha) / M) + (M : ℝ)⁻¹ := hh
    _ = _ := by ring

/-- A finite relabeling preserves matrix-power moments. [the stated conclusion holds](goal).-/
-- @node: matrix_moment_relabel
lemma matrix_moment_relabel {S U : Type*} [Fintype S] [Fintype U]
    [DecidableEq S] [DecidableEq U] (e : U ≃ S) (p r : S → ℝ)
    (P : Matrix S S ℝ) (k : Nat) :
    (∑ i : U, (Matrix.vecMul (p ∘ e)
      ((Matrix.of fun i j => P (e i) (e j)) ^ k)) i * r (e i)) =
    ∑ i : S, (Matrix.vecMul p (P ^ k)) i * r i := by
  have hpow : ((Matrix.of fun i j => P (e i) (e j)) ^ k) =
      fun i j => (P ^ k) (e i) (e j) := by
    exact ((Matrix.reindexRingEquiv ℝ e.symm).map_pow P k).symm
  rw [hpow]
  have hvec (i : U) : Matrix.vecMul (p ∘ e)
      (fun i j => (P ^ k) (e i) (e j)) i = Matrix.vecMul p (P ^ k) (e i) := by
    exact e.sum_comp (fun j => p j * (P ^ k) j (e i))
  simp_rw [hvec]
  exact e.sum_comp (fun i => (Matrix.vecMul p (P ^ k)) i * r i)

/-- Relabeling a finite state space preserves contraction of probability vectors. [Under the listed formal conditions](hyp:hc), [the stated conclusion holds](goal).-/
-- @node: contractsL1_relabel
lemma contractsL1_relabel {S U : Type*} [Fintype S] [Fintype U]
    (e : U ≃ S) (P : Matrix S S ℝ) {alpha : ℝ} (hc : ContractsL1 P alpha) :
    ContractsL1 (Matrix.of fun i j => P (e i) (e j)) alpha := by
  intro p q hp hq
  have hprob (v : U → ℝ) (hv : IsProbabilityVector v) :
      IsProbabilityVector (v ∘ e.symm) :=
    ⟨fun i => hv.1 _, (e.symm.sum_comp v).trans hv.2⟩
  have hstep (v : U → ℝ) (i : U) :
      markovStep (v ∘ e.symm) P (e i) =
        markovStep v (Matrix.of fun i j => P (e i) (e j)) i := by
    symm
    simpa only [markovStep, Matrix.vecMul, dotProduct, Function.comp_apply,
      Equiv.symm_apply_apply, Matrix.of_apply] using
      e.sum_comp (fun j => v (e.symm j) * P j (e i))
  have hdist (v w : U → ℝ) : l1Distance (v ∘ e.symm) (w ∘ e.symm) =
      l1Distance v w := e.symm.sum_comp (fun i => |v i - w i|)
  have hh := hc (p ∘ e.symm) (q ∘ e.symm) (hprob p hp) (hprob q hq)
  rw [hdist] at hh
  have hl : l1Distance (markovStep (p ∘ e.symm) P) (markovStep (q ∘ e.symm) P) =
      l1Distance (markovStep p (Matrix.of fun i j => P (e i) (e j)))
        (markovStep q (Matrix.of fun i j => P (e i) (e j))) := by
    unfold l1Distance
    rw [← e.sum_comp (fun i => |markovStep (p ∘ e.symm) P i -
      markovStep (q ∘ e.symm) P i|)]
    simp_rw [hstep]
  rw [hl] at hh
  exact hh

/-- A stable grid candidate approximates all seven target-policy moments. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: grid_approximation
lemma grid_approximation {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) :
    ∃ c ∈ gridCandidates (gridSize T (mixingAlpha t0)) (mixingAlpha t0),
      ∀ k : Fin 7,
        |(∑ s, (Matrix.vecMul (stationaryLaw (policyKernel M M.b))
            (fourMatrixPower (Matrix.of (policyKernel M M.e)) k.val)) s *
            rewardRegression M s) -
          (∑ s : Fin 4,
            (Matrix.vecMul (gridNu c)
              ((stabilizedGridMatrix (mixingAlpha t0) c) ^ k.val)) s *
              gridReward c s)| ≤ (T : ℝ)⁻¹ := by
  classical
  let alpha := mixingAlpha t0
  let N := gridSize T alpha
  let e : Fin 4 ≃ JointState 2 2 := (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm
  let d := stationaryLaw (policyKernel M M.b)
  let r := rewardRegression M
  let P : FourMatrix := Matrix.of (policyKernel M M.e)
  let R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => P (e i) (e j)
  have hα : 0 < alpha := Real.exp_pos _
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hN : 0 < N := by
    apply Nat.ceil_pos.mpr
    change 0 < (22 + 36 / alpha) * T
    positivity
  have hd : IsProbabilityVector d := hM.stationary_start.1.1
  have hde : IsProbabilityVector (d ∘ e) :=
    ⟨fun i => hd.1 _, (e.sum_comp d).trans hd.2⟩
  have hP := policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.e hM.policy_overlap.1
  have hR : IsStochasticMatrix R := by
    refine ⟨fun i j => hP.1 _ _, ?_⟩
    intro i
    exact (e.sum_comp (fun j => P (e i) j)).trans (hP.2 (e i))
  have hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1 :=
    rewardRegression_unit M hM.pomdp_kernel hM.policy_overlap.1
  have hc : ContractsL1 R alpha := contractsL1_relabel e P hM.target_contraction
  obtain ⟨c, hc, herr⟩ := grid_candidate_moment_approximation hN hα (d ∘ e) (r ∘ e)
    R hde hR (fun i => hr (e i)) hc
  refine ⟨c, hc, ?_⟩
  intro k
  have hmoment := matrix_moment_relabel e d r P k.val
  have hh := herr k.val
  change |(∑ i, (Matrix.vecMul (d ∘ e) (R ^ k.val)) i * r (e i)) - _| ≤ _ at hh
  rw [hmoment] at hh
  change |(∑ s, (Matrix.vecMul d (P ^ k.val)) s * r s) - _| ≤ _
  apply hh.trans
  have hk : (k.val : ℝ) ≤ 6 := by exact_mod_cast (show k.val ≤ 6 by omega)
  have hcoef : 4 + (k.val : ℝ) * (3 + 6 / alpha) ≤ 22 + 36 / alpha := by
    have h := mul_le_mul_of_nonneg_right hk
      (by positivity : 0 ≤ 3 + 6 / alpha)
    linear_combination h
  have hceil : (22 + 36 / alpha) * T ≤ (N : ℝ) := Nat.le_ceil _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (4 + (k.val : ℝ) * (3 + 6 / alpha)) / N ≤ (22 + 36 / alpha) / N :=
      div_le_div_of_nonneg_right hcoef hNr.le
    _ ≤ (T : ℝ)⁻¹ := by
      rw [← one_div]
      apply (div_le_div_iff₀ hNr hTr).mpr
      simpa using hceil

end CausalSmith.Stat.PomdpBinaryhiddenRate
