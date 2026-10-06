module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridFit

/-!
# Stationary value transfer for the selected grid

Relabeling the four grid coordinates puts the selected realization on the
joint-state carrier. The pair-polynomial modulus then gives equation (16).
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- The initial coordinates of an admissible positive-resolution code sum to one. [Under the listed formal conditions](hyp:hN,hc), [the stated conclusion holds](goal).-/
-- @node: gridNu_probability
lemma gridNu_probability {N : Nat} (hN : 0 < N) {a : ℝ} {c : GridCode N}
    (hc : c ∈ gridCandidates N a) : IsProbabilityVector (gridNu c) := by
  classical
  obtain ⟨nu, hnu, R, hR, r, hr, heq⟩ := by
    simpa only [gridCandidateUniverse, Finset.mem_biUnion, Finset.mem_image]
      using (Finset.mem_filter.mp hc).1
  cases heq
  constructor
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [gridNu, ← Finset.sum_div]
    have hsum : (∑ i : Fin 4, ((nu i).val : ℝ)) = N := by
      exact_mod_cast (Finset.mem_filter.mp hnu).2
    rw [hsum, div_self (by positivity : (N : ℝ) ≠ 0)]

/-- The candidate filter and reset mixture enforce the specified contraction radius. [Under the listed formal conditions](hyp:hN,ha,hc), [the stated conclusion holds](goal).-/
-- @node: stabilizedGridMatrix_dobrushin_le
lemma stabilizedGridMatrix_dobrushin_le {N : Nat} (hN : 0 < N)
    {a : ℝ} (ha : 0 < a) {c : GridCode N} (hc : c ∈ gridCandidates N a) :
    gridDobrushin (stabilizedGridMatrix a c) ≤ a := by
  let lam := a / (a + 6 / (N : ℝ))
  have hden : 0 < a + 6 / (N : ℝ) := by positivity
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hf := (Finset.mem_filter.mp hc).2
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hij : (1 / 2 : ℝ) * ∑ s, |gridR c i s - gridR c j s| ≤
      gridDobrushin (gridR c) :=
    (le_ciSup (f := fun j : Fin 4 => (1 / 2 : ℝ) * ∑ s,
      |gridR c i s - gridR c j s|) (Set.finite_range _).bddAbove j).trans
      (le_ciSup (f := fun i : Fin 4 => ⨆ j : Fin 4,
        (1 / 2 : ℝ) * ∑ s, |gridR c i s - gridR c j s|)
        (Set.finite_range _).bddAbove i)
  calc
    _ = lam * ((1 / 2 : ℝ) * ∑ s, |gridR c i s - gridR c j s|) := by
      have he (s : Fin 4) : stabilizedGridMatrix a c i s -
          stabilizedGridMatrix a c j s = lam * (gridR c i s - gridR c j s) := by
        dsimp [stabilizedGridMatrix, lam]; ring
      simp_rw [he, abs_mul, abs_of_nonneg hlam]
      rw [← Finset.mul_sum]
      ring
    _ ≤ lam * (a + 6 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (hij.trans hf) hlam
    _ = a := div_mul_cancel₀ a hden.ne'

/-- Relabeling the grid coordinates allows direct use of the joint-state value modulus. [Under the listed formal conditions](hyp:hN,ha,ha1,hc,hP,hnu,hpi,hr,hd), [the stated conclusion holds](goal).-/
-- @node: grid_value_modulus
lemma grid_value_modulus {N : Nat} (hN : 0 < N) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) {c : GridCode N} (hc : c ∈ gridCandidates N a)
    (P : FourMatrix) (nu pi r : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hnu : IsProbabilityVector nu)
    (hpi : IsStationary P pi) (hr : ∀ s, r s ∈ Set.Icc (0 : ℝ) 1)
    (hd : dobrushin P ≤ a) :
    |(∑ i : Fin 4, stationaryLaw (stabilizedGridMatrix a c) i * gridReward c i) -
      matrixValue pi r| ≤ stabilityFactor a *
      (⨆ k : Fin 7, |gridCodeMoment a c k.val - matrixMoment nu P r k.val|) := by
  let e : JointState 2 2 ≃ Fin 4 := finProdFinEquiv
  let G := stabilizedGridMatrix a c
  let Q : FourMatrix := Matrix.of fun i j => G (e i) (e j)
  let d := stationaryLaw G
  have hs := stabilizedGridMatrix_stationary hN ha hc
  have hg := (stabilizedGridMatrix_row_error hN ha c (gridR_stochastic hN hc)).1
  have hQ : IsStochasticMatrix Q := by
    refine ⟨fun i j => hg.1 _ _, ?_⟩
    intro i
    exact (e.sum_comp (fun j => G (e i) j)).trans (hg.2 _)
  have hprob (v : Fin 4 → ℝ) (hv : IsProbabilityVector v) :
      IsProbabilityVector (v ∘ e) :=
    ⟨fun i => hv.1 _, (e.sum_comp v).trans hv.2⟩
  have hstat : IsStationary Q (d ∘ e) := by
    refine ⟨hprob d hs.1, ?_⟩
    funext i
    change (∑ j, d (e j) * G (e j) (e i)) = d (e i)
    exact (e.sum_comp (fun j => d j * G j (e i))).trans (congrFun hs.2 (e i))
  have hreward : ∀ i, gridReward c i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    apply (div_le_one (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
    exact_mod_cast (Nat.le_of_lt_succ (c.2.2 i).isLt)
  have hdelta : dobrushin Q ≤ a := by
    apply ciSup_le
    intro i
    apply ciSup_le
    intro j
    change (1 / 2 : ℝ) * ∑ s, |G (e i) (e s) - G (e j) (e s)| ≤ a
    rw [e.sum_comp (fun s => |G (e i) s - G (e j) s|)]
    exact ((le_ciSup (f := fun j : Fin 4 => (1 / 2 : ℝ) * ∑ s,
      |G (e i) s - G j s|) (Set.finite_range _).bddAbove (e j)).trans
      (le_ciSup (f := fun i : Fin 4 => ⨆ j : Fin 4,
        (1 / 2 : ℝ) * ∑ s, |G i s - G j s|)
        (Set.finite_range _).bddAbove (e i))).trans
      (stabilizedGridMatrix_dobrushin_le hN ha hc)
  have hh := (pairPolynomial_value_modulus Q P (gridNu c ∘ e) nu (d ∘ e) pi
    (gridReward c ∘ e) r a ha ha1 hQ hP
    (hprob _ (gridNu_probability hN hc)) hnu hstat hpi
    (fun i => hreward (e i)) hr hdelta hd).2.2.2
  have hvalue : matrixValue (d ∘ e) (gridReward c ∘ e) =
      ∑ i : Fin 4, d i * gridReward c i := by
    exact e.sum_comp (fun i => d i * gridReward c i)
  have hm (k : Nat) : matrixMoment (gridNu c ∘ e) Q (gridReward c ∘ e) k =
      gridCodeMoment a c k := matrix_moment_relabel e (gridNu c) (gridReward c) G k
  simpa only [hvalue, hm] using hh

/-- Equation (16): the selected stationary value inherits twice the empirical moment error. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: stableGridEstimator_value_error
lemma stableGridEstimator_value_error {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) (w : ObsView T 2) :
    |stableGridEstimator T t0 M.b M.e w - targetValue M| ≤
      stabilityFactor (mixingAlpha t0) *
        (2 * (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w -
          matrixMoment (stationaryLaw (policyKernel M M.b))
            (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val|) + (T : ℝ)⁻¹) := by
  let a := mixingAlpha t0
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by
    change mixingAlpha t0 < 1
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hN : 0 < gridSize T a := by
    apply Nat.ceil_pos.mpr
    have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    change 0 < (22 + 36 / a) * T
    positivity
  let e : Fin 4 ≃ JointState 2 2 := (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm
  have hd : dobrushin (Matrix.of (policyKernel M M.e)) ≤ a := by
    have hh := contractsL1_gridDobrushin
      (Matrix.of fun i j => policyKernel M M.e (e i) (e j)) ha.le
      (contractsL1_relabel e _ hM.target_contraction)
    apply ciSup_le
    intro i
    apply ciSup_le
    intro j
    have heq := e.sum_comp (fun s => |policyKernel M M.e i s - policyKernel M M.e j s|)
    change (1 / 2 : ℝ) * ∑ s, |policyKernel M M.e i s - policyKernel M M.e j s| ≤ a
    rw [← heq]
    have hij := ((le_ciSup (f := fun j : Fin 4 => (1 / 2 : ℝ) * ∑ s,
      |policyKernel M M.e (e (e.symm i)) (e s) - policyKernel M M.e (e j) (e s)|)
      (Set.finite_range _).bddAbove (e.symm j)).trans
      (le_ciSup (f := fun i : Fin 4 => ⨆ j : Fin 4, (1 / 2 : ℝ) * ∑ s,
        |policyKernel M M.e (e i) (e s) - policyKernel M M.e (e j) (e s)|)
        (Set.finite_range _).bddAbove (e.symm i))).trans hh
    simpa only [Equiv.apply_symm_apply] using hij
  have hh := grid_value_modulus hN ha ha1 (selectGridCode_mem a ha.le M.b M.e w)
    (Matrix.of (policyKernel M M.e)) _ _ _
    (policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.e hM.policy_overlap.1)
    hM.stationary_start.1.1 (targetStationary_of_class M hM)
    (rewardRegression_unit M hM.pomdp_kernel hM.policy_overlap.1) hd
  exact hh.trans (mul_le_mul_of_nonneg_left
    (selected_grid_intervention_moment_error hT M hM w)
    (by unfold stabilityFactor; positivity))

end CausalSmith.Stat.PomdpBinaryhiddenRate
