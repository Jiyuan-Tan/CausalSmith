module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridRounding
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridPerturbation

/-!
# Stability and error of rounded grid kernels

Row-wise rounding preserves the Dobrushin filter. Mixing with the uniform
kernel enforces contraction and costs at most 6/(alpha M) in row TV.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- Contraction of probability vectors bounds every pair of point-mass rows. [Under the listed formal conditions](hyp:hα,hc), [the stated conclusion holds](goal).-/
-- @node: contractsL1_gridDobrushin
lemma contractsL1_gridDobrushin (P : Matrix (Fin 4) (Fin 4) ℝ)
    {alpha : ℝ} (hα : 0 ≤ alpha) (hc : ContractsL1 P alpha) :
    gridDobrushin P ≤ alpha := by
  classical
  let d (i : Fin 4) : Fin 4 → ℝ := fun s => if s = i then 1 else 0
  have hd (i : Fin 4) : IsProbabilityVector (d i) := by
    constructor
    · intro s; dsimp [d]; split_ifs <;> norm_num
    · simp [d]
  have hstep (i : Fin 4) : markovStep (d i) P = P i := by
    ext s
    simp [markovStep, Matrix.vecMul, dotProduct, d]
  have hdist (i j : Fin 4) : l1Distance (d i) (d j) ≤ 2 := by
    unfold l1Distance
    calc
      _ ≤ ∑ s, (|d i s| + |d j s|) := Finset.sum_le_sum (fun s _ => abs_sub _ _)
      _ = 2 := by
        simp_rw [abs_of_nonneg ((hd i).1 _), abs_of_nonneg ((hd j).1 _)]
        rw [Finset.sum_add_distrib, (hd i).2, (hd j).2]
        norm_num
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hh := hc (d i) (d j) (hd i) (hd j)
  rw [hstep, hstep] at hh
  have he := mul_le_mul_of_nonneg_left (hdist i j) hα
  unfold l1Distance at hh he
  linarith

/-- TV obeys the triangle inequality between finite row vectors. [the stated conclusion holds](goal).-/
-- @node: row_tv_triangle
lemma row_tv_triangle {S : Type*} [Fintype S] (p q r : S → ℝ) :
    (1 / 2 : ℝ) * ∑ i, |p i - r i| ≤
      (1 / 2 : ℝ) * ∑ i, |p i - q i| + (1 / 2 : ℝ) * ∑ i, |q i - r i| := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => abs_sub_le (p i) (q i) (r i))
  rw [Finset.sum_add_distrib] at h
  linarith

/-- Row-wise TV approximation perturbs the Dobrushin coefficient by twice its error. [Under the listed formal conditions](hyp:hPR), [the stated conclusion holds](goal).-/
-- @node: gridDobrushin_perturbation
lemma gridDobrushin_perturbation (P R : Matrix (Fin 4) (Fin 4) ℝ) {ε : ℝ}
    (hPR : ∀ i, (1 / 2 : ℝ) * ∑ j, |P i j - R i j| ≤ ε) :
    gridDobrushin R ≤ gridDobrushin P + 2 * ε := by
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hij : (1 / 2 : ℝ) * ∑ s, |P i s - P j s| ≤ gridDobrushin P :=
    (le_ciSup (f := fun j : Fin 4 => (1 / 2 : ℝ) * ∑ s, |P i s - P j s|)
      (Set.finite_range _).bddAbove j).trans
      (le_ciSup (f := fun i : Fin 4 => ⨆ j : Fin 4,
        (1 / 2 : ℝ) * ∑ s, |P i s - P j s|) (Set.finite_range _).bddAbove i)
  have hi := hPR i
  have hj := hPR j
  have h1 := row_tv_triangle (R i) (P i) (R j)
  have h2 := row_tv_triangle (P i) (P j) (R j)
  have hsym : (∑ s, |R i s - P i s|) = ∑ s, |P i s - R i s| := by
    simp_rw [abs_sub_comm]
  rw [hsym] at h1
  linarith

/-- Uniform-reset stabilization preserves stochasticity and has the required row error. [Under the listed formal conditions](hyp:hM,hα,hR), [the stated conclusion holds](goal).-/
-- @node: stabilizedGridMatrix_row_error
lemma stabilizedGridMatrix_row_error {M : Nat} (hM : 0 < M)
    {alpha : ℝ} (hα : 0 < alpha) (c : GridCode M)
    (hR : IsStochasticMatrix (gridR c)) :
    IsStochasticMatrix (stabilizedGridMatrix alpha c) ∧
    ∀ i, (1 / 2 : ℝ) * ∑ j,
      |gridR c i j - stabilizedGridMatrix alpha c i j| ≤ 6 / (alpha * M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let lam := alpha / (alpha + 6 / (M : ℝ))
  have hden : 0 < alpha + 6 / (M : ℝ) := by positivity
  have hlam0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hlam1 : lam ≤ 1 := by
    exact (div_le_one hden).mpr (le_add_of_nonneg_right (by positivity))
  have hmass : 1 - lam ≤ 6 / (alpha * M) := by
    calc
      1 - lam = (6 / (M : ℝ)) / (alpha + 6 / (M : ℝ)) := by
        dsimp [lam]
        field_simp
        ring
      _ ≤ (6 / (M : ℝ)) / alpha := div_le_div_of_nonneg_left
        (by positivity) hα (le_add_of_nonneg_right (by positivity))
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · constructor
    · intro i j
      change 0 ≤ lam * gridR c i j + (1 - lam) / 4
      exact add_nonneg (mul_nonneg hlam0 (hR.1 i j)) (by positivity)
    · intro i
      change (∑ j : Fin 4, (lam * gridR c i j + (1 - lam) / 4)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hR.2 i]
      simp
      ring
  · intro i
    have hunit : IsProbabilityVector (fun _ : Fin 4 => (1 / 4 : ℝ)) :=
      ⟨by intro j; norm_num, by norm_num⟩
    have htv : (1 / 2 : ℝ) * ∑ j : Fin 4, |gridR c i j - 1 / 4| ≤ 1 := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => abs_sub (gridR c i j) (1 / 4))
      simp_rw [abs_of_nonneg (hR.1 i _)] at h
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
      rw [Finset.sum_add_distrib, hR.2 i] at h
      norm_num at h
      linarith
    calc
      _ = (1 - lam) * ((1 / 2 : ℝ) * ∑ j : Fin 4, |gridR c i j - 1 / 4|) := by
        change (1 / 2 : ℝ) * ∑ j : Fin 4,
          |gridR c i j - (lam * gridR c i j + (1 - lam) / 4)| = _
        have he (j : Fin 4) : gridR c i j - (lam * gridR c i j + (1 - lam) / 4) =
            (1 - lam) * (gridR c i j - 1 / 4) := by ring
        simp_rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlam1)]
        rw [← Finset.mul_sum]
        ring
      _ ≤ (1 - lam) * 1 := mul_le_mul_of_nonneg_left htv (sub_nonneg.mpr hlam1)
      _ ≤ _ := by simpa using hmass

end CausalSmith.Stat.PomdpBinaryhiddenRate
