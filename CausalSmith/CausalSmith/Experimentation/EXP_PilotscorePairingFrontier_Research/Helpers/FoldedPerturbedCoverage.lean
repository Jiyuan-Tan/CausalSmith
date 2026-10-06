module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCoverage

/-! # Coverage bound for the seven perturbed affine branches -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open scoped BigOperators Matrix

structure GridBranch where
  lower : ℝ
  upper : ℝ
  slope : ℝ
  domainLength : ℝ

noncomputable def gridBranchDensity {n : ℕ}
    (h : ℝ) (b : Fin n → GridBranch) (y : ℝ) : ℝ :=
  ∑ i, h / (b i).slope *
    ((gridIntervalIndices h (b i).lower (b i).upper y).card : ℝ)

lemma gridBranchDensity_error {n : ℕ} {h : ℝ} (hh : 0 < h)
    (b : Fin n → GridBranch)
    (hs : ∀ i, 0 < (b i).slope)
    (hr : ∀ i, 0 ≤ (b i).domainLength)
    (hlen : ∀ i, (b i).upper - (b i).lower =
      (b i).slope * (b i).domainLength) (y : ℝ) :
    |gridBranchDensity h b y - ∑ i, (b i).domainLength| ≤
      ∑ i, h / (b i).slope := by
  have hi (i : Fin n) :
      |h / (b i).slope *
          ((gridIntervalIndices h (b i).lower (b i).upper y).card : ℝ) -
        (b i).domainLength| ≤ h / (b i).slope :=
    weighted_gridIntervalIndices_error hh (hs i) (hr i) (hlen i)
  rw [gridBranchDensity, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hi i)

noncomputable def perturbedBranches (h a ε c : ℝ) : Fin 7 → GridBranch := ![
  ⟨0, h / 4 + a, h + 4 * a, 1 / 4⟩,
  ⟨13 * h / 32 + 3 * a / 8, h / 4 + a, 4 * a - h, 5 / 32⟩,
  ⟨7 * h / 16 + a / 4 + ε * a * c,
    13 * h / 32 + 3 * a / 8, 4 * a - h - 32 * ε * a * c, 1 / 32⟩,
  ⟨9 * h / 16 - a / 4 + ε * a * c,
    7 * h / 16 + a / 4 + ε * a * c, 4 * a - h, 1 / 8⟩,
  ⟨19 * h / 32 - 3 * a / 8,
    9 * h / 16 - a / 4 + ε * a * c, 4 * a - h + 32 * ε * a * c, 1 / 32⟩,
  ⟨3 * h / 4 - a, 19 * h / 32 - 3 * a / 8, 4 * a - h, 5 / 32⟩,
  ⟨3 * h / 4 - a, h, h + 4 * a, 1 / 4⟩]

noncomputable def periodicPerturbedDensity (h a ε c y : ℝ) : ℝ :=
  gridBranchDensity h (perturbedBranches h a ε c) y

-- keep: reusable uniform coverage bound for perturbed folded densities
lemma periodicPerturbedDensity_error {h a ε c y : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    |periodicPerturbedDensity h a ε c y - 1| ≤
      2 * (h / (h + 4 * a)) + 3 * (h / (4 * a - h)) +
        h / (4 * a - h - 32 * ε * a * c) +
        h / (4 * a - h + 32 * ε * a * c) := by
  have hsout : 0 < h + 4 * a := triangular_outer_slope_positive hh ha
  have hsmid : 0 < 4 * a - h := by
    have := triangular_middle_slope_negative hh hscale
    linarith
  have hsup : 0 < 4 * a - h - 32 * ε * a * c := by
    have := perturbed_ramp_up_slope_neg hh hscale hε hc
    linarith
  have hsdown : 0 < 4 * a - h + 32 * ε * a * c := by
    have := perturbed_ramp_down_slope_neg hh hscale hε0 hc.1
    linarith
  have hs (i : Fin 7) : 0 < (perturbedBranches h a ε c i).slope := by
    fin_cases i <;> simp [perturbedBranches, hsout, hsmid, hsup, hsdown]
  have hr (i : Fin 7) : 0 ≤ (perturbedBranches h a ε c i).domainLength := by
    fin_cases i <;> norm_num [perturbedBranches]
  have hlen (i : Fin 7) :
      (perturbedBranches h a ε c i).upper -
        (perturbedBranches h a ε c i).lower =
      (perturbedBranches h a ε c i).slope *
        (perturbedBranches h a ε c i).domainLength := by
    fin_cases i <;> simp [perturbedBranches] <;> ring
  have hbound := gridBranchDensity_error hh (perturbedBranches h a ε c)
    hs hr hlen y
  have hmass : (∑ i : Fin 7, (perturbedBranches h a ε c i).domainLength) = 1 := by
    norm_num [Fin.sum_univ_succ, perturbedBranches]
  have hslope : (∑ i : Fin 7, h / (perturbedBranches h a ε c i).slope) =
      2 * (h / (h + 4 * a)) + 3 * (h / (4 * a - h)) +
        h / (4 * a - h - 32 * ε * a * c) +
        h / (4 * a - h + 32 * ε * a * c) := by
    simp [Fin.sum_univ_succ, perturbedBranches]
    ring
  rw [hmass] at hbound
  rw [hslope] at hbound
  exact hbound

end CausalSmith.Experimentation.PilotscorePairingFrontier
