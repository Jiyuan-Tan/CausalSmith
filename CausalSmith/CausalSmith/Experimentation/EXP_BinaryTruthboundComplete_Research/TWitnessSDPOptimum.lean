import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.WitnessData
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- [The witness variance matrix](goal) is the six-by-six covariance matrix of the concrete witness experiment. -/
noncomputable def witnessAMatrix : Matrix (Fin 6) (Fin 6) ℝ := fun i k =>
  varianceMatrix witnessExperiment (wcoord i) (wcoord k)

/-- A [six-by-six matrix](hyp:H) is [witness-HMS feasible](goal) when it [is symmetric](step:1), [dominates the witness variance matrix in positive-semidefinite order](step:2), and has zero entries at coordinate pairs [zero–three](step:3), [zero–four](step:4), [one–four](step:5), [two–three](step:6), [two–four](step:7), and [four–five](step:8). -/
def witnessHMSFeasible (H : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  H.IsSymm ∧ (H - witnessAMatrix).PosSemidef ∧
  H 0 3 = 0 ∧ H 0 4 = 0 ∧ H 1 4 = 0 ∧
  H 2 3 = 0 ∧ H 2 4 = 0 ∧ H 4 5 = 0

/-- For [a six-by-six matrix](hyp:H), [the witness HMS objective](goal) is its homogeneous quadratic form averaged uniformly over the binary witness cube. -/
noncomputable def witnessHMSObjective (H : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  (1 / 64 : ℝ) * ∑ θ : Theta witnessExperiment,
    ∑ i : Fin 6, ∑ k : Fin 6,
      H i k * ((θ (wcoord i) : ℕ) : ℝ) * ((θ (wcoord k) : ℕ) : ℝ)

/-- For [two witness coordinates](hyp:i,k), [the sum of their binary products over the full six-dimensional cube is 32 on the diagonal and 16 off the diagonal](goal). -/
-- @node: witness_bitMoment
lemma witness_bitMoment (i k : Fin 6) :
    (∑ θ : (Fin 6 → Fin 2), ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)) =
      if i = k then 32 else 16 := by
  have h : (∑ θ : (Fin 6 → Fin 2), (θ i : ℕ) * (θ k : ℕ)) =
      if i = k then 32 else 16 := by native_decide +revert
  exact_mod_cast h

/-- For [a six-by-six matrix](hyp:H), [the witness HMS objective is the entrywise sum with diagonal weight one half and off-diagonal weight one quarter](goal). -/
-- @node: witnessHMSObjective_eq_moment
lemma witnessHMSObjective_eq_moment (H : Matrix (Fin 6) (Fin 6) ℝ) :
    witnessHMSObjective H =
      ∑ i : Fin 6, ∑ k : Fin 6, (if i = k then (1 / 2 : ℝ) else 1 / 4) * H i k := by
  unfold witnessHMSObjective
  rw [show (∑ θ : Theta witnessExperiment,
      ∑ i : Fin 6, ∑ k : Fin 6,
        H i k * ((θ (wcoord i) : ℕ) : ℝ) * ((θ (wcoord k) : ℕ) : ℝ)) =
      ∑ i : Fin 6, ∑ k : Fin 6, H i k *
        ∑ θ : (Fin 6 → Fin 2), ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ) by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    have hi : wcoord i = i := by apply Fin.ext; rfl
    have hk : wcoord k = k := by apply Fin.ext; rfl
    rw [hi, hk]
    ring]
  simp_rw [witness_bitMoment]
  rw [show (1 / 64 : ℝ) * ∑ i : Fin 6, ∑ k : Fin 6,
      H i k * (if i = k then 32 else 16) =
      ∑ i : Fin 6, ∑ k : Fin 6,
        (1 / 64 : ℝ) * (H i k * (if i = k then 32 else 16)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  split <;> ring

/-- [The witness variance matrix is symmetric](goal). -/
-- @node: witnessAMatrix_isSymm
lemma witnessAMatrix_isSymm : witnessAMatrix.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i k
  unfold witnessAMatrix varianceMatrix targetCoeff
  congr 1
  · apply Finset.sum_congr rfl
    intro z _
    ring
  · ring

/-- For [a concrete witness coordinate](hyp:i), [its cast into the witness setup equals the original coordinate](goal). -/
-- @node: wcoord_eq_self
lemma wcoord_eq_self (i : Fin 6) : wcoord i = i := by apply Fin.ext; rfl

/-- For [two witness coordinates](hyp:i,k), [the corresponding witness variance-matrix entry equals the uniform second moment of their scores minus the product of their uniform means](goal). -/
-- @node: witnessAMatrix_apply
lemma witnessAMatrix_apply (i k : Fin 6) :
    witnessAMatrix i k =
      (∑ z : Fin 3, (1 / 3 : ℝ) * (witnessV z i * witnessV z k)) -
      (∑ z : Fin 3, (1 / 3 : ℝ) * witnessV z i) *
        (∑ z : Fin 3, (1 / 3 : ℝ) * witnessV z k) := by
  rfl

/-- [The HMS objective of the witness variance matrix equals 11/9](goal). -/
-- @node: witnessAObjective
lemma witnessAObjective : witnessHMSObjective witnessAMatrix = 11 / 9 := by
  rw [witnessHMSObjective_eq_moment]
  simp only [Fin.sum_univ_six]
  simp_rw [witnessAMatrix_apply]
  simp_rw [Fin.sum_univ_three]
  norm_num [witnessV, Fin.ext_iff]

/-- For [a six-by-six matrix](hyp:H) satisfying [the witness HMS feasibility constraints](hyp:hH), [its witness HMS objective is at least 7/6 plus the square root of 17 divided by 9](goal). -/
-- @node: witnessHMS_lower
lemma witnessHMS_lower (H : Matrix (Fin 6) (Fin 6) ℝ) (hH : witnessHMSFeasible H) :
    7 / 6 + Real.sqrt 17 / 9 ≤ witnessHMSObjective H := by
  let ρ : ℝ := Real.sqrt 17
  let M : Matrix (Fin 6) (Fin 6) ℝ := H - witnessAMatrix
  let L : Matrix (Fin 6) (Fin 6) ℝ := fun i l =>
    match i.1, l.1 with
    | 0, 0 => 1
    | 1, 0 => 1/2 | 1, 1 => 1
    | 2, 0 => 1/2 | 2, 1 => 1/3 | 2, 2 => 1
    | 3, 1 => 2/3 | 3, 2 => (-5+3*ρ)/8 | 3, 3 => 1
    | 4, 0 => -ρ/34 | 4, 1 => -ρ/17 | 4, 2 => 3*ρ/17
    | 4, 3 => 1+3*ρ/17 | 4, 4 => 1
    | 5, 0 => 1/2 | 5, 1 => 1/3 | 5, 2 => 1/4
    | 5, 3 => (3+ρ)/4 | 5, 4 => ρ/4 | 5, 5 => 1
    | _, _ => 0
  let d : Fin 6 → ℝ := fun l =>
    match l.1 with
    | 0 => 1/2 | 1 => 3/8 | 2 => 1/3
    | 3 => (5*ρ-19)/32 | 4 => (9-ρ)/34 | _ => 0
  let quad (N : Matrix (Fin 6) (Fin 6) ℝ) (x : Fin 6 → ℝ) : ℝ :=
    ∑ i, x i * ∑ k, N i k * x k
  have hsq : ρ ^ 2 = 17 := by
    dsimp [ρ]
    exact Real.sq_sqrt (by norm_num)
  have hrho : 0 ≤ ρ := Real.sqrt_nonneg 17
  have hd : ∀ l, 0 ≤ d l := by
    intro l
    fin_cases l <;> simp [d] <;> try norm_num
    · nlinarith
    · nlinarith
  have hpsd : M.PosSemidef := hH.2.1
  have hquad : ∀ l, 0 ≤ quad M (fun i => L i l) := by
    intro l
    simpa [quad, dotProduct, Matrix.mulVec] using
      hpsd.dotProduct_mulVec_nonneg (fun i => L i l)
  have hweighted : 0 ≤ ∑ l, d l * quad M (fun i => L i l) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hd l) (hquad l)
  have hsym : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp hpsd.1
  have hm03 : M 0 3 = 0 := by
    dsimp [M]
    rw [hH.2.2.1]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hm04 : M 0 4 = 2/9 := by
    dsimp [M]
    rw [hH.2.2.2.1]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hm14 : M 1 4 = 1/3 := by
    dsimp [M]
    rw [hH.2.2.2.2.1]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hm23 : M 2 3 = 0 := by
    dsimp [M]
    rw [hH.2.2.2.2.2.1]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hm24 : M 2 4 = -2/9 := by
    dsimp [M]
    rw [hH.2.2.2.2.2.2.1]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hm45 : M 4 5 = -4/9 := by
    dsimp [M]
    rw [hH.2.2.2.2.2.2.2]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV]
  have hid : witnessHMSObjective M =
      (∑ l, d l * quad M (fun i => L i l)) +
      2 * ((1/4+ρ/68) * M 0 4 + (1/4+ρ/34) * M 1 4 +
        (1/4-3*ρ/68) * M 2 4 + (1/4-5*ρ/68) * M 4 5) := by
    rw [witnessHMSObjective_eq_moment]
    simp only [Fin.sum_univ_six]
    simp only [hsym.apply 0 1, hsym.apply 0 2, hsym.apply 0 4,
      hsym.apply 0 5, hsym.apply 1 2, hsym.apply 1 3, hsym.apply 1 4,
      hsym.apply 1 5, hsym.apply 2 3, hsym.apply 2 4, hsym.apply 2 5,
      hsym.apply 3 4, hsym.apply 3 5, hsym.apply 4 5]
    simp only [hm23]
    simp only [quad]
    simp_rw [Fin.sum_univ_six]
    simp [L, d, ρ]
    simp only [hsym.apply 0 1, hsym.apply 0 2, hsym.apply 0 3, hsym.apply 0 4,
      hsym.apply 0 5, hsym.apply 1 2, hsym.apply 1 3, hsym.apply 1 4,
      hsym.apply 1 5, hsym.apply 2 3, hsym.apply 2 4, hsym.apply 2 5,
      hsym.apply 3 4, hsym.apply 3 5, hsym.apply 4 5]
    simp only [hm03, hm23]
    have hsqrt2 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hsqrt3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by
      calc
        Real.sqrt 17 ^ 3 = Real.sqrt 17 ^ 2 * Real.sqrt 17 := by ring
        _ = 17 * Real.sqrt 17 := by rw [hsqrt2]
    ring_nf
    rw [hsqrt2, hsqrt3]
    ring
  have hfixed : 2 * ((1/4+ρ/68) * M 0 4 + (1/4+ρ/34) * M 1 4 +
        (1/4-3*ρ/68) * M 2 4 + (1/4-5*ρ/68) * M 4 5) =
      (2*ρ-1)/18 := by
    rw [hm04, hm14, hm24, hm45]
    ring
  have hobjM : (2*ρ-1)/18 ≤ witnessHMSObjective M := by
    rw [hid, hfixed]
    linarith
  have hlin : witnessHMSObjective H =
      witnessHMSObjective witnessAMatrix + witnessHMSObjective M := by
    dsimp [M]
    unfold witnessHMSObjective
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hlin, witnessAObjective]
  dsimp [ρ] at hobjM
  linarith

/-- [A witness-HMS feasible matrix attains objective value 7/6 plus the square root of 17 divided by 9](goal). -/
-- @node: witnessHMS_attains
lemma witnessHMS_attains : ∃ H, witnessHMSFeasible H ∧
    witnessHMSObjective H = 7 / 6 + Real.sqrt 17 / 9 := by
  let ρ : ℝ := Real.sqrt 17
  let w : Fin 6 → ℝ := fun i =>
    match i.1 with
    | 0 => 1 | 1 => 3/2 | 2 => -1 | 3 => 0 | 4 => ρ/2 | _ => -2
  let M : Matrix (Fin 6) (Fin 6) ℝ := fun i k => 4/(9*ρ) * w i * w k
  let H : Matrix (Fin 6) (Fin 6) ℝ := witnessAMatrix + M
  have hsq : ρ ^ 2 = 17 := by
    dsimp [ρ]
    exact Real.sq_sqrt (by norm_num)
  have hrhopos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hrhone : ρ ≠ 0 := ne_of_gt hrhopos
  have hMpsd : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.isHermitian_iff_isSymm.mpr
      apply Matrix.IsSymm.ext
      intro i k
      simp [M]
      ring
    · intro x
      simp only [dotProduct, Matrix.mulVec, star_id_of_comm]
      simp_rw [Fin.sum_univ_six]
      simp [M, w]
      have hc : 0 ≤ 4 / (9 * ρ) := by positivity
      nlinarith [sq_nonneg (x 0 + (3/2)*x 1 - x 2 + (ρ/2)*x 4 - 2*x 5)]
  have hHsym : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i k
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_isSymm.apply i k]
    simp [M]
    ring
  have hdiff : H - witnessAMatrix = M := by
    ext i k
    simp [H]
  have hzero03 : H 0 3 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
  have hzero04 : H 0 4 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
    field_simp [hrhone]
    norm_num
  have hzero14 : H 1 4 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
    field_simp [hrhone]
    norm_num
  have hzero23 : H 2 3 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
  have hzero24 : H 2 4 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
    field_simp [hrhone]
    norm_num
  have hzero45 : H 4 5 = 0 := by
    simp only [H, Matrix.add_apply]
    rw [witnessAMatrix_apply]
    simp only [Fin.sum_univ_three]
    norm_num [witnessV, M, w]
    field_simp [hrhone]
    norm_num
  refine ⟨H, ⟨hHsym, ?_, hzero03, hzero04, hzero14, hzero23, hzero24, hzero45⟩, ?_⟩
  · rw [hdiff]
    exact hMpsd
  · rw [show witnessHMSObjective H = witnessHMSObjective witnessAMatrix +
        witnessHMSObjective M by
      unfold witnessHMSObjective
      simp only [H, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      ring]
    rw [witnessAObjective, witnessHMSObjective_eq_moment]
    simp only [Fin.sum_univ_six]
    simp [M, w]
    field_simp [hrhone]
    nlinarith [hsq]

/-- [The witness HMS semidefinite optimum is 7/6 plus the square root of 17 divided by 9, this value is attained, and its exact gaps above the unrestricted and degree-two witness values are respectively `(8√17−23)/72` and `(4√17−13)/36`](goal). -/
-- @node: prop:witness-hms-sdp-optimum
theorem witness_hms_sdp_optimum :
    sInf (witnessHMSObjective '' {H | witnessHMSFeasible H}) = 7 / 6 + Real.sqrt 17 / 9 ∧
    (∃ H, witnessHMSFeasible H ∧ witnessHMSObjective H = 7 / 6 + Real.sqrt 17 / 9) ∧
    (7 / 6 + Real.sqrt 17 / 9) - 107 / 72 = (8 * Real.sqrt 17 - 23) / 72 ∧
    (7 / 6 + Real.sqrt 17 / 9) - 55 / 36 = (4 * Real.sqrt 17 - 13) / 36 := by
  obtain ⟨Hstar, hfeas, hobj⟩ := witnessHMS_attains
  have hbdd : BddBelow (witnessHMSObjective '' {H | witnessHMSFeasible H}) := by
    refine ⟨7 / 6 + Real.sqrt 17 / 9, ?_⟩
    rintro _ ⟨H, hH, rfl⟩
    exact witnessHMS_lower H hH
  refine ⟨le_antisymm (csInf_le hbdd ⟨Hstar, hfeas, hobj⟩) ?_,
    ⟨⟨Hstar, hfeas, hobj⟩, ?_⟩⟩
  · apply le_csInf
    · exact ⟨witnessHMSObjective Hstar, Hstar, hfeas, rfl⟩
    rintro _ ⟨H, hH, rfl⟩
    exact witnessHMS_lower H hH
  · constructor <;> ring

end CausalSmith.Experimentation.BinaryTruthbound
