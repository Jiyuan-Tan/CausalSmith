module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Multiindex

/-!
# Sorted coordinate words and prefix intervals

The sorted list of repeated coordinates identifies each word position with
the half-open interval between consecutive cumulative coordinate counts.
This purely combinatorial bridge permits identification with prefix-based
coordinate partial definitions, independently of the Taylor conversion.
-/

public section

open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a vector of coordinate counts](hyp:κ), [a position r in its sorted word](hyp:r), and [a
coordinate i](hyp:i), [the sorted word has coordinate i at position r exactly when r is at least
the sum of the counts of the coordinates before i and strictly less than that sum plus the count of
i](goal). -/
theorem sortedWord_eq_iff_prefix {d : ℕ} (κ : Fin d → ℕ)
    (r : Fin (multiOrder κ)) (i : Fin d) :
    sortedWord κ r = i ↔
      (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) ≤ r.val ∧
        r.val < (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) + κ i := by
  classical
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    let κ' : Fin d → ℕ := fun j => κ j.succ
    have horder : multiOrder κ = κ 0 + multiOrder κ' := by
      exact Fin.sum_univ_succ κ
    have hlist : countList κ =
        List.replicate (κ 0) 0 ++ (countList κ').map Fin.succ := by
      simp only [countList, List.ofFn_succ, List.flatten_cons,
        List.map_flatten, List.map_ofFn]
      simp [κ', Function.comp_def]
    have hprefix (j : Fin d) :
        (∑ k ∈ Finset.univ.filter (fun k => k < j.succ), κ k) =
          κ 0 + ∑ k ∈ Finset.univ.filter (fun k => k < j), κ' k := by
      simp only [Finset.sum_filter]
      rw [Fin.sum_univ_succ]
      simp [κ', Fin.succ_lt_succ_iff]
    by_cases hr : r.val < κ 0
    · have hword : sortedWord κ r = 0 := by
        simp only [sortedWord, List.get_eq_getElem]
        simp only [hlist]
        rw [List.getElem_append_left (by simpa using hr)]
        exact List.getElem_replicate _
      rw [hword]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hr]
      · rw [hprefix]
        have hne : (0 : Fin (d + 1)) ≠ j.succ := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_succ] at this
          omega
        simp only [hne, false_iff]
        omega
    · have htail : r.val - κ 0 < multiOrder κ' := by
        have := r.isLt
        simp only [horder] at this
        omega
      let r' : Fin (multiOrder κ') := ⟨r.val - κ 0, htail⟩
      have hword : sortedWord κ r = (sortedWord κ' r').succ := by
        simp only [sortedWord, List.get_eq_getElem]
        simp only [hlist]
        rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hr)]
        simp only [List.length_replicate, List.getElem_map]
        rfl
      rw [hword]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hr]
      · rw [Fin.succ_inj, ih κ' r' j, hprefix]
        change
          ((∑ k ∈ Finset.univ.filter (fun k => k < j), κ' k) ≤ r.val - κ 0 ∧
            r.val - κ 0 < (∑ k ∈ Finset.univ.filter (fun k => k < j), κ' k) + κ' j) ↔
          (κ 0 + (∑ k ∈ Finset.univ.filter (fun k => k < j), κ' k) ≤ r.val ∧
            r.val < κ 0 + (∑ k ∈ Finset.univ.filter (fun k => k < j), κ' k) + κ' j)
        omega

/-- For [a vector of coordinate counts](hyp:κ) and [a position r in its sorted word](hyp:r), [the
unit vector of the coordinate at position r equals the sum over coordinates i of the unit vector of
i whenever r is at least the sum of the counts before i and strictly less than that sum plus the
count of i, and zero otherwise](goal). -/
theorem sorted_coordinate_directions_eq_prefix {d : ℕ} (κ : Fin d → ℕ)
    (r : Fin (multiOrder κ)) :
    EuclideanSpace.single (sortedWord κ r) (1 : ℝ) =
      ∑ i, if (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) ≤ r.val ∧
        r.val < (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) + κ i
      then EuclideanSpace.single i (1 : ℝ) else 0 := by
  classical
  symm
  rw [Finset.sum_eq_single (sortedWord κ r)]
  · rw [if_pos ((sortedWord_eq_iff_prefix κ r _).mp rfl)]
  · intro i _ hi
    rw [if_neg (fun h => hi ((sortedWord_eq_iff_prefix κ r i).mpr h).symm)]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

