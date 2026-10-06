module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionClosedExterior

/-!
# Geometry of the closed one-face reflection collar

The cube and its closed exterior slab are the two closed pieces used to glue
one-face reflection. Their union is the collar and their overlap is the face.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

private theorem leftClosedExteriorCollar_eq_pi (d m : ℕ) (i : Fin d) :
    leftClosedExteriorCollar d m i =
      Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [leftClosedExteriorCollar, leftCubeCollar, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_univ_pi]
  constructor
  · rintro ⟨hx, hxi⟩ j
    by_cases h : j = i
    · subst j
      have hi := hx i
      simp only [↓reduceIte, Set.mem_Icc] at hi ⊢
      exact ⟨hi.1, hxi⟩
    · simpa [h] using hx j
  · intro hx
    constructor
    · intro j
      by_cases h : j = i
      · subst j
        have hj := hx i
        simp only [↓reduceIte, Set.mem_Icc] at hj ⊢
        exact ⟨hj.1, le_trans hj.2 (by norm_num)⟩
      · simpa [h] using hx j
    · have hj := hx i
      simp only [↓reduceIte, Set.mem_Icc] at hj
      simpa using hj.2

/-- [The closure of the open exterior collar at the left face in coordinate i is
the closed exterior slab](goal), including the face itself and all remaining
coordinate edges. -/
theorem closure_leftOpenCubeCollar (d m : ℕ) (i : Fin d) :
    closure (leftOpenCubeCollar d m i) =
      leftClosedExteriorCollar d m i := by
  have hopen : leftOpenCubeCollar d m i =
      Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) := by
    ext x
    simp only [leftOpenCubeCollar, Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor <;> intro hx j <;> by_cases hj : j = i <;>
      simpa [hj] using hx j
  rw [hopen, leftClosedExteriorCollar_eq_pi, closure_pi_set]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp only [↓reduceIte]
    rw [closure_Ioo]
    have hpos : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith
  · simp [h, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

/-- [The closed exterior slab of a one-face cube collar is a closed set](goal). -/
theorem isClosed_leftClosedExteriorCollar (d m : ℕ) (i : Fin d) :
    IsClosed (leftClosedExteriorCollar d m i) := by
  rw [leftClosedExteriorCollar_eq_pi]
  apply isClosed_set_pi
  intro j hj
  split_ifs <;> exact isClosed_Icc

/-- [A one-face cube collar is a closed set](goal). -/
theorem isClosed_leftCubeCollar (d m : ℕ) (i : Fin d) :
    IsClosed (leftCubeCollar d m i) := by
  have hpi : leftCubeCollar d m i =
      Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1
        else Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [leftCubeCollar, Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor <;> intro hx j <;> specialize hx j <;>
      split_ifs at hx ⊢ <;> exact hx
  rw [hpi]
  apply isClosed_set_pi
  intro j hj
  split_ifs <;> exact isClosed_Icc

/-- [The closed exterior slab of a one-face cube collar has unique within-set
derivatives at every point](goal). -/
theorem uniqueDiffOn_leftClosedExteriorCollar (d m : ℕ) (i : Fin d) :
    UniqueDiffOn ℝ (leftClosedExteriorCollar d m i) := by
  rw [leftClosedExteriorCollar_eq_pi]
  apply UniqueDiffOn.pi
  intro j hj
  split_ifs
  · apply uniqueDiffOn_Icc
    have hpos : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith
  · exact uniqueDiffOn_Icc (by norm_num)

/-- [The closed one-face cube collar has unique within-set derivatives at every
point](goal). -/
theorem uniqueDiffOn_leftCubeCollar (d m : ℕ) (i : Fin d) :
    UniqueDiffOn ℝ (leftCubeCollar d m i) := by
  have hpi : leftCubeCollar d m i =
      Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1
        else Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [leftCubeCollar, Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor <;> intro hx j <;> specialize hx j <;>
      split_ifs at hx ⊢ <;> exact hx
  rw [hpi]
  apply UniqueDiffOn.pi
  intro j hj
  split_ifs
  · apply uniqueDiffOn_Icc
    have hpos : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith
  · exact uniqueDiffOn_Icc (by norm_num)

/-- [The closed exterior slab and the normalized cube together make up the whole
closed one-face collar](goal). -/
theorem leftClosedExteriorCollar_union_cube (d m : ℕ) (i : Fin d) :
    leftClosedExteriorCollar d m i ∪ cube d = leftCubeCollar d m i := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact hx.1
    · intro j
      by_cases h : j = i
      · subst j
        simp only [↓reduceIte, Set.mem_Icc]
        have hi := hx i
        have hnonneg : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
        exact ⟨by linarith [hi.1], hi.2⟩
      · simpa [leftCubeCollar, h] using hx j
  · intro hx
    by_cases hxi : x i ≤ -1
    · exact Or.inl ⟨hx, hxi⟩
    · right
      intro j
      by_cases h : j = i
      · subst j
        have hi := hx i
        simp only [↓reduceIte, Set.mem_Icc] at hi
        exact ⟨le_of_not_ge hxi, hi.2⟩
      · simpa [leftCubeCollar, h] using hx j

/-- [The closed exterior slab and the normalized cube overlap exactly in the
selected left face, the set of cube points whose i-th coordinate equals
−1](goal), edges and corners included. -/
theorem leftClosedExteriorCollar_inter_cube (d m : ℕ) (i : Fin d) :
    leftClosedExteriorCollar d m i ∩ cube d =
      {x ∈ cube d | x i = -1} := by
  ext x
  constructor
  · rintro ⟨⟨hc, hle⟩, hx⟩
    exact ⟨hx, le_antisymm hle (hx i).1⟩
  · rintro ⟨hx, hxi⟩
    refine ⟨⟨?_, hxi.le⟩, hx⟩
    intro j
    by_cases h : j = i
    · subst j
      simp only [↓reduceIte, Set.mem_Icc]
      have hnonneg : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      constructor
      · linarith
      · exact (hx i).2
    · simpa [leftCubeCollar, h] using hx j

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
