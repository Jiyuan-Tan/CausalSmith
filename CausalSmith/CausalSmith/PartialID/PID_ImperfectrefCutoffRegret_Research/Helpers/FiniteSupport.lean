import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Measure.Dirac
import Causalean.Mathlib.MeasureTheory.FiniteAtomicMeasure

/-! Finite ordered score support and prefix-mass coordinates. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

-- @node: ass:finite-score-support
def FiniteScoreSupport (M : ImperfectReferenceModel) (m : ℕ)
    (x : Fin m → ℝ) : Prop :=
  StrictMono x ∧ (scoreMarginal M).support = Set.range x
  -- @realizes \(P_S\)(finite support enumerated by the ordered x_j)

-- @env: S2
structure FiniteScoreModel where
  toModel : ImperfectReferenceModel
  m : ℕ -- @realizes \(m\)(number of score values)
  x : Fin m → ℝ -- @realizes \(x_j\)(ordered real score values)
  support : FiniteScoreSupport toModel m x

noncomputable def cellMass (F : FiniteScoreModel) (r : Bool)
    (j : Fin F.m) : ℝ :=
  stratumMass F.toModel r (singletonBorel (F.x j))
  -- @realizes \(w_{rj}\)(μ_r singleton mass)

noncomputable def prefixMass (F : FiniteScoreModel) (r : Bool)
    (j : ℕ) : ℝ :=
  ∑ k : Fin F.m, if (k : ℕ) < j then cellMass F r k else 0
  -- @realizes \(A_r(j)\)(sum of cells strictly before j; A_r(0)=0)

lemma cellMass_mem_Icc (F : FiniteScoreModel) (r : Bool) (j : Fin F.m) :
    cellMass F r j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact measureReal_nonneg
  · calc
      cellMass F r j ≤ (obsMeasure F.toModel r).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = obsMass F.toModel r := rfl
      _ ≤ 1 := (obsMass_mem_Icc F.toModel r).2
  -- @realizes \(w_{rj}\)(probability-cell range [0,1])

lemma prefixMass_mem_Icc (F : FiniteScoreModel) (r : Bool) (j : ℕ)
    (hj : j ≤ F.m) : prefixMass F r j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simp only [prefixMass]
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact (cellMass_mem_Icc F r k).1
    · positivity
  · have hsum := sum_measureReal_le_measureReal_univ
      (μ := obsMeasure F.toModel r) (s := (Finset.univ : Finset (Fin F.m)))
      (t := fun k => if (k : ℕ) < j then {F.x k} else ∅)
      (by
        intro k hk
        by_cases hkj : (k : ℕ) < j <;> simp [hkj])
      (by
        intro k hk l hl hkl
        change Disjoint (if (k : ℕ) < j then {F.x k} else ∅)
          (if (l : ℕ) < j then {F.x l} else ∅)
        by_cases hkj : (k : ℕ) < j
        · rw [if_pos hkj]
          by_cases hlj : (l : ℕ) < j
          · rw [if_pos hlj, Set.disjoint_left]
            intro z hzk hzl
            simp only [Set.mem_singleton_iff] at hzk hzl
            exact hkl (F.support.1.injective (hzk.symm.trans hzl))
          · rw [if_neg hlj]
            simp
        · rw [if_neg hkj]
          exact Set.empty_disjoint _)
    calc
      prefixMass F r j ≤ (obsMeasure F.toModel r).real Set.univ := by
        simpa [prefixMass, cellMass, stratumMass, singletonBorel, apply_ite] using hsum
      _ = obsMass F.toModel r := rfl
      _ ≤ 1 := (obsMass_mem_Icc F.toModel r).2
  -- @realizes \(A_r(j)\)(probability-prefix range [0,1])

def inducedPolicyIndex (F : FiniteScoreModel) (t : EReal) : ℕ :=
  (Finset.univ.filter (fun j : Fin F.m => (F.x j : EReal) < t)).card

noncomputable def policyIndices (F : FiniteScoreModel) : List ℕ :=
  by
    classical
    exact (List.range (F.m + 1)).filter
      (fun j => decide (∃ t ∈ F.toModel.T, inducedPolicyIndex F t = j))
      -- @realizes \(K_{\mathcal T}\)(ordered induced policy-index set)

lemma prefix_interval_mass (F : FiniteScoreModel) (r : Bool)
    {i j : ℕ} (hij : i ≤ j) :
    prefixMass F r j - prefixMass F r i =
      ∑ k : Fin F.m, if i ≤ (k : ℕ) ∧ (k : ℕ) < j then cellMass F r k else 0 := by
  simp only [prefixMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hki : (k : ℕ) < i
  · have hkj : (k : ℕ) < j := lt_of_lt_of_le hki hij
    simp [hki, hkj]
  · by_cases hkj : (k : ℕ) < j
    · have hik : i ≤ (k : ℕ) := Nat.le_of_not_gt hki
      simp [hki, hkj, hik]
    · simp [hki, hkj]

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
