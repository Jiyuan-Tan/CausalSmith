import Causalean.Graph.FiniteDensity.Positive.FiniteWitness
import Causalean.Mathlib.Analysis.LogRatioStability

/-!
# Examples for positive-mechanism stratum openness

This module exercises the two reusable APIs on a binary two-node DAG and on the scalar pair
`q(x) = exp(x)`, `p(x) = 1` over the unit interval.
-/

open Set

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean
open Causalean.Mathlib.Analysis

/-- The two-node DAG has the single directed edge `0 → 1`. -/
def binaryEdgeDAG : DAG (Fin 2) where
  edge i j := i = 0 ∧ j = 1
  decEdge := inferInstance
  acyclic := by
    apply DAG.acyclic_of_topoOrder (r := (· < ·)) (τ := fun i : Fin 2 ↦ i.val)
    rintro u v ⟨rfl, rfl⟩
    norm_num

/-- The binary example has a fair root and a child which matches its parent with probability
three quarters. -/
def binaryMechanism : PositiveFiniteDAGMechanism binaryEdgeDAG (fun _ : Fin 2 ↦ Bool) where
  factor i x := if i = 0 then (1 / 2 : ℝ)
    else if x 1 = x 0 then (3 / 4 : ℝ) else (1 / 4 : ℝ)
  factor_pos := by
    intro i x
    split_ifs <;> norm_num
  factor_normalized := by
    intro i x
    fin_cases i
    · simp
    · cases h : x 0 <;> simp [h] <;> norm_num
  factor_local := by
    intro i x y hxy
    fin_cases i
    · simp
    · have h0 : x 0 = y 0 := hxy 0 (by
        simp [binaryEdgeDAG, DAG.mem_parents])
      have h1 : x 1 = y 1 := hxy 1 (by simp)
      simp [h0, h1]

/-- In the binary mechanism, the unique edge is not conditionally independent given its empty
set of other parents, as certified by an explicit nonzero local contrast. -/
example :
    ¬ binaryMechanism.CondIndepCoordinates 1 0 ((binaryEdgeDAG.parents 1).erase 0) := by
  apply PositiveFiniteDAGMechanism.EdgeWitness.not_condIndep binaryMechanism
    (i := 1) (j := 0)
  · exact ⟨rfl, rfl⟩
  · refine
      { base := fun _ ↦ false
        child₀ := false
        child₁ := true
        parent₀ := false
        parent₁ := true
        nonzero := ?_ }
    norm_num [PositiveFiniteDAGMechanism.localContrast, binaryMechanism,
      Function.update]

/-- The log ratio of `exp` to the constant-one function has a uniformly positive within-derivative
on the unit interval, so all sufficiently small uniform `C¹` perturbations preserve its sign. -/
example : ∃ ε > 0, ∀ q' p' : ℝ → ℝ,
    DifferentiableOn ℝ q' (Icc 0 1) → DifferentiableOn ℝ p' (Icc 0 1) →
    C1CloseOn (Icc 0 1) ε q' Real.exp →
    C1CloseOn (Icc 0 1) ε p' (fun _ ↦ 1) →
    ∀ x ∈ Icc 0 1, 0 < q' x ∧ 0 < p' x ∧
      0 < derivWithin (logRatio q' p') (Icc 0 1) x := by
  have hq : ContDiffOn ℝ 1 Real.exp (Icc 0 1) := Real.contDiff_exp.contDiffOn
  have hp : ContDiffOn ℝ 1 (fun _ : ℝ ↦ (1 : ℝ)) (Icc 0 1) :=
    contDiff_const.contDiffOn
  have hqlower : ∀ x ∈ Icc (0 : ℝ) 1, (1 : ℝ) ≤ Real.exp x := by
    intro x hx
    exact Real.one_le_exp hx.1
  have hplower : ∀ x ∈ Icc (0 : ℝ) 1, (1 : ℝ) ≤ (fun _ : ℝ ↦ (1 : ℝ)) x := by
    simp
  have hfixed : ∀ x ∈ Icc (0 : ℝ) 1,
      (1 : ℝ) ≤ 1 * derivWithin (logRatio Real.exp (fun _ ↦ 1)) (Icc 0 1) x := by
    intro x hx
    rw [one_mul, derivWithin_logRatio (by norm_num)
      (hq.differentiableOn (by norm_num))
      (hp.differentiableOn (by norm_num))
      (fun y _ ↦ Real.exp_pos y) (fun _ _ ↦ zero_lt_one) hx]
    have hexp : derivWithin Real.exp (Icc 0 1) x = Real.exp x :=
      (Real.hasDerivAt_exp x).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hx)
    rw [hexp]
    simp [Real.exp_ne_zero]
  simpa only [one_mul] using
    (logRatioDerivative_fixedSign_open_C1 (a := 0) (b := 1)
      (m := 1) (margin := 1) (q := Real.exp) (p := fun _ ↦ 1) (sign := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hp hqlower hplower
      (Or.inl rfl) hfixed)

end Causalean.Graph.FiniteDensity
