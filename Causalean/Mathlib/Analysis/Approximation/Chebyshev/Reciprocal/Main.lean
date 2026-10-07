module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.AlternationLower
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.ResidualOscillation

/-!
# Exact best uniform approximation of the reciprocal function

For every positive real interval and every natural degree bound, this module
identifies the best uniform polynomial approximation error for `x ↦ x⁻¹`.
The formula follows from an explicit Chebyshev polynomial, its sharp bound,
and alternating equality points.  It also gives the interval `[1,K²]` formula
used in finite moment duality.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- A [positive lower endpoint](hyp:a,ha), [strictly larger upper endpoint](hyp:b,hab), and [degree
bound m](hyp:m) imply [that the explicit reciprocal approximating polynomial approximates the
function 1 / z uniformly on the interval within the reciprocal approximation error](goal). -/
theorem reciprocalApproxPoly_upper {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    uniformApproxError (fun z : ℝ => z⁻¹) a b (reciprocalApproxPoly a b m) ≤
      reciprocalError a b m := by
  -- Combine `reciprocalApproxPoly_residual`, `reciprocalResidualPoly_bound`,
  -- `reciprocalResidualPoly_at_shape`, and `intervalSupNorm_le_iff`.
  have hcontinuous : ContinuousOn
      (fun z : ℝ => z⁻¹ - (reciprocalApproxPoly a b m).eval z)
      (Set.Icc a b) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.inv₀ continuousOn_id
      intro z hz
      exact ne_of_gt (lt_of_lt_of_le ha hz.1)
    · exact (reciprocalApproxPoly a b m).continuous.continuousOn
  change intervalSupNorm
    (fun z : ℝ => z⁻¹ - (reciprocalApproxPoly a b m).eval z) a b ≤ _
  apply (intervalSupNorm_le_iff hcontinuous hab.le).2
  intro z hz
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hd : 0 < b - a := sub_pos.mpr hab
  have hv : 1 < intervalShape a b := intervalShape_gt_one ha hab
  have hs : 0 < intervalShape a b ^ 2 - 1 := by nlinarith
  have hρ : 0 < intervalDecay a b := (intervalDecay_mem_Ioo ha hab).1
  have hRpos : 0 < (reciprocalResidualPoly a b m).eval (intervalShape a b) := by
    rw [reciprocalResidualPoly_at_shape ha hab]
    exact div_pos (by positivity) (pow_pos hρ m)
  have hden : 0 < z * (reciprocalResidualPoly a b m).eval (intervalShape a b) :=
    mul_pos hzpos hRpos
  rw [reciprocalApproxPoly_residual ha hab (ne_of_gt hzpos) m, abs_div,
    abs_of_pos hden]
  have hnum := reciprocalResidualPoly_bound ha hab hz m
  have hnum' : |(reciprocalResidualPoly a b m).eval
      (intervalShape a b - 2 * z / (b - a))| ≤ 4 * z / (b - a) := by
    convert hnum using 1
    ring
  calc
    |(reciprocalResidualPoly a b m).eval
        (intervalShape a b - 2 * z / (b - a))| /
        (z * (reciprocalResidualPoly a b m).eval (intervalShape a b)) ≤
        (4 * z / (b - a)) /
        (z * (reciprocalResidualPoly a b m).eval (intervalShape a b)) :=
      div_le_div_of_nonneg_right hnum' hden.le
    _ = reciprocalError a b m := by
      rw [reciprocalResidualPoly_at_shape ha hab]
      unfold reciprocalError
      field_simp [ne_of_gt hzpos, ne_of_gt hd, ne_of_gt hs, ne_of_gt hρ]
      ring

/-- A [positive lower endpoint](hyp:a,ha), [strictly larger upper
endpoint](hyp:b,hab), and [degree bound](hyp:m) imply [the existence of
ordered points with alternating residual values for the explicit reciprocal
approximant](goal). -/
theorem reciprocalApproxPoly_alternates {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    ∃ nodes : Fin (m + 2) → ℝ,
      StrictMono nodes ∧
      (∀ i, nodes i ∈ Set.Icc a b) ∧
      (∀ i,
        (nodes i)⁻¹ - (reciprocalApproxPoly a b m).eval (nodes i) =
          (-1 : ℝ) ^ (i : ℕ) * reciprocalError a b m) := by
  -- Apply `reciprocalResidualPoly_alternating_nodes`, then simplify using
  -- `reciprocalApproxPoly_residual` and the value of `R(v)`.
  obtain ⟨nodes, hmono, hmem, halt⟩ :=
    reciprocalResidualPoly_alternating_nodes ha hab m
  refine ⟨nodes, hmono, hmem, ?_⟩
  intro i
  have hzpos : 0 < nodes i := lt_of_lt_of_le ha (hmem i).1
  have hd : 0 < b - a := sub_pos.mpr hab
  have hv : 1 < intervalShape a b := intervalShape_gt_one ha hab
  have hs : 0 < intervalShape a b ^ 2 - 1 := by nlinarith
  have hρ : 0 < intervalDecay a b := (intervalDecay_mem_Ioo ha hab).1
  rw [reciprocalApproxPoly_residual ha hab (ne_of_gt hzpos) m, halt i,
    reciprocalResidualPoly_at_shape ha hab]
  unfold reciprocalError
  field_simp [ne_of_gt hzpos, ne_of_gt hd, ne_of_gt hs, ne_of_gt hρ]
  ring

/-- A [positive lower endpoint](hyp:a,ha), [strictly larger upper endpoint](hyp:b,hab), and [degree
bound m](hyp:m) imply [that the best uniform error in approximating 1 / z on the interval by
polynomials of degree at most m equals exactly 2 ρ^m divided by (b − a)(v² − 1), where v = (a + b)
/ (b − a) and ρ = v minus the square root of v² − 1](goal). -/
theorem bestUniformApproxError_reciprocal {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    bestUniformApproxError (fun z : ℝ => z⁻¹) a b m =
      (let v := (a + b) / (b - a)
       let ρ := v - Real.sqrt (v ^ 2 - 1)
       2 * ρ ^ m / ((b - a) * (v ^ 2 - 1))) := by
  have hf : ContinuousOn (fun z : ℝ => z⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro z hz
    exact ne_of_gt (lt_of_lt_of_le ha hz.1)
  have hres : ContinuousOn
      (fun z : ℝ => z⁻¹ - (reciprocalApproxPoly a b m).eval z)
      (Set.Icc a b) := hf.sub (reciprocalApproxPoly a b m).continuous.continuousOn
  have hbound : ∀ z ∈ Set.Icc a b,
      |z⁻¹ - (reciprocalApproxPoly a b m).eval z| ≤ reciprocalError a b m :=
    (intervalSupNorm_le_iff hres hab.le).mp (reciprocalApproxPoly_upper ha hab m)
  obtain ⟨nodes, hmono, hmem, halt⟩ :=
    reciprocalApproxPoly_alternates ha hab m
  have hbest := (alternatingResidual_certifiesBest hab hf
    (le_of_lt (reciprocalError_pos ha hab m))
    (reciprocalApproxPoly a b m) (reciprocalApproxPoly_degree_le m)
    hbound nodes hmono hmem halt).2
  exact hbest

/-- For a [natural number K at least two](hyp:K,hK), [the best uniform error in approximating
1 / z on the interval from one to K² by polynomials of degree at most K equals (K² − 1) / (2 K²)
times the K-th power of (K − 1) / (K + 1)](goal). -/
theorem bestUniformApproxError_reciprocal_one_sq
    (K : ℕ) (hK : 2 ≤ K) :
    bestUniformApproxError (fun z : ℝ => z⁻¹) 1 ((K : ℝ) ^ 2) K =
      (((K : ℝ) ^ 2 - 1) / (2 * (K : ℝ) ^ 2)) *
        (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K := by
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hbound : (1 : ℝ) < (K : ℝ) ^ 2 := by nlinarith
  rw [bestUniformApproxError_reciprocal (by norm_num) hbound K]
  change reciprocalError 1 ((K : ℝ) ^ 2) K = _
  exact reciprocalError_one_sq K hK

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
