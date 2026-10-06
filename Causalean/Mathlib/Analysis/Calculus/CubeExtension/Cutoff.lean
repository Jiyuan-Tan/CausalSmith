module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Glue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Support

/-!
# The exact cubic-power coordinate cutoff

This file supplies the compactly supported scalar profile equal to
`(1-u^2)^3` on `|u| ≤ 1` and zero elsewhere, including both glued derivatives.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- At [a scalar input](hyp:u), [the cutoff](goal) is
[the exact cubic-power polynomial inside the unit interval and zero outside](step:1). -/
noncomputable def cutoff (u : ℝ) : ℝ :=
  if |u| ≤ 1 then (1 - u ^ 2) ^ 3 else 0

/-- At [a scalar input](hyp:u), [the explicit first jet](goal) is
[the polynomial derivative on the closed unit interval and zero outside](step:1). -/
noncomputable def cutoffD1 (u : ℝ) : ℝ :=
  if |u| ≤ 1 then -6 * u * (1 - u ^ 2) ^ 2 else 0

/-- At [a scalar input](hyp:u), [the explicit second jet](goal) is
[the second polynomial derivative on the closed unit interval and zero outside](step:1). -/
noncomputable def cutoffD2 (u : ℝ) : ℝ :=
  if |u| ≤ 1 then -6 * (1 - u ^ 2) ^ 2 + 24 * u ^ 2 * (1 - u ^ 2) else 0

/-- At [every real input](hyp:u), [the cubic-power branch has its exact first
derivative](goal), before it is glued to the zero branch. -/
theorem cutoff_polynomial_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v : ℝ => (1 - v ^ 2) ^ 3)
      (-6 * u * (1 - u ^ 2) ^ 2) u := by
  convert! (((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow 3)
    using 1 <;> (try simp) <;> ring

/-- At [every real input](hyp:u), [the first polynomial branch has its exact
second derivative](goal), before either branch is glued. -/
theorem cutoff_polynomialD1_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v : ℝ => -6 * v * (1 - v ^ 2) ^ 2)
      (-6 * (1 - u ^ 2) ^ 2 + 24 * u ^ 2 * (1 - u ^ 2)) u := by
  convert! (((hasDerivAt_id u).const_mul (-6)).mul
    (((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow 2))
    using 1 <;> (try simp) <;> ring

/-- [The cutoff takes value one at the origin](goal). -/
theorem cutoff_zero : cutoff 0 = 1 := by
  norm_num [cutoff]

/-- [The cutoff is even](goal) at [every input](hyp:u). -/
theorem cutoff_neg (u : ℝ) : cutoff (-u) = cutoff u := by
  simp [cutoff]

/-- [The cutoff lies between zero and one](goal) at [every scalar input](hyp:u). -/
theorem cutoff_bounds (u : ℝ) : 0 ≤ cutoff u ∧ cutoff u ≤ 1 := by
  by_cases hu : |u| ≤ 1
  · rw [cutoff, if_pos hu]
    have hnonneg : 0 ≤ 1 - u ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one u).2 hu)
    exact ⟨pow_nonneg hnonneg 3, pow_le_one₀ hnonneg (by nlinarith [sq_nonneg u])⟩
  · simp [cutoff, hu]

/-- [The nonzero support is exactly the open unit interval](goal). -/
theorem cutoff_support : Function.support cutoff = Set.Ioo (-1) 1 := by
  ext u
  change cutoff u ≠ 0 ↔ -1 < u ∧ u < 1
  rw [← abs_lt]
  constructor
  · intro h
    have hle : |u| ≤ 1 := by
      by_contra hn
      exact h (by simp [cutoff, hn])
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hsq : u ^ 2 = 1 := by nlinarith [sq_abs u]
    exact h (by simp [cutoff, hle, hsq])
  · intro h
    have hsq : u ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one u).2 h
    simp only [cutoff, if_pos h.le]
    exact pow_ne_zero 3 (ne_of_gt (sub_pos.mpr hsq))

/-- [The closed support is exactly the closed unit interval](goal). -/
theorem cutoff_tsupport : tsupport cutoff = Set.Icc (-1) 1 := by
  change closure (Function.support cutoff) = Set.Icc (-1) 1
  rw [cutoff_support, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

/-- [The cutoff has compact support](goal). -/
theorem cutoff_hasCompactSupport : HasCompactSupport cutoff := by
  change IsCompact (tsupport cutoff)
  rw [cutoff_tsupport]
  exact isCompact_Icc

/-- [A branch vanishing at the left endpoint](hyp:p,hleft) has
[the closed-interval cutoff represented by two nested joins](goal). -/
private theorem cutoff_branch_eq_join (p : ℝ → ℝ) (hleft : p (-1) = 0) :
    (fun u => if |u| ≤ 1 then p u else 0) =
      joinAt (-1) (fun _ => 0) (joinAt 1 p (fun _ => 0)) := by
  funext u
  by_cases hl : u ≤ -1
  · by_cases ha : |u| ≤ 1
    · have he : u = -1 := le_antisymm hl (abs_le.mp ha).1
      subst u
      simp [joinAt, hleft]
    · simp [joinAt, hl, ha]
  · by_cases hr : u ≤ 1
    · have ha : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hr⟩
      simp [joinAt, hl, hr, ha]
    · have ha : ¬ |u| ≤ 1 := fun h => hr (abs_le.mp h).2
      simp [joinAt, hl, hr, ha]

/-- [A polynomial branch and its derivative](hyp:p,dp,hp) whose
[endpoint values vanish](hyp:hl,hr,hdl,hdr) have
[the derivative obtained by cutting off both branches](goal) at [each input](hyp:u). -/
private theorem cutoff_branch_hasDerivAt (p dp : ℝ → ℝ)
    (hp : ∀ u, HasDerivAt p (dp u) u)
    (hl : p (-1) = 0) (hr : p 1 = 0)
    (hdl : dp (-1) = 0) (hdr : dp 1 = 0) (u : ℝ) :
    HasDerivAt (fun v => if |v| ≤ 1 then p v else 0)
      (if |u| ≤ 1 then dp u else 0) u := by
  change HasDerivAt (fun v => if |v| ≤ 1 then p v else 0)
    ((fun v => if |v| ≤ 1 then dp v else 0) u) u
  rw [cutoff_branch_eq_join p hl, cutoff_branch_eq_join dp hdl]
  exact joinAt_hasDerivAt (-1) (fun x => hasDerivAt_const x 0)
    (joinAt_hasDerivAt 1 hp (fun x => hasDerivAt_const x 0) hr hdr)
    (by norm_num [joinAt, hl]) (by norm_num [joinAt, hdl]) u

/-- [The cutoff has the stated first derivative](goal) at [every input](hyp:u),
including both glue points.

Express the cutoff as two `joinAt` operations at -1 and 1. The branch
polynomials have matching zero first jets at both junctions. Use
`joinAt (-1) (fun _ => 0) (joinAt 1 (fun v => (1-v^2)^3) (fun _ => 0))`;
its value at -1 is zero, so the closed-half-line convention agrees with cutoff.
The two polynomial derivative helpers above supply the branch derivatives. -/
theorem cutoff_hasDerivAt (u : ℝ) : HasDerivAt cutoff (cutoffD1 u) u := by
  exact cutoff_branch_hasDerivAt
    (fun v => (1 - v ^ 2) ^ 3) (fun v => -6 * v * (1 - v ^ 2) ^ 2)
    cutoff_polynomial_hasDerivAt (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u

/-- [The explicit first jet has the stated second derivative](goal) at
[every input](hyp:u), including both glue points. -/
theorem cutoffD1_hasDerivAt (u : ℝ) : HasDerivAt cutoffD1 (cutoffD2 u) u := by
  exact cutoff_branch_hasDerivAt
    (fun v => -6 * v * (1 - v ^ 2) ^ 2)
    (fun v => -6 * (1 - v ^ 2) ^ 2 + 24 * v ^ 2 * (1 - v ^ 2))
    cutoff_polynomialD1_hasDerivAt (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u

/-- [The cutoff is globally twice continuously differentiable](goal). -/
theorem cutoff_contDiff : ContDiff ℝ 2 cutoff := by
  have hd : deriv cutoff = cutoffD1 :=
    funext fun u => (cutoff_hasDerivAt u).deriv
  have hdd : deriv cutoffD1 = cutoffD2 :=
    funext fun u => (cutoffD1_hasDerivAt u).deriv
  have hp : ContDiff ℝ 2
      (fun u : ℝ => -6 * (1 - u ^ 2) ^ 2 + 24 * u ^ 2 * (1 - u ^ 2)) := by
    fun_prop
  have hc : Continuous cutoffD2 := by
    unfold cutoffD2
    rw [cutoff_branch_eq_join _ (by norm_num)]
    exact joinAt_continuous (-1) continuous_const
      (joinAt_continuous 1 hp.continuous continuous_const (by norm_num))
      (by norm_num [joinAt])
  apply (contDiff_succ_iff_deriv (n := 1)).2
  refine ⟨fun u => (cutoff_hasDerivAt u).differentiableAt, by simp, ?_⟩
  rw [hd]
  apply contDiff_one_iff_deriv.2
  refine ⟨fun u => (cutoffD1_hasDerivAt u).differentiableAt, ?_⟩
  rw [hdd]
  exact hc

/-- [The ordinary derivative equals the explicit first jet](goal). -/
theorem cutoff_deriv : deriv cutoff = cutoffD1 := by
  funext u
  exact (cutoff_hasDerivAt u).deriv

/-- [The second ordinary derivative equals the explicit second jet](goal). -/
theorem cutoff_deriv_two : deriv (deriv cutoff) = cutoffD2 := by
  rw [cutoff_deriv]
  funext u
  exact (cutoffD1_hasDerivAt u).deriv

/-- At [an input in the closed polynomial region](hyp:u,hu),
[the first derivative has the exact polynomial formula](goal). -/
theorem cutoff_deriv_of_abs_le (u : ℝ) (hu : |u| ≤ 1) :
    deriv cutoff u = -6 * u * (1 - u ^ 2) ^ 2 := by
  simp [cutoff_deriv, cutoffD1, hu]

/-- At [an input in the closed polynomial region](hyp:u,hu),
[the second derivative has the exact polynomial formula](goal). -/
theorem cutoff_second_deriv_of_abs_le (u : ℝ) (hu : |u| ≤ 1) :
    deriv (deriv cutoff) u = -6 * (1 - u ^ 2) ^ 2 + 24 * u ^ 2 * (1 - u ^ 2) := by
  simp [cutoff_deriv_two, cutoffD2, hu]

/-- At [an input](hyp:u) [on or outside the unit boundary](hyp:hu),
[the value and both ordinary jets vanish](goal). -/
theorem cutoff_jets_zero (u : ℝ) (hu : 1 ≤ |u|) :
    cutoff u = 0 ∧ deriv cutoff u = 0 ∧ deriv (deriv cutoff) u = 0 := by
  rw [cutoff_deriv_two, cutoff_deriv]
  by_cases hle : |u| ≤ 1
  · have heq : |u| = 1 := le_antisymm hle hu
    have hsq : u ^ 2 = 1 := by nlinarith [sq_abs u]
    simp [cutoff, cutoffD1, cutoffD2, hle, hsq]
  · simp [cutoff, cutoffD1, cutoffD2, hle]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
