/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fixed Longitudinal Treatment Path: general-`n` identification (final theorems)

Combines `conditionalPath_base` and `conditionalPath_step` from `DTR/Induction.lean` into the
backward-induction proof of `conditionalPath_backdoor` for arbitrary horizon `n ≥ 1`,
and derives the integrated identification `treatmentPath_backdoor` as a corollary.

The conditional identification target is

    (historyBundle 0).condExpGiven (Y_of dbar) =ᵐ[μ] innerReg dbar (n - 1)

which is the iterated-conditional-expectation form of `prop:po-dynamic-backdoor`
from `Basic Concepts.tex` (`subsec:po-dynamic-regime`), specialized here to
prescribed treatment sequences.
-/

module
public import Causalean.PO.ID.Exact.DTR.StrongCancellation

/-! # Fixed Longitudinal Treatment Path Backdoor Identification

This file proves the general finite-horizon fixed-treatment-path backdoor
identification theorem. It combines the base and inductive cancellation steps
into a backward induction argument and then integrates the resulting conditional
mean identity.

The exported theorem `conditionalPath_iter` records the full induction invariant,
`conditionalPath_backdoor` gives the conditional mean identification, and
`treatmentPath_backdoor` identifies the mean potential outcome with the adjusted
longitudinal-path functional. Every intervention is a fixed `Fin n → δ` path;
history-dependent decision rules are not represented. -/

public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLongitudinalPathSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-- Under [the fixed-path assumptions](hyp:hA), [a positive horizon](hyp:hn), and
[a longitudinal-path system with a prescribed treatment path](hyp:S,dbar), [the
backward-induction invariant equates each adjusted regression times its partial path
indicator with the matching history-conditional outcome mean times that indicator](goal). -/
theorem conditionalPath_iter [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : POLongitudinalPathSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (hn : 0 < n) :
    ∀ j : ℕ, j < n →
      (fun ω => S.innerReg dbar j ω * S.indD dbar (n - 1 - j) ω)
        =ᵐ[P.μ]
      (fun ω => S.indD dbar (n - 1 - j) ω *
        (S.historyBundle (n - 1 - j) (by omega)).condExpGiven
          (S.Y_of dbar) P.μ ω) := by
  intro j hj
  induction j with
  | zero =>
    have h := S.conditionalPath_base hA dbar hn
    -- `conditionalPath_base` produces the j = 0 case with `n - 1` on the indD side;
    -- `n - 1 - 0 = n - 1`, so the two statements coincide.
    have heq : n - 1 - 0 = n - 1 := by omega
    simp only [heq]
    convert h using 3
  | succ j ih =>
    have hj' : j < n := Nat.lt_of_succ_lt hj
    have ih' := ih hj'
    -- `conditionalPath_step` consumes IH at depth j (with index `n - j - 1` on indD)
    -- and produces depth j+1 (with index `n - j - 2`).  Bridge `n - 1 - j`
    -- ↔ `n - j - 1` and `n - 1 - (j + 1)` ↔ `n - j - 2`.
    have heq1 : n - 1 - j = n - j - 1 := by omega
    have heq2 : n - 1 - (j + 1) = n - j - 2 := by omega
    have hk : n - j - 2 < n := by omega
    -- Reshape ih' to match conditionalPath_step's IH-shape.
    have ihStep :
        (fun ω => S.innerReg dbar j ω * S.indD dbar (n - j - 1) ω)
          =ᵐ[P.μ]
        (fun ω => S.indD dbar (n - j - 1) ω *
          (S.historyBundle (n - j - 1) (by omega)).condExpGiven
            (S.Y_of dbar) P.μ ω) := by
      have := ih'
      simp only [heq1] at this
      convert this using 2
    have hjlt : j < n := Nat.lt_of_succ_lt hj
    have hIH_int : Integrable (S.innerReg dbar j) P.μ :=
      (S.conditionalPath_strong hA dbar hn j hjlt).2
    have hStep := S.conditionalPath_step hA dbar j hj hk hIH_int ihStep
    -- Reshape `hStep`'s conclusion to the goal indices.
    simp only [heq2]
    convert hStep using 2

/-- **General-`n` conditional treatment-path backdoor identification.** Under [the
fixed-treatment-path identification assumptions](hyp:hA), for [a positive
horizon `n`](hyp:hn), [a longitudinal-path system and prescribed treatment
path](hyp:S,dbar) satisfy [the conditional mean of `Y(dbar)` given the initial-history
σ-algebra equals the outermost iterated-CE functional `innerReg dbar (n - 1)`](goal). -/
theorem conditionalPath_backdoor [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : POLongitudinalPathSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (hn : 0 < n) :
    (S.historyBundle 0 hn).condExpGiven (S.Y_of dbar) P.μ
      =ᵐ[P.μ] S.innerReg dbar (n - 1) := by
  -- Specialize conditionalPath_iter at j = n - 1.  Note `n - 1 - (n - 1) = 0` and
  -- `S.indD dbar 0 = fun _ => 1` by definition.
  have hjlt : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have hiter := S.conditionalPath_iter hA dbar hn (n - 1) hjlt
  have hzero : n - 1 - (n - 1) = 0 := by omega
  simp only [hzero] at hiter
  -- After specialization: `innerReg (n-1) · indD 0 =ᵐ indD 0 · μ[Y_of|σ_0]`.
  -- Both `· indD 0` factors are `· 1` by definition, so the equality reduces.
  have hindD0 : S.indD dbar 0 = fun _ => (1 : ℝ) := rfl
  rw [hindD0] at hiter
  -- Now hiter : `(fun ω => innerReg (n-1) ω * 1) =ᵐ (fun ω => 1 * μ[Y|σ_0] ω)`.
  filter_upwards [hiter] with ω hω
  simp only [mul_one, one_mul] at hω
  exact hω.symm

/-- **General-`n` integrated treatment-path backdoor identification.** Under [the
fixed-treatment-path identification assumptions](hyp:hA), for [a positive
horizon `n`](hyp:hn), [a longitudinal-path system and prescribed treatment
path](hyp:S,dbar) satisfy [the mean potential outcome `E[Y(dbar)]` equals the
integral of the outermost adjusted functional `innerReg dbar (n - 1)`](goal). -/
theorem treatmentPath_backdoor [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : POLongitudinalPathSystem P n δ γ) (hA : S.Assumptions) (dbar : Fin n → δ)
    (hn : 0 < n) :
    S.treatmentPathMean dbar = S.adjustedTreatmentPathMean dbar := by
  unfold POLongitudinalPathSystem.treatmentPathMean
    POLongitudinalPathSystem.adjustedTreatmentPathMean
  -- adjustedTreatmentPathMean branches on `0 < n`; pick the positive branch.
  rw [if_pos hn]
  -- ∫ Y_of dbar = ∫ μ[Y_of dbar | σ_0] = ∫ innerReg (n-1).
  have hCE : ∫ ω, S.Y_of dbar ω ∂P.μ
      = ∫ ω, (S.historyBundle 0 hn).condExpGiven (S.Y_of dbar) P.μ ω ∂P.μ := by
    unfold POCFBundle.condExpGiven
    exact (MeasureTheory.integral_condExp (S.historyBundle 0 hn).sigma_le).symm
  rw [hCE]
  exact MeasureTheory.integral_congr_ae (S.conditionalPath_backdoor hA dbar hn)

end POLongitudinalPathSystem

end PO
end Causalean
