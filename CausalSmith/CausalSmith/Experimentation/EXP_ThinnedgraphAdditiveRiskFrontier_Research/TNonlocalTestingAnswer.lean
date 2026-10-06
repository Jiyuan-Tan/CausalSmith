module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TBlockTestingScale

/-!
# Nonlocal testing answer
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The original block family attains its nonlocal radius, with the explicit degree-two scale.  [For the stated data and conditions](hyp:n,B,d,q,hn,hB,hd,hfit,hq), [the stated conclusion holds](goal). -/
-- @node: thm:nonlocal-testing-answer
theorem nonlocal_testing_answer (n B d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) :
    let s := testingScale B d q
    let TV := fun h => Causalean.Stat.tvDist (blockMixtureLaw n B d q true h)
      (blockMixtureLaw n B d q false h)
    let hbar := sSup {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2}
    (100 * Real.pi)⁻¹ * s ≤ hbar ∧ hbar ≤ 2 * s ∧
    (∀ h : ℝ, 0 ≤ h → h ≤ (100 * Real.pi)⁻¹ * s → TV h ≤ 1 / 2) ∧
    (d = 2 → s = if 0 < q then min 1 (Real.sqrt (2 / (B * (2 * q - q ^ 2)))) else 1) := by
  dsimp only
  have htest := block_testing_scale n B d q (thinnedDesign (Fin n) q) hn hB hd hfit hq
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨htest.2.2.1, htest.2.2.2, htest.1, ?_⟩
  intro hd2
  subst d
  have hp : retentionP 2 q = 2 * q - q ^ 2 := by
    unfold retentionP
    ring
  by_cases hqpos : 0 < q
  · have hppos : 0 < retentionP 2 q := by
      rw [hp]
      nlinarith [hq.2]
    rw [hp] at hppos
    simp only [testingScale, hp, if_pos hppos, if_pos hqpos, Nat.cast_mul,
      Nat.cast_ofNat]
    congr 1
    have hden : 0 < (B : ℝ) * 2 * (2 * q - q ^ 2) := by
      have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
      positivity
    have hsqrt : 0 < Real.sqrt ((B : ℝ) * 2 * (2 * q - q ^ 2)) :=
      Real.sqrt_pos.2 hden
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    rw [div_pow, Real.sq_sqrt hden.le]
    field_simp
  · have hqzero : q = 0 := le_antisymm (le_of_not_gt hqpos) hq.1
    subst q
    simp [testingScale, retentionP]


end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
