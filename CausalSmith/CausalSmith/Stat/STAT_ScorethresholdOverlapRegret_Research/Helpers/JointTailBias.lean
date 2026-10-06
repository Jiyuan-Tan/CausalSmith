module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTailGrid

/-! # Joint-tail bias — uniform assembly

The rounded dyadic grid and its geometric sums give a uniform two-power bias
bound, including the matched exponents without a logarithmic multiplier.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- The law-class assumptions and rounded grid give a uniform bias envelope
on a positive deletion window depending only on the public exponents. -/
-- @node: jointTail_uniform_bias_bound
lemma jointTail_uniform_bias_bound (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ C a0 : ℝ, 0 ≤ C ∧ 0 < a0 ∧
      ∀ (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) (a : ℝ),
        LawClass α γ θ n P e → 0 < a → a ≤ a0 →
        biasFunctional P a ≤ C * (a ^ sLoc α γ θ + a ^ θ) := by
  obtain ⟨Cs, hCs, hs⟩ := jointTail_rounded_grid_sum α γ θ hα hγ hθ
  let Cd := Co θ * (2 : ℝ) ^ α
  let Cg := Co θ * (max 2 ((2 : ℝ) ^ (1 / γ))) ^ α * (2 : ℝ) ^ θ
  let Cu := (max Cm ((2 : ℝ) ^ α) * (2 : ℝ) ^ α) *
    max 1 ((2 : ℝ) ^ (-(-α - 1)))
  have hCd : 0 ≤ Cd := by dsimp [Cd, Co]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg, Co]; positivity
  have hCu : 0 ≤ Cu := by dsimp [Cu, Cm]; positivity
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  let a0 := min (1 / 4 : ℝ)
    ((1 / 4 : ℝ) ^ ((betaExp α γ θ + 1) / betaExp α γ θ))
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  refine ⟨Cd + Cg * Cs + Cu, a0, by positivity, ha0, ?_⟩
  intro n P e a hClass ha hasmall
  have haquarter : a ≤ 1 / 4 := hasmall.trans (min_le_left _ _)
  have ha1 : a ≤ 1 := by linarith
  have he : 0 ≤ betaExp α γ θ / (betaExp α γ θ + 1) := by positivity
  have hcancel : ((betaExp α γ θ + 1) / betaExp α γ θ) *
      (betaExp α γ θ / (betaExp α γ θ + 1)) = 1 := by field_simp
  have hsmall : a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ 1 / 4 := by
    calc
      _ ≤ ((1 / 4 : ℝ) ^ ((betaExp α γ θ + 1) / betaExp α γ θ)) ^
          (betaExp α γ θ / (betaExp α γ θ + 1)) :=
        Real.rpow_le_rpow ha.le (hasmall.trans (min_le_right _ _)) he
      _ = 1 / 4 := by
        rw [← Real.rpow_mul (by norm_num), hcancel, Real.rpow_one]
  obtain ⟨L, U, hLU, hL, hLn, hU, hUn, hgrid⟩ :=
    jointTail_transition_grid α γ θ a hα hγ hθ ha ha1 hsmall
  have hawindow : a ≤ co * (2 : ℝ) ^ γ := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ γ := Real.one_le_rpow (by norm_num) hγ.le
    dsimp [co]
    linarith
  have hbound := jointTail_bias_transition_grid_bound P α γ θ a L U
    hClass.wf hClass.score.1 hα hγ hθ hClass.margin hClass.envelope
    hClass.effectBound ha hawindow hL hLn hU hUn.le hgrid
  have hsum := hs a L U ha ha1 hLU hL hLn.le hU
  have hd : Cd * a ^ θ ≤ Cd * (a ^ sLoc α γ θ + a ^ θ) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)) hCd
  have hu : Cu * a ^ sLoc α γ θ ≤ Cu * (a ^ sLoc α γ θ + a ^ θ) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _)) hCu
  calc
    biasFunctional P a ≤ Cd * a ^ θ + Cg *
        (∑ k ∈ Finset.range U,
          if k ≤ L then a ^ (α + 1) * (a * (2 : ℝ) ^ k) ^ (θ - α - 1)
          else a * (a * (2 : ℝ) ^ k) ^ (θ + α / γ - 1)) + Cu * a ^ sLoc α γ θ := hbound
    _ ≤ Cd * (a ^ sLoc α γ θ + a ^ θ) +
        Cg * (Cs * (a ^ sLoc α γ θ + a ^ θ)) + Cu * (a ^ sLoc α γ θ + a ^ θ) :=
      add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left hsum hCg)) hu
    _ = _ := by ring

/-- Uniform bias bound with independent overlap-tail and small-effect powers. -/
-- @node: lem:joint-tail-bias
lemma joint_tail_bias (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    (∃ C a0 : ℝ, 0 ≤ C ∧ 0 < a0 ∧
      ∀ (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) (a : ℝ),
        LawClass α γ θ n P e → 0 < a → a ≤ a0 →
        biasFunctional P a ≤ C*(a^(sLoc α γ θ)+a^θ)) ∧
    (∃ C a0 : ℝ, 0 ≤ C ∧ 0 < a0 ∧
      ∀ (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) (a : ℝ),
        LawClass 1 (2/3) (3/2) n P e → 0 < a → a ≤ a0 →
        biasFunctional P a ≤ C*a^(3/2:ℝ)) := by
  have hgeneral : ∀ (α γ θ : ℝ), 0 < α → 0 < γ → 0 < θ →
      ∃ C a0 : ℝ, 0 ≤ C ∧ 0 < a0 ∧
        ∀ (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) (a : ℝ),
          LawClass α γ θ n P e → 0 < a → a ≤ a0 →
          biasFunctional P a ≤ C*(a^(sLoc α γ θ)+a^θ) := by
    exact jointTail_uniform_bias_bound
  refine ⟨hgeneral α γ θ hα hγ hθ, ?_⟩
  obtain ⟨C, a0, hC, ha0, hbound⟩ :=
    hgeneral 1 (2/3) (3/2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨2*C, a0, by positivity, ha0, ?_⟩
  intro n P e a hClass ha haSmall
  have hs : sLoc 1 (2/3) (3/2) = (3/2:ℝ) := by
    norm_num [sLoc, betaExp]
  have h := hbound n P e a hClass ha haSmall
  rw [hs] at h
  nlinarith

end CausalSmith.Stat.ScorethresholdOverlapRegret
