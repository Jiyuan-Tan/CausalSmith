module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RiskBounds
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.TUpper
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.TLowerAllProcedure
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreGrouping

/-! # Score-threshold overlap regret — matched minimax frontier

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: deletionSchedule_range
/-- The balancing schedule is a valid deletion level for every positive sample size. -/
lemma deletionSchedule_range (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (hn : 0 < n) :
    0 < deletionSchedule α γ θ n ∧ deletionSchedule α γ θ n ≤ 1/4 := by
  have hsLoc : 0 < sLoc α γ θ := by
    unfold sLoc betaExp
    positivity
  have hs : 0 < sExp α γ θ := lt_min hsLoc hθ
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold deletionSchedule
  exact ⟨lt_min (by norm_num) (Real.rpow_pos_of_pos hn' _), min_le_left _ _⟩

-- @node: rateSelector_learnerClass
/-- The rate selector, ignoring the independent randomizer, is an admissible learner. -/
lemma rateSelector_learnerClass (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (hn : 0 < n) :
    LearnerClass n (fun e d _ x => rateSelector α γ θ e d x) := by
  intro e he heRange
  have ha := deletionSchedule_range α γ θ n hα hγ hθ hn
  have hSel := sortedSelector_exact (deletionSchedule α γ θ n) e ha he heRange hn
  constructor
  · let GoodData := {d : Fin n → Observation //
        ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1}
    let pack : ((Fin n → {o : Observation //
        o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1}) ×
        Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) → GoodData := fun z =>
      ⟨fun i => (z.1 i).1, fun i => (z.1 i).2⟩
    have hpack : Measurable pack := by fun_prop
    have hmap : Measurable (fun z :
        (Fin n → {o : Observation //
          o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1}) ×
          Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1 => (pack z, z.2.2)) := by
      fun_prop
    simpa only [rateSelector, pack, Function.comp_def] using hSel.2.2.2.1.comp hmap
  · intro e' heq z
    exact congrFun (sortedSelector_congr_logger
      (deletionSchedule α γ θ n) e e' (fun i => (z.1 i).1)
      (fun i => (z.1 i).2.1) heq) z.2.2.1

-- @node: integral_experiment_ignore_randomizer
/-- Integrating a sample statistic over the independent uniform randomizer changes nothing. -/
lemma integral_experiment_ignore_randomizer (P : RowLaw) (n : ℕ)
    (hwf : WellFormed P) (f : (Fin n → Observation) → ℝ) :
    (∫ du, f du.1 ∂experiment P n) = ∫ d, f d ∂sampleLaw P n := by
  haveI : IsProbabilityMeasure (sampleLaw P n) := sampleLaw_isProbability P n hwf
  haveI : SFinite uniformRandomizer := by
    unfold uniformRandomizer
    infer_instance
  have hU : (∫ _u : ℝ, (1:ℝ) ∂uniformRandomizer) = 1 := by
    simp [uniformRandomizer]
  calc
    (∫ du, f du.1 ∂experiment P n) =
        (∫ d, f d ∂sampleLaw P n) *
          (∫ _u : ℝ, (1:ℝ) ∂uniformRandomizer) := by
      simpa only [experiment, mul_one] using
        (integral_prod_mul (μ := sampleLaw P n) (ν := uniformRandomizer)
          f (fun _ : ℝ => (1:ℝ)))
    _ = _ := by rw [hU, mul_one]

/-- Worst-case expected regret of the rate selector over the class. -/
noncomputable def selectorWorstRisk (α γ θ : ℝ) (n : ℕ) : ℝ :=
  ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2},
    ∫ d, regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
      (measurablePolicy (rateSelector α γ θ Pe.1.2 d)) ∂sampleLaw Pe.1.1 n

-- @node: thm:matched-frontier
/-- Matched expected-regret frontier, with the feasible selector between the bounds. -/
theorem matched_frontier (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ c C : ℝ, ∃ N : ℕ, 0 < c ∧ c ≤ C ∧
      ∀ n ≥ N,
        c*(n:ℝ)^(-rExp α γ θ) ≤ minimaxRegret α γ θ n ∧
        minimaxRegret α γ θ n ≤ selectorWorstRisk α γ θ n ∧
        selectorWorstRisk α γ θ n ≤ C*(n:ℝ)^(-rExp α γ θ) := by
  obtain ⟨c₀, N₀, hc₀, hLower⟩ := lower_all_procedure α γ θ hα hγ hθ
  obtain ⟨C₀, N₁, hC₀, hUpper⟩ := upper_bound α γ θ hα hγ hθ
  obtain ⟨N₂, hLocal⟩ := localPair_mem_lawClass α γ θ hα hγ hθ
  refine ⟨c₀, max c₀ C₀, max (max N₀ N₁) N₂, hc₀, le_max_left _ _, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn₁ : N₁ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hPow : 0 ≤ (n : ℝ) ^ (-rExp α γ θ) := by positivity
  constructor
  · simpa only [(hLower n hn₀).2] using (hLower n hn₀).1
  constructor
  · have hnPos : 0 < n := (hLocal n hn₂ true).sampleSize
    let Φ : {Φ : Learner n // LearnerClass n Φ} :=
      ⟨fun e d _ x => rateSelector α γ θ e d x,
        rateSelector_learnerClass α γ θ n hα hγ hθ hnPos⟩
    let risk : {Φ : Learner n // LearnerClass n Φ} → ℝ := fun Ψ =>
      ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2},
        ∫ du, regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
          (measurablePolicy (fun x => Ψ.1 Pe.1.2 du.1 du.2 x))
          ∂experiment Pe.1.1 n
    have hDef : minimaxRegret α γ θ n = ⨅ Ψ, risk Ψ := rfl
    have hLowerPos : 0 < minimaxRegret α γ θ n := by
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
      have hp : 0 < (n : ℝ)^(-rExp α γ θ) := Real.rpow_pos_of_pos hnReal _
      have hl := (hLower n hn₀).1
      rw [(hLower n hn₀).2] at hl
      exact lt_of_lt_of_le (mul_pos hc₀ hp) hl
    have hBdd : BddBelow (Set.range risk) := by
      by_contra h
      have hzero : minimaxRegret α γ θ n = 0 := by
        rw [hDef, ciInf_of_not_bddBelow h, Real.sInf_empty]
      linarith
    calc
      minimaxRegret α γ θ n = ⨅ Ψ, risk Ψ := hDef
      _ ≤ risk Φ := ciInf_le hBdd Φ
      _ = selectorWorstRisk α γ θ n := by
        unfold risk selectorWorstRisk
        congr 1
        funext Pe
        simpa [Φ] using integral_experiment_ignore_randomizer Pe.1.1 n Pe.2.wf
          (fun d => regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
            (measurablePolicy (rateSelector α γ θ Pe.1.2 d)))
  · unfold selectorWorstRisk
    haveI : Nonempty {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2} :=
      ⟨⟨(localPair α γ θ n true, localLogger α γ θ n), hLocal n hn₂ true⟩⟩
    apply ciSup_le
    intro Pe
    exact (hUpper n hn₁ Pe.1.1 Pe.1.2 Pe.2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hPow)

end CausalSmith.Stat.ScorethresholdOverlapRegret
