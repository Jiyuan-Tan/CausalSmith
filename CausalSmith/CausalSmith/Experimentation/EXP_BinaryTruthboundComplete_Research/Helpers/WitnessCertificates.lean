import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.WitnessData
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.FiniteConeDuality
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TObservableMobius
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-! Finite certificate interfaces for the 64 witness schedules. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- For [a six-coordinate binary schedule](hyp:θ), [the witness code](goal) is its binary integer encoding. -/
-- @node: witnessCodeNat
def witnessCodeNat (θ : Fin 6 → Fin 2) : ℕ :=
  ∑ i, (θ i : ℕ) * 2 ^ (5 - i.1)

/-- For [a six-coordinate binary schedule](hyp:θ), [the rational μ-star weight](goal) is the specified uniform certificate weight. -/
-- @node: muStarRat
def muStarRat (θ : Fin 6 → Fin 2) : ℚ :=
  if witnessCodeNat θ ∈ ([0,7,11,14,19,20,28,31,32,39,43,44,48,53,56,59] : List ℕ)
  then 1 / 16 else 0

/-- For [a six-coordinate binary schedule](hyp:θ), [the rational ν-star weight](goal) is the specified uniform certificate weight. -/
-- @node: nuStarRat
def nuStarRat (θ : Fin 6 → Fin 2) : ℚ :=
  if witnessCodeNat θ ∈ ([3,10,16,31,36,47,49,60] : List ℕ) then 1 / 8 else 0

/-- For [a coordinate set and binary schedule](hyp:S,θ), [the natural-number witness monomial](goal) is the product of its selected bits. -/
-- @node: witnessMonomialNat
def witnessMonomialNat (S : Finset (Fin 6)) (θ : Fin 6 → Fin 2) : ℕ :=
  ∏ i ∈ S, (θ i : ℕ)

/-- [μ-star matches every observed witness monomial margin with the uniform distribution](goal). -/
-- @node: muStarRat_margins
lemma muStarRat_margins : ∀ S : Finset (Fin 6),
    (∃ z : Fin 3, S ⊆ witnessO z) →
    (∑ θ, muStarRat θ * witnessMonomialNat S θ) =
      ∑ θ, (1 / 64 : ℚ) * witnessMonomialNat S θ := by
  native_decide

/-- [ν-star matches every observed witness monomial margin through degree three with the uniform distribution](goal). -/
-- @node: nuStarRat_degree_three_margins
lemma nuStarRat_degree_three_margins : ∀ S : Finset (Fin 6),
    (∃ z : Fin 3, S ⊆ witnessO z) → S.card ≤ 3 →
    (∑ θ, nuStarRat θ * witnessMonomialNat S θ) =
      ∑ θ, (1 / 64 : ℚ) * witnessMonomialNat S θ := by
  native_decide

/-- For [a witness schedule](hyp:θ), [the real μ-star weight equals the cast rational certificate weight](goal). -/
-- @node: muStar_eq_ratCast
lemma muStar_eq_ratCast (θ : Theta witnessExperiment) :
    muStar θ = (muStarRat θ : ℝ) := by
  change (if witnessCode θ ∈
      ([0,7,11,14,19,20,28,31,32,39,43,44,48,53,56,59] : List ℕ)
    then (1 / 16 : ℝ) else 0) =
    ((if witnessCodeNat θ ∈
      ([0,7,11,14,19,20,28,31,32,39,43,44,48,53,56,59] : List ℕ)
    then (1 / 16 : ℚ) else 0 : ℚ) : ℝ)
  have hc : witnessCode θ = witnessCodeNat θ := rfl
  rw [hc]
  split <;> norm_num

/-- For [a witness schedule](hyp:θ), [the real ν-star weight equals the cast rational certificate weight](goal). -/
-- @node: nuStar_eq_ratCast
lemma nuStar_eq_ratCast (θ : Theta witnessExperiment) :
    nuStar θ = (nuStarRat θ : ℝ) := by
  change (if witnessCode θ ∈ ([3,10,16,31,36,47,49,60] : List ℕ)
    then (1 / 8 : ℝ) else 0) =
    ((if witnessCodeNat θ ∈ ([3,10,16,31,36,47,49,60] : List ℕ)
    then (1 / 8 : ℚ) else 0 : ℚ) : ℝ)
  have hc : witnessCode θ = witnessCodeNat θ := rfl
  rw [hc]
  split <;> norm_num

/-- For [a witness support and schedule](hyp:S,θ), [the real monomial equals the cast natural witness monomial](goal). -/
-- @node: witnessMonomial_eq_natCast
lemma witnessMonomial_eq_natCast (S : Finset (Fin 6))
    (θ : Theta witnessExperiment) :
    monomial witnessExperiment S θ = ((witnessMonomialNat S θ : ℕ) : ℝ) := by
  simp only [monomial, witnessMonomialNat, Nat.cast_prod]
  rfl

set_option maxHeartbeats 1000000 in
/-- For [a witness coordinate set](hyp:S), [observability is equivalent to containment in a witness observation set](goal). -/
-- @node: witness_observable_iff
lemma witness_observable_iff (S : Finset (Fin 6)) :
    S ∈ observableComplex witnessExperiment ↔ ∃ z : Fin 3, S ⊆ witnessO z := by
  change S ∈ Finset.univ.powerset.filter (fun S => ∃ z : Fin 3, S ⊆ witnessO z) ↔ _
  simp

set_option maxHeartbeats 2000000 in
-- The exact check expands all 64 binary schedules and their three assignment-local table rows.
/-- [The expected value of the displayed nonnegative assignment tables is exactly the unrestricted witness bound](goal). -/
lemma bStar_implemented : expectedRule witnessExperiment hStar = bStar := by
  funext θ
  have hm01 : wcoord 1 ∈ witnessExperiment.O (0 : Fin 3) := by
    change (1 : Fin 6) ∈ witnessO 0
    decide
  have hm03 : wcoord 3 ∈ witnessExperiment.O (0 : Fin 3) := by
    change (3 : Fin 6) ∈ witnessO 0
    decide
  have hm05 : wcoord 5 ∈ witnessExperiment.O (0 : Fin 3) := by
    change (5 : Fin 6) ∈ witnessO 0
    decide
  have hm13 : wcoord 3 ∈ witnessExperiment.O (1 : Fin 3) := by
    change (3 : Fin 6) ∈ witnessO 1
    decide
  have hm14 : wcoord 4 ∈ witnessExperiment.O (1 : Fin 3) := by
    change (4 : Fin 6) ∈ witnessO 1
    decide
  have hm20 : wcoord 0 ∈ witnessExperiment.O (2 : Fin 3) := by
    change (0 : Fin 6) ∈ witnessO 2
    decide
  have hm21 : wcoord 1 ∈ witnessExperiment.O (2 : Fin 3) := by
    change (1 : Fin 6) ∈ witnessO 2
    decide
  have hm22 : wcoord 2 ∈ witnessExperiment.O (2 : Fin 3) := by
    change (2 : Fin 6) ∈ witnessO 2
    decide
  have hm25 : wcoord 5 ∈ witnessExperiment.O (2 : Fin 3) := by
    change (5 : Fin 6) ∈ witnessO 2
    decide
  have h0 : θ (wcoord 0) = 0 ∨ θ (wcoord 0) = 1 := by omega
  rcases h0 with h0 | h0 <;>
    have h1 : θ (wcoord 1) = 0 ∨ θ (wcoord 1) = 1 := by omega
  all_goals rcases h1 with h1 | h1
  all_goals
    have h2 : θ (wcoord 2) = 0 ∨ θ (wcoord 2) = 1 := by omega
  all_goals rcases h2 with h2 | h2
  all_goals
    have h3 : θ (wcoord 3) = 0 ∨ θ (wcoord 3) = 1 := by omega
  all_goals rcases h3 with h3 | h3
  all_goals
    have h4 : θ (wcoord 4) = 0 ∨ θ (wcoord 4) = 1 := by omega
  all_goals rcases h4 with h4 | h4
  all_goals
    have h5 : θ (wcoord 5) = 0 ∨ θ (wcoord 5) = 1 := by omega
  all_goals rcases h5 with h5 | h5
  all_goals
    change (∑ z : Fin 3, (1 / 3 : ℝ) * hStar z (restrict witnessExperiment z θ)) = bStar θ
    rw [Fin.sum_univ_three]
    simp only [hStar, witnessLocalIndex, localBit, restrict, bStar, witnessP, witnessX,
      centeredCoord]
    simp only [hm01, hm03, hm05, hm13, hm14, hm20, hm21, hm22, hm25, ↓reduceDIte]
    simp only [h0, h1, h2, h3, h4, h5]
    norm_num [hStarValue]

/-- For [a witness schedule](hyp:θ), [the true variance equals the displayed explicit quadratic polynomial](goal). -/
-- @node: witness_trueVariance_explicit
lemma witness_trueVariance_explicit (θ : Theta witnessExperiment) :
    trueVarianceFn witnessExperiment θ =
      (8 * ((θ (wcoord 0) : ℕ) : ℝ) * ((θ (wcoord 0) : ℕ) : ℝ) +
       6 * ((θ (wcoord 1) : ℕ) : ℝ) * ((θ (wcoord 1) : ℕ) : ℝ) +
       8 * ((θ (wcoord 2) : ℕ) : ℝ) * ((θ (wcoord 2) : ℕ) : ℝ) +
       6 * ((θ (wcoord 3) : ℕ) : ℝ) * ((θ (wcoord 3) : ℕ) : ℝ) +
       2 * ((θ (wcoord 4) : ℕ) : ℝ) * ((θ (wcoord 4) : ℕ) : ℝ) +
       14 * ((θ (wcoord 5) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ) -
       16 * ((θ (wcoord 0) : ℕ) : ℝ) * ((θ (wcoord 2) : ℕ) : ℝ) -
       4 * ((θ (wcoord 0) : ℕ) : ℝ) * ((θ (wcoord 4) : ℕ) : ℝ) +
       4 * ((θ (wcoord 0) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ) +
       12 * ((θ (wcoord 1) : ℕ) : ℝ) * ((θ (wcoord 3) : ℕ) : ℝ) -
       6 * ((θ (wcoord 1) : ℕ) : ℝ) * ((θ (wcoord 4) : ℕ) : ℝ) -
       18 * ((θ (wcoord 1) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ) +
       4 * ((θ (wcoord 2) : ℕ) : ℝ) * ((θ (wcoord 4) : ℕ) : ℝ) -
       4 * ((θ (wcoord 2) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ) -
       6 * ((θ (wcoord 3) : ℕ) : ℝ) * ((θ (wcoord 4) : ℕ) : ℝ) -
       18 * ((θ (wcoord 3) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ) +
       8 * ((θ (wcoord 4) : ℕ) : ℝ) * ((θ (wcoord 5) : ℕ) : ℝ)) / 9 := by
  have hA (i k : Fin 6) :
      varianceMatrix witnessExperiment (wcoord i) (wcoord k) =
        (∑ z : Fin 3, (1 / 3 : ℝ) * (witnessV z i * witnessV z k)) -
          (∑ z : Fin 3, (1 / 3 : ℝ) * witnessV z i) *
            (∑ z : Fin 3, (1 / 3 : ℝ) * witnessV z k) := by
    rfl
  rw [show trueVarianceFn witnessExperiment θ =
      ∑ i : Fin 6, ∑ k : Fin 6,
        varianceMatrix witnessExperiment (wcoord i) (wcoord k) *
          ((θ (wcoord i) : ℕ) : ℝ) * ((θ (wcoord k) : ℕ) : ℝ) by rfl]
  simp_rw [hA]
  rw [Fin.sum_univ_six]
  simp_rw [Fin.sum_univ_six]
  simp_rw [Fin.sum_univ_three]
  norm_num [witnessV]
  ring

set_option maxHeartbeats 1000000 in
-- The degree-two span and pointwise domination are checked exactly on the witness cube.
/-- [The displayed quadratic witness bound belongs to the degree-two conservative cone](goal). -/
lemma rStar_feasible : rStar ∈ conservativeCone witnessExperiment 2 := by
  classical
  have hmono (S : Finset (Fin witnessExperiment.K))
      (hS : S ∈ observableComplex witnessExperiment) (hc : S.card ≤ 2) :
      monomial witnessExperiment S ∈ observableSpan witnessExperiment 2 := by
    unfold observableSpan
    apply Submodule.subset_span
    exact ⟨S, hS, by exact_mod_cast hc, rfl⟩
  have hpair (i k : Fin 6) (hne : i ≠ k)
      (hp : ({wcoord i, wcoord k} : Finset (Fin witnessExperiment.K)) ∈
        observableComplex witnessExperiment) :
      (fun θ => centeredCoord θ (wcoord i) * centeredCoord θ (wcoord k)) ∈
        observableSpan witnessExperiment 2 := by
    have hw : wcoord i ≠ wcoord k := by
      intro h
      apply hne
      simpa [wcoord, witnessK_eq] using h
    have hp' := hmono {wcoord i, wcoord k} hp (by simp [hw])
    have hi := hmono {wcoord i} (observableComplex_downward_closed witnessExperiment hp (by simp))
      (by simp)
    have hk := hmono {wcoord k} (observableComplex_downward_closed witnessExperiment hp (by simp))
      (by simp)
    have he := hmono ∅ (observableComplex_downward_closed witnessExperiment hp (by simp))
      (by simp)
    rw [show (fun θ => centeredCoord θ (wcoord i) * centeredCoord θ (wcoord k)) =
        (4 : ℝ) • monomial witnessExperiment {wcoord i, wcoord k} -
          (2 : ℝ) • monomial witnessExperiment {wcoord i} -
          (2 : ℝ) • monomial witnessExperiment {wcoord k} + monomial witnessExperiment ∅ by
      funext θ
      simp only [centeredCoord, monomial, Pi.smul_apply, smul_eq_mul,
        Pi.sub_apply, Pi.add_apply]
      simp [hw]
      ring]
    exact Submodule.add_mem _
      (Submodule.sub_mem _
        (Submodule.sub_mem _
          (Submodule.smul_mem _ 4 hp')
          (Submodule.smul_mem _ 2 hi))
        (Submodule.smul_mem _ 2 hk)) he
  have hp (S : Finset (Fin witnessExperiment.K)) (z : Fin 3)
      (h : S ⊆ witnessExperiment.O z) : S ∈ observableComplex witnessExperiment := by
    simp only [observableComplex, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by simp, z, h⟩
  have h01 := hpair 0 1 (by decide) (hp {wcoord 0, wcoord 1} 2 (by decide))
  have h02 := hpair 0 2 (by decide) (hp {wcoord 0, wcoord 2} 2 (by decide))
  have h05 := hpair 0 5 (by decide) (hp {wcoord 0, wcoord 5} 2 (by decide))
  have h12 := hpair 1 2 (by decide) (hp {wcoord 1, wcoord 2} 2 (by decide))
  have h13 := hpair 1 3 (by decide) (hp {wcoord 1, wcoord 3} 0 (by decide))
  have h15 := hpair 1 5 (by decide) (hp {wcoord 1, wcoord 5} 0 (by decide))
  have h25 := hpair 2 5 (by decide) (hp {wcoord 2, wcoord 5} 2 (by decide))
  have h34 := hpair 3 4 (by decide) (hp {wcoord 3, wcoord 4} 1 (by decide))
  have h35 := hpair 3 5 (by decide) (hp {wcoord 3, wcoord 5} 0 (by decide))
  have he := hmono ∅ (observableComplex_downward_closed witnessExperiment
    (hp {wcoord 0, wcoord 1} 2 (by decide)) (by simp)) (by simp)
  constructor
  · rw [show rStar =
        (110 / 72 : ℝ) • monomial witnessExperiment ∅ +
        (3 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 0) * centeredCoord θ (wcoord 1)) -
        (35 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 0) * centeredCoord θ (wcoord 2)) +
        (3 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 0) * centeredCoord θ (wcoord 5)) -
        (3 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 1) * centeredCoord θ (wcoord 2)) +
        (24 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 1) * centeredCoord θ (wcoord 3)) -
        (45 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 1) * centeredCoord θ (wcoord 5)) -
        (3 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 2) * centeredCoord θ (wcoord 5)) -
        (12 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 3) * centeredCoord θ (wcoord 4)) -
        (36 / 72 : ℝ) • (fun θ => centeredCoord θ (wcoord 3) * centeredCoord θ (wcoord 5)) by
      funext θ
      simp only [rStar, witnessP, witnessX, Pi.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.sub_apply, monomial]
      norm_num
      ring]
    exact Submodule.sub_mem _
      (Submodule.sub_mem _
        (Submodule.sub_mem _
          (Submodule.sub_mem _
            (Submodule.add_mem _
              (Submodule.sub_mem _
                (Submodule.add_mem _
                  (Submodule.sub_mem _
                    (Submodule.add_mem _
                      (Submodule.smul_mem _ _ he)
                      (Submodule.smul_mem _ _ h01))
                    (Submodule.smul_mem _ _ h02))
                  (Submodule.smul_mem _ _ h05))
                (Submodule.smul_mem _ _ h12))
              (Submodule.smul_mem _ _ h13))
            (Submodule.smul_mem _ _ h15))
          (Submodule.smul_mem _ _ h25))
        (Submodule.smul_mem _ _ h34))
      (Submodule.smul_mem _ _ h35)
  · intro θ
    rw [witness_trueVariance_explicit]
    have h0 : θ (wcoord 0) = 0 ∨ θ (wcoord 0) = 1 := by omega
    rcases h0 with h0 | h0 <;>
      have h1 : θ (wcoord 1) = 0 ∨ θ (wcoord 1) = 1 := by omega
    all_goals rcases h1 with h1 | h1
    all_goals have h2 : θ (wcoord 2) = 0 ∨ θ (wcoord 2) = 1 := by omega
    all_goals rcases h2 with h2 | h2
    all_goals have h3 : θ (wcoord 3) = 0 ∨ θ (wcoord 3) = 1 := by omega
    all_goals rcases h3 with h3 | h3
    all_goals have h4 : θ (wcoord 4) = 0 ∨ θ (wcoord 4) = 1 := by omega
    all_goals rcases h4 with h4 | h4
    all_goals have h5 : θ (wcoord 5) = 0 ∨ θ (wcoord 5) = 1 := by omega
    all_goals rcases h5 with h5 | h5
    all_goals simp [rStar, witnessP, witnessX, centeredCoord, h0, h1, h2, h3, h4, h5]
    all_goals norm_num

set_option maxHeartbeats 1000000 in
/-- [The displayed quartic witness bound belongs to the unrestricted conservative cone](goal). -/
lemma bStar_feasible : bStar ∈ unrestrictedConservativeCone witnessExperiment := by
  constructor
  · exact (((expectedRule_mem_observableSpan_iff witnessExperiment).1 bStar).1).mp
      ⟨hStar, bStar_implemented⟩
  · intro θ
    have h0 : θ (wcoord 0) = 0 ∨ θ (wcoord 0) = 1 := by omega
    rcases h0 with h0 | h0 <;>
      have h1 : θ (wcoord 1) = 0 ∨ θ (wcoord 1) = 1 := by omega
    all_goals rcases h1 with h1 | h1
    all_goals
      have h2 : θ (wcoord 2) = 0 ∨ θ (wcoord 2) = 1 := by omega
    all_goals rcases h2 with h2 | h2
    all_goals
      have h3 : θ (wcoord 3) = 0 ∨ θ (wcoord 3) = 1 := by omega
    all_goals rcases h3 with h3 | h3
    all_goals
      have h4 : θ (wcoord 4) = 0 ∨ θ (wcoord 4) = 1 := by omega
    all_goals rcases h4 with h4 | h4
    all_goals
      have h5 : θ (wcoord 5) = 0 ∨ θ (wcoord 5) = 1 := by omega
    all_goals rcases h5 with h5 | h5
    all_goals
      rw [witness_trueVariance_explicit]
      simp only [bStar, witnessP, witnessX, centeredCoord,
        h0, h1, h2, h3, h4, h5]
      norm_num

/-- [Every assignment and local outcome receives a table value between zero and five](goal). -/
lemma hStar_nonnegative_bounded : ∀ z y, 0 ≤ hStar z y ∧ hStar z y ≤ 5 := by
  classical
  intro z y
  have hbit (i : Fin witnessExperiment.K) : localBit witnessExperiment z y i ≤ 1 := by
    unfold localBit
    split
    next h =>
      have hy : (y ⟨i, h⟩).val < 2 := (y ⟨i, h⟩).isLt
      omega
    next => omega
  have hidx : witnessLocalIndex z y ≤ 15 := by
    rcases z with ⟨z, hz⟩
    interval_cases z
    · have h1 := hbit (wcoord 1)
      have h3 := hbit (wcoord 3)
      have h5 := hbit (wcoord 5)
      simp only [witnessLocalIndex]
      omega
    · have h3 := hbit (wcoord 3)
      have h4 := hbit (wcoord 4)
      simp only [witnessLocalIndex]
      omega
    · have h0 := hbit (wcoord 0)
      have h1 := hbit (wcoord 1)
      have h2 := hbit (wcoord 2)
      have h5 := hbit (wcoord 5)
      simp only [witnessLocalIndex]
      omega
  unfold hStar
  generalize hn : witnessLocalIndex z y = n at hidx ⊢
  fin_cases z <;> interval_cases n <;> norm_num [hStarValue]

/-- [The displayed sixteen-point uniform law satisfies every observable dual margin of the witness objective](goal). -/
lemma muStar_dual_uniform :
    muStar ∈ dualMarginSet witnessExperiment witnessObjective := by
  constructor
  · intro θ
    unfold muStar
    split <;> norm_num
  · intro S hS
    have hrat := muStarRat_margins S ((witness_observable_iff S).mp hS)
    have hmono : ∀ θ, monomial witnessExperiment S θ =
        ((witnessMonomialNat S θ : ℕ) : ℝ) := fun θ =>
      witnessMonomial_eq_natCast S θ
    simp_rw [hmono]
    convert congrArg (fun x : ℚ => (x : ℝ)) hrat using 1 <;>
      simp only [witnessObjective, witnessQ, Subtype.coe_mk, muStar_eq_ratCast,
        Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] <;> rfl

/-- [For each observable coordinate set of size at most three, the displayed eight-point law matches the corresponding uniform-cube monomial moment](goal). -/
lemma nuStar_degree_three_margins :
    ∀ S ∈ observableComplex witnessExperiment, S.card ≤ 3 →
      ∑ θ, nuStar θ * monomial witnessExperiment S θ =
        ∑ θ, ((1 : ℝ) / 64) * monomial witnessExperiment S θ := by
  intro S hS hcard
  have hrat := nuStarRat_degree_three_margins S
    ((witness_observable_iff S).mp hS) hcard
  have hmono : ∀ θ, monomial witnessExperiment S θ =
      ((witnessMonomialNat S θ : ℕ) : ℝ) := fun θ =>
    witnessMonomial_eq_natCast S θ
  simp_rw [hmono]
  convert congrArg (fun x : ℚ => (x : ℝ)) hrat using 1 <;>
    simp only [nuStar_eq_ratCast, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] <;> rfl

end CausalSmith.Experimentation.BinaryTruthbound
