module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.MomentCertificate
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.TripleConstruction
public import Mathlib.Analysis.Complex.ExponentialBounds

public section

open MeasureTheory Set Finset

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

private lemma half_le_natFloor_of_one_le_zeng {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  by_cases hx2 : x ≤ 2
  · have hfloor : 1 ≤ Nat.floor x := Nat.le_floor (n := 1) (a := x) (by simpa using hx)
    have hone : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hfloor
    linarith
  · have hfloor := Nat.sub_one_lt_floor x
    have hxlarge : 2 < x := lt_of_not_ge hx2
    linarith

/-- Given [the specified inputs and assumptions](hyp:ε,c₁,c₂,c₄,n,d,K,M), [the stated mathematical conclusion holds](goal). -/
private theorem exists_triplePriors_uniformScale (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ c0 gap : ℝ, 0 < c0 ∧ c0 < 1 ∧ 0 < gap ∧
      ∀ b : ℝ, 0 < b → ∀ K : ℕ, 1 ≤ K →
        ∃ T : TriplePriors K b ε (endpointScale c0 K * b * gap),
          (∫ t, t.1 ∂T.ν₀) = endpointScale c0 K * b := by
  have hq0 : 0 < 1 - 2 * ε := by linarith
  have hq1 : 1 - 2 * ε ≤ 1 := by linarith
  obtain ⟨c0, gap, hc0, hc0one, hgap, hscalar⟩ :=
    exists_scalarPriors (1 - 2 * ε) hq0 hq1
  refine ⟨c0, gap, hc0, hc0one, hgap, ?_⟩
  intro b hb K hK
  have hKrpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have ha0 : 0 < endpointScale c0 K := by
    unfold endpointScale
    positivity
  have ha1 : endpointScale c0 K ≤ 1 := by
    unfold endpointScale
    apply (div_le_iff₀ (sq_pos_of_pos hKrpos)).2
    have hc0le : c0 ≤ 1 := le_of_lt hc0one
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [sq_nonneg ((K : ℝ) - 1)]
  obtain ⟨S⟩ := hscalar K hK
  obtain ⟨T, _, _, hmean⟩ :=
    scalarPriors_to_triple hK ha0 rfl hε0 hε1 hb S
  exact ⟨T, hmean⟩

/-- Given [a paper-local moment-prior pair](hyp:M), [a generic triple-prior certificate exists at the same scale and target gap](goal). -/
theorem ZengMomentPriorPair.exists_triplePriors
    {ε c₁ c₂ c₄ : ℝ} {n d K : ℕ}
    (M : ZengMomentPriorPair ε c₁ c₂ c₄ n d K) :
    Nonempty (TriplePriors K (c₁ * Real.log n / n) ε
      (c₄ / ((n : ℝ) * Real.log n))) := by
  letI : IsProbabilityMeasure M.prior0 := M.probability0
  letI : IsProbabilityMeasure M.prior1 := M.probability1
  let B : Set MarkedParam := {z | 0 ≤ z.1 ∧
    z.1 ≤ c₁ * Real.log n / n ∧ ε ≤ z.2.1 ∧ z.2.1 ≤ 1 - ε ∧
      0 ≤ z.2.2 ∧ z.2.2 ≤ 1}
  obtain ⟨s0, s1, hs0, hs1, h0, h1⟩ := M.finite_support
  have hsup0 : M.prior0 B = 1 := by
    apply le_antisymm prob_le_one
    rw [← hs0]
    apply measure_mono
    intro z hz
    exact h0 z hz
  have hsup1 : M.prior1 B = 1 := by
    apply le_antisymm prob_le_one
    rw [← hs1]
    apply measure_mono
    intro z hz
    exact h1 z hz
  exact ⟨{
    positive_degree := M.degree_pos
    ν₀ := M.prior0
    ν₁ := M.prior1
    probability₀ := M.probability0
    probability₁ := M.probability1
    finite₀ := ⟨s0, hs0⟩
    finite₁ := ⟨s1, hs1⟩
    supported₀ := hsup0
    supported₁ := hsup1
    mixed_match := by
      intro i j k hijk
      simpa [mixedMonomial] using M.matched_moments i j k hijk
    mean_p_match := M.mean_p_eq
    target_gap := by
      rw [abs_sub_comm]
      simpa [targetFunctional] using M.separated_pmu }⟩
end CausalSmith.Stat.MarRareqLogfrontier
