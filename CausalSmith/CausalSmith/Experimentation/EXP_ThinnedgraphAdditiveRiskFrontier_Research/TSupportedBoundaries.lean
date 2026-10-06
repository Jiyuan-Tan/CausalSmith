module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.FrontierLower
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TBlockTestingScale
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TObservableUpper

/-!
# Supported boundary regimes
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Enlarging the schedule degree class cannot reduce minimax risk.  [For the stated data and conditions](hyp:V,D,d,d',hdd), [the stated conclusion holds](goal). -/
-- @node: minimaxRisk_mono_degree
lemma minimaxRisk_mono_degree {V : Type*} [Fintype V] [DecidableEq V]
    (D : Measure (Assign V × Audit V)) {d d' : ℕ} (hdd : d ≤ d') :
    minimaxRisk D d ≤ minimaxRisk D d' := by
  apply Causalean.Stat.minimaxValueENNReal_mono_class
    (fun θ => ⟨θ.1, θ.2.mono hdd⟩)
  intro T θ
  exact le_rfl

/-- The degree-one testing frontier dominates the reciprocal audit sample size.  [For the stated data and conditions](hyp:n,hn,q,hq), [the stated conclusion holds](goal). -/
-- @node: degree_one_frontier_reciprocal
lemma degree_one_frontier_reciprocal (n : ℕ) (hn : 4 ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    1 / (1 + n * q) ≤ frontierScale n 1 q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 ≤ (n : ℝ) * q := mul_nonneg hn'.le hq.1
  have hden : 0 < 1 + (n : ℝ) * q := by linarith
  by_cases hp : 0 < q
  · simp only [frontierScale, if_pos hp, Nat.cast_one, one_pow,
      pow_one, sub_sub_cancel]
    apply le_min
    · exact (div_le_one hden).2 (by linarith)
    · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hn' hp) (by linarith)
  · have hz : q = 0 := by linarith [hq.1]
    subst q
    simp [frontierScale]

/-- The degree-one observable envelope gives the reciprocal audit upper bound.  [For the stated data and conditions](hyp:n,hn,q,hq), [the stated conclusion holds](goal). -/
-- @node: degree_one_envelope_upper
lemma degree_one_envelope_upper (n : ℕ) (hn : 4 ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    min 1 (upperEnvelope n 1 q) ≤ ENNReal.ofReal (21 / (1 + n * q)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 ≤ (n : ℝ) * q := mul_nonneg hn'.le hq.1
  have hden : 0 < 1 + (n : ℝ) * q := by linarith
  by_cases hp : 0 < q
  · have hnp : 0 < (n : ℝ) * q := mul_pos hn' hp
    have hu : 5 * ((1 : ℝ) + 1) ^ 2 / n + 4 * 1 * (1 - q) / (n * q) ≤
        20 / (n * q) := by
      apply (le_div_iff₀ hnp).2
      field_simp
      nlinarith [hq.2]
    have he : min 1 (upperEnvelope n 1 q) ≤ ENNReal.ofReal (min 1 (20 / (n * q))) := by
      rw [upperEnvelope, if_pos hp, ← ENNReal.ofReal_one, ← ENNReal.ofReal_min]
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by simpa using hu))
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    by_cases hs : (n : ℝ) * q ≤ 20
    · exact (min_le_left _ _).trans ((le_div_iff₀ hden).2 (by linarith))
    · apply (min_le_right _ _).trans
      apply (div_le_div_iff₀ hnp hden).2
      nlinarith
  · have hz : q = 0 := by linarith [hq.1]
    subst q
    simp [upperEnvelope]

/-- Universal lower bound and the zero-retention, known-graph, and degree-one boundary
sandwiches.  [the stated conclusion holds](goal). -/
-- @node: thm:supported-boundaries
theorem supported_boundaries :
    ∃ c C0 : ℝ, 0 < c ∧ 0 < C0 ∧
    -- @realizes c(positive universal constant, outside every regime binder)
    -- @realizes C0(positive finite universal constant, outside every regime binder)
    ∀ n : ℕ, 4 ≤ n → -- @realizes n(population size n ≥ 4)
    ∀ d : ℕ, 1 ≤ d → d ≤ n - 1 → -- @realizes d(1 ≤ d ≤ n-1)
    ∀ q : ℝ, q ∈ Set.Icc 0 1 → -- @realizes q(known retention in [0,1])
    ∀ D : Measure (Assign (Fin n) × Audit (Fin n)),
      AssignmentLaw D → AuditLaw D q → DesignIndependent D →
      ENNReal.ofReal (c * max (min 1 (((d : ℝ) + 1) ^ 2 / n)) (1 / (1 + n * q))) ≤ minimaxRisk D d ∧
      (q = 0 → minimaxRisk D d ≤ 1) ∧
      (q = 1 → minimaxRisk D d ≤ ENNReal.ofReal (C0 * min 1 (((d : ℝ) + 1) ^ 2 / n))) ∧
      (d = 1 → minimaxRisk D d ≤ ENNReal.ofReal (C0 / (1 + n * q)))  := by
  -- Reuse the proved degree-one block frontier with its conservative universal constant.
  let c : ℝ := (2560000 * Real.pi ^ 2)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, 21, hc, by norm_num, ?_⟩
  intro n hn d hd hdu q hq D ha hw hi
  have hD := design_eq_thinnedDesign D q ha hw hi
  subst D
  have hupper := observable_upper (V := Fin n) d q
    (by simpa using hn) hd (by simpa using hdu) hq
  have hu : minimaxRisk (thinnedDesign (Fin n) q) d ≤ min 1 (upperEnvelope n d q) := by
    simpa only [Fintype.card_fin] using hupper.1.trans hupper.2.1
  have hsup := supplied_block_record_lower n d q (thinnedDesign (Fin n) q)
    hn hd hdu hq ha hw hi
  have hfirst : ENNReal.ofReal (c * min 1 (((d : ℝ) + 1) ^ 2 / n)) ≤
      minimaxRisk (thinnedDesign (Fin n) q) d := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hsup
    apply mul_le_mul_of_nonneg_right _ (le_min (by norm_num) (by positivity))
    dsimp [c]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2
      (by nlinarith [sq_pos_of_pos Real.pi_pos])
  have hsecond : ENNReal.ofReal (c * (1 / (1 + n * q))) ≤
      minimaxRisk (thinnedDesign (Fin n) q) d := by
    have hl := frontier_minimax_lower n 1 q hn (by omega) (by omega) hq
    apply le_trans (ENNReal.ofReal_le_ofReal ?_)
      (hl.trans (minimaxRisk_mono_degree _ hd))
    simpa [c, div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (degree_one_frontier_reciprocal n hn q hq) hc.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_max_of_nonneg _ _ hc.le, ENNReal.ofReal_max]
    exact max_le hfirst hsecond
  · intro _
    exact hu.trans (min_le_left _ _)
  · intro hqone
    subst q
    have he : min 1 (upperEnvelope n d 1) ≤
        ENNReal.ofReal (21 * min 1 (((d : ℝ) + 1) ^ 2 / n)) := by
      simp only [upperEnvelope, zero_lt_one, ↓reduceIte, sub_self, mul_zero,
        zero_div, add_zero]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_min]
      apply ENNReal.ofReal_le_ofReal
      by_cases hs : ((d : ℝ) + 1) ^ 2 / n ≤ 1
      · rw [min_eq_right hs]
        have heq : 5 * ((d : ℝ) + 1) ^ 2 / n = 5 * (((d : ℝ) + 1) ^ 2 / n) := by ring
        rw [heq]
        exact (min_le_right _ _).trans (by nlinarith [show 0 ≤ ((d : ℝ) + 1) ^ 2 / n by positivity])
      · rw [min_eq_left (le_of_not_ge hs)]
        exact (min_le_left _ _).trans (by norm_num)
    exact hu.trans he
  · intro hdOne
    subst d
    exact hu.trans
      (degree_one_envelope_upper n hn q hq)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
