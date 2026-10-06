module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TMatchedFrontier
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Uniform consistency threshold and fixed-parameter reductions
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open Filter
open scoped Topology

/-- For [the displayed parameters](hyp:d), [UniformlyConsistent](goal) is the object specified by this definition. -/
def UniformlyConsistent (d : ℕ → ℕ) (ε : ℕ → ℝ) : Prop :=
  ∃ est : ∀ n, Estimator n (d n),
    Tendsto
      (fun n => Causalean.Stat.worstCaseRiskReal
        (observedRisk n (d := d n) (ε := ε n)) (est n))
      atTop (𝓝 0)

-- @node: logAlphabet_bounds
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd), the [stated conclusion](goal) holds. -/
lemma logAlphabet_bounds (d : ℕ) (hd : 2 ≤ d) :
    0 < logAlphabet d ∧ logAlphabet d ≤ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : Real.log (d : ℝ) ≤ d - 1 :=
    Real.log_le_sub_one_of_pos hdpos
  have hlog0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  have hform : logAlphabet d = 1 + Real.log (d : ℝ) := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
  rw [hform]
  constructor <;> linarith

-- @node: min_one_mul_bounds
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ha,hx), the [stated conclusion](goal) holds. -/
lemma min_one_mul_bounds {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    min 1 x ≤ min 1 (a * x) ∧ min 1 (a * x) ≤ a * min 1 x := by
  constructor
  · exact min_le_min le_rfl (by nlinarith)
  · rcases le_total x 1 with h | h
    · rw [min_eq_right h]
      exact min_le_right _ _
    · rw [min_eq_left h]
      calc
        min 1 (a * x) ≤ 1 := min_le_left _ _
        _ ≤ a * 1 := by simpa using ha

-- @node: thm:consistency-threshold
/-- [Uniform consistency holds exactly when the alphabet-to-effective-sample-size ratio tends to zero; moreover, for a fixed alphabet the minimax risk is comparable to one capped by the inverse effective sample size, and for fixed overlap it is comparable to one capped by the alphabet-to-sample-size log ratio](goal). -/
theorem consistency_threshold :
    (∀ (d : ℕ → ℕ) (ε : ℕ → ℝ),
      (∀ n, 2 ≤ d n ∧ 0 < ε n ∧ ε n ≤ 1 / 2) →
      (UniformlyConsistent d ε ↔
        Tendsto (fun n => (d n : ℝ) /
          ((n : ℝ) * ε n * logAlphabet (d n))) atTop (𝓝 0))) ∧
    (∀ d : ℕ, 2 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ (n : ℕ) (ε : ℝ),
          1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
          c * min 1 (1 / ((n : ℝ) * ε)) ≤ minimaxRisk n d ε ∧
          minimaxRisk n d ε ≤ C * min 1 (1 / ((n : ℝ) * ε))) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ (n d : ℕ),
          1 ≤ n → 2 ≤ d →
          c * min 1 ((d : ℝ) / ((n : ℝ) * logAlphabet d)) ≤
            minimaxRisk n d ε ∧
          minimaxRisk n d ε ≤
            C * min 1 ((d : ℝ) / ((n : ℝ) * logAlphabet d))) := by
  obtain ⟨cstar, Cstar, H₀, κ, D₀, hH₀, hκ, hD₀, hcstar, hcC, hfront⟩ :=
    matched_frontier
  constructor
  · intro d ε hd
    have h := weighted_separation_and_frontier.2.2
      (fun n => n) d ε tendsto_id hd
    simpa only [UniformlyConsistent] using h
  constructor
  · intro d hd
    obtain ⟨hLpos, hLle⟩ := logAlphabet_bounds d hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have ha : 1 ≤ (d : ℝ) / logAlphabet d := by
      apply (le_div_iff₀ hLpos).2
      simpa using hLle
    refine ⟨cstar, Cstar * (d : ℝ) / logAlphabet d,
      hcstar, ?_, ?_⟩
    · have hCa : Cstar ≤ Cstar * ((d : ℝ) / logAlphabet d) :=
        by simpa using mul_le_mul_of_nonneg_left ha (le_trans (le_of_lt hcstar) hcC)
      calc cstar ≤ Cstar := hcC
        _ ≤ Cstar * ((d : ℝ) / logAlphabet d) := hCa
        _ = Cstar * (d : ℝ) / logAlphabet d := by ring
    · intro n ε hn hε hεhalf
      obtain ⟨hlower, hmid, hupper, _, _⟩ := hfront n d ε hn hd hε hεhalf
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hx : 0 ≤ 1 / ((n : ℝ) * ε) := by positivity
      obtain ⟨hminlo, hminhi⟩ := min_one_mul_bounds ha hx
      have heq : rateScale n d ε =
          min 1 (((d : ℝ) / logAlphabet d) * (1 / ((n : ℝ) * ε))) := by
        rw [rateScale]
        congr 1
        field_simp
      rw [heq] at hlower hupper
      constructor
      · exact (mul_le_mul_of_nonneg_left hminlo (le_of_lt hcstar)).trans hlower
      · have hC : 0 ≤ Cstar := le_trans (le_of_lt hcstar) hcC
        calc
          minimaxRisk n d ε ≤ Cstar * min 1 (((d : ℝ) / logAlphabet d) * (1 / ((n : ℝ) * ε))) := hmid.trans hupper
          _ ≤ (Cstar * (d : ℝ) / logAlphabet d) * min 1 (1 / ((n : ℝ) * ε)) := by
            calc
              Cstar * min 1 (((d : ℝ) / logAlphabet d) * (1 / ((n : ℝ) * ε))) ≤
                  Cstar * (((d : ℝ) / logAlphabet d) * min 1 (1 / ((n : ℝ) * ε))) :=
                mul_le_mul_of_nonneg_left hminhi hC
              _ = _ := by ring
  · intro ε hε hεhalf
    refine ⟨cstar, Cstar / ε, hcstar, ?_, ?_⟩
    · have ha : 1 ≤ 1 / ε := by
        apply (le_div_iff₀ hε).2
        linarith
      have hCa : Cstar ≤ Cstar * (1 / ε) :=
        by simpa using mul_le_mul_of_nonneg_left ha (le_trans (le_of_lt hcstar) hcC)
      calc cstar ≤ Cstar := hcC
        _ ≤ Cstar * (1 / ε) := hCa
        _ = Cstar / ε := by ring
    · intro n d hn hd
      obtain ⟨hlower, hmid, hupper, _, _⟩ := hfront n d ε hn hd hε hεhalf
      obtain ⟨hLpos, _⟩ := logAlphabet_bounds d hd
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hx : 0 ≤ (d : ℝ) / ((n : ℝ) * logAlphabet d) := by positivity
      have ha : 1 ≤ 1 / ε := by
        apply (le_div_iff₀ hε).2
        linarith
      obtain ⟨hminlo, hminhi⟩ := min_one_mul_bounds ha hx
      have heq : rateScale n d ε =
          min 1 ((1 / ε) * ((d : ℝ) / ((n : ℝ) * logAlphabet d))) := by
        rw [rateScale]
        congr 1
        field_simp
      rw [heq] at hlower hupper
      constructor
      · exact (mul_le_mul_of_nonneg_left hminlo (le_of_lt hcstar)).trans hlower
      · have hC : 0 ≤ Cstar := le_trans (le_of_lt hcstar) hcC
        calc
          minimaxRisk n d ε ≤ Cstar * min 1 ((1 / ε) * ((d : ℝ) / ((n : ℝ) * logAlphabet d))) := hmid.trans hupper
          _ ≤ (Cstar / ε) * min 1 ((d : ℝ) / ((n : ℝ) * logAlphabet d)) := by
            calc
              Cstar * min 1 ((1 / ε) * ((d : ℝ) / ((n : ℝ) * logAlphabet d))) ≤
                  Cstar * ((1 / ε) * min 1 ((d : ℝ) / ((n : ℝ) * logAlphabet d))) :=
                mul_le_mul_of_nonneg_left hminhi hC
              _ = _ := by ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
