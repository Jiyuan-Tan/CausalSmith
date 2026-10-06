module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Concentration
public import Causalean.Stat.Minimax.ChiSquared

/-! # Small-sample two-point comparison -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

-- @node: converse_smallN_separation
/-- The Bernoulli perturbation dominates the requested scale at bounded sample sizes. Given [the specified input `a`](hyp:a), [the specified input `c`](hyp:c), [the specified input `N`](hyp:N), [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `ha`](hyp:ha), [the specified input `hc`](hyp:hc), [the specified input `hcn`](hyp:hcn), [the specified input `hn`](hyp:hn), [the specified input `hN`](hyp:hN), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma converse_smallN_separation (a c : ℝ) (N n d : ℕ) (q : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) (hcn : c ≤ 2 * a / Real.sqrt N)
    (hn : 1 ≤ n) (hN : n < N)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    c * gScale n d q ≤ a / Real.sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hrootn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hroots : Real.sqrt (n : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (Nat.le_of_lt hN)
  have hdelta : 0 ≤ delta q := by
    simp only [delta]
    linarith [hq.2]
  have hscale : gScale n d q ≤ 1 / 2 := by
    unfold gScale
    have hmin : min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ≤ 1 := min_le_left _ _
    have h := mul_le_mul_of_nonneg_left hmin hdelta
    dsimp [delta] at h ⊢
    linarith [hq.1]
  have hcle : c * gScale n d q ≤ c / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hscale hc]
  have hca : c / 2 ≤ a / Real.sqrt N := by
    calc
      c / 2 ≤ (2 * a / Real.sqrt N) / 2 :=
        div_le_div_of_nonneg_right hcn (by norm_num)
      _ = a / Real.sqrt N := by ring
  have hdiv : a / Real.sqrt N ≤ a / Real.sqrt n := by
    exact div_le_div_of_nonneg_left (le_of_lt ha) hrootn hroots
  exact hcle.trans (hca.trans hdiv)

end CausalSmith.Stat.MarNearcompleteFrontier
