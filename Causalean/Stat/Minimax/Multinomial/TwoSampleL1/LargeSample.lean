module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FuzzyRisk

/-!
# Large-sample two-multinomial L1 minimax lower bound

The rate applies to every alphabet of size at least two and every fixed
sample size greater than the square of that alphabet size.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

/-- [There is a universal constant c > 0 such that, for every alphabet size k ≥ 2 and every sample size n > k², the minimax squared risk of estimating the L1 distance between two probability vectors on k symbols from two independent samples of size n is at least c · k / (n · log(e·k))](goal). -/
theorem twoSampleL1MinimaxRisk_largeSample_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ, 2 ≤ k → k ^ 2 < n →
      c * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) ≤
        twoSampleL1MinimaxRisk n k := by
  obtain ⟨a, ha, hwitness⟩ := largeSample_fuzzyCertificate
  refine ⟨11 * a / 512, by positivity, ?_⟩
  intro k n hk hn
  obtain ⟨W, hsep⟩ := hwitness k n hk hn
  calc
    11 * a / 512 * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) =
        (11 / 512 : ℝ) * (a * ((k : ℝ) / ((n : ℝ) * logAlphabet k))) := by ring
    _ ≤ (11 / 512 : ℝ) * W.delta ^ 2 :=
      mul_le_mul_of_nonneg_left hsep (by norm_num)
    _ = 11 * W.delta ^ 2 / 512 := by ring
    _ ≤ twoSampleL1MinimaxRisk n k := W.minimax_lower

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
