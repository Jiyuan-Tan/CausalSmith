module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonPredictive
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetTail
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Numerical parameters for the large-alphabet balanced prior

Above a universal alphabet threshold, the moment degree can grow like the
alphabet logarithm. A small balanced tilt then meets the Poisson comparison,
target concentration, and squared-separation requirements simultaneously.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The dyadic degree is bounded by three times the alphabet logarithm. -/
private lemma paired_degree_log_bound (k : ℕ) (hk : 2 ≤ k) :
    ((Nat.log2 k + 1 : ℕ) : ℝ) ≤
      3 * Real.log (Real.exp 1 * (k : ℝ)) := by
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hlogb : (Nat.log2 k : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.log2_le_logb k
  have hlogk' : Real.log (Real.exp 1 * (k : ℝ)) =
      1 + Real.log (k : ℝ) := by
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
  push_cast
  rw [hlogk']
  have h := (le_div_iff₀ (by linarith : 0 < Real.log 2)).1 hlogb
  have hq : 0 ≤ (Nat.log2 k : ℝ) := by positivity
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hlog₂)]

/-- Eventually the pair count dominates the squared dyadic degree. -/
private lemma eventually_paired_degree_scale :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      320000 * (16 * ((Nat.log2 k + 1 : ℕ) : ℝ)) ^ 2 ≤
        ((k / 2 : ℕ) : ℝ) := by
  open Filter in
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show (0 : ℝ) < 1 / 4000000000 by norm_num)
  have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have he : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (k : ℝ) ^ 2 ≤ (k : ℝ) / 4000000000 := by
    filter_upwards [h.filter_mono ht] with k hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (k : ℝ))),
      abs_of_nonneg hk0, div_eq_mul_inv, mul_comm] using hk
  rw [Filter.eventually_atTop] at he
  obtain ⟨K0, hK0⟩ := he
  refine ⟨max K0 1000000000, ?_⟩
  intro k hk
  have hkK : K0 ≤ k := le_trans (Nat.le_max_left _ _) hk
  have hkbig : 1000000000 ≤ k := le_trans (Nat.le_max_right _ _) hk
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hu : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hlogb : (Nat.log2 k : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.log2_le_logb k
  have hq : ((Nat.log2 k + 1 : ℕ) : ℝ) ≤
      1 + 2 * Real.log (k : ℝ) := by
    push_cast
    have hh := (le_div_iff₀ (by linarith : 0 < Real.log 2)).1 hlogb
    have hnonneg : 0 ≤ (Nat.log2 k : ℝ) := by positivity
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hlog₂)]
  have hqsq : (((Nat.log2 k + 1 : ℕ) : ℝ)) ^ 2 ≤
      2 + 8 * Real.log (k : ℝ) ^ 2 := by
    have hnonneg : (0 : ℝ) ≤ (Nat.log2 k + 1 : ℕ) := by positivity
    nlinarith [sq_nonneg (1 - 2 * Real.log (k : ℝ))]
  have hlogsq := hK0 k hkK
  have hb : (k : ℝ) / 3 ≤ ((k / 2 : ℕ) : ℝ) := by
    have hh : k ≤ 3 * (k / 2) := by omega
    have hhR : (k : ℝ) ≤ 3 * ((k / 2 : ℕ) : ℝ) := by exact_mod_cast hh
    linarith
  have hkbigR : (1000000000 : ℝ) ≤ k := by exact_mod_cast hkbig
  nlinarith

/-- The dyadic degree makes the comparison remainder uniformly small. -/
private lemma paired_degree_tail (k : ℕ) (hk : 4 ≤ k) :
    ((k / 2 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((16 * (Nat.log2 k + 1) : ℕ) : ℝ) / 4) ≤
        1 / 32 := by
  let q := Nat.log2 k + 1
  have hkq : k < 2 ^ q := by
    simpa [q, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega : 1 < 2) k)
  have hkqR : (k : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast (Nat.le_of_lt hkq)
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : ((k / 2 : ℕ) : ℝ) ≤ k := by
    exact_mod_cast (Nat.div_le_self k 2)
  have hpow : (k : ℝ) ^ 4 ≤ ((2 : ℝ) ^ q) ^ 4 := by gcongr
  have hrw :
      (2 : ℝ) ^ (-((16 * q : ℕ) : ℝ) / 4) =
      1 / ((2 : ℝ) ^ q) ^ 4 := by
    have he : -((16 * q : ℕ) : ℝ) / 4 = -((4 * q : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [← pow_mul]
    simp only [mul_comm]
    ring
  rw [hrw]
  calc
    ((k / 2 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ q) ^ 4)
        ≤ (k : ℝ) / ((2 : ℝ) ^ q) ^ 4 := by
          rw [mul_one_div]
          gcongr
    _ ≤ (k : ℝ) / (k : ℝ) ^ 4 := by gcongr
    _ ≤ 1 / 32 := by
          have hkpow : (k : ℝ) ^ 4 ≥ 64 * (k : ℝ) := by
            nlinarith [sq_nonneg ((k : ℝ) - 4)]
          apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)).2
          nlinarith

/-- The doubled-mean Poisson lower tail is small beyond a fixed count. -/
private lemma paired_poisson_tail (n : ℕ) (hn : 256 ≤ n) :
    (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal ≤
      1 / 64 := by
  have hparam : Real.toNNReal (2 * (n : ℝ)) = 2 * (n : NNReal) := by
    apply NNReal.eq
    simp [Real.coe_toNNReal (2 * (n : ℝ)) (by positivity)]
  have htail :=
    Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poisson_two_n_lower_tail n
  have htailReal :
      (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal ≤
        Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
    rw [hparam]
    calc
      (poissonMeasure (2 * (n : NNReal)) (Set.Iio n)).toReal ≤
          (ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2)))).toReal :=
        ENNReal.toReal_mono (by simp) htail
      _ = _ := ENNReal.toReal_ofReal (Real.exp_nonneg _)
  have hc : (3 / 10 : ℝ) ≤ 1 - Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (64 : ℝ) ≤ (n : ℝ) * (1 - Real.log 2) := by nlinarith
  have hexp := Real.add_one_le_exp ((n : ℝ) * (1 - Real.log 2))
  have hh : Real.exp (-(n : ℝ) * (1 - Real.log 2)) =
      (Real.exp ((n : ℝ) * (1 - Real.log 2)))⁻¹ := by
    rw [show -(n : ℝ) * (1 - Real.log 2) =
      -((n : ℝ) * (1 - Real.log 2)) by ring, Real.exp_neg]
  rw [hh] at htailReal
  calc
    _ ≤ (Real.exp ((n : ℝ) * (1 - Real.log 2)))⁻¹ := htailReal
    _ ≤ 1 / 64 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- [There are a universal constant a > 0 and an alphabet threshold K ≥ 2 such that for every alphabet size k ≥ K and sample size n > k² there exist a pair count b ≥ 1 with 2b ≤ k, a moment degree L ≥ 1, a tilt t between 0 and 1, and a separation δ > 0 satisfying the comparison budget 100·(n/b)·t² ≤ L, the concentration budget 128·t² ≤ b·δ², the closeness budget b · 2^(−L/4) plus twice the probability that a Poisson count with mean 2n falls below n is at most 1/16, the separation bound δ ≤ t/(50L), and the rate bound δ² ≥ a · k / (n · log(e·k))](goal). -/
theorem exists_pairedLargeParameters :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ k n : ℕ, K ≤ k → k ^ 2 < n →
        ∃ b L : ℕ, ∃ t δ : ℝ,
          0 < b ∧ 1 ≤ L ∧ b * 2 ≤ k ∧
          0 ≤ t ∧ t ≤ 1 ∧ 0 < δ ∧
          100 * ((n : ℝ) / (b : ℝ)) * t ^ 2 ≤ (L : ℝ) ∧
          128 * t ^ 2 ≤ (b : ℝ) * δ ^ 2 ∧
          (b : ℝ) * (2 : ℝ) ^ (-(L : ℝ) / 4) +
            2 * (poissonMeasure (Real.toNNReal (2 * (n : ℝ))) (Set.Iio n)).toReal ≤
              1 / 16 ∧
          δ ≤ t * ((1 / 50 : ℝ) / (L : ℝ)) ∧
          a * ((k : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 * (k : ℝ)))) ≤ δ ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := eventually_paired_degree_scale
  refine ⟨1 / 100000000, by norm_num, max K₀ 256, by omega, ?_⟩
  intro k n hk hn
  have hkK : K₀ ≤ k := le_trans (Nat.le_max_left _ _) hk
  have hk256 : 256 ≤ k := le_trans (Nat.le_max_right _ _) hk
  have hk2 : 2 ≤ k := by omega
  have hk4 : 4 ≤ k := by omega
  have hn256 : 256 ≤ n := by
    have : k ^ 2 ≤ n := Nat.le_of_lt hn
    nlinarith
  let b : ℕ := k / 2
  let L : ℕ := 16 * (Nat.log2 k + 1)
  have hbposN : 0 < b := by dsimp [b]; omega
  have hLposN : 0 < L := by dsimp [L]; omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hbposN
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hscale : 320000 * (L : ℝ) ^ 2 ≤ (b : ℝ) := by
    simpa [L, b] using hK₀ k hkK
  have hLlog : (L : ℝ) ≤
      48 * Real.log (Real.exp 1 * (k : ℝ)) := by
    calc
      (L : ℝ) = 16 * ((Nat.log2 k + 1 : ℕ) : ℝ) := by simp [L]
      _ ≤ 16 * (3 * Real.log (Real.exp 1 * (k : ℝ))) := by
        gcongr
        exact paired_degree_log_bound k hk2
      _ = _ := by ring
  have hlogpos : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
    apply Real.log_pos
    have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    have hk1 : (1 : ℝ) ≤ k := by
      exact_mod_cast (show 1 ≤ k by omega)
    nlinarith [Real.exp_pos 1]
  let t : ℝ := Real.sqrt ((b : ℝ) * (L : ℝ) / (200 * (n : ℝ)))
  let δ : ℝ := t / (50 * (L : ℝ))
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = (b : ℝ) * (L : ℝ) / (200 * (n : ℝ)) := by
    exact Real.sq_sqrt (by positivity)
  have hδ_sq : δ ^ 2 = (b : ℝ) / (500000 * (n : ℝ) * (L : ℝ)) := by
    dsimp [δ]
    rw [div_pow, ht_sq]
    field_simp
    ring
  refine ⟨b, L, t, δ, hbposN, by omega, ?_, ht0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b]
    omega
  · have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLposN
    have hLb : (L : ℝ) ≤ b := by
      nlinarith [mul_nonneg hLpos.le (sub_nonneg.mpr hL1)]
    have hbK : (b : ℝ) ≤ k := by
      dsimp [b]
      exact_mod_cast (Nat.div_le_self k 2)
    have hnK : (k : ℝ) ^ 2 < n := by exact_mod_cast hn
    have hprod : (b : ℝ) * L ≤ (k : ℝ) ^ 2 := by
      calc
        (b : ℝ) * L ≤ b * b := by gcongr
        _ ≤ k * k := by gcongr
        _ = k ^ 2 := by ring
    have hs : t ^ 2 < 1 := by
      rw [ht_sq]
      apply (div_lt_iff₀ (by positivity : 0 < 200 * (n : ℝ))).2
      nlinarith
    nlinarith
  · dsimp [δ, t]
    positivity
  · rw [ht_sq]
    have hh : 100 * ((n : ℝ) / (b : ℝ)) *
        ((b : ℝ) * (L : ℝ) / (200 * (n : ℝ))) = (L : ℝ) / 2 := by
      field_simp
      ring
    rw [hh]
    linarith
  · rw [ht_sq, hδ_sq]
    have hmult := mul_le_mul_of_nonneg_right hscale
      (mul_nonneg hbpos.le hnpos.le)
    have hh : 128 * ((b : ℝ) * (L : ℝ)) / (200 * (n : ℝ)) ≤
        ((b : ℝ) * (b : ℝ)) / (500000 * (n : ℝ) * (L : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 200 * (n : ℝ))
        (by positivity : 0 < 500000 * (n : ℝ) * (L : ℝ))).2
      nlinarith [hmult]
    convert hh using 1 <;> ring
  · have htail₁ := paired_degree_tail k hk4
    have htail₂ := paired_poisson_tail n hn256
    dsimp [b, L]
    linarith
  · dsimp [δ]
    ring_nf
    exact le_refl _
  · rw [hδ_sq]
    have hbK : (k : ℝ) / 3 ≤ b := by
      dsimp [b]
      have hh : k ≤ 3 * (k / 2) := by omega
      have hhR : (k : ℝ) ≤ 3 * ((k / 2 : ℕ) : ℝ) := by
        exact_mod_cast hh
      linarith
    have hKL : (k : ℝ) * L ≤ 200 * (b : ℝ) *
        Real.log (Real.exp 1 * (k : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hLlog hkpos.le
      have h2 := mul_le_mul_of_nonneg_right hbK hlogpos.le
      nlinarith
    have hcross := mul_le_mul_of_nonneg_right hKL hnpos.le
    have he : (1 / 100000000 : ℝ) *
        ((k : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 * (k : ℝ)))) =
        (k : ℝ) / (100000000 * (n : ℝ) *
          Real.log (Real.exp 1 * (k : ℝ))) := by ring
    rw [he]
    apply (div_le_div_iff₀
      (by positivity : 0 < 100000000 * (n : ℝ) *
        Real.log (Real.exp 1 * (k : ℝ)))
      (by positivity : 0 < 500000 * (n : ℝ) * (L : ℝ))).2
    nlinarith

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
