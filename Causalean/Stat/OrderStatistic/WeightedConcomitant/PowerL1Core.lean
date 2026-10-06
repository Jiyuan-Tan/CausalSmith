module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerCurvature
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformOrderCDF

/-!
# L1 approximation of the power density by finite Bernstein cells

The hinge-cell kernel is an adjacent order-statistic CDF. Combined with a
curvature representation of a real power, this reduces the small-power L1
bound to the centered adjacent-mixture moment bound. The endpoint and
large-power cases use unit-density identities.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- At an adjacent threshold `(k+δ)/N`, multiplying a hinge-cell mass by
`N` gives zero before cell `k`, `1-δ` in cell `k`, and one after it. -/
theorem hingeCell_at_adjacent {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (j : Fin N) :
    (N : ℝ) * hingeCell N ((k + δ) / N) j =
      if (j : ℕ) < k then 0 else if (j : ℕ) = k then 1 - δ else 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
  rcases hδ with ⟨hδ0, hδ1⟩
  rw [hingeCell_eq_piecewise hN]
  rcases lt_trichotomy (j : ℕ) k with hjk | hjk | hkj
  · have hjk' : ((j : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hjk
    have hleft : ¬ (k + δ) / (N : ℝ) ≤ ((j : ℕ) : ℝ) / (N : ℝ) := by
      rw [div_le_div_iff_of_pos_right hNr]
      linarith
    simp only [if_pos hjk, if_neg hleft]
    split_ifs with hmid
    · have hmid' : (k : ℝ) + δ ≤ ((j : ℕ) : ℝ) + 1 := by
        exact (div_le_div_iff_of_pos_right hNr).mp hmid
      have heq : (k : ℝ) + δ = ((j : ℕ) : ℝ) + 1 := by linarith
      rw [← heq]
      ring
    · ring
  · subst k
    have hmid : ((j : ℕ) : ℝ) + δ ≤ ((j : ℕ) : ℝ) + 1 := by linarith
    have hmid' : (((j : ℕ) : ℝ) + δ) / (N : ℝ) ≤
        (((j : ℕ) : ℝ) + 1) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNr).mpr hmid
    simp only [lt_self_iff_false, ↓reduceIte, if_pos hmid']
    split_ifs with hleft
    · have hδeq : δ = 0 := by
        have := (div_le_div_iff_of_pos_right hNr).mp hleft
        linarith
      simp [hδeq, hNne]
    · field_simp
      ring
  · have hkj' : (k : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hkj
    have hleft : ((k : ℝ) + δ) / (N : ℝ) ≤
        ((j : ℕ) : ℝ) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNr).mpr (by linarith)
    simp [not_lt.mpr (Nat.le_of_lt hkj), ne_of_gt hkj, hleft, hNne]

/-- The Bernstein kernel of an adjacent hinge is the convex combination of
the two binomial upper tails with cutoffs `k` and `k+1`. -/
theorem bernsteinCell_hinge_eq_binomial_tails {N k : ℕ}
    (hN : 0 < N) (hk : k < N) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) :
    bernsteinCell N (hingeCell N ((k + δ) / N)) u =
      (1 - δ) * (∑ j ∈ Finset.Icc k (N - 1),
        (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j)) +
      δ * (∑ j ∈ Finset.Icc (k + 1) (N - 1),
        (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j)) := by
  let f : ℕ → ℝ := fun j =>
    (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j)
  have hsets (a : ℕ) : Finset.Icc a (N - 1) =
      (Finset.range N).filter (fun j => a ≤ j) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  have htail (a : ℕ) :
      (∑ j ∈ Finset.range N, if a ≤ j then f j else 0) =
        ∑ j ∈ Finset.Icc a (N - 1), f j := by
    rw [hsets, Finset.sum_filter]
  have hcoeff (j : ℕ) :
      (if j < k then (0 : ℝ) else if j = k then 1 - δ else 1) =
        (if k ≤ j then 1 - δ else 0) +
          (if k + 1 ≤ j then δ else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, show ¬ k ≤ j by omega, show ¬ k + 1 ≤ j by omega]
    · subst j
      simp
    · have hkj : k + 1 ≤ j := Nat.succ_le_of_lt h
      simp [show ¬ j < k by omega, show j ≠ k by omega, hkj,
        Nat.le_of_lt h]
  calc
    bernsteinCell N (hingeCell N ((k + δ) / N)) u =
        ∑ j : Fin N,
          ((if (j : ℕ) < k then (0 : ℝ)
            else if (j : ℕ) = k then 1 - δ else 1) * f (j : ℕ)) := by
      unfold bernsteinCell
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hingeCell_at_adjacent hN hk hδ j]
      dsimp [f]
      ring
    _ = ∑ j ∈ Finset.range N,
          ((if j < k then (0 : ℝ) else if j = k then 1 - δ else 1) * f j) :=
      by simpa only using (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (if j < k then (0 : ℝ) else if j = k then 1 - δ else 1) * f j) N)
    _ = ∑ j ∈ Finset.range N,
          ((if k ≤ j then 1 - δ else 0) * f j +
            (if k + 1 ≤ j then δ else 0) * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff j]
      ring
    _ = (1 - δ) * (∑ j ∈ Finset.Icc k (N - 1), f j) +
          δ * (∑ j ∈ Finset.Icc (k + 1) (N - 1), f j) := by
      calc
        _ = ∑ j ∈ Finset.range N,
              ((1 - δ) * (if k ≤ j then f j else 0) +
                δ * (if k + 1 ≤ j then f j else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [ite_mul, mul_ite, zero_mul, mul_zero]
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            htail k, htail (k + 1)]
    _ = _ := rfl

/-- For a [positive sample size](hyp:hN), [adjacent cell](hyp:hk), and
 [interpolation fraction](hyp:hδ), at an [interior point](hyp:hu), the Bernstein density of the corresponding
 hinge increments is [the CDF of the adjacent order-statistic mixture](goal)
 at each interior point of the unit interval. -/
theorem bernsteinCell_hinge_eq_adjacent_cdf {N k : ℕ}
    (hN : 0 < N) (hk : k < N) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    bernsteinCell N (hingeCell N ((k + δ) / N)) u =
      ((adjacentOrderMix N k δ) (Set.Iic u)).toReal := by
  -- A hinge increment is 0 below cell k, (1-δ)/N in cell k, and
  -- 1/N above it. The Bernstein binomial tail is the CDF of the
  -- kth order statistic of N-1 uniforms; mix the adjacent tails.
  -- At δ=1 and u=1 the deterministic upper endpoint creates a CDF jump,
  -- so this exact pointwise identity is stated on the open interval.
  let ν := iidSample uniform01 (N - 1)
  let μ₀ : Measure ℝ := ν.map (fun x => if h : k = 0 then (0 : ℝ)
    else if h' : k ≤ N - 1 then sortedSample (N - 1) x ⟨k - 1, by omega⟩
    else 1)
  let μ₁ : Measure ℝ := ν.map (fun x => if h : k + 1 = N then (1 : ℝ)
    else if h' : k < N - 1 then sortedSample (N - 1) x ⟨k, h'⟩
    else 1)
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν, iidSample]
    infer_instance
  letI := hν
  haveI : IsFiniteMeasure μ₀ := by
    dsimp [μ₀]
    exact Measure.isFiniteMeasure_map ν _
  haveI : IsFiniteMeasure μ₁ := by
    dsimp [μ₁]
    exact Measure.isFiniteMeasure_map ν _
  haveI : IsFiniteMeasure ((ENNReal.ofReal (1 - δ)) • μ₀) :=
    Measure.smul_finite μ₀ (by simp)
  haveI : IsFiniteMeasure ((ENNReal.ofReal δ) • μ₁) :=
    Measure.smul_finite μ₁ (by simp)
  have hδ₀ : 0 ≤ δ := hδ.1
  have hδ₁ : 0 ≤ 1 - δ := by linarith [hδ.2]
  have hmix : ((adjacentOrderMix N k δ) (Set.Iic u)).toReal =
      (1 - δ) * (μ₀ (Set.Iic u)).toReal +
        δ * (μ₁ (Set.Iic u)).toReal := by
    change (((ENNReal.ofReal (1 - δ)) • μ₀ +
      (ENNReal.ofReal δ) • μ₁) (Set.Iic u)).toReal = _
    rw [← Measure.real, measureReal_add_apply,
      measureReal_ennreal_smul_apply,
      measureReal_ennreal_smul_apply]
    simp [Measure.real, ENNReal.toReal_ofReal hδ₀,
      ENNReal.toReal_ofReal hδ₁]
  have hL : (μ₀ (Set.Iic u)).toReal =
      ∑ j ∈ Finset.Icc k (N - 1),
        (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j) := by
    by_cases hk₀ : k = 0
    · subst k
      have hs : (∑ j ∈ Finset.Icc 0 (N - 1),
          (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j)) = 1 := by
        have hI : Finset.Icc 0 (N - 1) = Finset.range ((N - 1) + 1) := by
          ext j
          simp only [Finset.mem_Icc, zero_le, true_and, Finset.mem_range]
          omega
        rw [hI]
        calc
          _ = ∑ j ∈ Finset.range (N - 1 + 1),
              u ^ j * (1 - u) ^ (N - 1 - j) * (Nat.choose (N - 1) j : ℝ) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (u + (1 - u)) ^ (N - 1) := by rw [add_pow]
          _ = 1 := by simp
      simp [μ₀, Measure.map_const, hs, hu.1.le]
    · have hkn : k ≤ N - 1 := by omega
      have hr : k - 1 < N - 1 := by omega
      have hks : k - 1 + 1 = k := by omega
      simp only [μ₀, hk₀, hkn, dite_false, dite_true]
      rw [uniform_sorted_cdf_eq_binomial_tail ⟨k - 1, hr⟩ ⟨hu.1.le, hu.2.le⟩]
      have h1u : 0 ≤ 1 - u := by linarith [hu.2]
      rw [hks, ENNReal.toReal_ofReal (Finset.sum_nonneg (by
        intro j hj
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hu.1.le _))
          (pow_nonneg h1u _)))]
  have hU : (μ₁ (Set.Iic u)).toReal =
      ∑ j ∈ Finset.Icc (k + 1) (N - 1),
        (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j) := by
    by_cases htop : k + 1 = N
    · have hs : (∑ j ∈ Finset.Icc (k + 1) (N - 1),
          (Nat.choose (N - 1) j : ℝ) * u ^ j * (1 - u) ^ (N - 1 - j)) = 0 := by
        have : Finset.Icc (k + 1) (N - 1) = ∅ := by
          apply Finset.Icc_eq_empty_of_lt
          omega
        simp [this]
      have heq : μ₁ = ν.map (fun _ => (1 : ℝ)) := by simp [μ₁, htop]
      rw [heq, Measure.map_const]
      simp [hs, Set.mem_Iic, not_le.mpr hu.2]
    · have hkn : k < N - 1 := by omega
      have hks : k + 1 ≤ N - 1 := by omega
      simp only [μ₁, htop, hkn, dite_false, dite_true]
      rw [uniform_sorted_cdf_eq_binomial_tail ⟨k, hkn⟩ ⟨hu.1.le, hu.2.le⟩]
      have h1u : 0 ≤ 1 - u := by linarith [hu.2]
      rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (by
        intro j hj
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hu.1.le _))
          (pow_nonneg h1u _)))]
  rw [bernsteinCell_hinge_eq_binomial_tails hN hk hδ u, hmix, hL, hU]

/-- Every [threshold](hyp:ht) in the unit interval [lies in an adjacent cell](goal) of
a [positive sample size](hyp:hN), including the right endpoint by taking the
last cell and interpolation fraction one. -/
theorem unit_threshold_eq_adjacent {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k : ℕ, ∃ δ : ℝ,
      k < N ∧ δ ∈ Set.Icc (0 : ℝ) 1 ∧ t = (k + δ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
  by_cases htop : t = 1
  · refine ⟨N - 1, 1, by omega, by norm_num, ?_⟩
    rw [htop]
    have hlast : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      exact_mod_cast (by omega : N - 1 + 1 = N)
    rw [hlast]
    exact (div_self hNne).symm
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 htop
    let k := Nat.floor ((N : ℝ) * t)
    let δ := (N : ℝ) * t - k
    have hNt0 : 0 ≤ (N : ℝ) * t := mul_nonneg hNr.le ht.1
    have hklo : (k : ℝ) ≤ (N : ℝ) * t := Nat.floor_le hNt0
    have hkhi : (N : ℝ) * t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkN : k < N := by
      have hkr : (k : ℝ) < N := lt_of_le_of_lt hklo (mul_lt_of_lt_one_right hNr htlt)
      exact_mod_cast hkr
    refine ⟨k, δ, hkN, ⟨by dsimp [δ]; linarith, by dsimp [δ]; linarith⟩, ?_⟩
    dsimp [δ]
    field_simp
    ring

/-- For a [unit-interval threshold](hyp:ht), [the Bernstein kernel of its hinge
cells approximates the threshold step function in L1 with error at most
`sqrt (2*t/N)`](goal) for a [positive sample size](hyp:hN). -/
theorem bernsteinCell_hinge_indicator_L1 {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |bernsteinCell N (hingeCell N t) u -
        (if t ≤ u then (1 : ℝ) else 0)| ∂volume) ≤
      Real.sqrt (2 * t / N) := by
  obtain ⟨k, δ, hk, hδ, rfl⟩ := unit_threshold_eq_adjacent hN ht
  have hEq :
      (∫ u in Set.Icc (0 : ℝ) 1,
        |bernsteinCell N (hingeCell N ((k + δ) / N)) u -
          (if (k + δ) / N ≤ u then (1 : ℝ) else 0)| ∂volume) =
      (∫ u in Set.Icc (0 : ℝ) 1,
        |((adjacentOrderMix N k δ) (Set.Iic u)).toReal -
          (if (k + δ) / N ≤ u then (1 : ℝ) else 0)| ∂volume) := by
    simp only [integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp
    rw [bernsteinCell_hinge_eq_adjacent_cdf hN hk hδ hu]
  rw [hEq]
  exact
    _root_.Causalean.Stat.OrderStatistic.WeightedConcomitant.adjacentOrderMix_indicator_L1_le_sqrt_two_t_over_N
      hN hk hδ

/-- For a [power strictly greater than one](hyp:hs) and [unit-interval point](hyp:hu),
 [the power density is a constant minus its integrated curvature thresholds](goal). -/
theorem powerDensity_eq_sub_curvature_integral {s u : ℝ}
    (hs : 1 < s) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    powerDensity s u = s -
      ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * (if t ≤ u then (1 : ℝ) else 0) ∂volume := by
  have hind : (fun t : ℝ => powerCurvature s t * (if t ≤ u then (1 : ℝ) else 0)) =
      (Set.Iic u).indicator (powerCurvature s) := by
    funext t
    by_cases ht : t ≤ u <;> simp [Set.indicator, ht]
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Iic u = Set.Icc 0 u := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨ht0, _⟩, htu⟩
      exact ⟨ht0, htu⟩
    · rintro ⟨ht0, htu⟩
      exact ⟨⟨ht0, htu.trans hu.2⟩, htu⟩
  rw [hind, setIntegral_indicator measurableSet_Iic, hset,
    integral_powerCurvature_Icc hs hu]
  ring

/-- For a positive sample size and a real power above one, each power cell
mass is its constant-density mass minus the curvature-weighted hinge cell. -/
theorem powerCell_eq_sub_curvature_hinge_integral {N : ℕ}
    (hN : 0 < N) {s : ℝ} (hs : 1 < s) (j : Fin N) :
    powerCell N s j = s / N -
      ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * hingeCell N t j ∂volume := by
  let a : ℝ := (j : ℝ) / N
  let b : ℝ := (((j : ℕ) + 1 : ℝ) / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : a ≤ b := by
    dsimp [a, b]
    apply div_le_div_of_nonneg_right _ hNr.le
    linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    apply (div_le_one hNr).2
    exact_mod_cast j.isLt
  have hgeom (t : ℝ) :
      (∫ u in Set.Ioc a b, if t ≤ u then (1 : ℝ) else 0 ∂volume) =
        hingeCell N t j := by
    have hstep : (∫ u in Set.Ioc a b, if t ≤ u then (1 : ℝ) else 0 ∂volume) =
        (∫ u in Set.Ioc a b,
          (Set.Ioi t).indicator (fun _ => (1 : ℝ)) u ∂volume) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (volume.ae_ne t)] with u hu
      by_cases htu : t < u
      · simp [Set.indicator, htu, htu.le]
      · have : ¬ t ≤ u := by
          intro h
          rcases h.eq_or_lt with he | hl
          · exact hu he.symm
          · exact htu hl
        simp [Set.indicator, htu, this]
    rw [hstep, setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi]
    simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc]
    change max (b - max a t) 0 = max (b - t) 0 - max (a - t) 0
    rcases le_total t a with h | h
    · rw [max_eq_left h]
      simp [max_eq_left (by linarith : 0 ≤ b - a),
        max_eq_left (by linarith : 0 ≤ b - t),
        max_eq_left (by linarith : 0 ≤ a - t)]
    · rcases le_total t b with h' | h'
      · rw [max_eq_right h]
        simp [max_eq_left (by linarith : 0 ≤ b - t),
          max_eq_right (by linarith : a - t ≤ 0)]
      · rw [max_eq_right h]
        simp [max_eq_right (by linarith : b - t ≤ 0),
          max_eq_right (by linarith : a - t ≤ 0)]
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (s - 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hr' : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (s - 2)) volume 0 1 := by
    convert (hr.comp_sub_left 1).symm using 1 <;> norm_num
  have hq : Integrable (powerCurvature s) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    change IntervalIntegrable (fun t : ℝ => s * (s - 1) * (1 - t) ^ (s - 2)) volume 0 1
    exact hr'.const_mul (s * (s - 1))
  let μ := volume.restrict (Set.Ioc a b)
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hqprod : Integrable (fun z : ℝ × ℝ => powerCurvature s z.2) (μ.prod ν) := by
    exact hq.comp_snd μ
  have hF : Integrable
      (fun z : ℝ × ℝ => powerCurvature s z.2 * if z.2 ≤ z.1 then (1 : ℝ) else 0)
      (μ.prod ν) := by
    apply hqprod.mul_bdd (c := 1)
    · exact ((measurable_const.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const).aestronglyMeasurable)
    · filter_upwards [] with z
      split_ifs <;> simp
  have hswap :
      (∫ u in Set.Ioc a b, ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume ∂volume) =
      (∫ t in Set.Icc (0 : ℝ) 1, ∫ u in Set.Ioc a b,
        powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume ∂volume) := by
    exact integral_integral_swap (μ := μ) (ν := ν) hF
  have hinner_int : Integrable
      (fun u : ℝ => ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume) μ :=
    hF.integral_prod_left
  have hcell : powerCell N s j =
      ∫ u in Set.Ioc a b, powerDensity s u ∂volume := by
    rw [powerCell_eq_integral hN hs.le j, intervalIntegral.integral_of_le hab]
    rfl
  have hconst : (∫ u in Set.Ioc a b, s ∂volume) = s / N := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab]
    simp only [smul_eq_mul]
    dsimp [a, b]
    field_simp
    ring
  calc
    powerCell N s j = ∫ u in Set.Ioc a b, powerDensity s u ∂volume := hcell
    _ = ∫ u in Set.Ioc a b,
          s - ∫ t in Set.Icc (0 : ℝ) 1,
            powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact powerDensity_eq_sub_curvature_integral hs
        ⟨ha0.trans hu.1.le, hu.2.trans hb1⟩
    _ = s / N - ∫ u in Set.Ioc a b, ∫ t in Set.Icc (0 : ℝ) 1,
          powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume ∂volume := by
      rw [integral_sub (integrable_const _) hinner_int, hconst]
    _ = s / N - ∫ t in Set.Icc (0 : ℝ) 1, ∫ u in Set.Ioc a b,
          powerCurvature s t * if t ≤ u then (1 : ℝ) else 0 ∂volume ∂volume := by
      rw [hswap]
    _ = s / N - ∫ t in Set.Icc (0 : ℝ) 1,
          powerCurvature s t * hingeCell N t j ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_const_mul, hgeom]

/-- For a [positive sample size](hyp:hN), [power strictly above one](hyp:hs), and [evaluation point](hyp:u),
 [the Bernstein power kernel is a constant minus the curvature-weighted
 Bernstein hinge kernel](goal). -/
theorem bernsteinCell_power_eq_sub_curvature_hinge_integral {N : ℕ}
    (hN : 0 < N) {s : ℝ} (hs : 1 < s) (u : ℝ) :
    bernsteinCell N (powerCell N s) u = s -
      ∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * bernsteinCell N (hingeCell N t) u ∂volume := by
  -- Integrate the preceding hinge representation over each cell, then use
  -- finite-sum linearity and the binomial partition of unity. This is valid
  -- for every real u because the Bernstein basis sum is identically one.
  let b (j : Fin N) : ℝ :=
    (Nat.choose (N - 1) (j : ℕ) : ℝ) * u ^ (j : ℕ) *
      (1 - u) ^ (N - 1 - (j : ℕ))
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hsum : (∑ j : Fin N, b j) = 1 := by
    have hpow := add_pow u (1 - u) (N - 1)
    rw [show N - 1 + 1 = N by omega, ← Fin.sum_univ_eq_sum_range] at hpow
    convert hpow.symm using 1
    · apply Finset.sum_congr rfl
      intro j hj
      dsimp [b]
      ring
    · ring
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (s - 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hr' : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (s - 2)) volume 0 1 := by
    convert (hr.comp_sub_left 1).symm using 1 <;> norm_num
  have hq : Integrable (powerCurvature s) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    change IntervalIntegrable (fun t : ℝ => s * (s - 1) * (1 - t) ^ (s - 2)) volume 0 1
    exact hr'.const_mul (s * (s - 1))
  have hbound (j : Fin N) (t : ℝ) : ‖hingeCell N t j‖ ≤ (1 : ℝ) / N := by
    have hNr' : (0 : ℝ) < N := by exact_mod_cast hN
    have hw : (((j : ℕ) : ℝ) + 1) / N - ((j : ℕ) : ℝ) / N = (1 : ℝ) / N := by
      ring
    rw [hingeCell_eq_piecewise hN]
    split_ifs with ha hb
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · have hlt : ((j : ℕ) : ℝ) / N < t := lt_of_not_ge ha
      have hnonneg : 0 ≤ (((j : ℕ) : ℝ) + 1) / N - t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      linarith
    · simp [hNr'.le]
  have hint (j : Fin N) : Integrable
      (fun t : ℝ => powerCurvature s t * hingeCell N t j)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply hq.mul_bdd (c := (1 : ℝ) / N)
    · have hc : Continuous (hingeCell N · j) := by
        unfold hingeCell
        fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [] with t
      exact hbound j t
  have hint' (j : Fin N) : Integrable
      (fun t : ℝ => powerCurvature s t * hingeCell N t j * b j)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hint j).mul_const _
  have hswap :
      (∑ j : Fin N, (∫ t in Set.Icc (0 : ℝ) 1,
        powerCurvature s t * hingeCell N t j ∂volume) * b j) =
      ∫ t in Set.Icc (0 : ℝ) 1,
        ∑ j : Fin N, powerCurvature s t * hingeCell N t j * b j ∂volume := by
    rw [integral_finsetSum (s := Finset.univ) (fun j hj => hint' j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const]
  calc
    bernsteinCell N (powerCell N s) u =
        N * ∑ j : Fin N, powerCell N s j * b j := by
      unfold bernsteinCell
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [b]
      ring
    _ = N * ∑ j : Fin N,
          (s / N - ∫ t in Set.Icc (0 : ℝ) 1,
            powerCurvature s t * hingeCell N t j ∂volume) * b j := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [powerCell_eq_sub_curvature_hinge_integral hN hs j]
    _ = N * (s / N * (∑ j : Fin N, b j) -
          ∑ j : Fin N, (∫ t in Set.Icc (0 : ℝ) 1,
            powerCurvature s t * hingeCell N t j ∂volume) * b j) := by
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = s - ∫ t in Set.Icc (0 : ℝ) 1,
          powerCurvature s t * bernsteinCell N (hingeCell N t) u ∂volume := by
      rw [hsum, mul_one, hswap, mul_sub, mul_div_cancel₀ s hNr]
      rw [← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [bernsteinCell, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [b]
      ring

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
