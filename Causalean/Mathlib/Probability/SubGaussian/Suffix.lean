module
public import Causalean.Mathlib.Probability.SubGaussian.DyadicPartition
public import Causalean.Mathlib.Probability.SubGaussian.Prefix
public import Causalean.Mathlib.Probability.SubGaussian.Series
public import Causalean.Mathlib.Probability.SubGaussian.SuffixBlock

/-!
# Integral of the polynomially decaying Gaussian suffix

The second deterministic ingredient controls all coordinates beyond a given
positive index when their variance proxies decay by a power of the index.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory

/-- For [a decay exponent](hyp:α) satisfying [strict positivity](hyp:hα), [there
is a positive constant depending only on the exponent such that, for every number of
terms `N`, starting index `m ≥ 1` and scale `σ > 0`, the clipped suffix sum
`min(1, Σ 2·exp(-t²/(2σ²(m/(k+1))^α)))` over the indices `k < N` with `k+1 ≥ m` is
integrable in `t` over the positive half-line with integral at most the constant times
`σ·√(1 + log m)`](goal).

Proof strategy: split `k+1 ≥ m` into dyadic blocks
`2^j m ≤ k+1 < 2^(j+1) m`.  Block `j` has at most `2^j m`
members and every proxy there is at most `σ² 2^(-αj)`.
Use `dyadic_suffix_partition` to exchange the index and block sums.
Apply `gaussian_suffix_block_integral` blockwise, then use
`weighted_dyadic_geometric_bound` to sum the block contributions.  To handle
the clipped sum of blocks,
use `min 1 (∑ x_j) ≤ ∑ min 1 x_j`; finite `N` avoids an infinite
measurability issue, while a uniform summable bound proves integrability.
For `L = 2^j m`, the block scale is
`((m : ℝ) / L)^(α/2) = (exp (-α * log 2 / 2))^j`.
Since `m ≥ 1` and `log 2 ≤ 1`, the remaining factor obeys
`sqrt (1 + log L) ≤ (j+1) * sqrt (1 + log m)`.
Use `integrable_finsetSum` and `integral_finsetSum` for the finite block
majorant, and `setIntegral_mono_ae` for the final comparison. -/
theorem decaying_gaussian_suffix_integral (α : ℝ) (hα : 0 < α) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (N m : ℕ) (σ : ℝ), 1 ≤ m → 0 < σ →
        let g : ℝ → ℝ := fun t =>
          min 1 (∑ k : Fin N,
            if m ≤ k.val + 1 then
              2 * Real.exp (-(t ^ 2) /
                (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))
            else 0)
        IntegrableOn g (Set.Ioi (0 : ℝ)) volume ∧
          ∫ t in Set.Ioi (0 : ℝ), g t ≤
            Cα * σ * Real.sqrt (1 + Real.log (m : ℝ)) := by
  obtain ⟨C, hC, hblock⟩ := gaussian_suffix_block_integral α hα
  obtain ⟨D, hD, hgeom⟩ := weighted_dyadic_geometric_bound α hα
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro N m σ hm hσ
  dsimp
  let f (k : Fin N) (t : ℝ) : ℝ :=
    2 * Real.exp (-(t ^ 2) /
      (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))
  let B (j : ℕ) (t : ℝ) : ℝ :=
    ∑ k : Fin N,
      if 2 ^ j * m ≤ k.val + 1 ∧ k.val + 1 < 2 * (2 ^ j * m)
      then f k t else 0
  let F (j : ℕ) (t : ℝ) : ℝ := min 1 (B j t)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmreal
  have hsqrt : 0 ≤ Real.sqrt (1 + Real.log (m : ℝ)) :=
    Real.sqrt_nonneg _
  have hBi (j : ℕ) : IntegrableOn (F j) (Set.Ioi (0 : ℝ)) volume := by
    have hmL : m ≤ 2 ^ j * m := by
      have hp : 1 ≤ 2 ^ j := by exact Nat.one_le_pow j 2 (by omega)
      exact Nat.le_mul_of_pos_left m hp
    exact (hblock N m (2 ^ j * m) σ hm hmL hσ).1
  have hBbound (j : ℕ) :
      (∫ t in Set.Ioi (0 : ℝ), F j t) ≤
        C * σ * ((m : ℝ) / (2 ^ j * m : ℝ)) ^ (α / 2) *
          Real.sqrt (1 + Real.log (2 ^ j * m : ℝ)) := by
    have hmL : m ≤ 2 ^ j * m := by
      have hp : 1 ≤ 2 ^ j := by exact Nat.one_le_pow j 2 (by omega)
      exact Nat.le_mul_of_pos_left m hp
    simpa only [F, B, f, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (hblock N m (2 ^ j * m) σ hm hmL hσ).2
  have hscale (j : ℕ) :
      ((m : ℝ) / (2 ^ j * m : ℝ)) ^ (α / 2) =
        (Real.exp (-(α * Real.log 2 / 2))) ^ j := by
    have hmpos : (0 : ℝ) < m := by linarith
    have hp : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hcast : (2 ^ j * m : ℝ) = (2 : ℝ) ^ j * m := by norm_cast
    have hratio : (m : ℝ) / (2 ^ j * m : ℝ) = ((2 : ℝ) ^ j)⁻¹ := by
      rw [hcast]
      field_simp
    rw [hratio, Real.rpow_def_of_pos (inv_pos.mpr hp), Real.log_inv,
      Real.log_pow, ← Real.exp_nat_mul]
    congr 1
    ring
  have hlogscale (j : ℕ) :
      Real.sqrt (1 + Real.log (2 ^ j * m : ℝ)) ≤
        ((j : ℝ) + 1) * Real.sqrt (1 + Real.log (m : ℝ)) := by
    have hmpos : (0 : ℝ) < m := by linarith
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      convert (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)) using 1 <;> norm_num
    have hlogeq : Real.log (2 ^ j * m : ℝ) =
        (j : ℝ) * Real.log 2 + Real.log (m : ℝ) := by
      rw [Real.log_mul (by positivity) hmpos.ne', Real.log_pow]
    have harg : 0 ≤ 1 + Real.log (2 ^ j * m : ℝ) := by
      rw [hlogeq]
      have : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      nlinarith
    have hsq : Real.sqrt (1 + Real.log (m : ℝ)) ^ 2 =
        1 + Real.log (m : ℝ) := Real.sq_sqrt (by linarith)
    have hsq' : Real.sqrt (1 + Real.log (2 ^ j * m : ℝ)) ^ 2 =
        1 + Real.log (2 ^ j * m : ℝ) := Real.sq_sqrt harg
    have hnonneg : 0 ≤ ((j : ℝ) + 1) * Real.sqrt (1 + Real.log (m : ℝ)) := by
      positivity
    nlinarith [mul_nonneg hj (sub_nonneg.mpr hlog2),
      mul_nonneg hj hlogm, sq_nonneg (j : ℝ)]
  have hpointNonneg (t : ℝ) (j : ℕ) : 0 ≤ B j t := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro k _
    split <;> positivity [f]
  have hminsum (t : ℝ) (s : Finset ℕ) :
      min 1 (∑ j ∈ s, B j t) ≤ ∑ j ∈ s, F j t := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [F]
    | @insert j s hjs ih =>
      simp only [Finset.sum_insert hjs]
      have ha := hpointNonneg t j
      have hb : 0 ≤ ∑ i ∈ s, B i t := by
        exact Finset.sum_nonneg (fun i _ => hpointNonneg t i)
      have hmin : min 1 (B j t + ∑ i ∈ s, B i t) ≤
          min 1 (B j t) + min 1 (∑ i ∈ s, B i t) := by
        rcases le_total 1 (B j t) with h | h
        · have hc : 1 ≤ B j t + ∑ i ∈ s, B i t := by linarith
          rw [min_eq_left hc, min_eq_left h]
          have : 0 ≤ min 1 (∑ i ∈ s, B i t) := le_min (by norm_num) hb
          linarith
        · rcases le_total 1 (∑ i ∈ s, B i t) with h' | h'
          · have : 1 ≤ B j t + ∑ i ∈ s, B i t := by linarith
            rw [min_eq_left this, min_eq_left h']
            have : 0 ≤ min 1 (B j t) := le_min (by norm_num) ha
            linarith
          · rw [min_eq_right h, min_eq_right h']
            exact min_le_right _ _
      dsimp [F] at ih ⊢
      linarith
  have hpoint (t : ℝ) :
      min 1 (∑ k : Fin N,
        if m ≤ k.val + 1 then f k t else 0) ≤
        ∑ j ∈ Finset.range (N + 1), F j t := by
    rw [dyadic_suffix_partition N m hm (fun k => f k t)]
    exact hminsum t (Finset.range (N + 1))
  have hterm (k : Fin N) : Integrable (f k) volume := by
    have hb : 0 < (1 / (2 * σ ^ 2 *
        ((m : ℝ) / (k.val + 1 : ℝ)) ^ α) : ℝ) := by positivity
    have hi := (integrable_exp_neg_mul_sq hb).const_mul (2 : ℝ)
    convert hi using 1
    ext t
    dsimp [f]
    congr 1
    ring
  have hraw : IntegrableOn
      (fun t : ℝ => ∑ k : Fin N,
        if m ≤ k.val + 1 then f k t else 0)
      (Set.Ioi (0 : ℝ)) volume := by
    apply Integrable.integrableOn
    apply integrable_finsetSum
    intro k _
    split
    · exact hterm k
    · exact integrable_zero _ _ _
  have hgi : IntegrableOn
      (fun t : ℝ => min 1 (∑ k : Fin N,
        if m ≤ k.val + 1 then f k t else 0))
      (Set.Ioi (0 : ℝ)) volume := by
    apply hraw.mono'
    · exact (aestronglyMeasurable_const.inf hraw.aestronglyMeasurable)
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        apply le_min (by norm_num)
        apply Finset.sum_nonneg
        intro k _
        split <;> positivity [f])]
      exact min_le_right _ _
  have hsumInt : IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.range (N + 1), F j t)
      (Set.Ioi (0 : ℝ)) volume := by
    apply integrable_finsetSum
    intro j _
    exact hBi j
  refine ⟨hgi, ?_⟩
  calc
    (∫ t in Set.Ioi (0 : ℝ),
      min 1 (∑ k : Fin N, if m ≤ k.val + 1 then f k t else 0)) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          ∑ j ∈ Finset.range (N + 1), F j t :=
      setIntegral_mono_ae hgi hsumInt (Filter.Eventually.of_forall hpoint)
    _ = ∑ j ∈ Finset.range (N + 1),
          ∫ t in Set.Ioi (0 : ℝ), F j t := by
      exact integral_finsetSum _ (fun j _ => hBi j)
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          C * σ * (((j : ℝ) + 1) *
            (Real.exp (-(α * Real.log 2 / 2))) ^ j) *
              Real.sqrt (1 + Real.log (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ C * σ * ((m : ℝ) / (2 ^ j * m : ℝ)) ^ (α / 2) *
            Real.sqrt (1 + Real.log (2 ^ j * m : ℝ)) := hBbound j
        _ ≤ C * σ * (((j : ℝ) + 1) *
              (Real.exp (-(α * Real.log 2 / 2))) ^ j) *
                Real.sqrt (1 + Real.log (m : ℝ)) := by
          rw [hscale]
          have hp : 0 ≤ C * σ * (Real.exp (-(α * Real.log 2 / 2))) ^ j := by
            positivity
          nlinarith [hlogscale j]
    _ = C * σ * (∑ j ∈ Finset.range (N + 1),
          ((j : ℝ) + 1) *
            (Real.exp (-(α * Real.log 2 / 2))) ^ j) *
              Real.sqrt (1 + Real.log (m : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (C * D) * σ * Real.sqrt (1 + Real.log (m : ℝ)) := by
      have hp : 0 ≤ C * σ * Real.sqrt (1 + Real.log (m : ℝ)) := by
        positivity
      nlinarith [hgeom (N + 1)]

end Causalean.Mathlib.Probability.SubGaussian
