module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightFactorialSquare

/-! Poisson moments and integrability of the factorial-overlap kernel. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- The overlap polynomial is integrable under every Poisson count law. -/
lemma factorialOverlap_integrable (rate : ℝ≥0) (j q : ℕ) :
    Integrable (fun N : ℕ => factorialOverlap N j q) (poissonMeasure rate) := by
  unfold factorialOverlap
  apply integrable_finset_sum
  intro b hb
  apply Integrable.const_mul
  simpa only [falling] using
    Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
      rate (j + q + 2 - b)

/-- Equation (30)'s one-count overlap moment, before inserting the polynomial
coefficients. -/
lemma factorialOverlap_integral (rate : ℝ≥0) (j q : ℕ) :
    (∫ N : ℕ, factorialOverlap N j q ∂poissonMeasure rate) =
      ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
          (rate : ℝ) ^ (j + q + 2 - b) := by
  unfold factorialOverlap
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [integral_const_mul]
    change _ * (∫ a : ℕ, (a.descFactorial (j + q + 2 - b) : ℝ)
      ∂poissonMeasure rate) = _
    rw [Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment]
  · intro b hb
    apply Integrable.const_mul
    simpa only [falling] using
      Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
        rate (j + q + 2 - b)

/-- The combinatorial overlap coefficient has the factorial-series envelope
used in equation (31). -/
lemma overlapCoefficient_le_pow_div_factorial (K j q b : ℕ)
    (hj : j + 1 ≤ K) (hq : q + 1 ≤ K) :
    ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) ≤
      (K : ℝ) ^ (2 * b) / (Nat.factorial b : ℝ) := by
  have hjd : (j + 1).descFactorial b ≤ K ^ b :=
    ((j + 1).descFactorial_le_pow b).trans
      (Nat.pow_le_pow_left hj b)
  have hqd : (q + 1).descFactorial b ≤ K ^ b :=
    ((q + 1).descFactorial_le_pow b).trans
      (Nat.pow_le_pow_left hq b)
  have hnat :
      (Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b) *
          Nat.factorial b ≤ K ^ (2 * b) := by
    calc
      _ = (j + 1).descFactorial b * (q + 1).descFactorial b := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ ≤ K ^ b * K ^ b := Nat.mul_le_mul hjd hqd
      _ = K ^ (2 * b) := by rw [← pow_add]; congr 1 <;> omega
  rw [le_div_iff₀' (by positivity : (0 : ℝ) < Nat.factorial b)]
  have hnat' : Nat.factorial b *
      (Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b) ≤
        K ^ (2 * b) := by
    simpa [mul_comm] using hnat
  exact_mod_cast hnat'

/-- Equation (31): after the `4096 K` normalization, every overlap sum is
dominated by the exponential series at `K / 4096`. -/
lemma normalized_overlap_sum_le_exp (K j q : ℕ) (hK : 1 ≤ K)
    (hj : j + 1 ≤ K) (hq : q + 1 ≤ K) :
    (∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) /
          (4096 * (K : ℝ)) ^ b) ≤
      Real.exp ((K : ℝ) / 4096) := by
  calc
    _ ≤ ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        (((K : ℝ) / 4096) ^ b / (Nat.factorial b : ℝ)) := by
      apply Finset.sum_le_sum
      intro b hb
      have hden : 0 < (4096 * (K : ℝ)) ^ b := by positivity
      calc
        _ ≤ ((K : ℝ) ^ (2 * b) / (Nat.factorial b : ℝ)) /
            (4096 * (K : ℝ)) ^ b :=
          div_le_div_of_nonneg_right (overlapCoefficient_le_pow_div_factorial K j q b hj hq)
            hden.le
        _ = ((K : ℝ) / 4096) ^ b / (Nat.factorial b : ℝ) := by
          have hKr : (K : ℝ) ≠ 0 := by positivity
          rw [show 2 * b = b + b by omega, pow_add, mul_pow]
          rw [div_pow]
          field_simp [hKr]
    _ ≤ Real.exp ((K : ℝ) / 4096) := by
      exact Real.sum_le_exp_of_nonneg (by positivity)
        (min (j + 1) (q + 1) + 1)

/-- Pointwise form of the exact factorial resummation in equation (30). -/
lemma count_sq_FK_sq_eq_overlap_sum (K : ℕ) (R : ℝ) (N : ℕ) :
    (N : ℝ) ^ 2 * FK K R N ^ 2 =
      ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
        (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) * factorialOverlap N j q := by
  have hoverlap (j q : ℕ) :
      factorialOverlap N j q =
        (N : ℝ) ^ 2 * (falling (N - 1) j : ℝ) * (falling (N - 1) q : ℝ) := by
    unfold factorialOverlap
    norm_num only [Nat.cast_mul]
    rw [← audit_descFactorial_overlap,
      ← natCast_mul_falling_pred, ← natCast_mul_falling_pred]
    ring
  simp_rw [hoverlap]
  unfold FK
  rw [show (∑ ell ∈ Finset.range (K - 1),
      gCoeff K ell * (falling (N - 1) ell : ℝ) / R ^ ell) ^ 2 =
      (∑ ell ∈ Finset.range (K - 1),
        gCoeff K ell * (falling (N - 1) ell : ℝ) / R ^ ell) *
      (∑ ell ∈ Finset.range (K - 1),
        gCoeff K ell * (falling (N - 1) ell : ℝ) / R ^ ell) by ring]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The squared light count polynomial is integrable under a Poisson law. -/
lemma count_sq_FK_sq_integrable (K : ℕ) (R : ℝ) (rate : ℝ≥0) :
    Integrable (fun N : ℕ => (N : ℝ) ^ 2 * FK K R N ^ 2)
      (poissonMeasure rate) := by
  rw [show (fun N : ℕ => (N : ℝ) ^ 2 * FK K R N ^ 2) =
      fun N : ℕ => ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
        (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) * factorialOverlap N j q by
    funext N
    exact count_sq_FK_sq_eq_overlap_sum K R N]
  apply integrable_finset_sum
  intro j hj
  apply integrable_finset_sum
  intro q hq
  exact (factorialOverlap_integrable rate j q).const_mul _

/-- Equation (30), as an exact finite double sum. -/
lemma count_sq_FK_sq_integral (K : ℕ) (R : ℝ) (rate : ℝ≥0) :
    (∫ N : ℕ, (N : ℝ) ^ 2 * FK K R N ^ 2 ∂poissonMeasure rate) =
      ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
        (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) *
          ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
            ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
              (rate : ℝ) ^ (j + q + 2 - b) := by
  rw [show (fun N : ℕ => (N : ℝ) ^ 2 * FK K R N ^ 2) =
      fun N : ℕ => ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
        (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) * factorialOverlap N j q by
    funext N
    exact count_sq_FK_sq_eq_overlap_sum K R N]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_const_mul, factorialOverlap_integral]
    · intro q hq
      exact (factorialOverlap_integrable rate j q).const_mul _
  · intro j hj
    apply integrable_finset_sum
    intro q hq
    exact (factorialOverlap_integrable rate j q).const_mul _

private lemma overlap_power_le (K j q b : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hj : j + 1 ≤ K) (hq : q + 1 ≤ K)
    (hb : b < min (j + 1) (q + 1) + 1) :
    x ^ (j + q + 2 - b) ≤ x * (1 + x) ^ (2 * K) := by
  have hbj : b ≤ j + 1 := by omega
  have hpos : 1 ≤ j + q + 2 - b := by omega
  have htop : j + q + 2 - b ≤ 2 * K := by omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hpos
  rw [he]
  rw [Nat.add_comm 1 e, pow_succ]
  rw [mul_comm (x ^ e) x]
  apply mul_le_mul_of_nonneg_left _ hx
  have hxbase : x ≤ 1 + x := by linarith
  have hbase : 1 ≤ 1 + x := by linarith
  exact (pow_le_pow_left₀ hx hxbase e).trans
    (pow_le_pow_right₀ hbase (by omega))

/-- The inner overlap sum in (30), after scaling by `R = 4096 K`, has the
uniform envelope used in equation (32). -/
lemma scaled_overlap_sum_le (K j q : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hK : 1 ≤ K) (hj : j + 1 ≤ K) (hq : q + 1 ≤ K) :
    (∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
          (4096 * (K : ℝ) * x) ^ (j + q + 2 - b)) /
        (4096 * (K : ℝ)) ^ (j + q) ≤
      (4096 * (K : ℝ)) ^ 2 * x * (1 + x) ^ (2 * K) *
        Real.exp ((K : ℝ) / 4096) := by
  let R : ℝ := 4096 * (K : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hpoint (b : ℕ) (hb : b ∈ Finset.range (min (j + 1) (q + 1) + 1)) :
      (((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
          (R * x) ^ (j + q + 2 - b)) / R ^ (j + q) ≤
        R ^ 2 * x * (1 + x) ^ (2 * K) *
          (((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) /
            R ^ b) := by
    have hb' : b < min (j + 1) (q + 1) + 1 := Finset.mem_range.mp hb
    have hble : b ≤ j + q + 2 := by omega
    have hpow := overlap_power_le K j q b x hx hj hq hb'
    have hc : 0 ≤
        ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) := by
      positivity
    have hscaled :
        ((R * x) ^ (j + q + 2 - b)) / R ^ (j + q) =
          R ^ 2 * (x ^ (j + q + 2 - b) / R ^ b) := by
      rw [mul_pow]
      field_simp [ne_of_gt hR]
      have hexp : (j + q + 2 - b) + b = (j + q) + 2 := by omega
      have hRp : R ^ (j + q + 2 - b) * R ^ b = R ^ (j + q) * R ^ 2 := by
        rw [← pow_add, ← pow_add, hexp]
      calc
        R ^ (j + q + 2 - b) * x ^ (j + q + 2 - b) * R ^ b =
            x ^ (j + q + 2 - b) *
              (R ^ (j + q + 2 - b) * R ^ b) := by ring
        _ = _ := by rw [hRp]; ring
    rw [mul_div_assoc, hscaled]
    calc
      _ ≤ ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
          (R ^ 2 * (x * (1 + x) ^ (2 * K) / R ^ b)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact div_le_div_of_nonneg_right hpow (by positivity)
      _ = R ^ 2 * x * (1 + x) ^ (2 * K) *
          (((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) /
            R ^ b) := by ring
  rw [Finset.sum_div]
  calc
    _ ≤ ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        R ^ 2 * x * (1 + x) ^ (2 * K) *
          (((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) /
            R ^ b) := Finset.sum_le_sum (fun b hb => hpoint b hb)
    _ = R ^ 2 * x * (1 + x) ^ (2 * K) *
        (∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
          ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) /
            R ^ b) := by rw [Finset.mul_sum]
    _ ≤ R ^ 2 * x * (1 + x) ^ (2 * K) * Real.exp ((K : ℝ) / 4096) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [R] using normalized_overlap_sum_le_exp K j q hK hj hq)
        (by positivity)

/-- Equation (32): the exact overlap resummation yields an exponential, rather
than superexponential, second-moment envelope. -/
lemma poisson_count_sq_FK_sq_le (K : ℕ) (x : ℝ) (hx : 0 ≤ x) (hK : 1 ≤ K) :
    (∫ N : ℕ, (N : ℝ) ^ 2 * FK K (4096 * (K : ℝ)) N ^ 2
        ∂poissonMeasure (Real.toNNReal (4096 * (K : ℝ) * x))) ≤
      (4096 * (K : ℝ)) ^ 2 * x * (1 + x) ^ (2 * K) *
        (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 *
          Real.exp ((K : ℝ) / 4096) := by
  let R : ℝ := 4096 * (K : ℝ)
  let rate : ℝ≥0 := Real.toNNReal (R * x)
  have hR : 0 < R := by dsimp [R]; positivity
  have hrate : (rate : ℝ) = R * x := by
    simp [rate, max_eq_left (mul_nonneg hR.le hx)]
  let E : ℝ := R ^ 2 * x * (1 + x) ^ (2 * K) * Real.exp ((K : ℝ) / 4096)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hterm (j : ℕ) (hjmem : j ∈ Finset.range (K - 1))
      (q : ℕ) (hqmem : q ∈ Finset.range (K - 1)) :
      (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) *
          ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
            ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
              (rate : ℝ) ^ (j + q + 2 - b) ≤
        |gCoeff K j| * |gCoeff K q| * E := by
    have hj : j + 1 ≤ K := by
      have := Finset.mem_range.mp hjmem
      omega
    have hq : q + 1 ≤ K := by
      have := Finset.mem_range.mp hqmem
      omega
    let S : ℝ := ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
      ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
        (R * x) ^ (j + q + 2 - b)
    have hS : 0 ≤ S := by
      dsimp [S]
      positivity
    have hnorm : S / R ^ (j + q) ≤ E := by
      simpa only [S, R, E] using scaled_overlap_sum_le K j q x hx hK hj hq
    have hnorm0 : 0 ≤ S / R ^ (j + q) := div_nonneg hS (by positivity)
    have hg : gCoeff K j * gCoeff K q ≤ |gCoeff K j| * |gCoeff K q| := by
      calc
        _ ≤ |gCoeff K j * gCoeff K q| := le_abs_self _
        _ = _ := abs_mul _ _
    rw [hrate]
    change (gCoeff K j * gCoeff K q / (R ^ j * R ^ q)) * S ≤ _
    rw [← pow_add]
    calc
      (gCoeff K j * gCoeff K q / R ^ (j + q)) * S =
          (gCoeff K j * gCoeff K q) * (S / R ^ (j + q)) := by ring
      _ ≤ (|gCoeff K j| * |gCoeff K q|) * (S / R ^ (j + q)) :=
        mul_le_mul_of_nonneg_right hg hnorm0
      _ ≤ (|gCoeff K j| * |gCoeff K q|) * E :=
        mul_le_mul_of_nonneg_left hnorm (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := rfl
  rw [show Real.toNNReal (4096 * (K : ℝ) * x) = rate by rfl,
    show 4096 * (K : ℝ) = R by rfl, count_sq_FK_sq_integral]
  calc
    _ ≤ ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
        |gCoeff K j| * |gCoeff K q| * E := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro q hq
      exact hterm j hj q hq
    _ = E * (∑ j ∈ Finset.range (K - 1), |gCoeff K j|) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by dsimp [E, R]; ring

/-- On the guarded event, the audit coefficient is exactly the normalized sum
of the two factorial polynomials from equation (34). -/
lemma lightFactorialCoefficient_eq_FK {n : ℕ} (rho : ℝ) (N0 N1 : ℕ)
    (hn : 0 < n) (h0 : N0 ≠ 0) (h1 : N1 ≠ 0) :
    lightFactorialCoefficient n rho N0 N1 =
      (FK (degree n rho) (blockMean n * lightScale n rho) N0 +
        FK (degree n rho) (blockMean n * lightScale n rho) N1) /
          (lightScale n rho * blockMean n ^ 2) := by
  let K := degree n rho
  let B := lightScale n rho
  let m := blockMean n
  have hB : B ≠ 0 := (lightScale_pos n rho hn).ne'
  have hm : m ≠ 0 := by
    have hpost : 0 < n - n / 2 := by omega
    dsimp [m, blockMean, postPilotSize, pilotSize]
    positivity
  rw [lightFactorialCoefficient, if_neg (not_or.mpr ⟨h0, h1⟩)]
  unfold FK
  rw [add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow]
  field_simp [hB, hm]
  ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
