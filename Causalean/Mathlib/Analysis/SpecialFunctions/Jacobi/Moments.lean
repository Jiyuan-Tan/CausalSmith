module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Beta
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Singular

/-!
# Weighted moments of the shifted Jacobi perturbation

The positive moments use the Rodrigues derivative and repeated integration
by parts on `[ε,1]`; the left endpoint is then removed.  The zeroth moment
has an explicit rising-factorial value and a Gamma-function restatement.
-/

public section

namespace Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi

open MeasureTheory intervalIntegral

/-- A [degree](hyp:k), [moment index](hyp:j), and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), give [interval integrability of the corresponding weighted shifted-Jacobi moment](goal).

For `α > 0`, every nonnegative-integer weighted moment of `h` is
integrable on `[0,1]`, including the singular weight with exponent `α-1`. -/
theorem h_weight_intervalIntegrable (k j : ℕ) (α : ℝ) (hα : 0 < α) :
    IntervalIntegrable
      (fun x : ℝ => x ^ (α - 1 + (j : ℝ)) * h k α x)
      volume 0 1 := by
  have hp : -1 < α - 1 + (j : ℝ) := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hh : Continuous (h k α) := by
    unfold h jacobiShifted
    fun_prop
  exact (intervalIntegrable_rpow' hp).mul_continuousOn hh.continuousOn

/-- A [degree](hyp:k), [moment index](hyp:j), and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), [a positive moment index](hyp:hj), and [an index no greater than the degree](hyp:hjk), give [a vanishing weighted shifted-Jacobi moment](goal).

For each `1 ≤ j ≤ k`, the `j`th weighted moment of the shifted Jacobi
perturbation vanishes. -/
theorem h_weighted_moment_zero (k j : ℕ) (α : ℝ) (hα : 0 < α)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    (∫ x in (0 : ℝ)..1, x ^ (α - 1 + (j : ℝ)) * h k α x) = 0 := by
  let p : ℝ → ℝ := fun x => x ^ (j - 1)
  let f := rodKernel k α
  let c := rising (α + 1) k
  have hc : c ≠ 0 := ne_of_gt (rising_pos (α + 1) k (by linarith))
  have hpow : ∀ x : ℝ, 0 < x →
      x ^ (α - 1 + (j : ℝ)) * h k α x =
        c⁻¹ * (p x * (deriv^[k] f) x) := by
    intro x hx
    have hexp : α - 1 + (j : ℝ) = ((j - 1 : ℕ) : ℝ) + α := by
      have hj' : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        simp [Nat.cast_sub hj]
      rw [hj']; ring
    rw [hexp, Real.rpow_add hx, Real.rpow_natCast]
    have hr := h_rodrigues k α x hα hx
    change x ^ α * h k α x = (deriv^[k] f) x / c at hr
    rw [mul_assoc, hr]
    dsimp [p]
    field_simp
  have hp : ∀ x : ℝ, ContDiffAt ℝ ⊤ p x := by
    intro x
    dsimp [p]
    fun_prop
  have hkzero : ∀ x : ℝ, (deriv^[k] p) x = 0 := by
    intro x
    rw [← iteratedDeriv_eq_iterate, show p = (fun x : ℝ => x ^ (j - 1)) from rfl,
      iteratedDeriv_pow]
    have hlt : j - 1 < k := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
  have hpleft (i : ℕ) : ContinuousAt (deriv^[i] p) 0 := by
    have heq : (deriv^[i] p) =
        fun x : ℝ => (j - 1).descFactorial i * x ^ (j - 1 - i) := by
      funext x
      rw [← iteratedDeriv_eq_iterate, show p = (fun x : ℝ => x ^ (j - 1)) from rfl,
        iteratedDeriv_pow]
    rw [heq]
    fun_prop
  have hleft (i : ℕ) (hik : i < k) :
      Filter.Tendsto (fun x : ℝ => (deriv^[i] f) x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    rodKernel_deriv_tendsto_zero k i α hik hα
  have hboundary : Filter.Tendsto
      (fun a : ℝ => ∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i * ((deriv^[i] p) a * (deriv^[k - 1 - i] f) a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht := (tendsto_finsetSum (Finset.range k) (fun i hi => by
      have hlt : k - 1 - i < k := by
        have hii : i < k := Finset.mem_range.mp hi
        omega
      simpa using ((hpleft i).tendsto.mono_left inf_le_left |>.mul
        (hleft (k - 1 - i) hlt) |>.const_mul ((-1 : ℝ) ^ i))))
    convert ht using 1 <;> first | rfl | simp
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact (div_le_iff₀ (by positivity)).2 (by simpa using hn)
  have hatend : Filter.Tendsto a Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [a, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Filter.Eventually.of_forall (fun n => ha n)
  have htrunc (n : ℕ) (hn : 0 < n) :
      (∫ x in a n..1, x ^ (α - 1 + (j : ℝ)) * h k α x) =
        -c⁻¹ * (∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
            (deriv^[k - 1 - i] f) (a n))) := by
    have hfp : ∀ x ∈ Set.Icc (a n) 1, ContDiffAt ℝ ⊤ f x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le (ha n) hx.1
      dsimp [f, rodKernel]
      exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hxpos)).mul (by fun_prop)
    have han : a n < 1 := by
      dsimp [a]
      have hn' : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hn
      exact (div_lt_iff₀ (by positivity)).2 (by simpa using hn')
    have hibp := integral_mul_iterated_deriv_with_boundary k (a n) 1 p f
      (fun x hx => hp x) hfp han
    simp only [hkzero, zero_mul, intervalIntegral.integral_zero, mul_zero, add_zero] at hibp
    have hright : (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i *
          ((deriv^[i] p) 1 * (deriv^[k - 1 - i] f) 1 -
           (deriv^[i] p) (a n) * (deriv^[k - 1 - i] f) (a n))) =
        -(∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
            (deriv^[k - 1 - i] f) (a n))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hlt : k - 1 - i < k := by
        have hii : i < k := Finset.mem_range.mp hi
        omega
      rw [rodKernel_deriv_one k (k - 1 - i) α hlt hα]
      ring
    rw [hright] at hibp
    calc
      _ = ∫ x in a n..1, c⁻¹ * (p x * (deriv^[k] f) x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (a n) 1 := by
          simpa only [Set.uIcc_of_le (ha1 n)] using hx
        exact hpow x (lt_of_lt_of_le (ha n) hx'.1)
      _ = c⁻¹ * (∫ x in a n..1, p x * (deriv^[k] f) x) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [hibp]; ring
  have hlim1 := tendsto_integral_one_div_nat
    (fun x : ℝ => x ^ (α - 1 + (j : ℝ)) * h k α x)
    (h_weight_intervalIntegrable k j α hα)
  have hlim2 : Filter.Tendsto
      (fun n : ℕ => -c⁻¹ * (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
          (deriv^[k - 1 - i] f) (a n)))) Filter.atTop (nhds 0) := by
    simpa using (hboundary.comp hatend).const_mul (-c⁻¹)
  have heq : (∫ x in (0 : ℝ)..1, x ^ (α - 1 + (j : ℝ)) * h k α x) = 0 :=
    tendsto_nhds_unique (hlim1.congr' (Filter.eventually_gt_atTop 0 |>.mono
      (fun n hn => htrunc n hn))) hlim2
  exact heq

/-- A [degree](hyp:k) and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), give [the exact zeroth weighted moment as a squared rising-factorial ratio](goal).

The zeroth weighted moment equals the square of a normalized
rising-factorial ratio. -/
theorem h_zeroth_moment_rising (k : ℕ) (α : ℝ) (hα : 0 < α) :
    α * (∫ x in (0 : ℝ)..1, x ^ (α - 1) * h k α x) =
      ((Nat.factorial k : ℝ) / rising (α + 1) k) ^ 2 := by
  let p : ℝ → ℝ := fun x => x⁻¹
  let f := rodKernel k α
  let c := rising (α + 1) k
  let g : ℝ → ℝ := fun x => x ^ (α - 1) * (1 - x) ^ k
  let q : ℝ → ℝ := fun x => x ^ (α - 1) * h k α x
  have hc : c ≠ 0 := ne_of_gt (rising_pos (α + 1) k (by linarith))
  have hp (x : ℝ) (hx : 0 < x) : ContDiffAt ℝ ⊤ p x := by
    dsimp [p]
    exact contDiffAt_inv ℝ (ne_of_gt hx)
  have hfp (x : ℝ) (hx : 0 < x) : ContDiffAt ℝ ⊤ f x := by
    dsimp [f, rodKernel]
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).mul (by fun_prop)
  have hq (x : ℝ) (hx : 0 < x) : q x = c⁻¹ * (p x * (deriv^[k] f) x) := by
    have hr := h_rodrigues k α x hα hx
    change x ^ α * h k α x = (deriv^[k] f) x / c at hr
    dsimp [q, p]
    rw [show α - 1 = α + (-1 : ℝ) by ring, Real.rpow_add hx,
      Real.rpow_neg_one]
    calc
      x ^ α * x⁻¹ * h k α x = x⁻¹ * (x ^ α * h k α x) := by ring
      _ = _ := by rw [hr]; ring
  have hder (x : ℝ) (hx : 0 < x) :
      (-1 : ℝ) ^ k * ((deriv^[k] p) x * f x) = (k.factorial : ℝ) * g x := by
    dsimp [p, f, rodKernel, g]
    rw [iter_deriv_inv]
    have he : ((-1 - (k : ℤ) : ℤ) : ℝ) + (α + (k : ℝ)) = α - 1 := by
      push_cast; ring
    rw [← Real.rpow_intCast]
    have hs : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (k.factorial : ℝ) *
          (x ^ ((-1 - (k : ℤ) : ℤ) : ℝ) * x ^ (α + (k : ℝ))) * (1 - x) ^ k := by ring
      _ = _ := by rw [hs, ← Real.rpow_add hx, he]; ring
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact (div_le_iff₀ (by positivity)).2 (by simpa using hn)
  have hatend : Filter.Tendsto a Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [a, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Filter.Eventually.of_forall (fun n => ha n)
  have hboundary : Filter.Tendsto
      (fun x : ℝ => ∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i * ((deriv^[i] p) x * (deriv^[k - 1 - i] f) x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [p, f] using (tendsto_finsetSum (Finset.range k) (fun i hi =>
      (inv_mul_rodKernel_deriv_tendsto_zero k i α hα (Finset.mem_range.mp hi)).const_mul
        ((-1 : ℝ) ^ i)))
  have htrunc (n : ℕ) (hn : 0 < n) :
      (∫ x in a n..1, q x) =
        -(c⁻¹ * (∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
            (deriv^[k - 1 - i] f) (a n)))) +
          c⁻¹ * (k.factorial : ℝ) * (∫ x in a n..1, g x) := by
    have han : a n < 1 := by
      dsimp [a]
      have hn' : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hn
      exact (div_lt_iff₀ (by positivity)).2 (by simpa using hn')
    have hibp := integral_mul_iterated_deriv_with_boundary k (a n) 1 p f
      (fun x hx => hp x (lt_of_lt_of_le (ha n) hx.1))
      (fun x hx => hfp x (lt_of_lt_of_le (ha n) hx.1)) han
    have hright : (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i *
          ((deriv^[i] p) 1 * (deriv^[k - 1 - i] f) 1 -
           (deriv^[i] p) (a n) * (deriv^[k - 1 - i] f) (a n))) =
        -(∑ i ∈ Finset.range k,
          (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
            (deriv^[k - 1 - i] f) (a n))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hlt : k - 1 - i < k := by
        have hii : i < k := Finset.mem_range.mp hi
        omega
      rw [show f = rodKernel k α from rfl, rodKernel_deriv_one k (k - 1 - i) α hlt hα]
      ring
    rw [hright] at hibp
    calc
      _ = c⁻¹ * (∫ x in a n..1, p x * (deriv^[k] f) x) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (a n) 1 := by
          simpa only [Set.uIcc_of_le (ha1 n)] using hx
        exact hq x (lt_of_lt_of_le (ha n) hx'.1)
      _ = _ := by
        rw [hibp, mul_add, ← intervalIntegral.integral_const_mul]
        have heq : (∫ x in a n..1, (-1 : ℝ) ^ k * ((deriv^[k] p) x * f x)) =
            (∫ x in a n..1, (k.factorial : ℝ) * g x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Set.Icc (a n) 1 := by
            simpa only [Set.uIcc_of_le (ha1 n)] using hx
          exact hder x (lt_of_lt_of_le (ha n) hx'.1)
        rw [heq, intervalIntegral.integral_const_mul]
        ring
  have hlimq := tendsto_integral_one_div_nat q (by
    simpa only [q, Nat.cast_zero, add_zero] using
      (h_weight_intervalIntegrable k 0 α hα))
  have hlimg := tendsto_integral_one_div_nat g (by
    dsimp [g]
    exact (intervalIntegrable_rpow' (by linarith : -1 < α - 1)).mul_continuousOn
      (by fun_prop))
  have hlimb : Filter.Tendsto
      (fun n : ℕ => -(c⁻¹ * (∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ i * ((deriv^[i] p) (a n) *
          (deriv^[k - 1 - i] f) (a n))))) Filter.atTop (nhds 0) := by
    simpa using ((hboundary.comp hatend).const_mul c⁻¹).neg
  have heq : (∫ x in (0 : ℝ)..1, q x) =
      c⁻¹ * (k.factorial : ℝ) * (∫ x in (0 : ℝ)..1, g x) := by
    apply tendsto_nhds_unique (hlimq.congr' (Filter.eventually_gt_atTop 0 |>.mono
      (fun n hn => htrunc n hn)))
    simpa only [a, Nat.cast_add, Nat.cast_one, zero_add, mul_assoc] using
      hlimb.add ((hlimg.const_mul (k.factorial : ℝ)).const_mul c⁻¹)
  rw [show (∫ x in (0 : ℝ)..1, x ^ (α - 1) * h k α x) =
    (∫ x in (0 : ℝ)..1, q x) from rfl, heq,
    show (∫ x in (0 : ℝ)..1, g x) =
      (k.factorial : ℝ) / (α * c) by
        simpa [g, c] using integral_rpow_mul_one_sub_pow k α hα]
  dsimp [c]
  have hr : rising (α + 1) k ≠ 0 := hc
  field_simp [hr]

/-- A [degree](hyp:k) and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), give [the rising factorial as a Gamma-function ratio](goal).

The rising factorial at `α+1` is the Gamma quotient
`Γ(α+k+1)/Γ(α+1)` for positive `α`. -/
theorem rising_eq_gamma_ratio (k : ℕ) (α : ℝ) (hα : 0 < α) :
    rising (α + 1) k =
      Real.Gamma (α + (k : ℝ) + 1) / Real.Gamma (α + 1) := by
  have hΓ : Real.Gamma (α + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  induction k with
  | zero =>
      simp [rising, hΓ]
  | succ k ih =>
      rw [rising, ascPochhammer_succ_eval]
      change rising (α + 1) k * (α + 1 + (k : ℝ)) = _
      rw [ih]
      have hpos : α + (k : ℝ) + 1 ≠ 0 := by positivity
      have hrec := Real.Gamma_add_one hpos
      have heq : α + ((k + 1 : ℕ) : ℝ) + 1 =
          (α + (k : ℝ) + 1) + 1 := by push_cast; ring
      rw [heq, hrec]
      ring

/-- A [degree](hyp:k) and [positive shape parameter](hyp:α), with [parameter positivity](hyp:hα), give [the exact zeroth weighted moment as a squared Gamma-function ratio](goal).

The zeroth weighted moment is the square of the Gamma ratio
`Γ(α+1)Γ(k+1)/Γ(k+α+1)`. -/
theorem h_zeroth_moment_gamma (k : ℕ) (α : ℝ) (hα : 0 < α) :
    α * (∫ x in (0 : ℝ)..1, x ^ (α - 1) * h k α x) =
      (Real.Gamma (α + 1) * Real.Gamma ((k : ℝ) + 1) /
        Real.Gamma ((k : ℝ) + α + 1)) ^ 2 := by
  rw [h_zeroth_moment_rising k α hα, rising_eq_gamma_ratio k α hα]
  have hΓ₁ : Real.Gamma (α + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hΓ₂ : Real.Gamma (α + (k : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  rw [Real.Gamma_nat_eq_factorial]
  have harg : (k : ℝ) + α + 1 = α + (k : ℝ) + 1 := by ring
  rw [harg]
  field_simp

end Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
