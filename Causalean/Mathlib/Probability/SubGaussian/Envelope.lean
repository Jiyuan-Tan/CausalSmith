module
public import Causalean.Mathlib.Probability.SubGaussian.Prefix
public import Causalean.Mathlib.Probability.SubGaussian.Suffix

/-!
# Deterministic ordered Gaussian-tail envelope

An integrable one-dimensional majorant controls the sum of Gaussian tails with
variance proxies capped at `a²` and decaying like `b²(k+1)^(-α)`.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory

/-- For [a decay exponent](hyp:α) satisfying [strict positivity](hyp:hα),
[there is a positive constant depending only on the exponent such that, for every
number of terms `N` and all positive cap scale `a` and initial scale `b`, the clipped
tail sum `min(1, Σ_{k<N} 2·exp(-t²/(2·min(a², b²(k+1)^(-α)))))` is integrable in `t` over
the positive half-line with integral at most the constant times
`a·√(1 + max(0, log((b/a)^(2/α))))`](goal).

Proof strategy: put `m = max 1 (ceil ((b/a)^(2/α)))`.  Split indices at `m`,
where the cap `a²` crosses `b²(k+1)^(-α)`.  Bound the low-index part by
`clipped_gaussian_integral` with `m` terms and scale `a`.  For the suffix,
`b²(k+1)^(-α) ≤ a² (m/(k+1))^α`; use
`decaying_gaussian_suffix_integral` with scale `a`.  Combine the two clipped
tail integrals and compare `log m` with the target logarithm.  Specifically,
`m ≤ 1 + max 1 ((b/a)^(2/α)) ≤ 2 * max 1 ((b/a)^(2/α))`, so
`1 + log m ≤ 2 * (1 + max 0 (log ((b/a)^(2/α))))`.  The same comparison
controls both the prefix and suffix bounds.  Pointwise use
`min 1 (x+y) ≤ min 1 x + min 1 y` for nonnegative partial sums; prove
integrability of the original function from its finite Gaussian sum.  The
empty sum at `N = 0` is zero. -/
theorem ordered_gaussian_tail_integral (α : ℝ) (hα : 0 < α) :
    ∃ Kα : ℝ, 0 < Kα ∧
      ∀ (N : ℕ) (a b : ℝ), 0 < a → 0 < b →
        let g : ℝ → ℝ := fun t =>
          min 1 (∑ k : Fin N,
            2 * Real.exp (-(t ^ 2) /
              (2 * min (a ^ 2)
                (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)))))
        IntegrableOn g (Set.Ioi (0 : ℝ)) volume ∧
          ∫ t in Set.Ioi (0 : ℝ), g t ≤
            Kα * a * Real.sqrt
              (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨C, hC, hprefix⟩ := clipped_gaussian_integral
  obtain ⟨D, hD, hsuffix⟩ := decaying_gaussian_suffix_integral α hα
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro N a b ha hb
  dsimp
  let R : ℝ := (b / a) ^ (2 / α)
  let m : ℕ := ⌈R⌉₊
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr hR
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hRm : R ≤ (m : ℝ) := Nat.le_ceil R
  have hmR : (m : ℝ) ≤ 2 * max 1 R := by
    have hceil : (m : ℝ) < R + 1 := Nat.ceil_lt_add_one hR.le
    rcases le_total R 1 with h | h
    · rw [max_eq_left h]
      linarith
    · rw [max_eq_right h]
      linarith
  have hlogm : 1 + Real.log (m : ℝ) ≤
      2 * (1 + max 0 (Real.log R)) := by
    have hmax : (0 : ℝ) < max 1 R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hlog : Real.log (m : ℝ) ≤ Real.log (2 * max 1 R) :=
      Real.log_le_log hmpos hmR
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      exact this
    have hlogmax : Real.log (max 1 R) = max 0 (Real.log R) := by
      rcases le_total R 1 with h | h
      · rw [max_eq_left h, Real.log_one, max_eq_left]
        exact Real.log_nonpos (le_of_lt hR) h
      · rw [max_eq_right h, max_eq_right]
        exact Real.log_nonneg h
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmax.ne', hlogmax] at hlog
    have : 0 ≤ max 0 (Real.log R) := le_max_left _ _
    linarith
  have hsqrt : Real.sqrt (1 + Real.log (m : ℝ)) ≤
      2 * Real.sqrt (1 + max 0 (Real.log R)) := by
    have hnonneg : 0 ≤ 1 + Real.log (m : ℝ) := by
      have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
      linarith
    have harg : 0 ≤ 1 + max 0 (Real.log R) := by
      have : 0 ≤ max 0 (Real.log R) := le_max_left _ _
      linarith
    have hs := Real.sqrt_le_sqrt hlogm
    have hsq : Real.sqrt (2 * (1 + max 0 (Real.log R))) ≤
        2 * Real.sqrt (1 + max 0 (Real.log R)) := by
      have h1 := Real.sq_sqrt harg
      have h2 := Real.sq_sqrt (show 0 ≤ 2 * (1 + max 0 (Real.log R)) by positivity)
      nlinarith [Real.sqrt_nonneg (2 * (1 + max 0 (Real.log R))),
        Real.sqrt_nonneg (1 + max 0 (Real.log R))]
    exact hs.trans hsq
  have hRpow : R ^ α = (b / a) ^ (2 : ℕ) := by
    dsimp [R]
    rw [← Real.rpow_mul (div_pos hb ha).le]
    have he : (2 / α) * α = 2 := by field_simp
    rw [he]
    norm_cast
  have hba : b ^ 2 ≤ a ^ 2 * (m : ℝ) ^ α := by
    have hrpow := Real.rpow_le_rpow hR.le hRm hα.le
    have hdiv : (b / a) ^ (2 : ℕ) = b ^ 2 / a ^ 2 := by ring
    rw [hRpow, hdiv] at hrpow
    have ha2 : 0 < a ^ 2 := by positivity
    apply (div_le_iff₀ ha2).mp at hrpow
    nlinarith
  have hvar (k : Fin N) :
      b ^ 2 * (k.val + 1 : ℝ) ^ (-α) ≤
        a ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α := by
    have hk : (0 : ℝ) < (k.val + 1 : ℝ) := by positivity
    rw [Real.div_rpow hmpos.le hk.le, Real.rpow_neg hk.le]
    have hpow : 0 ≤ ((k.val + 1 : ℝ) ^ α)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_right hba hpow
    have heq : a ^ 2 * (m : ℝ) ^ α * ((k.val + 1 : ℝ) ^ α)⁻¹ =
        a ^ 2 * ((m : ℝ) ^ α / (k.val + 1 : ℝ) ^ α) := by ring
    rw [heq] at hh
    exact hh
  let f (k : Fin N) (t : ℝ) : ℝ :=
    2 * Real.exp (-(t ^ 2) /
      (2 * min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))))
  let P (t : ℝ) : ℝ :=
    min 1 (2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2)))
  let S (t : ℝ) : ℝ :=
    min 1 (∑ k : Fin N,
      if m ≤ k.val + 1 then
        2 * Real.exp (-(t ^ 2) /
          (2 * a ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))
      else 0)
  let g (t : ℝ) : ℝ := min 1 (∑ k : Fin N, f k t)
  have hfpos (k : Fin N) :
      0 < min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) := by
    apply lt_min <;> positivity
  have hfint (k : Fin N) : Integrable (f k) volume := by
    have hh : 0 < (1 / (2 * min (a ^ 2)
        (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))) : ℝ) := by
      positivity [hfpos k]
    have hi := (integrable_exp_neg_mul_sq hh).const_mul (2 : ℝ)
    convert hi using 1
    ext t
    dsimp [f]
    congr 1
    ring_nf
  have hgint : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    have hraw : IntegrableOn (fun t : ℝ => ∑ k : Fin N, f k t)
        (Set.Ioi (0 : ℝ)) volume :=
      (integrable_finsetSum _ (fun k _ => hfint k)).integrableOn
    apply hraw.mono'
    · exact (aestronglyMeasurable_const.inf hraw.aestronglyMeasurable)
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        dsimp [g]
        apply le_min (by norm_num)
        exact Finset.sum_nonneg (fun k _ => by positivity [f]))]
      exact min_le_right _ _
  obtain ⟨hPint, hPbound⟩ := hprefix m a hm ha
  obtain ⟨hSint, hSbound⟩ := hsuffix N m a hm ha
  have hPint' : IntegrableOn P (Set.Ioi (0 : ℝ)) volume := hPint
  have hSint' : IntegrableOn S (Set.Ioi (0 : ℝ)) volume := hSint
  let T : Finset (Fin N) := Finset.univ.filter (fun k => k.val + 1 < m)
  have hTcard : T.card ≤ m := by
    have hc : T.card ≤ (Finset.range m).card := by
      apply Finset.card_le_card_of_injOn (fun k : Fin N => k.val)
      · intro k hk
        have hkm : k.val + 1 < m := (Finset.mem_filter.mp hk).2
        simpa using (show k.val < m by omega)
      · intro k _ j _ heq
        exact Fin.ext heq
    simpa using hc
  have hprefixTerm (k : Fin N) (t : ℝ) :
      f k t ≤ 2 * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
    have hd : 0 < 2 * min (a ^ 2)
        (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) := by
      positivity [hfpos k]
    have ha2 : 0 < 2 * a ^ 2 := by positivity
    have hden : 2 * min (a ^ 2)
        (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) ≤ 2 * a ^ 2 := by
      nlinarith [min_le_left (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))]
    have he : -(t ^ 2) /
        (2 * min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))) ≤
          -(t ^ 2) / (2 * a ^ 2) := by
      apply (div_le_div_iff₀ hd ha2).2
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hden)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
  have hprefixPoint (t : ℝ) :
      min 1 (∑ k : Fin N, if k.val + 1 < m then f k t else 0) ≤ P t := by
    have heq : (∑ k : Fin N, if k.val + 1 < m then f k t else 0) =
        ∑ k ∈ T, f k t := by simp [T, Finset.sum_filter]
    rw [heq]
    have hsum : (∑ k ∈ T, f k t) ≤
        2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
      calc
        _ ≤ ∑ _k ∈ T, 2 * Real.exp (-(t ^ 2) / (2 * a ^ 2)) :=
          Finset.sum_le_sum (fun k _ => hprefixTerm k t)
        _ = (T.card : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * a ^ 2))) := by simp
        _ ≤ 2 * (m : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
          have hc : (T.card : ℝ) ≤ m := by exact_mod_cast hTcard
          nlinarith [Real.exp_pos (-(t ^ 2) / (2 * a ^ 2))]
    exact min_le_min_left _ hsum
  have hsuffixTerm (k : Fin N) (t : ℝ) :
      f k t ≤ 2 * Real.exp (-(t ^ 2) /
        (2 * a ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) := by
    have hd : 0 < 2 * min (a ^ 2)
        (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) := by
      positivity [hfpos k]
    have hd2 : 0 < 2 * a ^ 2 *
        ((m : ℝ) / (k.val + 1 : ℝ)) ^ α := by positivity
    have hden : 2 * min (a ^ 2)
        (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) ≤
          2 * a ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α := by
      nlinarith [min_le_right (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)), hvar k]
    have he : -(t ^ 2) /
        (2 * min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))) ≤
          -(t ^ 2) /
            (2 * a ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α) := by
      apply (div_le_div_iff₀ hd hd2).2
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hden)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
  have hsuffixPoint (t : ℝ) :
      min 1 (∑ k : Fin N, if m ≤ k.val + 1 then f k t else 0) ≤ S t := by
    apply min_le_min_left
    apply Finset.sum_le_sum
    intro k _
    split
    · exact hsuffixTerm k t
    · exact le_refl 0
  have hpoint (t : ℝ) : g t ≤ P t + S t := by
    have hsplit : (∑ k : Fin N, f k t) =
        (∑ k : Fin N, if k.val + 1 < m then f k t else 0) +
          (∑ k : Fin N, if m ≤ k.val + 1 then f k t else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val + 1 < m
      · have hnot : ¬m ≤ k.val + 1 := by omega
        simp [hk, hnot]
      · have hle : m ≤ k.val + 1 := by omega
        simp [hk, hle]
    dsimp [g]
    rw [hsplit]
    have hmin (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
        min 1 (x + y) ≤ min 1 x + min 1 y := by
      rcases le_total 1 x with h | h
      · rw [min_eq_left h, min_eq_left (by linarith : 1 ≤ x + y)]
        have : 0 ≤ min 1 y := le_min (by norm_num) hy
        linarith
      · rcases le_total 1 y with h' | h'
        · rw [min_eq_left h', min_eq_left (by linarith : 1 ≤ x + y)]
          have : 0 ≤ min 1 x := le_min (by norm_num) hx
          linarith
        · rw [min_eq_right h, min_eq_right h']
          exact min_le_right _ _
    have hx : 0 ≤ (∑ k : Fin N, if k.val + 1 < m then f k t else 0) := by
      apply Finset.sum_nonneg
      intro k _
      split <;> positivity [f]
    have hy : 0 ≤ (∑ k : Fin N, if m ≤ k.val + 1 then f k t else 0) := by
      apply Finset.sum_nonneg
      intro k _
      split <;> positivity [f]
    exact (hmin _ _ hx hy).trans (add_le_add (hprefixPoint t) (hsuffixPoint t))
  have hp : (∫ t in Set.Ioi (0 : ℝ), P t) ≤
      C * a * Real.sqrt (1 + Real.log (m : ℝ)) := hPbound
  have hs : (∫ t in Set.Ioi (0 : ℝ), S t) ≤
      D * a * Real.sqrt (1 + Real.log (m : ℝ)) := hSbound
  refine ⟨hgint, ?_⟩
  change (∫ t in Set.Ioi (0 : ℝ), g t) ≤
    2 * (C + D) * a * Real.sqrt (1 + max 0 (Real.log R))
  calc
    (∫ t in Set.Ioi (0 : ℝ), g t) ≤
        ∫ t in Set.Ioi (0 : ℝ), P t + S t :=
      setIntegral_mono_ae hgint (hPint'.add hSint')
        (Filter.Eventually.of_forall hpoint)
    _ = (∫ t in Set.Ioi (0 : ℝ), P t) +
        (∫ t in Set.Ioi (0 : ℝ), S t) :=
      integral_add hPint' hSint'
    _ ≤ (C + D) * a * Real.sqrt (1 + Real.log (m : ℝ)) := by
      linarith [hp, hs]
    _ ≤ 2 * (C + D) * a * Real.sqrt (1 + max 0 (Real.log R)) := by
      have hh := mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ (C + D) * a by positivity)
      nlinarith

end Causalean.Mathlib.Probability.SubGaussian
