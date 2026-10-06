module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedFixedQMinimaxFrontier
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.PPhaseBoundaries

/-! PUnrestrictedFixedQPhaseBoundaries for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: fixedQRate_eq_frontierRate_one
/-- Given [the specified inputs and assumptions](hyp:n,d), [the stated mathematical conclusion holds](goal). -/
lemma fixedQRate_eq_frontierRate_one (n d : ℕ) :
    fixedQRate n d = frontierRate n d 1 := by
  simp [fixedQRate, frontierRate, effectiveSize, logScale]

-- @node: fixedQRate_tendsto_iff_dimension_littleO
/-- Given [the specified inputs and assumptions](hyp:d), [the stated mathematical conclusion holds](goal). -/
lemma fixedQRate_tendsto_iff_dimension_littleO (d : ℕ → ℕ) :
    Tendsto (fun n => fixedQRate n (d n)) atTop (nhds 0) ↔
      (fun n => (d n : ℝ)) =o[atTop]
        (fun n => (n : ℝ) * Real.log (Real.exp 1 + n)) := by
  let a : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  let x : ℕ → ℝ := fun n => (d n : ℝ) /
    ((n : ℝ) * Real.log (Real.exp 1 + n))
  have hlog (n : ℕ) : 0 < Real.log (Real.exp 1 + n) := by
    apply Real.log_pos
    have : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx (n : ℕ) : 0 ≤ x n := by
    dsimp [x]
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hlog n)))
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa only [a, Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hsq : Tendsto (fun n => (x n) ^ 2) atTop (nhds 0) ↔
      Tendsto x atTop (nhds 0) := by
    constructor
    · intro h
      have hs := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp h
      have hs' : Tendsto (fun n => Real.sqrt ((x n) ^ 2)) atTop (nhds 0) := by
        convert hs using 1 <;> simp [Function.comp_def]
      exact hs'.congr' (Eventually.of_forall (fun n => by
        simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (hx n)]))
    · intro h
      convert h.pow 2 using 1 <;> norm_num
  have hlittle : (fun n => (d n : ℝ)) =o[atTop]
      (fun n => (n : ℝ) * Real.log (Real.exp 1 + n)) ↔
      Tendsto x atTop (nhds 0) := by
    have hden : ∀ᶠ (n : ℕ) in (atTop : Filter ℕ),
        (n : ℝ) * Real.log (Real.exp 1 + n) = 0 → (d n : ℝ) = 0 := by
      filter_upwards [eventually_ge_atTop 1] with n hn hzero
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      exact False.elim ((ne_of_gt (mul_pos hn' (hlog n))) hzero)
    exact Asymptotics.isLittleO_iff_tendsto' hden
  change Tendsto (fun n => min 1 (a n + (x n) ^ 2)) atTop (nhds 0) ↔ _
  rw [phase_min_rate_tendsto a (fun n => (x n) ^ 2)
    (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun n => sq_nonneg _) ha0, hsq, hlittle]

/-- Given [the specified inputs and assumptions](hyp:hZeng_of_gate,q,hq), [the stated mathematical conclusion holds](goal). -/
-- @node: prop:unrestricted-fixed-q-phase-boundaries
theorem unrestricted_fixed_q_phase_boundaries
    (hZeng_of_gate : ZengTheoremTwoLower)
    (q : ℝ) (hq : 0 < q ∧ q < 1 / 2) :
    (∀ (d : ℕ → ℕ), (∀ n, 1 ≤ d n) →
      (Tendsto (fun n => unrestrictedMinimaxRisk n (d n) q) atTop (nhds 0) ↔
        (fun n => (d n : ℝ)) =o[atTop]
          (fun n => (n : ℝ) * Real.log (Real.exp 1 + n)))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ M : ℝ, 0 < M →
      ∃ C : ℝ, c ≤ C ∧
        ∀ (d : ℕ → ℕ), (∀ n, 1 ≤ d n) →
          (∀ᶠ n in (atTop : Filter ℕ),
            (d n : ℝ) ≤ M * Real.sqrt n * Real.log (Real.exp 1 + n)) →
          (∀ᶠ n in (atTop : Filter ℕ),
            c * ((n : ℕ) : ℝ)⁻¹ ≤ unrestrictedMinimaxRisk n (d n) q ∧
              unrestrictedMinimaxRisk n (d n) q ≤ C * ((n : ℕ) : ℝ)⁻¹)) ∧
    (∀ (d : ℕ → ℕ), (∀ n, 1 ≤ d n) →
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ᶠ n in (atTop : Filter ℕ),
          c * ((n : ℕ) : ℝ)⁻¹ ≤ unrestrictedMinimaxRisk n (d n) q ∧
            unrestrictedMinimaxRisk n (d n) q ≤ C * ((n : ℕ) : ℝ)⁻¹) →
      (fun n => (d n : ℝ)) =O[atTop]
        (fun n => Real.sqrt n * Real.log (Real.exp 1 + n))) := by
  obtain ⟨a, B, ha, haB, hfrontier⟩ :=
    unrestricted_fixed_q_minimax_frontier hZeng_of_gate q hq.1 hq.2
  have hB : 0 ≤ B := le_trans (le_of_lt ha) haB
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hrate : Tendsto (fun n => unrestrictedMinimaxRisk n (d n) q) atTop
        (nhds 0) ↔ Tendsto (fun n => fixedQRate n (d n)) atTop (nhds 0) := by
      have hr (n : ℕ) : 0 ≤ fixedQRate n (d n) := by
        unfold fixedQRate
        exact le_min (by norm_num) (add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (sq_nonneg _))
      have hbound : ∀ᶠ n in (atTop : Filter ℕ),
          a * fixedQRate n (d n) ≤ unrestrictedMinimaxRisk n (d n) q ∧
          unrestrictedMinimaxRisk n (d n) q ≤ B * fixedQRate n (d n) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        obtain ⟨hlo, hhi, _, _⟩ := hfrontier n (d n) hn (hd n)
        exact ⟨hlo, hhi⟩
      constructor
      · intro h
        have hupper : Tendsto (fun n => a⁻¹ * unrestrictedMinimaxRisk n (d n) q)
            atTop (nhds 0) := by
          convert tendsto_const_nhds.mul h using 1 <;> simp
        apply squeeze_zero' (Eventually.of_forall hr) ?_ hupper
        filter_upwards [hbound] with n hn
        calc
          fixedQRate n (d n) ≤ unrestrictedMinimaxRisk n (d n) q / a :=
            (le_div_iff₀ ha).2 (by simpa [mul_comm] using hn.1)
          _ = a⁻¹ * unrestrictedMinimaxRisk n (d n) q := by ring
      · intro h
        have hupper : Tendsto (fun n => B * fixedQRate n (d n))
            atTop (nhds 0) := by
          convert tendsto_const_nhds.mul h using 1 <;> simp
        apply squeeze_zero' ?_ (hbound.mono fun n hn => hn.2) hupper
        filter_upwards [hbound] with n hn
        exact (mul_nonneg (le_of_lt ha) (hr n)).trans hn.1
    exact hrate.trans (fixedQRate_tendsto_iff_dimension_littleO d)
  · refine ⟨a, ha, ?_⟩
    intro M hM
    refine ⟨B * (1 + M ^ 2), ?_, ?_⟩
    · nlinarith [sq_nonneg M, mul_nonneg hB (sq_nonneg M)]
    · intro d hd hdim
      filter_upwards [eventually_ge_atTop 1, hdim] with n hn hdn
      obtain ⟨hlo, hhi, _, _⟩ := hfrontier n (d n) hn (hd n)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog : 0 < Real.log (Real.exp 1 + n) := by
        apply Real.log_pos
        have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
        linarith
      have hden : 0 < (n : ℝ) * Real.log (Real.exp 1 + n) :=
        mul_pos hnpos hlog
      have hroot : (Real.sqrt n) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (le_of_lt hnpos)
      have hdim_sq : (d n : ℝ)^2 ≤
          M^2 * ((n : ℝ) * Real.log (Real.exp 1 + n)^2) := by
        have hright : 0 ≤ M * Real.sqrt n * Real.log (Real.exp 1 + n) := by positivity
        calc
          (d n : ℝ)^2 ≤ (M * Real.sqrt n * Real.log (Real.exp 1 + n))^2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hdn)
              (add_nonneg hright (Nat.cast_nonneg (d n)))]
          _ = M^2 * ((n : ℝ) * Real.log (Real.exp 1 + n)^2) := by
            rw [mul_pow, mul_pow, hroot]
            ring
      have hsq : ((d n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2 ≤
          M^2 * (n : ℝ)⁻¹ := by
        rw [div_pow]
        apply (div_le_iff₀ (pow_pos hden 2)).2
        have heq : (n : ℝ)⁻¹ * ((n : ℝ) * Real.log (Real.exp 1 + n)) ^ 2 =
            (n : ℝ) * Real.log (Real.exp 1 + n)^2 := by
          field_simp [ne_of_gt hnpos]
        rw [mul_assoc, heq]
        exact hdim_sq
      have hinv : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnpos).2 (by exact_mod_cast hn)
      have hrate_low : (n : ℝ)⁻¹ ≤ fixedQRate n (d n) := by
        unfold fixedQRate
        exact le_min hinv (le_add_of_nonneg_right (sq_nonneg _))
      have hrate_up : fixedQRate n (d n) ≤
          (1 + M^2) * (n : ℝ)⁻¹ := by
        unfold fixedQRate
        calc
          min 1 ((n : ℝ)⁻¹ + _) ≤ (n : ℝ)⁻¹ + _ := min_le_right _ _
          _ ≤ (1 + M^2) * (n : ℝ)⁻¹ := by nlinarith
      exact ⟨(mul_le_mul_of_nonneg_left hrate_low (le_of_lt ha)).trans hlo,
        hhi.trans (by
          calc
            B * fixedQRate n (d n) ≤ B * ((1 + M^2) * (n : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left hrate_up hB
            _ = (B * (1 + M^2)) * (n : ℝ)⁻¹ := by ring)⟩
  · intro d hd hparam
    obtain ⟨c, C, hc, hcC, hbound⟩ := hparam
    have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
    have hratebound : ∀ᶠ n in (atTop : Filter ℕ),
        a * fixedQRate n (d n) ≤ unrestrictedMinimaxRisk n (d n) q ∧
        unrestrictedMinimaxRisk n (d n) q ≤ C * (n : ℝ)⁻¹ := by
      filter_upwards [eventually_ge_atTop 1, hbound] with n hn hbc
      exact ⟨(hfrontier n (d n) hn (hd n)).1, hbc.2⟩
    have hrate0 : Tendsto (fun n => fixedQRate n (d n)) atTop (nhds 0) := by
      have hupper : Tendsto (fun n : ℕ => (C / a) * (n : ℝ)⁻¹)
          atTop (nhds 0) := by
        have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) := by
          simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
              atTop atTop))
        simpa only [mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => C / a) atTop (nhds (C / a))).mul hinv
      apply squeeze_zero' ?_ ?_ hupper
      · filter_upwards [eventually_ge_atTop 1] with n hn
        unfold fixedQRate
        exact le_min (by norm_num) (add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (sq_nonneg _))
      · filter_upwards [hratebound] with n hn
        calc
          fixedQRate n (d n) ≤ unrestrictedMinimaxRisk n (d n) q / a :=
            (le_div_iff₀ ha).2 (by simpa [mul_comm] using hn.1)
          _ ≤ (C / a) * (n : ℝ)⁻¹ := by
            exact div_le_div_of_nonneg_right hn.2 (le_of_lt ha) |>.trans_eq (by ring)
    have hsmall : ∀ᶠ n in (atTop : Filter ℕ), fixedQRate n (d n) < 1 :=
      hrate0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    let K : ℝ := max 1 (C / a)
    have hK : 0 ≤ K := le_trans (by norm_num) (le_max_left _ _)
    have hK2 : C / a ≤ K^2 := by
      have h1 : 1 ≤ K := le_max_left _ _
      have h2 : C / a ≤ K := le_max_right _ _
      nlinarith
    rw [Asymptotics.isBigO_iff]
    refine ⟨K, ?_⟩
    filter_upwards [eventually_ge_atTop 1, hratebound, hsmall] with n hn hb hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log (Real.exp 1 + n) := by
      apply Real.log_pos
      have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    have hden : 0 < (n : ℝ) * Real.log (Real.exp 1 + n) :=
      mul_pos hnpos hlog
    have hsum : (n : ℝ)⁻¹ +
        ((d n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)))^2 < 1 := by
      by_contra hnot
      have hge : 1 ≤ (n : ℝ)⁻¹ +
          ((d n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)))^2 :=
        le_of_not_gt hnot
      simp [fixedQRate, min_eq_left hge] at hs
    have hsq : ((d n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)))^2 ≤
        (C / a) * (n : ℝ)⁻¹ := by
      have hr : fixedQRate n (d n) = (n : ℝ)⁻¹ +
          ((d n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)))^2 := by
        simp [fixedQRate, min_eq_right (le_of_lt hsum)]
      have hu : fixedQRate n (d n) ≤ (C / a) * (n : ℝ)⁻¹ := by
        calc
          fixedQRate n (d n) ≤ unrestrictedMinimaxRisk n (d n) q / a :=
            (le_div_iff₀ ha).2 (by simpa [mul_comm] using hb.1)
          _ ≤ (C / a) * (n : ℝ)⁻¹ := by
            calc
              unrestrictedMinimaxRisk n (d n) q / a ≤
                  (C * (n : ℝ)⁻¹) / a :=
                div_le_div_of_nonneg_right hb.2 (le_of_lt ha)
              _ = (C / a) * (n : ℝ)⁻¹ := by ring
      nlinarith [inv_nonneg.mpr (le_of_lt hnpos)]
    have hdsq : (d n : ℝ)^2 ≤
        (C / a) * ((n : ℝ) * Real.log (Real.exp 1 + n)^2) := by
      rw [div_pow] at hsq
      have hp := mul_le_mul_of_nonneg_right hsq (le_of_lt (pow_pos hden 2))
      have heq : (n : ℝ)⁻¹ * ((n : ℝ) * Real.log (Real.exp 1 + n))^2 =
          (n : ℝ) * Real.log (Real.exp 1 + n)^2 := by
        field_simp [ne_of_gt hnpos]
      rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hden 2)), mul_assoc, heq] at hp
      exact hp
    have hroot : (Real.sqrt n)^2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
    have hdim : (d n : ℝ) ≤ K * (Real.sqrt n * Real.log (Real.exp 1 + n)) := by
      have hprod : 0 ≤ (n : ℝ) * Real.log (Real.exp 1 + n)^2 := by positivity
      have hkdsq : (d n : ℝ)^2 ≤
          K^2 * ((n : ℝ) * Real.log (Real.exp 1 + n)^2) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK2) hprod]
      have hright : 0 ≤ K * (Real.sqrt n * Real.log (Real.exp 1 + n)) := by positivity
      have hright_sq : (K * (Real.sqrt n * Real.log (Real.exp 1 + n)))^2 =
          K^2 * ((n : ℝ) * Real.log (Real.exp 1 + n)^2) := by
        rw [mul_pow, mul_pow, hroot]
      rw [← hright_sq] at hkdsq
      nlinarith [Nat.cast_nonneg (α := ℝ) (d n)]
    change ‖(d n : ℝ)‖ ≤ K * ‖Real.sqrt n * Real.log (Real.exp 1 + n)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (d n)),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hlog))]
    exact hdim

end CausalSmith.Stat.MarRareqLogfrontier
