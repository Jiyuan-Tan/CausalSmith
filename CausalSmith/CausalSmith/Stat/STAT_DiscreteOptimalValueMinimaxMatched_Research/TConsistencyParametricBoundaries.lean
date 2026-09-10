import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TParentReduction

/-! Consistency and parametric-rate boundaries along arbitrary alphabet sequences. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open Filter Asymptotics

/-- For [the specified risk sequence](hyp:risk), the [parametric-rate property says that the risk is eventually bounded above and below by positive constant multiples of one over sample size](goal). There are constants such that [the lower constant is positive](step:1), [it does not exceed the upper constant](step:2), and [the risk eventually lies between those constants divided by sample size](step:3). -/
def ParametricRate (risk : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ᶠ n in atTop, c / n ≤ risk n ∧ risk n ≤ C / n

/-- For [the specified alphabet-size sequence](hyp:dseq), the [bounded-alphabet sequence is an alphabet-size sequence that remains uniformly bounded asymptotically](goal). -/
def BoundedAlphabetSequence (dseq : ℕ → ℕ) : Prop :=
  IsBigO atTop (fun n => (dseq n : ℝ)) (fun _ => (1 : ℝ))

-- @node: phaseScale
private noncomputable def phaseScale (dseq : ℕ → ℕ) (n : ℕ) : ℝ :=
  min 1 ((dseq n : ℝ) / (n * logAlphabet (dseq n)))

-- @node: rawPhaseScale
private noncomputable def rawPhaseScale (dseq : ℕ → ℕ) (n : ℕ) : ℝ :=
  (dseq n : ℝ) / ((n : ℝ) * logAlphabet (dseq n))

-- @node: littleOScale
private noncomputable def littleOScale (dseq : ℕ → ℕ) (n : ℕ) : ℝ :=
  (dseq n : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 * n))

-- @node: phase_scale_tendsto_iff_littleO
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [the phase scale converges to zero exactly when $d=o(nlog(en))$](goal). -/
lemma phase_scale_tendsto_iff_littleO (dseq : ℕ → ℕ) (hd : ∀ n, 2 ≤ dseq n) :
    Tendsto (phaseScale dseq) atTop (nhds 0) ↔
      IsLittleO atTop (fun n => (dseq n : ℝ))
        (fun n => (n : ℝ) * Real.log (Real.exp 1 * n)) := by
  have hden : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (Real.exp 1 * n) = 0 → (dseq n : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn1 hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlog : 0 < Real.log (Real.exp 1 * n) := Real.log_pos (by
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      exact lt_of_lt_of_le he (by nlinarith [Real.exp_pos 1]))
    nlinarith
  rw [Asymptotics.isLittleO_iff_tendsto' hden]
  change Tendsto (phaseScale dseq) atTop (nhds 0) ↔
    Tendsto (littleOScale dseq) atTop (nhds 0)
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => ((Real.sqrt n)⁻¹ : ℝ)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have hlogN : Tendsto (fun n : ℕ => Real.log (Real.exp 1 * n)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact hN.const_mul_atTop (Real.exp_pos 1)
  have hinvlog : Tendsto (fun n : ℕ => (Real.log (Real.exp 1 * n))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogN
  constructor
  · intro hb
    have hraw : Tendsto (rawPhaseScale dseq) atTop (nhds 0) := by
      have hsmall : ∀ᶠ n in atTop, phaseScale dseq n < 1 / 2 :=
        (tendsto_order.1 hb).2 (1 / 2) (by norm_num)
      have heq : ∀ᶠ n in atTop, phaseScale dseq n = rawPhaseScale dseq n := by
        filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hs
        have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
        have hdR : (0 : ℝ) < dseq n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n))
        have hlogd : 0 < logAlphabet (dseq n) := by
          unfold logAlphabet
          apply Real.log_pos
          have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
          calc
            1 < Real.exp 1 := he
            _ = Real.exp 1 * 1 := by ring
            _ ≤ Real.exp 1 * dseq n := mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)
        have hnonneg : 0 ≤ rawPhaseScale dseq n := by
          exact div_nonneg (le_of_lt hdR) (mul_nonneg (le_of_lt hnR) (le_of_lt hlogd))
        have hlt : rawPhaseScale dseq n < 1 := by
          by_contra h
          have : phaseScale dseq n = 1 := min_eq_left (le_of_not_gt h)
          rw [this] at hs
          norm_num at hs
        exact min_eq_right (le_of_lt hlt)
      exact hb.congr' heq
    have hupperT : Tendsto (fun n : ℕ =>
        (Real.log (Real.exp 1 * n))⁻¹ + 2 * rawPhaseScale dseq n) atTop (nhds 0) := by
      convert hinvlog.add (hraw.const_mul 2) using 1 <;> norm_num
    have hsqueeze := tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := littleOScale dseq)
      (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
      hupperT
    apply (by simpa using hsqueeze :
      (∀ᶠ n in atTop, 0 ≤ littleOScale dseq n) →
      (∀ᶠ n in atTop, littleOScale dseq n ≤
        (Real.log (Real.exp 1 * n))⁻¹ + 2 * rawPhaseScale dseq n) →
      Tendsto (littleOScale dseq) atTop (nhds 0))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
      have hlogn : 0 < Real.log (Real.exp 1 * n) := Real.log_pos (by
        have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact lt_of_lt_of_le he (by nlinarith [Real.exp_pos 1]))
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hnR) (le_of_lt hlogn))
    · have hraw_small_ev : ∀ᶠ n in atTop, rawPhaseScale dseq n ≤ 1 / 2 :=
        ((tendsto_order.1 hraw).2 (1 / 2) (by norm_num)).mono (by
          intro n hn
          exact le_of_lt hn)
      filter_upwards [eventually_ge_atTop 1, hraw_small_ev] with n hn hraw_small
      have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
      have hdR : (0 : ℝ) < dseq n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n))
      have hlogn : 0 < Real.log (Real.exp 1 * n) := Real.log_pos (by
        have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact lt_of_lt_of_le he (by nlinarith [Real.exp_pos 1]))
      have hlogd : 0 < logAlphabet (dseq n) := by
        unfold logAlphabet
        apply Real.log_pos
        have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
        calc
          1 < Real.exp 1 := he
          _ = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * dseq n := mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)
      have hnonneg : 0 ≤ littleOScale dseq n := by
        exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hnR) (le_of_lt hlogn))
      have hrawnonneg : 0 ≤ rawPhaseScale dseq n := by
        exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hnR) (le_of_lt hlogd))
      by_cases hdn : dseq n < n
      · have hratio : (dseq n : ℝ) / n ≤ 1 := by
          rw [div_le_one hnR]
          exact_mod_cast le_of_lt hdn
        calc
          littleOScale dseq n = ((dseq n : ℝ) / n) /
              Real.log (Real.exp 1 * n) := by
                simp [littleOScale, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
          _ ≤ 1 / Real.log (Real.exp 1 * n) := by
            apply div_le_div_of_nonneg_right hratio (le_of_lt hlogn)
          _ ≤ (Real.log (Real.exp 1 * n))⁻¹ + 2 * rawPhaseScale dseq n := by
            rw [one_div]
            nlinarith
      · have hnd : n ≤ dseq n := le_of_not_gt hdn
        let t : ℝ := (dseq n : ℝ) / n
        have ht : 1 ≤ t := (one_le_div hnR).2 (by exact_mod_cast hnd)
        have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
        have hsplit : logAlphabet (dseq n) =
            Real.log (Real.exp 1 * n) + Real.log t := by
          dsimp [t]
          rw [logAlphabet, ← Real.log_mul (by positivity : Real.exp 1 * (n : ℝ) ≠ 0)
            (by positivity : (dseq n : ℝ) / n ≠ 0)]
          congr 1
          field_simp
        have hlogt : Real.log t ≤ t := Real.log_le_self (le_of_lt htpos)
        have ht_le : t ≤ Real.log (Real.exp 1 * n) := by
          have hraw_eq : rawPhaseScale dseq n = t /
              (Real.log (Real.exp 1 * n) + Real.log t) := by
            rw [rawPhaseScale, hsplit]
            dsimp [t]
            field_simp
          rw [hraw_eq] at hraw_small
          have hdenpos : 0 < Real.log (Real.exp 1 * n) + Real.log t :=
            add_pos_of_pos_of_nonneg hlogn (Real.log_nonneg ht)
          rw [div_le_iff₀ hdenpos] at hraw_small
          nlinarith
        have hden_le : Real.log (Real.exp 1 * n) + Real.log t ≤
            2 * Real.log (Real.exp 1 * n) := by linarith
        have hcomp : littleOScale dseq n ≤ 2 * rawPhaseScale dseq n := by
          have hhalfpos : 0 < (Real.log (Real.exp 1 * n) + Real.log t) / 2 := by
            exact div_pos (add_pos_of_pos_of_nonneg hlogn (Real.log_nonneg ht)) (by norm_num)
          calc
            littleOScale dseq n ≤ (dseq n : ℝ) /
                ((n : ℝ) * ((Real.log (Real.exp 1 * n) + Real.log t) / 2)) := by
              unfold littleOScale
              apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hnR hhalfpos)
              exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hnR)
            _ = 2 * rawPhaseScale dseq n := by
              rw [rawPhaseScale, hsplit]
              field_simp
        exact hcomp.trans (by linarith [show 0 ≤ (Real.log (Real.exp 1 * n))⁻¹ by positivity])
  · intro ha
    have hraw : Tendsto (rawPhaseScale dseq) atTop (nhds 0) := by
      have hupperT : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ +
          2 * littleOScale dseq n) atTop (nhds 0) := by
        convert hsqrt.add (ha.const_mul 2) using 1 <;> norm_num
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
        hupperT
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
        have hlogd : 0 < logAlphabet (dseq n) := by
          unfold logAlphabet
          apply Real.log_pos
          have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
          exact he.trans_le (by
            simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
        exact div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (le_of_lt hnR) (le_of_lt hlogd))
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
        have hdR : (0 : ℝ) < dseq n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n))
        have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
        have hsqrtn : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt (le_of_lt hnR)
        have hlogd : 0 < logAlphabet (dseq n) := by
          unfold logAlphabet
          apply Real.log_pos
          have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
          exact he.trans_le (by
            simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
        have hlogd_one : 1 ≤ logAlphabet (dseq n) := by
          rw [logAlphabet]
          have hmul : Real.exp 1 ≤ Real.exp 1 * (dseq n : ℝ) := by
            have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
            simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)
          calc
            1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
            _ ≤ _ := Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
              (mul_pos (Real.exp_pos 1) hdR) hmul
        have hlogn : 0 < Real.log (Real.exp 1 * n) := Real.log_pos (by
          have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          exact he.trans_le (by simpa using mul_le_mul_of_nonneg_left hn1 (Real.exp_nonneg 1)))
        by_cases hsmall : (dseq n : ℝ) ≤ Real.sqrt n
        · have hfirst : rawPhaseScale dseq n ≤ (dseq n : ℝ) / n := by
            unfold rawPhaseScale
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR
              (by simpa using mul_le_mul_of_nonneg_left hlogd_one (le_of_lt hnR))
          calc
            rawPhaseScale dseq n ≤ (dseq n : ℝ) / n := hfirst
            _ ≤ Real.sqrt n / n := by gcongr
            _ = (Real.sqrt n)⁻¹ := by
              field_simp
              nlinarith [hsqrtn]
            _ ≤ (Real.sqrt n)⁻¹ + 2 * littleOScale dseq n := by
              have ha0 : 0 ≤ littleOScale dseq n :=
                div_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_of_lt hnR) (le_of_lt hlogn))
              nlinarith
        · have hsqrt_lt : Real.sqrt n < (dseq n : ℝ) := lt_of_not_ge hsmall
          have hn_le_sq : (n : ℝ) ≤ (dseq n : ℝ) ^ 2 := by nlinarith
          have harg : Real.exp 1 * (n : ℝ) ≤
              (Real.exp 1 * (dseq n : ℝ)) ^ 2 := by
            have heone : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
            have hesq : Real.exp 1 ≤ (Real.exp 1) ^ 2 := by
              nlinarith [Real.exp_pos 1]
            calc
              Real.exp 1 * (n : ℝ) ≤ Real.exp 1 * (dseq n : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hn_le_sq (Real.exp_nonneg 1)
              _ ≤ (Real.exp 1) ^ 2 * (dseq n : ℝ) ^ 2 := by
                exact mul_le_mul_of_nonneg_right hesq (sq_nonneg _)
              _ = (Real.exp 1 * (dseq n : ℝ)) ^ 2 := by ring
          have hlogcomp : Real.log (Real.exp 1 * n) ≤ 2 * logAlphabet (dseq n) := by
            have hmono := Real.strictMonoOn_log.monotoneOn
              (mul_pos (Real.exp_pos 1) hnR)
              (sq_pos_of_pos (mul_pos (Real.exp_pos 1) hdR)) harg
            rw [Real.log_pow] at hmono
            simpa [logAlphabet] using hmono
          have hhalfpos : 0 < Real.log (Real.exp 1 * n) / 2 := div_pos hlogn (by norm_num)
          have hcomp : rawPhaseScale dseq n ≤ 2 * littleOScale dseq n := by
            calc
              rawPhaseScale dseq n ≤ (dseq n : ℝ) /
                  ((n : ℝ) * (Real.log (Real.exp 1 * n) / 2)) := by
                unfold rawPhaseScale
                exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
                  (mul_pos hnR hhalfpos)
                  (mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hnR))
              _ = 2 * littleOScale dseq n := by
                unfold littleOScale
                field_simp
          exact hcomp.trans (by
            have : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
            linarith)
    have hmin : Tendsto (fun n : ℕ => min (1 : ℝ) (rawPhaseScale dseq n))
        atTop (nhds 0) := by
      convert (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds).min hraw using 1 <;> norm_num
    change Tendsto (fun n : ℕ => min (1 : ℝ)
      ((dseq n : ℝ) / ((n : ℝ) * logAlphabet (dseq n)))) atTop (nhds 0)
    exact hmin

-- @node: risk_zero_iff_phase_scale
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the stated c condition holds](hyp:hc), and [the stated c condition holds](hyp:hC), and [the stated bounds condition holds](hyp:hbounds), then [a risk sequence satisfying the stated two-sided phase-scale bounds converges to zero exactly when the phase scale does](goal). -/
lemma risk_zero_iff_phase_scale (risk : ℕ → ℝ) (dseq : ℕ → ℕ) (hd : ∀ n, 2 ≤ dseq n)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hbounds : ∀ n : ℕ, 1 ≤ n →
      c * phaseScale dseq n ≤ risk n ∧ risk n ≤ C * phaseScale dseq n) :
    Tendsto risk atTop (nhds 0) ↔ Tendsto (phaseScale dseq) atTop (nhds 0) := by
  have hs_nonneg : ∀ n, 0 ≤ phaseScale dseq n := by
    intro n
    by_cases hn : n = 0
    · simp [phaseScale, hn]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hdR : (0 : ℝ) < dseq n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n))
      have hlogd : 0 < logAlphabet (dseq n) := by
        unfold logAlphabet
        apply Real.log_pos
        have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
        exact he.trans_le (by simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
      unfold phaseScale
      rw [le_min_iff]
      exact ⟨by norm_num, by positivity⟩
  constructor
  · intro hr
    have hu : Tendsto (fun n => c⁻¹ * risk n) atTop (nhds 0) := by
      convert hr.const_mul c⁻¹ using 1 <;> norm_num
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds) hu
    · exact Filter.Eventually.of_forall (fun n => hs_nonneg n)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have := (hbounds n hn).1
      have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
      calc
        phaseScale dseq n = c⁻¹ * (c * phaseScale dseq n) := by field_simp
        _ ≤ c⁻¹ * risk n := mul_le_mul_of_nonneg_left this hcinv
  · intro hs
    have hu : Tendsto (fun n => C * phaseScale dseq n) atTop (nhds 0) := by
      convert hs.const_mul C using 1 <;> norm_num
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds) hu
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (mul_nonneg (le_of_lt hc) (hs_nonneg n)).trans (hbounds n hn).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (hbounds n hn).2

-- @node: parametric_implies_bounded_alphabet
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the stated c condition holds](hyp:hc), and [the stated lower condition holds](hyp:hlower), and [the stated param condition holds](hyp:hparam), then [a two-sided parametric risk bound forces the alphabet-size sequence to be uniformly bounded](goal). -/
lemma parametric_implies_bounded_alphabet (risk : ℕ → ℝ) (dseq : ℕ → ℕ)
    (hd : ∀ n, 2 ≤ dseq n) (c C : ℝ) (hc : 0 < c)
    (hlower : ∀ n : ℕ, 1 ≤ n → c * phaseScale dseq n ≤ risk n)
    (hparam : ParametricRate risk) : BoundedAlphabetSequence dseq := by
  obtain ⟨a, B, ha, _haB, hp⟩ := hparam
  unfold BoundedAlphabetSequence
  rw [Asymptotics.isBigO_iff]
  refine ⟨max 1 (4 * (B / c) ^ 2), ?_⟩
  filter_upwards [hp, eventually_ge_atTop 1,
    eventually_ge_atTop (Nat.ceil (B / c) + 2)] with n hpn hn hlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
  have hdR : (0 : ℝ) < dseq n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n))
  have hlogd : 0 < logAlphabet (dseq n) := by
    unfold logAlphabet
    apply Real.log_pos
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) (hd n))
    exact he.trans_le (by simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
  have hBC : 0 ≤ B := le_trans (le_of_lt ha) _haB
  have hscale_bound : (n : ℝ) * phaseScale dseq n ≤ B / c := by
    have h := (hlower n hn).trans hpn.2
    rw [le_div_iff₀ hc]
    calc
      (n : ℝ) * phaseScale dseq n * c = (n : ℝ) *
          (c * phaseScale dseq n) := by ring
      _ ≤ (n : ℝ) * risk n :=
        mul_le_mul_of_nonneg_left (hlower n hn) (le_of_lt hnR)
      _ ≤ (n : ℝ) * (B / n) := mul_le_mul_of_nonneg_left hpn.2 (le_of_lt hnR)
      _ = B := by field_simp
  have hn_gt : B / c < (n : ℝ) := by
    have hceil : B / c ≤ Nat.ceil (B / c) := Nat.le_ceil _
    exact lt_of_le_of_lt hceil (by exact_mod_cast (by omega : Nat.ceil (B / c) < n))
  have hraw_le : rawPhaseScale dseq n ≤ 1 := by
    by_contra h
    have hs : phaseScale dseq n = 1 := by
      unfold phaseScale
      exact min_eq_left (le_of_not_ge h)
    rw [hs] at hscale_bound
    linarith
  have hratio : (dseq n : ℝ) / logAlphabet (dseq n) ≤ B / c := by
    have hs : phaseScale dseq n = rawPhaseScale dseq n := min_eq_right hraw_le
    rw [hs, rawPhaseScale] at hscale_bound
    calc
      (dseq n : ℝ) / logAlphabet (dseq n) =
          (n : ℝ) * ((dseq n : ℝ) / ((n : ℝ) * logAlphabet (dseq n))) := by field_simp
      _ ≤ B / c := hscale_bound
  have hlog_sqrt : logAlphabet (dseq n) ≤ 2 * Real.sqrt (dseq n) := by
    have hsqrtpos : 0 < Real.sqrt (dseq n) := Real.sqrt_pos.2 hdR
    have hbase := Real.log_le_sub_one_of_pos hsqrtpos
    have hroot := Real.log_sqrt (le_of_lt hdR)
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR), Real.log_exp] at ⊢
    nlinarith
  have hsqrt_bound : Real.sqrt (dseq n) ≤ 2 * (B / c) := by
    have hsqrt_nonneg := Real.sqrt_nonneg (dseq n)
    have hsqrt_sq := Real.mul_self_sqrt (le_of_lt hdR)
    have haux : Real.sqrt (dseq n) ≤
        2 * ((dseq n : ℝ) / logAlphabet (dseq n)) := by
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hlogd]
      nlinarith
    linarith
  have hdBound : (dseq n : ℝ) ≤ 4 * (B / c) ^ 2 := by
    nlinarith [Real.sq_sqrt (le_of_lt hdR), sq_nonneg (2 * (B / c) - Real.sqrt (dseq n))]
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (dseq n : ℝ) from Nat.cast_nonneg _),
    norm_one, mul_one]
  apply le_max_of_le_right
  exact hdBound

-- @node: bounded_alphabet_sequence_global_bound
/-- [a bounded-alphabet sequence admits a single finite upper bound at every sample size](goal). -/
lemma bounded_alphabet_sequence_global_bound (dseq : ℕ → ℕ) (h : BoundedAlphabetSequence dseq) :
    ∃ dmax : ℕ, ∀ n, dseq n ≤ dmax := by
  unfold BoundedAlphabetSequence at h
  have hb : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) Filter.cofinite
      (fun n => ‖(dseq n : ℝ)‖) := by
    have hb' := (Asymptotics.isBigO_const_iff.mp h).2
    simpa only [Nat.cofinite_eq_atTop] using hb'
  obtain ⟨K, hK⟩ := Filter.IsBoundedUnder.bddAbove_range_of_cofinite hb
  refine ⟨Nat.ceil K, ?_⟩
  intro n
  have hn : ‖(dseq n : ℝ)‖ ≤ K := hK ⟨n, rfl⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (dseq n : ℝ) from Nat.cast_nonneg _)] at hn
  have hceil : K ≤ Nat.ceil K := Nat.le_ceil K
  exact_mod_cast hn.trans hceil

-- @node: thm:consistency-and-parametric-boundaries
/-- If [the Cai--Low moment-matching prior result is available](hyp:h_cai_low_of_gate), and [the Jiao--Han--Weissman Poisson L1 lower bound is available](hyp:h_jhw_of_gate), then [observed and causal minimax risks are consistent exactly when $d=o(nlog(en))$, and attain the parametric $1/n$ rate exactly for uniformly bounded alphabets](goal). -/
theorem consistency_and_parametric_boundaries
    (h_cai_low_of_gate : CaiLowAbsoluteMomentPriors)
    (h_jhw_of_gate : JhwPoissonL1Lower) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      (∀ (dseq : ℕ → ℕ), (∀ n, 2 ≤ dseq n) →
        (Tendsto (fun n => minimaxRisk n (dseq n) epsilon) atTop (nhds 0) ↔
          IsLittleO atTop (fun n => (dseq n : ℝ))
            (fun n => (n : ℝ) * Real.log (Real.exp 1 * n)))) ∧
      (∀ (dseq : ℕ → ℕ), (∀ n, 2 ≤ dseq n) →
        (ParametricRate (fun n => minimaxRisk n (dseq n) epsilon) ↔
          BoundedAlphabetSequence dseq) ∧
        (ParametricRate (fun n => causalMinimaxRisk n (dseq n) epsilon) ↔
          BoundedAlphabetSequence dseq)) ∧
      (∀ (dseq : ℕ → ℕ), (∀ n, 2 ≤ dseq n) →
        (Tendsto (fun n => causalMinimaxRisk n (dseq n) epsilon) atTop (nhds 0) ↔
          IsLittleO atTop (fun n => (dseq n : ℝ))
            (fun n => (n : ℝ) * Real.log (Real.exp 1 * n)))) := by
  obtain ⟨_tuning, _htuning, hfrontier⟩ :=
    matched_minimax_frontier h_cai_low_of_gate h_jhw_of_gate
  obtain ⟨_tuning2, _htuning2, _hcompare, _hfallback, hbounded⟩ :=
    parent_reduction h_cai_low_of_gate h_jhw_of_gate
  intro epsilon hepsilon hepsilon'
  obtain ⟨c, C, hc, hcC, hb⟩ := hfrontier epsilon hepsilon hepsilon'
  have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
  have hbounded' := hbounded epsilon hepsilon hepsilon'
  have hobs_bounds (dseq : ℕ → ℕ) (hd : ∀ n, 2 ≤ dseq n) :
      ∀ n : ℕ, 1 ≤ n →
        c * phaseScale dseq n ≤ minimaxRisk n (dseq n) epsilon ∧
        minimaxRisk n (dseq n) epsilon ≤ C * phaseScale dseq n := by
    intro n hn
    obtain ⟨hl, hm, hu, _⟩ := hb n (dseq n) hn (hd n)
    exact ⟨hl, hm.trans hu⟩
  have hcausal_eq (dseq : ℕ → ℕ) (hd : ∀ n, 2 ≤ dseq n) :
      ∀ᶠ n in atTop, causalMinimaxRisk n (dseq n) epsilon =
        minimaxRisk n (dseq n) epsilon := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hb n (dseq n) hn (hd n)).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro dseq hd
    exact (risk_zero_iff_phase_scale _ dseq hd c C hc hC (hobs_bounds dseq hd)).trans
      (phase_scale_tendsto_iff_littleO dseq hd)
  · intro dseq hd
    constructor
    · constructor
      · exact fun hp => parametric_implies_bounded_alphabet _ dseq hd c C hc
          (fun n hn => (hobs_bounds dseq hd n hn).1) hp
      · intro hbd
        exact hbounded' dseq hd (bounded_alphabet_sequence_global_bound dseq hbd)
    · calc
      ParametricRate (fun n => causalMinimaxRisk n (dseq n) epsilon) ↔
          ParametricRate (fun n => minimaxRisk n (dseq n) epsilon) := by
        constructor
        · rintro ⟨a, B, ha, haB, h⟩
          refine ⟨a, B, ha, haB, ?_⟩
          filter_upwards [h, hcausal_eq dseq hd] with n hn heq
          simpa [heq] using hn
        · rintro ⟨a, B, ha, haB, h⟩
          refine ⟨a, B, ha, haB, ?_⟩
          filter_upwards [h, hcausal_eq dseq hd] with n hn heq
          simpa [heq] using hn
      _ ↔ BoundedAlphabetSequence dseq := ⟨fun hp => parametric_implies_bounded_alphabet _ dseq hd c C hc
          (fun n hn => (hobs_bounds dseq hd n hn).1) hp,
        fun hbd => hbounded' dseq hd (bounded_alphabet_sequence_global_bound dseq hbd)⟩
  · intro dseq hd
    rw [show Tendsto (fun n => causalMinimaxRisk n (dseq n) epsilon) atTop (nhds 0) ↔
        Tendsto (fun n => minimaxRisk n (dseq n) epsilon) atTop (nhds 0) from
      ⟨fun h => h.congr' (hcausal_eq dseq hd),
        fun h => h.congr' ((hcausal_eq dseq hd).mono fun _ heq => heq.symm)⟩]
    exact (risk_zero_iff_phase_scale _ dseq hd c C hc hC (hobs_bounds dseq hd)).trans
      (phase_scale_tendsto_iff_littleO dseq hd)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
