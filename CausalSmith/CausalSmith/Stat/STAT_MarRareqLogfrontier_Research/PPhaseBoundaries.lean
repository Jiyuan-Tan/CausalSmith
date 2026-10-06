module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TMatchedMinimaxFrontier

/-! PPhaseBoundaries for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: phase_min_rate_tendsto
/-- Given [the specified inputs and assumptions](hyp:a,b,ha,hb,ha0), [the stated mathematical conclusion holds](goal). -/
lemma phase_min_rate_tendsto (a b : ℕ → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t)
    (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto (fun t => min 1 (a t + b t)) atTop (nhds 0) ↔
      Tendsto b atTop (nhds 0) := by
  constructor
  · intro h
    have hsmall : ∀ᶠ t in atTop, min 1 (a t + b t) < 1 :=
      h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hsum : Tendsto (fun t => a t + b t) atTop (nhds 0) := by
      apply h.congr'
      filter_upwards [hsmall] with t ht
      have hab : a t + b t < 1 := by
        by_contra hnot
        have hge : 1 ≤ a t + b t := le_of_not_gt hnot
        simp [min_eq_left hge] at ht
      exact min_eq_right (le_of_lt hab)
    exact squeeze_zero hb (fun t => le_add_of_nonneg_left (ha t)) hsum
  · intro hb0
    have hsum : Tendsto (fun t => a t + b t) atTop (nhds 0) := by
      convert ha0.add hb0 using 1 <;> simp
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).min hsum)

-- @node: phase_frontier_rate_tendsto
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hN), [the stated mathematical conclusion holds](goal). -/
lemma phase_frontier_rate_tendsto
    (n d : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hq : ∀ t, 0 < q t)
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    Tendsto (fun t => frontierRate (n t) (d t) (q t)) atTop (nhds 0) ↔
      (fun t => (d t : ℝ)) =o[atTop]
        (fun t => effectiveSize (n t) (q t) * logScale (n t) (q t)) := by
  let a : ℕ → ℝ := fun t => (effectiveSize (n t) (q t))⁻¹
  let x : ℕ → ℝ := fun t => (d t : ℝ) /
    (effectiveSize (n t) (q t) * logScale (n t) (q t))
  have hNpos (t : ℕ) : 0 < effectiveSize (n t) (q t) := by
    unfold effectiveSize
    exact mul_pos (by exact_mod_cast hn t) (hq t)
  have hL (t : ℕ) : 0 < logScale (n t) (q t) := by
    change 0 < Real.log (Real.exp 1 + effectiveSize (n t) (q t))
    apply Real.log_pos
    have : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [hNpos t]
  have hx (t : ℕ) : 0 ≤ x t := div_nonneg (Nat.cast_nonneg _) (le_of_lt (mul_pos (hNpos t) (hL t)))
  have ha0 : Tendsto a atTop (nhds 0) := tendsto_inv_atTop_zero.comp hN
  have hsq : Tendsto (fun t => (x t) ^ 2) atTop (nhds 0) ↔
      Tendsto x atTop (nhds 0) := by
    constructor
    · intro h
      have hs := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp h
      have hs' : Tendsto (fun t => Real.sqrt ((x t) ^ 2)) atTop (nhds 0) := by
        convert hs using 1 <;> simp [Function.comp_def]
      exact hs'.congr' (Eventually.of_forall (fun t => by
        simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (hx t)]))
    · intro h
      convert h.pow 2 using 1 <;> norm_num
  have hlittle : (fun t => (d t : ℝ)) =o[atTop]
      (fun t => effectiveSize (n t) (q t) * logScale (n t) (q t)) ↔
      Tendsto x atTop (nhds 0) := by
    have hden : ∀ t, effectiveSize (n t) (q t) * logScale (n t) (q t) = 0 →
        (d t : ℝ) = 0 := by
      intro t ht
      exact False.elim ((ne_of_gt (mul_pos (hNpos t) (hL t))) ht)
    exact Asymptotics.isLittleO_iff_tendsto hden
  change Tendsto (fun t => min 1 (a t + (x t) ^ 2)) atTop (nhds 0) ↔ _
  rw [phase_min_rate_tendsto a (fun t => (x t) ^ 2)
    (fun t => inv_nonneg.mpr (le_of_lt (hNpos t)))
    (fun t => sq_nonneg _) ha0, hsq, hlittle]

-- @node: phase_rate_lower_bigO
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hN), [the stated mathematical conclusion holds](goal). -/
lemma phase_rate_lower_bigO
    (n d : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hq : ∀ t, 0 < q t)
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    (fun t => (effectiveSize (n t) (q t))⁻¹) =O[atTop]
      (fun t => frontierRate (n t) (d t) (q t)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [hN.eventually_ge_atTop 1] with t ht
  have hNpos : 0 < effectiveSize (n t) (q t) := by
    unfold effectiveSize
    exact mul_pos (by exact_mod_cast hn t) (hq t)
  have ha : 0 ≤ (effectiveSize (n t) (q t))⁻¹ := inv_nonneg.mpr (le_of_lt hNpos)
  have ha1 : (effectiveSize (n t) (q t))⁻¹ ≤ 1 := (inv_le_one₀ hNpos).2 ht
  have hr : 0 ≤ frontierRate (n t) (d t) (q t) := by
    unfold frontierRate
    exact le_min (by norm_num) (add_nonneg ha (sq_nonneg _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hr]
  simp only [one_mul]
  unfold frontierRate
  exact le_min ha1 (le_add_of_nonneg_right (sq_nonneg _))

-- @node: phase_dimension_rate_bigO
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hN), [the stated mathematical conclusion holds](goal). -/
lemma phase_dimension_rate_bigO
    (n d : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hq : ∀ t, 0 < q t)
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    (fun t => frontierRate (n t) (d t) (q t)) =O[atTop]
      (fun t => (effectiveSize (n t) (q t))⁻¹) ↔
    (fun t => (d t : ℝ)) =O[atTop]
      (fun t => Real.sqrt (effectiveSize (n t) (q t)) * logScale (n t) (q t)) := by
  let N : ℕ → ℝ := fun t => effectiveSize (n t) (q t)
  let L : ℕ → ℝ := fun t => logScale (n t) (q t)
  let B : ℕ → ℝ := fun t => Real.sqrt (N t) * L t
  have hNpos (t : ℕ) : 0 < N t := by
    dsimp [N, effectiveSize]
    exact mul_pos (by exact_mod_cast hn t) (hq t)
  have hL (t : ℕ) : 0 < L t := by
    change 0 < Real.log (Real.exp 1 + N t)
    apply Real.log_pos
    have : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [hNpos t]
  have hB (t : ℕ) : 0 < B t := mul_pos (Real.sqrt_pos.2 (hNpos t)) (hL t)
  have hden (t : ℕ) : 0 < N t * L t := mul_pos (hNpos t) (hL t)
  have hident (t : ℕ) : (N t)⁻¹ * (N t * L t)^2 = (B t)^2 := by
    dsimp [B]
    simp only [mul_pow, Real.sq_sqrt (le_of_lt (hNpos t))]
    field_simp [ne_of_gt (hNpos t)]
  have ha (t : ℕ) : 0 ≤ (N t)⁻¹ := inv_nonneg.mpr (le_of_lt (hNpos t))
  have hr (t : ℕ) : 0 ≤ frontierRate (n t) (d t) (q t) := by
    unfold frontierRate
    exact le_min (by norm_num) (add_nonneg (ha t) (sq_nonneg _))
  constructor
  · intro hO
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
    have hrate0 : Tendsto (fun t => frontierRate (n t) (d t) (q t)) atTop (nhds 0) := by
      have hca : Tendsto (fun t => c * (N t)⁻¹) atTop (nhds 0) := by
        convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c)).mul
          (tendsto_inv_atTop_zero.comp hN) using 1 <;> simp [N]
      apply squeeze_zero' (Eventually.of_forall hr) ?_ hca
      filter_upwards [hc] with t ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hr t),
        abs_of_nonneg (ha t)] at ht
      exact ht
    have hsmall : ∀ᶠ t in atTop, frontierRate (n t) (d t) (q t) < 1 :=
      hrate0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    rw [Asymptotics.isBigO_iff]
    refine ⟨max 1 c, ?_⟩
    filter_upwards [hc, hsmall] with t hct hst
    have hsum : (N t)⁻¹ + ((d t : ℝ) / (N t * L t)) ^ 2 < 1 := by
      by_contra hnot
      have hge : 1 ≤ (N t)⁻¹ + ((d t : ℝ) / (N t * L t)) ^ 2 :=
        le_of_not_gt hnot
      simp [frontierRate, N, L, min_eq_left hge] at hst
    have hrate : frontierRate (n t) (d t) (q t) =
        (N t)⁻¹ + ((d t : ℝ) / (N t * L t)) ^ 2 := by
      simp [frontierRate, N, L, min_eq_right (le_of_lt hsum)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hr t),
      abs_of_nonneg (ha t), hrate] at hct
    have hb : ((d t : ℝ) / (N t * L t)) ^ 2 ≤ c * (N t)⁻¹ := by
      nlinarith [ha t]
    have hsq : (d t : ℝ)^2 ≤ c * (B t)^2 := by
      rw [div_pow] at hb
      have hp := (mul_le_mul_of_nonneg_right hb (le_of_lt (pow_pos (hden t) 2)))
      rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos (hden t) 2)), mul_assoc, hident] at hp
      nlinarith
    have hK : 0 ≤ (max 1 c) * B t := mul_nonneg (by positivity) (le_of_lt (hB t))
    have hcm : c ≤ (max 1 c)^2 := by
      have h1 : 1 ≤ max 1 c := le_max_left _ _
      have hc' : c ≤ max 1 c := le_max_right _ _
      nlinarith
    have hdim : (d t : ℝ) ≤ max 1 c * B t := by
      have hB2 : 0 ≤ (B t)^2 := sq_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr hcm) hB2]
    change ‖(d t : ℝ)‖ ≤ max 1 c * ‖B t‖
    have hd0 : (0 : ℝ) ≤ (d t : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0,
      abs_of_nonneg (le_of_lt (hB t))]
    exact hdim
  · intro hO
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
    rw [Asymptotics.isBigO_iff]
    refine ⟨1 + c^2, ?_⟩
    filter_upwards [hc] with t hct
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (le_of_lt (hB t))] at hct
    have hsq : (d t : ℝ)^2 ≤ c^2 * (B t)^2 := by
      have hcB : 0 ≤ c * B t := le_trans (Nat.cast_nonneg _) hct
      nlinarith
    have hb : ((d t : ℝ) / (N t * L t)) ^ 2 ≤ c^2 * (N t)⁻¹ := by
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos (hden t) 2)).2
      rw [mul_assoc, hident]
      exact hsq
    have hrate : frontierRate (n t) (d t) (q t) ≤ (1 + c^2) * (N t)⁻¹ := by
      unfold frontierRate
      calc
        min 1 ((N t)⁻¹ + ((d t : ℝ) / (N t * L t)) ^ 2) ≤
          (N t)⁻¹ + ((d t : ℝ) / (N t * L t)) ^ 2 := min_le_right _ _
        _ ≤ (1 + c^2) * (N t)⁻¹ := by nlinarith
    change ‖frontierRate (n t) (d t) (q t)‖ ≤ (1 + c^2) * ‖(N t)⁻¹‖
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hr t), abs_of_nonneg (ha t)]
      using hrate

-- @node: prop:phase-boundaries
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hslice,hN), [the stated mathematical conclusion holds](goal). -/
theorem phase_boundaries (n d : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : ∀ t, 1 ≤ n t) (hd : ∀ t, 1 ≤ d t)
    (hq : ∀ t, 0 < q t ∧ q t ≤ 1)
    (hslice : ∀ t, RareArrivalSlice (n t) (q t))
    (hN : Tendsto (fun t => effectiveSize (n t) (q t)) atTop atTop) :
    (Tendsto (fun t => minimaxRisk (n t) (d t) (q t)) atTop (nhds 0) ↔
      (fun t => (d t : ℝ)) =o[atTop]
        (fun t => effectiveSize (n t) (q t) * logScale (n t) (q t))) ∧
    ((fun t => minimaxRisk (n t) (d t) (q t)) =Θ[atTop]
       (fun t => (effectiveSize (n t) (q t))⁻¹) ↔
     (fun t => (d t : ℝ)) =O[atTop]
       (fun t => Real.sqrt (effectiveSize (n t) (q t)) * logScale (n t) (q t))) := by
  constructor
  · obtain ⟨c, C, hc, hcC, hbounds⟩ := matched_minimax_frontier
    have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
    have hr (t : ℕ) : 0 ≤ frontierRate (n t) (d t) (q t) := by
      unfold frontierRate
      have hNpos : 0 < effectiveSize (n t) (q t) := by
        unfold effectiveSize
        exact mul_pos (by exact_mod_cast hn t) (hq t).1
      exact le_min (by norm_num) (add_nonneg
        (inv_nonneg.mpr (le_of_lt hNpos)) (sq_nonneg _))
    have hboth (t : ℕ) :
        c * frontierRate (n t) (d t) (q t) ≤ minimaxRisk (n t) (d t) (q t) ∧
        minimaxRisk (n t) (d t) (q t) ≤ C * frontierRate (n t) (d t) (q t) :=
      hbounds (n t) (d t) (q t) (hn t) (hd t) (hq t).1 (hq t).2 (hslice t)
    have hiff : Tendsto (fun t => minimaxRisk (n t) (d t) (q t)) atTop (nhds 0) ↔
        Tendsto (fun t => frontierRate (n t) (d t) (q t)) atTop (nhds 0) := by
      constructor
      · intro h
        apply squeeze_zero hr (fun t => ?_)
          (by convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => c⁻¹) atTop (nhds c⁻¹)).mul h using 1 <;> simp)
        have hle := (hboth t).1
        have hle' : frontierRate (n t) (d t) (q t) ≤
            minimaxRisk (n t) (d t) (q t) / c :=
          (le_div_iff₀ hc).2 (by simpa [mul_comm] using hle)
        simpa [div_eq_inv_mul] using hle'
      · intro h
        apply squeeze_zero
          (fun t => le_trans (mul_nonneg (le_of_lt hc) (hr t)) (hboth t).1)
          (fun t => (hboth t).2)
        convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (nhds C)).mul h using 1 <;> simp
    exact hiff.trans (phase_frontier_rate_tendsto n d q hn (fun t => (hq t).1) hN)
  · obtain ⟨c, C, hc, hcC, hbounds⟩ := matched_minimax_frontier
    have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
    have hr (t : ℕ) : 0 ≤ frontierRate (n t) (d t) (q t) := by
      unfold frontierRate
      have hNpos : 0 < effectiveSize (n t) (q t) := by
        unfold effectiveSize
        exact mul_pos (by exact_mod_cast hn t) (hq t).1
      exact le_min (by norm_num) (add_nonneg
        (inv_nonneg.mpr (le_of_lt hNpos)) (sq_nonneg _))
    have hboth (t : ℕ) :
        c * frontierRate (n t) (d t) (q t) ≤ minimaxRisk (n t) (d t) (q t) ∧
        minimaxRisk (n t) (d t) (q t) ≤ C * frontierRate (n t) (d t) (q t) :=
      hbounds (n t) (d t) (q t) (hn t) (hd t) (hq t).1 (hq t).2 (hslice t)
    have hm (t : ℕ) : 0 ≤ minimaxRisk (n t) (d t) (q t) :=
      le_trans (mul_nonneg (le_of_lt hc) (hr t)) (hboth t).1
    have hRiskRate : (fun t => minimaxRisk (n t) (d t) (q t)) =Θ[atTop]
        (fun t => frontierRate (n t) (d t) (q t)) := by
      constructor
      · rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        filter_upwards with t
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hm t), abs_of_nonneg (hr t)]
        exact (hboth t).2
      · rw [Asymptotics.isBigO_iff]
        refine ⟨c⁻¹, ?_⟩
        filter_upwards with t
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hr t), abs_of_nonneg (hm t)]
        have hle : frontierRate (n t) (d t) (q t) ≤
            minimaxRisk (n t) (d t) (q t) / c :=
          (le_div_iff₀ hc).2 (by simpa [mul_comm] using (hboth t).1)
        simpa [div_eq_inv_mul] using hle
    have hbase := phase_rate_lower_bigO n d q hn (fun t => (hq t).1) hN
    have hdim := phase_dimension_rate_bigO n d q hn (fun t => (hq t).1) hN
    constructor
    · intro htheta
      exact hdim.mp (hRiskRate.2.trans htheta.1)
    · intro hO
      exact ⟨hRiskRate.1.trans (hdim.mpr hO), hbase.trans hRiskRate.2⟩

end CausalSmith.Stat.MarRareqLogfrontier
