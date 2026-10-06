module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.RateAlgebra

/-!
# Numerical consistency of the private value rate

Logarithmic comparisons and the consistency criterion for arbitrary resource sequences.
-/

public section
noncomputable section
open scoped Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated l condition](hyp:hL) and [the stated hx condition](hyp:hx). [The shifted logarithm lies between the unshifted logarithm and its logarithmic correction](goal). -/
-- @node: consistency_log_comparisons
lemma consistency_log_comparisons (L x : ℝ) (hL : 1 ≤ L) (hx : 0 ≤ x) :
    Real.log (1+x) ≤ Real.log (Real.exp 1+L*x) ∧
    Real.log (Real.exp 1+L*x) ≤ Real.log (1+x) + Real.log (Real.exp 1+L) := by
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr zero_lt_one
  have hp : 0 < Real.exp 1+L*x := by positivity
  constructor
  · apply Real.log_le_log (by positivity)
    nlinarith
  · rw [← Real.log_mul (by positivity : (1+x : ℝ) ≠ 0)
      (by positivity : (Real.exp 1+L : ℝ) ≠ 0)]
    apply Real.log_le_log hp
    nlinarith

/-- Assume [dimension at least two](hyp:hd), [the stated ht condition](hyp:ht), and [the stated hr condition](hyp:hr). [Off saturation the desired logarithmic ratio is bounded by the square root of the rate](goal). -/
-- @node: consistency_ratio_sq_le_rho
lemma consistency_ratio_sq_le_rho (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t)
    (hr : rho t d < 1) :
    (Real.log (1+(d : ℝ)^2/t)/logDim d)^2 ≤ rho t d := by
  have hLp := logDim_pos d hd
  have hL := (logDim_bounds d hd).1
  have hx : 0 ≤ (d : ℝ)^2/t := div_nonneg (sq_nonneg _) ht.le
  have hg : 0 ≤ Real.log (1+(d : ℝ)^2/t)/logDim d :=
    div_nonneg (Real.log_nonneg (by linarith)) hLp.le
  by_cases hb : (d : ℝ)^2 * logDim d ≤ t
  · rw [rho, if_pos hb]
    have hxL : (d : ℝ)^2/t * logDim d ≤ 1 := by
      apply (div_le_one ht).mpr at hb
      simpa [div_mul_eq_mul_div] using hb
    have hlog : Real.log (1+(d : ℝ)^2/t) ≤ (d : ℝ)^2/t := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < 1+(d : ℝ)^2/t by positivity)
      linarith
    have hgx : Real.log (1+(d : ℝ)^2/t)/logDim d ≤ ((d : ℝ)^2/t)/logDim d :=
      div_le_div_of_nonneg_right hlog hLp.le
    have hxg : (d : ℝ)^2/t / logDim d ≤ 1 := by
      apply (div_le_one hLp).mpr
      nlinarith
    have hpow : (Real.log (1+(d : ℝ)^2/t)/logDim d)^2 ≤ ((d : ℝ)^2/t)/logDim d := by
      nlinarith
    simpa [div_div] using hpow
  · rw [rho, if_neg hb] at hr ⊢
    have hw := (consistency_log_comparisons (logDim d) ((d : ℝ)^2/t) hL hx).1
    have hwg : Real.log (1+(d : ℝ)^2/t)/logDim d ≤
        Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d := by
      apply div_le_div_of_nonneg_right _ hLp.le
      simpa [div_mul_eq_mul_div, mul_comm] using hw
    have hmin : min 1 (Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d) =
        Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d := by
      apply min_eq_right
      by_contra hn
      rw [min_eq_left (le_of_not_ge hn)] at hr
      norm_num at hr
    rw [hmin]
    nlinarith

/-- Assume [dimension at least two](hyp:hd) and [the stated ht condition](hyp:ht). [Both branches are bounded by the logarithmic ratio, its correction, and a dense remainder](goal). -/
-- @node: consistency_rho_upper
lemma consistency_rho_upper (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : 0 < t) :
    rho t d ≤
      (Real.log (1+(d : ℝ)^2/t)/logDim d +
        Real.log (Real.exp 1+logDim d)/logDim d)^2 + (1/logDim d)^2 := by
  have hLp := logDim_pos d hd
  have hL := (logDim_bounds d hd).1
  have hx : 0 ≤ (d : ℝ)^2/t := div_nonneg (sq_nonneg _) ht.le
  have hg : 0 ≤ Real.log (1+(d : ℝ)^2/t)/logDim d :=
    div_nonneg (Real.log_nonneg (by linarith)) hLp.le
  have he : 0 ≤ Real.log (Real.exp 1+logDim d)/logDim d := by
    apply div_nonneg _ hLp.le
    apply Real.log_nonneg
    have he := Real.exp_pos (1 : ℝ)
    linarith
  by_cases hb : (d : ℝ)^2*logDim d ≤ t
  · rw [rho, if_pos hb]
    have hden : 0 < t*logDim d := mul_pos ht hLp
    have hbound : (d : ℝ)^2/(t*logDim d) ≤ (1/logDim d)^2 := by
      apply (div_le_iff₀ hden).mpr
      field_simp
      nlinarith
    exact hbound.trans (le_add_of_nonneg_left (sq_nonneg _))
  · rw [rho, if_neg hb]
    have hw := (consistency_log_comparisons (logDim d) ((d : ℝ)^2/t) hL hx).2
    have hwg : Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d ≤
        Real.log (1+(d : ℝ)^2/t)/logDim d +
          Real.log (Real.exp 1+logDim d)/logDim d := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hLp.le
      simpa [div_mul_eq_mul_div, mul_comm] using hw
    have hm := (min_le_right (1 : ℝ)
      (Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d)).trans hwg
    have hm0 : 0 ≤ min 1 (Real.log (Real.exp 1+(d : ℝ)^2*logDim d/t)/logDim d) := by
      apply le_min (by norm_num)
      apply div_nonneg _ hLp.le
      apply Real.log_nonneg
      have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
      have hz : 0 ≤ (d : ℝ)^2*logDim d/t := by positivity
      linarith
    nlinarith [sq_nonneg (1/logDim d)]

/-- [The logarithmic correction vanishes with dimension](goal). -/
-- @node: consistency_correction_tendsto
lemma consistency_correction_tendsto :
    Filter.Tendsto (fun d : ℕ => Real.log (Real.exp 1+logDim d)/logDim d)
      Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun d => logDim d + Real.exp 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [logDim_tendsto_atTop.eventually_ge_atTop (b-Real.exp 1)] with d hd
    linarith
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.exp 1) 1 (by norm_num)).comp
    hshift
  simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using hh

/-- Assume [the stated h condition](hyp:h). [The paper's exact consistency criterion holds for arbitrary, possibly oscillating resources](goal). -/
-- @node: rho_consistency_iff
lemma rho_consistency_iff (ns ds : ℕ → ℕ) (es : ℕ → ℝ)
    (h : ∀ k, Allowed (ns k) (ds k) (es k)) :
    (Filter.Tendsto (fun k => rho (ns k*(es k)^2) (ds k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun k => (ns k : ℝ)*(es k)^2) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => Real.log (1+(ds k : ℝ)^2/(ns k*(es k)^2))/logDim (ds k))
        Filter.atTop (nhds 0)) := by
  let t : ℕ → ℝ := fun k => ns k*(es k)^2
  let g : ℕ → ℝ := fun k => Real.log (1+(ds k : ℝ)^2/t k)/logDim (ds k)
  have ht (k : ℕ) : 0 < t k := by
    have hn : (0 : ℝ) < ns k := by exact_mod_cast (show 0 < ns k by have := (h k).1; omega)
    exact mul_pos hn (sq_pos_of_pos (h k).2.2.1)
  have hg (k : ℕ) : 0 ≤ g k := by
    apply div_nonneg _ (logDim_pos _ (h k).2.1).le
    apply Real.log_nonneg
    have hx : 0 ≤ (ds k : ℝ)^2/t k := by positivity
    linarith
  have hr (k : ℕ) : 0 ≤ rho (t k) (ds k) :=
    (le_min (by norm_num) (by positivity)).trans (rho_elementary_comparisons _ _ _ (h k)).1
  change Filter.Tendsto (fun k => rho (t k) (ds k)) _ _ ↔
    Filter.Tendsto t _ _ ∧ Filter.Tendsto g _ _
  constructor
  · intro hρ
    constructor
    · apply Filter.tendsto_atTop.mpr
      intro b
      have hB : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hsmall := hρ.eventually_lt_const (show (0 : ℝ) < 1/max b 1 by positivity)
      filter_upwards [hsmall] with k hk
      by_contra hbt
      have htB : t k ≤ max b 1 := (le_of_not_ge hbt).trans (le_max_left _ _)
      have hinv : 1/max b 1 ≤ 1/t k :=
        div_le_div_of_nonneg_left (by norm_num) (ht k) htB
      have hcap : 1/max b 1 ≤ 1 := (div_le_one hB).mpr (le_max_right _ _)
      have hlo := (rho_elementary_comparisons _ _ _ (h k)).1
      change min 1 (1/t k) ≤ rho (t k) (ds k) at hlo
      exact (not_lt_of_ge ((le_min hcap hinv).trans hlo)) hk
    · apply tendsto_order.mpr
      constructor
      · intro a ha
        exact Filter.Eventually.of_forall (fun k => ha.trans_le (hg k))
      · intro b hb
        filter_upwards [hρ.eventually_lt_const (sq_pos_of_pos hb),
          hρ.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with k hk hk1
        have hsq := consistency_ratio_sq_le_rho (ds k) (t k) (h k).2.1 (ht k) hk1
        change (g k)^2 ≤ rho (t k) (ds k) at hsq
        nlinarith [hg k]
  · rintro ⟨hT,hG⟩
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun k => ha.trans_le (hr k))
    · intro b hb
      let q : ℝ := Real.sqrt b / 4
      have hq : 0 < q := by dsimp [q]; positivity
      have hq2 : q^2 = b/16 := by
        dsimp [q]
        rw [div_pow, Real.sq_sqrt hb.le]
        norm_num
      have hE := consistency_correction_tendsto.eventually_lt_const hq
      have hInv : Filter.Tendsto (fun d : ℕ => 1/logDim d) Filter.atTop (nhds (0 : ℝ)) := by
        simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp logDim_tendsto_atTop)
      obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp (hE.and (hInv.eventually_lt_const hq))
      filter_upwards [hG.eventually_lt_const hq,
        hT.eventually_ge_atTop (4*(D : ℝ)^2/b+1)] with k hgq htk
      by_cases hd : D ≤ ds k
      · obtain ⟨heq, hiq⟩ := hD (ds k) hd
        have he0 : 0 ≤ Real.log (Real.exp 1+logDim (ds k))/logDim (ds k) := by
          apply div_nonneg _ (logDim_pos _ (h k).2.1).le
          apply Real.log_nonneg
          have hL := (logDim_bounds _ (h k).2.1).1
          have he := Real.exp_pos (1 : ℝ)
          linarith
        have hi0 : 0 ≤ 1/logDim (ds k) := by positivity [logDim_pos _ (h k).2.1]
        have hupper := consistency_rho_upper (ds k) (t k) (h k).2.1 (ht k)
        change rho (t k) (ds k) ≤
          (g k + Real.log (Real.exp 1+logDim (ds k))/logDim (ds k))^2 +
            (1/logDim (ds k))^2 at hupper
        nlinarith [hg k, sq_nonneg (g k + Real.log (Real.exp 1+logDim (ds k))/logDim (ds k))]
      · have hdR : (ds k : ℝ) ≤ D := by exact_mod_cast (le_of_not_ge hd)
        have hu := (rho_elementary_comparisons _ _ _ (h k)).2.1
        change rho (t k) (ds k) ≤ 4*min 1 ((ds k : ℝ)^2/t k) at hu
        have hmin := min_le_right (1 : ℝ) ((ds k : ℝ)^2/t k)
        have htarget : 4*((ds k : ℝ)^2/t k) < b := by
          rw [← mul_div_assoc, div_lt_iff₀ (ht k)]
          have hbmul := (div_le_iff₀ hb).mp (show 4*(D : ℝ)^2/b ≤ t k-1 by linarith)
          nlinarith [sq_nonneg (D : ℝ), sq_nonneg (ds k : ℝ)]
        exact lt_of_le_of_lt (hu.trans (mul_le_mul_of_nonneg_left hmin (by norm_num))) htarget

/-- [Pure numerical branch, consistency, parametric boundary and elbow assertions](goal). -/
-- @node: rate_resource_conclusions
lemma rate_resource_conclusions : RateResourceConclusions := by
  refine ⟨rho_saturation_iff, ?_, ?_⟩
  · intro ns ds es h
    refine ⟨?_, rho_parametric_comparable_iff ns ds es h, ?_⟩
    · exact rho_consistency_iff ns ds es h
    · exact rho_parametric_iff_bounded_dimension ns ds es h
  · exact rho_elbow_comparison

end CausalSmith.Stat.LdpOptvalueUniformFrontier
