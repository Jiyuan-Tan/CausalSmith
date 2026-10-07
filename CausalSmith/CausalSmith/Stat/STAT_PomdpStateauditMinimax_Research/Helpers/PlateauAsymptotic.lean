module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwVariance
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionAsymptotic
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.TCloneBudgetFrontier

/-! # Analytic packaging for the high-cardinality plateau. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open Filter

lemma signedDepthCardinality_log_bounds {t0 zeta B0 : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB0 : 1 ≤ B0) :
    ∃ cLog CLog : ℝ, 0 < cLog ∧ cLog ≤ CLog ∧
      ∀ T : Nat, 2 ≤ T →
        cLog * Real.log T ≤ (signedDepthCardinality T t0 zeta B0 : ℝ) ∧
        (signedDepthCardinality T t0 zeta B0 : ℝ) ≤ CLog * Real.log T := by
  let D : ℝ := 2 / t0 + zeta
  let l2 : ℝ := Real.log 2
  let cLog : ℝ := 1 / D
  let CLog : ℝ := (2 / D) * (1 + Real.log (16 * B0) / l2) + 4 / l2
  have hD : 0 < D := by dsimp [D]; positivity
  have hl2 : 0 < l2 := by dsimp [l2]; exact Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (16 * B0) := by
    apply Real.log_nonneg
    nlinarith
  have hc : 0 < cLog := by dsimp [cLog]; positivity
  have hcC : cLog ≤ CLog := by
    dsimp [cLog, CLog]
    have hq : 0 ≤ Real.log (16 * B0) / Real.log 2 :=
      div_nonneg hlogB hl2.le
    have htwoD : 1 / D ≤ 2 / D := by
      exact div_le_div_of_nonneg_right (by norm_num) hD.le
    have hterm : 0 ≤ 4 / Real.log 2 := by positivity
    nlinarith [mul_nonneg (show 0 ≤ 2 / D by positivity)
      (by linarith : 0 ≤ 1 + Real.log (16 * B0) / Real.log 2)]
  refine ⟨cLog, CLog, hc, hcC, ?_⟩
  intro T hT
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hTtwo : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by linarith)
  let x : ℝ := Real.log (16 * B0 * T) / D
  have harg : 1 < 16 * B0 * (T : ℝ) := by nlinarith
  have hx : 0 < x := div_pos (Real.log_pos harg) hD
  have hceil : 0 < ⌈x⌉ := Int.ceil_pos.mpr hx
  have hto : (((Int.toNat ⌈x⌉ : Nat) : ℝ)) = (⌈x⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hceil.le
  have hhor : signedDepthHorizon T t0 zeta B0 = Int.toNat ⌈x⌉ := by
    unfold signedDepthHorizon
    have hden : 2 * Real.log (1 / mixingAlpha t0) +
        Real.log (policyFactor zeta) = D := by
      dsimp [D]
      simp [mixingAlpha, policyFactor]
      field_simp
    rw [hden]
    change max 1 (Int.toNat ⌈x⌉) = Int.toNat ⌈x⌉
    apply max_eq_right
    omega
  have hxform : x = (Real.log (16 * B0) + Real.log (T : ℝ)) / D := by
    dsimp [x]
    rw [show 16 * B0 * (T : ℝ) = (16 * B0) * (T : ℝ) by ring,
      Real.log_mul (by positivity) (ne_of_gt hTr)]
  have hlowx : Real.log (T : ℝ) / D ≤ x := by
    rw [hxform]
    exact div_le_div_of_nonneg_right (by linarith) hD.le
  have hcard : (signedDepthCardinality T t0 zeta B0 : ℝ) =
      2 * ((⌈x⌉ : ℝ) + 1) := by
    rw [signedDepthCardinality, hhor]
    push_cast
    rw [hto]
  constructor
  · rw [hcard]
    have hxc : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
    have hq : Real.log (T : ℝ) / D ≤ (⌈x⌉ : ℝ) := hlowx.trans hxc
    have hceil0 : 0 ≤ (⌈x⌉ : ℝ) := by exact_mod_cast hceil.le
    dsimp [cLog]
    calc
      (1 / D) * Real.log (T : ℝ) = Real.log (T : ℝ) / D := by ring
      _ ≤ (⌈x⌉ : ℝ) := hq
      _ ≤ 2 * ((⌈x⌉ : ℝ) + 1) := by nlinarith
  · rw [hcard]
    have hxc : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
    have hlog2le : Real.log 2 ≤ Real.log (T : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hTr hTtwo
    have hlogB_le : Real.log (16 * B0) ≤
        (Real.log (16 * B0) / l2) * Real.log (T : ℝ) := by
      have hratio : 1 ≤ Real.log (T : ℝ) / l2 := by
        exact (le_div_iff₀ hl2).2 (by simpa [l2] using hlog2le)
      calc
        _ = Real.log (16 * B0) * 1 := by ring
        _ ≤ Real.log (16 * B0) * (Real.log (T : ℝ) / l2) :=
          mul_le_mul_of_nonneg_left hratio hlogB
        _ = _ := by ring
    have hxupper : x ≤
        ((1 / D) * (1 + Real.log (16 * B0) / l2)) * Real.log (T : ℝ) := by
      rw [hxform]
      calc
        (Real.log (16 * B0) + Real.log (T : ℝ)) / D ≤
            ((Real.log (16 * B0) / l2) * Real.log (T : ℝ) +
              Real.log (T : ℝ)) / D :=
          div_le_div_of_nonneg_right (by linarith [hlogB_le]) hD.le
        _ = ((1 / D) * (1 + Real.log (16 * B0) / l2)) *
              Real.log (T : ℝ) := by ring
    have hfour : 4 ≤ (4 / l2) * Real.log (T : ℝ) := by
      calc
        4 = (4 / l2) * l2 := by field_simp
        _ ≤ (4 / l2) * Real.log (T : ℝ) :=
          mul_le_mul_of_nonneg_left (by simpa [l2] using hlog2le) (by positivity)
    dsimp [CLog]
    calc
      2 * ((⌈x⌉ : ℝ) + 1) ≤ 2 * x + 4 := by linarith
      _ ≤ 2 * (((1 / D) * (1 + Real.log (16 * B0) / l2)) *
            Real.log (T : ℝ)) + 4 := by linarith
      _ ≤ 2 * (((1 / D) * (1 + Real.log (16 * B0) / l2)) *
            Real.log (T : ℝ)) + (4 / l2) * Real.log (T : ℝ) := by linarith
      _ = ((2 / D) * (1 + Real.log (16 * B0) / Real.log 2) +
            4 / Real.log 2) * Real.log (T : ℝ) := by dsimp [l2]; ring

/-- Along every diverging expected-audit sequence, the collision-calibrated
clone budget times the signed-depth cardinality is bounded above and below by
constant multiples of the squared expected audit count times `log T`. -/
lemma signedDepthCardinality_mul_cloneBudget_eventually_bounds
    {t0 zeta B0 delta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hB0 : 1 ≤ B0) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ cAud CAud : ℝ, 0 < cAud ∧ cAud ≤ CAud ∧
      ∀ (Tseq : Nat → Nat) (etaseq : Nat → ℝ),
        (∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1) →
        Tendsto (fun j => (Tseq j : ℝ) * etaseq j) atTop atTop →
        Filter.Eventually (fun j =>
          cAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j) ≤
              ((signedDepthCardinality (Tseq j) t0 zeta B0 *
                cloneBudget (Tseq j) (etaseq j) delta hdelta : Nat) : ℝ) ∧
            ((signedDepthCardinality (Tseq j) t0 zeta B0 *
              cloneBudget (Tseq j) (etaseq j) delta hdelta : Nat) : ℝ) ≤
              CAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j))
          atTop := by
  obtain ⟨cLog, CLog, hcLog, hcLogC, hcard⟩ :=
    signedDepthCardinality_log_bounds ht0 hzeta hB0
  let L : ℝ := -Real.log (1 - delta)
  have hL : 0 < L := by
    dsimp [L]
    have hp : 0 < 1 - delta := by linarith [hdelta.2]
    have hlt : 1 - delta < 1 := by linarith [hdelta.1]
    linarith [Real.log_neg hp hlt]
  let cAud : ℝ := cLog / (8 * L)
  let CAud : ℝ := 2 * CLog / L
  have hcAud : 0 < cAud := by dsimp [cAud]; positivity
  have hcAudC : cAud ≤ CAud := by
    dsimp [cAud, CAud]
    have hCL : 0 < CLog := lt_of_lt_of_le hcLog hcLogC
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * L) hL).2
    nlinarith
  refine ⟨cAud, CAud, hcAud, hcAudC, ?_⟩
  intro Tseq etaseq heta hmean
  have hclone := clone_budget_frontier.2.2.2.1 delta hdelta Tseq etaseq heta hmean
  have hscale := collisionScale_over_mean_sq_tendsto_half Tseq etaseq heta hmean
  have hclone_lo := (tendsto_order.1 hclone).1 (1 / 2 : ℝ) (by norm_num)
  have hclone_hi := (tendsto_order.1 hclone).2 (2 : ℝ) (by norm_num)
  have hscale_lo := (tendsto_order.1 hscale).1 (1 / 4 : ℝ) (by norm_num)
  have hscale_hi := (tendsto_order.1 hscale).2 (1 : ℝ) (by norm_num)
  have hmean2 := hmean.eventually_gt_atTop 2
  filter_upwards [hclone_lo, hclone_hi, hscale_lo, hscale_hi, hmean2] with
      j hjclo hjchi hjslo hjshi hjmean
  let mu : ℝ := (Tseq j : ℝ) * etaseq j
  let s : ℝ := collisionScale (Tseq j) (etaseq j)
  let m : ℝ := (cloneBudget (Tseq j) (etaseq j) delta hdelta : ℝ)
  have hmu : 0 < mu := by dsimp [mu]; linarith
  have hmu2 : 0 < mu ^ 2 := sq_pos_of_pos hmu
  have hslo : mu ^ 2 / 4 < s := by
    have hh := (lt_div_iff₀ hmu2).mp (by simpa [mu, s] using hjslo)
    simpa [div_eq_mul_inv, mul_comm, s] using hh
  have hs : 0 < s := lt_trans (by positivity) hslo
  have hsL : 0 < s / L := div_pos hs hL
  have hmlo : (1 / 2 : ℝ) * (s / L) < m := by
    exact (lt_div_iff₀ hsL).mp (by simpa [L, s, m] using hjclo)
  have hmhi : m < 2 * (s / L) := by
    exact (div_lt_iff₀ hsL).mp (by simpa [L, s, m] using hjchi)
  have hsupper : s < mu ^ 2 := by
    change s / mu ^ 2 < 1 at hjshi
    simpa using (div_lt_iff₀ hmu2).mp hjshi
  have hm_lower : mu ^ 2 / (8 * L) ≤ m := by
    calc
      mu ^ 2 / (8 * L) = (1 / 2 : ℝ) * ((mu ^ 2 / 4) / L) := by ring
      _ ≤ (1 / 2 : ℝ) * (s / L) := by
        gcongr
      _ ≤ m := hmlo.le
  have hm_upper : m ≤ 2 * mu ^ 2 / L := by
    calc
      m ≤ 2 * (s / L) := hmhi.le
      _ ≤ 2 * (mu ^ 2 / L) := by gcongr
      _ = 2 * mu ^ 2 / L := by ring
  have hT : 2 ≤ Tseq j := by
    have hmuT : mu ≤ (Tseq j : ℝ) := by
      dsimp [mu]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (heta j).2
    exact_mod_cast (show (2 : ℝ) ≤ Tseq j by linarith)
  obtain ⟨hcardlo, hcardhi⟩ := hcard (Tseq j) hT
  have hlog0 : 0 ≤ Real.log (Tseq j : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < Tseq j by omega))).le
  have hcard0 : 0 ≤ (signedDepthCardinality (Tseq j) t0 zeta B0 : ℝ) := by positivity
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  constructor
  · push_cast
    change cAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j) ≤
      (signedDepthCardinality (Tseq j) t0 zeta B0 : ℝ) * m
    have hp := mul_le_mul hcardlo hm_lower (by positivity) hcard0
    have heq : cAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 *
        Real.log (Tseq j) =
        (cLog * Real.log (Tseq j : ℝ)) * (mu ^ 2 / (8 * L)) := by
      dsimp [cAud, mu]
      ring
    rw [heq]
    exact hp
  · push_cast
    change (signedDepthCardinality (Tseq j) t0 zeta B0 : ℝ) * m ≤
      CAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j)
    have hp := mul_le_mul hcardhi hm_upper hm0
      (mul_nonneg (le_trans hcLog.le hcLogC) hlog0)
    have heq : (CLog * Real.log (Tseq j : ℝ)) * (2 * mu ^ 2 / L) =
        CAud * (etaseq j) ^ 2 * (Tseq j : ℝ) ^ 2 * Real.log (Tseq j) := by
      dsimp [CAud, mu]
      ring
    rw [← heq]
    exact hp

end CausalSmith.Stat.PomdpStateauditMinimax
