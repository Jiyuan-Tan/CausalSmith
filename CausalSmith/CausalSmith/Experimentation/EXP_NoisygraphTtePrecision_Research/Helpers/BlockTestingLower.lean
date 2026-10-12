module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ChannelTransfer
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MissingOnlyTesting
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.SeparatedPriorDecisions
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.FrontierLower

/-!
# Supported block decisions under the noisy channel

Independent OR transfer preserves the block-prior targets and contracts the
full-record testing distance. Separate decision reductions give risk and length.
-/

public section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false


/-- Given [the stated assumptions](hyp:h), [The complete block record is Borel in its prior and experimental draws.](goal) -/
-- @node: noisy_block_record_measurable
@[fun_prop] lemma noisy_block_record_measurable (n B s : ℕ) (σ : Bool) (h : ℝ) :
    Measurable (fun x : (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.SourcePartition B s × (Fin B → ℝ)) ×
      (Assign (Fin n) × Acq (Fin n)) => recordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h x.1) x.2) := by
  apply measurable_from_prod_countable_left
  intro ω
  apply measurable_from_prod_countable_right
  intro t
  simp only [recordOf, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd,
    zero_mul, add_zero]
  apply measurable_const.prodMk
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro i
  apply Measurable.add
  · apply Finset.measurable_sum
    intro ℓ hℓ
    by_cases hi : i ∈ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.recipientBlock n B s ℓ <;>
      simp only [hi, ite_true, ite_false] <;> fun_prop
  · exact measurable_const

/-- Given [the stated assumptions](hyp:h,hqr), [Conditioning on the finite source partition makes the block record kernel Borel.](goal) -/
-- @node: noisy_block_kernel_measurable
@[fun_prop] lemma noisy_block_kernel_measurable (n B s : ℕ) (σ : Bool) (h q r : ℝ)
    (hqr : ChannelDomain q r) :
    Measurable (fun ξ => (noisyDesign q r (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ)).map
      (recordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ))) := by
  apply measurable_from_prod_countable_right
  intro t
  let ξ₀ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.SourcePartition B s × (Fin B → ℝ) := (t, fun _ => 0)
  let :=  noisyDesign_probability q r hqr (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ₀)
  have hm : Measurable (fun x : (Fin B → ℝ) × (Assign (Fin n) × Acq (Fin n)) =>
      recordOf (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h (t, x.1)) x.2) :=
    (noisy_block_record_measurable n B s σ h).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact sign_measurable_map_parameter
    (noisyDesign q r (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ₀)) _ hm

/-- Given [the stated assumptions](hyp:h,hqr), [Applying the OR kernel to a block mixture realizes its entire target-channel law.](goal) -/
-- @node: noisy_block_mixture_transfer
lemma noisy_block_mixture_transfer (n B s : ℕ) (σ : Bool) (h q r : ℝ)
    (hqr : ChannelDomain q r) :
    (mixtureRecordLaw (channelSourceProb q r) 0 (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s)
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h)).bind (channelRecordKernel r) =
    mixtureRecordLaw q r (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h) := by
  have hp := (channelSourceProb_spec q r hqr).1
  have hr : r ∈ Set.Icc 0 1 := ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  unfold mixtureRecordLaw
  rw [Measure.bind_bind
    (noisy_block_kernel_measurable n B s σ h _ _ ⟨by norm_num, hp.1, hp.2⟩).aemeasurable
    (channelRecordKernel_measurable r hr).aemeasurable]
  congr 1
  funext ξ
  exact channel_transfer_law q r hqr _

/-- Given [the stated assumptions](hyp:hs,h,hfit), [The block targets are exactly constant, so their exceptional separation mass is zero.](goal) -/
-- @node: noisy_block_target_measurable
@[fun_prop] lemma noisy_block_target_measurable (n B s : ℕ) (hs : 1 ≤ s)
    (hfit : 2*(B*s) ≤ n) (σ : Bool) (h : ℝ) :
    Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ)) := by
  simp_rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule_tte n B s σ h hs hfit]
  fun_prop

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hB,hs,hsd,hqr,hfit), [Supported block tests give both decision lower bounds after independent OR transfer.](goal) -/
-- @node: noisy_block_decisions_lower
lemma noisy_block_decisions_lower (n d B s : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (hB : 1 ≤ B) (hs : 1 ≤ s) (hsd : s ≤ d)
    (hfit : 2*(B*s) ≤ n) (q r : ℝ) (hqr : ChannelDomain q r) :
    let h := (100*Real.pi)⁻¹ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s (channelSourceProb q r)
    let a := (B*s : ℕ)*h/n
    ENNReal.ofReal (a^2/4) ≤ minimaxRisk (noisyDesign (V := Fin n) q r) d ∧
    ENNReal.ofReal (3*a/5) ≤ minimaxLength (noisyDesign (V := Fin n) q r) d := by
  let p := channelSourceProb q r
  have hp := (channelSourceProb_spec q r hqr).1
  let h := (100*Real.pi)⁻¹ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s p
  let a : ℝ := (B*s : ℕ)*h/n
  have hscale := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale_pos_le_one B s p hB hs
  have hh : 0 < h := mul_pos (by positivity) hscale.1
  have hhu : h ≤ 1/4 := by
    calc
      h ≤ (100*Real.pi)⁻¹ := mul_le_of_le_one_right (by positivity) hscale.2
      _ ≤ 1/4 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ (by positivity : 0 < 100*Real.pi)).mpr
        nlinarith [Real.pi_gt_three]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hapos : 0 < a := div_pos (mul_pos (by exact_mod_cast
    (show 0 < B*s by positivity)) hh) hnpos
  have ha1 : a ≤ 1 := by
    have hcount : (B*s : ℕ) ≤ (n : ℝ) := by exact_mod_cast (show B*s ≤ n by omega)
    apply (div_le_one hnpos).mpr
    exact (mul_le_of_le_one_right (by positivity) (hhu.trans (by norm_num))).trans hcount
  let :=  CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.partitionLaw_probability B s
  let :=  CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockBaselineLaw_probability B
  let : IsProbabilityMeasure (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) := by
    unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw
    infer_instance
  have htest := missing_only_supported_testing n d s B hn hd hdu hs hsd hB hfit p hp
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n)) (noisyDesign_atoms p 0 ⟨by norm_num, hp.1, hp.2⟩).1 h hh le_rfl
  have hclass (σ : Bool) := (htest.1 σ).mono (fun _ hξ => hξ.1)
  have hsep (σ : Bool) : (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s).real
      {ξ | if σ then CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ) < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s σ h ξ)} ≤ 0 := by
    cases σ <;> simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule_tte n B s _ h hs hfit,
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf, a, neg_div]
  have hsourceP := separated_mixture_probability p 0 ⟨by norm_num, hp.1, hp.2⟩
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s true h)
    (noisy_block_kernel_measurable n B s true h p 0 ⟨by norm_num, hp.1, hp.2⟩)
  have hsourceM := separated_mixture_probability p 0 ⟨by norm_num, hp.1, hp.2⟩
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s false h)
    (noisy_block_kernel_measurable n B s false h p 0 ⟨by norm_num, hp.1, hp.2⟩)
  let :=  hsourceP
  let :=  hsourceM
  have htv : Causalean.Stat.tvDist
      (mixtureRecordLaw q r (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s true h))
      (mixtureRecordLaw q r (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s false h)) ≤ 1/2 := by
    rw [← noisy_block_mixture_transfer n B s true h q r hqr,
      ← noisy_block_mixture_transfer n B s false h q r hqr]
    exact (channel_transfer_tv r ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩ _ _).trans htest.2
  have hl := separated_prior_decisions n d q r hn hd hdu hqr
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockParamLaw B s)
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s true h) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockSchedule n B s false h)
    (noisy_block_kernel_measurable n B s true h q r hqr)
    (noisy_block_kernel_measurable n B s false h q r hqr)
    (noisy_block_target_measurable n B s hs hfit true h)
    (noisy_block_target_measurable n B s hs hfit false h)
    a 0 (1/2) hapos ha1 (by norm_num) (hclass true) (hclass false)
    (by simpa using hsep true) (by simpa using hsep false) htv
  change ENNReal.ofReal (a^2/4) ≤ _ ∧ ENNReal.ofReal (3*a/5) ≤ _
  convert hl using 1 <;> congr 2 <;> ring

/-- Given [the stated assumptions](hyp:hqr), [The calibrated comparison retention never exceeds the public true-edge probability.](goal) -/
-- @node: channelSourceProb_le
lemma channelSourceProb_le (q r : ℝ) (hqr : ChannelDomain q r) :
    channelSourceProb q r ≤ q := by
  by_cases hr : r < 1
  · rw [channelSourceProb, if_pos hr]
    apply (div_le_iff₀ (by linarith : 0 < 1-r)).mpr
    nlinarith [mul_nonneg hqr.1 (sub_nonneg.mpr hqr.2.2)]
  · rw [channelSourceProb, if_neg hr]
    exact hqr.1.trans hqr.2.1

/-- Given [the stated assumptions](hyp:hn,hd,hB,hs,hmn,hqr,hcap), [The block testing scale dominates both the degree and missing-edge costs.](goal) -/
-- @node: noisy_block_scale_dominates
lemma noisy_block_scale_dominates (n d B s : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hB : 1 ≤ B) (hs : 1 ≤ s) (hmn : B*s ≤ n)
    (hcap : s = d ∨ (n : ℝ)/16 ≤ s) (q r : ℝ) (hqr : ChannelDomain q r) :
    min 1 ((d : ℝ)^2/n + d/(n*q)) ≤
      2 * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s
        (channelSourceProb q r)^2 := by
  let p := channelSourceProb q r
  let α := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.retentionP s p
  have hp := (channelSourceProb_spec q r hqr).1
  have hα := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.retentionP_mem_Icc s p hp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hNpos : (0 : ℝ) < (B*s : ℕ) := by exact_mod_cast (show 0 < B*s by positivity)
  have hNle : (B*s : ℕ) ≤ (n : ℝ) := by exact_mod_cast hmn
  by_cases hαpos : 0 < α
  · have hden : 0 < (B*s : ℕ)*α := mul_pos hNpos hαpos
    have hsq : ((s : ℝ) / Real.sqrt ((B*s : ℕ)*α))^2 =
        (s : ℝ)^2/((B*s : ℕ)*α) := by
      rw [div_pow, Real.sq_sqrt hden.le]
    have hscale : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s p =
        min 1 ((s : ℝ)/Real.sqrt ((B*s : ℕ)*α)) := by
      rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale, if_pos hαpos]
    by_cases hclip : (s : ℝ)/Real.sqrt ((B*s : ℕ)*α) ≤ 1
    · rw [hscale, min_eq_right hclip, hsq]
      have hdenle : (B*s : ℕ)*α ≤ (n : ℝ) :=
        (mul_le_of_le_one_right hNpos.le hα.2).trans hNle
      rcases hcap with hsd | hlarge
      · subst s
        have hαq : α ≤ (d : ℝ)*q :=
          (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.retentionP_le_order_mul d p hp).trans
            (mul_le_mul_of_nonneg_left (channelSourceProb_le q r hqr) (by positivity))
        have hqpos : 0 < q := by
          by_contra h
          have hqle : q ≤ 0 := le_of_not_gt h
          have : (d : ℝ)*q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hqle
          linarith
        have hdeg : (d : ℝ)^2/n ≤ (d : ℝ)^2/((B*d : ℕ)*α) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hden hdenle
        have hmiss : (d : ℝ)/(n*q) ≤ (d : ℝ)^2/((B*d : ℕ)*α) := by
          apply (div_le_div_iff₀ (mul_pos hnpos hqpos) hden).mpr
          have hbound : (B*d : ℕ)*α ≤ (n : ℝ)*((d : ℝ)*q) :=
            (mul_le_mul_of_nonneg_left hαq hNpos.le).trans
              (mul_le_mul_of_nonneg_right hNle (by positivity))
          nlinarith [mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ d)]
        linarith [min_le_right (1 : ℝ) ((d : ℝ)^2/n + d/(n*q))]
      · have hnreal : (512 : ℝ) ≤ n := by exact_mod_cast hn
        have hbig : (n : ℝ) ≤ 2*(s : ℝ)^2 := by nlinarith
        have htwo : (1 : ℝ) ≤ 2*((s : ℝ)^2/((B*s : ℕ)*α)) :=
          by
          rw [← mul_div_assoc]
          exact (le_div_iff₀ hden).mpr (by nlinarith)
        linarith [min_le_left (1 : ℝ) ((d : ℝ)^2/n + d/(n*q))]
    · rw [hscale, min_eq_left (le_of_not_ge hclip), one_pow]
      linarith [min_le_left (1 : ℝ) ((d : ℝ)^2/n + d/(n*q))]
  · have hz : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s p = 1 := by
      rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale, if_neg hαpos]
    rw [hz, one_pow]
    linarith [min_le_left (1 : ℝ) ((d : ℝ)^2/n + d/(n*q))]

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [Rounded blocks occupy at least a quarter of the population and retain both lower costs.](goal) -/
-- @node: degree_missing_risk_strong
lemma degree_missing_risk_strong (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) :
    ENNReal.ofReal (min 1 ((d : ℝ)^2/n + d/(n*q)) / (1280000*Real.pi^2)) ≤
      minimaxRisk (noisyDesign (V := Fin n) q r) d := by
  let s := min d (n/8)
  let B := n/(2*s)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hsd : s ≤ d := Nat.min_le_left _ _
  have hsmall : 4*s < n := by dsimp [s]; omega
  obtain ⟨hB, hfit, hquarter⟩ :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.frontier_block_rounding n s hs hsmall
  have hcap : s = d ∨ (n : ℝ)/16 ≤ s := by
    by_cases heq : s = d
    · exact Or.inl heq
    · right
      have hround : n ≤ 16*s := by dsimp [s] at *; omega
      have hr : (n : ℝ) ≤ 16*(s : ℝ) := by exact_mod_cast hround
      linarith
  let t := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s
    (channelSourceProb q r)
  let k := (100*Real.pi)⁻¹
  let a : ℝ := (B*s : ℕ)*(k*t)/n
  have hscale := noisy_block_scale_dominates n d B s hn hd hB hs (by change B*s ≤ n; change 2*(B*s) ≤ n at hfit; omega) hcap q r hqr
  have ht := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale_pos_le_one
    B s (channelSourceProb q r) hB hs
  have hk : 0 < k := by dsimp [k]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : (1/4 : ℝ) ≤ (B*s : ℕ)/(n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by change (n : ℝ)/4 ≤ (B*s : ℕ) at hquarter; nlinarith [hquarter])
  have htarget : k*t/4 ≤ a := by
    calc
      k*t/4 = (1/4 : ℝ)*(k*t) := by ring
      _ ≤ ((B*s : ℕ)/(n : ℝ))*(k*t) :=
        mul_le_mul_of_nonneg_right hratio (mul_pos hk ht.1).le
      _ = a := by dsimp [a]; ring
  have hsq : (k*t/4)^2 ≤ a^2 :=
    (sq_le_sq₀ (div_nonneg (mul_pos hk ht.1).le (by norm_num))
      ((div_nonneg (mul_pos hk ht.1).le (by norm_num)).trans htarget)).mpr htarget
  have hid : (k*t/4)^2/4 = t^2/(640000*Real.pi^2) := by
    dsimp [k]
    field_simp
    <;> ring
  have hl := (noisy_block_decisions_lower n d B s (by omega) hd hdu hB hs hsd hfit q r hqr).1
  apply (ENNReal.ofReal_le_ofReal ?_).trans hl
  change min 1 ((d : ℝ)^2/n + d/(n*q))/(1280000*Real.pi^2) ≤ a^2/4
  calc
    _ ≤ (2*t^2)/(1280000*Real.pi^2) :=
      div_le_div_of_nonneg_right hscale (by positivity)
    _ = t^2/(640000*Real.pi^2) := by ring
    _ = (k*t/4)^2/4 := hid.symm
    _ ≤ a^2/4 := div_le_div_of_nonneg_right hsq (by norm_num)

end CausalSmith.Experimentation.NoisygraphTtePrecision
