module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Envelope
public import Causalean.Stat.Concentration.Localization.UniformDeviation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rate discharge for localized-deviation peeling

This module proves that the corrected localized-deviation peeling condition accepts the
finite-VC rate and an explicit rate equivalent to the Lipschitz scale `n⁻²⁄⁵`.  The only
remaining geometric input is that a stated peeling depth covers the envelope radius.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open Filter Topology

/-- For [an envelope radius](hyp:b), [a failure probability](hyp:δ), [a target rate](hyp:ρ),
and [a sample size](hyp:n), the [localized-deviation peeling condition](goal) asserts that one
dyadic depth covers the envelope and absorbs both Bousquet slack terms. -/
def PeelingCondition (b δ ρ : ℝ) (n : ℕ) : Prop :=
  ∃ L : ℕ,
    b ≤ ρ * (2 : ℝ) ^ L ∧
    2 * Real.sqrt
        ((1 + 8 * b) * Real.log (2 * ((L : ℝ) + 1) / δ) / n)
      + 8 * b * Real.log (2 * ((L : ℝ) + 1) / δ) / (n * ρ) ≤ ρ

/-- If [the envelope radius is nonnegative](hyp:hb), [the failure probability lies in
`(0,1]`](hyp:hδ,hδ'), [the sample size and target rate are positive](hyp:hn,hρ), [depth `L`
covers the envelope](hyp:hcover), and [the normalized logarithmic cost is at most the displayed
constant](hyp:hq), then [the peeling condition holds](goal). -/
theorem peelingCondition_of_normalizedLog_le
    {b δ ρ : ℝ} {n L : ℕ}
    (hb : 0 ≤ b) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hn : 0 < n) (hρ : 0 < ρ)
    (hcover : b ≤ ρ * (2 : ℝ) ^ L)
    (hq : Real.log (2 * ((L : ℝ) + 1) / δ) /
        ((n : ℝ) * ρ ^ 2) ≤ (64 * (1 + 8 * b))⁻¹) :
    PeelingCondition b δ ρ n := by
  refine ⟨L, hcover, ?_⟩
  have hA : 0 < 1 + 8 * b := by positivity
  have hx : 0 ≤ Real.log (2 * ((L : ℝ) + 1) / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hρ0 : 0 ≤ ρ := hρ.le
  have hfirstsq :
      (1 + 8 * b) * Real.log (2 * ((L : ℝ) + 1) / δ) / n ≤ ρ ^ 2 / 64 := by
    field_simp [hnR.ne', hρ.ne', hA.ne'] at hq ⊢
    nlinarith
  have hfirst :
      2 * Real.sqrt ((1 + 8 * b) * Real.log (2 * ((L : ℝ) + 1) / δ) / n)
        ≤ ρ / 4 := by
    have hz : 0 ≤ (1 + 8 * b) * Real.log (2 * ((L : ℝ) + 1) / δ) / n := by
      positivity
    have hs : Real.sqrt
        ((1 + 8 * b) * Real.log (2 * ((L : ℝ) + 1) / δ) / n) ≤ ρ / 8 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith⟩
    nlinarith
  have hsecond :
      8 * b * Real.log (2 * ((L : ℝ) + 1) / δ) / (n * ρ) ≤ ρ / 8 := by
    rw [div_le_iff₀ (mul_pos hnR hρ)]
    rw [div_eq_mul_inv] at hq
    field_simp [hρ.ne'] at hq
    nlinarith
  linarith

private theorem tendsto_log_mul_add_one_div (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (c * (x + 1)) / x) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hlog : Tendsto (fun x : ℝ => Real.log (x + 1) / (x + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hratio : Tendsto (fun x : ℝ => (x + 1) / x) atTop (𝓝 1) := by
    have hzero : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
    have hsum :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hzero
    norm_num at hsum
    apply hsum.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp [hx]
  have hprod := hlog.mul hratio
  norm_num at hprod
  have hbase : Tendsto (fun x : ℝ => Real.log (x + 1) / x) atTop (𝓝 0) := by
    apply hprod.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ), eventually_ne_atTop (-1 : ℝ)]
      with x hx hx1
    have hxplus : x + 1 ≠ 0 := by
      intro h
      apply hx1
      linarith
    field_simp [hx, hxplus]
  have hcdiv : Tendsto (fun x : ℝ => Real.log c / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hsum := hcdiv.add hbase
  norm_num at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul hc.ne' (by positivity : x + 1 ≠ 0)]
  ring

/-- For [a positive leading constant](hyp:C), [a sample size](hyp:n), the [explicit Lipschitz
peeling rate](goal) is `C·sqrt((n+1)^(1/5)/n)`, which is equivalent to `C·n⁻²⁄⁵`. -/
noncomputable def lipschitzPeelingRate (C : ℝ) (n : ℕ) : ℝ :=
  C * Real.sqrt (((n : ℝ) + 1) ^ (1 / 5 : ℝ) / (n : ℝ))

/-- For [a leading constant](hyp:C) and [a positive sample size](hyp:hn), the [squared explicit
Lipschitz peeling rate equals `C²(n+1)^(1/5)/n`](goal), exhibiting the `n⁻⁴⁄⁵` squared rate. -/
@[simp] theorem lipschitzPeelingRate_sq (C : ℝ) {n : ℕ} (hn : 0 < n) :
    (lipschitzPeelingRate C n) ^ 2 =
      C ^ 2 * (((n : ℝ) + 1) ^ (1 / 5 : ℝ) / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : 0 ≤ ((n : ℝ) + 1) ^ (1 / 5 : ℝ) := by positivity
  unfold lipschitzPeelingRate
  rw [mul_pow, Real.sq_sqrt (div_nonneg hpow hnR.le)]

private theorem tendsto_log_mul_add_one_div_rpow_one_fifth (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
      Real.log (c * (x + 1)) / (x + 1) ^ (1 / 5 : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hlog : Tendsto (fun x : ℝ =>
      Real.log (x + 1) / (x + 1) ^ (1 / 5 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero.comp
        hshift
  have hpow : Tendsto (fun x : ℝ => (x + 1) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hshift
  have hcdiv : Tendsto (fun x : ℝ =>
      Real.log c / (x + 1) ^ (1 / 5 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hsum := hcdiv.add hlog
  norm_num at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul hc.ne' (by positivity : x + 1 ≠ 0)]
  ring

/-- For [a nonnegative envelope radius](hyp:hb), [a confidence level in `(0,1]`](hyp:hδ,hδ'),
and [a positive Lipschitz-rate constant](hyp:hC), there is [a sample-size threshold](goal) after
which every peeling depth `L ≤ n` that covers the envelope verifies the corrected peeling
condition at the explicit rate `lipschitzPeelingRate C n`. -/
theorem lipschitzPeelingRate_peelingCondition_eventually
    {b δ C : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) (hδ' : δ ≤ 1) (hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      L ≤ n →
      b ≤ lipschitzPeelingRate C n * (2 : ℝ) ^ L →
      PeelingCondition b δ (lipschitzPeelingRate C n) n := by
  let c : ℝ := 2 / δ
  have hc : 0 < c := div_pos (by norm_num) hδ
  have hlim : Tendsto (fun n : ℕ =>
      Real.log (c * ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ (1 / 5 : ℝ))
      atTop (𝓝 0) := by
    exact (tendsto_log_mul_add_one_div_rpow_one_fifth c hc).comp
      tendsto_natCast_atTop_atTop
  have hthreshold : 0 < C ^ 2 / (64 * (1 + 8 * b)) := by positivity
  have hevent := (tendsto_order.1 hlim).2 _ hthreshold
  have hall : ∀ᶠ m : ℕ in atTop, ∀ L : ℕ,
      L ≤ m →
      b ≤ lipschitzPeelingRate C m * (2 : ℝ) ^ L →
      PeelingCondition b δ (lipschitzPeelingRate C m) m := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with m hmlim hmpos
    intro L hL hcover
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hrate : 0 < lipschitzPeelingRate C m := by
      unfold lipschitzPeelingRate
      positivity
    apply peelingCondition_of_normalizedLog_le hb hδ hδ' hmpos hrate hcover
    have hlogmono :
      Real.log (2 * ((L : ℝ) + 1) / δ) ≤
        Real.log (c * ((m : ℝ) + 1)) := by
      apply Real.log_le_log
      · positivity
      · have hLR : (L : ℝ) ≤ m := by exact_mod_cast hL
        dsimp [c]
        rw [div_mul_eq_mul_div]
        exact (div_le_div_iff_of_pos_right hδ).2 (by nlinarith)
    have hdenom :
        (m : ℝ) * (lipschitzPeelingRate C m) ^ 2 =
          C ^ 2 * ((m : ℝ) + 1) ^ (1 / 5 : ℝ) := by
      unfold lipschitzPeelingRate
      have hpow : 0 ≤ ((m : ℝ) + 1) ^ (1 / 5 : ℝ) := by positivity
      rw [mul_pow, Real.sq_sqrt (div_nonneg hpow hmR.le)]
      field_simp [hmR.ne']
    rw [hdenom]
    have hupper := hmlim
    dsimp [c] at hupper
    have hdenpos : 0 < C ^ 2 * ((m : ℝ) + 1) ^ (1 / 5 : ℝ) := by positivity
    rw [div_le_iff₀ hdenpos]
    have hpowpos : 0 < ((m : ℝ) + 1) ^ (1 / 5 : ℝ) :=
      Real.rpow_pos_of_pos (by positivity) _
    rw [div_lt_iff₀ hpowpos] at hupper
    have hA : 0 < 1 + 8 * b := by positivity
    dsimp [c] at hlogmono
    calc
      Real.log (2 * ((L : ℝ) + 1) / δ) ≤
          Real.log (2 / δ * ((m : ℝ) + 1)) := hlogmono
      _ ≤ (64 * (1 + 8 * b))⁻¹ *
          (C ^ 2 * ((m : ℝ) + 1) ^ (1 / 5 : ℝ)) := by
        apply le_of_lt
        convert hupper using 1 <;> field_simp [hA.ne'] <;> ring
  exact eventually_atTop.1 hall

/-- For [a nonnegative envelope radius](hyp:hb), [a confidence level in `(0,1]`](hyp:hδ,hδ'),
[a VC tuning constant at least one](hyp:hK), and [a positive VC dimension](hyp:hd), there is
[a sample-size threshold](goal) after which every logarithmic peeling depth that covers the
envelope verifies the corrected peeling condition at `vcLocalizedSlope K d n`. -/
theorem vcLocalizedSlope_peelingCondition_eventually
    {b δ K : ℝ} {d : ℕ}
    (hb : 0 ≤ b) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hK : 1 ≤ K) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (L : ℝ) ≤ Real.log ((n : ℝ) + 1) →
      b ≤ vcLocalizedSlope K d n * (2 : ℝ) ^ L →
      PeelingCondition b δ (vcLocalizedSlope K d n) n := by
  let c : ℝ := 2 / δ
  have hc : 0 < c := div_pos (by norm_num) hδ
  have htend : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ =>
      Real.log (c * (Real.log ((n : ℝ) + 1) + 1)) /
        Real.log ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_log_mul_add_one_div c hc).comp htend
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hthreshold : 0 < 36 * K * d / (64 * (1 + 8 * b)) := by positivity
  have hevent := (tendsto_order.1 hlim).2 _ hthreshold
  have hall : ∀ᶠ m : ℕ in atTop, ∀ L : ℕ,
      (L : ℝ) ≤ Real.log ((m : ℝ) + 1) →
      b ≤ vcLocalizedSlope K d m * (2 : ℝ) ^ L →
      PeelingCondition b δ (vcLocalizedSlope K d m) m := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with m hmlim hmpos
    intro L hL hcover
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have htpos : 0 < Real.log ((m : ℝ) + 1) :=
      Real.log_pos (by exact_mod_cast Nat.one_lt_cast.mpr (Nat.lt_add_one_iff.mpr hmpos))
    have hrate : 0 < vcLocalizedSlope K d m :=
      vcLocalizedSlope_pos hKpos.le hmpos
    apply peelingCondition_of_normalizedLog_le hb hδ hδ' hmpos hrate hcover
    have hlogmono :
        Real.log (2 * ((L : ℝ) + 1) / δ) ≤
          Real.log (c * (Real.log ((m : ℝ) + 1) + 1)) := by
      apply Real.log_le_log
      · positivity
      · dsimp [c]
        rw [div_mul_eq_mul_div]
        exact (div_le_div_iff_of_pos_right hδ).2 (by nlinarith)
    have hinside :
        0 ≤ (K * (d : ℝ) * Real.log ((m : ℝ) + 1) + 1) / (m : ℝ) := by
      positivity
    have hdenom :
        (m : ℝ) * (vcLocalizedSlope K d m) ^ 2 =
          36 * (K * (d : ℝ) * Real.log ((m : ℝ) + 1) + 1) := by
      unfold vcLocalizedSlope
      rw [mul_pow, Real.sq_sqrt hinside]
      field_simp [hmR.ne']
      norm_num
    rw [hdenom]
    have hupper := hmlim
    dsimp [c] at hupper hlogmono
    rw [div_lt_iff₀ htpos] at hupper
    have hA : 0 < 1 + 8 * b := by positivity
    have hdenpos :
        0 < 36 * (K * (d : ℝ) * Real.log ((m : ℝ) + 1) + 1) := by positivity
    rw [div_le_iff₀ hdenpos]
    calc
      Real.log (2 * ((L : ℝ) + 1) / δ) ≤
          Real.log (2 / δ * (Real.log ((m : ℝ) + 1) + 1)) := hlogmono
      _ ≤ (64 * (1 + 8 * b))⁻¹ *
          (36 * (K * (d : ℝ) * Real.log ((m : ℝ) + 1) + 1)) := by
        apply le_of_lt
        field_simp [hA.ne'] at hupper ⊢
        nlinarith [mul_pos (mul_pos hKpos hdR) htpos]
  exact eventually_atTop.1 hall

end Causalean.Stat.Concentration
