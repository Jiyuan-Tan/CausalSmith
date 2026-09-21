/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bahadur representation — inversion and assembly

The inversion-and-Taylor step proves
`Gₙ(q̂ₙ) = −f₀·√n(q̂ₙ − q₀) + o_p(1)`, then assembles sample-quantile asymptotic
linearity `sampleQuantile_isAsymLinear` and the generic
`sampleQuantile_quantileRegularity` bundle. Builds on the root-n rate layer.
-/

module
public import Causalean.Stat.Quantile.SampleQuantileBahadur.Rate

/-! # Bahadur Linearity and Assembly

This file finishes the elementary Bahadur derivation for the empirical sample
quantile. It proves that the atom term and Taylor remainder vanish, establishes
the inversion identity `IIDSample.sampleQuantile_inversion`, relates the
normalized quantile influence-function sum to the empirical process through
`IIDSample.normalizedSum_quantileIF_eq`, and assembles the derived asymptotic
linearity theorem `IIDSample.sampleQuantile_isAsymLinear`.

The endpoint theorem `IIDSample.sampleQuantile_quantileRegularity` packages the
derived remainder into the reusable `QuantileRegularity` structure from
`SampleQuantile.lean`, so downstream scalar and vector quantile CLTs do not need
to assume a Bahadur expansion separately for the ordinary sample quantile.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-! ## Inversion and Taylor expansion -/

omit [IsProbabilityMeasure μ] in
/-- **Sum of in-probability limits.**  If `Xn →ₚ 0` and `Yn →ₚ 0`
then `Xn + Yn →ₚ 0`.  Union bound: `{ε ≤ |Xn+Yn|} ⊆ {ε/2 ≤ |Xn|} ∪ {ε/2 ≤ |Yn|}`. -/
lemma Tendsto_inProb.add_zero_zero {Xn Yn : ℕ → Ω → ℝ}
    (hX : Tendsto_inProb Xn (fun _ => 0) μ) (hY : Tendsto_inProb Yn (fun _ => 0) μ) :
    Tendsto_inProb (fun n ω => Xn n ω + Yn n ω) (fun _ => 0) μ := by
  rw [Tendsto_inProb_iff] at hX hY ⊢
  rw [tendstoInMeasure_iff_norm] at hX hY ⊢
  intro ε hε
  have hX2 := hX (ε / 2) (by linarith)
  have hY2 := hY (ε / 2) (by linarith)
  have hsum := hX2.add hY2
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
  simp only [Set.mem_union, Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have : |Xn n ω + Yn n ω| < ε := by
    calc |Xn n ω + Yn n ω| ≤ |Xn n ω| + |Yn n ω| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  exact absurd hω (not_le.mpr this)

omit [IsProbabilityMeasure μ] in
/-- **Little-o in probability implies convergence in probability.**
An `IsLittleOp _ 1` sequence converges to
`0` in probability.  Both unwind to the same `μ{· < |·|} → 0` statement up to a
harmless `<`/`≤` slack (handled with `ε/2`). -/
lemma Tendsto_inProb.of_isLittleOp_one {Xn : ℕ → Ω → ℝ}
    (h : IsLittleOp Xn (fun _ => (1 : ℝ)) μ) :
    Tendsto_inProb Xn (fun _ => 0) μ := by
  rw [Tendsto_inProb_iff]
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h2 := h (ε / 2) (by linarith)
  simp only [mul_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun n => zero_le) (fun n => ?_)
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
  linarith

omit [IsProbabilityMeasure P] in
/-- **The sample-quantile atom term vanishes.** For [an iid sample](hyp:S) satisfying
[local quantile regularity](hyp:hreg), [the scaled empirical-cdf overshoot at the sample quantile,
`√n (F̂ₙ(q̂ₙ) − τ)`, converges to zero in probability](goal).

Inside the regularity neighborhood the atom bound is at most `1/n`; root-`n` tightness makes the
probability that the sample quantile leaves that neighborhood vanish. -/
lemma IIDSample.sampleQuantile_atom_term_tendsto_zero (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    Tendsto_inProb
      (fun n ω => Real.sqrt (n : ℝ) * (S.empiricalCDF (S.sampleQuantile τ n ω) n ω - τ))
      (fun _ => 0) μ := by
  rw [Tendsto_inProb_iff]
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨ρ, hρ, hcont⟩ := hreg.cont
  -- `1/√n → 0`, so eventually `1/√n < ε`; combine with the a.e. atom bound.
  have hInvSqrt : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have hsqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hsqrt_atTop
  set Un : ℕ → Ω → ℝ :=
    fun n ω => Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀) with hUn
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hUnBig : IsBigOp Un (fun _ => (1 : ℝ)) μ := by
    simpa [Un] using S.sampleQuantile_rate hreg
  have hscaled : Tendsto_inProb
      (fun n ω => (Real.sqrt (n : ℝ))⁻¹ * Un n ω) (fun _ => 0) μ :=
    Tendsto_inProb.of_isLittleOp_one (hUnBig.const_mul_tendsto_zero hInvSqrt)
  have hlocalTail : Tendsto
      (fun n : ℕ => μ {ω | ρ ≤ ‖(Real.sqrt (n : ℝ))⁻¹ * Un n ω - 0‖})
      atTop (nhds 0) :=
    (tendstoInMeasure_iff_norm.mp hscaled) ρ hρ
  have hev : ∀ᶠ n : ℕ in atTop, (Real.sqrt (n : ℝ))⁻¹ < ε := by
    have := (Metric.tendsto_nhds.mp hInvSqrt) ε hε
    filter_upwards [this] with n hn
    have hnn : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    exact hn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlocalTail
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev, (eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hnε hn1
  have hnpos : 0 < n := hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hatom := S.sampleQuantile_atom_bound hρ hcont hnpos
    hreg.tau_pos hreg.tau_lt_one
  apply measure_mono_ae
  filter_upwards [hatom] with ω hω
  intro hbad
  simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hbad ⊢
  have hnotlocal : ¬ S.sampleQuantile τ n ω ∈
      Set.Ioo (q₀ - ρ) (q₀ + ρ) := by
    intro hlocal
    have hatomω := hω hlocal
    have hbound : |Real.sqrt (n : ℝ) *
        (S.empiricalCDF (S.sampleQuantile τ n ω) n ω - τ)|
        ≤ (Real.sqrt (n : ℝ))⁻¹ := by
      rw [abs_mul, abs_of_nonneg hsq.le]
      calc
        Real.sqrt (n : ℝ) *
              |S.empiricalCDF (S.sampleQuantile τ n ω) n ω - τ|
            ≤ Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hatomω hsq.le
        _ = (Real.sqrt (n : ℝ))⁻¹ := by
          have h := Real.mul_self_sqrt hnR.le
          field_simp
          nlinarith [h]
    exact (not_lt_of_ge hbad) (lt_of_le_of_lt hbound hnε)
  have hrad : ρ ≤ |S.sampleQuantile τ n ω - q₀| := by
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hnotlocal
    rcases hnotlocal with hlo | hhi
    · rw [le_abs]
      exact Or.inr (by linarith)
    · rw [le_abs]
      exact Or.inl (by linarith)
  have hsqrtinv : (Real.sqrt (n : ℝ))⁻¹ * Real.sqrt (n : ℝ) = 1 :=
    inv_mul_cancel₀ hsq.ne'
  have hgoal : ρ ≤ |(Real.sqrt (n : ℝ))⁻¹ * Un n ω| := by
    simp only [Un, abs_mul, abs_inv, abs_of_pos hsq]
    rw [← mul_assoc, hsqrtinv, one_mul]
    exact hrad
  exact hgoal

/-- **The Taylor remainder vanishes at the sample quantile.**
Writing `R(y) = F(y) − F(q₀) −
f₀(y − q₀)` for the first-order Taylor remainder of `F = cdf P` at `q₀`, the
scaled remainder at the sample quantile vanishes in probability:
`√n · R(q̂ₙ) →ₚ 0`.  Mirrors the `hRn` block of `deltaMethod_scalar`: the driver
`Un = √n(q̂ₙ − q₀)` is `O_p(1)`, consistency `q̂ₙ →ₚ q₀` localizes the
derivative little-o `|R(y)| ≤ η|y − q₀|`, and `|√n·R(q̂ₙ)| ≤ η|Un|`. -/
lemma IIDSample.sampleQuantile_taylor_remainder_tendsto_zero (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    Tendsto_inProb
      (fun n ω => Real.sqrt (n : ℝ) *
        (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
          - f₀ * (S.sampleQuantile τ n ω - q₀)))
      (fun _ => 0) μ := by
  -- Driver `Un = √n(q̂ₙ − q₀)` is `O_p(1)` (L4).
  set Un : ℕ → Ω → ℝ := fun n ω => Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)
    with hUn
  have hUnBig : IsBigOp Un (fun _ => (1 : ℝ)) μ := S.sampleQuantile_rate hreg
  -- `(√n)⁻¹ → 0`.
  have hInvSqrt : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have hsqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hsqrt_atTop
  -- `(√n)⁻¹ · Un = q̂ₙ − q₀` (eventually), hence `q̂ₙ →ₚ q₀` (consistency).
  have hDeltaScaled : IsLittleOp (fun n ω => (Real.sqrt (n : ℝ))⁻¹ * Un n ω)
      (fun _ => (1 : ℝ)) μ :=
    IsBigOp.const_mul_tendsto_zero hUnBig hInvSqrt
  have hEqD : ∀ᶠ (n : ℕ) in atTop,
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ * Un n ω) =
        (fun ω => S.sampleQuantile τ n ω - q₀) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    funext ω
    have hnpos_nat : 0 < n := lt_of_lt_of_le zero_lt_one hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
    simp only [hUn]
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
  have hDeltaProb : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun n => μ {ω | ρ ≤ |S.sampleQuantile τ n ω - q₀|}) atTop (𝓝 0) := by
    intro ρ hρ
    have h := hDeltaScaled ρ hρ
    refine h.congr' ?_
    filter_upwards [hEqD] with n hn
    congr 1
    ext ω
    have heq : (Real.sqrt (n : ℝ))⁻¹ * Un n ω =
        S.sampleQuantile τ n ω - q₀ := congr_fun hn ω
    simp only [Set.mem_setOf_eq, mul_one, Real.norm_eq_abs]
    rw [heq]
  -- Now produce `IsLittleOp (√n·R(q̂ₙ)) 1`, copying `deltaMethod_scalar`'s hRn.
  apply Tendsto_inProb.of_isLittleOp_one
  apply (Modes.isLittleOpF_iff_strict _ _ _ _
    (Eventually.of_forall fun _ => zero_lt_one)).2
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n; simp [hδtop]
  have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  set α : ℝ := δ.toReal / 8 with hα
  have hαpos : 0 < α := by rw [hα]; linarith
  rcases hUnBig (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos) with
    ⟨M0, hM0pos, hM0⟩
  set M : ℝ := max M0 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  have hM0le : M0 ≤ M := le_max_left M0 1
  set A : ℕ → Set Ω := fun n => {ω | M < |Un n ω|} with hAdef
  set C : ℕ → Set Ω := fun n => {ω | ε < |Real.sqrt (n : ℝ) *
    (cdf P (S.sampleQuantile τ n ω) - cdf P q₀ - f₀ * (S.sampleQuantile τ n ω - q₀))|}
    with hCdef
  have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_))
      (Filter.limsup_le_of_le (h := hM0))
    intro n
    refine measure_mono fun ω hω => ?_
    simp only [hAdef, Set.mem_setOf_eq, mul_one, Real.norm_eq_abs] at hω ⊢
    nlinarith
  have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
  have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA halpha_two)
  set η : ℝ := ε / M with hη
  have hηpos : 0 < η := div_pos hε hMpos
  -- Derivative little-o, localized near `q₀`.
  have hderiv_event :
      ∀ᶠ x in 𝓝 q₀, |cdf P x - cdf P q₀ - f₀ * (x - q₀)| ≤ η * |x - q₀| := by
    have hderiv_event0 := hreg.hasDeriv.isLittleO.def hηpos
    filter_upwards [hderiv_event0] with x hx
    simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hx
  rcases Metric.eventually_nhds_iff.mp hderiv_event with ⟨ρ, hρpos, hρprop⟩
  set B : ℕ → Set Ω := fun n => {ω | ρ ≤ |S.sampleQuantile τ n ω - q₀|} with hBdef
  have hDeltaHalf := hDeltaProb (ρ / 2) (by linarith)
  have hBsmall0 := (ENNReal.tendsto_nhds_zero.mp hDeltaHalf) (ENNReal.ofReal α)
    (ENNReal.ofReal_pos.mpr hαpos)
  have hBevent : ∀ᶠ n in atTop, μ (B n) < ENNReal.ofReal (2 * α) := by
    filter_upwards [hBsmall0] with n hn
    refine lt_of_le_of_lt (le_trans (measure_mono fun ω hω => ?_) hn) halpha_two
    simp only [hBdef, Set.mem_setOf_eq] at hω
    simp only [Set.mem_setOf_eq]; linarith
  have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
    intro n
    have hsubset : C n ⊆ A n ∪ B n := by
      intro ω hω
      by_contra hnot
      have hnotA : ¬ M < |Un n ω| := fun hx => hnot (Or.inl hx)
      have hnotB : ¬ ρ ≤ |S.sampleQuantile τ n ω - q₀| := fun hx => hnot (Or.inr hx)
      have hUnle : |Un n ω| ≤ M := le_of_not_gt hnotA
      have hnear : |S.sampleQuantile τ n ω - q₀| < ρ := lt_of_not_ge hnotB
      have hder := hρprop (by simpa [Real.dist_eq] using hnear)
      -- `|√n·R(q̂ₙ)| ≤ η·|Un|` from the derivative bound and `Un = √n(q̂ₙ−q₀)`.
      have hRabs : |Real.sqrt (n : ℝ) *
          (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
            - f₀ * (S.sampleQuantile τ n ω - q₀))| ≤ η * |Un n ω| := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (n : ℝ) * |cdf P (S.sampleQuantile τ n ω) - cdf P q₀
                - f₀ * (S.sampleQuantile τ n ω - q₀)|
            ≤ Real.sqrt (n : ℝ) * (η * |S.sampleQuantile τ n ω - q₀|) :=
              mul_le_mul_of_nonneg_left hder (Real.sqrt_nonneg _)
          _ = η * |Un n ω| := by
              rw [hUn]; simp only
              rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]; ring
      have hRle : |Real.sqrt (n : ℝ) *
          (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
            - f₀ * (S.sampleQuantile τ n ω - q₀))| ≤ ε :=
        calc _ ≤ η * |Un n ω| := hRabs
          _ ≤ η * M := mul_le_mul_of_nonneg_left hUnle hηpos.le
          _ = ε := by rw [hη]; field_simp
      have hωlt : ε < |Real.sqrt (n : ℝ) *
          (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
            - f₀ * (S.sampleQuantile τ n ω - q₀))| := by
        simpa [hCdef, Set.mem_setOf_eq] using hω
      exact absurd hRle (not_le.mpr hωlt)
    exact le_trans (measure_mono hsubset) (measure_union_le (A n) (B n))
  have hfour_alpha_lt_delta : ENNReal.ofReal (4 * α) < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hδtop, hα]; linarith
  filter_upwards [hAevent, hBevent] with n hAn hBn
  refine le_of_lt <| calc
    μ {ω | ε * (fun _ => (1 : ℝ)) n < |Real.sqrt (n : ℝ) *
        (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
          - f₀ * (S.sampleQuantile τ n ω - q₀))|} = μ (C n) := by simp [hCdef]
    _ ≤ μ (A n) + μ (B n) := hpoint n
    _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) := ENNReal.add_lt_add hAn hBn
    _ = ENNReal.ofReal (4 * α) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    _ < δ := hfour_alpha_lt_delta

/-- **Sample-quantile inversion identity.** Given [a `SampleQuantileReg` regularity bundle
`hreg`](hyp:hreg) — interior quantile level, positive density $f_0$ at the population quantile
$q_0$, cdf identification, differentiability of the population cdf at $q_0$, and cdf continuity
on a positive-radius neighborhood of $q_0$ — [the empirical process $G_n$ evaluated at the
sample quantile $\hat q_n(\tau)$, plus
$f_0$ times the rescaled deviation $\sqrt n(\hat q_n(\tau)-q_0)$, converges to zero in
probability](goal); equivalently $G_n(\hat q_n(\tau)) = -f_0\sqrt n(\hat q_n(\tau)-q_0) + o_p(1)$.

Uses the switching relation (`τ ≤ F̂ₙ(q̂ₙ)` and atom bound `|F̂ₙ(q̂ₙ) − τ| ≤ 1/n`, hence
`√n(F̂ₙ(q̂ₙ) − τ) →ₚ 0`) together with the first-order Taylor expansion
`F(q̂ₙ) = τ + f₀(q̂ₙ − q₀) + o(q̂ₙ − q₀)` from `HasDerivAt F f₀ q₀`. -/
lemma IIDSample.sampleQuantile_inversion (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    Tendsto_inProb
      (fun n ω => S.empProcess n ω (S.sampleQuantile τ n ω)
        + f₀ * (Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)))
      (fun _ => 0) μ := by
  -- Atom term `Aₙ = √n(F̂ₙ(q̂ₙ) − τ) →ₚ 0`.
  have hAtom := S.sampleQuantile_atom_term_tendsto_zero hreg
  -- Taylor remainder `√n·R(q̂ₙ) →ₚ 0`; negate it.
  have hRem := S.sampleQuantile_taylor_remainder_tendsto_zero hreg
  have hRemNeg : Tendsto_inProb
      (fun n ω => -(Real.sqrt (n : ℝ) *
        (cdf P (S.sampleQuantile τ n ω) - cdf P q₀
          - f₀ * (S.sampleQuantile τ n ω - q₀)))) (fun _ => 0) μ := by
    rw [Tendsto_inProb_iff] at hRem ⊢
    rw [tendstoInMeasure_iff_norm] at hRem ⊢
    intro ε hε
    refine (hRem ε hε).congr fun n => ?_
    refine measure_congr (Eventually.of_forall fun ω => ?_)
    simp only [sub_zero, Real.norm_eq_abs, abs_neg]
  -- Sum of the two in-probability limits.
  have hsum := hAtom.add_zero_zero hRemNeg
  -- The target equals `Aₙ + (−√n·R(q̂ₙ))` pointwise (ring identity, using `τ = F(q₀)`).
  rw [Tendsto_inProb_iff] at hsum ⊢
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl hsum
  refine Eventually.of_forall fun ω => ?_
  simp only [IIDSample.empProcess, hreg.cdf_eq]
  ring

/-! ## Normalized-sum identity -/

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- The empirical-process fluctuation at the population quantile is exactly the
negative normalized influence-function sum: for [an i.i.d. real sample](hyp:S),
[a nonzero density value](hyp:_hf0), [identification of the population CDF at
the quantile](hyp:hcdf), [a sample size](hyp:n), and [an outcome](hyp:ω),
[the normalized sum equals `−Gₙ(q₀)/f₀`](goal).

The algebraic identity is total when the density value is zero; the nonzero
premise is retained by this interface. -/
lemma IIDSample.normalizedSum_quantileIF_eq (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (_hf0 : f₀ ≠ 0) (hcdf : cdf P q₀ = τ) (n : ℕ) (ω : Ω) :
    (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, quantileIF τ q₀ f₀ (S.Z i ω)
      = - S.empProcess n ω q₀ / f₀ := by
  -- `ψ_τ = −cdfIF/f₀` (using `cdf P q₀ = τ`), then the empirical-cdf key identity.
  have hpt : ∀ z, quantileIF τ q₀ f₀ z = - cdfIF P q₀ z / f₀ := by
    intro z; unfold quantileIF cdfIF; rw [hcdf]; ring
  have hemp : S.empProcess n ω q₀
      = (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, cdfIF P q₀ (S.Z i ω) := by
    have h := rescaledEmpiricalCDF_eq_normalizedSum S q₀ n ω
    simpa [IIDSample.empProcess, Finset.card_range] using h
  simp_rw [hpt]
  rw [hemp, show (∑ i ∈ Finset.range n, -cdfIF P q₀ (S.Z i ω) / f₀)
        = (- ∑ i ∈ Finset.range n, cdfIF P q₀ (S.Z i ω)) / f₀ by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]]
  ring

/-! ## Derived asymptotic linearity -/

omit [IsProbabilityMeasure μ] in
/-- Scalar multiple preserves in-probability convergence to `0`. -/
lemma Tendsto_inProb.const_mul_zero {Xn : ℕ → Ω → ℝ} (c : ℝ)
    (h : Tendsto_inProb Xn (fun _ => 0) μ) :
    Tendsto_inProb (fun n ω => c * Xn n ω) (fun _ => 0) μ := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [Tendsto_inProb_iff]
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hempty : ∀ n, {ω : Ω | ε ≤ ‖(0 : ℝ) * Xn n ω - 0‖} = (∅ : Set Ω) := by
      intro n; ext ω
      simp only [zero_mul, sub_zero, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_le]
      exact hε
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds
  · rw [Tendsto_inProb_iff] at h ⊢
    rw [tendstoInMeasure_iff_norm] at h ⊢
    intro ε hε
    have hcpos : 0 < |c| := abs_pos.mpr hc
    have h' := h (ε / |c|) (div_pos hε hcpos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'
      (fun _ => zero_le) (fun n => ?_)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    rw [abs_mul] at hω
    rw [div_le_iff₀ hcpos]
    calc ε ≤ |c| * |Xn n ω| := hω
      _ = |Xn n ω| * |c| := mul_comm _ _

/-- **Sample-quantile asymptotic linearity (derived).** Given [a `SampleQuantileReg` regularity
bundle `hreg`](hyp:hreg) for the population $\tau$-quantile $q_0$ with density $f_0$, [the sample
$\tau$-quantile $\hat q_n(\tau)$ is asymptotically linear at $q_0$ with influence function
$\psi_\tau$, the Bahadur remainder being proved — not assumed — $o_p(1)$](goal).

Combines L5 (inversion), L3 at `Uₙ = √n(q̂ₙ − q₀)` (which is `O_p(1)` by L4), and
the normalized-sum identity. -/
theorem IIDSample.sampleQuantile_isAsymLinear (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    IsAsymLinear (S.sampleQuantile τ) q₀ (quantileIF τ q₀ f₀) S (fun m => Finset.range m) := by
  refine ⟨quantileIF_mean_zero hreg.cdf_eq, quantileIF_sq_integrable, ?_⟩
  have hf0 : f₀ ≠ 0 := ne_of_gt hreg.density_pos
  -- L5: `empProcess(q̂ₙ) + f₀·√n(q̂ₙ−q₀) →ₚ 0`.
  have hP1 := S.sampleQuantile_inversion hreg
  -- L3 at the L4 rate, with `q₀ + Uₙ/√n = q̂ₙ`: `empProcess(q̂ₙ) − empProcess(q₀) →ₚ 0`.
  have hUn : IsBigOp (fun n ω => Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀))
      (fun _ => (1 : ℝ)) μ := S.sampleQuantile_rate hreg
  have hosc := S.empProcess_oscillation hreg hUn
  have hP2 : Tendsto_inProb
      (fun n ω => S.empProcess n ω (S.sampleQuantile τ n ω) - S.empProcess n ω q₀)
      (fun _ => 0) μ := by
    have heq : (fun n ω => S.empProcess n ω
          (q₀ + (Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)) / Real.sqrt (n : ℝ))
            - S.empProcess n ω q₀)
        = (fun n ω => S.empProcess n ω (S.sampleQuantile τ n ω) - S.empProcess n ω q₀) := by
      funext n ω
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [IIDSample.empProcess]
      · have hs : Real.sqrt (n : ℝ) ≠ 0 :=
          Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
        have harg : q₀ + (Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)) / Real.sqrt (n : ℝ)
            = S.sampleQuantile τ n ω := by
          rw [mul_comm, mul_div_assoc, div_self hs, mul_one]; ring
        rw [harg]
    rwa [heq] at hosc
  -- Assemble: `R̃ₙ = (1/f₀)·P1ₙ + (−1/f₀)·P2ₙ`.
  have hcP1 := hP1.const_mul_zero (1 / f₀)
  have hcP2 := hP2.const_mul_zero (-(1 / f₀))
  have hsum := Tendsto_inProb.add_zero_zero hcP1 hcP2
  have heq : (fun n ω =>
        (1 / f₀) * (S.empProcess n ω (S.sampleQuantile τ n ω)
            + f₀ * (Real.sqrt (n : ℝ) * (S.sampleQuantile τ n ω - q₀)))
          + -(1 / f₀) * (S.empProcess n ω (S.sampleQuantile τ n ω) - S.empProcess n ω q₀))
      = (fun n ω =>
        Real.sqrt ((Finset.range n).card : ℝ) * (S.sampleQuantile τ n ω - q₀)
          - (Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, quantileIF τ q₀ f₀ (S.Z i ω)) := by
    funext n ω
    rw [Finset.card_range, S.normalizedSum_quantileIF_eq hf0 hreg.cdf_eq n ω]
    field_simp
    ring
  rw [heq] at hsum
  exact hsum.isLittleOp_one

/-- **Sample quantile satisfies `QuantileRegularity` (derived Bahadur).** Given [a
`SampleQuantileReg` regularity bundle `hreg`](hyp:hreg) for the population $\tau$-quantile $q_0$
with density $f_0$, [the sample $\tau$-quantile sequence itself satisfies the generic
`QuantileRegularity` bundle for these parameters, with the Bahadur remainder now derived rather
than assumed](goal).

Downstream this hands the sample quantile to `QuantileRegularity.tendsto_normal`. -/
theorem IIDSample.sampleQuantile_quantileRegularity (S : IIDSample Ω ℝ μ P)
    {τ q₀ f₀ : ℝ} (hreg : SampleQuantileReg P τ q₀ f₀) :
    QuantileRegularity S (S.sampleQuantile τ) τ q₀ f₀ where
  tau_pos := hreg.tau_pos
  tau_lt_one := hreg.tau_lt_one
  density_pos := hreg.density_pos
  cdf_eq := hreg.cdf_eq
  hasDeriv := hreg.hasDeriv
  bahadur := (S.sampleQuantile_isAsymLinear hreg).remainder

end Causalean.Stat
