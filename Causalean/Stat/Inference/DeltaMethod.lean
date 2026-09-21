/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Delta method

Smooth-function CLT. Given `r_n (T_n − t₀) ⇒ Q` (in distribution),
`r_n → ∞`, and `g` differentiable at `t₀`, the rescaled image
`r_n (g(T_n) − g(t₀))` converges in distribution to the pushforward of `Q`
along the derivative `Dg(t₀)`. Square-root-rate wrappers are retained as
corollaries.

For scalar `g : ℝ → ℝ` and the project's Gaussian limit measure with variance parameter `σ²`, the
conclusion specialises to the same wrapper with variance parameter `g'² σ²`; negative variance
parameters are interpreted by `gaussianMeasure` as zero variance.

Mirrors `thm:par-delta-scalar` and `thm:par-delta-vector` in the spec doc
`doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.

Reference: van der Vaart (1998), Theorem 3.1.
-/

module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Limit.ConvergenceVec
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
This file proves smooth delta-method results at any nonnegative rate diverging
to infinity. The scalar theorem `deltaMethod_scalar_rate` transforms a Gaussian
limit through a differentiable real map and returns the Gaussian limit with
variance parameter `g' ^ 2 * σsq`.

The multivariate theorem `deltaMethod_rate` works at the probability-measure
level and maps the limiting law through the Fréchet derivative. The proofs use
the stochastic-order and tightness
utilities from `Causalean.Stat.Limit.Convergence`.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Scalar delta method -/

/-- **Scalar delta method at a general rate.** For a real-valued estimator sequence `Tn` of a
target `t₀`, suppose [the nonnegative rate `r` diverges to infinity](hyp:hrnonneg,hr), [the
rescaled deviation `r n * (Tn − t₀)` is measurable at every sample size](hyp:hTn), and [the
rescaled image `r n * (g(Tn) − g(t₀))` is measurable at every sample size](hyp:hgTn), where `g`
is [differentiable at `t₀` with derivative `g'`](hyp:_hg). If [the rescaled deviation converges
in distribution to the project's Gaussian law with mean zero and variance `σ²`](hyp:_hCLT), then
[the rescaled image converges in distribution to the same Gaussian wrapper with variance
`g'² · σ²`](goal).

The theorem does not require `σ²` to be nonnegative: `gaussianMeasure` clips negative variance
parameters to zero, so that project-specific convention is part of both the premise and the
conclusion.

Spec label: `thm:par-delta-scalar`.  Reference: van der Vaart 1998 Thm 3.1. -/
theorem deltaMethod_scalar_rate
    (Tn : ℕ → Ω → ℝ) (t₀ : ℝ) (g : ℝ → ℝ) (g' σsq : ℝ) (r : ℕ → ℝ)
    (hrnonneg : ∀ n, 0 ≤ r n) (hr : Tendsto r atTop atTop)
    (hTn : ∀ (n : ℕ), AEMeasurable (fun ω => r n * (Tn n ω - t₀)) μ)
    (hgTn : ∀ (n : ℕ), AEMeasurable (fun ω => r n * (g (Tn n ω) - g t₀)) μ)
    (_hg : HasDerivAt g g' t₀)
    (_hCLT : Tendsto_dist (fun (n : ℕ) ω => r n * (Tn n ω - t₀))
              (gaussianMeasure 0 σsq) μ hTn) :
    Tendsto_dist (fun (n : ℕ) ω => r n * (g (Tn n ω) - g t₀))
                 (gaussianMeasure 0 (g' ^ 2 * σsq)) μ hgTn := by
  let Sn : ℕ → Ω → ℝ := fun n ω => r n * (Tn n ω - t₀)
  let Zn : ℕ → Ω → ℝ := fun n ω => g' * Sn n ω
  let Yn : ℕ → Ω → ℝ := fun n ω => r n * (g (Tn n ω) - g t₀)
  have hSn_meas : ∀ n, AEMeasurable (Sn n) μ := by
    simpa [Sn] using hTn
  have hZn_meas : ∀ n, AEMeasurable (Zn n) μ := by
    intro n
    exact (hSn_meas n).const_mul g'
  have hYn_meas : ∀ n, AEMeasurable (Yn n) μ := by
    simpa [Yn] using hgTn
  have hSnBig : IsBigOp Sn (fun _ => (1 : ℝ)) μ := by
    simpa [Sn] using Tendsto_dist.tightness hTn _hCLT
  have hZdist :
      Tendsto_dist Zn (gaussianMeasure 0 (g' ^ 2 * σsq)) μ hZn_meas := by
    simpa [Sn, Zn] using
      Tendsto_dist.const_mul_tendsto_gaussian
        (a := fun _ : ℕ => g') (a₀ := g') (v := σsq)
        hSn_meas (by simpa [Sn] using _hCLT) tendsto_const_nhds
  have hInvSqrt : Tendsto (fun n : ℕ => (r n)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hr
  have hDeltaScaled : IsLittleOp (fun n ω => (r n)⁻¹ * Sn n ω)
      (fun _ => (1 : ℝ)) μ :=
    IsBigOp.const_mul_tendsto_zero hSnBig hInvSqrt
  have hEqD : ∀ᶠ (n : ℕ) in atTop,
      (fun ω => (r n)⁻¹ * Sn n ω) =
        (fun ω => Tn n ω - t₀) := by
    filter_upwards [tendsto_atTop.1 hr 1] with n hn
    funext ω
    have hr_ne : r n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
    calc
      (r n)⁻¹ * Sn n ω
          = (r n)⁻¹ * (r n * (Tn n ω - t₀)) := by
              rfl
      _ = ((r n)⁻¹ * r n) * (Tn n ω - t₀) := by
              ring
      _ = Tn n ω - t₀ := by rw [inv_mul_cancel₀ hr_ne, one_mul]
  have hDeltaProb : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun n => μ {ω | ρ < |Tn n ω - t₀|}) atTop (𝓝 0) := by
    intro ρ hρ
    have h := (Modes.isLittleOpF_iff_strict
      (fun _ => μ) (fun n ω => (r n)⁻¹ * Sn n ω) atTop
      (fun _ => (1 : ℝ)) (Eventually.of_forall fun _ => zero_lt_one)).mp
      hDeltaScaled ρ hρ
    refine h.congr' ?_
    filter_upwards [hEqD] with n hn
    congr 1
    ext ω
    change ρ * (fun _ => (1 : ℝ)) n <
        |(fun ω => (r n)⁻¹ * Sn n ω) ω| ↔
      ρ < |Tn n ω - t₀|
    have heq : (fun ω => (r n)⁻¹ * Sn n ω) ω = Tn n ω - t₀ :=
      congr_fun hn ω
    simp [heq]
  have hRn : IsLittleOp (fun n ω => Yn n ω - Zn n ω) (fun _ => (1 : ℝ)) μ := by
    apply (Modes.isLittleOpF_iff_strict
      (fun _ => μ) (fun n ω => Yn n ω - Zn n ω) atTop
      (fun _ => (1 : ℝ)) (Eventually.of_forall fun _ => zero_lt_one)).2
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · filter_upwards with n
      simp [hδtop]
    have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
    let α : ℝ := δ.toReal / 8
    have hαpos : 0 < α := by
      dsimp [α]
      linarith
    rcases hSnBig (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos) with
      ⟨M0, _hM0pos, hM0event⟩
    have hM0 := Filter.limsup_le_of_le (h := hM0event)
    let M : ℝ := max M0 1
    have hMpos : 0 < M := by
      dsimp [M]
      exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
    have hM0le : M0 ≤ M := by
      dsimp [M]
      exact le_max_left M0 1
    let A : ℕ → Set Ω := fun n => {ω | M < |Sn n ω|}
    let C : ℕ → Set Ω := fun n => {ω | ε < |Yn n ω - Zn n ω|}
    have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
      refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
      intro n
      apply measure_mono
      intro ω hω
      dsimp [A, Sn] at hω ⊢
      nlinarith
    have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
      rw [ENNReal.ofReal_lt_ofReal_iff]
      · linarith
      · linarith
    have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA halpha_two)
    let η : ℝ := ε / M
    have hηpos : 0 < η := by
      dsimp [η]
      exact div_pos hε hMpos
    have hderiv_event :
        ∀ᶠ x in 𝓝 t₀, |g x - g t₀ - g' * (x - t₀)| ≤ η * |x - t₀| := by
      have hderiv_event0 := _hg.isLittleO.def hηpos
      filter_upwards [hderiv_event0] with x hx
      simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hx
    rcases Metric.eventually_nhds_iff.mp hderiv_event with ⟨ρ, hρpos, hρprop⟩
    let B : ℕ → Set Ω := fun n => {ω | ρ ≤ |Tn n ω - t₀|}
    have hDeltaHalf := hDeltaProb (ρ / 2) (by linarith)
    have hBsmall0 := (ENNReal.tendsto_nhds_zero.mp hDeltaHalf) (ENNReal.ofReal α) (by
      exact ENNReal.ofReal_pos.mpr hαpos)
    have hBevent : ∀ᶠ n in atTop, μ (B n) < ENNReal.ofReal (2 * α) := by
      filter_upwards [hBsmall0] with n hn
      exact lt_of_le_of_lt (le_trans (measure_mono (by
        intro ω hω
        dsimp [B] at hω
        have : ρ / 2 < |Tn n ω - t₀| := by linarith
        exact this)) hn) halpha_two
    have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
      intro n
      have hsubset : C n ⊆ A n ∪ B n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ M < |Sn n ω| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotB : ¬ ρ ≤ |Tn n ω - t₀| := by
          intro hx
          exact hnot (Or.inr hx)
        have hSnle : |Sn n ω| ≤ M := le_of_not_gt hnotA
        have hnear : |Tn n ω - t₀| < ρ := lt_of_not_ge hnotB
        have hder := hρprop (by simpa [Real.dist_eq] using hnear)
        have hRabs : |Yn n ω - Zn n ω| ≤ η * |Sn n ω| := by
          calc
            |Yn n ω - Zn n ω|
                = |r n *
                    (g (Tn n ω) - g t₀ - g' * (Tn n ω - t₀))| := by
                  dsimp [Yn, Zn, Sn]
                  congr 1
                  ring
            _ = |r n| *
                  |g (Tn n ω) - g t₀ - g' * (Tn n ω - t₀)| := by
                  rw [abs_mul]
            _ = r n *
                  |g (Tn n ω) - g t₀ - g' * (Tn n ω - t₀)| := by
                  rw [abs_of_nonneg (hrnonneg n)]
            _ ≤ r n * (η * |Tn n ω - t₀|) := by
                  exact mul_le_mul_of_nonneg_left hder (hrnonneg n)
            _ = η * |Sn n ω| := by
                  dsimp [Sn]
                  rw [abs_mul, abs_of_nonneg (hrnonneg n)]
                  ring
        have hRle : |Yn n ω - Zn n ω| ≤ ε := by
          calc
            |Yn n ω - Zn n ω| ≤ η * |Sn n ω| := hRabs
            _ ≤ η * M := by exact mul_le_mul_of_nonneg_left hSnle (le_of_lt hηpos)
            _ = ε := by
              dsimp [η]
              field_simp [hMpos.ne']
        exact not_lt_of_ge hRle hω
      calc
        μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
        _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
    have hfour_alpha_lt_delta : ENNReal.ofReal (4 * α) < δ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [α]
        linarith
      · dsimp [α]
        linarith [le_of_lt hδpos]
      · exact hδtop
    filter_upwards [hAevent, hBevent] with n hAn hBn
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n < |Yn n ω - Zn n ω|} = μ (C n) := by
            simp [C]
      _ ≤ μ (A n) + μ (B n) := hpoint n
      _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) := ENNReal.add_lt_add hAn hBn
      _ = ENNReal.ofReal (4 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1; ring
        · linarith
        · linarith
      _ < δ := hfour_alpha_lt_delta
  simpa [Yn] using Tendsto_dist.add_isLittleOp_one hZn_meas hYn_meas hZdist hRn

/-- **Square-root-rate scalar delta method.** Given [measurability of the scaled original
statistic](hyp:hTn), [measurability of the scaled transform](hyp:hgTn),
[differentiability of `g` at `t₀`](hyp:_hg), and [the square-root-rate Gaussian limit for
`Tn`](hyp:_hCLT), [the transformed statistic has the derivative-scaled Gaussian limit](goal).

This is the `r n = √n` corollary of `deltaMethod_scalar_rate`. -/
theorem deltaMethod_scalar
    (Tn : ℕ → Ω → ℝ) (t₀ : ℝ) (g : ℝ → ℝ) (g' σsq : ℝ)
    (hTn : ∀ (n : ℕ), AEMeasurable (fun ω => Real.sqrt (n : ℝ) * (Tn n ω - t₀)) μ)
    (hgTn : ∀ (n : ℕ), AEMeasurable (fun ω => Real.sqrt (n : ℝ) * (g (Tn n ω) - g t₀)) μ)
    (_hg : HasDerivAt g g' t₀)
    (_hCLT : Tendsto_dist (fun (n : ℕ) ω => Real.sqrt (n : ℝ) * (Tn n ω - t₀))
              (gaussianMeasure 0 σsq) μ hTn) :
    Tendsto_dist (fun (n : ℕ) ω => Real.sqrt (n : ℝ) * (g (Tn n ω) - g t₀))
                 (gaussianMeasure 0 (g' ^ 2 * σsq)) μ hgTn := by
  exact deltaMethod_scalar_rate Tn t₀ g g' σsq (fun n => Real.sqrt (n : ℝ))
    (fun n => Real.sqrt_nonneg _)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    hTn hgTn _hg _hCLT

/-! ## Multivariate delta method

`Tendsto_dist` in `Causalean.Stat.Limit.Convergence` is hard-wired to ℝ-valued
sequences, so the multivariate form is stated directly at the
`ProbabilityMeasure`/pushforward level.  -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

section

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Multivariate delta method at a general rate.** Let `Tn` be a sequence of `E`-valued
estimators of a target `t₀`, let [the nonnegative rate `r` diverge to infinity](hyp:hrnonneg,hr),
and let `g : E → F` be [Fréchet-differentiable at `t₀` with derivative `Dg`](hyp:_hg). Given
[that the rescaled deviations `r n • (Tn − t₀)` are measurable](hyp:hTn) and [that their
images `r n • (g(Tn) − g(t₀))` are measurable](hyp:hgTn), if
[the laws of `r n • (Tn − t₀)` converge weakly to a probability measure `Q` on `E`](hyp:_hCLT),
then [the laws of `r n • (g(Tn) − g(t₀))` converge weakly to the pushforward of `Q` along the
linear map `Dg`](goal).

Phrased at the measure level: the laws of `√n • (T_n − t₀)` under `μ`
converge weakly to `Q`, and the laws of `√n • (g (T_n) − g t₀)` converge
weakly to `Q.toMeasure.map Dg`.

Spec label: `thm:par-delta-vector`.  Reference: van der Vaart 1998 Thm 3.1.

For Gaussian `Q` the pushforward gives the standard `Dg ∘ Σ ∘ Dg^*`
covariance; the abstract pushforward statement is left unspecialised. -/
theorem deltaMethod_rate
    (Tn : ℕ → Ω → E) (t₀ : E) (g : E → F) (Dg : E →L[ℝ] F)
    (Q : ProbabilityMeasure E) (r : ℕ → ℝ)
    (hrnonneg : ∀ n, 0 ≤ r n) (hr : Tendsto r atTop atTop)
    (hTn : ∀ n, AEMeasurable (fun ω => (r n) • (Tn n ω - t₀)) μ)
    (hgTn : ∀ n, AEMeasurable (fun ω => (r n) • (g (Tn n ω) - g t₀)) μ)
    (_hg : HasFDerivAt g Dg t₀)
    (_hCLT :
      Tendsto (β := ProbabilityMeasure E)
        (fun n =>
          ⟨μ.map (fun ω => (r n) • (Tn n ω - t₀)),
            Measure.isProbabilityMeasure_map (hTn n)⟩)
        atTop (𝓝 Q)) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun ω => (r n) • (g (Tn n ω) - g t₀)),
          Measure.isProbabilityMeasure_map (hgTn n)⟩)
      atTop
      (𝓝 ⟨Q.toMeasure.map Dg,
            Measure.isProbabilityMeasure_map Dg.continuous.measurable.aemeasurable⟩) := by
  let Sn : ℕ → Ω → E := fun n ω => (r n) • (Tn n ω - t₀)
  let Zn : ℕ → Ω → F := fun n ω => Dg (Sn n ω)
  let Yn : ℕ → Ω → F := fun n ω => (r n) • (g (Tn n ω) - g t₀)
  haveI : IsProbabilityMeasure (Q.toMeasure) := Q.2
  haveI : IsProbabilityMeasure (Q.toMeasure.map (fun x : E => ‖x‖)) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  haveI : IsProbabilityMeasure (Q.toMeasure.map Dg) :=
    Measure.isProbabilityMeasure_map Dg.continuous.measurable.aemeasurable
  have hSn_meas : ∀ n, AEMeasurable (Sn n) μ := by
    simpa [Sn] using hTn
  have hZn_meas : ∀ n, AEMeasurable (Zn n) μ := by
    intro n
    exact Dg.continuous.measurable.comp_aemeasurable (hSn_meas n)
  have hYn_meas : ∀ n, AEMeasurable (Yn n) μ := by
    simpa [Yn] using hgTn
  have hSnDist : Tendsto_dist_vec Sn Q.toMeasure μ hSn_meas := by
    apply (Tendsto_dist_vec_iff _ _ _ hSn_meas).2
    change Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map (Sn n), Measure.isProbabilityMeasure_map (hSn_meas n)⟩)
      atTop (𝓝 Q)
    simpa [Sn] using _hCLT
  have hNormSn_meas : ∀ n, AEMeasurable (fun ω => ‖Sn n ω‖) μ := by
    intro n
    exact continuous_norm.measurable.comp_aemeasurable (hSn_meas n)
  have hNormDistVec :
      Tendsto_dist_vec (fun n ω => ‖Sn n ω‖)
        (Q.toMeasure.map (fun x : E => ‖x‖)) μ hNormSn_meas := by
    apply (Tendsto_dist_vec_iff _ _ _ hNormSn_meas).2
    exact
      Tendsto_dist_vec.map_continuous
        (Q := Q.toMeasure) (g := fun x : E => ‖x‖)
        continuous_norm hSn_meas hSnDist
  have hNormDist :
      Tendsto_dist (fun n ω => ‖Sn n ω‖)
        (Q.toMeasure.map (fun x : E => ‖x‖)) μ hNormSn_meas := by
    apply (Tendsto_dist_iff _ _ _ hNormSn_meas).2
    have hNormDistVec' := (Tendsto_dist_vec_iff _ _ _ hNormSn_meas).1 hNormDistVec
    change Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨μ.map ((fun n ω => ‖Sn n ω‖) n),
          Measure.isProbabilityMeasure_map (hNormSn_meas n)⟩)
      atTop
      (𝓝 ⟨Q.toMeasure.map (fun x : E => ‖x‖), inferInstance⟩) at hNormDistVec'
    exact hNormDistVec'
  have hSnBig : IsBigOp (fun n ω => ‖Sn n ω‖) (fun _ => (1 : ℝ)) μ :=
    Tendsto_dist.tightness hNormSn_meas hNormDist
  have hInvSqrt : Tendsto (fun n : ℕ => (r n)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hr
  have hDeltaScaled : IsLittleOp
      (fun n ω => (r n)⁻¹ * ‖Sn n ω‖)
      (fun _ => (1 : ℝ)) μ :=
    IsBigOp.const_mul_tendsto_zero hSnBig hInvSqrt
  have hEqD : ∀ᶠ (n : ℕ) in atTop,
      (fun ω => (r n)⁻¹ * ‖Sn n ω‖) =
        (fun ω => ‖Tn n ω - t₀‖) := by
    filter_upwards [tendsto_atTop.1 hr 1] with n hn
    funext ω
    have hr_ne : r n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
    calc
      (r n)⁻¹ * ‖Sn n ω‖
          = (r n)⁻¹ *
              ‖(r n) • (Tn n ω - t₀)‖ := by
              rfl
      _ = (r n)⁻¹ *
              (r n * ‖Tn n ω - t₀‖) := by
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (hrnonneg n)]
      _ = ‖Tn n ω - t₀‖ := by
              rw [← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
  have hDeltaProb : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun n => μ {ω | ρ < ‖Tn n ω - t₀‖}) atTop (𝓝 0) := by
    intro ρ hρ
    have h := (Modes.isLittleOpF_iff_strict
      (fun _ => μ) (fun n ω => (r n)⁻¹ * ‖Sn n ω‖) atTop
      (fun _ => (1 : ℝ)) (Eventually.of_forall fun _ => zero_lt_one)).mp
      hDeltaScaled ρ hρ
    refine h.congr' ?_
    filter_upwards [hEqD] with n hn
    congr 1
    ext ω
    change ρ * (fun _ => (1 : ℝ)) n <
        |(fun ω => (r n)⁻¹ * ‖Sn n ω‖) ω| ↔
      ρ < ‖Tn n ω - t₀‖
    have heq : (fun ω => (r n)⁻¹ * ‖Sn n ω‖) ω =
        ‖Tn n ω - t₀‖ :=
      congr_fun hn ω
    simp [heq]
  have hRn : IsLittleOp (fun n ω => ‖Yn n ω - Zn n ω‖) (fun _ => (1 : ℝ)) μ := by
    apply (Modes.isLittleOpF_iff_strict
      (fun _ => μ) (fun n ω => ‖Yn n ω - Zn n ω‖) atTop
      (fun _ => (1 : ℝ)) (Eventually.of_forall fun _ => zero_lt_one)).2
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · filter_upwards with n
      simp [hδtop]
    have hδpos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
    let α : ℝ := δ.toReal / 8
    have hαpos : 0 < α := by
      dsimp [α]
      linarith
    rcases hSnBig (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos) with
      ⟨M0, _hM0pos, hM0event⟩
    have hM0 := Filter.limsup_le_of_le (h := hM0event)
    let M : ℝ := max M0 1
    have hMpos : 0 < M := by
      dsimp [M]
      exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
    have hM0le : M0 ≤ M := by
      dsimp [M]
      exact le_max_left M0 1
    let A : ℕ → Set Ω := fun n => {ω | M < ‖Sn n ω‖}
    let C : ℕ → Set Ω := fun n => {ω | ε < ‖Yn n ω - Zn n ω‖}
    have hlimA : Filter.limsup (fun n => μ (A n)) atTop ≤ ENNReal.ofReal α := by
      refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_)) hM0
      intro n
      apply measure_mono
      intro ω hω
      dsimp [A] at hω ⊢
      have hM0_lt : M0 < ‖Sn n ω‖ := lt_of_le_of_lt hM0le hω
      simpa [abs_of_nonneg (norm_nonneg (Sn n ω))] using hM0_lt.le
    have halpha_two : ENNReal.ofReal α < ENNReal.ofReal (2 * α) := by
      rw [ENNReal.ofReal_lt_ofReal_iff]
      · linarith
      · linarith
    have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA halpha_two)
    let η : ℝ := ε / M
    have hηpos : 0 < η := by
      dsimp [η]
      exact div_pos hε hMpos
    have hderiv_event :
        ∀ᶠ x in 𝓝 t₀, ‖g x - g t₀ - Dg (x - t₀)‖ ≤ η * ‖x - t₀‖ := by
      have hderiv_event0 := _hg.isLittleO.def hηpos
      filter_upwards [hderiv_event0] with x hx
      simpa using hx
    rcases Metric.eventually_nhds_iff.mp hderiv_event with ⟨ρ, hρpos, hρprop⟩
    let B : ℕ → Set Ω := fun n => {ω | ρ ≤ ‖Tn n ω - t₀‖}
    have hDeltaHalf := hDeltaProb (ρ / 2) (by linarith)
    have hBsmall0 := (ENNReal.tendsto_nhds_zero.mp hDeltaHalf) (ENNReal.ofReal α) (by
      exact ENNReal.ofReal_pos.mpr hαpos)
    have hBevent : ∀ᶠ n in atTop, μ (B n) < ENNReal.ofReal (2 * α) := by
      filter_upwards [hBsmall0] with n hn
      exact lt_of_le_of_lt (le_trans (measure_mono (by
        intro ω hω
        dsimp [B] at hω
        have : ρ / 2 < ‖Tn n ω - t₀‖ := by linarith
        exact this)) hn) halpha_two
    have hpoint : ∀ n, μ (C n) ≤ μ (A n) + μ (B n) := by
      intro n
      have hsubset : C n ⊆ A n ∪ B n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ M < ‖Sn n ω‖ := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotB : ¬ ρ ≤ ‖Tn n ω - t₀‖ := by
          intro hx
          exact hnot (Or.inr hx)
        have hSnle : ‖Sn n ω‖ ≤ M := le_of_not_gt hnotA
        have hnear : ‖Tn n ω - t₀‖ < ρ := lt_of_not_ge hnotB
        have hder := hρprop (by simpa [dist_eq_norm] using hnear)
        have hRnorm : ‖Yn n ω - Zn n ω‖ ≤ η * ‖Sn n ω‖ := by
          calc
            ‖Yn n ω - Zn n ω‖
                = ‖(r n) •
                    (g (Tn n ω) - g t₀ - Dg (Tn n ω - t₀))‖ := by
                  dsimp [Yn, Zn, Sn]
                  rw [Dg.map_smul]
                  congr 1
                  simp [smul_sub]
            _ = r n *
                  ‖g (Tn n ω) - g t₀ - Dg (Tn n ω - t₀)‖ := by
                  rw [norm_smul, Real.norm_eq_abs,
                    abs_of_nonneg (hrnonneg n)]
            _ ≤ r n * (η * ‖Tn n ω - t₀‖) := by
                  exact mul_le_mul_of_nonneg_left hder (hrnonneg n)
            _ = η * ‖Sn n ω‖ := by
                  dsimp [Sn]
                  rw [norm_smul, Real.norm_eq_abs,
                    abs_of_nonneg (hrnonneg n)]
                  ring
        have hRle : ‖Yn n ω - Zn n ω‖ ≤ ε := by
          calc
            ‖Yn n ω - Zn n ω‖ ≤ η * ‖Sn n ω‖ := hRnorm
            _ ≤ η * M := by exact mul_le_mul_of_nonneg_left hSnle (le_of_lt hηpos)
            _ = ε := by
              dsimp [η]
              field_simp [hMpos.ne']
        exact not_lt_of_ge hRle hω
      calc
        μ (C n) ≤ μ (A n ∪ B n) := measure_mono hsubset
        _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
    have hfour_alpha_lt_delta : ENNReal.ofReal (4 * α) < δ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [α]
        linarith
      · dsimp [α]
        linarith [le_of_lt hδpos]
      · exact hδtop
    filter_upwards [hAevent, hBevent] with n hAn hBn
    exact le_of_lt <| calc
      μ {ω | ε * (fun _ => (1 : ℝ)) n < |‖Yn n ω - Zn n ω‖|} = μ (C n) := by
            simp [C]
      _ ≤ μ (A n) + μ (B n) := hpoint n
      _ < ENNReal.ofReal (2 * α) + ENNReal.ofReal (2 * α) := ENNReal.add_lt_add hAn hBn
      _ = ENNReal.ofReal (4 * α) := by
        rw [← ENNReal.ofReal_add]
        · congr 1; ring
        · linarith
        · linarith
      _ < δ := hfour_alpha_lt_delta
  have hZdist : Tendsto_dist_vec Zn (Q.toMeasure.map Dg) μ hZn_meas := by
    apply (Tendsto_dist_vec_iff _ _ _ hZn_meas).2
    exact
      Tendsto_dist_vec.map_continuous
        (Q := Q.toMeasure) (g := fun x : E => Dg x)
        Dg.continuous hSn_meas hSnDist
  apply (Tendsto_dist_vec_iff _ _ _ hYn_meas).1
  exact Tendsto_dist_vec.add_isLittleOp_one
    (Q := Q.toMeasure.map Dg) (Xn := Zn) (Yn := Yn)
    hZn_meas hYn_meas hZdist hRn

/-- **Square-root-rate multivariate delta method.** Given [measurability of the scaled
original statistic](hyp:hTn), [measurability of the scaled transform](hyp:hgTn),
[Fréchet differentiability at the target](hyp:_hg), and [the square-root-rate weak
limit](hyp:_hCLT), [the transformed statistic converges to the derivative pushforward](goal).

This is the `r n = √n` corollary of `deltaMethod_rate`. -/
theorem deltaMethod
    (Tn : ℕ → Ω → E) (t₀ : E) (g : E → F) (Dg : E →L[ℝ] F)
    (Q : ProbabilityMeasure E)
    (hTn : ∀ (n : ℕ), AEMeasurable (fun ω => Real.sqrt (n : ℝ) • (Tn n ω - t₀)) μ)
    (hgTn : ∀ (n : ℕ), AEMeasurable (fun ω => Real.sqrt (n : ℝ) • (g (Tn n ω) - g t₀)) μ)
    (_hg : HasFDerivAt g Dg t₀)
    (_hCLT :
      Tendsto (β := ProbabilityMeasure E) (fun (n : ℕ) =>
          (⟨μ.map (fun ω => Real.sqrt (n : ℝ) • (Tn n ω - t₀)),
            Measure.isProbabilityMeasure_map (hTn n)⟩ : ProbabilityMeasure E))
        atTop (𝓝 Q)) :
    Tendsto (β := ProbabilityMeasure F) (fun (n : ℕ) =>
        (⟨μ.map (fun ω => Real.sqrt (n : ℝ) • (g (Tn n ω) - g t₀)),
          Measure.isProbabilityMeasure_map (hgTn n)⟩ : ProbabilityMeasure F))
      atTop
      (𝓝 ⟨Q.toMeasure.map Dg,
        Measure.isProbabilityMeasure_map Dg.continuous.measurable.aemeasurable⟩) := by
  exact deltaMethod_rate Tn t₀ g Dg Q (fun n => Real.sqrt (n : ℝ))
    (fun n => Real.sqrt_nonneg _)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    hTn hgTn _hg _hCLT

end

/-! ## Gaussian pushforwards -/

section GaussianPushforward

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- **Linear image of a Gaussian law.** For [a Gaussian probability law `Q`](hyp:Q) and
[a continuous linear map `Dg`](hyp:Dg), [the pushforward is Gaussian and its covariance
bilinear form is `Σ(Dg₀⁺ u, Dg₀⁺ v)`, equivalently the operator covariance
`Dg ∘ Σ ∘ Dg⁺`](goal).

This is the Gaussian specialization of the delta-method pushforward. -/
theorem gaussian_pushforward_covariance
    (Q : Measure G) [IsProbabilityMeasure Q] [IsGaussian Q] (Dg : G →L[ℝ] H) :
    IsGaussian (Q.map Dg) ∧
      ∀ u v, covarianceBilin (Q.map Dg) u v =
        covarianceBilin Q (Dg.adjoint u) (Dg.adjoint v) := by
  constructor
  · infer_instance
  · exact covarianceBilin_map IsGaussian.memLp_two_id Dg

end GaussianPushforward

end Causalean.Stat
