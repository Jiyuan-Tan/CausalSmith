module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Basic
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.SmoothRemainder
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Uniformization
public import Causalean.Stat.CLT.GaussianLimit
public import Causalean.Stat.Quantile.SampleQuantileBahadur.Linearity

/-!
# Sampling and bootstrap linearization of smooth moment estimators

This module turns Fréchet differentiability at the population moment into the two first-order
expansions needed by `BootstrapAsymLinear`: one under the original iid sampling law and one under
the conditional Efron resampling law.  Only differentiability at the target is used.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}

private theorem finMean_sampleVector_vec {d n : ℕ}
    (S : IIDSample Omega X mu P) (g : X → EuclideanSpace ℝ (Fin d)) (omega : Omega) :
    finMean (fun i ↦ g (S.sampleVector n omega i)) = S.sampleMeanVec g n omega := by
  unfold finMean IIDSample.sampleVector IIDSample.sampleMeanVec
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ g (S.Z i omega)) n]

private theorem integrable_of_integrable_norm_sq
    {d : ℕ} (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P) [IsFiniteMeasure P] :
    Integrable g P := by
  have hmem : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2
  exact hmem.integrable (by norm_num)

private theorem sqrt_smul_sampleMeanVec_sub_eq_normalizedSum
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) :
    (fun (n : ℕ) omega ↦ Real.sqrt (n : ℝ) • (S.sampleMeanVec g n omega - m)) =
      IsAsymLinearVec.normalizedSum S (fun x ↦ g x - m) (fun k ↦ Finset.range k) := by
  funext n omega
  unfold IsAsymLinearVec.normalizedSum IIDSample.sampleMeanVec
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, smul_sub]
    rw [show (Real.sqrt (n : ℝ)) • ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (S.Z i omega)) =
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, g (S.Z i omega) by
      rw [← mul_smul]
      congr 1
      field_simp
      rw [hsqrt_sq]]
    rw [show (Real.sqrt (n : ℝ)) • m =
        (Real.sqrt (n : ℝ))⁻¹ • (n : ℝ) • m by
      rw [← mul_smul]
      congr 1
      field_simp
      rw [hsqrt_sq]]
    simp [Finset.smul_sum, Nat.cast_smul_eq_nsmul]

/-- **Sampling delta linearization.** For [an iid sample](hyp:S), a [measurable vector moment
with integrable squared norm](hyp:g,hg,hg2), and a [transform Fréchet differentiable at the
population moment](hyp:h,Dh,hderiv), [the square-root-scaled estimator remainder after its
influence-function sum converges to zero in probability](goal). -/
theorem samplingLinearization_smoothFunctionOfMeans
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (Dh : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hderiv : HasFDerivAt h Dh (∫ x, g x ∂P)) :
    Tendsto_inProb
      (fun n omega ↦
        Real.sqrt (n : ℝ) *
            (smoothMeanEstimator g h n (S.sampleVector n omega) - h (∫ x, g x ∂P)) -
          IsAsymLinear.normalizedSum S
            (fun x ↦ Dh (g x - ∫ y, g y ∂P))
            (fun k ↦ Finset.range k) n omega)
      (fun _ ↦ 0) mu := by
  let _ : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let m : EuclideanSpace ℝ (Fin d) := ∫ x, g x ∂P
  let psi : X → EuclideanSpace ℝ (Fin d) := fun x ↦ g x - m
  let T : ℕ → Omega → EuclideanSpace ℝ (Fin d) := S.sampleMeanVec g
  let Sn : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n omega ↦
    Real.sqrt (n : ℝ) • (T n omega - m)
  let R : ℕ → Omega → ℝ := fun n omega ↦
    Real.sqrt (n : ℝ) * (h (T n omega) - h m - Dh (T n omega - m))
  have hg_int : Integrable g P := integrable_of_integrable_norm_sq g hg hg2
  have hpsi : Measurable psi := by
    dsimp [psi, m]
    fun_prop
  have hpsi_mem : MemLp psi 2 P := by
    have hg_mem : MemLp g 2 P :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2
    exact hg_mem.sub (memLp_const m)
  have hpsi2 : Integrable (fun x ↦ ‖psi x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hpsi.aestronglyMeasurable).1 hpsi_mem
  have hpsi_mean : ∫ x, psi x ∂P = 0 := by
    dsimp [psi, m]
    rw [integral_sub hg_int (integrable_const _)]
    simp
  have hSn_eq : Sn = IsAsymLinearVec.normalizedSum S psi (fun k ↦ Finset.range k) := by
    exact sqrt_smul_sampleMeanVec_sub_eq_normalizedSum S g m
  have hSn_meas : ∀ n, AEMeasurable (Sn n) mu := by
    intro n
    dsimp [Sn, T]
    fun_prop
  have hSnDist : Tendsto_dist_vec Sn (gaussianLimit hpsi hpsi2) mu hSn_meas := by
    simpa only [hSn_eq] using S.clt_normalizedSum_vec hpsi hpsi2 hpsi_mean
  have hnorm_meas : ∀ n, AEMeasurable (fun omega ↦ ‖Sn n omega‖) mu := by
    intro n
    fun_prop
  let _ : IsProbabilityMeasure ((gaussianLimit hpsi hpsi2).map
      (fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖)) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hnormDist : Tendsto_dist (fun n omega ↦ ‖Sn n omega‖)
      ((gaussianLimit hpsi hpsi2).map fun z ↦ ‖z‖) mu hnorm_meas :=
    (Tendsto_dist_iff _ _ _ hnorm_meas).2
      (Tendsto_dist_vec.map_continuous continuous_norm hSn_meas hSnDist)
  have hSnBig : IsBigOp (fun n omega ↦ ‖Sn n omega‖) (fun _ ↦ (1 : ℝ)) mu :=
    Tendsto_dist.tightness hnorm_meas hnormDist
  have hTmeasure : TendstoInMeasure mu T atTop (fun _ ↦ m) :=
    S.sampleMeanVec_tendstoInMeasure hg hg_int
  have hRlittle : IsLittleOp R (fun _ ↦ (1 : ℝ)) mu := by
    apply (Modes.isLittleOpF_iff_strict _ _ _ _
      (Eventually.of_forall fun _ => zero_lt_one)).2
    intro epsilon hepsilon
    rw [ENNReal.tendsto_nhds_zero]
    intro delta hdelta
    by_cases hdeltatop : delta = ⊤
    · filter_upwards with n
      simp [hdeltatop]
    have hdeltapos : 0 < delta.toReal := ENNReal.toReal_pos (ne_of_gt hdelta) hdeltatop
    let alpha : ℝ := delta.toReal / 8
    have halpha : 0 < alpha := by dsimp [alpha]; linarith
    rcases hSnBig (ENNReal.ofReal alpha) (ENNReal.ofReal_pos.mpr halpha) with
      ⟨M0, hM0pos, hM0⟩
    let M : ℝ := max M0 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
    have hM0M : M0 ≤ M := le_max_left _ _
    let A : ℕ → Set Omega := fun n ↦ {omega | M < ‖Sn n omega‖}
    have hlimA : Filter.limsup (fun n ↦ mu (A n)) atTop ≤ ENNReal.ofReal alpha := by
      refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_))
        (Filter.limsup_le_of_le (h := hM0))
      intro n
      apply measure_mono
      intro omega homega
      dsimp [A] at homega ⊢
      have := lt_of_le_of_lt hM0M homega
      simpa [abs_of_nonneg (norm_nonneg _)] using this.le
    have halpha2 : ENNReal.ofReal alpha < ENNReal.ofReal (2 * alpha) := by
      rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
    have hAevent := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimA halpha2)
    let eta : ℝ := epsilon / M
    have heta : 0 < eta := div_pos hepsilon hM
    have hlocal : ∀ᶠ z in 𝓝 m,
        ‖h z - h m - Dh (z - m)‖ ≤ eta * ‖z - m‖ := by
      have h0 := (smoothRemainder_isLittleO hderiv).def heta
      simpa [m] using h0
    rcases Metric.eventually_nhds_iff.mp hlocal with ⟨rho, hrho, hrhoprop⟩
    have hTtail : Tendsto (fun n ↦ mu {omega | rho / 2 ≤ ‖T n omega - m‖})
        atTop (𝓝 0) := by
      rw [tendstoInMeasure_iff_norm] at hTmeasure
      exact hTmeasure (rho / 2) (by positivity)
    have hBsmall := (ENNReal.tendsto_nhds_zero.mp hTtail) (ENNReal.ofReal alpha)
      (ENNReal.ofReal_pos.mpr halpha)
    filter_upwards [hAevent, hBsmall] with n hAn hBn
    let B : Set Omega := {omega | rho ≤ ‖T n omega - m‖}
    let C : Set Omega := {omega | epsilon < |R n omega|}
    have hB : mu B < ENNReal.ofReal (2 * alpha) := by
      refine lt_of_le_of_lt (le_trans (measure_mono ?_) hBn) halpha2
      intro omega homega
      change rho ≤ ‖T n omega - m‖ at homega
      change rho / 2 ≤ ‖T n omega - m‖
      linarith
    have hsubset : C ⊆ A n ∪ B := by
      intro omega homega
      by_contra hnot
      have hSnle : ‖Sn n omega‖ ≤ M := le_of_not_gt (fun hA ↦ hnot (Or.inl hA))
      have hnear : ‖T n omega - m‖ < rho := lt_of_not_ge (fun hB' ↦ hnot (Or.inr hB'))
      have hder := hrhoprop (by simpa [dist_eq_norm] using hnear)
      have hRle : |R n omega| ≤ epsilon := by
        calc
          |R n omega| = Real.sqrt (n : ℝ) *
              ‖h (T n omega) - h m - Dh (T n omega - m)‖ := by
                dsimp [R]
                rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ Real.sqrt (n : ℝ) * (eta * ‖T n omega - m‖) :=
            mul_le_mul_of_nonneg_left hder (Real.sqrt_nonneg _)
          _ = eta * ‖Sn n omega‖ := by
            dsimp [Sn]
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
          _ ≤ eta * M := mul_le_mul_of_nonneg_left hSnle heta.le
          _ = epsilon := by dsimp [eta]; field_simp [hM.ne']
      exact not_lt_of_ge hRle homega
    have h4alpha : ENNReal.ofReal (4 * alpha) < delta := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal]
      · dsimp [alpha]; linarith
      · dsimp [alpha]; linarith
      · exact hdeltatop
    exact le_of_lt <| calc
      mu {omega | epsilon * (fun _ ↦ (1 : ℝ)) n < |R n omega|} = mu C := by simp [C]
      _ ≤ mu (A n ∪ B) := measure_mono hsubset
      _ ≤ mu (A n) + mu B := measure_union_le _ _
      _ < ENNReal.ofReal (2 * alpha) + ENNReal.ofReal (2 * alpha) :=
        ENNReal.add_lt_add hAn hB
      _ = ENNReal.ofReal (4 * alpha) := by
        rw [← ENNReal.ofReal_add] <;> try linarith
        congr 1 <;> ring
      _ < delta := h4alpha
  have hRprob := Tendsto_inProb.of_isLittleOp_one hRlittle
  rw [Tendsto_inProb_iff] at hRprob ⊢
  refine hRprob.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with n hn
  filter_upwards with omega
  dsimp [R, T, m]
  rw [← finMean_sampleVector_vec S g omega]
  unfold smoothMeanEstimator
  have hlin :
      IsAsymLinear.normalizedSum S
          (fun x ↦ Dh (g x - ∫ y, g y ∂P)) (fun k ↦ Finset.range k) n omega =
        Real.sqrt (n : ℝ) *
          Dh (finMean (fun i ↦ g (S.sampleVector n omega i)) - ∫ y, g y ∂P) := by
    unfold IsAsymLinear.normalizedSum finMean IIDSample.sampleVector
    simp only [Finset.card_range, ContinuousLinearMap.map_sub, map_sum, map_smul,
      smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hfin : (∑ i : Fin n, Dh (g (S.Z i omega))) =
        ∑ i ∈ Finset.range n, Dh (g (S.Z i omega)) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ Dh (g (S.Z i omega))) n
    rw [hfin]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp
    rw [hsqrt_sq]
  rw [hlin]
  ring

/-- **Conditional bootstrap delta linearization.** For [an iid sample](hyp:S), a [measurable
vector moment with integrable squared norm](hyp:g,hg,hg2), and a [transform Fréchet
differentiable at the population moment](hyp:h,Dh,hderiv), for every positive tolerance [the outer
sampling probability of a conditional bootstrap linearization failure tends to zero](goal). -/
theorem bootstrapLinearization_smoothFunctionOfMeans
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (Dh : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hderiv : HasFDerivAt h Dh (∫ x, g x ∂P)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ mu.real {omega |
          epsilon < (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon < abs
              (centeredEstimatorBootstrapStatistic
                  (smoothMeanEstimator g h) n (S.sampleVector n omega) xstar -
                centeredBootstrapSum
                  (fun x ↦ Dh (g x - ∫ y, g y ∂P))
                  (S.sampleVector n omega) xstar)}})
        atTop (𝓝 0) := by
  classical
  let _ : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let m : EuclideanSpace ℝ (Fin d) := ∫ x, g x ∂P
  let psi : X → EuclideanSpace ℝ (Fin d) := fun x ↦ g x - m
  let T : ℕ → Omega → EuclideanSpace ℝ (Fin d) := S.sampleMeanVec g
  let Sn : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n omega ↦
    Real.sqrt (n : ℝ) • (T n omega - m)
  have hg_int : Integrable g P := integrable_of_integrable_norm_sq g hg hg2
  have hpsi : Measurable psi := by
    dsimp [psi, m]
    fun_prop
  have hpsi_mem : MemLp psi 2 P := by
    have hg_mem : MemLp g 2 P :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2
    exact hg_mem.sub (memLp_const m)
  have hpsi2 : Integrable (fun x ↦ ‖psi x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hpsi.aestronglyMeasurable).1 hpsi_mem
  have hpsi_mean : ∫ x, psi x ∂P = 0 := by
    dsimp [psi, m]
    rw [integral_sub hg_int (integrable_const _)]
    simp
  have hSn_eq : Sn = IsAsymLinearVec.normalizedSum S psi (fun k ↦ Finset.range k) := by
    exact sqrt_smul_sampleMeanVec_sub_eq_normalizedSum S g m
  have hSn_meas : ∀ n, AEMeasurable (Sn n) mu := by
    intro n
    dsimp [Sn, T]
    fun_prop
  have hSnDist : Tendsto_dist_vec Sn (gaussianLimit hpsi hpsi2) mu hSn_meas := by
    simpa only [hSn_eq] using S.clt_normalizedSum_vec hpsi hpsi2 hpsi_mean
  have hnorm_meas : ∀ n, AEMeasurable (fun omega ↦ ‖Sn n omega‖) mu := by
    intro n
    fun_prop
  let _ : IsProbabilityMeasure ((gaussianLimit hpsi hpsi2).map
      (fun z : EuclideanSpace ℝ (Fin d) ↦ ‖z‖)) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hnormDist : Tendsto_dist (fun n omega ↦ ‖Sn n omega‖)
      ((gaussianLimit hpsi hpsi2).map fun z ↦ ‖z‖) mu hnorm_meas :=
    (Tendsto_dist_iff _ _ _ hnorm_meas).2
      (Tendsto_dist_vec.map_continuous continuous_norm hSn_meas hSnDist)
  have hSnBig : IsBigOp (fun n omega ↦ ‖Sn n omega‖) (fun _ ↦ (1 : ℝ)) mu :=
    Tendsto_dist.tightness hnorm_meas hnormDist
  intro epsilon hepsilon
  rw [Metric.tendsto_atTop]
  intro delta hdelta
  let alpha : ℝ := delta / 12
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  rcases hSnBig (ENNReal.ofReal alpha) (ENNReal.ofReal_pos.mpr halpha) with
    ⟨M₀, hM₀pos, hM₀⟩
  have hM₀lim : Filter.limsup
      (fun n ↦ mu {omega | M₀ < ‖Sn n omega‖}) atTop ≤ ENNReal.ofReal alpha := by
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall ?_))
      (Filter.limsup_le_of_le (h := hM₀))
    intro n
    apply measure_mono
    intro omega homega
    simpa [abs_of_nonneg (norm_nonneg _)] using homega.le
  have halpha_lt : ENNReal.ofReal alpha < ENNReal.ofReal (2 * alpha) := by
    rw [ENNReal.ofReal_lt_ofReal_iff] <;> linarith
  have hdataENN := Filter.eventually_lt_of_limsup_lt
    (lt_of_le_of_lt hM₀lim halpha_lt)
  have hdata : ∀ᶠ n : ℕ in atTop,
      mu.real {omega | M₀ < ‖Sn n omega‖} < 2 * alpha := by
    filter_upwards [hdataENN] with n hn'
    rw [Measure.real_def]
    have hfin : mu {omega | M₀ < ‖Sn n omega‖} ≠ ⊤ := measure_ne_top _ _
    have htop : ENNReal.ofReal (2 * alpha) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      (mu {omega | M₀ < ‖Sn n omega‖}).toReal <
          (ENNReal.ofReal (2 * alpha)).toReal :=
        (ENNReal.toReal_lt_toReal hfin htop).2 hn'
      _ = 2 * alpha := ENNReal.toReal_ofReal (by positivity)
  rcases scaledBootstrapMeanDifferenceVec_outer_tight S g hg hg2
      (epsilon / 4) (by positivity) (delta / 3) (by positivity) with
    ⟨Mₑ, hMₑ, hboot⟩
  let K : ℝ := max Mₑ (max M₀ 1)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right M₀ 1) (le_max_right Mₑ (max M₀ 1)))
  let eta : ℝ := epsilon / (4 * K)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hlocal : ∀ᶠ z in nhds m,
      ‖h z - h m - Dh (z - m)‖ ≤ eta * ‖z - m‖ := by
    simpa [m] using (smoothRemainder_isLittleO hderiv).def heta
  rcases Metric.eventually_nhds_iff.mp hlocal with ⟨rho, hrho, hrhoprop⟩
  let qNear : ℕ → Omega → ℝ := fun n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | rho / 2 < ‖finMean (fun i ↦ g (xstar i)) - m‖}
  have hqNear_meas (n : ℕ) : Measurable (qNear n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) :=
      {z | rho / 2 < ‖finMean (fun i ↦ g (z.2 i)) - m‖}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold finMean
      fun_prop
    have hsamp : Measurable (fun omega ↦ S.sampleVector n omega) := by
      apply measurable_pi_iff.mpr
      intro i
      exact S.meas i
    change Measurable ((fun x : Fin n → X ↦
      (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) ∘
        fun omega ↦ S.sampleVector n omega)
    exact (measurable_bootstrapResample_real_of_measurableSet A hA).comp hsamp
  have hqNear_ae : ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ qNear n omega) atTop (nhds 0) := by
    filter_upwards [bootstrapMeanVec_sub_populationMean_tendsto_zero_ae
      S g hg hg_int] with omega homega
    simpa [qNear, m] using homega (rho / 2) (by positivity)
  have hnearOuter : Tendsto
      (fun n ↦ mu.real {omega | epsilon / 4 < qNear n omega}) atTop (nhds 0) :=
    measureReal_gt_tendsto_zero_of_ae_tendsto hqNear_meas hqNear_ae
      (epsilon / 4) (by positivity)
  have hnear := hnearOuter.eventually (Iio_mem_nhds (show 0 < delta / 3 by positivity))
  have hsqrt : ∀ᶠ n : ℕ in atTop, 2 * K / rho < Real.sqrt (n : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  apply eventually_atTop.1
  filter_upwards [hdata, hboot, hnear, hsqrt, eventually_ne_atTop 0] with
      n hdata_n hboot_n hnear_n hsqrt_n hn
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  let badData : Set Omega := {omega | M₀ < ‖Sn n omega‖}
  let badNear : Set Omega := {omega | epsilon / 4 < qNear n omega}
  let badBoot : Set Omega := {omega |
    epsilon / 4 < (bootstrapResample (S.sampleVector n omega)).real
      {xstar | Mₑ < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖}}
  have houterSubset :
      {omega | epsilon < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < abs
          (centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n
              (S.sampleVector n omega) xstar -
            centeredBootstrapSum
              (fun x ↦ Dh (g x - ∫ y, g y ∂P))
              (S.sampleVector n omega) xstar)}} ⊆
        badData ∪ (badNear ∪ badBoot) := by
    intro omega homega
    by_contra hgood
    have hdata_good : ‖Sn n omega‖ ≤ M₀ :=
      le_of_not_gt (fun hh ↦ hgood (Or.inl hh))
    have hnear_good : qNear n omega ≤ epsilon / 4 :=
      le_of_not_gt (fun hh ↦ hgood (Or.inr (Or.inl hh)))
    have hboot_good :
        (bootstrapResample (S.sampleVector n omega)).real
          {xstar | Mₑ < ‖scaledBootstrapMeanDifference g n
            (S.sampleVector n omega) xstar‖} ≤ epsilon / 4 :=
      le_of_not_gt (fun hh ↦ hgood (Or.inr (Or.inr hh)))
    let data : Fin n → X := S.sampleVector n omega
    let bad : Set (Fin n → X) := {xstar | epsilon < abs
      (centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n data xstar -
        centeredBootstrapSum (fun x ↦ Dh (g x - ∫ y, g y ∂P)) data xstar)}
    let near : Set (Fin n → X) :=
      {xstar | rho / 2 < ‖finMean (fun i ↦ g (xstar i)) - m‖}
    let boot : Set (Fin n → X) :=
      {xstar | Mₑ < ‖scaledBootstrapMeanDifference g n data xstar‖}
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hKdata : ‖Sn n omega‖ ≤ K :=
      hdata_good.trans (le_trans (le_max_left M₀ 1)
        (le_max_right Mₑ (max M₀ 1)))
    have hTm : ‖finMean (fun i ↦ g (data i)) - m‖ < rho := by
      have hscale : Real.sqrt (n : ℝ) *
          ‖finMean (fun i ↦ g (data i)) - m‖ = ‖Sn n omega‖ := by
        dsimp [Sn, T, data]
        rw [← finMean_sampleVector_vec S g omega, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have hprod : Real.sqrt (n : ℝ) *
          ‖finMean (fun i ↦ g (data i)) - m‖ <
          Real.sqrt (n : ℝ) * rho := by
        rw [hscale]
        calc
          ‖Sn n omega‖ ≤ K := hKdata
          _ < Real.sqrt (n : ℝ) * rho := by
            calc
              K < 2 * K := by linarith
              _ = (2 * K / rho) * rho := by field_simp
              _ < Real.sqrt (n : ℝ) * rho :=
                mul_lt_mul_of_pos_right hsqrt_n hrho
      nlinarith
    have hbadSubset : bad ⊆ near ∪ boot := by
      intro xstar hxstar
      by_contra hxgood
      have hxnear : ‖finMean (fun i ↦ g (xstar i)) - m‖ ≤ rho / 2 :=
        le_of_not_gt (fun hh ↦ hxgood (Or.inl hh))
      have hxboot : ‖scaledBootstrapMeanDifference g n data xstar‖ ≤ Mₑ :=
        le_of_not_gt (fun hh ↦ hxgood (Or.inr hh))
      have hlocalStar := hrhoprop (by
        simpa [dist_eq_norm] using lt_of_le_of_lt hxnear (by linarith))
      have hlocalData := hrhoprop (by simpa [dist_eq_norm] using hTm)
      let starMean := finMean (fun i ↦ g (xstar i))
      let dataMean := finMean (fun i ↦ g (data i))
      have herror :
          centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n data xstar -
              centeredBootstrapSum (fun x ↦ Dh (g x - ∫ y, g y ∂P)) data xstar =
            Real.sqrt (n : ℝ) *
              ((h starMean - h m - Dh (starMean - m)) -
                (h dataMean - h m - Dh (dataMean - m))) := by
        rw [centeredBootstrapSum_eq_sqrt_mul_finAverage_sub hn]
        unfold centeredEstimatorBootstrapStatistic smoothMeanEstimator
        change _ = Real.sqrt (n : ℝ) *
          ((h starMean - h m - Dh (starMean - m)) -
            (h dataMean - h m - Dh (dataMean - m)))
        have hstar : finMean (fun i ↦ Dh (g (xstar i) - ∫ y, g y ∂P)) =
            Dh (starMean - m) := by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          unfold finMean starMean finMean
          simp only [Finset.sum_sub_distrib, map_sub, map_smul, map_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            smul_eq_mul]
          field_simp
          simp [m]
        have hdat : finMean (fun i ↦ Dh (g (data i) - ∫ y, g y ∂P)) =
            Dh (dataMean - m) := by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          unfold finMean dataMean finMean
          simp only [Finset.sum_sub_distrib, map_sub, map_smul, map_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            smul_eq_mul]
          field_simp
          simp [m]
        rw [hstar, hdat]
        ring
      have hscaledStar :
          Real.sqrt (n : ℝ) • (starMean - m) =
            scaledBootstrapMeanDifference g n data xstar + Sn n omega := by
        dsimp [scaledBootstrapMeanDifference, Sn, T, starMean, dataMean, data]
        rw [← finMean_sampleVector_vec S g omega]
        rw [← sub_add_sub_cancel starMean dataMean m, smul_add]
      have hstarScale : Real.sqrt (n : ℝ) * ‖starMean - m‖ ≤
          ‖scaledBootstrapMeanDifference g n data xstar‖ + ‖Sn n omega‖ := by
        calc
          Real.sqrt (n : ℝ) * ‖starMean - m‖ =
              ‖Real.sqrt (n : ℝ) • (starMean - m)‖ := by
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg (Real.sqrt_nonneg _)]
          _ = ‖scaledBootstrapMeanDifference g n data xstar + Sn n omega‖ := by
              rw [hscaledStar]
          _ ≤ _ := norm_add_le _ _
      have hdataScale : Real.sqrt (n : ℝ) * ‖dataMean - m‖ = ‖Sn n omega‖ := by
        dsimp [Sn, T, dataMean, data]
        rw [← finMean_sampleVector_vec S g omega, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have herrle : abs
          (centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n data xstar -
            centeredBootstrapSum (fun x ↦ Dh (g x - ∫ y, g y ∂P)) data xstar) ≤
          eta * (K + 2 * K) := by
        rw [herror, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc
          Real.sqrt (n : ℝ) * ‖
              (h starMean - h m - Dh (starMean - m)) -
                (h dataMean - h m - Dh (dataMean - m))‖ ≤
              Real.sqrt (n : ℝ) *
                (eta * ‖starMean - m‖ + eta * ‖dataMean - m‖) := by
                gcongr
                exact (norm_sub_le _ _).trans (add_le_add hlocalStar hlocalData)
          _ = eta * (Real.sqrt (n : ℝ) * ‖starMean - m‖ +
                Real.sqrt (n : ℝ) * ‖dataMean - m‖) := by ring
          _ ≤ eta * ((‖scaledBootstrapMeanDifference g n data xstar‖ +
                ‖Sn n omega‖) + ‖Sn n omega‖) := by
              apply mul_le_mul_of_nonneg_left _ heta.le
              exact add_le_add hstarScale hdataScale.le
          _ ≤ eta * (K + 2 * K) := by
              have hbK : ‖scaledBootstrapMeanDifference g n data xstar‖ ≤ K :=
                hxboot.trans (le_max_left Mₑ (max M₀ 1))
              apply mul_le_mul_of_nonneg_left _ heta.le
              linarith
      have herrlt : abs
          (centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n data xstar -
            centeredBootstrapSum (fun x ↦ Dh (g x - ∫ y, g y ∂P)) data xstar) <
          epsilon := by
        refine lt_of_le_of_lt herrle ?_
        dsimp [eta]
        field_simp
        nlinarith
      exact (not_lt_of_ge herrlt.le) hxstar
    let _ : IsProbabilityMeasure (bootstrapResample data) :=
      bootstrapResample_isProbabilityMeasure data hn
    have hcond : (bootstrapResample data).real bad ≤
        (bootstrapResample data).real near + (bootstrapResample data).real boot :=
      (measureReal_mono hbadSubset).trans (measureReal_union_le _ _)
    have hnear_good' : (bootstrapResample data).real near ≤ epsilon / 4 := by
      simpa [qNear, data, near] using hnear_good
    have hboot_good' : (bootstrapResample data).real boot ≤ epsilon / 4 := by
      simpa [data, boot] using hboot_good
    have hcond' : (bootstrapResample data).real bad ≤ epsilon / 2 := by
      apply hcond.trans
      linarith
    have homega' : epsilon < (bootstrapResample data).real bad := by
      simpa [data, bad] using homega
    exact (not_lt_of_ge (hcond'.trans (by linarith))) homega'
  calc
    mu.real {omega | epsilon < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | epsilon < abs
          (centeredEstimatorBootstrapStatistic (smoothMeanEstimator g h) n
              (S.sampleVector n omega) xstar -
            centeredBootstrapSum (fun x ↦ Dh (g x - ∫ y, g y ∂P))
              (S.sampleVector n omega) xstar)}} ≤
        mu.real (badData ∪ (badNear ∪ badBoot)) := measureReal_mono houterSubset
    _ ≤ mu.real badData + (mu.real badNear + mu.real badBoot) :=
      (measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_union_le _ _))
    _ < delta := by
      dsimp [badData, badNear, badBoot]
      dsimp [alpha] at hdata_n
      linarith

end

end Causalean.Stat
