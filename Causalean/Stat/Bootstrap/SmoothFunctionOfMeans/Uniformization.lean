module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Measurability
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Tightness

/-!
# Uniformizing almost-sure conditional probability bounds

This module isolates the measure-theoretic step that turns an almost-everywhere pointwise limit
of measurable conditional-probability majorants into convergence of their outer sampling tails.
It is the final generic bridge needed before constructing the smooth bootstrap remainder majorant.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- If [a sequence of measurable real functions](hyp:f,hf) [converges pointwise to zero almost
everywhere](hyp:hlim), then for [every positive threshold](hyp:epsilon,hepsilon) [the real measure
of its strict upper-tail event tends to zero](goal). -/
theorem measureReal_gt_tendsto_zero_of_ae_tendsto
    [IsFiniteMeasure mu] {f : ℕ → Omega → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ omega ∂mu, Tendsto (fun n ↦ f n omega) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun n ↦ mu.real {omega | epsilon < f n omega}) atTop (𝓝 0) := by
  have hmeasure : TendstoInMeasure mu f atTop (fun _ ↦ 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (hf n).aestronglyMeasurable) hlim
  have htail :
      Tendsto (fun n ↦ mu.real {omega | epsilon ≤ ‖f n omega - 0‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_norm.mp hmeasure) epsilon hepsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htail
  · exact Eventually.of_forall fun _ ↦ measureReal_nonneg
  · exact Eventually.of_forall fun n ↦ measureReal_mono fun omega homega ↦ by
      change epsilon ≤ ‖f n omega - 0‖
      simpa only [sub_zero, Real.norm_eq_abs] using
        homega.le.trans (le_abs_self (f n omega))

/-- **Outer uniformization of conditional bootstrap tightness.** For [an iid sample](hyp:S) and
a [measurable square-integrable finite-dimensional moment](hyp:g,hg,hg2), given [positive inner
and outer tail tolerances](hyp:epsilon,hepsilon,delta,hdelta), there is one deterministic positive
radius such that [the sampling probability of data sets whose conditional scaled-bootstrap-mean
tail exceeds the inner tolerance is eventually below the outer tolerance](goal). -/
theorem scaledBootstrapMeanDifferenceVec_outer_tight
    {X : Type*} [MeasurableSpace X] {P : Measure X}
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d))
    (hg : Measurable g) (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      mu.real {omega |
        epsilon < (bootstrapResample (S.sampleVector n omega)).real
          {xstar | M < ‖scaledBootstrapMeanDifference g n
            (S.sampleVector n omega) xstar‖}} < delta := by
  classical
  let _ : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  let q : ℕ → ℕ → Omega → ℝ := fun K n omega ↦
    (bootstrapResample (S.sampleVector n omega)).real
      {xstar | (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖}
  have hq_meas (K n : ℕ) : Measurable (q K n) := by
    let A : Set ((Fin n → X) × (Fin n → X)) :=
      {z | (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n z.1 z.2‖}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      unfold scaledBootstrapMeanDifference finMean
      fun_prop
    have hsamp : Measurable (fun omega ↦ S.sampleVector n omega) := by
      apply measurable_pi_iff.mpr
      intro i
      exact S.meas i
    change Measurable ((fun x : Fin n → X ↦
      (bootstrapResample x).real {xstar | (x, xstar) ∈ A}) ∘
        fun omega ↦ S.sampleVector n omega)
    exact (measurable_bootstrapResample_real_of_measurableSet A hA).comp hsamp
  let G : ℕ → Set Omega := fun K ↦
    {omega | ∀ n, K ≤ n → q K n omega < epsilon}
  have hG_meas (K : ℕ) : MeasurableSet (G K) := by
    have hrepr : G K = ⋂ n : ℕ, ⋂ (_h : K ≤ n),
        {omega | q K n omega < epsilon} := by
      ext omega
      simp only [G, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hrepr]
    exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_lt (hq_meas K n) measurable_const
  have hG_mono : Monotone G := by
    intro K L hKL omega homega
    change ∀ n, K ≤ n → q K n omega < epsilon at homega
    change ∀ n, L ≤ n → q L n omega < epsilon
    intro n hLn
    have htail := homega n (hKL.trans hLn)
    by_cases hEq : K = L
    · simpa [hEq] using htail
    · have hKLlt : K < L := lt_of_le_of_ne hKL hEq
      have hn : n ≠ 0 := by omega
      let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
        bootstrapResample_isProbabilityMeasure _ hn
      apply (measureReal_mono ?_).trans_lt htail
      intro xstar hxstar
      change (L + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖ at hxstar
      change (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖
      have hcast : (K + 1 : ℝ) < (L + 1 : ℝ) := by
        exact_mod_cast Nat.add_lt_add_right hKLlt 1
      exact hcast.trans hxstar
  have hbounded :=
    scaledBootstrapMeanDifferenceVec_conditionallyBounded S g hg hg2
  unfold ConditionallyBoundedInProbability at hbounded
  have heventually_G : ∀ᵐ omega ∂mu, ∀ᶠ K : ℕ in atTop, omega ∈ G K := by
    filter_upwards [hbounded] with omega homega
    rcases homega epsilon hepsilon with ⟨R, hR, htail⟩
    rcases eventually_atTop.1 htail with ⟨N, hN⟩
    obtain ⟨K₀ : ℕ, hK₀⟩ := exists_nat_gt R
    have hK₀pos : 0 < K₀ := by
      by_contra h
      have : K₀ = 0 := Nat.eq_zero_of_not_pos h
      subst K₀
      norm_num at hK₀
      linarith
    let K := max N K₀
    have homegaK : omega ∈ G K := by
      change ∀ n, K ≤ n → q K n omega < epsilon
      intro n hKn
      have hNn : N ≤ n := (Nat.le_max_left N K₀).trans hKn
      have hK₀K : K₀ ≤ K := Nat.le_max_right N K₀
      have hn : n ≠ 0 := by omega
      let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
        bootstrapResample_isProbabilityMeasure _ hn
      apply (measureReal_mono ?_).trans_lt (hN n hNn)
      intro xstar hxstar
      change (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖ at hxstar
      change R < ‖scaledBootstrapMeanDifference g n
        (S.sampleVector n omega) xstar‖
      apply (show R < (K + 1 : ℝ) by
        calc
          R < (K₀ : ℝ) := hK₀
          _ ≤ (K : ℝ) := by exact_mod_cast hK₀K
          _ < (K + 1 : ℝ) := by norm_num).trans hxstar
    filter_upwards [eventually_ge_atTop K] with L hKL
    exact hG_mono hKL homegaK
  let f : ℕ → Omega → ℝ := fun K omega ↦ if omega ∈ G K then 0 else 1
  have hf_meas (K : ℕ) : Measurable (f K) := by
    exact Measurable.ite (hG_meas K) measurable_const measurable_const
  have hf_zero : ∀ᵐ omega ∂mu,
      Tendsto (fun K ↦ f K omega) atTop (𝓝 0) := by
    filter_upwards [heventually_G] with omega homega
    have heq : ∀ᶠ K : ℕ in atTop, f K omega = 0 := by
      filter_upwards [homega] with K hK
      simp [f, hK]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hcompl_tendsto := measureReal_gt_tendsto_zero_of_ae_tendsto
    hf_meas hf_zero (1 / 2 : ℝ) (by norm_num)
  have hsmall : ∀ᶠ K : ℕ in atTop,
      mu.real {omega | (1 / 2 : ℝ) < f K omega} < delta :=
    hcompl_tendsto.eventually (Iio_mem_nhds hdelta)
  rcases eventually_atTop.1 hsmall with ⟨K, hK⟩
  refine ⟨K + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop K] with n hKn
  have hbad : {omega |
      epsilon < (bootstrapResample (S.sampleVector n omega)).real
        {xstar | (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
          (S.sampleVector n omega) xstar‖}} ⊆ (G K)ᶜ := by
    intro omega homega hgood
    exact (not_lt_of_ge homega.le) (hgood n hKn)
  calc
    mu.real {omega |
        epsilon < (bootstrapResample (S.sampleVector n omega)).real
          {xstar | (K + 1 : ℝ) < ‖scaledBootstrapMeanDifference g n
            (S.sampleVector n omega) xstar‖}} ≤
        mu.real (G K)ᶜ := measureReal_mono hbad
    _ = mu.real {omega | (1 / 2 : ℝ) < f K omega} := by
      congr 1
      ext omega
      by_cases homega : omega ∈ G K
      · simp [f, homega]
      · simp [f, homega]
        norm_num
    _ < delta := hK K le_rfl

end

end Causalean.Stat
