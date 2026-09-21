module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Basic
public import Causalean.Stat.Bootstrap.EfronResampling.Moments
public import Mathlib.Probability.StrongLaw

/-!
# Conditional bootstrap weak laws for sample means

This module proves scalar conditional bootstrap weak laws under a first moment, centered either
at the data mean or at the population mean.  The finite-dimensional coordinate reduction is kept
in the downstream `WeakLawVector` module.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  {mu : Measure Omega} {P : Measure X}

private theorem bootstrapResample_map
    {n : ℕ} (x : Fin n → X) (g : X → ℝ) (hg : Measurable g) (hn : n ≠ 0) :
    (bootstrapResample x).map (fun y i ↦ g (y i)) =
      bootstrapResample (fun i ↦ g (x i)) := by
  have hemp :
      empiricalMeasure (fun i : Fin n ↦ g (x i)) =
        (empiricalMeasure x).map g := by
    unfold empiricalMeasure Concentration.finiteSampleMeasure
    rw [Measure.map_smul, Measure.map_finset_sum hg.aemeasurable]
    simp_rw [Measure.map_dirac' hg]
  let _ : IsProbabilityMeasure (empiricalMeasure x) :=
    empiricalMeasure_isProbabilityMeasure x hn
  unfold bootstrapResample
  rw [hemp, ← Measure.pi_map_pi (fun _ ↦ hg.aemeasurable)]

private theorem integrable_bootstrapResample
    {n : ℕ} (x : Fin n → X) (f : (Fin n → X) → ℝ) (hf : Measurable f) :
    Integrable f (bootstrapResample x) := by
  rw [bootstrapResample_eq_average_dirac]
  apply Integrable.smul_measure
  · rw [integrable_finsetSum_measure]
    intro j hj
    exact integrable_dirac' hf.stronglyMeasurable (by simp)
  · simp

private theorem integral_comp_finMean_bootstrapResample
    {n : ℕ} (x : Fin n → X) (g : X → ℝ) (hg : Measurable g) (hn : n ≠ 0) :
    ∫ y, finMean (fun i ↦ g (y i)) ∂bootstrapResample x =
      finMean (fun i ↦ g (x i)) := by
  let G : (Fin n → X) → (Fin n → ℝ) := fun y i ↦ g (y i)
  have hG : Measurable G := by fun_prop
  have hfm : Measurable (finMean : (Fin n → ℝ) → ℝ) := by
    unfold finMean
    fun_prop
  rw [← integral_map hG.aemeasurable hfm.aestronglyMeasurable,
    bootstrapResample_map x g hg hn]
  simpa [G, finMean, smul_eq_mul] using
    integral_finMean_bootstrapResample (fun i ↦ g (x i)) hn

private theorem integral_centered_comp_finMean_sq_bootstrapResample
    {n : ℕ} (x : Fin n → X) (g : X → ℝ) (hg : Measurable g) (hn : n ≠ 0) :
    ∫ y, (Real.sqrt n *
        (finMean (fun i ↦ g (y i)) - finMean (fun i ↦ g (x i)))) ^ 2
        ∂bootstrapResample x =
      (n : ℝ)⁻¹ * ∑ i, (g (x i) - finMean (fun i ↦ g (x i))) ^ 2 := by
  let G : (Fin n → X) → (Fin n → ℝ) := fun y i ↦ g (y i)
  have hG : Measurable G := by fun_prop
  let F : (Fin n → ℝ) → ℝ := fun y ↦
    (Real.sqrt n * (finMean y - finMean (fun i ↦ g (x i)))) ^ 2
  have hF : Measurable F := by
    dsimp [F]
    unfold finMean
    fun_prop
  rw [← integral_map hG.aemeasurable hF.aestronglyMeasurable,
    bootstrapResample_map x g hg hn]
  simpa [F, G, finMean, smul_eq_mul] using
    integral_centered_finMean_sq_bootstrapResample
      (fun i ↦ g (x i)) hn

private theorem centered_finMean_sq_le
    {n : ℕ} (x : Fin n → ℝ) (hn : n ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (hx : ∀ i, |x i| ≤ K) :
    (n : ℝ)⁻¹ * ∑ i, (x i - finMean x) ^ 2 ≤ 4 * K ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm : |finMean x| ≤ K := by
    unfold finMean
    rw [smul_eq_mul, abs_mul, abs_inv,
      abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      (n : ℝ)⁻¹ * |∑ i, x i| ≤ (n : ℝ)⁻¹ * ∑ i, |x i| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, K := by
        gcongr with i
        exact hx i
      _ = K := by simp [hn]
  calc
    (n : ℝ)⁻¹ * ∑ i, (x i - finMean x) ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (2 * K) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro i hi
          have habs : |x i - finMean x| ≤ 2 * K := by
            calc
              |x i - finMean x| ≤ |x i| + |finMean x| := abs_sub _ _
              _ ≤ K + K := add_le_add (hx i) hm
              _ = 2 * K := by ring
          have hs := (sq_le_sq₀ (abs_nonneg (x i - finMean x))
            (by positivity : 0 ≤ 2 * K)).2 habs
          simpa [sq_abs] using hs
    _ = 4 * K ^ 2 := by
      simp [hn]
      ring

private theorem bootstrapMean_bounded_le
    {n : ℕ} (x : Fin n → X) (g : X → ℝ) (hg : Measurable g)
    (hn : n ≠ 0) (K : ℝ) (hK : 0 ≤ K) (hgK : ∀ z, |g z| ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (bootstrapResample x).real
        {y | epsilon < |finMean (fun i ↦ g (y i)) -
          finMean (fun i ↦ g (x i))|} ≤
      4 * K ^ 2 / ((n : ℝ) * epsilon ^ 2) := by
  let D : (Fin n → X) → ℝ := fun y ↦
    finMean (fun i ↦ g (y i)) - finMean (fun i ↦ g (x i))
  let F : (Fin n → X) → ℝ := fun y ↦ (Real.sqrt n * D y) ^ 2
  have hD : Measurable D := by
    dsimp [D]
    unfold finMean
    fun_prop
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  let T : ℝ := (Real.sqrt n * epsilon) ^ 2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let _ : IsProbabilityMeasure (bootstrapResample x) :=
    bootstrapResample_isProbabilityMeasure x hn
  have hsubset : {y | epsilon < |D y|} ⊆ {y | T ≤ F y} := by
    intro y hy
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hmul : Real.sqrt n * epsilon < |Real.sqrt n * D y| := by
      calc
        Real.sqrt n * epsilon < Real.sqrt n * |D y| :=
          mul_lt_mul_of_pos_left hy hsqrt
        _ = |Real.sqrt n * D y| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) hepsilon.le)
      (abs_nonneg (Real.sqrt n * D y))).2 hmul.le
    simpa only [T, F, Set.mem_ofPred_eq, sq_abs] using hs
  have hmono := measureReal_mono (μ := bootstrapResample x) hsubset
    (measure_ne_top (bootstrapResample x) _)
  have hmarkov :
      T * (bootstrapResample x).real {y | T ≤ F y} ≤
        ∫ y, F y ∂bootstrapResample x := by
    apply mul_meas_ge_le_integral_of_nonneg
    · exact Eventually.of_forall (fun y ↦ sq_nonneg _)
    · exact integrable_bootstrapResample x F hF
  have hintegral : ∫ y, F y ∂bootstrapResample x ≤ 4 * K ^ 2 := by
    change (∫ y, (Real.sqrt n *
      (finMean (fun i ↦ g (y i)) - finMean (fun i ↦ g (x i)))) ^ 2
      ∂bootstrapResample x) ≤ _
    rw [integral_centered_comp_finMean_sq_bootstrapResample x g hg hn]
    exact centered_finMean_sq_le (fun i ↦ g (x i)) hn K hK (fun i ↦ hgK _)
  calc
    (bootstrapResample x).real
        {y | epsilon < |finMean (fun i ↦ g (y i)) -
          finMean (fun i ↦ g (x i))|} =
        (bootstrapResample x).real {y | epsilon < |D y|} := rfl
    _ ≤ (bootstrapResample x).real {y | T ≤ F y} := hmono
    _ ≤ 4 * K ^ 2 / T := (le_div_iff₀ hT).2 (by
      simpa [mul_comm] using hmarkov.trans hintegral)
    _ = 4 * K ^ 2 / ((n : ℝ) * epsilon ^ 2) := by
      congr 1
      dsimp [T]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

private theorem abs_finMean_le_finMean
    {n : ℕ} (x : Fin n → X) (q r : X → ℝ)
    (hqr : ∀ z, |q z| ≤ r z) :
    |finMean (fun i ↦ q (x i))| ≤ finMean (fun i ↦ r (x i)) := by
  unfold finMean
  rw [smul_eq_mul, smul_eq_mul, abs_mul, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg n)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |∑ i, q (x i)| ≤ ∑ i, |q (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, r (x i) := Finset.sum_le_sum fun i hi ↦ hqr _

private theorem bootstrapMean_enveloped_le
    {n : ℕ} (x : Fin n → X) (q r : X → ℝ)
    (hr : Measurable r) (hrnonneg : ∀ z, 0 ≤ r z)
    (hqr : ∀ z, |q z| ≤ r z) (hn : n ≠ 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hdata : finMean (fun i ↦ r (x i)) ≤ epsilon / 4) :
    (bootstrapResample x).real
        {y | epsilon / 2 < |finMean (fun i ↦ q (y i)) -
          finMean (fun i ↦ q (x i))|} ≤
      4 / epsilon * finMean (fun i ↦ r (x i)) := by
  let R : (Fin n → X) → ℝ := fun y ↦ finMean (fun i ↦ r (y i))
  have hR : Measurable R := by
    dsimp [R]
    unfold finMean
    fun_prop
  have hRnonneg : ∀ y, 0 ≤ R y := by
    intro y
    dsimp [R, finMean]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i hi ↦ hrnonneg _)
  change R x ≤ epsilon / 4 at hdata
  have hsubset :
      {y | epsilon / 2 < |finMean (fun i ↦ q (y i)) -
        finMean (fun i ↦ q (x i))|} ⊆
        {y | epsilon / 4 ≤ R y} := by
    intro y hy
    change epsilon / 2 < |finMean (fun i ↦ q (y i)) -
      finMean (fun i ↦ q (x i))| at hy
    have htri :
        |finMean (fun i ↦ q (y i)) - finMean (fun i ↦ q (x i))| ≤
          R y + R x := by
      calc
        |finMean (fun i ↦ q (y i)) - finMean (fun i ↦ q (x i))| ≤
            |finMean (fun i ↦ q (y i))| +
              |finMean (fun i ↦ q (x i))| := abs_sub _ _
        _ ≤ R y + R x := add_le_add
          (abs_finMean_le_finMean y q r hqr)
          (abs_finMean_le_finMean x q r hqr)
    by_contra hnot
    change ¬ epsilon / 4 ≤ R y at hnot
    have hylt : R y < epsilon / 4 := lt_of_not_ge hnot
    linarith
  let _ : IsProbabilityMeasure (bootstrapResample x) :=
    bootstrapResample_isProbabilityMeasure x hn
  have hmono := measureReal_mono (μ := bootstrapResample x) hsubset
    (measure_ne_top (bootstrapResample x) _)
  have hmarkov :
      (epsilon / 4) * (bootstrapResample x).real {y | epsilon / 4 ≤ R y} ≤
        ∫ y, R y ∂bootstrapResample x := by
    apply mul_meas_ge_le_integral_of_nonneg
    · exact Eventually.of_forall hRnonneg
    · exact integrable_bootstrapResample x R hR
  have hint : (∫ y, R y ∂bootstrapResample x) = R x :=
    integral_comp_finMean_bootstrapResample x r hr hn
  calc
    (bootstrapResample x).real
        {y | epsilon / 2 < |finMean (fun i ↦ q (y i)) -
          finMean (fun i ↦ q (x i))|} ≤
        (bootstrapResample x).real {y | epsilon / 4 ≤ R y} := hmono
    _ ≤ 4 / epsilon * R x := by
      rw [hint] at hmarkov
      have ht : 0 < epsilon / 4 := by positivity
      have hp :
          (bootstrapResample x).real {y | epsilon / 4 ≤ R y} *
              (epsilon / 4) ≤ R x := by
        simpa [mul_comm] using hmarkov
      have hdiv := (le_div_iff₀ ht).2 hp
      calc
        (bootstrapResample x).real {y | epsilon / 4 ≤ R y} ≤
            R x / (epsilon / 4) := hdiv
        _ = 4 / epsilon * R x := by field_simp
    _ = 4 / epsilon * finMean (fun i ↦ r (x i)) := rfl

private theorem tailIntegral_tendsto_zero
    (g : X → ℝ) (hg : Measurable g) (hg_int : Integrable g P) :
    Tendsto (fun A : ℝ ↦ ∫ x, |g x - truncation g A x| ∂P)
      atTop (𝓝 0) := by
  have hmeas : ∀ A : ℝ, AEStronglyMeasurable
      (fun x ↦ |g x - truncation g A x|) P := by
    intro A
    exact (hg.aestronglyMeasurable.sub
      hg.aestronglyMeasurable.truncation).norm
  have hbound : ∀ A : ℝ, ∀ᵐ x ∂P,
      ‖|g x - truncation g A x|‖ ≤ 2 * |g x| := by
    intro A
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |g x - truncation g A x| ≤ |g x| + |truncation g A x| := abs_sub _ _
      _ ≤ |g x| + |g x| :=
        add_le_add_right (abs_truncation_le_abs_self g A x) _
      _ = 2 * |g x| := by ring
  have hpoint : ∀ᵐ x ∂P,
      Tendsto (fun A : ℝ ↦ |g x - truncation g A x|) atTop (𝓝 0) := by
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop |g x|] with A hA
    rw [truncation_eq_self hA, sub_self, abs_zero]
  simpa using
    (tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ 2 * |g x|) (Eventually.of_forall hmeas)
      (Eventually.of_forall hbound) (hg_int.norm.const_mul 2) hpoint)

private theorem finMean_add_tail
    {n : ℕ} (x : Fin n → X) (g t : X → ℝ) :
    finMean (fun i ↦ g (x i)) =
      finMean (fun i ↦ t (x i)) +
        finMean (fun i ↦ (g - t) (x i)) := by
  unfold finMean
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, smul_eq_mul]
  ring

private theorem finMean_sampleVector
    (S : IIDSample Omega X mu P) (g : X → ℝ) (n : ℕ) (omega : Omega) :
    finMean (fun i ↦ g (S.sampleVector n omega i)) =
      S.sampleMean g n omega := by
  unfold finMean IIDSample.sampleVector IIDSample.sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ g (S.Z i omega)) n]
  rw [smul_eq_mul]

/-- For [an iid sample](hyp:S) and [a measurable integrable real statistic](hyp:g,hg,hg_int),
[the sample mean converges almost surely to its population mean](goal). -/
theorem sampleMean_integrable_tendsto_ae
    (S : IIDSample Omega X mu P) (g : X → ℝ)
    (hg : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ S.sampleMean g n omega) atTop (𝓝 (∫ x, g x ∂P)) := by
  haveI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hg_int_sample : Integrable (fun omega ↦ g (S.Z 0 omega)) mu := by
    have hmap : Integrable g (mu.map (S.Z 0)) := by
      simpa [S.law] using hg_int
    exact hmap.comp_measurable (S.meas 0)
  have hindep : Pairwise (Function.onFun (fun f₁ f₂ ↦ IndepFun f₁ f₂ mu)
      (fun i omega ↦ g (S.Z i omega))) := by
    have hi : iIndepFun (fun i ↦ g ∘ S.Z i) mu :=
      S.indep.comp (fun _ ↦ g) (fun _ ↦ hg)
    intro i j hij
    exact hi.indepFun hij
  have hident : ∀ i, IdentDistrib (fun omega ↦ g (S.Z i omega))
      (fun omega ↦ g (S.Z 0 omega)) mu mu := by
    intro i
    exact ((S.identDist i).symm.comp hg)
  have hslln := strong_law_ae_real
    (fun i omega ↦ g (S.Z i omega)) hg_int_sample hindep hident
  have hint : (∫ omega, g (S.Z 0 omega) ∂mu) = ∫ x, g x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hg.aestronglyMeasurable, S.law]
  filter_upwards [hslln] with omega homega
  unfold IIDSample.sampleMean
  simpa [hint, div_eq_mul_inv, mul_comm] using homega

/-- **Conditional bootstrap weak law.** For [an iid sample](hyp:S) and [a measurable integrable
real statistic](hyp:g,hg,hg_int), for almost every data sequence and every positive tolerance,
[the conditional probability that the resample mean differs from the data mean tends to
zero](goal). -/
theorem bootstrapMean_sub_dataMean_tendsto_zero_ae
    (S : IIDSample Omega X mu P) (g : X → ℝ)
    (hg : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ omega ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            |finMean (fun i ↦ g (xstar i)) -
              finMean (fun i ↦ g (S.sampleVector n omega i))|})
        atTop (𝓝 0) := by
  have htails : ∀ᵐ omega ∂mu, ∀ M : ℕ,
      Tendsto
        (fun n ↦ S.sampleMean
          (fun x ↦ |g x - truncation g (M : ℝ) x|) n omega)
        atTop
        (nhds (∫ x, |g x - truncation g (M : ℝ) x| ∂P)) := by
    rw [ae_all_iff]
    intro M
    let r : X → ℝ := fun x ↦ |g x - truncation g (M : ℝ) x|
    have hr : Measurable r := by
      dsimp [r]
      unfold truncation
      exact (hg.sub
        ((measurable_id.indicator measurableSet_Ioc).comp hg)).abs
    have hrint : Integrable r P := by
      refine Integrable.mono (hg_int.norm.const_mul 2)
        hr.aestronglyMeasurable ?_
      filter_upwards with x
      dsimp [r]
      rw [abs_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * |g x|)]
      calc
        |g x - truncation g (M : ℝ) x| ≤
            |g x| + |truncation g (M : ℝ) x| := abs_sub _ _
        _ ≤ |g x| + |g x| :=
          add_le_add_right (abs_truncation_le_abs_self g (M : ℝ) x) _
        _ = 2 * |g x| := by ring
    simpa [r] using sampleMean_integrable_tendsto_ae S r hr hrint
  filter_upwards [htails] with omega homega
  intro epsilon hepsilon
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact ha.trans_le measureReal_nonneg
  · intro delta hdelta
    let c : ℝ := min (delta * epsilon / 16) (epsilon / 4)
    have hc : 0 < c := by
      dsimp [c]
      exact lt_min (by positivity) (by positivity)
    have htailNat : Tendsto
        (fun M : ℕ ↦ ∫ x, |g x - truncation g (M : ℝ) x| ∂P)
        atTop (nhds 0) := by
      exact (tailIntegral_tendsto_zero g hg hg_int).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hsmall : ∀ᶠ M : ℕ in atTop,
        ∫ x, |g x - truncation g (M : ℝ) x| ∂P < c / 2 :=
      htailNat.eventually (eventually_lt_nhds (by positivity))
    rcases eventually_atTop.1 hsmall with ⟨M, hM⟩
    have hpop : ∫ x, |g x - truncation g (M : ℝ) x| ∂P < c :=
      (hM M le_rfl).trans (by linarith [hc])
    have hsample : ∀ᶠ n : ℕ in atTop,
        S.sampleMean (fun x ↦ |g x - truncation g (M : ℝ) x|)
          n omega < c :=
      (homega M).eventually (eventually_lt_nhds hpop)
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) * (epsilon / 2) ^ 2)
        atTop atTop := by
      simpa [mul_comm] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
          (sq_pos_of_pos (by positivity : 0 < epsilon / 2))
    have hrate : Tendsto
        (fun n : ℕ ↦ 4 * |(M : ℝ)| ^ 2 /
          ((n : ℝ) * (epsilon / 2) ^ 2)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    have hrateSmall : ∀ᶠ n : ℕ in atTop,
        4 * |(M : ℝ)| ^ 2 / ((n : ℝ) * (epsilon / 2) ^ 2) <
          3 * delta / 4 :=
      hrate.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hsample, hrateSmall, eventually_ne_atTop 0]
      with n hsample_n hrate_n hn
    let t : X → ℝ := truncation g (M : ℝ)
    let q : X → ℝ := g - t
    let r : X → ℝ := fun x ↦ |q x|
    let data : Fin n → X := S.sampleVector n omega
    have ht : Measurable t := by
      dsimp [t]
      unfold truncation
      exact (measurable_id.indicator measurableSet_Ioc).comp hg
    have hr : Measurable r := by
      dsimp [r, q]
      exact (hg.sub ht).abs
    have hrnonneg : ∀ x, 0 ≤ r x := fun x ↦ abs_nonneg _
    have hdata : finMean (fun i ↦ r (data i)) ≤ epsilon / 4 := by
      rw [show finMean (fun i ↦ r (data i)) =
        S.sampleMean r n omega by exact finMean_sampleVector S r n omega]
      have hc_le : c ≤ epsilon / 4 := min_le_right _ _
      exact (le_of_lt (by simpa [r, q, t, data] using hsample_n)).trans hc_le
    have hset :
        {xstar : Fin n → X | epsilon <
          |finMean (fun i ↦ g (xstar i)) - finMean (fun i ↦ g (data i))|} ⊆
        {xstar : Fin n → X | epsilon / 2 <
          |finMean (fun i ↦ t (xstar i)) - finMean (fun i ↦ t (data i))|} ∪
        {xstar : Fin n → X | epsilon / 2 <
          |finMean (fun i ↦ q (xstar i)) - finMean (fun i ↦ q (data i))|} := by
      intro xstar hxstar
      change epsilon <
        |finMean (fun i ↦ g (xstar i)) - finMean (fun i ↦ g (data i))| at hxstar
      rw [finMean_add_tail xstar g t, finMean_add_tail data g t] at hxstar
      change _ ∨ _
      by_contra hnot
      simp only [Set.mem_setOf_eq] at hnot
      push_neg at hnot
      have htri := abs_add_le
        (finMean (fun i ↦ t (xstar i)) - finMean (fun i ↦ t (data i)))
        (finMean (fun i ↦ q (xstar i)) - finMean (fun i ↦ q (data i)))
      rw [show
        finMean (fun i ↦ t (xstar i)) + finMean (fun i ↦ q (xstar i)) -
            (finMean (fun i ↦ t (data i)) + finMean (fun i ↦ q (data i))) =
          (finMean (fun i ↦ t (xstar i)) - finMean (fun i ↦ t (data i))) +
            (finMean (fun i ↦ q (xstar i)) - finMean (fun i ↦ q (data i))) by ring]
        at hxstar
      linarith
    let _ : IsProbabilityMeasure (bootstrapResample data) :=
      bootstrapResample_isProbabilityMeasure data hn
    have hmono := measureReal_mono (μ := bootstrapResample data) hset
      (measure_ne_top (bootstrapResample data) _)
    have hunion := measureReal_union_le
      (μ := bootstrapResample data)
      {xstar : Fin n → X | epsilon / 2 <
        |finMean (fun i ↦ t (xstar i)) - finMean (fun i ↦ t (data i))|}
      {xstar : Fin n → X | epsilon / 2 <
        |finMean (fun i ↦ q (xstar i)) - finMean (fun i ↦ q (data i))|}
    have hbounded := bootstrapMean_bounded_le data t ht hn |(M : ℝ)|
      (abs_nonneg _) (fun x ↦ abs_truncation_le_bound g (M : ℝ) x)
      (epsilon / 2) (by positivity)
    have htail := bootstrapMean_enveloped_le data q r hr hrnonneg
      (fun x ↦ le_rfl) hn epsilon hepsilon hdata
    have hsample_fin : finMean (fun i ↦ r (data i)) < c := by
      rw [show finMean (fun i ↦ r (data i)) =
        S.sampleMean r n omega by exact finMean_sampleVector S r n omega]
      simpa [r, q, t, data] using hsample_n
    have htailSmall : 4 / epsilon * finMean (fun i ↦ r (data i)) <
        delta / 4 := by
      have hc_le : c ≤ delta * epsilon / 16 := min_le_left _ _
      have hrs : finMean (fun i ↦ r (data i)) < delta * epsilon / 16 :=
        hsample_fin.trans_le hc_le
      have heinv : 0 < 4 / epsilon := by positivity
      calc
        4 / epsilon * finMean (fun i ↦ r (data i)) <
            4 / epsilon * (delta * epsilon / 16) :=
          mul_lt_mul_of_pos_left hrs heinv
        _ = delta / 4 := by field_simp; norm_num
    calc
      (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            |finMean (fun i ↦ g (xstar i)) -
              finMean (fun i ↦ g (S.sampleVector n omega i))|} =
          (bootstrapResample data).real
            {xstar | epsilon <
              |finMean (fun i ↦ g (xstar i)) -
                finMean (fun i ↦ g (data i))|} := rfl
      _ ≤ (bootstrapResample data).real
            {xstar | epsilon / 2 <
              |finMean (fun i ↦ t (xstar i)) - finMean (fun i ↦ t (data i))|} +
          (bootstrapResample data).real
            {xstar | epsilon / 2 <
              |finMean (fun i ↦ q (xstar i)) - finMean (fun i ↦ q (data i))|} :=
        hmono.trans hunion
      _ ≤ 4 * |(M : ℝ)| ^ 2 / ((n : ℝ) * (epsilon / 2) ^ 2) +
          4 / epsilon * finMean (fun i ↦ r (data i)) := add_le_add hbounded htail
      _ < delta := by linarith

/-- For [an iid sample](hyp:S) and [a measurable integrable real statistic](hyp:g,hg,hg_int),
for almost every data sequence and every positive tolerance, [the conditional probability that
the bootstrap mean differs from the population mean tends to zero](goal). -/
theorem bootstrapMean_sub_populationMean_tendsto_zero_ae
    (S : IIDSample Omega X mu P) (g : X → ℝ)
    (hg : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ omega ∂mu, ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n ↦ (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon <
            |finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P|})
        atTop (𝓝 0) := by
  filter_upwards [bootstrapMean_sub_dataMean_tendsto_zero_ae S g hg hg_int,
    sampleMean_integrable_tendsto_ae S g hg hg_int] with omega hboot hmean
  intro epsilon hepsilon
  have hbootHalf := hboot (epsilon / 2) (by positivity)
  have hmeanHalf : ∀ᶠ n : ℕ in atTop,
      |S.sampleMean g n omega - ∫ x, g x ∂P| < epsilon / 2 := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_atTop.1 hmean (epsilon / 2) (by positivity))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact ha.trans_le measureReal_nonneg
  · intro delta hdelta
    have hbootSmall : ∀ᶠ n : ℕ in atTop,
        (bootstrapResample (S.sampleVector n omega)).real
          {xstar | epsilon / 2 <
            |finMean (fun i ↦ g (xstar i)) -
              finMean (fun i ↦ g (S.sampleVector n omega i))|} < delta :=
      hbootHalf.eventually (eventually_lt_nhds hdelta)
    filter_upwards [hmeanHalf, hbootSmall, eventually_ne_atTop 0]
      with n hmean_n hboot_n hn
    let _ : IsProbabilityMeasure (bootstrapResample (S.sampleVector n omega)) :=
      bootstrapResample_isProbabilityMeasure _ hn
    have hset :
        {xstar : Fin n → X | epsilon <
          |finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P|} ⊆
        {xstar : Fin n → X | epsilon / 2 <
          |finMean (fun i ↦ g (xstar i)) -
            finMean (fun i ↦ g (S.sampleVector n omega i))|} := by
      intro xstar hxstar
      change epsilon < |finMean (fun i ↦ g (xstar i)) - ∫ x, g x ∂P| at hxstar
      rw [finMean_sampleVector S g n omega]
      by_contra hnot
      change ¬ epsilon / 2 <
        |finMean (fun i ↦ g (xstar i)) - S.sampleMean g n omega| at hnot
      have htri := abs_sub_le
        (finMean (fun i ↦ g (xstar i))) (S.sampleMean g n omega)
        (∫ x, g x ∂P)
      linarith [le_of_not_gt hnot]
    exact (measureReal_mono (μ := bootstrapResample (S.sampleVector n omega))
      hset (measure_ne_top _ _)).trans_lt hboot_n

end

end Causalean.Stat
