module

public import Causalean.Stat.Bootstrap.EfronResampling.Mean.AlmostSure
public import Causalean.Stat.Bootstrap.EfronResampling.Moments
public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.WeakLawVector
public import Causalean.Stat.Concentration.Chebyshev

/-!
# Conditional bootstrap tightness for sample means

This module gives the exact finite-sample Chebyshev bound for the centered bootstrap mean and
deduces almost-sure conditional tightness.  Coordinate bounds and a norm-tightness theorem cover
finite-dimensional moment vectors.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Topology

noncomputable section

variable {Omega X E : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mu : Measure Omega} {P : Measure X}

/-- Given [a moment function](hyp:g), [a sample size](hyp:n), [observed data](hyp:x), and
[resampled data](hyp:xstar), the [scaled centered bootstrap mean](goal) is the square-root-size
multiple of the difference between the resample and data means. -/
def scaledBootstrapMeanDifference (g : X → E) (n : ℕ)
    (x xstar : Fin n → X) : E :=
  Real.sqrt (n : ℝ) •
    (finMean (fun i ↦ g (xstar i)) - finMean (fun i ↦ g (x i)))

private theorem bootstrapResample_map_real
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

private theorem integrable_bootstrapResample_real
    {n : ℕ} (x : Fin n → X) (f : (Fin n → X) → ℝ) (hf : Measurable f) :
    Integrable f (bootstrapResample x) := by
  rw [bootstrapResample_eq_average_dirac]
  apply Integrable.smul_measure
  · rw [integrable_finsetSum_measure]
    intro j hj
    exact integrable_dirac' hf.stronglyMeasurable (by simp)
  · simp

private theorem integral_finMean_bootstrapResample_real
    {n : ℕ} (x : Fin n → X) (g : X → ℝ) (hg : Measurable g) (hn : n ≠ 0) :
    ∫ y, finMean (fun i ↦ g (y i)) ∂bootstrapResample x =
      finMean (fun i ↦ g (x i)) := by
  let G : (Fin n → X) → (Fin n → ℝ) := fun y i ↦ g (y i)
  have hG : Measurable G := by fun_prop
  have hfm : Measurable (finMean : (Fin n → ℝ) → ℝ) := by
    unfold finMean
    fun_prop
  rw [← integral_map hG.aemeasurable hfm.aestronglyMeasurable,
    bootstrapResample_map_real x g hg hn]
  simpa [G, finMean, smul_eq_mul] using
    integral_finMean_bootstrapResample (fun i ↦ g (x i)) hn

private theorem integral_centered_finMean_sq_bootstrapResample_real
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
    bootstrapResample_map_real x g hg hn]
  simpa [F, G, finMean, smul_eq_mul] using
    integral_centered_finMean_sq_bootstrapResample
      (fun i ↦ g (x i)) hn

private theorem centered_finMean_sq_eq
    {n : ℕ} (a : Fin n → ℝ) (hn : n ≠ 0) :
    (n : ℝ)⁻¹ * ∑ i, (a i - finMean a) ^ 2 =
      finMean (fun i ↦ (a i) ^ 2) - (finMean a) ^ 2 := by
  unfold finMean
  simp only [smul_eq_mul]
  simp_rw [sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ x, 2 * a x * ((n : ℝ)⁻¹ * ∑ i, a i)) =
      2 * (∑ x, a x) * ((n : ℝ)⁻¹ * ∑ i, a i) by
    rw [← Finset.sum_mul, ← Finset.mul_sum]]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

private theorem finMean_sampleVector_real
    (S : IIDSample Omega X mu P) (g : X → ℝ) (n : ℕ) (omega : Omega) :
    finMean (fun i ↦ g (S.sampleVector n omega i)) =
      S.sampleMean g n omega := by
  unfold finMean IIDSample.sampleVector IIDSample.sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ g (S.Z i omega)) n]
  rw [smul_eq_mul]

private theorem finMean_apply_real
    {d n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (finMean v) j = finMean (fun i ↦ v i j) := by
  unfold finMean
  simp [Finset.sum_apply]

private theorem euclidean_norm_le_sum_abs_real
    {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ∑ j, |v j| := by
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_iff).2
  constructor
  · exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · simpa [Real.norm_eq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun j ↦ |v j|)
        (fun j hj ↦ abs_nonneg (v j)))

private theorem euclidean_norm_event_subset_coordinate_thresholds
    {A : Type*} {d : ℕ} (v : A → EuclideanSpace ℝ (Fin d)) (M : Fin d → ℝ) :
    {x | (∑ j, M j) < ‖v x‖} ⊆
      ⋃ j : Fin d, {x | M j < |v x j|} := by
  intro x hx
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
  have hsum : ∑ j, |v x j| ≤ ∑ j, M j :=
    Finset.sum_le_sum fun j hj ↦ hnot j
  exact (not_lt_of_ge ((euclidean_norm_le_sum_abs_real (v x)).trans hsum)) hx

/-- **Exact conditional Chebyshev bound.** For [a measurable real statistic](hyp:g,hg),
[nonempty observed data](hyp:x,hn), and [a positive threshold](hyp:M,hM), [the conditional
tail of the square-root-scaled bootstrap mean is at most the empirical variance divided by the
threshold squared](goal). -/
theorem bootstrapMean_chebyshev
    (g : X → ℝ) (hg : Measurable g) {n : ℕ} (x : Fin n → X)
    (hn : n ≠ 0) (M : ℝ) (hM : 0 < M) :
    (bootstrapResample x).real
        {xstar | M < |scaledBootstrapMeanDifference g n x xstar|} ≤
      (finMean (fun i ↦ (g (x i)) ^ 2) -
        (finMean (fun i ↦ g (x i))) ^ 2) / M ^ 2 := by
  let D : (Fin n → X) → ℝ := fun xstar ↦
    scaledBootstrapMeanDifference g n x xstar
  have hD : Measurable D := by
    dsimp [D, scaledBootstrapMeanDifference]
    unfold finMean
    fun_prop
  let _ : IsProbabilityMeasure (bootstrapResample x) :=
    bootstrapResample_isProbabilityMeasure x hn
  have hDsq : Integrable (fun xstar ↦ (D xstar) ^ 2) (bootstrapResample x) :=
    integrable_bootstrapResample_real x _ (hD.pow_const 2)
  have hDmem : MemLp D 2 (bootstrapResample x) :=
    (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).2 hDsq
  have hmean : (∫ xstar, D xstar ∂bootstrapResample x) = 0 := by
    change (∫ xstar, Real.sqrt n *
      (finMean (fun i ↦ g (xstar i)) - finMean (fun i ↦ g (x i)))
      ∂bootstrapResample x) = 0
    rw [integral_const_mul, integral_sub
      (integrable_bootstrapResample_real x _ (by
        unfold finMean
        fun_prop)) (integrable_const _),
      integral_finMean_bootstrapResample_real x g hg hn]
    simp
  have hvar : variance D (bootstrapResample x) =
      finMean (fun i ↦ (g (x i)) ^ 2) -
        (finMean (fun i ↦ g (x i))) ^ 2 := by
    rw [variance_eq_integral hD.aemeasurable, hmean]
    simp only [sub_zero]
    change (∫ xstar, (Real.sqrt n *
      (finMean (fun i ↦ g (xstar i)) - finMean (fun i ↦ g (x i)))) ^ 2
      ∂bootstrapResample x) = _
    rw [integral_centered_finMean_sq_bootstrapResample_real x g hg hn,
      centered_finMean_sq_eq (fun i ↦ g (x i)) hn]
  have hcheb := Concentration.probability_abs_sub_mean_gt_le
    (bootstrapResample x) D 0
      (finMean (fun i ↦ (g (x i)) ^ 2) -
        (finMean (fun i ↦ g (x i))) ^ 2) M
      hDmem hM hmean hvar.le
  rw [measureReal_def]
  simpa only [D, sub_zero] using hcheb

/-- For [an iid sample](hyp:S) and a [measurable square-integrable real
statistic](hyp:g,hg,hg2), [the square-root-scaled centered bootstrap mean is conditionally bounded
in probability for almost every data sequence](goal). -/
theorem scaledBootstrapMeanDifference_conditionallyBounded
    (S : IIDSample Omega X mu P) (g : X → ℝ)
    (hg : Measurable g) (hg2 : Integrable (fun x ↦ (g x) ^ 2) P) :
    ConditionallyBoundedInProbability S (scaledBootstrapMeanDifference g) := by
  unfold ConditionallyBoundedInProbability
  filter_upwards [empiricalVar_tendsto_ae S g hg hg2] with omega hvar
  intro epsilon hepsilon
  let B : ℝ := |variance g P| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let M : ℝ := Real.sqrt (B / epsilon + 1)
  have hM : 0 < M := by
    dsimp [M]
    exact Real.sqrt_pos.2 (by positivity)
  refine ⟨M, hM, ?_⟩
  have hvar_bound : ∀ᶠ n : ℕ in atTop, S.empiricalVar g n omega < B :=
    hvar.eventually (eventually_lt_nhds (by
      dsimp [B]
      linarith [le_abs_self (variance g P)]))
  filter_upwards [hvar_bound, eventually_ne_atTop 0] with n hnvar hn
  have hcheb := bootstrapMean_chebyshev g hg (S.sampleVector n omega) hn M hM
  have hemp :
      finMean (fun i ↦ (g (S.sampleVector n omega i)) ^ 2) -
          (finMean (fun i ↦ g (S.sampleVector n omega i))) ^ 2 =
        S.empiricalVar g n omega := by
    rw [finMean_sampleVector_real S (fun x ↦ (g x) ^ 2) n omega,
      finMean_sampleVector_real S g n omega]
    rfl
  calc
    (bootstrapResample (S.sampleVector n omega)).real
        {xstar | M < ‖scaledBootstrapMeanDifference g n
          (S.sampleVector n omega) xstar‖} ≤
        S.empiricalVar g n omega / M ^ 2 := by
          simpa [Real.norm_eq_abs, hemp] using hcheb
    _ < B / M ^ 2 := by
      exact div_lt_div_of_pos_right hnvar (sq_pos_of_pos hM)
    _ < epsilon := by
      dsimp [M]
      rw [Real.sq_sqrt (by positivity : 0 ≤ B / epsilon + 1)]
      rw [div_lt_iff₀ (by positivity : 0 < B / epsilon + 1)]
      calc
        B < B + epsilon := lt_add_of_pos_right B hepsilon
        _ = epsilon * (B / epsilon + 1) := by field_simp

/-- For [a measurable finite-dimensional moment function](hyp:g,hg), [nonempty observed
data](hyp:x,hn), [a coordinate](hyp:j), and [a positive threshold](hyp:M,hM), [that coordinate
of the scaled bootstrap mean obeys the empirical-variance Chebyshev bound](goal). -/
theorem bootstrapMeanVec_coordinate_chebyshev
    {d : ℕ} (g : X → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    {n : ℕ} (x : Fin n → X) (j : Fin d)
    (hn : n ≠ 0) (M : ℝ) (hM : 0 < M) :
    (bootstrapResample x).real
        {xstar | M < |(scaledBootstrapMeanDifference g n x xstar) j|} ≤
      (finMean (fun i ↦ (g (x i) j) ^ 2) -
        (finMean (fun i ↦ g (x i) j)) ^ 2) / M ^ 2 := by
  have h := bootstrapMean_chebyshev (fun z ↦ g z j) (by fun_prop)
    x hn M hM
  simpa only [scaledBootstrapMeanDifference, PiLp.smul_apply, PiLp.sub_apply,
    finMean_apply_real, smul_eq_mul] using h

/-- **Finite-dimensional bootstrap tightness.** For [an iid sample](hyp:S) and a [measurable
vector statistic with integrable squared norm](hyp:g,hg,hg2), [the norm of its
square-root-scaled centered bootstrap mean is conditionally bounded in probability almost
surely in the data](goal). -/
theorem scaledBootstrapMeanDifferenceVec_conditionallyBounded
    {d : ℕ} (S : IIDSample Omega X mu P)
    (g : X → EuclideanSpace ℝ (Fin d))
    (hg : Measurable g) (hg2 : Integrable (fun x ↦ ‖g x‖ ^ 2) P) :
    ConditionallyBoundedInProbability S (scaledBootstrapMeanDifference g) := by
  have hcoord_sq : ∀ j : Fin d, Integrable (fun x ↦ (g x j) ^ 2) P := by
    intro j
    apply hg2.mono (by fun_prop)
    filter_upwards with x
    have hnorm : |g x j| ≤ ‖g x‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (g x) j
    have hsq := (sq_le_sq₀ (abs_nonneg (g x j)) (norm_nonneg (g x))).2 hnorm
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using hsq
  have hcoord : ∀ᵐ omega ∂mu, ∀ j : Fin d, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
        (bootstrapResample (S.sampleVector n omega)).real
          {xstar | M < ‖scaledBootstrapMeanDifference (fun x ↦ g x j) n
            (S.sampleVector n omega) xstar‖} < epsilon := by
    rw [ae_all_iff]
    intro j
    exact scaledBootstrapMeanDifference_conditionallyBounded S
      (fun x ↦ g x j) (by fun_prop) (hcoord_sq j)
  unfold ConditionallyBoundedInProbability
  filter_upwards [hcoord] with omega homega
  intro epsilon hepsilon
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards with n
    have hv : ∀ xstar : Fin n → X,
        scaledBootstrapMeanDifference g n (S.sampleVector n omega) xstar = 0 :=
      fun xstar ↦ Subsingleton.elim _ _
    simp_rw [hv, norm_zero, not_lt_of_ge zero_le_one]
    simpa using hepsilon
  · let eta : ℝ := epsilon / d
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    choose M hM htail using fun j ↦ homega j eta heta
    let R : ℝ := ∑ j : Fin d, M j
    have hR : 0 < R := by
      dsimp [R]
      apply Finset.sum_pos
      · intro j hj
        exact hM j
      · exact ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩
    refine ⟨R, hR, ?_⟩
    have hall : ∀ᶠ n : ℕ in atTop, ∀ j : Fin d,
        (bootstrapResample (S.sampleVector n omega)).real
          {xstar | M j < ‖scaledBootstrapMeanDifference (fun x ↦ g x j) n
            (S.sampleVector n omega) xstar‖} < eta :=
      eventually_all.2 htail
    filter_upwards [hall, eventually_ne_atTop 0] with n hnall hn
    let data : Fin n → X := S.sampleVector n omega
    let V : (Fin n → X) → EuclideanSpace ℝ (Fin d) := fun xstar ↦
      scaledBootstrapMeanDifference g n data xstar
    have hset : {xstar | R < ‖V xstar‖} ⊆
        ⋃ j : Fin d, {xstar | M j < |V xstar j|} := by
      simpa only [R] using
        euclidean_norm_event_subset_coordinate_thresholds V M
    let _ : IsProbabilityMeasure (bootstrapResample data) :=
      bootstrapResample_isProbabilityMeasure data hn
    calc
      (bootstrapResample (S.sampleVector n omega)).real
          {xstar | R < ‖scaledBootstrapMeanDifference g n
            (S.sampleVector n omega) xstar‖} =
          (bootstrapResample data).real {xstar | R < ‖V xstar‖} := rfl
      _ ≤ (bootstrapResample data).real
          (⋃ j : Fin d, {xstar | M j < |V xstar j|}) :=
        measureReal_mono hset (measure_ne_top _ _)
      _ ≤ ∑ j : Fin d, (bootstrapResample data).real
          {xstar | M j < |V xstar j|} :=
        measureReal_iUnion_fintype_le _
      _ < ∑ _j : Fin d, eta := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩
        · intro j hj
          simpa only [data, V, scaledBootstrapMeanDifference, PiLp.smul_apply,
            PiLp.sub_apply, finMean_apply_real, Real.norm_eq_abs, smul_eq_mul] using
            hnall j
      _ = epsilon := by
        dsimp [eta]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end

end Causalean.Stat
