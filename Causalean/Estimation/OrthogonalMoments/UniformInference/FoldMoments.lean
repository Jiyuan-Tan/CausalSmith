module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Basic
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcessHighProbability

/-! # Uniform foldwise score rates and centered fold moments

On a training-measurable good event, each fold's estimated score has a
deterministic L² approximation rate and a deterministic mean-drift rate
(`RateConditions`). Conditional independence of the evaluation fold then gives the
good-event second moment and zero mean of the foldwise centered process. The tail
bound and asymptotic linearity built on these moments live in `FoldRates`.
-/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

/-- Uniform score rates hold when each fold's estimated-minus-oracle score
is jointly and training-measurable, has L² norm at most `r n` and mean drift
at most `C * a n * b n` on a training-measurable good event, and that event fails with
probability at most `δ n` uniformly over the current law class. The rates
`r n`, `√n a n b n`, and `δ n` vanish. -/
structure RateConditions (r a b : ℕ → ℝ) (C : ℝ) (δ : ℕ → ℝ≥0∞) where
  good : ℕ → ι → Fin K → Set Ω
  r_nonneg : ∀ n, 0 ≤ r n
  a_nonneg : ∀ n, 0 ≤ a n
  b_nonneg : ∀ n, 0 ≤ b n
  C_nonneg : 0 ≤ C
  r_tendsto : Tendsto r atTop (𝓝 0)
  sqrt_product_tendsto :
    Tendsto (fun (n : ℕ) => Real.sqrt (n : ℝ) * a n * b n) atTop (𝓝 0)
  δ_tendsto : Tendsto δ atTop (𝓝 0)
  fail : ∀ n p, p ∈ F.lawClass n → ∀ k,
    F.sampleLaw p (good n p k)ᶜ ≤ δ n
  good_train : ∀ n p k,
    MeasurableSet[MeasurableSpace.comap
      (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
      inferInstance] (good n p k)
  diff_meas : ∀ n p k,
    Measurable (fun q : Ω × Z =>
      F.score n p k q.1 q.2 - F.oracle p q.2)
  diff_train : ∀ n p k,
    Measurable[(MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace Z)]
      (fun q : Ω × Z => F.score n p k q.1 q.2 - F.oracle p q.2)
  diff_L2 : ∀ n p k ω, ω ∈ good n p k →
    MemLp (fun z => F.score n p k ω z - F.oracle p z) 2 (F.laws p) ∧
    (eLpNorm (fun z => F.score n p k ω z - F.oracle p z) 2
      (F.laws p)).toReal ≤ r n
  drift : ∀ n p k ω, ω ∈ good n p k →
    |∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p| ≤ C * a n * b n

namespace Family

/-- The foldwise centered empirical process is the held-out sum of the
estimated-minus-oracle score after subtracting its training-conditional
population mean, scaled by the square root of the full sample size. -/
noncomputable def foldCentered (n : ℕ) (p : ι) (k : Fin K) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i ∈ (F.split p).fold n k,
      ((F.score n p k ω ((F.sample p).Z i ω) -
          F.oracle p ((F.sample p).Z i ω)) -
        ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p)

/-- [Under the uniform score-rate conditions](hyp:R), [the integral over the training-measurable
good event of the squared foldwise centered process is at most the squared L² score rate](goal).
-/
theorem foldCentered_good_sq_lintegral_le
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ)
    (n : ℕ) (p : ι) (k : Fin K) :
    (∫⁻ ω in R.good n p k,
      ENNReal.ofReal ((F.foldCentered n p k ω) ^ 2) ∂F.sampleLaw p) ≤
      ENNReal.ofReal ((r n) ^ 2) := by
  classical
  letI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  letI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  have hmA :
      (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance : MeasurableSpace Ω) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (measurable_pi_iff.mpr
      fun i : (F.split p).trainComplement n k => (F.sample p).meas i) ht
  have hgood : MeasurableSet (R.good n p k) :=
    hmA _ (R.good_train n p k)
  let g : Ω → Z → ℝ := fun ω z =>
    if ω ∈ R.good n p k then F.score n p k ω z - F.oracle p z else 0
  have hg_train :
      Measurable[(MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry g) := by
    exact Measurable.ite (measurable_fst (R.good_train n p k))
      (R.diff_train n p k) measurable_const
  have hg : Measurable (Function.uncurry g) := by
    exact Measurable.ite (measurable_fst hgood)
      (R.diff_meas n p k) measurable_const
  have hmem : ∀ ω, MemLp (g ω) 2 (F.laws p) := by
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simpa [g, hω] using (R.diff_L2 n p k ω hω).1
    · simp [g, hω]
  have hnorm : ∀ ω, (eLpNorm (g ω) 2 (F.laws p)).toReal ≤ r n := by
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simpa [g, hω] using (R.diff_L2 n p k ω hω).2
    · simp [g, hω, R.r_nonneg n]
  have hL2 :
      (∫⁻ ω, ENNReal.ofReal ((eLpNorm (g ω) 2 (F.laws p)).toReal ^ 2)
        ∂F.sampleLaw p) ≤ ENNReal.ofReal ((r n) ^ 2) := by
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((r n) ^ 2) ∂F.sampleLaw p := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        have hnn : 0 ≤ (eLpNorm (g ω) 2 (F.laws p)).toReal :=
          ENNReal.toReal_nonneg
        nlinarith [hnorm ω, hnn, R.r_nonneg n]
      _ = _ := by simp
  have hiid :
      (F.sampleLaw p).map
        (fun ω (i : (F.split p).fold n k) => (F.sample p).Z i ω) =
      Measure.pi (fun _ : (F.split p).fold n k => F.laws p) := by
    have hindep_s :
        iIndepFun (fun i : (F.split p).fold n k => (F.sample p).Z i)
          (F.sampleLaw p) :=
      (F.sample p).indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : (F.split p).fold n k =>
        ((F.sample p).meas i).aemeasurable)).mp hindep_s
    calc
      _ = Measure.pi (fun i : (F.split p).fold n k =>
        (F.sampleLaw p).map ((F.sample p).Z i)) := hmap
      _ = Measure.pi (fun _ : (F.split p).fold n k => F.laws p) := by
        simp only [(F.sample p).map_eq]
  have hsq := Causalean.Mathlib.iid_centered_sum_sq_lintegral_unscaled_le
    (s := (F.split p).fold n k) (W := (F.sample p).Z)
    (fun i _ => (F.sample p).meas i)
    (MeasurableSpace.comap
      (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
      inferInstance) hmA
    ((F.split p).folds_indep n k).symm hiid g hg_train hmem
  have hcard : ((F.split p).fold n k).card ≤ n := by
    have hs : (F.split p).fold n k ⊆ Finset.range n := by
      intro i hi
      rw [← (F.split p).cover n]
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩
    simpa using Finset.card_le_card hs
  by_cases hn : n = 0
  · subst n
    simp [foldCentered]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hpoint (ω : Ω) :
      ENNReal.ofReal
        (((Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ (F.split p).fold n k,
            (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2) =
      (n : ENNReal)⁻¹ *
        ENNReal.ofReal
          ((∑ i ∈ (F.split p).fold n k,
            (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2) := by
    let z : ℝ := ∑ i ∈ (F.split p).fold n k,
      (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
    have heq : ((Real.sqrt (n : ℝ))⁻¹ * z) ^ 2 =
        ((n : ℝ)⁻¹) * z ^ 2 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (le_of_lt hnR)]
    rw [show ((Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ (F.split p).fold n k,
          (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2 =
        ((n : ℝ)⁻¹) *
          (∑ i ∈ (F.split p).fold n k,
            (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2 by
        simpa [z] using heq]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hnR))]
    rw [ENNReal.ofReal_inv_of_pos hnR]
    norm_num
  have hscaled :
      (∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ (F.split p).fold n k,
            (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2)
        ∂F.sampleLaw p) ≤ ENNReal.ofReal ((r n) ^ 2) := by
    calc
      _ = (n : ENNReal)⁻¹ *
          ∫⁻ ω, ENNReal.ofReal
            ((∑ i ∈ (F.split p).fold n k,
              (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)) ^ 2)
            ∂F.sampleLaw p := by
          simp_rw [hpoint]
          rw [lintegral_const_mul' _ _ (by simp [hn])]
      _ ≤ (n : ENNReal)⁻¹ *
          ((↑((F.split p).fold n k).card : ENNReal) *
            ∫⁻ ω, ENNReal.ofReal
              ((eLpNorm (g ω) 2 (F.laws p)).toReal ^ 2) ∂F.sampleLaw p) := by
          gcongr
      _ ≤ (n : ENNReal)⁻¹ *
          ((↑((F.split p).fold n k).card : ENNReal) *
            ENNReal.ofReal ((r n) ^ 2)) := by
          gcongr
      _ ≤ (n : ENNReal)⁻¹ *
          ((n : ENNReal) * ENNReal.ofReal ((r n) ^ 2)) := by
          gcongr
      _ = ENNReal.ofReal ((r n) ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hn) (by simp),
            one_mul]
  let Y : Ω → ℝ := fun ω =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ (F.split p).fold n k,
        (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)
  have hclip (ω : Ω) :
      Y ω = if ω ∈ R.good n p k then F.foldCentered n p k ω else 0 := by
    by_cases hω : ω ∈ R.good n p k
    · simp [Y, g, hω, foldCentered]
    · simp [Y, g, hω]
  have hset :
      (∫⁻ ω in R.good n p k,
        ENNReal.ofReal ((F.foldCentered n p k ω) ^ 2) ∂F.sampleLaw p) =
      ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂F.sampleLaw p := by
    rw [← lintegral_indicator hgood]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simp [Set.indicator, hω, hclip ω]
    · simp [Set.indicator, hω, hclip ω]
  simpa only [hset] using hscaled

/-- [Under the uniform score-rate conditions](hyp:R), [the integral over the training-measurable
good event of the squared foldwise centered score process is at most the square of its L²
rate](goal). -/
theorem foldCentered_good_secondMoment
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ)
    (n : ℕ) (p : ι) (k : Fin K) :
    ∫ ω in R.good n p k, (F.foldCentered n p k ω) ^ 2
      ∂F.sampleLaw p ≤ (r n) ^ 2 := by
  letI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  letI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  have hdiffMean :
      Measurable (fun ω => ∫ z,
        F.score n p k ω z - F.oracle p z ∂F.laws p) :=
    (R.diff_meas n p k).stronglyMeasurable.integral_prod_right.measurable
  have hfold : Measurable (F.foldCentered n p k) := by
    unfold foldCentered
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact ((R.diff_meas n p k).comp
      (measurable_id.prodMk ((F.sample p).meas i))).sub hdiffMean
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    ((hfold.pow_const 2).aestronglyMeasurable)]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _)
    (F.foldCentered_good_sq_lintegral_le R n p k)

/-- On a training-measurable good event, the held-out centered score has
zero integrated conditional mean under the law of the full sample. -/
theorem foldCentered_good_mean_zero
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ)
    (n : ℕ) (p : ι) (k : Fin K) :
    ∫ ω in R.good n p k, F.foldCentered n p k ω ∂F.sampleLaw p = 0 := by
  classical
  letI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  letI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  have hmA :
      (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance : MeasurableSpace Ω) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (measurable_pi_iff.mpr
      fun i : (F.split p).trainComplement n k => (F.sample p).meas i) ht
  have hgood : MeasurableSet (R.good n p k) :=
    hmA _ (R.good_train n p k)
  have hdiffMean :
      Measurable (fun ω => ∫ z,
        F.score n p k ω z - F.oracle p z ∂F.laws p) :=
    (R.diff_meas n p k).stronglyMeasurable.integral_prod_right.measurable
  have hfold : Measurable (F.foldCentered n p k) := by
    unfold foldCentered
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact ((R.diff_meas n p k).comp
      (measurable_id.prodMk ((F.sample p).meas i))).sub hdiffMean
  have hsqInt : Integrable (fun ω => (F.foldCentered n p k ω) ^ 2)
      ((F.sampleLaw p).restrict (R.good n p k)) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((hfold.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).mp
    exact ne_top_of_le_ne_top (by simp)
      (F.foldCentered_good_sq_lintegral_le R n p k)
  have hfoldLp : MemLp (F.foldCentered n p k) 2
      ((F.sampleLaw p).restrict (R.good n p k)) :=
    (memLp_two_iff_integrable_sq hfold.aestronglyMeasurable).mpr hsqInt
  have hfoldInt : IntegrableOn (F.foldCentered n p k)
      (R.good n p k) (F.sampleLaw p) :=
    hfoldLp.integrable (by norm_num)
  let g : Ω → Z → ℝ := fun ω z =>
    if ω ∈ R.good n p k then F.score n p k ω z - F.oracle p z else 0
  have hg_train :
      Measurable[(MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace Z)]
        (Function.uncurry g) := by
    exact Measurable.ite (measurable_fst (R.good_train n p k))
      (R.diff_train n p k) measurable_const
  have hmem : ∀ ω, MemLp (g ω) 2 (F.laws p) := by
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simpa [g, hω] using (R.diff_L2 n p k ω hω).1
    · simp [g, hω]
  let Y : Ω → ℝ := fun ω =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ (F.split p).fold n k,
        (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)
  have hclip (ω : Ω) :
      Y ω = if ω ∈ R.good n p k then F.foldCentered n p k ω else 0 := by
    by_cases hω : ω ∈ R.good n p k
    · simp [Y, g, hω, foldCentered]
    · simp [Y, g, hω]
  have hYint : Integrable Y (F.sampleLaw p) := by
    have h := hfoldInt.integrable_indicator hgood
    have hEq : Y = (R.good n p k).indicator (F.foldCentered n p k) := by
      funext ω
      rw [hclip]
      by_cases hω : ω ∈ R.good n p k
      · simp [Set.indicator, hω]
      · simp [Set.indicator, hω]
    rw [hEq]
    exact h
  let s : Finset ℕ := (F.split p).fold n k
  let νX : Measure ((i : s) → Z) := Measure.pi (fun _ : s => F.laws p)
  let J : Ω → Ω × ((i : s) → Z) :=
    fun ω => (ω, fun i : s => (F.sample p).Z i ω)
  let H : Ω × ((i : s) → Z) → ℝ :=
    fun q => (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i : s, (g q.1 (q.2 i) - ∫ z, g q.1 z ∂F.laws p)
  have hZmeas :
      Measurable (fun ω (i : s) => (F.sample p).Z i ω) :=
    measurable_pi_iff.mpr fun i : s => (F.sample p).meas i
  have hJmeas :
      @Measurable Ω (Ω × ((i : s) → Z)) _
        ((MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance).prod inferInstance) J :=
    (measurable_id'' hmA).prodMk hZmeas
  have hiid :
      (F.sampleLaw p).map (fun ω (i : s) => (F.sample p).Z i ω) =
        νX := by
    have hindep_s :
        iIndepFun (fun i : s => (F.sample p).Z i) (F.sampleLaw p) :=
      (F.sample p).indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : s => ((F.sample p).meas i).aemeasurable)).mp hindep_s
    calc
      _ = Measure.pi (fun i : s =>
        (F.sampleLaw p).map ((F.sample p).Z i)) := hmap
      _ = νX := by simp [νX, (F.sample p).map_eq]
  have hJlaw :
      @Measure.map Ω (Ω × ((i : s) → Z)) _
        ((MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance).prod inferInstance)
        J (F.sampleLaw p) =
      @Measure.prod Ω ((i : s) → Z)
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance
        ((F.sampleLaw p).trim hmA) νX := by
    have hraw := Causalean.Mathlib.indep_trim_prod_map_eq
      (Ω := Ω) (β := ((i : s) → Z)) (μ := F.sampleLaw p)
      (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance) hmA hZmeas.aemeasurable
      ((F.split p).folds_indep n k).symm
    simpa [J, νX, hiid] using hraw
  have hc_train :
      @Measurable Ω ℝ
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance
        (fun ω => ∫ z, g ω z ∂F.laws p) := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
      inferInstance
    exact hg_train.stronglyMeasurable.integral_prod_right.measurable
  have hHmeas :
      @Measurable (Ω × ((i : s) → Z)) ℝ
        ((MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance).prod inferInstance) inferInstance H := by
    dsimp [H]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    have hpair :
        @Measurable (Ω × ((i : s) → Z)) (Ω × Z)
          ((MeasurableSpace.comap
            (fun ω (j : (F.split p).trainComplement n k) => (F.sample p).Z j ω)
            inferInstance).prod inferInstance)
          ((MeasurableSpace.comap
            (fun ω (j : (F.split p).trainComplement n k) => (F.sample p).Z j ω)
            inferInstance).prod inferInstance)
          (fun q => (q.1, q.2 i)) := by
      exact measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact (hg_train.comp hpair).sub (hc_train.comp measurable_fst)
  have hcomp : H ∘ J = Y := by
    funext ω
    change (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i : s, (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p) =
      (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ (F.split p).fold n k,
          (g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p)
    congr 1
    simpa [s] using
      (Finset.sum_attach ((F.split p).fold n k)
        (fun i => g ω ((F.sample p).Z i ω) - ∫ z, g ω z ∂F.laws p))
  letI : MeasurableSpace (Ω × ((i : s) → Z)) :=
    (MeasurableSpace.comap
      (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
      inferInstance).prod inferInstance
  have hHint : Integrable H ((F.sampleLaw p).map J) := by
    apply (integrable_map_measure hHmeas.aestronglyMeasurable
      hJmeas.aemeasurable).mpr
    simpa only [hcomp] using hYint
  have hinner (ω : Ω) : (∫ v, H (ω, v) ∂νX) = 0 := by
    have hterm (i : s) :
        ∫ v : ((i : s) → Z),
          (g ω (v i) - ∫ z, g ω z ∂F.laws p) ∂νX = 0 := by
      have hgi : Integrable (g ω) (F.laws p) :=
        (hmem ω).integrable (by norm_num)
      have hmp := measurePreserving_eval
        (fun _ : s => F.laws p) i
      have hcompInt : Integrable (fun v : ((i : s) → Z) => g ω (v i)) νX :=
        (by
          have hmp' : MeasurePreserving (Function.eval i) νX (F.laws p) := by
            simpa [νX] using hmp
          exact (hmp'.integrable_comp hgi.aestronglyMeasurable).2 hgi)
      have hmap : (∫ v : ((i : s) → Z), g ω (v i) ∂νX) =
          ∫ z, g ω z ∂F.laws p := by
        have hgi_map :
            AEStronglyMeasurable (g ω)
              (νX.map (Function.eval i)) := by
          simpa [νX, hmp.map_eq] using hgi.aestronglyMeasurable
        have h := integral_map hmp.aemeasurable hgi_map
        rw [hmp.map_eq] at h
        simpa [νX] using h.symm
      rw [integral_sub hcompInt (integrable_const _), hmap]
      simp
    simp only [H]
    rw [integral_const_mul]
    rw [integral_finset_sum]
    · simp [hterm]
    · intro i hi
      have hgi : Integrable (g ω) (F.laws p) :=
        (hmem ω).integrable (by norm_num)
      have hmp := measurePreserving_eval (fun _ : s => F.laws p) i
      have hcompInt : Integrable (fun v : ((i : s) → Z) => g ω (v i)) νX := by
        have hmp' : MeasurePreserving (Function.eval i) νX (F.laws p) := by
          simpa [νX] using hmp
        exact (hmp'.integrable_comp hgi.aestronglyMeasurable).2 hgi
      exact hcompInt.sub (integrable_const _)
  have hHint' : Integrable H
      (@Measure.prod Ω ((i : s) → Z)
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance
        ((F.sampleLaw p).trim hmA) νX) := by
    simpa only [hJlaw] using hHint
  have hfull : (∫ ω, Y ω ∂F.sampleLaw p) = 0 := by
    calc
      _ = ∫ q, H q ∂((F.sampleLaw p).map J) := by
        rw [← hcomp]
        exact (integral_map hJmeas.aemeasurable
          hHmeas.aestronglyMeasurable).symm
      _ = ∫ q, H q ∂
          (@Measure.prod Ω ((i : s) → Z)
            (MeasurableSpace.comap
              (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
              inferInstance) inferInstance
            ((F.sampleLaw p).trim hmA) νX) := by rw [hJlaw]
      _ = ∫ ω, ∫ v, H (ω, v) ∂νX ∂((F.sampleLaw p).trim hmA) := by
        letI : MeasurableSpace Ω := MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance
        exact integral_prod H hHint'
      _ = 0 := by simp [hinner]
  rw [← integral_indicator hgood]
  have hEq :
      (R.good n p k).indicator (F.foldCentered n p k) = Y := by
    funext ω
    rw [hclip]
    by_cases hω : ω ∈ R.good n p k
    · simp [Set.indicator, hω]
    · simp [Set.indicator, hω]
  rw [hEq]
  exact hfull

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
