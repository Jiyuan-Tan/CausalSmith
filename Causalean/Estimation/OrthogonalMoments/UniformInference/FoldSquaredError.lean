module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldRates

/-! # Held-out squared score error

Training measurability and independence of the evaluation fold bound the
observed squared score error by its population L² rate, on the fold's good
event. This is the variance-estimation counterpart of the centered fold sum.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions](hyp:R), at
[a positive sample size n](hyp:n,hn), [a law p](hyp:p) and [an evaluation fold k](hyp:k),
[the expected held-out average of the squared estimated-minus-oracle scores, restricted to the
training-measurable good event, is at most the squared L² score rate r(n)²](goal).

The average divides the fold's sum by the full sample size n. -/
theorem foldSquaredError_good_lintegral_le
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ)
    (n : ℕ) (hn : 0 < n) (p : ι) (k : Fin K) :
    (∫⁻ ω in R.good n p k,
      ENNReal.ofReal ((n : ℝ)⁻¹ *
        ∑ i ∈ (F.split p).fold n k,
          (F.score n p k ω ((F.sample p).Z i ω) -
            F.oracle p ((F.sample p).Z i ω)) ^ 2) ∂F.sampleLaw p) ≤
      ENNReal.ofReal ((r n) ^ 2) := by
  /- Clip the score difference to zero outside `R.good`. For each training
  realization the evaluation coordinates have law `F.laws p`; integrate the
  finite sum through the product law, then use `R.diff_L2` and card(fold) ≤ n.
  The corresponding centered-sum construction is in `FoldRates`. -/
  classical
  letI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  letI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  let s := (F.split p).fold n k
  have hmA : (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    exact (measurable_pi_iff.mpr
      fun i : (F.split p).trainComplement n k => (F.sample p).meas i) hu
  have hgood : MeasurableSet (R.good n p k) :=
    hmA _ (R.good_train n p k)
  let g : Ω → Z → ℝ := fun ω z =>
    if ω ∈ R.good n p k then F.score n p k ω z - F.oracle p z else 0
  have hg_train : Measurable[(MeasurableSpace.comap
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
  have hnorm : ∀ ω, (eLpNorm (g ω) 2 (F.laws p)).toReal ≤ r n := by
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simpa [g, hω] using (R.diff_L2 n p k ω hω).2
    · simp [g, hω, R.r_nonneg n]
  have htuple : Measurable
      (fun ω => fun i : s => (F.sample p).Z i ω) := by
    exact measurable_pi_iff.mpr fun i => (F.sample p).meas i
  have hiid :
      (F.sampleLaw p).map (fun ω (i : s) => (F.sample p).Z i ω) =
      Measure.pi (fun _ : s => F.laws p) := by
    have hindep : iIndepFun (fun i : s => (F.sample p).Z i)
        (F.sampleLaw p) :=
      (F.sample p).indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : s => ((F.sample p).meas i).aemeasurable)).mp hindep
    calc
      _ = Measure.pi (fun i : s =>
          (F.sampleLaw p).map ((F.sample p).Z i)) := hmap
      _ = Measure.pi (fun _ : s => F.laws p) := by
        simp only [(F.sample p).map_eq]
  have hjoin :
      @Measure.map Ω (Ω × (s → Z)) _ (@Prod.instMeasurableSpace Ω (s → Z)
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance)
        (fun ω => (ω, fun i : s => (F.sample p).Z i ω)) (F.sampleLaw p) =
      @Measure.prod Ω (s → Z)
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance
        ((F.sampleLaw p).trim hmA)
        (Measure.pi (fun _ : s => F.laws p)) := by
    have hraw := Causalean.Mathlib.indep_trim_prod_map_eq
      (Ω := Ω) (β := s → Z) (μ := F.sampleLaw p)
      (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance) hmA htuple.aemeasurable ((F.split p).folds_indep n k).symm
    simpa [hiid] using hraw
  have hterm (i : ℕ) (hi : i ∈ s) :
      (∫⁻ ω, ENNReal.ofReal ((g ω ((F.sample p).Z i ω)) ^ 2)
        ∂F.sampleLaw p) ≤ ENNReal.ofReal ((r n) ^ 2) := by
    let j : s := ⟨i, hi⟩
    let H : Ω × (s → Z) → ENNReal :=
      fun q => ENNReal.ofReal ((g q.1 (q.2 j)) ^ 2)
    have hH : Measurable[(MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace (s → Z))]
        H := by
      have hpair : @Measurable (Ω × (s → Z)) (Ω × Z)
        ((MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace (s → Z)))
        ((MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace Z))
          (fun q : Ω × (s → Z) => (q.1, q.2 j)) := by
        letI : MeasurableSpace Ω := MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance
        fun_prop
      have hreal : Measurable[(MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance).prod (inferInstance : MeasurableSpace (s → Z))]
          (fun q : Ω × (s → Z) => (g q.1 (q.2 j)) ^ 2) := by
        simpa only [Function.uncurry, Function.comp_def] using
          (hg_train.comp hpair).pow_const 2
      exact ENNReal.measurable_ofReal.comp hreal
    have hJ : @Measurable Ω (Ω × (s → Z)) _
        ((MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance).prod inferInstance)
        (fun ω => (ω, fun j : s => (F.sample p).Z j ω)) := by
      exact (measurable_id'' hmA).prod htuple
    have hinner (ω : Ω) :
        (∫⁻ v : s → Z, H (ω, v) ∂Measure.pi (fun _ : s => F.laws p)) =
        ∫⁻ z, ENNReal.ofReal ((g ω z) ^ 2) ∂F.laws p := by
      have hf : Measurable (fun z => ENNReal.ofReal ((g ω z) ^ 2)) := by
        have hp : @Measurable Z (Ω × Z) _
            ((MeasurableSpace.comap
              (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
              inferInstance).prod inferInstance)
            (fun z : Z => (ω, z)) := by
          letI : MeasurableSpace Ω := MeasurableSpace.comap
            (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
            inferInstance
          fun_prop
        exact ENNReal.measurable_ofReal.comp (by
          simpa only [Function.uncurry, Function.comp_def] using
            (hg_train.comp hp).pow_const 2)
      simpa [H, j] using
        (measurePreserving_eval (fun _ : s => F.laws p) j).lintegral_comp hf
    have henergy (ω : Ω) :
        (∫⁻ z, ENNReal.ofReal ((g ω z) ^ 2) ∂F.laws p) =
        ENNReal.ofReal ((eLpNorm (g ω) 2 (F.laws p)).toReal ^ 2) := by
      have hint : Integrable (fun z => (g ω z) ^ 2) (F.laws p) :=
        (hmem ω).integrable_sq
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun z => sq_nonneg (g ω z))]
      have he := Causalean.Mathlib.eLpNorm_two_sq_toReal_eq_integral_sq
        (hmem ω)
      simpa [Real.norm_eq_abs, sq_abs] using he.symm
    calc
      _ = ∫⁻ q, H q ∂@Measure.map Ω (Ω × (s → Z)) _
          (@Prod.instMeasurableSpace Ω (s → Z)
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
          inferInstance) inferInstance)
          (fun ω => (ω, fun j : s => (F.sample p).Z j ω))
          (F.sampleLaw p) := by
            rw [@lintegral_map Ω (Ω × (s → Z)) _
              (@Prod.instMeasurableSpace Ω (s → Z)
                (MeasurableSpace.comap
                  (fun ω (j : (F.split p).trainComplement n k) =>
                    (F.sample p).Z j ω) inferInstance) inferInstance)
              (F.sampleLaw p) H
              (fun ω => (ω, fun j : s => (F.sample p).Z j ω)) hH hJ]
      _ = ∫⁻ q, H q ∂@Measure.prod Ω (s → Z)
          (MeasurableSpace.comap
            (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
            inferInstance) inferInstance
          ((F.sampleLaw p).trim hmA)
          (Measure.pi (fun _ : s => F.laws p)) := by rw [hjoin]
      _ = ∫⁻ ω, ∫⁻ v, H (ω, v) ∂Measure.pi
          (fun _ : s => F.laws p) ∂(F.sampleLaw p).trim hmA :=
            @lintegral_prod Ω (s → Z)
              (MeasurableSpace.comap
                (fun ω (j : (F.split p).trainComplement n k) =>
                  (F.sample p).Z j ω) inferInstance) inferInstance
              ((F.sampleLaw p).trim hmA)
              (Measure.pi (fun _ : s => F.laws p)) _ H hH.aemeasurable
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((r n) ^ 2)
          ∂(F.sampleLaw p).trim hmA := by
        apply lintegral_mono
        intro ω
        change (∫⁻ v : s → Z, H (ω, v) ∂Measure.pi
          (fun _ : s => F.laws p)) ≤ ENNReal.ofReal ((r n) ^ 2)
        rw [hinner ω, henergy ω]
        apply ENNReal.ofReal_le_ofReal
        have hnn : 0 ≤ (eLpNorm (g ω) 2 (F.laws p)).toReal :=
          ENNReal.toReal_nonneg
        nlinarith [hnorm ω, hnn, R.r_nonneg n]
      _ = ENNReal.ofReal ((r n) ^ 2) := by
        simp [trim_measurableSet_eq hmA MeasurableSet.univ]
  have hcard : s.card ≤ n := by
    have hs : s ⊆ Finset.range n := by
      intro i hi
      rw [← (F.split p).cover n]
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩
    simpa [s] using Finset.card_le_card hs
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpoint (ω : Ω) :
      ENNReal.ofReal ((n : ℝ)⁻¹ *
        ∑ i ∈ s, (g ω ((F.sample p).Z i ω)) ^ 2) =
      (n : ENNReal)⁻¹ *
        ∑ i ∈ s, ENNReal.ofReal ((g ω ((F.sample p).Z i ω)) ^ 2) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hnR)),
      ENNReal.ofReal_inv_of_pos hnR]
    norm_num
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i hi
    exact sq_nonneg _
  have hscaled :
      (∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ *
        ∑ i ∈ s, (g ω ((F.sample p).Z i ω)) ^ 2)
        ∂F.sampleLaw p) ≤ ENNReal.ofReal ((r n) ^ 2) := by
    calc
      _ = (n : ENNReal)⁻¹ *
          ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal
            ((g ω ((F.sample p).Z i ω)) ^ 2) ∂F.sampleLaw p := by
          simp_rw [hpoint]
          rw [lintegral_const_mul' _ _ (by simp [Nat.ne_of_gt hn])]
          rw [lintegral_finsetSum]
          intro i hi
          have hm : Measurable (fun ω => g ω ((F.sample p).Z i ω)) := by
            have hp : Measurable (fun ω => (ω, (F.sample p).Z i ω)) := by
              exact measurable_id.prod ((F.sample p).meas i)
            have hg : Measurable (Function.uncurry g) := by
              exact Measurable.ite (measurable_fst hgood)
                (R.diff_meas n p k) measurable_const
            exact hg.comp hp
          exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
      _ ≤ (n : ENNReal)⁻¹ * (s.card *
          ENNReal.ofReal ((r n) ^ 2)) := by
          gcongr
          calc
            _ ≤ ∑ i ∈ s, ENNReal.ofReal ((r n) ^ 2) :=
              Finset.sum_le_sum fun i hi => hterm i hi
            _ = s.card * ENNReal.ofReal ((r n) ^ 2) := by simp
      _ ≤ (n : ENNReal)⁻¹ *
          ((n : ENNReal) * ENNReal.ofReal ((r n) ^ 2)) := by gcongr
      _ = ENNReal.ofReal ((r n) ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel
            (by simpa using Nat.ne_of_gt hn) (by simp), one_mul]
  have hclip (ω : Ω) :
      ((n : ℝ)⁻¹ * ∑ i ∈ s,
        (g ω ((F.sample p).Z i ω)) ^ 2) =
      if ω ∈ R.good n p k then
        ((n : ℝ)⁻¹ * ∑ i ∈ s,
          (F.score n p k ω ((F.sample p).Z i ω) -
            F.oracle p ((F.sample p).Z i ω)) ^ 2) else 0 := by
    by_cases hω : ω ∈ R.good n p k
    · simp [g, hω]
    · simp [g, hω]
  have hset :
      (∫⁻ ω in R.good n p k,
        ENNReal.ofReal ((n : ℝ)⁻¹ *
          ∑ i ∈ (F.split p).fold n k,
            (F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2) ∂F.sampleLaw p) =
      ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ *
        ∑ i ∈ s, (g ω ((F.sample p).Z i ω)) ^ 2) ∂F.sampleLaw p := by
    rw [← lintegral_indicator hgood]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ R.good n p k
    · simp [Set.indicator, hω, g, s]
    · simp [Set.indicator, hω, g]
  simpa only [hset] using hscaled

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
