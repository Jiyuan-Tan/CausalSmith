import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.MarkedPoisson.Palm.Decomposition

/-!
# Certificate specialization of the marked-Poisson Palm calculation

This module specializes the Palm count decomposition to finite signed certificates and derives the aggregate-mixture comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [the compact-support condition](hyp:hsupp), [the coordinate index](hyp:i), [the supplied input hi](hyp:hi). -/
theorem node_mem_support
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (i : ι) (hi : C.weight i ≠ 0) :
    C.node i ∈ Set.Icc (a / κ) B := by
  classical
  rw [variation_eq_absoluteMeasure, absoluteMeasure,
    ae_finsetSum_measure_iff] at hsupp
  have h := hsupp i (Finset.mem_univ i)
  have hc : ENNReal.ofReal |C.weight i| ≠ 0 := by simp [hi]
  rw [Measure.ae_ennreal_smul_measure_iff hc, ae_dirac_iff] at h
  · exact h
  · exact measurableSet_Icc

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the coordinate index](hyp:i). -/
theorem polarSign_node
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) (i : ι) :
    C.polarSign (C.node i) = Real.sign (C.weight i) := by
  classical
  unfold polarSign
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    have hne : C.node i ≠ C.node k := C.node_injective.ne hki.symm
    simp [hne]
  · simp

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp), [the target function](hyp:f), [the supplied input g](hyp:g), [the supplied input hf](hyp:hf), [the supplied input hg](hyp:hg), [the supplied input h0](hyp:h0). -/
theorem zeroInflated_integral_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (f g : ℝ → ℝ) (hf : Integrable f (C.zeroInflatedPrior a))
    (hg : Integrable g (C.zeroInflatedPrior a)) (h0 : f 0 = g 0) :
    (∫ p, f p ∂C.zeroInflatedPrior a) - ∫ p, g p ∂C.zeroInflatedPrior a =
      ∑ i, |C.weight i| * (a / (C.node i + a)) *
        (f (C.node i) - g (C.node i)) := by
  classical
  let dμ := C.signedMeasure.variation.withDensity
      (fun p => ENNReal.ofReal (a / (p + a)))
  let r := ENNReal.ofReal
      (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation)
  have hzero : C.zeroInflatedPrior a = dμ + r • Measure.dirac 0 := rfl
  have hfd : Integrable f dμ := by
    apply hf.mono_measure
    rw [hzero]
    exact Measure.le_add_right le_rfl
  have hfr : Integrable f (r • Measure.dirac 0) := by
    apply hf.mono_measure
    rw [hzero]
    exact Measure.le_add_left le_rfl
  have hgd : Integrable g dμ := by
    apply hg.mono_measure
    rw [hzero]
    exact Measure.le_add_right le_rfl
  have hgr : Integrable g (r • Measure.dirac 0) := by
    apply hg.mono_measure
    rw [hzero]
    exact Measure.le_add_left le_rfl
  rw [hzero, integral_add_measure hfd hfr, integral_add_measure hgd hgr]
  have hr : (∫ p, f p ∂r • Measure.dirac 0) =
      ∫ p, g p ∂r • Measure.dirac 0 := by
    simp [h0]
  rw [hr]
  simp only [add_sub_add_right_eq_sub]
  dsimp [dμ]
  rw [integral_withDensity_eq_integral_toReal_smul
      (μ := C.signedMeasure.variation)
      (by fun_prop : Measurable (fun p : ℝ => ENNReal.ofReal (a / (p + a))))
      (Filter.Eventually.of_forall fun _ => by finiteness) f,
    integral_withDensity_eq_integral_toReal_smul
      (μ := C.signedMeasure.variation)
      (by fun_prop : Measurable (fun p : ℝ => ENNReal.ofReal (a / (p + a))))
      (Filter.Eventually.of_forall fun _ => by finiteness) g,
    variation_eq_absoluteMeasure, absoluteMeasure,
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by rw [smul_eq_mul, enorm_mul]; finiteness)).smul_measure (by simp)),
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by rw [smul_eq_mul, enorm_mul]; finiteness)).smul_measure (by simp))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : C.weight i = 0
  · simp [hw]
  · have hnode := node_mem_support C a κ B hsupp i hw
    have hp : 0 < C.node i :=
      lt_of_lt_of_le (div_pos ha hκ) hnode.1
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp). -/
theorem polarSign_zero
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    C.polarSign 0 = 0 := by
  classical
  unfold polarSign
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hnode
  · by_cases hw : C.weight i = 0
    · simp [hw]
    · have hs := node_mem_support C a κ B hsupp i hw
      have hp : 0 < C.node i :=
        lt_of_lt_of_le (div_pos ha hκ) hs.1
      linarith
  · rfl

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp), [the observed count vector](hyp:z). -/
theorem markedPredictive_real_singleton_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (z : MarkedPoissonObservation) :
    (C.markedPoissonPredictive ε a u v false).real {z} -
        (C.markedPoissonPredictive ε a u v true).real {z} =
      ∑ i, |C.weight i| * (a / (C.node i + a)) *
        ((markedPoissonLaw ε a u v C.polarSign false (C.node i)).real {z} -
          (markedPoissonLaw ε a u v C.polarSign true (C.node i)).real {z}) := by
  let _ : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    C.zeroInflatedPrior_isProbabilityMeasure a κ B ha hκ hsupp
  have hreal (branch : Bool) :
      (C.markedPoissonPredictive ε a u v branch).real {z} =
        ∫ p, (markedPoissonLaw ε a u v C.polarSign branch p).real {z}
          ∂C.zeroInflatedPrior a := by
    rw [measureReal_def, markedPoissonPredictive,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z)]
    have htop : ∀ᵐ p ∂C.zeroInflatedPrior a,
        markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch p {z} < ∞ := by
      filter_upwards with p
      rw [markedPoissonKernel_apply]
      exact measure_lt_top _ _
    rw [← integral_toReal
      (Kernel.measurable_coe
        (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch)
        (measurableSet_singleton z)).aemeasurable htop]
    apply integral_congr_ae
    filter_upwards with p
    rw [markedPoissonKernel_apply, measureReal_def]
  rw [hreal false, hreal true]
  apply zeroInflated_integral_sub C a κ B ha hκ hsupp
  · apply Integrable.of_bound
      (by
        simpa only [markedPoissonKernel_apply, measureReal_def] using
          (Kernel.measurable_coe
            (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign false)
            (measurableSet_singleton z)).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards with p
    have hle := ENNReal.toReal_mono
      (measure_ne_top (markedPoissonLaw ε a u v C.polarSign false p) _)
      (measure_mono (Set.subset_univ {z}))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, measureReal_def]
    simpa using hle
  · apply Integrable.of_bound
      (by
        simpa only [markedPoissonKernel_apply, measureReal_def] using
          (Kernel.measurable_coe
            (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign true)
            (measurableSet_singleton z)).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards with p
    have hle := ENNReal.toReal_mono
      (measure_ne_top (markedPoissonLaw ε a u v C.polarSign true p) _)
      (measure_mono (Set.subset_univ {z}))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, measureReal_def]
    simpa using hle
  · have hzero := polarSign_zero C a κ B ha hκ hsupp
    simp [markedPoissonLaw, branchMark, hzero]

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp), [the number of independent coordinates](hyp:k), [the supplied input l](hyp:l), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem markedPredictive_real_both_positive_sub_eq_zero
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (k l s t : ℕ) :
    (C.markedPoissonPredictive ε a u v false).real
        {((k + 1, l + 1), (s, t))} -
      (C.markedPoissonPredictive ε a u v true).real
        {((k + 1, l + 1), (s, t))} = 0 := by
  rw [markedPredictive_real_singleton_sub C ε a u v κ B ha hκ hsupp]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hw : C.weight i = 0
  · simp [hw]
  · have hsign : Real.sign (C.weight i) = 1 ∨
        Real.sign (C.weight i) = -1 :=
      (Real.sign_apply_eq_of_ne_zero _ hw).symm
    have hlaw (branch : Bool) :
        markedPoissonLaw ε a u v C.polarSign branch (C.node i) =
          markedPoissonLaw ε a u v
            (fun _ => Real.sign (C.weight i)) branch (C.node i) := by
      unfold markedPoissonLaw
      rw [polarSign_node]
    rw [hlaw false, hlaw true]
    rcases hsign with hs | hs <;> rw [hs] <;>
      simp [markedPoissonLaw, branchMark, prod_real_singleton,
        poissonMeasure_real_singleton, zero_pow (by omega : k + 1 ≠ 0),
        zero_pow (by omega : l + 1 ≠ 0)]

/-- The [stated conclusion](goal) follows from [the evaluation point](hyp:x). -/
theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with hx | hx
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the target function](hyp:f). -/
theorem jordan_integral_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    (∫ p, f p ∂C.positivePrior) - ∫ p, f p ∂C.negativePrior =
      2 * ∑ i, C.weight i * f (C.node i) := by
  classical
  rw [positivePrior, negativePrior,
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, 2 * (C.weight i * f (C.node i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ENNReal.toReal_ofReal
          (mul_nonneg (by norm_num) (le_max_right _ _)),
        ENNReal.toReal_ofReal
          (mul_nonneg (by norm_num) (le_max_right _ _)),
        ← sub_mul, ← mul_sub, max_sub_max_neg]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1). -/
noncomputable instance aggregatePoissonKernel_isMarkovKernel
    (ε a t : ℝ) : IsMarkovKernel (aggregatePoissonKernel ε a t) where
  isProbabilityMeasure p := by
    rw [aggregatePoissonKernel_apply]
    infer_instance

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the source measurable space](hyp:X), [the experiment kernel](hyp:K), [the observed count vector](hyp:z). -/
theorem priorPredictive_real_singleton_sub_jordan
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : Kernel ℝ X) [IsMarkovKernel K] (z : X) :
    (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive C.positivePrior K).real {z} -
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive C.negativePrior K).real {z} =
      2 * ∑ i, C.weight i * (K (C.node i)).real {z} := by
  have hreal (π : Measure ℝ) [IsProbabilityMeasure π] :
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π K).real {z} =
        ∫ p, (K p).real {z} ∂π := by
    rw [measureReal_def,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z)]
    have htop : ∀ᵐ p ∂π, K p {z} < ∞ := by
      filter_upwards with p
      exact measure_lt_top _ _
    rw [← integral_toReal
      (K.measurable_coe (measurableSet_singleton z)).aemeasurable htop]
    rfl
  rw [hreal C.positivePrior, hreal C.negativePrior]
  exact jordan_integral_sub C (fun p => (K p).real {z})

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [positive total intensity](hyp:ht), [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplit_aggregatePredictive_real_target_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (first : Bool) (k s t : ℕ) :
    (palmSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) first ∘ₘ
      aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
        {palmSplitTarget first k s t} -
      (palmSplitKernel
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval) first ∘ₘ
        aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
          {palmSplitTarget first k s t} =
      2 * ∑ i, C.weight i *
        (palmSplitKernel
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval) first ∘ₘ
          aggregatePoissonLaw ε a (u + v) (C.node i)).real
            {palmSplitTarget first k s t} := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  have hcomp (π : Measure ℝ) :
      palmSplitKernel q first ∘ₘ aggregatePoissonPredictive π ε a (u + v) =
        Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π
          (palmSplitKernel q first ∘ₖ aggregatePoissonKernel ε a (u + v)) := by
    unfold aggregatePoissonPredictive
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    rw [Measure.bind_bind (Kernel.aemeasurable _) (Kernel.aemeasurable _)]
    rfl
  change
    (palmSplitKernel q first ∘ₘ
        aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
          {palmSplitTarget first k s t} -
      (palmSplitKernel q first ∘ₘ
        aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
          {palmSplitTarget first k s t} =
      2 * ∑ i, C.weight i *
        (palmSplitKernel q first ∘ₘ
          aggregatePoissonLaw ε a (u + v) (C.node i)).real
            {palmSplitTarget first k s t}
  rw [hcomp C.positivePrior, hcomp C.negativePrior,
    priorPredictive_real_singleton_sub_jordan]
  apply congrArg (fun x : ℝ => 2 * x)
  apply Finset.sum_congr rfl
  intro i hi
  rw [Kernel.comp_apply, aggregatePoissonKernel_apply]

/-- The [stated conclusion](goal) follows from [the evaluation point](hyp:x). -/
theorem abs_mul_sign (x : ℝ) : |x| * Real.sign x = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    ring
  · simp
  · rw [abs_of_pos hx, Real.sign_of_pos hx, mul_one]

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the supplied input hκeq](hyp:hκeq), [positive shift](hyp:ha), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [positive total intensity](hyp:ht), [the compact-support condition](hyp:hsupp), [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem markedPredictive_real_target_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε κ a B u v : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκeq : κ = (1 - 2 * ε) / ε)
    (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (first : Bool) (k s t : ℕ) :
    (C.markedPoissonPredictive ε a u v false).real
        {palmSplitTarget first k s t} -
      (C.markedPoissonPredictive ε a u v true).real
        {palmSplitTarget first k s t} =
      (if first then (-1 : ℝ) else 1) * (u * ε * a / 2) *
        ((palmSplitKernel
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval) first ∘ₘ
          aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
            {palmSplitTarget first k s t} -
          (palmSplitKernel
              (⟨u / (u + v), by
                constructor
                · positivity
                · rw [div_le_one ht]
                  linarith⟩ : unitInterval) first ∘ₘ
            aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
              {palmSplitTarget first k s t}) := by
  have hκpos : 0 < κ := by
    rw [hκeq]
    apply div_pos
    · nlinarith
    · exact hε
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  rw [markedPredictive_real_singleton_sub C ε a u v κ B ha hκpos hsupp,
    palmSplit_aggregatePredictive_real_target_sub C ε a u v hu hv ht]
  calc
    _ = ∑ i, (if first then (-1 : ℝ) else 1) * (u * ε * a) *
        (C.weight i *
          (palmSplitKernel q first ∘ₘ
            aggregatePoissonLaw ε a (u + v) (C.node i)).real
              {palmSplitTarget first k s t}) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hw : C.weight i = 0
      · simp [hw]
      · have hnode := node_mem_support C a κ B hsupp i hw
        have hp : 0 < C.node i :=
          lt_of_lt_of_le (div_pos ha hκpos) hnode.1
        have hpa : 0 < C.node i + a := add_pos hp ha
        have hr : 0 ≤ ε * (C.node i + a) := by positivity
        have hrate : 0 ≤ u * (ε * (C.node i + a)) := mul_nonneg hu hr
        have ha_le : a ≤ κ * C.node i := by
          simpa [mul_comm] using (div_le_iff₀ hκpos).mp hnode.1
        have hκε : κ * ε = 1 - 2 * ε := by
          rw [hκeq]
          field_simp
        have hc : 0 ≤ controlMass ε a (C.node i) := by
          simp [controlMass, treatedMass]
          nlinarith [mul_nonneg hε.le hp.le]
        have hsign : Real.sign (C.weight i) = 1 ∨
            Real.sign (C.weight i) = -1 :=
          (Real.sign_apply_eq_of_ne_zero _ hw).symm
        have hlaw (branch : Bool) :
            markedPoissonLaw ε a u v C.polarSign branch (C.node i) =
              markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) branch (C.node i) := by
          unfold markedPoissonLaw
          rw [polarSign_node]
        rw [hlaw false, hlaw true]
        change |C.weight i| * (a / (C.node i + a)) *
            ((markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) false (C.node i)).real
                  {palmSplitTarget first k s t} -
              (markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) true (C.node i)).real
                  {palmSplitTarget first k s t}) = _
        rw [markedPoissonLaw_real_target_sub ε a u v (C.node i)
          (Real.sign (C.weight i)) hsign first k s t,
          palmSplit_aggregatePoissonLaw_real_target
            ε a u v (C.node i) hu hv ht hr hc first k s t]
        calc
          _ = |C.weight i| *
              (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) *
              ((a / (C.node i + a)) *
                (poissonMeasure (Real.toNNReal
                  (u * (ε * (C.node i + a))))).real {k + 1}) *
              (poissonMeasure (Real.toNNReal
                (v * (ε * (C.node i + a))))).real {s} *
              (poissonMeasure (Real.toNNReal
                ((u + v) * controlMass ε a (C.node i)))).real {t} := by ring
          _ = |C.weight i| *
              (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) *
              ((u * ε * a / (k + 1)) *
                (poissonMeasure (Real.toNNReal
                  (u * (ε * (C.node i + a))))).real {k}) *
              (poissonMeasure (Real.toNNReal
                (v * (ε * (C.node i + a))))).real {s} *
              (poissonMeasure (Real.toNNReal
                ((u + v) * controlMass ε a (C.node i)))).real {t} := by
            rw [poisson_palm ε a u (C.node i) hrate hpa k]
          _ = _ := by
            rw [show |C.weight i| *
                (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) =
                (if first then (-1 : ℝ) else 1) * C.weight i by
              cases first <;> simp [abs_mul_sign]]
            ring
    _ = _ := by
      dsimp [q]
      rw [← Finset.mul_sum]
      ring


end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
