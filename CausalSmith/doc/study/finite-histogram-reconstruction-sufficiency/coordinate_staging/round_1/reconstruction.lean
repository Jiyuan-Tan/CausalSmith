import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction.Kernel
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction.CountLaw

/-!
# Reconstruction of finite ordered samples from histograms

This module states the fixed-total and Poissonized identities obtained by
mixing the parameter-free uniform histogram-fibre reconstruction kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Given [a finite-alphabet probability law](hyp:P) and [a fixed sample
size](hyp:n), the [multinomial histogram law](goal) is the count-vector image
of the ordered iid product law. -/
noncomputable def multinomialHistogramLaw
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) : Measure (X → ℕ) :=
  Measure.map finiteSampleHistogram (Measure.pi fun _ : Fin n ↦ P)

private lemma finiteProductMass_eq_histogramProduct
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) (x : Fin n → X) :
    (∏ i, P {x i}) = ∏ a, P {a} ^ finiteSampleHistogram x a := by
  unfold finiteSampleHistogram
  rw [← Fintype.prod_fiberwise' x (fun a ↦ P {a})]
  congr 1
  funext a
  simp

private lemma finiteProductMass_eq_of_histogram_eq
    {n : ℕ} {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [SigmaFinite P] {x y : Fin n → X}
    (h : finiteSampleHistogram x = finiteSampleHistogram y) :
    (Measure.pi fun _ : Fin n ↦ P) {x} =
      (Measure.pi fun _ : Fin n ↦ P) {y} := by
  rw [Measure.pi_singleton, Measure.pi_singleton,
    finiteProductMass_eq_histogramProduct,
    finiteProductMass_eq_histogramProduct, h]

private lemma finiteSampleHistogram_arrowCongr
    {m n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (h : m = n) (x : Fin n → X) :
    finiteSampleHistogram
        ((Equiv.arrowCongr (finCongr h.symm) (Equiv.refl X)) x) =
      finiteSampleHistogram x := by
  funext a
  unfold finiteSampleHistogram
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (finCongr h) (fun i ↦ by simp)

private lemma measurableSet_finiteSample_singleton
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : FiniteSample X) : MeasurableSet ({s} : Set (FiniteSample X)) := by
  rcases s with ⟨m, z⟩
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change @MeasurableSet (Fin n → X) inferInstance
    ((Sigma.mk (β := fun k => Fin k → X) n) ⁻¹'
      ({⟨m, z⟩} : Set (FiniteSample X)))
  by_cases hn : n = m
  · subst n
    convert measurableSet_singleton z
    ext y
    simp
  · convert MeasurableSet.empty
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false]
    intro h
    exact hn (Sigma.mk.inj_iff.mp h).1

private lemma measurableSet_finiteSampleHistogram_eq
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] (c : X → ℕ) :
    MeasurableSet {s : FiniteSample X | finiteSampleHistogram s.points = c} := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change @MeasurableSet (Fin n → X) inferInstance
    ((Sigma.mk (β := fun k => Fin k → X) n) ⁻¹'
      {s : FiniteSample X | finiteSampleHistogram s.points = c})
  exact Set.Finite.measurableSet (Set.toFinite _)

private lemma measurable_finiteSampleHistogram_local
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] :
    Measurable (fun s : FiniteSample X ↦ finiteSampleHistogram s.points) := by
  apply measurable_to_countable'
  intro c
  exact measurableSet_finiteSampleHistogram_eq c

/-- Given [a finite-alphabet probability law](hyp:P) and [a fixed sample
size](hyp:n), uniformly reconstructing its multinomial histogram [recovers the
embedded ordered iid sample law exactly](goal). -/
theorem multinomialHistogramLaw_comp_reconstruction
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    histogramReconstructionKernel X ∘ₘ multinomialHistogramLaw P n =
      Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P) := by
  classical
  let μ := Measure.pi fun _ : Fin n ↦ P
  apply Measure.ext_of_singleton
  rintro ⟨m, z⟩
  by_cases hmn : m = n
  · subst m
    have hkernel (x : Fin n → X) :
        histogramReconstructionKernel X (finiteSampleHistogram x)
            {fixedSizeEmbed n z} =
          if finiteSampleHistogram x = finiteSampleHistogram z then
            (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹
          else 0 := by
      split_ifs with hx
      · rw [hx]
        have htot : histogramTotal (finiteSampleHistogram z) = n :=
          histogramTotal_finiteSampleHistogram z
        let z' : Fin (histogramTotal (finiteSampleHistogram z)) → X :=
          fun i ↦ z (Fin.cast htot i)
        have hz' : finiteSampleHistogram z' = finiteSampleHistogram z := by
          funext a
          unfold finiteSampleHistogram
          apply Fintype.card_congr
          exact Equiv.subtypeEquiv (finCongr htot) (fun i ↦ by rfl)
        let w : HistogramFiber (finiteSampleHistogram z) := ⟨z', hz'⟩
        have hw := histogramReconstructionKernel_singleton
          (X := X) (finiteSampleHistogram z) w
        have hembed : fixedSizeEmbed (histogramTotal (finiteSampleHistogram z)) w.1 =
            fixedSizeEmbed n z := by
          apply Sigma.ext htot
          apply (Fin.heq_fun_iff htot).2
          intro i
          simp only [w, z', fixedSizeEmbed]
          congr
        rw [hembed] at hw
        exact hw
      · let E : Set (FiniteSample X) :=
          {s | finiteSampleHistogram s.points = finiteSampleHistogram x}
        have hE : MeasurableSet E :=
          measurableSet_finiteSampleHistogram_eq (finiteSampleHistogram x)
        have hEc : histogramReconstructionKernel X (finiteSampleHistogram x) Eᶜ = 0 := by
          rw [measure_compl hE (measure_ne_top _ _),
            histogramReconstructionKernel_histogram_eq]
          simp
        apply measure_mono_null (t := Eᶜ) _ hEc
        intro s hs
        simp only [Set.mem_singleton_iff] at hs
        subst s
        simp only [Set.mem_compl_iff, FiniteSample.points, fixedSizeEmbed]
        change finiteSampleHistogram z ≠ finiteSampleHistogram x
        exact fun h ↦ hx h.symm
    have hmass (x : Fin n → X)
        (hx : finiteSampleHistogram x = finiteSampleHistogram z) :
        μ {x} = μ {z} :=
      finiteProductMass_eq_of_histogram_eq P hx
    rw [Measure.bind_apply (measurableSet_finiteSample_singleton _)
      (histogramReconstructionKernel X).aemeasurable]
    unfold multinomialHistogramLaw
    rw [lintegral_map
      ((histogramReconstructionKernel X).measurable_coe
        (measurableSet_finiteSample_singleton _))
      (measurable_of_countable _), lintegral_fintype]
    change (∑ x, histogramReconstructionKernel X (finiteSampleHistogram x)
      {fixedSizeEmbed n z} * μ {x}) = _
    simp_rw [hkernel]
    rw [Measure.map_apply (measurable_fixedSizeEmbed n)
      (measurableSet_finiteSample_singleton _)]
    have hpre : fixedSizeEmbed n ⁻¹' ({(⟨n, z⟩ : FiniteSample X)} : Set (FiniteSample X)) =
        {z} := by
      ext x
      simp [fixedSizeEmbed]
    rw [hpre]
    let p : (Fin n → X) → Prop := fun x ↦
      finiteSampleHistogram x = finiteSampleHistogram z
    have hsum :
        (∑ x, (if p x then
            (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹
          else 0) * μ {x}) =
          ∑ x ∈ (Finset.univ.filter p),
            (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹ *
              μ {x} := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : p x
      · have hx' : finiteSampleHistogram x = finiteSampleHistogram z := hx
        simp [hx, hx']
      · have hx' : ¬finiteSampleHistogram x = finiteSampleHistogram z := hx
        simp [hx, hx']
    change (∑ x, (if p x then
      (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹
      else 0) * μ {x}) = μ {z}
    rw [hsum]
    have hcard : (Finset.univ.filter p).card =
        Fintype.card (HistogramFiber (finiteSampleHistogram z)) := by
      rw [← Fintype.card_subtype p]
      apply Fintype.card_congr
      let e : (Fin n → X) ≃
          (Fin (histogramTotal (finiteSampleHistogram z)) → X) :=
        Equiv.arrowCongr
          (finCongr (histogramTotal_finiteSampleHistogram z).symm) (Equiv.refl X)
      exact Equiv.subtypeEquiv e (fun x ↦ by
        change p x ↔ finiteSampleHistogram (e x) = finiteSampleHistogram z
        rw [show finiteSampleHistogram (e x) = finiteSampleHistogram x by
          exact finiteSampleHistogram_arrowCongr
            (histogramTotal_finiteSampleHistogram z) x])
    have hconst :
        (∑ x ∈ (Finset.univ.filter p),
            (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹ *
              μ {x}) =
          ∑ _x ∈ (Finset.univ.filter p),
            (Fintype.card (HistogramFiber (finiteSampleHistogram z)) : ℝ≥0∞)⁻¹ *
              μ {z} := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hmass x (Finset.mem_filter.mp hx).2]
    rw [hconst, Finset.sum_const, hcard]
    letI : Nonempty (HistogramFiber (finiteSampleHistogram z)) :=
      histogramFiber_nonempty _
    rw [nsmul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · simpa using Fintype.card_ne_zero
    · exact ENNReal.natCast_ne_top _
  · rw [Measure.bind_apply (measurableSet_finiteSample_singleton _)
      (histogramReconstructionKernel X).aemeasurable]
    unfold multinomialHistogramLaw
    rw [lintegral_map
      ((histogramReconstructionKernel X).measurable_coe
        (measurableSet_finiteSample_singleton _))
      (measurable_of_countable _)]
    have hzero : ∀ x : Fin n → X,
        histogramReconstructionKernel X (finiteSampleHistogram x) {⟨m, z⟩} = 0 := by
      intro x
      let E : Set (FiniteSample X) :=
        {s | finiteSampleHistogram s.points = finiteSampleHistogram x}
      have hE : MeasurableSet E :=
        measurableSet_finiteSampleHistogram_eq (finiteSampleHistogram x)
      have hEc : histogramReconstructionKernel X (finiteSampleHistogram x) Eᶜ = 0 := by
        rw [measure_compl hE (measure_ne_top _ _),
          histogramReconstructionKernel_histogram_eq]
        simp
      apply measure_mono_null (t := Eᶜ) _ hEc
      intro s hs
      simp only [Set.mem_singleton_iff] at hs
      subst s
      simp only [Set.mem_compl_iff, FiniteSample.points]
      intro hz
      apply hmn
      calc
        m = histogramTotal (finiteSampleHistogram z) :=
          (histogramTotal_finiteSampleHistogram z).symm
        _ = histogramTotal (finiteSampleHistogram x) := congrArg histogramTotal hz
        _ = n := histogramTotal_finiteSampleHistogram x
    simp_rw [hzero]
    simp
    rw [Measure.map_apply (measurable_fixedSizeEmbed n)
      (measurableSet_finiteSample_singleton _)]
    have hpre : fixedSizeEmbed n ⁻¹' ({⟨m, z⟩} : Set (FiniteSample X)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hx
      exact hmn (Sigma.mk.inj_iff.mp hx).1.symm
    rw [hpre, measure_empty]

private lemma independentPoissonCountLaw_restrict_histogramTotal_eq
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (N : ℕ) :
    (independentPoissonCountLaw P lambda).restrict
        (histogramTotal ⁻¹' ({N} : Set ℕ)) =
      (poissonMeasure lambda) {N} • multinomialHistogramLaw P N := by
  rw [← finitePoissonSampleLaw_map_histogram P lambda]
  rw [Measure.restrict_map measurable_finiteSampleHistogram_local
    ((measurable_of_countable histogramTotal) (measurableSet_singleton N))]
  have hpre :
      (fun s : FiniteSample X ↦ finiteSampleHistogram s.points) ⁻¹'
          (histogramTotal ⁻¹' ({N} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({N} : Set ℕ) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [histogramTotal_finiteSampleHistogram]
  rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
    Measure.map_smul, Measure.map_map measurable_finiteSampleHistogram_local
      (measurable_fixedSizeEmbed N)]
  rfl

private lemma measure_eq_sum_restrict_finiteSample_count
    {X : Type*} [MeasurableSpace X] (μ : Measure (FiniteSample X)) :
    μ = Measure.sum (fun N ↦
      μ.restrict (FiniteSample.count ⁻¹' ({N} : Set ℕ))) := by
  have hdis : Pairwise (Function.onFun Disjoint
      (fun N : ℕ ↦ (FiniteSample.count : FiniteSample X → ℕ) ⁻¹'
        ({N} : Set ℕ))) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro s hi hj
    apply hij
    simpa using hi.symm.trans hj
  have hcover : ⋃ N : ℕ,
      (FiniteSample.count : FiniteSample X → ℕ) ⁻¹' ({N} : Set ℕ) =
        Set.univ := by
    ext s
    simp
  calc
    μ = μ.restrict Set.univ := by rw [Measure.restrict_univ]
    _ = μ.restrict (⋃ N : ℕ,
        FiniteSample.count ⁻¹' ({N} : Set ℕ)) := by rw [hcover]
    _ = Measure.sum (fun N ↦
        μ.restrict (FiniteSample.count ⁻¹' ({N} : Set ℕ))) := by
      exact Measure.restrict_iUnion hdis
        (fun N ↦ measurable_finiteSample_count (MeasurableSet.singleton N))

private lemma measure_eq_sum_restrict_histogramTotal
    {X : Type*} [Fintype X] [MeasurableSpace X]
    (μ : Measure (X → ℕ)) :
    μ = Measure.sum (fun N ↦
      μ.restrict (histogramTotal ⁻¹' ({N} : Set ℕ))) := by
  have hdis : Pairwise (Function.onFun Disjoint
      (fun N : ℕ ↦ (histogramTotal (X := X)) ⁻¹' ({N} : Set ℕ))) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro c hi hj
    apply hij
    simpa using hi.symm.trans hj
  have hcover : ⋃ N : ℕ,
      (histogramTotal (X := X)) ⁻¹' ({N} : Set ℕ) = Set.univ := by
    ext c
    simp
  calc
    μ = μ.restrict Set.univ := by rw [Measure.restrict_univ]
    _ = μ.restrict (⋃ N : ℕ,
        (histogramTotal (X := X)) ⁻¹' ({N} : Set ℕ)) := by rw [hcover]
    _ = Measure.sum (fun N ↦
        μ.restrict ((histogramTotal (X := X)) ⁻¹' ({N} : Set ℕ))) := by
      exact Measure.restrict_iUnion hdis
        (fun N ↦ (measurable_of_countable histogramTotal)
          (MeasurableSet.singleton N))

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson
intensity](hyp:lambda), passing its independent cell counts through the
parameter-free reconstruction kernel [recovers the ordered finite Poisson
sample law exactly](goal). -/
theorem independentPoissonCountLaw_comp_reconstruction
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) :
    histogramReconstructionKernel X ∘ₘ independentPoissonCountLaw P lambda =
      finitePoissonSampleLaw P lambda := by
  let K := histogramReconstructionKernel X
  let ν := independentPoissonCountLaw P lambda
  let μ := finitePoissonSampleLaw P lambda
  have hpiece (N : ℕ) :
      K ∘ₘ ν.restrict (histogramTotal ⁻¹' ({N} : Set ℕ)) =
        μ.restrict (FiniteSample.count ⁻¹' ({N} : Set ℕ)) := by
    rw [show ν.restrict (histogramTotal ⁻¹' ({N} : Set ℕ)) =
        (poissonMeasure lambda) {N} • multinomialHistogramLaw P N by
      exact independentPoissonCountLaw_restrict_histogramTotal_eq P lambda N,
      Measure.bind_smul, multinomialHistogramLaw_comp_reconstruction,
      show μ.restrict (FiniteSample.count ⁻¹' ({N} : Set ℕ)) =
        (poissonMeasure lambda) {N} •
          Measure.map (fixedSizeEmbed N) (Measure.pi fun _ : Fin N ↦ P) by
        exact finitePoissonSampleLaw_restrict_count_eq P lambda N]
  calc
    K ∘ₘ ν = K ∘ₘ Measure.sum (fun N ↦
        ν.restrict (histogramTotal ⁻¹' ({N} : Set ℕ))) := by
      rw [← measure_eq_sum_restrict_histogramTotal ν]
    _ = Measure.sum (fun N ↦ K ∘ₘ
        ν.restrict (histogramTotal ⁻¹' ({N} : Set ℕ))) := by
      exact Measure.bind_sum _ _ K.aemeasurable
    _ = Measure.sum (fun N ↦
        μ.restrict (FiniteSample.count ⁻¹' ({N} : Set ℕ))) := by
      congr 1
      funext N
      exact hpiece N
    _ = μ := (measure_eq_sum_restrict_finiteSample_count μ).symm

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.HistogramReconstruction
