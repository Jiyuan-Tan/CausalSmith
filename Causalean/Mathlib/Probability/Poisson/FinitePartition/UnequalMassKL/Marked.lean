module
public import Causalean.Mathlib.InformationTheory.KLBind
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL.Count
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Marked Poisson divergence at unequal rates

This module factors a finite marked Poisson law through its count and
fixed-size conditional sample kernel, then applies the KL chain rule at
unequal rates.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL

/-- If two Markov kernel binds record their respective base coordinates, and
the source conditional kernels are almost everywhere absolutely continuous
with respect to the target kernels, their KL is base KL plus the source-base
average of conditional KL. The two base laws may differ. -/
private theorem klDiv_bind_eq_base_add_of_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    [MeasurableSpace.CountableOrCountablyGenerated B Ω]
    (m n : Measure B) [IsFiniteMeasure m] [IsFiniteMeasure n]
    (κ η : Kernel B Ω) [IsMarkovKernel κ] [IsMarkovKernel η]
    (proj : Ω → B) (hproj : Measurable proj)
    (hgraph : MeasurableSet {p : B × Ω | p.1 = proj p.2})
    (hκ_fib : ∀ᵐ b ∂m, (κ b) {ω | proj ω = b}ᶜ = 0)
    (hη_fib : ∀ᵐ b ∂n, (η b) {ω | proj ω = b}ᶜ = 0)
    (hκη : ∀ᵐ b ∂m, κ b ≪ η b) :
    InformationTheory.klDiv (m.bind κ) (n.bind η) =
      InformationTheory.klDiv m n +
        ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m := by
  let g : Ω → B × Ω := fun ω => (proj ω, ω)
  have hg_emb : MeasurableEmbedding g := by
    simpa [g] using
      Causalean.Mathlib.InformationTheory.Measure.measurableEmbedding_base_recording
        (proj := proj) hproj hgraph
  have hκ_map : (m.bind κ).map g = m ⊗ₘ κ := by
    simpa [g] using
      Causalean.Mathlib.InformationTheory.Measure.map_bind_eq_compProd_of_base_recording
        (m := m) (κ := κ) (proj := proj) hproj hκ_fib
  have hη_map : (n.bind η).map g = n ⊗ₘ η := by
    simpa [g] using
      Causalean.Mathlib.InformationTheory.Measure.map_bind_eq_compProd_of_base_recording
        (m := n) (κ := η) (proj := proj) hproj hη_fib
  have hmκ : IsFiniteMeasure (m.bind κ) := by
    rw [← Measure.snd_compProd (μ := m) (κ := κ)]
    infer_instance
  have hnη : IsFiniteMeasure (n.bind η) := by
    rw [← Measure.snd_compProd (μ := n) (κ := η)]
    infer_instance
  calc
    InformationTheory.klDiv (m.bind κ) (n.bind η)
        = InformationTheory.klDiv ((m.bind κ).map g) ((n.bind η).map g) := by
          exact (Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
            (μ := m.bind κ) (ν := n.bind η) (f := g) hg_emb).symm
    _ = InformationTheory.klDiv (m ⊗ₘ κ) (n ⊗ₘ η) := by
      rw [hκ_map, hη_map]
    _ = InformationTheory.klDiv m n +
          InformationTheory.klDiv (m ⊗ₘ κ) (m ⊗ₘ η) :=
      InformationTheory.klDiv_compProd_eq_add m n κ η
    _ = InformationTheory.klDiv m n +
          ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m := by
      rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac hκη]


open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- At each count, the fixed-size sample kernel embeds an independent tuple
of observations into the finite-sample space. -/
private noncomputable def fixedSampleKernel
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] :
    Kernel ℕ (FiniteSample X) where
  toFun n := Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
  measurable' := Measurable.of_discrete

/-- The fixed-size sample kernel has probability fibers at every count. -/
private instance fixedSampleKernel_isMarkov
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] :
    IsMarkovKernel (fixedSampleKernel P) where
  isProbabilityMeasure n := by
    change IsProbabilityMeasure
      (Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P))
    exact Measure.isProbabilityMeasure_map
      (measurable_fixedSizeEmbed n).aemeasurable

/-- Embedding tuples of a given length into the finite-sample space is a
measurable embedding. -/
private theorem measurableEmbedding_fixedSizeEmbed
    {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableEmbedding (fixedSizeEmbed (X := X) n) where
  injective x y h := by simpa [fixedSizeEmbed] using h
  measurable := measurable_fixedSizeEmbed n
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ a, MeasurableSpace.map
        (@Sigma.mk ℕ (fun k ↦ Fin k → X) a) inferInstance]
      (@Sigma.mk ℕ (fun k ↦ Fin k → X) n '' s)
    simp only [MeasurableSpace.measurableSet_iInf]
    intro a
    change MeasurableSet
      ((@Sigma.mk ℕ (fun k ↦ Fin k → X) a) ⁻¹'
        (@Sigma.mk ℕ (fun k ↦ Fin k → X) n '' s))
    by_cases h : a = n
    · subst a
      have hinj : Function.Injective
          (@Sigma.mk ℕ (fun k ↦ Fin k → X) n) := by
        intro x y hxy
        simpa using hxy
      rw [hinj.preimage_image]
      exact hs
    · rw [Set.preimage_image_sigmaMk_of_ne h]
      exact MeasurableSet.empty

/-- The KL divergence of two length-`n` iid tuples is `n` times the KL
divergence of the one-point laws, including the infinite-divergence case. -/
private theorem klDiv_pi_const
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv
        (Measure.pi fun _ : Fin n ↦ P)
        (Measure.pi fun _ : Fin n ↦ Q) =
      (n : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  by_cases hn : n = 0
  · subst n
    have heq : (Measure.pi fun _ : Fin 0 ↦ P) =
        (Measure.pi fun _ : Fin 0 ↦ Q) := by
      apply Measure.pi_eq
      intro s hs
      simp
    rw [heq]
    simp
  by_cases htop : InformationTheory.klDiv P Q = ∞
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i : Fin n := ⟨0, hnpos⟩
    have hle := InformationTheory.klDiv_map_le (Measure.pi fun _ : Fin n ↦ P)
      (Measure.pi fun _ : Fin n ↦ Q) (measurable_pi_apply i)
    rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n ↦ Q) i).map_eq, htop] at hle
    have hpi : InformationTheory.klDiv
        (Measure.pi fun _ : Fin n ↦ P)
        (Measure.pi fun _ : Fin n ↦ Q) = ∞ := top_unique hle
    rw [hpi, htop]
    exact (ENNReal.mul_top (by positivity)).symm
  · obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp htop
    have htensor := Causalean.Mathlib.InformationTheory.productKL_tensorization
      n P Q hac hint
    apply (ENNReal.toReal_eq_toReal_iff' htensor.product_ne_top ?_).mp
    · simpa [ENNReal.toReal_mul] using
        Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
          n P Q hac hint
    · exact ENNReal.mul_ne_top (by simp) htop

/-- The finite Poisson sample law is the bind of its count law with the
fixed-size sample kernel. -/
private theorem finitePoissonSampleLaw_eq_bind_fixedSampleKernel
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (r : ℝ≥0) :
    finitePoissonSampleLaw P r =
      (poissonMeasure r).bind (fixedSampleKernel P) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_countable']
  symm
  calc
    ∑' n : ℕ, (fixedSampleKernel P n) s * poissonMeasure r {n}
        = ∑' n : ℕ,
            ((finitePoissonSampleLaw P r).restrict
              (FiniteSample.count ⁻¹' ({n} : Set ℕ))) s := by
          congr 1
          funext n
          rw [finitePoissonSampleLaw_restrict_count_eq, Measure.smul_apply]
          simp only [smul_eq_mul]
          exact mul_comm _ _
    _ = finitePoissonSampleLaw P r s := by
      rw [← Measure.sum_apply _ hs, ← Measure.restrict_iUnion]
      · rw [show (⋃ n : ℕ, FiniteSample.count ⁻¹' ({n} : Set ℕ)) = Set.univ by
          ext x
          simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_univ, iff_true]
          exact ⟨x.count, rfl⟩, Measure.restrict_univ]
      · intro i j hij
        exact (Set.disjoint_singleton.mpr hij).preimage FiniteSample.count
      · intro n
        exact measurable_finiteSample_count
          (MeasurableSet.singleton n)

/-- The fixed-size sample kernel has KL equal to sample size times the KL
of one observation, including singular observation laws. -/
private theorem klDiv_fixedSampleKernel
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) :
    InformationTheory.klDiv (fixedSampleKernel P n) (fixedSampleKernel Q n) =
      (n : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  change InformationTheory.klDiv
      (Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P))
      (Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ Q)) = _
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
    (measurableEmbedding_fixedSizeEmbed n)]
  exact klDiv_pi_const n P Q

/-- A fixed-size kernel gives zero mass to samples with any other count. -/
private theorem fixedSampleKernel_count_fibre
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    fixedSampleKernel P n {s | s.count = n}ᶜ = 0 := by
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
    {s | s.count = n}ᶜ = 0
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P)
    (FiniteSample.count ⁻¹' ({n} : Set ℕ))ᶜ = 0
  rw [Measure.map_apply (measurable_fixedSizeEmbed n)
    ((measurable_finiteSample_count (MeasurableSet.singleton n)).compl)]
  have hpre : fixedSizeEmbed n ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (Set.univ : Set (Fin n → X)) := by
    ext x
    simp [fixedSizeEmbed, FiniteSample.count]
  rw [Set.preimage_compl, hpre]
  simp

/-- Absolute continuity of one-point laws passes to each fixed-size sample
kernel, including the empty sample. -/
private theorem fixedSampleKernel_ac
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) :
    fixedSampleKernel P n ≪ fixedSampleKernel Q n := by
  change Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ P) ≪
    Measure.map (fixedSizeEmbed n) (Measure.pi fun _ : Fin n ↦ Q)
  exact (Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
    P Q hPQ n).map (measurable_fixedSizeEmbed n)

/-- Appending the same independent real mark law preserves the KL
divergence between two observation probability laws. -/
private theorem klDiv_prod_common_mark
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] :
    InformationTheory.klDiv (P.prod R) (Q.prod R) =
      InformationTheory.klDiv P Q := by
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact InformationTheory.klDiv_compProd_left P Q (Kernel.const X R)


open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- When the point law is absolutely continuous, the divergence between
marked Poisson sample laws splits into the count divergence and source-rate
times point-law divergence, even for different count rates. -/
private theorem klDiv_finiteMarkedPoissonSampleLaw_of_ac_unequal
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (r s : ℝ≥0)
    (hPQ : P ≪ Q) :
    InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw P R r)
        (finiteMarkedPoissonSampleLaw Q R s) =
      InformationTheory.klDiv (poissonMeasure r) (poissonMeasure s) +
        (r : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  have hprod : P.prod R ≪ Q.prod R := hPQ.prod .rfl
  unfold finiteMarkedPoissonSampleLaw
  rw [finitePoissonSampleLaw_eq_bind_fixedSampleKernel,
    finitePoissonSampleLaw_eq_bind_fixedSampleKernel]
  rw [klDiv_bind_eq_base_add_of_recording
    (poissonMeasure r) (poissonMeasure s)
    (fixedSampleKernel (P.prod R)) (fixedSampleKernel (Q.prod R))
    FiniteSample.count measurable_finiteSample_count
    ((measurable_fst.eq (measurable_finiteSample_count.comp measurable_snd)).setOf)
    (Filter.Eventually.of_forall (fixedSampleKernel_count_fibre (P.prod R)))
    (Filter.Eventually.of_forall (fixedSampleKernel_count_fibre (Q.prod R)))
    (Filter.Eventually.of_forall (fixedSampleKernel_ac (P.prod R) (Q.prod R) hprod))]
  simp_rw [klDiv_fixedSampleKernel, klDiv_prod_common_mark P Q R]
  rw [lintegral_mul_const _ (by fun_prop), poisson_lintegral_count]

/-- A positive-rate marked Poisson source cannot be absolutely continuous
with respect to a marked Poisson target when its one-point law is singular
with respect to the target one-point law. The target rate may be zero. -/
private theorem finiteMarkedPoissonSampleLaw_not_ac_of_not_point_ac
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (r s : ℝ≥0)
    (hr : r ≠ 0) (hPQ : ¬ P ≪ Q) :
    ¬ finiteMarkedPoissonSampleLaw P R r ≪
      finiteMarkedPoissonSampleLaw Q R s := by
  intro hfull
  let c : ℝ≥0∞ := poissonMeasure r ({1} : Set ℕ)
  have hc : c ≠ 0 := by
    change poissonMeasure r ({1} : Set ℕ) ≠ 0
    rw [poissonMeasure_singleton_eq_poissonPMF r 1]
    change ENNReal.ofReal (poissonPMFReal r 1) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (poissonPMFReal_pos (pos_of_ne_zero hr)))
  have hrest := hfull.restrict
    (FiniteSample.count ⁻¹' ({1} : Set ℕ))
  unfold finiteMarkedPoissonSampleLaw at hrest
  rw [finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq] at hrest
  have hmaps :
      Measure.map (fixedSizeEmbed 1)
          (Measure.pi fun _ : Fin 1 ↦ P.prod R) ≪
        Measure.map (fixedSizeEmbed 1)
          (Measure.pi fun _ : Fin 1 ↦ Q.prod R) := by
    exact (Measure.absolutelyContinuous_smul hc).trans <|
      hrest.trans Measure.smul_absolutelyContinuous
  have hpi : (Measure.pi fun _ : Fin 1 ↦ P.prod R) ≪
      (Measure.pi fun _ : Fin 1 ↦ Q.prod R) := by
    let f := fixedSizeEmbed (X := X × ℝ) 1
    have hf := measurableEmbedding_fixedSizeEmbed (X := X × ℝ) 1
    refine Measure.AbsolutelyContinuous.mk ?_
    intro u hu hqu
    have himage : MeasurableSet (f '' u) := hf.measurableSet_image' hu
    have hzero : (Measure.map f (Measure.pi fun _ : Fin 1 ↦ Q.prod R)) (f '' u) = 0 := by
      rw [hf.map_apply _ (f '' u), hf.injective.preimage_image]
      exact hqu
    have := hmaps hzero
    rwa [hf.map_apply _ (f '' u), hf.injective.preimage_image] at this
  have hprod := hpi.map (measurable_pi_apply (0 : Fin 1))
  rw [(measurePreserving_eval (fun _ : Fin 1 ↦ P.prod R) (0 : Fin 1)).map_eq,
    (measurePreserving_eval (fun _ : Fin 1 ↦ Q.prod R) (0 : Fin 1)).map_eq] at hprod
  have hfst := hprod.map measurable_fst
  exact hPQ (by simpa [Measure.map_fst_prod, measure_univ] using hfst)

/-- A zero-rate marked Poisson source has only the empty sample, so its KL
against any target marked Poisson sample law is exactly the count-law KL. -/
private theorem klDiv_finiteMarkedPoissonSampleLaw_zero_left
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (s : ℝ≥0) :
    InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw P R 0)
        (finiteMarkedPoissonSampleLaw Q R s) =
      InformationTheory.klDiv (poissonMeasure 0) (poissonMeasure s) := by
  have heq : finiteMarkedPoissonSampleLaw P R 0 =
      finiteMarkedPoissonSampleLaw Q R 0 := by
    unfold finiteMarkedPoissonSampleLaw
    rw [finitePoissonSampleLaw_eq_bind_fixedSampleKernel,
      finitePoissonSampleLaw_eq_bind_fixedSampleKernel,
      poissonMeasure_zero_eq_dirac]
    rw [Measure.dirac_bind (Measurable.of_discrete) 0,
      Measure.dirac_bind (Measurable.of_discrete) 0]
    change Measure.map (fixedSizeEmbed 0) (Measure.pi fun _ : Fin 0 ↦ P.prod R) =
      Measure.map (fixedSizeEmbed 0) (Measure.pi fun _ : Fin 0 ↦ Q.prod R)
    have hpi : (Measure.pi fun _ : Fin 0 ↦ P.prod R) =
        (Measure.pi fun _ : Fin 0 ↦ Q.prod R) := by
      apply Measure.pi_eq
      intro u hu
      simp
    rw [hpi]
  rw [heq]
  simpa using
    klDiv_finiteMarkedPoissonSampleLaw_of_ac_unequal Q Q R 0 s (by rfl)

/-- On [a standard Borel point space](hyp:X), [two point probability laws](hyp:P,Q),
[a shared real mark law](hyp:R), and [two nonnegative count rates](hyp:r,s) imply that
[the extended-real KL divergence between the two finite marked Poisson sample laws equals
the KL divergence between the two Poisson count laws plus the first (source) rate times
the KL divergence between the point laws](goal). -/
theorem klDiv_finiteMarkedPoissonSampleLaw_unequal
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] (r s : ℝ≥0) :
    InformationTheory.klDiv
        (finiteMarkedPoissonSampleLaw P R r)
        (finiteMarkedPoissonSampleLaw Q R s) =
      InformationTheory.klDiv (poissonMeasure r) (poissonMeasure s) +
        (r : ℝ≥0∞) * InformationTheory.klDiv P Q := by
  by_cases hPQ : P ≪ Q
  · exact klDiv_finiteMarkedPoissonSampleLaw_of_ac_unequal P Q R r s hPQ
  by_cases hr : r = 0
  · subst r
    rw [klDiv_finiteMarkedPoissonSampleLaw_zero_left]
    simp
  rw [InformationTheory.klDiv_of_not_ac
      (finiteMarkedPoissonSampleLaw_not_ac_of_not_point_ac P Q R r s hr hPQ),
    InformationTheory.klDiv_of_not_ac hPQ]
  have hr' : (r : ℝ≥0∞) ≠ 0 := by simpa using hr
  simp [ENNReal.mul_top hr']

end Causalean.Mathlib.Probability.Poisson.FinitePartition.UnequalMassKL
