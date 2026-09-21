module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessCancellation
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Explicit-witness density algebra

This file isolates the pointwise cancellations that turn the sparse and
cancellation witness expectations into the low-dimensional integrals used by
the certificate proof.
-/

public section

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: integral_fin_three_pi_eq_iterated
/-- Fubini's theorem for a three-coordinate product measure, written in the
explicit coordinate order used by the witness calculations.  Given [the stated inputs and conditions](hyp:hf), [the stated conclusion](goal) follows. -/
lemma integral_fin_three_pi_eq_iterated (μ : Measure ℝ) [SigmaFinite μ]
    (f : (Fin 3 → ℝ) → ℝ) (hf : Integrable f (Measure.pi fun _ : Fin 3 => μ)) :
    (∫ v, f v ∂Measure.pi fun _ : Fin 3 => μ) =
      ∫ x, (∫ y, (∫ z, f ![x, y, z] ∂μ) ∂μ) ∂μ := by
  let e3 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he3 := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0).symm
  have hf3 : Integrable (f ∘ e3.symm) (μ.prod (Measure.pi fun _ : Fin 2 => μ)) :=
    (he3.integrable_comp_emb e3.symm.measurableEmbedding).2 hf
  rw [← he3.integral_comp e3.symm.measurableEmbedding]
  have hf3' := hf3
  change Integrable
    (fun z => f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm z))
    (μ.prod (Measure.pi fun _ : Fin 2 => μ)) at hf3'
  rw [integral_prod _ hf3']
  apply integral_congr_ae
  filter_upwards [hf3.prod_right_ae] with x hfx
  let e2 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  have he2 := (measurePreserving_piFinSuccAbove (fun _ : Fin 2 => μ) 0).symm
  have hf2 : Integrable ((fun v => f (e3.symm (x, v))) ∘ e2.symm)
      (μ.prod (Measure.pi fun _ : Fin 1 => μ)) :=
    (he2.integrable_comp_emb e2.symm.measurableEmbedding).2 hfx
  rw [← he2.integral_comp e2.symm.measurableEmbedding]
  have hf2' := hf2
  change Integrable (fun z => f (e3.symm (x, e2.symm z)))
    (μ.prod (Measure.pi fun _ : Fin 1 => μ)) at hf2'
  rw [integral_prod _ hf2']
  simp only [e3, e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero]
  apply integral_congr_ae
  filter_upwards [hf2'.prod_right_ae] with y hfy
  let e1 := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he1 := (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm
  rw [← he1.integral_comp e1.symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  funext i
  fin_cases i <;> rfl

-- @node: sparse_observationalDensity_mul_ratio_sq
/-- In the sparse observational law, one child-density factor cancels from the
square of the explicit child ratio.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma sparse_observationalDensity_mul_ratio_sq (s : SignVector 3)
    (v : LatentState 3) (hv : v ∈ latentCube 3) :
    observationalDensity (sparseWitness s) v *
        (((sparseWitness s).q 1 (v 1) / (sparseWitness s).p 1 v) ^ 2) =
      ((sparseWitness s).q 1 (v 1)) ^ 2 / (sparseWitness s).p 1 v := by
  have hp : (sparseWitness s).p 1 v ≠ 0 :=
    ne_of_gt ((sparseWitness_positive_normalized_smooth s).1 1 v hv)
  simp only [observationalDensity]
  simp [sparseWitness, sparseP]
  field_simp

-- @node: sparse_parentInterventionalDensity_mul_ratio_sq
/-- Under the sparse parent intervention, the same cancellation leaves the
parent tilt multiplying the reduced child integrand.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma sparse_parentInterventionalDensity_mul_ratio_sq (s : SignVector 3)
    (v : LatentState 3) (hv : v ∈ latentCube 3) :
    interventionalDensity (sparseWitness s) 0 v *
        (((sparseWitness s).q 1 (v 1) / (sparseWitness s).p 1 v) ^ 2) =
      (sparseWitness s).q 0 (v 0) *
        (((sparseWitness s).q 1 (v 1)) ^ 2 / (sparseWitness s).p 1 v) := by
  have hp : (sparseWitness s).p 1 v ≠ 0 :=
    ne_of_gt ((sparseWitness_positive_normalized_smooth s).1 1 v hv)
  simp only [interventionalDensity]
  simp [sparseWitness, sparseP]
  field_simp

-- @node: cancellation_density_difference_mul_test
/-- The cancellation witness's parent-interventional minus observational test
integrand factors into the parent tilt and the child test integrand.  [the stated conclusion](goal) follows. -/
lemma cancellation_density_difference_mul_test (s : SignVector 3)
    (v : LatentState 3) (psi : ℝ → ℝ) :
    (interventionalDensity (cancellationWitness s) 0 v -
        observationalDensity (cancellationWitness s) v) *
        psi ((cancellationWitness s).q 1 (v 1) /
          (cancellationWitness s).p 1 v) =
      ((cancellationWitness s).q 0 (v 0) - 1) *
        ((cancellationWitness s).p 1 v *
          psi ((cancellationWitness s).q 1 (v 1) /
            (cancellationWitness s).p 1 v)) := by
  simp only [interventionalDensity, observationalDensity]
  simp [cancellationWitness, cancellationP]
  ring

-- @node: cancellation_factored_test_eq_reflected_integrand
/-- Expanding the cancellation witness identifies its factored density
difference with the reflected two-coordinate integrand from the FTC argument.  [the stated conclusion](goal) follows. -/
lemma cancellation_factored_test_eq_reflected_integrand (s : SignVector 3)
    (v : LatentState 3) (psi : ℝ → ℝ) :
    ((cancellationWitness s).q 0 (v 0) - 1) *
        ((cancellationWitness s).p 1 v *
          psi ((cancellationWitness s).q 1 (v 1) /
            (cancellationWitness s).p 1 v)) =
      (exponentialInterventionDensity (reflectedCoordinate s 0 (v 0)) - 1) *
        ((1 + (1 / 10 : ℝ) *
            cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (reflectedCoordinate s 1 (v 1))) *
          psi (exponentialInterventionDensity (reflectedCoordinate s 1 (v 1)) /
            (1 + (1 / 10 : ℝ) *
              cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (reflectedCoordinate s 1 (v 1))))) := by
  simp [cancellationWitness, sparseQ, cancellationP]

-- @node: cancellation_density_difference_eq_reflected_integrand
/-- The full density difference against a ratio-law test function is exactly
the reflected two-coordinate cancellation integrand.  [the stated conclusion](goal) follows. -/
lemma cancellation_density_difference_eq_reflected_integrand (s : SignVector 3)
    (v : LatentState 3) (psi : ℝ → ℝ) :
    (interventionalDensity (cancellationWitness s) 0 v -
        observationalDensity (cancellationWitness s) v) *
        psi ((cancellationWitness s).q 1 (v 1) /
          (cancellationWitness s).p 1 v) =
      (exponentialInterventionDensity (reflectedCoordinate s 0 (v 0)) - 1) *
        ((1 + (1 / 10 : ℝ) *
            cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (reflectedCoordinate s 1 (v 1))) *
          psi (exponentialInterventionDensity (reflectedCoordinate s 1 (v 1)) /
            (1 + (1 / 10 : ℝ) *
              cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (reflectedCoordinate s 1 (v 1))))) := by
  rw [cancellation_density_difference_mul_test,
    cancellation_factored_test_eq_reflected_integrand]

-- @node: cancellation_reflected_iterated_test_integral_zero
/-- Coordinate reflections preserve the complete cancellation integral, so it
vanishes for every prescribed sign vector.  Given [the stated inputs and conditions](hyp:hpsi), [the stated conclusion](goal) follows. -/
lemma cancellation_reflected_iterated_test_integral_zero (s : SignVector 3)
    (psi : ℝ → ℝ) (hpsi : Continuous psi) :
    ∫ y in Set.Icc (0 : ℝ) 1,
      ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) *
          ((1 + (1 / 10 : ℝ) *
              cancellationPrimitive (reflectedCoordinate s 0 x) *
              centeredCoordinate (reflectedCoordinate s 1 y)) *
            psi (exponentialInterventionDensity (reflectedCoordinate s 1 y) /
              (1 + (1 / 10 : ℝ) *
                cancellationPrimitive (reflectedCoordinate s 0 x) *
                centeredCoordinate (reflectedCoordinate s 1 y)))) = 0 := by
  let J : ℝ → ℝ → ℝ := fun x y =>
    (exponentialInterventionDensity x - 1) *
      ((1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y) *
        psi (exponentialInterventionDensity y /
          (1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y)))
  change (∫ y in Set.Icc (0 : ℝ) 1, ∫ x in Set.Icc (0 : ℝ) 1,
    J (reflectedCoordinate s 0 x) (reflectedCoordinate s 1 y)) = 0
  calc
    _ = ∫ y in Set.Icc (0 : ℝ) 1, ∫ x in Set.Icc (0 : ℝ) 1,
        J x (reflectedCoordinate s 1 y) := by
      apply integral_congr_ae
      filter_upwards with y
      exact integral_reflectedCoordinate s 0
        (fun x => J x (reflectedCoordinate s 1 y))
    _ = ∫ y in Set.Icc (0 : ℝ) 1, ∫ x in Set.Icc (0 : ℝ) 1, J x y :=
      integral_reflectedCoordinate s 1
        (fun y => ∫ x in Set.Icc (0 : ℝ) 1, J x y)
    _ = 0 := cancellation_iterated_test_integral_zero psi hpsi

-- @node: measurable_sparseQ
/-- The [reflected exponential intervention slots are globally measurable](goal). -/
@[fun_prop] lemma measurable_sparseQ (s : SignVector 3) (i : Fin 3) :
    Measurable (sparseQ s i) := by
  rcases s.signed i with hi | hi
  · unfold sparseQ exponentialInterventionDensity reflectedCoordinate reflect
    rw [hi]
    norm_num
    fun_prop
  · unfold sparseQ exponentialInterventionDensity reflectedCoordinate reflect
    rw [hi]
    simp only [if_pos]
    fun_prop

-- @node: measurable_cancellationP
/-- [Every cancellation-witness observational mechanism slot is globally measurable](goal). -/
@[fun_prop] lemma measurable_cancellationP (s : SignVector 3) (i : Fin 3) :
    Measurable (cancellationP s i) := by
  fin_cases i
  · change Measurable (fun _ : LatentState 3 => (1 : ℝ))
    fun_prop
  · rcases s.signed 0 with h0 | h0 <;>
      rcases s.signed 1 with h1 | h1 <;>
      change Measurable (fun v : LatentState 3 => 1 + (1 / 10 : ℝ) *
        cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) <;>
      simp [cancellationPrimitive, centeredCoordinate, reflectedCoordinate, reflect, h0, h1,
        show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
  · change Measurable (fun _ : LatentState 3 => (1 : ℝ))
    fun_prop

-- @node: measurable_cancellationWitness_observationalDensity
/-- The [cancellation witness's observational joint density is globally measurable](goal). -/
@[fun_prop] lemma measurable_cancellationWitness_observationalDensity (s : SignVector 3) :
    Measurable (observationalDensity (cancellationWitness s)) := by
  unfold observationalDensity
  apply Finset.measurable_prod
  intro i _
  exact measurable_cancellationP s i

-- @node: measurable_cancellationWitness_interventionalDensity
/-- [Every cancellation-witness interventional joint density is globally measurable](goal). -/
@[fun_prop] lemma measurable_cancellationWitness_interventionalDensity
    (s : SignVector 3) (j : Fin 3) :
    Measurable (interventionalDensity (cancellationWitness s) j) := by
  unfold interventionalDensity
  apply (measurable_sparseQ s j).comp (measurable_pi_apply j) |>.mul
  apply Finset.measurable_prod
  intro i _
  exact measurable_cancellationP s i

-- @node: measurableSet_latentCube
/-- The finite latent unit cube is measurable.  [the stated conclusion](goal) follows. -/
lemma measurableSet_latentCube (n : ℕ) : MeasurableSet (latentCube n) := by
  rw [latentCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

-- @node: cancellationWitness_ratioLaws_eq
/-- The cancellation witness has exactly the same child-ratio law before and
after intervening on its parent.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_ratioLaws_eq (s : SignVector 3) :
    let W := canonicalObservedWorld threeNodeDAG (cancellationWitness s)
      (Equiv.refl (Fin 3))
    observationalRatioLaw W 1 = interventionalRatioLaw W 0 1 := by
  dsimp only
  let θ := cancellationWitness s
  let W := canonicalObservedWorld threeNodeDAG θ (Equiv.refl (Fin 3))
  have hpos : PositiveNormalizedSmoothMechanisms threeNodeDAG θ :=
    cancellationWitness_positive_normalized_smooth s
  letI : IsProbabilityMeasure (observationalLaw θ) :=
    observationalLaw_isProbabilityMeasure hpos
  letI : IsProbabilityMeasure (interventionalLaw θ ((Equiv.refl (Fin 3)) 0)) :=
    interventionalLaw_isProbabilityMeasure W hpos 0
  letI : IsFiniteMeasure (W.law 0) := by
    change IsFiniteMeasure (observationalLaw θ)
    infer_instance
  letI : IsFiniteMeasure (W.law (Fin.succ 0)) := by
    change IsFiniteMeasure (interventionalLaw θ ((Equiv.refl (Fin 3)) 0))
    infer_instance
  have hratio : Measurable (fun v : LatentState 3 =>
      θ.q ((Equiv.refl (Fin 3)) 1) (v ((Equiv.refl (Fin 3)) 1)) /
        θ.p ((Equiv.refl (Fin 3)) 1) v) := by
    dsimp only [θ]
    change Measurable ((sparseQ s 1 ∘ fun v : LatentState 3 => v 1) /
      cancellationP s 1)
    exact ((measurable_sparseQ s 1).comp (measurable_pi_apply 1)).div
      (measurable_cancellationP s 1)
  apply ratioLaws_eq_of_boundedContinuous_integrals_eq W 0 1
  intro ψ
  rw [canonical_observationalRatioLaw_eq_mechanismRatio_map hpos (Equiv.refl (Fin 3)) 1,
    canonical_interventionalRatioLaw_eq_mechanismRatio_map hpos (Equiv.refl (Fin 3)) 0 1]
  rw [MeasureTheory.integral_map]
  · rw [MeasureTheory.integral_map]
    · simp only [Equiv.refl_apply]
      let ratio : LatentState 3 → ℝ := fun v => θ.q 1 (v 1) / θ.p 1 v
      let μ : Measure (LatentState 3) := volume.restrict (latentCube 3)
      have hobs : (∫ v, ψ (ratio v) ∂observationalLaw θ) =
          ∫ v, observationalDensity θ v * ψ (ratio v) ∂μ := by
        unfold observationalLaw
        rw [integral_withDensity_eq_integral_toReal_smul]
        · apply integral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_latentCube 3)] with v hv
          rw [ENNReal.toReal_ofReal (le_of_lt (by
            unfold observationalDensity
            exact Finset.prod_pos fun i _ => hpos.1 i v hv))]
          rfl
        · exact (measurable_cancellationWitness_observationalDensity s).ennreal_ofReal
        · filter_upwards with v
          exact ENNReal.ofReal_lt_top
      have hint : (∫ v, ψ (ratio v) ∂interventionalLaw θ 0) =
          ∫ v, interventionalDensity θ 0 v * ψ (ratio v) ∂μ := by
        unfold interventionalLaw
        rw [integral_withDensity_eq_integral_toReal_smul]
        · apply integral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_latentCube 3)] with v hv
          rw [ENNReal.toReal_ofReal (le_of_lt (by
            unfold interventionalDensity
            exact mul_pos (hpos.2.1 0 (v 0) (hv 0 (Set.mem_univ 0)))
              (Finset.prod_pos fun i _ => hpos.1 i v hv)))]
          rfl
        · exact (measurable_cancellationWitness_interventionalDensity s 0).ennreal_ofReal
        · filter_upwards with v
          exact ENNReal.ofReal_lt_top
      rw [hobs, hint]
      have hcubeCompact : IsCompact (latentCube 3) := by
        rw [latentCube]
        exact isCompact_univ_pi fun _ => isCompact_Icc
      have hratioCont : ContinuousOn ratio (latentCube 3) := by
        apply ((hpos.2.2.2.1 1).continuousOn.comp
          ((continuous_apply 1).continuousOn)
          (fun (v : LatentState 3) (hv : v ∈ latentCube 3) =>
            hv 1 (Set.mem_univ 1))).div
          ((hpos.2.2.1 1).continuousOn)
        intro v hv
        exact ne_of_gt (hpos.1 1 v hv)
      have hobsDensityCont : ContinuousOn (observationalDensity θ) (latentCube 3) := by
        unfold observationalDensity
        exact continuousOn_finset_prod _ fun i _ => (hpos.2.2.1 i).continuousOn
      have hintDensityCont : ContinuousOn (interventionalDensity θ 0) (latentCube 3) := by
        unfold interventionalDensity
        apply ((hpos.2.2.2.1 0).continuousOn.comp
          ((continuous_apply 0).continuousOn)
          (fun (v : LatentState 3) (hv : v ∈ latentCube 3) =>
            hv 0 (Set.mem_univ 0))).mul
        exact continuousOn_finset_prod _ fun i _ => (hpos.2.2.1 i).continuousOn
      have hψratioCont : ContinuousOn (fun v => ψ (ratio v)) (latentCube 3) :=
        ψ.continuous.continuousOn.comp hratioCont (fun _ _ => Set.mem_univ _)
      have hobsInt : Integrable
          (fun v => observationalDensity θ v * ψ (ratio v)) μ := by
        dsimp only [μ]
        exact (hobsDensityCont.mul hψratioCont).integrableOn_compact hcubeCompact
      have hintInt : Integrable
          (fun v => interventionalDensity θ 0 v * ψ (ratio v)) μ := by
        dsimp only [μ]
        exact (hintDensityCont.mul hψratioCont).integrableOn_compact hcubeCompact
      rw [eq_comm, ← sub_eq_zero, ← integral_sub hintInt hobsInt]
      let f : LatentState 3 → ℝ := fun v =>
        (exponentialInterventionDensity (reflectedCoordinate s 0 (v 0)) - 1) *
          ((1 + (1 / 10 : ℝ) *
              cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (reflectedCoordinate s 1 (v 1))) *
            ψ (exponentialInterventionDensity (reflectedCoordinate s 1 (v 1)) /
              (1 + (1 / 10 : ℝ) *
                cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
                centeredCoordinate (reflectedCoordinate s 1 (v 1)))))
      have hdiff : (fun v => interventionalDensity θ 0 v * ψ (ratio v) -
          observationalDensity θ v * ψ (ratio v)) =ᵐ[μ] f := by
        filter_upwards with v
        dsimp only [θ, ratio, f]
        rw [← cancellation_density_difference_eq_reflected_integrand s v ψ]
        ring
      rw [integral_congr_ae hdiff]
      have hμ : μ = Measure.pi (fun _ : Fin 3 => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        dsimp only [μ]
        change volume.restrict (Set.univ.pi fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) = _
        rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
      have hf : Integrable f
          (Measure.pi (fun _ : Fin 3 => volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        rw [← hμ]
        exact (hintInt.sub hobsInt).congr hdiff
      let J : ℝ → ℝ → ℝ := fun x y =>
        (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) *
          ((1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x) *
              centeredCoordinate (reflectedCoordinate s 1 y)) *
            ψ (exponentialInterventionDensity (reflectedCoordinate s 1 y) /
              (1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x) *
                centeredCoordinate (reflectedCoordinate s 1 y))))
      let embed : ℝ × ℝ → LatentState 3 := fun z => ![z.1, z.2, 0]
      have hembedCont : Continuous embed := by
        fun_prop
      have hembedCube : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          embed z ∈ latentCube 3 := by
        intro z hz i _
        fin_cases i
        · simpa [embed] using hz.1
        · simpa [embed] using hz.2
        · simp [embed]
      have hdiffCont : ContinuousOn (fun v =>
          interventionalDensity θ 0 v * ψ (ratio v) -
            observationalDensity θ v * ψ (ratio v)) (latentCube 3) :=
        (hintDensityCont.mul hψratioCont).sub (hobsDensityCont.mul hψratioCont)
      have hJCont : ContinuousOn (Function.uncurry J)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
        apply (hdiffCont.comp hembedCont.continuousOn hembedCube).congr
        intro z hz
        dsimp only [Function.uncurry, J, embed, θ, ratio]
        simp only [Function.comp_apply]
        rw [← sub_mul,
          cancellation_density_difference_eq_reflected_integrand s ![z.1, z.2, 0] ψ]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hJInt : Integrable (Function.uncurry J)
          ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        rw [Measure.prod_restrict]
        exact hJCont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hunit : (volume.restrict (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
        simp [Measure.real, Real.volume_Icc]
      rw [hμ, integral_fin_three_pi_eq_iterated _ f hf]
      dsimp only [f]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, integral_const,
        hunit, one_smul]
      change (∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) 1, J x y) = 0
      rw [MeasureTheory.integral_integral_swap hJInt]
      exact cancellation_reflected_iterated_test_integral_zero s ψ ψ.continuous
    · exact hratio.aemeasurable
    · exact ψ.continuous.measurable.aestronglyMeasurable
  · exact hratio.aemeasurable
  · exact ψ.continuous.measurable.aestronglyMeasurable

-- @node: cancellationWitness_populationDiscrepancy_eq_zero
/-- Exact cancellation of the ratio laws makes the cancellation witness's
Gaussian population discrepancy vanish.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_populationDiscrepancy_eq_zero (s : SignVector 3) :
    let W := canonicalObservedWorld threeNodeDAG (cancellationWitness s)
      (Equiv.refl (Fin 3))
    populationDiscrepancy gaussianFeatureMap W 0 1 = 0 := by
  dsimp only
  apply populationDiscrepancy_eq_zero_of_ratioLaws_eq
  exact cancellationWitness_ratioLaws_eq s

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
