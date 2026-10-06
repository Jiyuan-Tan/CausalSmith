module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Channels
public import Causalean.Stat.Privacy.Staircase.Information
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Kernel.Composition.Comp

/-! # Measurable staircase refinement

The refinement splits each output density into fourteen extreme rays. Equality
in one information direction constrains rays mixed by a common output law. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Causalean.Stat.Privacy

private def patternIndex (s : Fin 14) : Staircase.RayIndex :=
  ⟨Finset.univ.filter (fun j : Fin 4 ↦ patternContains s j),
    by fin_cases s <;> decide,
    by fin_cases s <;> decide⟩

private def patternEquiv : Fin 14 ≃ Staircase.RayIndex :=
  Equiv.ofBijective patternIndex (by decide)

private lemma mem_patternIndex (s : Fin 14) (j : Fin 4) :
    j ∈ (patternEquiv s).val ↔ patternContains s j := by
  simp [patternEquiv, patternIndex]

private lemma patternRay_eq_ray (eps : ℝ) (s : Fin 14) (j : Fin 4) :
    patternRay eps s j = Staircase.ray (Real.exp eps) (patternEquiv s) j := by
  by_cases h : patternContains s j <;>
    simp [patternRay, Staircase.ray, privacyIncrement, privacyRatio,
      mem_patternIndex, h]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (Y0 Y1 W Y : ℕ → Ω → ℝ) (p : ℝ) (θ : TrialParameter)

private structure InteriorData (p : ℝ) (θ : TrialParameter) : Prop where
  assignmentInterior : InteriorAssignment p
  meansInterior : InteriorMeans θ

private lemma piTheta_by_val (j : Fin 4) :
    piTheta θ p j =
      if j.val = 0 then controlProb p * (1 - θ 0)
      else if j.val = 1 then controlProb p * θ 0
      else if j.val = 2 then p * (1 - θ 1)
      else p * θ 1 := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

private lemma piTheta_pos (hmodel : InteriorData p θ) (j : Fin 4) :
    0 < piTheta θ p j := by
  rcases hmodel.assignmentInterior with ⟨hp0, hp1⟩
  rcases hmodel.meansInterior with ⟨h00, h01, h10, h11⟩
  rw [piTheta_by_val p θ]
  rcases j with ⟨j, hj⟩
  interval_cases j <;> simp [controlProb] <;> positivity

private lemma sum_piTheta (hmodel : InteriorData p θ) :
    ∑ j, piTheta θ p j = 1 := by
  simp_rw [piTheta_by_val p θ]
  simp [Fin.sum_univ_four, controlProb]
  ring

private def trialScore (θ : TrialParameter) (p : ℝ) (j : Fin 4) (k : Fin 2) : ℝ :=
  inputDerivative p j k / piTheta θ p j

private lemma patternMass_eq_releaseMass (eps : ℝ) (s : Fin 14) :
    patternMass θ p eps s =
      ∑ j, piTheta θ p j * Staircase.ray (Real.exp eps) (patternEquiv s) j := by
  simp_rw [patternMass, patternRay_eq_ray]

private lemma patternGradient_eq_ray_score
    (hmodel : InteriorData p θ) (eps : ℝ)
    (s : Fin 14) (k : Fin 2) :
    patternGradient p eps s k =
      ∑ j, piTheta θ p j * Staircase.ray (Real.exp eps) (patternEquiv s) j *
        trialScore θ p j k := by
  have hterm (j : Fin 4) :
      piTheta θ p j * Staircase.ray (Real.exp eps) (patternEquiv s) j *
          trialScore θ p j k =
        Staircase.ray (Real.exp eps) (patternEquiv s) j * inputDerivative p j k := by
    unfold trialScore
    field_simp [ne_of_gt (piTheta_pos p θ hmodel j)]
  simp_rw [hterm]
  simp_rw [← patternRay_eq_ray]
  fin_cases s <;> fin_cases k <;>
    simp [patternGradient, inputDerivative, patternRay, patternContains,
      privacyIncrement, privacyRatio,
      controlProb, Fin.sum_univ_four] <;>
    norm_num [Nat.testBit] <;> split_ifs <;> norm_num at * <;> ring

private lemma sum_inputDerivative_mul_patternRay (p eps : ℝ)
    (s : Fin 14) (k : Fin 2) :
    (∑ j : Fin 4, inputDerivative p j k * patternRay eps s j) =
      patternGradient p eps s k := by
  fin_cases s <;> fin_cases k <;>
    simp [patternGradient, inputDerivative, patternRay, patternContains,
      privacyIncrement, privacyRatio, controlProb, Fin.sum_univ_four] <;>
    norm_num [Nat.testBit] <;> split_ifs <;> norm_num at * <;> ring

/-- Under the supplied quantities and conditions, the channel fisher info staircase eq information matrix assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the channel Fisher Info staircase eq information Matrix](goal).

Under the stated assumptions, the channel Fisher Info staircase eq information Matrix. -/
lemma channelFisherInfo_staircase_eq_informationMatrix
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    channelFisherInfo θ p (staircaseChannel ε α) =
      informationMatrix θ p ε α := by
  let Q := staircaseChannel ε α
  let R : Fin 14 → ℝ := fun s => ∑ j : Fin 4, patternRay ε s j
  have hray (s : Fin 14) (j : Fin 4) : 0 < patternRay ε s j := by
    unfold patternRay privacyIncrement privacyRatio
    cases patternContains s j <;> simp <;> positivity
  have hR (s : Fin 14) : 0 < R s := by
    exact lt_of_lt_of_le (hray s 0)
      (Finset.single_le_sum (fun j hj => (hray s j).le) (Finset.mem_univ 0))
  have hmass (s : Fin 14) : 0 < patternMass θ p ε s := by
    unfold patternMass
    apply Finset.sum_pos
    · intro j hj
      exact mul_pos (piTheta_pos p θ ⟨hp, hθ⟩ j) (hray s j)
    · simp
  have hdensity (j : Fin 4) :
      channelDensity Q j =ᵐ[dominatingMeasure Q]
        fun s => if α s = 0 then 0 else patternRay ε s j / R s := by
    exact channelDensity_staircase_ae ε α hε.le hα.1 j
  let _ : IsMarkovKernel Q := staircaseChannel_markov ε α hα
  let _ : IsFiniteMeasure (dominatingMeasure Q) :=
    ⟨by simp [dominatingMeasure]⟩
  ext a b
  unfold channelFisherInfo informationMatrix
  have hintegrand :
      (fun s => channelDerivativeDensity p Q a s *
          channelDerivativeDensity p Q b s / channelOutputDensity θ p Q s) =ᵐ[
        dominatingMeasure Q]
      fun s => if α s = 0 then 0 else
        patternGradient p ε s a * patternGradient p ε s b /
          (patternMass θ p ε s * R s) := by
    filter_upwards [hdensity 0, hdensity 1, hdensity 2, hdensity 3] with
      s h0 h1 h2 h3
    have hd (j : Fin 4) : channelDensity Q j s =
        if α s = 0 then 0 else patternRay ε s j / R s := by
      fin_cases j <;> assumption
    simp_rw [channelDerivativeDensity, channelOutputDensity, hd]
    by_cases ha : α s = 0
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      have hder (k : Fin 2) :
          (∑ j : Fin 4, inputDerivative p j k *
            (patternRay ε s j / R s)) = patternGradient p ε s k / R s := by
        simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        rw [sum_inputDerivative_mul_patternRay]
      have hout :
          (∑ j : Fin 4, piTheta θ p j * (patternRay ε s j / R s)) =
            patternMass θ p ε s / R s := by
        simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        rfl
      rw [hder a, hder b, hout]
      field_simp [ne_of_gt (hR s), ne_of_gt (hmass s)]
  rw [integral_congr_ae hintegrand]
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show (dominatingMeasure Q).real {s} = α s * R s by
    exact dominatingMeasure_staircase_singleton_real ε α hε.le hα.1 s]
  by_cases ha : α s = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte, smul_eq_mul]
    field_simp [ne_of_gt (hR s), ne_of_gt (hmass s)]

private def reindexedWeight {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {r : ℝ} (R : Staircase.Refinement Q r) : StaircaseWeight :=
  fun s ↦ R.alpha (patternEquiv s)

private def reindexedPostprocess {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {r : ℝ} (R : Staircase.Refinement Q r) :
    Kernel (Fin 14) Z :=
  Kernel.ofFunOfCountable fun s ↦ R.K (patternEquiv s)

private lemma reindexedPostprocess_markov {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {r : ℝ} (R : Staircase.Refinement Q r) :
    IsMarkovKernel (reindexedPostprocess R) := by
  letI : IsMarkovKernel R.K := R.markovK
  exact ⟨fun s ↦ inferInstanceAs (IsProbabilityMeasure (R.K (patternEquiv s)))⟩

private lemma reindexedWeight_feasible {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} (eps : ℝ)
    (R : Staircase.Refinement Q (Real.exp eps)) :
    staircaseFeasible eps (reindexedWeight R) := by
  constructor
  · intro s
    exact R.alpha (patternEquiv s) |>.coe_nonneg
  · intro j
    unfold staircaseMatrix reindexedWeight
    simp_rw [patternRay_eq_ray]
    exact (Equiv.sum_comp patternEquiv
      (fun S ↦ (R.alpha S : ℝ) * Staircase.ray (Real.exp eps) S j)).trans
        (R.normalized j)

private lemma reindexed_release_singleton {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} (eps : ℝ)
    (R : Staircase.Refinement Q (Real.exp eps)) (i : Fin 4) (s : Fin 14) :
    staircaseChannel eps (reindexedWeight R) i {s} = R.T i {patternEquiv s} := by
  rw [R.release_singleton]
  change (Measure.count.withDensity (fun u : Fin 14 ↦
    ENNReal.ofReal (reindexedWeight R u * patternRay eps u i))) {s} = _
  rw [withDensity_apply _ (MeasurableSet.singleton s)]
  simp [reindexedWeight, patternRay_eq_ray,
    ENNReal.ofReal_mul (R.alpha (patternEquiv s)).coe_nonneg]

private lemma reindexed_factorizes {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} (eps : ℝ)
    (R : Staircase.Refinement Q (Real.exp eps)) :
    Q = (reindexedPostprocess R).comp
      (staircaseChannel eps (reindexedWeight R)) := by
  calc
    Q = R.K ∘ₖ R.T := R.factorizes
    _ = (reindexedPostprocess R).comp
        (staircaseChannel eps (reindexedWeight R)) := by
      ext i A hA
      rw [Kernel.comp_apply' _ _ _ hA, Kernel.comp_apply' _ _ _ hA,
        lintegral_fintype, lintegral_fintype]
      rw [← Equiv.sum_comp patternEquiv]
      apply Finset.sum_congr rfl
      intro s _
      rw [reindexed_release_singleton eps R i s]
      rfl

private lemma releaseMass_reindex {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {eps : ℝ}
    (R : Staircase.Refinement Q (Real.exp eps)) (θ : TrialParameter) (p : ℝ)
    (s : Fin 14) :
    Staircase.releaseMass R.T (piTheta θ p) (patternEquiv s) =
      reindexedWeight R s * patternMass θ p eps s := by
  have hray (S : Staircase.RayIndex) (j : Fin 4) :
      0 ≤ Staircase.ray (Real.exp eps) S j := by
    unfold Staircase.ray
    split <;> positivity
  unfold Staircase.releaseMass patternMass reindexedWeight
  simp_rw [R.release_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hray _ _)]
  change (∑ x, piTheta θ p x * ((R.alpha (patternEquiv s) : ℝ) *
    Staircase.ray (Real.exp eps) (patternEquiv s) x)) = _
  simp_rw [patternRay_eq_ray]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma releaseNumerator_reindex {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {eps : ℝ}
    (R : Staircase.Refinement Q (Real.exp eps))
    (P : Fin 4 → ℝ) (u : Fin 4 → Fin 2 → ℝ) (g v : Fin 2 → ℝ)
    (s : Fin 14)
    (hg : ∀ k, g k = ∑ j, P j * Staircase.ray (Real.exp eps) (patternEquiv s) j *
      u j k) :
    (∑ j, P j * (R.T j {patternEquiv s}).toReal *
      Staircase.projectedScore u v j) =
      reindexedWeight R s * ∑ k, g k * v k := by
  have hray (S : Staircase.RayIndex) (j : Fin 4) :
      0 ≤ Staircase.ray (Real.exp eps) S j := by
    unfold Staircase.ray
    split <;> positivity
  simp_rw [R.release_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hray _ _)]
  change (∑ j, P j * ((R.alpha (patternEquiv s) : ℝ) *
    Staircase.ray (Real.exp eps) (patternEquiv s) j) * (∑ k, v k * u j k)) = _
  unfold reindexedWeight
  calc
    _ = (R.alpha (patternEquiv s) : ℝ) *
        ∑ k, (∑ j, P j * Staircase.ray (Real.exp eps) (patternEquiv s) j *
          u j k) * v k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp_rw [← hg]

private lemma releaseScore_reindex {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {eps : ℝ}
    (R : Staircase.Refinement Q (Real.exp eps))
    (hmodel : InteriorData p θ)
    (s : Fin 14) (t : ℝ) (hα : reindexedWeight R s ≠ 0) :
    Staircase.releaseScore R.T (piTheta θ p)
        (Staircase.projectedScore (trialScore θ p) (direction t)) (patternEquiv s) =
      projectedScore θ p eps s t := by
  unfold Staircase.releaseScore projectedScore projectedGradient
  rw [releaseNumerator_reindex R (piTheta θ p) (trialScore θ p)
      (patternGradient p eps s) (direction t) s
      (patternGradient_eq_ray_score p θ hmodel eps s),
    releaseMass_reindex R θ p s]
  field_simp [hα]

/-- the [information quadratic](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:I,v), these specify the stated inputs. -/
def informationQuadratic (I : Matrix (Fin 2) (Fin 2) ℝ)
    (v : TrialParameter) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, v a * I a b * v b

-- @node: informationQuadratic_eq_pattern_sum
/-- Under [the supplied quantities and conditions](hyp:p,eps,v), [the information quadratic eq pattern sum assertion](goal) holds. -/
lemma informationQuadratic_eq_pattern_sum
    (θ : TrialParameter) (p eps : ℝ) (α : StaircaseWeight) (v : TrialParameter) :
    informationQuadratic (informationMatrix θ p eps α) v =
      ∑ s, α s * (∑ k, patternGradient p eps s k * v k) ^ 2 /
        patternMass θ p eps s := by
  unfold informationQuadratic informationMatrix
  simp_rw [Finset.mul_sum, Finset.sum_mul, pow_two]
  calc
    (∑ a, ∑ b, ∑ s,
      v a * (α s * patternGradient p eps s a * patternGradient p eps s b /
        patternMass θ p eps s) * v b) =
        ∑ a, ∑ s, ∑ b,
          v a * (α s * patternGradient p eps s a * patternGradient p eps s b /
            patternMass θ p eps s) * v b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ a, ∑ b,
          v a * (α s * patternGradient p eps s a * patternGradient p eps s b /
            patternMass θ p eps s) * v b := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      ring

private lemma finiteFisher_reindex {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {eps : ℝ}
    (R : Staircase.Refinement Q (Real.exp eps))
    (hmodel : InteriorData p θ) (v : TrialParameter) :
    Staircase.finiteFisher R.T (piTheta θ p)
        (Staircase.projectedScore (trialScore θ p) v) =
      informationQuadratic (informationMatrix θ p eps (reindexedWeight R)) v := by
  unfold Staircase.finiteFisher
  rw [← Equiv.sum_comp patternEquiv]
  rw [informationQuadratic_eq_pattern_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [releaseNumerator_reindex R (piTheta θ p) (trialScore θ p)
      (patternGradient p eps s) v s
      (patternGradient_eq_ray_score p θ hmodel eps s),
    releaseMass_reindex R θ p s]
  by_cases hα : reindexedWeight R s = 0
  · simp [hα]
  · field_simp [hα]

private lemma piTheta_mul_trialScore
    (hmodel : InteriorData p θ) (j : Fin 4) (k : Fin 2) :
    piTheta θ p j * trialScore θ p j k = inputDerivative p j k := by
  unfold trialScore
  field_simp [ne_of_gt (piTheta_pos p θ hmodel j)]

private lemma outputNumerator_eq {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z)
    (hmodel : InteriorData p θ) (v : TrialParameter) (z : Z) :
    (∑ j, piTheta θ p j * channelDensity Q j z *
      Staircase.projectedScore (trialScore θ p) v j) =
      ∑ k, v k * channelDerivativeDensity p Q k z := by
  unfold Staircase.projectedScore channelDerivativeDensity
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [← piTheta_mul_trialScore p θ hmodel j k]
  ring

private lemma outputFisher_eq_integral {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z)
    (hmodel : InteriorData p θ) (v : TrialParameter) :
    Staircase.outputFisher Q (piTheta θ p)
        (Staircase.projectedScore (trialScore θ p) v) =
      ∫ z, (∑ k, v k * channelDerivativeDensity p Q k z) ^ 2 /
        channelOutputDensity θ p Q z ∂dominatingMeasure Q := by
  unfold Staircase.outputFisher Staircase.rowDensity Staircase.rowSum
  change (∫ z, (∑ i, piTheta θ p i * channelDensity Q i z *
      Staircase.projectedScore (trialScore θ p) v i) ^ 2 /
      channelOutputDensity θ p Q z ∂dominatingMeasure Q) = _
  congr 1
  funext z
  rw [outputNumerator_eq p θ Q hmodel v z]

private lemma patternMass_pos
    (hmodel : InteriorData p θ) (eps : ℝ) (s : Fin 14) :
    0 < patternMass θ p eps s := by
  unfold patternMass
  apply Finset.sum_pos
  intro j _
  apply mul_pos (piTheta_pos p θ hmodel j)
  rw [patternRay_eq_ray]
  unfold Staircase.ray
  split <;> positivity
  simp

private lemma reindexedPostprocess_apply {Z : Type*} [MeasurableSpace Z]
    {Q : Kernel (Fin 4) Z} {r : ℝ} (R : Staircase.Refinement Q r) (s : Fin 14) :
    reindexedPostprocess R s = R.K (patternEquiv s) := rfl

private lemma reindexed_rigidity {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] {eps : ℝ}
    (R : Staircase.Refinement Q (Real.exp eps))
    (hmodel : InteriorData p θ) (t : ℝ)
    (hgap : Staircase.finiteFisher R.T (piTheta θ p)
        (Staircase.projectedScore (trialScore θ p) (direction t)) -
      Staircase.outputFisher Q (piTheta θ p)
        (Staircase.projectedScore (trialScore θ p) (direction t)) = 0)
    (s u : Fin 14) (hs : reindexedWeight R s ≠ 0)
    (hu : reindexedWeight R u ≠ 0)
    (hnot : ¬ (reindexedPostprocess R s) ⟂ₘ (reindexedPostprocess R u)) :
    projectedScore θ p eps s t = projectedScore θ p eps u t := by
  have hαs : 0 < reindexedWeight R s :=
    lt_of_le_of_ne (R.alpha (patternEquiv s)).coe_nonneg (Ne.symm hs)
  have hαu : 0 < reindexedWeight R u :=
    lt_of_le_of_ne (R.alpha (patternEquiv u)).coe_nonneg (Ne.symm hu)
  have hms : 0 < Staircase.releaseMass R.T (piTheta θ p) (patternEquiv s) := by
    rw [releaseMass_reindex R θ p s]
    exact mul_pos hαs (patternMass_pos p θ hmodel eps s)
  have hmu : 0 < Staircase.releaseMass R.T (piTheta θ p) (patternEquiv u) := by
    rw [releaseMass_reindex R θ p u]
    exact mul_pos hαu (patternMass_pos p θ hmodel eps u)
  by_contra hneq
  have hsing := Staircase.equality_rigidity Q (Real.exp eps) R (piTheta θ p)
    (piTheta_pos p θ hmodel)
    (sum_piTheta p θ hmodel) (trialScore θ p) (direction t)
    hgap (patternEquiv s) (patternEquiv u) hms hmu (by
      rw [releaseScore_reindex p θ R hmodel s t hs,
        releaseScore_reindex p θ R hmodel u t hu]
      exact hneq)
  exact hnot (by simpa [reindexedPostprocess_apply] using hsing)

/-! The measure-theoretic input to the refinement.  Keeping these facts
separate is useful because the Radon--Nikodym construction below must use the
same dominating measure for all four rows. For [the displayed quantities and conditions](hyp:Q,j), these specify the stated inputs. -/
/-- [Every row of a finite-input channel is bounded by its dominating measure](goal). -/
lemma channelRow_le_dominating {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) (j : Fin 4) :
    Q j ≤ dominatingMeasure Q := by
  simp only [dominatingMeasure]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ j)

/-- [the channel row absolutely continuous dominating assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,j), these specify the stated inputs. -/
lemma channelRow_absolutelyContinuous_dominating {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) (j : Fin 4) :
    Q j ≪ dominatingMeasure Q :=
  Measure.absolutelyContinuous_of_le (channelRow_le_dominating Q j)

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- [the channel density measurable assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,j), these specify the stated inputs. -/
lemma channelDensity_measurable {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) (j : Fin 4) :
    Measurable (channelDensity Q j) := by
  exact (Measure.measurable_rnDeriv (Q j) (dominatingMeasure Q)).ennreal_toReal

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- [the channel density nonneg assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,j,z), these specify the stated inputs. -/
lemma channelDensity_nonneg {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) (j : Fin 4) (z : Z) :
    0 ≤ channelDensity Q j z :=
  ENNReal.toReal_nonneg

/-- [the channel density le one ae assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,j), these specify the stated inputs. -/
lemma channelDensity_le_one_ae {Z : Type*} [MeasurableSpace Z] {eps : ℝ}
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP eps Q) (j : Fin 4) :
    ∀ᵐ z ∂dominatingMeasure Q, channelDensity Q j z ≤ 1 := by
  let _ : IsMarkovKernel Q := hQ.1
  let _ : IsFiniteMeasure (dominatingMeasure Q) := ⟨by simp [dominatingMeasure]⟩
  filter_upwards [Measure.rnDeriv_le_one_of_le (channelRow_le_dominating Q j)] with z hz
  exact ENNReal.toReal_mono (by simp) hz

private lemma output_denominator_eq {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z) (z : Z) :
    (∑ i, piTheta θ p i * Staircase.rowDensity Q i z) =
      channelOutputDensity θ p Q z := by
  rfl

private lemma inputDerivative_eq_pi_mul_trialScore
    (hmodel : InteriorData p θ) (j : Fin 4) (k : Fin 2) :
    inputDerivative p j k = piTheta θ p j * trialScore θ p j k :=
  (piTheta_mul_trialScore p θ hmodel j k).symm

private lemma derivative_abs_le {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hmodel : InteriorData p θ)
    (Q : Kernel (Fin 4) Z) (k : Fin 2) (z : Z) :
    |channelDerivativeDensity p Q k z| ≤
      channelOutputDensity θ p Q z * ∑ i, |trialScore θ p i k| := by
  have hpi (i : Fin 4) : 0 ≤ piTheta θ p i :=
    le_of_lt (piTheta_pos p θ hmodel i)
  have hd (i : Fin 4) : 0 ≤ channelDensity Q i z := ENNReal.toReal_nonneg
  have hterm (i : Fin 4) :
      inputDerivative p i k * channelDensity Q i z =
        (piTheta θ p i * channelDensity Q i z) * trialScore θ p i k := by
    rw [inputDerivative_eq_pi_mul_trialScore p θ hmodel]
    ring
  unfold channelDerivativeDensity
  simp_rw [hterm]
  calc
    |∑ i, (piTheta θ p i * channelDensity Q i z) * trialScore θ p i k| ≤
        ∑ i, |(piTheta θ p i * channelDensity Q i z) * trialScore θ p i k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (piTheta θ p i * channelDensity Q i z) * |trialScore θ p i k| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hpi i) (hd i))]
    _ ≤ ∑ i, (piTheta θ p i * channelDensity Q i z) *
        (∑ j, |trialScore θ p j k|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hpi i) (hd i))
      exact Finset.single_le_sum (fun j hj => abs_nonneg (trialScore θ p j k))
        (Finset.mem_univ i)
    _ = channelOutputDensity θ p Q z * ∑ j, |trialScore θ p j k| := by
      rw [← Finset.sum_mul]
      rfl

private lemma outputDensity_nonneg {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hpi : ∀ i, 0 ≤ piTheta θ p i) (z : Z) :
    0 ≤ channelOutputDensity θ p Q z := by
  unfold channelOutputDensity
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hpi i) ENNReal.toReal_nonneg

private lemma cross_integrable {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hmodel : InteriorData p θ) (ε : ℝ)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) (a b : Fin 2) :
    Integrable (fun z => channelDerivativeDensity p Q a z *
      channelDerivativeDensity p Q b z / channelOutputDensity θ p Q z)
      (dominatingMeasure Q) := by
  let _ : IsMarkovKernel Q := hQ.1
  let _ : IsFiniteMeasure (dominatingMeasure Q) := ⟨by simp [dominatingMeasure]⟩
  let Ca : ℝ := ∑ i, |trialScore θ p i a|
  let Cb : ℝ := ∑ i, |trialScore θ p i b|
  let P : ℝ := ∑ i, piTheta θ p i
  have hpi (i : Fin 4) : 0 ≤ piTheta θ p i :=
    le_of_lt (piTheta_pos p θ hmodel i)
  have hCa : 0 ≤ Ca := Finset.sum_nonneg fun i hi => abs_nonneg _
  have hCb : 0 ≤ Cb := Finset.sum_nonneg fun i hi => abs_nonneg _
  have hP : 0 ≤ P := Finset.sum_nonneg fun i hi => hpi i
  have hmeas : Measurable (fun z => channelDerivativeDensity p Q a z *
      channelDerivativeDensity p Q b z / channelOutputDensity θ p Q z) := by
    unfold channelDerivativeDensity channelOutputDensity channelDensity
    fun_prop
  apply Integrable.of_bound hmeas.aestronglyMeasurable (P * Ca * Cb)
  filter_upwards [channelDensity_le_one_ae Q hQ 0,
      channelDensity_le_one_ae Q hQ 1,
      channelDensity_le_one_ae Q hQ 2,
      channelDensity_le_one_ae Q hQ 3] with z h0 h1 h2 h3
  have hdle (i : Fin 4) : channelDensity Q i z ≤ 1 := by
    fin_cases i <;> assumption
  have hHle : channelOutputDensity θ p Q z ≤ P := by
    unfold channelOutputDensity P
    apply Finset.sum_le_sum
    intro i hi
    simpa using mul_le_mul_of_nonneg_left (hdle i) (hpi i)
  have hH0 : 0 ≤ channelOutputDensity θ p Q z :=
    outputDensity_nonneg θ p Q hpi z
  have hDa := derivative_abs_le p θ hmodel Q a z
  have hDb := derivative_abs_le p θ hmodel Q b z
  change |channelDerivativeDensity p Q a z * channelDerivativeDensity p Q b z /
      channelOutputDensity θ p Q z| ≤ P * Ca * Cb
  by_cases hz : channelOutputDensity θ p Q z = 0
  · have ha : channelDerivativeDensity p Q a z = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa [Ca, hz] using hDa) (abs_nonneg _)
    simp [hz, ha, mul_nonneg (mul_nonneg hP hCa) hCb]
  · have hHpos : 0 < channelOutputDensity θ p Q z := lt_of_le_of_ne hH0 (Ne.symm hz)
    rw [abs_div, abs_mul, abs_of_pos hHpos]
    apply (div_le_iff₀ hHpos).2
    have hmul : |channelDerivativeDensity p Q a z| *
        |channelDerivativeDensity p Q b z| ≤
        (channelOutputDensity θ p Q z * Ca) *
          (channelOutputDensity θ p Q z * Cb) :=
      mul_le_mul hDa hDb (abs_nonneg _) (mul_nonneg hH0 hCa)
    calc
      |channelDerivativeDensity p Q a z| * |channelDerivativeDensity p Q b z| ≤
          (channelOutputDensity θ p Q z * Ca) *
            (channelOutputDensity θ p Q z * Cb) := hmul
      _ ≤ (P * Ca * Cb) * channelOutputDensity θ p Q z := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hHle) hCa,
          mul_nonneg (mul_nonneg hH0 hCa) hCb]

private lemma outputFisher_eq_informationQuadratic {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hmodel : InteriorData p θ) (ε : ℝ)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) (v : TrialParameter) :
    Staircase.outputFisher Q (piTheta θ p) (Staircase.projectedScore (trialScore θ p) v) =
      informationQuadratic (channelFisherInfo θ p Q) v := by
  let _ : IsMarkovKernel Q := hQ.1
  let _ : IsFiniteMeasure (dominatingMeasure Q) := ⟨by simp [dominatingMeasure]⟩
  unfold Staircase.outputFisher informationQuadratic channelFisherInfo
  rw [show Staircase.rowSum Q = dominatingMeasure Q by rfl]
  have hnum (z : Z) :
      (∑ i, piTheta θ p i * Staircase.rowDensity Q i z *
        Staircase.projectedScore (trialScore θ p) v i) =
        ∑ k, v k * channelDerivativeDensity p Q k z :=
    outputNumerator_eq p θ Q hmodel v z
  have hden (z : Z) :
      (∑ i, piTheta θ p i * Staircase.rowDensity Q i z) =
        channelOutputDensity θ p Q z :=
    output_denominator_eq θ p Q z
  simp_rw [hnum, hden]
  calc
    (∫ z, (∑ k, v k * channelDerivativeDensity p Q k z) ^ 2 /
        channelOutputDensity θ p Q z ∂dominatingMeasure Q) =
      ∫ z, ∑ a, ∑ b,
        v a * (channelDerivativeDensity p Q a z *
          channelDerivativeDensity p Q b z /
            channelOutputDensity θ p Q z) * v b ∂dominatingMeasure Q := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a, ∫ z, ∑ b,
        v a * (channelDerivativeDensity p Q a z *
          channelDerivativeDensity p Q b z /
            channelOutputDensity θ p Q z) * v b ∂dominatingMeasure Q := by
      rw [integral_finsetSum]
      intro a ha
      simpa using
        (integrable_finset_sum Finset.univ (fun b hb =>
          ((cross_integrable p θ hmodel ε Q hQ a b).const_mul
            (v a)).mul_const (v b)))
    _ = ∑ a, ∑ b, ∫ z,
        v a * (channelDerivativeDensity p Q a z *
          channelDerivativeDensity p Q b z /
            channelOutputDensity θ p Q z) * v b ∂dominatingMeasure Q := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum]
      intro b hb
      exact ((cross_integrable p θ hmodel ε Q hQ a b).const_mul
        (v a)).mul_const (v b)
    _ = ∑ a, ∑ b, v a *
        (∫ z, channelDerivativeDensity p Q a z * channelDerivativeDensity p Q b z /
          channelOutputDensity θ p Q z ∂dominatingMeasure Q) * v b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      let f : Z → ℝ := fun z => channelDerivativeDensity p Q a z *
        channelDerivativeDensity p Q b z / channelOutputDensity θ p Q z
      change (∫ z, v a * f z * v b ∂dominatingMeasure Q) =
        v a * (∫ z, f z ∂dominatingMeasure Q) * v b
      calc
        (∫ z, v a * f z * v b ∂dominatingMeasure Q) =
            ∫ z, v a * (f z * v b) ∂dominatingMeasure Q := by
          congr 1
          funext z
          ring
        _ = v a * ∫ z, f z * v b ∂dominatingMeasure Q := integral_const_mul _ _
        _ = v a * ((∫ z, f z ∂dominatingMeasure Q) * v b) := by
          rw [integral_mul_const]
        _ = v a * (∫ z, f z ∂dominatingMeasure Q) * v b := by ring

/-- Directional information as a single row-sum Radon--Nikodym integral. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hQ), [the information Quadratic eq channel Integral](goal).

Under the stated assumptions, the information Quadratic eq channel Integral. -/
lemma informationQuadratic_eq_channelIntegral {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (ε : ℝ)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) (v : TrialParameter) :
    informationQuadratic (channelFisherInfo θ p Q) v =
      ∫ z, (∑ k, v k * channelDerivativeDensity p Q k z) ^ 2 /
        channelOutputDensity θ p Q z ∂dominatingMeasure Q := by
  exact (outputFisher_eq_informationQuadratic p θ ⟨hp, hθ⟩ ε Q hQ v).symm.trans
    (outputFisher_eq_integral p θ Q ⟨hp, hθ⟩ v)

-- @node: channelFisherInfo_posSemidef
private lemma channelFisherInfo_posSemidef_interior {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hmodel : InteriorData p θ) (ε : ℝ)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) :
    (channelFisherInfo θ p Q).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial]
    unfold channelFisherInfo
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  · intro v
    rw [show star v ⬝ᵥ (channelFisherInfo θ p Q).mulVec v =
        informationQuadratic (channelFisherInfo θ p Q) v by
      simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial]
      ring]
    rw [← outputFisher_eq_informationQuadratic p θ hmodel ε Q hQ v]
    unfold Staircase.outputFisher
    apply integral_nonneg
    intro z
    apply div_nonneg (sq_nonneg _)
    exact outputDensity_nonneg θ p Q
      (fun i => (piTheta_pos p θ hmodel i).le) z

private lemma informationDifference_posSemidef {Z : Type*} [MeasurableSpace Z]
    (eps : ℝ) (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP eps Q)
    (R : Staircase.Refinement Q (Real.exp eps))
    (hmodel : InteriorData p θ) :
    (informationMatrix θ p eps (reindexedWeight R) -
      channelFisherInfo θ p Q).PosSemidef := by
  letI : IsMarkovKernel Q := hQ.1
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · unfold Matrix.IsHermitian
    ext a b
    change informationMatrix θ p eps (reindexedWeight R) b a -
        channelFisherInfo θ p Q b a =
      informationMatrix θ p eps (reindexedWeight R) a b -
        channelFisherInfo θ p Q a b
    congr 1
    · unfold informationMatrix
      apply Finset.sum_congr rfl
      intro s _
      ring
    · unfold channelFisherInfo
      apply integral_congr_ae
      filter_upwards [] with z
      ring
  · intro v
    have hgap := Staircase.fisher_gap_nonneg Q (Real.exp eps) R (piTheta θ p)
      (piTheta_pos p θ hmodel)
      (sum_piTheta p θ hmodel) (trialScore θ p) v
    rw [finiteFisher_reindex p θ R hmodel v,
      outputFisher_eq_informationQuadratic p θ hmodel eps Q hQ v]
      at hgap
    simp [dotProduct, Matrix.mulVec, informationQuadratic, Finset.mul_sum,
      Finset.sum_sub_distrib] at hgap ⊢
    linarith

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- [the ldp row le assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,x,x'), these specify the stated inputs. -/
lemma ldp_row_le {Z : Type*} [MeasurableSpace Z] {eps : ℝ}
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP eps Q) (x x' : Fin 4) :
    Q x ≤ ENNReal.ofReal (Real.exp eps) • Q x' := by
  rw [Measure.le_iff]
  intro A hA
  simpa [Measure.smul_apply, smul_eq_mul] using hQ.2 A hA x x'

/-- [the integral channel density assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,j), these specify the stated inputs. -/
lemma integral_channelDensity {Z : Type*} [MeasurableSpace Z] {eps : ℝ}
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP eps Q) (j : Fin 4) :
    ∫ z, channelDensity Q j z ∂dominatingMeasure Q = (Q j).real Set.univ := by
  let _ : IsMarkovKernel Q := hQ.1
  let _ : IsFiniteMeasure (dominatingMeasure Q) := ⟨by simp [dominatingMeasure]⟩
  exact Measure.integral_toReal_rnDeriv
    (channelRow_absolutelyContinuous_dominating Q j)

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- [the integral channel density eq one assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,j), these specify the stated inputs. -/
lemma integral_channelDensity_eq_one {Z : Type*} [MeasurableSpace Z] {eps : ℝ}
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP eps Q) (j : Fin 4) :
    ∫ z, channelDensity Q j z ∂dominatingMeasure Q = 1 := by
  rw [integral_channelDensity Q hQ j]
  let _ : IsMarkovKernel Q := hQ.1
  simp

/-- Under [the supplied quantities and conditions](hyp:heps), [the privacy increment pos assertion](goal) holds. -/
lemma privacyIncrement_pos {eps : ℝ} (heps : 0 < eps) :
    0 < privacyIncrement eps := by
  rw [privacyIncrement, privacyRatio, sub_pos]
  exact Real.one_lt_exp_iff.mpr heps

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under [the supplied quantities and conditions](hyp:eps,j), [the complementary pattern ray assertion](goal) holds. -/
lemma complementary_patternRay (eps : ℝ) (j : Fin 4) :
    patternRay eps 0 j + patternRay eps 13 j = Real.exp eps + 1 := by
  have h : patternContains 0 j = !(patternContains 13 j) := by
    fin_cases j <;> decide
  rw [patternRay, patternRay, h]
  cases h13 : patternContains 13 j <;>
    simp [privacyIncrement, privacyRatio] <;> ring

-- @node: lem:staircase-refinement
/-- the staircase refinement interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hfixed,hQ), [the staircase refinement interior](goal).

Under the stated assumptions, the staircase refinement interior. -/
lemma staircase_refinement_interior {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (epsSeq : ℕ → ℝ) (hfixed : FixedPrivacy epsSeq ε)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) :
    ∃ α : StaircaseWeight, ∃ K : Kernel (Fin 14) Z,
      staircaseFeasible ε α ∧ IsMarkovKernel K ∧
      Q = K.comp (staircaseChannel ε α) ∧
      (informationMatrix θ p ε α - channelFisherInfo θ p Q).PosSemidef ∧
      (∀ t : ℝ,
        informationQuadratic (informationMatrix θ p ε α) (direction t) =
          informationQuadratic (channelFisherInfo θ p Q) (direction t) →
        ∀ s u : Fin 14, α s ≠ 0 → α u ≠ 0 → ¬ (K s) ⟂ₘ (K u) →
          projectedScore θ p ε s t = projectedScore θ p ε u t) := by
  let hmodel : InteriorData p θ := ⟨hp, hθ⟩
  letI : IsMarkovKernel Q := hQ.1
  have hr : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hfixed.1
  obtain ⟨R⟩ := Staircase.exists_refinement Q (Real.exp ε) hr (by
    intro i j A hA
    exact hQ.2 A hA i j)
  refine ⟨reindexedWeight R, reindexedPostprocess R,
    reindexedWeight_feasible ε R, reindexedPostprocess_markov R,
    reindexed_factorizes ε R,
    informationDifference_posSemidef p θ ε Q hQ R hmodel, ?_⟩
  intro t heq s u hs hu hnot
  have hgap :
      Staircase.finiteFisher R.T (piTheta θ p)
          (Staircase.projectedScore (trialScore θ p) (direction t)) -
        Staircase.outputFisher Q (piTheta θ p)
          (Staircase.projectedScore (trialScore θ p) (direction t)) = 0 := by
    rw [finiteFisher_reindex p θ R hmodel (direction t),
      outputFisher_eq_informationQuadratic p θ hmodel ε Q hQ
        (direction t)]
    linarith
  exact reindexed_rigidity p θ Q R hmodel t hgap s u hs hu hnot

/-- the channel fisher info pos semidef assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hQ), [the channel Fisher Info pos Semidef](goal).

Under the stated assumptions, the channel Fisher Info pos Semidef. -/
lemma channelFisherInfo_posSemidef {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (θ : TrialParameter) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (ε : ℝ) (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP ε Q) :
    (channelFisherInfo θ p Q).PosSemidef := by
  exact channelFisherInfo_posSemidef_interior p θ ⟨hp, hθ⟩ ε Q hQ

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- [the staircase refinement assertion](goal) holds. For [the displayed quantities and conditions](hyp:Y0,Y1,W,Y,p,hmodel,epsSeq,hfixed,Q,hQ), these specify the stated inputs. -/
lemma staircase_refinement {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] (μ : Measure Ω) (Y0 Y1 W Y : ℕ → Ω → ℝ)
    (p : ℝ) (θ : TrialParameter) (ε : ℝ)
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (epsSeq : ℕ → ℝ) (hfixed : FixedPrivacy epsSeq ε)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) :
    ∃ α : StaircaseWeight, ∃ K : Kernel (Fin 14) Z,
      staircaseFeasible ε α ∧ IsMarkovKernel K ∧
      Q = K.comp (staircaseChannel ε α) ∧
      (informationMatrix θ p ε α - channelFisherInfo θ p Q).PosSemidef ∧
      (∀ t : ℝ,
        informationQuadratic (informationMatrix θ p ε α) (direction t) =
          informationQuadratic (channelFisherInfo θ p Q) (direction t) →
        ∀ s u : Fin 14, α s ≠ 0 → α u ≠ 0 → ¬ (K s) ⟂ₘ (K u) →
          projectedScore θ p ε s t = projectedScore θ p ε u t) := by
  exact staircase_refinement_interior p θ ε hmodel.assignmentInterior
    hmodel.meansInterior epsSeq hfixed Q hQ

end CausalSmith.Stat.LdpAteEfficiencySurface
