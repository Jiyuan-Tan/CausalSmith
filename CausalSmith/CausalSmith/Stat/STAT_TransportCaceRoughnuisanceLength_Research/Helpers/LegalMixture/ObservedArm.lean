module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Assignment

/-! # Observed arm identities for the lower experiment

The finite source-cell kernel disintegrates each observed arm integral.
Its weighted cell sum reproduces the exact primitive arm mean in roadmap (10).
-/

public section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Summing the eight observed source cells reproduces the conditional arm mean.  Under [the displayed assumptions and inputs](hyp:a,u,v,x,ha,hu,A,z), [the stated conclusion holds](goal). -/
-- @node: sourceCellMass_arm_mean_sum
lemma sourceCellMass_arm_mean_sum (a u v x : ℝ) (ha : a ≠ 0)
    (hu : |u| ≤ 1 / 100) (A z : Bool) :
    (∑ c : SourceCell, sourceCellMass a u v c *
      (if c.1 = z then armValue A (sourceCellObservation x c) else 0)) =
      assignmentWeight u z * armMeanFrom (fun _ => primitiveMass a u v) A z x := by
  cases A
  · rw [armMeanFrom_primitive_receipt_eq _ _ _ _ ha]
    cases z <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, sourceCellMass,
      sourceCellObservation, armValue, assignmentWeight, receiptOutcomeCell, receiptBase,
      boolReal, sign] <;> ring
  · rw [armMeanFrom_primitive_outcome_eq _ _ _ _ ha hu]
    have hp : 1 + 2 * u ≠ 0 := by have := (abs_le.mp hu).1; linarith
    have hm : 1 - 2 * u ≠ 0 := by have := (abs_le.mp hu).2; linarith
    cases z <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, sourceCellMass,
      sourceCellObservation, armValue, assignmentWeight, receiptOutcomeCell, receiptBase,
      boolReal, sign]
    all_goals field_simp; ring_nf
    all_goals field_simp [hp, hm, show 1 - u * 2 ≠ 0 by simpa [mul_comm] using hm]; ring

/-- A normalized nonnegative finite source-cell kernel gives its exact arm set integral.  Under [the displayed assumptions and inputs](hyp:a,u,hu,hw,A,z,B,hB), [the stated conclusion holds](goal). -/
-- @node: explicitSourceLaw_arm_setIntegral
lemma explicitSourceLaw_arm_setIntegral (a τ : ℝ) (u : ℝ → ℝ)
    (hu : Measurable u)
    (hw : ∀ x c, 0 ≤ sourceCellMass a (u x) (τ * u x) c)
    (A z : Bool) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ o in {o | o.1 ∈ B ∧ o.2.1 = z}, armValue A o
      ∂explicitSourceLaw a u (fun x => τ * u x)) =
    ∫ x in B, ∑ c : SourceCell, sourceCellMass a (u x) (τ * u x) c *
      (if c.1 = z then armValue A (sourceCellObservation x c) else 0)
      ∂volume.restrict covariateSpace := by
  classical
  let atom := sourceCellObservation
  let weight (x : ℝ) (c : SourceCell) := sourceCellMass a (u x) (τ * u x) c
  have hm (c : SourceCell) : Measurable (fun x => weight x c) := by
    rcases c with ⟨zc, d, y⟩
    cases zc <;> cases d <;> cases y <;>
      simp [weight, sourceCellMass, assignmentWeight, receiptOutcomeCell, receiptBase, sign]
      <;> fun_prop (disch := assumption)
  let κ : Kernel ℝ SourceObs := ⟨fun x => ∑ c, ENNReal.ofReal (weight x c) •
      Measure.dirac (atom x c), by
    refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hT]
    exact Finset.measurable_fun_sum _ (fun c _ =>
      (hm c).ennreal_ofReal.mul
        (measurable_one.indicator (hT.preimage (sourceCellObservation_measurable c))))⟩
  have hnorm (x : ℝ) : ∑ c, weight x c = 1 := sourceCellMass_sum a τ (u x)
  have hk (x : ℝ) : κ x = ∑ c, ENNReal.ofReal (weight x c) • Measure.dirac (atom x c) := rfl
  have : IsMarkovKernel κ := ⟨fun x => isProbabilityMeasure_iff.mpr (by
    rw [hk]
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem (Set.mem_univ _),
      Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hw x c), hnorm]
    simp)⟩
  let f : SourceObs → ℝ := fun o => if o.2.1 = z then armValue A o else 0
  have hz : MeasurableSet {o : SourceObs | o.2.1 = z} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ite hz
    · cases A
      · change Measurable (fun o : SourceObs => if o.2.2.1 then (1 : ℝ) else 0)
        exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
          measurable_const measurable_const
      · change Measurable (fun o : SourceObs => o.2.2.2)
        fun_prop
    · exact measurable_const
  have hbnd (x : ℝ) (c : SourceCell) : ‖f (atom x c)‖ ≤ 1 := by
    rcases c with ⟨zc, d, y⟩
    cases A <;> cases z <;> cases zc <;> cases d <;> cases y <;>
      norm_num [f, atom, sourceCellObservation, armValue, boolReal]
  have hfi (x : ℝ) (g : SourceObs → ℝ) : Integrable g (κ x) := by
    rw [hk]
    exact integrable_finsetSum_measure.mpr (fun c _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  have hint : Integrable f (κ ∘ₘ volume.restrict covariateSpace) := by
    apply (Measure.integrable_comp_iff hf.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => hfi x f), ?_⟩
    have heq (x : ℝ) : (∫ o, ‖f o‖ ∂κ x) = ∑ c, weight x c * ‖f (atom x c)‖ :=
      Causalean.Mathlib.Probability.Kernel.FiniteAtomic.integral_finiteAtomicKernel
        κ atom weight hw hk _ x (hfi x _)
    simp_rw [heq]
    have hmeas : Measurable (fun x => ∑ c, weight x c * ‖f (atom x c)‖) :=
      Finset.measurable_fun_sum _ (fun c _ =>
        (hm c).mul ((hf.comp (sourceCellObservation_measurable c)).norm))
    have : IsFiniteMeasure (volume.restrict covariateSpace) := by
      change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)); infer_instance
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (hw x c) (norm_nonneg _)))]
    calc
      ∑ c, weight x c * ‖f (atom x c)‖ ≤ ∑ c, weight x c * 1 :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hbnd x c) (hw x c))
      _ = 1 := by simpa using hnorm x
  have h := Causalean.Mathlib.Probability.Kernel.FiniteAtomic.setIntegral_finiteAtomicKernel
    (volume.restrict covariateSpace) κ atom weight hw hk Prod.fst measurable_fst
    (fun _ _ => rfl) B hB f hint
  have hμ : κ ∘ₘ volume.restrict covariateSpace =
      explicitSourceLaw a u (fun x => τ * u x) := rfl
  rw [hμ] at h
  have hevent : {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z} =
      {o | o.1 ∈ B} ∩ {o | o.2.1 = z} := rfl
  rw [hevent, ← setIntegral_indicator hz]
  convert h using 1
  · congr 1
    funext o
    by_cases ho : o.2.1 = z <;> simp [Set.indicator, f, ho]
  · congr 1

/-- Every legal component has the exact observed-arm integral required by the model class. Under [the displayed assumptions and inputs](hyp:a,cStar,n,sgn,ha,hc,hn,A,z,B,hB,hBC,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_arm_setIntegral
lemma legalIVComponent_arm_setIntegral (a cStar τ : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hc : 0 < cStar ∧ cStar ≤ 1 / 100) (hn : threshold ≤ n)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (A z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) (hBC : B ⊆ covariateSpace) :
    (∫ o in {o | o.1 ∈ B ∧ o.2.1 = z}, armValue A o
      ∂sourceObsLaw (legalIVComponent a n cStar τ sgn)) =
      ∫ x in B, (legalIVComponent a n cStar τ sgn).fS x *
        assignmentMass (legalIVComponent a n cStar τ sgn) z x *
        (legalIVComponent a n cStar τ sgn).m A z x := by
  have hb := actualStrength_bounds a n hn ha
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
  have hsource : sourceObsLaw (legalIVComponent a n cStar τ sgn) =
      explicitSourceLaw (actualStrength a n) (tiledPerturbation cStar n sgn)
        (fun x => τ * tiledPerturbation cStar n sgn x) :=
    lowerSourceLaw_eq_explicit a n cStar τ sgn hb hAdm hτ
  rw [hsource, explicitSourceLaw_arm_setIntegral _ _ _
    (tiledPerturbation_measurable cStar n sgn)
    (lowerSourceCellMass_nonneg a n cStar τ sgn hb hAdm hτ) A z B hB]
  rw [Measure.restrict_restrict hB, inter_eq_left.mpr hBC]
  apply setIntegral_congr_fun hB
  intro x hx
  have hu : |tiledPerturbation cStar n sgn x| ≤ 1 / 100 :=
    (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc.1.le).trans
      ((lowerHeight_le_amplitude cStar n hc.1.le hn).trans hc.2)
  dsimp only
  rw [sourceCellMass_arm_mean_sum _ _ _ x (ne_of_gt hb.1) hu A z]
  cases z <;> simp [legalIVComponent, lawFromMass, armMeanFrom, lowerMass, assignmentMass,
    assignmentWeight, coupledPerturbation] <;> ring

/-- The unperturbed center satisfies the same exact observed-arm identity.  Under [the displayed assumptions and inputs](hyp:a,n,hb,A,z,B,hB,hBC), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_arm_setIntegral
lemma mixtureCenter_arm_setIntegral (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) (A z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) (hBC : B ⊆ covariateSpace) :
    (∫ o in {o | o.1 ∈ B ∧ o.2.1 = z}, armValue A o ∂sourceObsLaw (mixtureCenter a n)) =
      ∫ x in B, (mixtureCenter a n).fS x * assignmentMass (mixtureCenter a n) z x *
        (mixtureCenter a n).m A z x := by
  have hsource : sourceObsLaw (mixtureCenter a n) =
      explicitSourceLaw (actualStrength a n) (fun _ => 0) (fun _ => 0) :=
    centerSourceLaw_eq_explicit a n hb
  have hw (x : ℝ) (c : SourceCell) :
      0 ≤ sourceCellMass (actualStrength a n) 0 (0 * 0) c := by
    simpa [sourceCellMass, sourceCenterMass, assignmentWeight] using
      (sourceCenterMass_pos (actualStrength a n) ⟨hb.1, by linarith [hb.2]⟩ c).le
  rw [hsource]
  have h := explicitSourceLaw_arm_setIntegral (actualStrength a n) 0 (fun _ => 0)
    measurable_const hw A z B hB
  simp only [mul_zero] at h
  rw [h, Measure.restrict_restrict hB, inter_eq_left.mpr hBC]
  apply setIntegral_congr_fun hB
  intro x hx
  dsimp only
  rw [sourceCellMass_arm_mean_sum _ 0 0 x (ne_of_gt hb.1) (by norm_num) A z]
  cases z <;> norm_num [mixtureCenter, lawFromMass, assignmentMass, assignmentWeight]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
