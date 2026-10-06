module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Likelihood

/-! # One-observation channel laws for the legal mixture -/

public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- For [the source-arm strength](hyp:a), [the tilt parameter](hyp:τ), [the covariate perturbation](hyp:u), and [an observed source record](hyp:o), [source observation likelihood](goal) is the likelihood of that record's encoded latent cell. -/
@[expose] noncomputable def sourceObsLikelihood (a τ : ℝ) (u : ℝ → ℝ)
    (o : SourceObs) : ℝ :=
  sourceLikelihood a τ (u o.1)
    (o.2.1, o.2.2.1, o.2.2.2 = 1)
/-- Given [the supplied inputs](hyp:a,u,o), [the stated result about source obs likelihood eq cell holds](goal). -/

lemma sourceObsLikelihood_eq_cell (a τ : ℝ) (u : ℝ → ℝ)
    (o : SourceObs) :
    sourceObsLikelihood a τ u o = sourceLikelihood a τ (u o.1)
      (o.2.1, o.2.2.1, o.2.2.2 = 1) := rfl
/-- Given [the supplied inputs](hyp:a,u,x,c), [the stated result about source obs likelihood on cell holds](goal). -/

lemma sourceObsLikelihood_on_cell (a τ : ℝ) (u : ℝ → ℝ)
    (x : ℝ) (c : SourceCell) :
    sourceObsLikelihood a τ u (sourceCellObservation x c) =
      sourceLikelihood a τ (u x) c := by
  rcases c with ⟨z, d, y⟩
  cases y <;> simp [sourceObsLikelihood, sourceCellObservation, boolReal]
/-- Given [the supplied inputs](hyp:a,u,hu), [the stated result about source obs likelihood measurable holds](goal). -/

lemma sourceObsLikelihood_measurable (a τ : ℝ) (u : ℝ → ℝ)
    (hu : Measurable u) : Measurable (sourceObsLikelihood a τ u) := by
  have hcell (z d y : Bool) : Measurable fun o : SourceObs =>
      sourceLikelihood a τ (u o.1) (z, d, y) := by
    unfold sourceLikelihood sourceDirection sourceCenterMass sourceCellMass
      assignmentWeight receiptOutcomeCell receiptBase sign
    cases z <;> cases d <;> cases y <;> simp <;> fun_prop
  have hz : MeasurableSet {o : SourceObs | o.2.1 = true} := by measurability
  have hd : MeasurableSet {o : SourceObs | o.2.2.1 = true} := by measurability
  have hy : MeasurableSet {o : SourceObs | o.2.2.2 = 1} := by measurability
  have hpiece : Measurable fun o : SourceObs =>
      if o.2.1 then
        if o.2.2.1 then
          if o.2.2.2 = 1 then sourceLikelihood a τ (u o.1) (true, true, true)
          else sourceLikelihood a τ (u o.1) (true, true, false)
        else if o.2.2.2 = 1 then sourceLikelihood a τ (u o.1) (true, false, true)
          else sourceLikelihood a τ (u o.1) (true, false, false)
      else if o.2.2.1 then
        if o.2.2.2 = 1 then sourceLikelihood a τ (u o.1) (false, true, true)
        else sourceLikelihood a τ (u o.1) (false, true, false)
      else if o.2.2.2 = 1 then sourceLikelihood a τ (u o.1) (false, false, true)
        else sourceLikelihood a τ (u o.1) (false, false, false) := by
    exact Measurable.ite hz
      (Measurable.ite hd (Measurable.ite hy (hcell true true true) (hcell true true false))
        (Measurable.ite hy (hcell true false true) (hcell true false false)))
      (Measurable.ite hd (Measurable.ite hy (hcell false true true) (hcell false true false))
        (Measurable.ite hy (hcell false false true) (hcell false false false)))
  convert hpiece using 1
  funext o
  rcases o with ⟨x, z, d, y⟩
  cases z <;> cases d <;>
    by_cases h : y = 1 <;> simp [sourceObsLikelihood, h]
/-- Given [the supplied inputs](hyp:a,u,v,hu,hv,A,hA), [the stated result about explicit source law apply holds](goal). -/

lemma explicitSourceLaw_apply (a : ℝ) (u v : ℝ → ℝ)
    (hu : Measurable u) (hv : Measurable v)
    (A : Set SourceObs) (hA : MeasurableSet A) :
    explicitSourceLaw a u v A =
      encodedCellSetMass (volume.restrict covariateSpace)
        (fun x c => ENNReal.ofReal (sourceCellMass a (u x) (v x) c))
        sourceCellObservation A := by
  classical
  unfold explicitSourceLaw encodedCellSetMass
  have hk : Measurable fun x =>
      ∑ c : SourceCell, ENNReal.ofReal (sourceCellMass a (u x) (v x) c) •
        Measure.dirac (sourceCellObservation x c) := by
    refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro c hc
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
    have hm : Measurable fun x => sourceCellMass a (u x) (v x) c := by
      rcases c with ⟨z, d, y⟩
      cases z <;> cases d <;> cases y <;>
        simp [sourceCellMass, assignmentWeight, receiptOutcomeCell,
          receiptBase, sign] <;> fun_prop (disch := assumption)
    exact hm.ennreal_ofReal.mul
      (measurable_one.indicator (hB.preimage (sourceCellObservation_measurable c)))
  rw [Measure.bind_apply hA hk.aemeasurable]
  apply lintegral_congr
  intro x
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA]
  apply Finset.sum_congr rfl
  intro c hc
  simp [Set.indicator]
/-- Given [the supplied inputs](hyp:a,u,ha,hu), [the stated result about explicit source law eq with density holds](goal). -/

lemma explicitSourceLaw_eq_withDensity (a τ : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a ∧ a < 1) (hu : Measurable u) :
    explicitSourceLaw a u (fun x => τ * u x) =
      (explicitSourceLaw a (fun _ => 0) (fun _ => 0)).withDensity
        (fun o => ENNReal.ofReal (sourceObsLikelihood a τ u o)) := by
  apply eq_withDensity_of_encodedCellSetMass
    (volume.restrict covariateSpace)
    (explicitSourceLaw a (fun _ => 0) (fun _ => 0))
    (explicitSourceLaw a u (fun x => τ * u x))
    (fun _ c => ENNReal.ofReal (sourceCenterMass a c))
    (fun x c => ENNReal.ofReal (sourceCellMass a (u x) (τ * u x) c))
    sourceCellObservation (sourceObsLikelihood a τ u)
  · intro c
    exact measurable_const
  · exact sourceCellObservation_measurable
  · exact sourceObsLikelihood_measurable a τ u hu
  · intro A hA
    simpa [sourceCenterMass] using
      explicitSourceLaw_apply a (fun _ => 0) (fun _ => 0)
        measurable_const measurable_const A hA
  · intro A hA
    exact explicitSourceLaw_apply a u (fun x => τ * u x) hu
      (measurable_const.mul hu) A hA
  · intro x c
    have hp := sourceCenterMass_pos a ha c
    have hreal : sourceCellMass a (u x) (τ * u x) c =
        sourceCenterMass a c * sourceLikelihood a τ (u x) c := by
      rw [sourceCellMass_affine]
      unfold sourceLikelihood
      field_simp [ne_of_gt hp]
    rw [sourceObsLikelihood_on_cell]
    rw [← ENNReal.ofReal_mul (le_of_lt hp), ← hreal]
/-- Given [the supplied inputs](hyp:a,u,v,ha,hu,hm,he,c), [the stated result about source cell mass nonneg of primitive holds](goal). -/

lemma sourceCellMass_nonneg_of_primitive (a u v : ℝ)
    (ha : a ≠ 0) (hu : u ^ 2 ≠ 1 / 4)
    (hm : ∀ d0 d1 y0 y1, 0 ≤ primitiveMass a u v d0 d1 y0 y1)
    (he : ∀ z, 0 ≤ assignmentWeight u z) (c : SourceCell) :
    0 ≤ sourceCellMass a u v c := by
  rcases c with ⟨z, d, y⟩
  rw [← observedPrimitiveMass_eq a u v ha hu z d y]
  apply mul_nonneg (he z)
  unfold observedPrimitiveMass
  apply Finset.sum_nonneg
  intro d0 hd0
  apply Finset.sum_nonneg
  intro d1 hd1
  apply Finset.sum_nonneg
  intro y0 hy0
  apply Finset.sum_nonneg
  intro y1 hy1
  split_ifs
  · exact hm d0 d1 y0 y1
  · exact le_rfl
/-- Given [the supplied inputs](hyp:a,u,ha,hq0,o), [the stated result about source obs likelihood nonneg of cell mass holds](goal). -/

lemma sourceObsLikelihood_nonneg_of_cellMass (a τ : ℝ) (u : ℝ → ℝ)
    (ha : 0 < a ∧ a < 1)
    (hq0 : ∀ x c, 0 ≤ sourceCellMass a (u x) (τ * u x) c)
    (o : SourceObs) : 0 ≤ sourceObsLikelihood a τ u o := by
  let c : SourceCell := (o.2.1, o.2.2.1, o.2.2.2 = 1)
  have hp := sourceCenterMass_pos a ha c
  have hreal : sourceCellMass a (u o.1) (τ * u o.1) c =
      sourceCenterMass a c * sourceLikelihood a τ (u o.1) c := by
    rw [sourceCellMass_affine]
    unfold sourceLikelihood
    field_simp [ne_of_gt hp]
  have hq := hq0 o.1 c
  rw [hreal] at hq
  unfold sourceObsLikelihood
  nlinarith
/-- Given [the supplied inputs](hyp:a,u,v,ha,hu), [the stated result about primitive mass sum holds](goal). -/

lemma primitiveMass_sum (a u v : ℝ) (ha : a ≠ 0)
    (hu : u ^ 2 ≠ 1 / 4) :
    ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      primitiveMass a u v d0 d1 y0 y1 = 1 := by
  have hp : 1 + 2 * u ≠ 0 := by
    intro h
    apply hu
    nlinarith
  have hm : 1 - 2 * u ≠ 0 := by
    intro h
    apply hu
    nlinarith
  simp [Fintype.sum_bool, primitiveMass, complierMargin, receiptBase,
    assignmentWeight, sign]
  field_simp [ha, hp, hm]
  ring
/-- Given [the supplied inputs](hyp:a,n,hn,ha), [the stated result about actual strength bounds holds](goal). -/

lemma actualStrength_bounds (a : ℝ) (n : ℕ)
    (hn : threshold ≤ n) (ha : 0 < a ∧ a ≤ 1 / 4) :
    0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4 := by
  have hn64 : (64 : ℝ) ≤ n := by
    exact_mod_cast (show 64 ≤ n by have : 256 ≤ n := hn; omega)
  have hpow : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 / 4 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 64)
      hn64 (by norm_num : (-(1 / 3 : ℝ)) ≤ 0)
    norm_num at h ⊢
    exact h
  unfold actualStrength
  constructor
  · exact lt_of_lt_of_le ha.1 (le_max_left _ _)
  · exact max_le ha.2 hpow
/-- Given [the supplied inputs](hyp:n,sgn,x), [the stated result about tiled perturbation zero holds](goal). -/

lemma tiledPerturbation_zero (n : ℕ) (sgn : Fin (lowerCells n) → Bool) (x : ℝ) :
    tiledPerturbation 0 n sgn x = 0 := by
  simp [tiledPerturbation, lowerHeight]

set_option maxHeartbeats 600000 in
/-- Given [the supplied inputs](hyp:a,n,hb), [the stated result about center source law eq explicit holds](goal). -/
lemma centerSourceLaw_eq_explicit (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    Measure.map observeSource
      (assignedFrom
        (primitivePopulation true (fun _ => 1)
          (fun _ => primitiveMass (actualStrength a n) 0 0))
        (fun _ => 1 / 2)) =
      explicitSourceLaw (actualStrength a n) (fun _ => 0) (fun _ => 0) := by
  let sgn : Fin (lowerCells n) → Bool := fun _ => false
  have hm : ∀ x d0 d1 y0 y1,
      0 ≤ lowerMass a n 0 0 sgn x d0 d1 y0 y1 := by
    intro x d0 d1 y0 y1
    simp only [lowerMass, tiledPerturbation_zero, coupledPerturbation,
      zero_mul]
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  have he : ∀ x z, 0 ≤ assignmentWeight (tiledPerturbation 0 n sgn x) z := by
    intro x z
    rw [tiledPerturbation_zero]
    cases z <;> norm_num [assignmentWeight]
  have h := sourceLaw_eq_explicit_of_nonneg a n 0 0 sgn hm he hb.1 (by
    intro x
    rw [tiledPerturbation_zero]
    norm_num)
  have hu : tiledPerturbation 0 n sgn = fun _ => 0 := by
    funext x
    exact tiledPerturbation_zero n sgn x
  have hv : coupledPerturbation 0 0 n sgn = fun _ => 0 := by
    funext x
    simp [coupledPerturbation]
  have hlm : lowerMass a n 0 0 sgn =
      fun _ => primitiveMass (actualStrength a n) 0 0 := by
    funext x d0 d1 y0 y1
    simp [lowerMass, tiledPerturbation_zero, coupledPerturbation]
  rw [hu, hv, hlm] at h
  simpa using h

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
