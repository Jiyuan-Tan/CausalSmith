module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Overlap

/-! # Source-channel overlap identities -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:a,ha), [the stated result about explicit center source law univ holds](goal). -/

lemma explicitCenterSourceLaw_univ (a : ℝ) (ha : 0 < a ∧ a < 1) :
    explicitSourceLaw a (fun _ => 0) (fun _ => 0) Set.univ = 1 := by
  rw [explicitSourceLaw_apply a (fun _ => 0) (fun _ => 0)
    measurable_const measurable_const Set.univ MeasurableSet.univ]
  unfold encodedCellSetMass
  simp only [Set.mem_univ, ↓reduceIte]
  rw [show (∑ c : SourceCell,
      ENNReal.ofReal (sourceCellMass a 0 0 c)) = 1 by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [show (∑ c : SourceCell, sourceCellMass a 0 0 c) = 1 by
        simpa [sourceCenterMass] using sourceCenterMass_sum a]
      simp
    · intro c hc
      simpa [sourceCenterMass] using (sourceCenterMass_pos a ha c).le]
  simp [covariateSpace]
/-- [The explicit center source law is probability object](goal) is defined from [the supplied inputs](hyp:a,ha). -/

noncomputable def explicitCenterSourceLaw_isProbability (a : ℝ)
    (ha : 0 < a ∧ a < 1) :
    IsProbabilityMeasure
      (explicitSourceLaw a (fun _ => 0) (fun _ => 0)) := by
  apply isProbabilityMeasure_iff.mpr
  exact explicitCenterSourceLaw_univ a ha
/-- Given [the supplied inputs](hyp:a,u), [the stated result about source cell mass sum holds](goal). -/

lemma sourceCellMass_sum (a τ u : ℝ) :
    ∑ cell : SourceCell, sourceCellMass a u (τ * u) cell = 1 := by
  simp_rw [sourceCellMass_affine]
  rw [Finset.sum_add_distrib, sourceCenterMass_sum]
  simp_rw [← Finset.mul_sum]
  rw [sourceDirection_sum]
  ring
/-- Given [the supplied inputs](hyp:a,u,hu,hq), [the stated result about explicit source law univ of nonneg holds](goal). -/

lemma explicitSourceLaw_univ_of_nonneg (a τ : ℝ) (u : ℝ → ℝ)
    (hu : Measurable u)
    (hq : ∀ x cell, 0 ≤ sourceCellMass a (u x) (τ * u x) cell) :
    explicitSourceLaw a u (fun x => τ * u x) Set.univ = 1 := by
  rw [explicitSourceLaw_apply a u (fun x => τ * u x) hu
    (measurable_const.mul hu) Set.univ MeasurableSet.univ]
  unfold encodedCellSetMass
  simp only [Set.mem_univ, ↓reduceIte]
  have hsum (x : ℝ) :
      ∑ cell : SourceCell,
          ENNReal.ofReal (sourceCellMass a (u x) (τ * u x) cell) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [sourceCellMass_sum a τ]
      simp
    · intro cell hcell
      exact hq x cell
  simp_rw [hsum]
  simp [covariateSpace]
/-- [The explicit source law is probability of nonneg object](goal) is defined from [the supplied inputs](hyp:a,u,hu,hq). -/

noncomputable def explicitSourceLaw_isProbability_of_nonneg
    (a τ : ℝ) (u : ℝ → ℝ) (hu : Measurable u)
    (hq : ∀ x cell, 0 ≤ sourceCellMass a (u x) (τ * u x) cell) :
    IsProbabilityMeasure (explicitSourceLaw a u (fun x => τ * u x)) := by
  apply isProbabilityMeasure_iff.mpr
  exact explicitSourceLaw_univ_of_nonneg a τ u hu hq
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,hτ), [the stated result about lower source cell mass nonneg holds](goal). -/

lemma lowerSourceCellMass_nonneg (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    ∀ x cell, 0 ≤ sourceCellMass (actualStrength a n)
      (tiledPerturbation cStar n sgn x)
      (coupledPerturbation cStar τ n sgn x) cell := by
  intro x cell
  apply sourceCellMass_nonneg_of_primitive
  · exact ne_of_gt hb.1
  · intro heq
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have hu' : |tiledPerturbation cStar n sgn x| ≤ 3 / 16 :=
      le_trans hu hAdm.2.1
    have hs : |tiledPerturbation cStar n sgn x| = 1 / 2 := by
      nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
        abs_nonneg (tiledPerturbation cStar n sgn x)]
    linarith
  · exact lowerMass_nonneg a n cStar τ sgn hb hAdm hτ x
  · intro z
    exact (lowerAssignmentWeight_mem_Icc a n cStar τ sgn hAdm x z).1
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,hτ), [the stated result about lower source likelihood nonneg holds](goal). -/

lemma lowerSourceLikelihood_nonneg (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    ∀ o, 0 ≤ sourceObsLikelihood (actualStrength a n) τ
      (tiledPerturbation cStar n sgn) o := by
  apply sourceObsLikelihood_nonneg_of_cellMass
  · exact ⟨hb.1, lt_of_le_of_lt hb.2 (by norm_num)⟩
  intro x cell
  simpa [coupledPerturbation] using
    lowerSourceCellMass_nonneg a n cStar τ sgn hb hAdm hτ x cell
/-- Given [the supplied inputs](hyp:a,cStar,n,s,t,ha), [the stated result about source likelihood pair integrable holds](goal). -/

lemma sourceLikelihood_pair_integrable (a τ cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (ha : 0 < a ∧ a < 1) :
    Integrable (fun o =>
      sourceObsLikelihood a τ (tiledPerturbation cStar n s) o *
        sourceObsLikelihood a τ (tiledPerturbation cStar n t) o)
      (explicitSourceLaw a (fun _ => 0) (fun _ => 0)) := by
  letI : IsProbabilityMeasure
      (explicitSourceLaw a (fun _ => 0) (fun _ => 0)) :=
    explicitCenterSourceLaw_isProbability a ha
  let B := 1 + |lowerHeight cStar n| *
    ∑ cell : SourceCell,
      |sourceDirection a τ cell / sourceCenterMass a cell|
  have hcoeff (cell : SourceCell) :
      |sourceDirection a τ cell / sourceCenterMass a cell| ≤
        ∑ d : SourceCell,
          |sourceDirection a τ d / sourceCenterMass a d| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun d : SourceCell =>
        |sourceDirection a τ d / sourceCenterMass a d|)
      (fun d _ => abs_nonneg _) (Finset.mem_univ cell)
  have hbound (r : Fin (lowerCells n) → Bool) (o : SourceObs) :
      |sourceObsLikelihood a τ (tiledPerturbation cStar n r) o| ≤ B := by
    rw [sourceObsLikelihood_eq_cell]
    unfold sourceLikelihood B
    rw [show tiledPerturbation cStar n r o.1 *
        sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
          sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1) =
        tiledPerturbation cStar n r o.1 *
          (sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
            sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1)) by ring]
    calc
      |1 + tiledPerturbation cStar n r o.1 *
          (sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
            sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1))| ≤
          1 + |tiledPerturbation cStar n r o.1| *
            |sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
              sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1)| := by
            calc
              _ ≤ |(1 : ℝ)| + |tiledPerturbation cStar n r o.1 *
                  (sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
                    sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1))| :=
                abs_add_le _ _
              _ = _ := by rw [abs_one, abs_mul]
      _ ≤ 1 + |lowerHeight cStar n| *
            |sourceDirection a τ (o.2.1, o.2.2.1, o.2.2.2 = 1) /
              sourceCenterMass a (o.2.1, o.2.2.1, o.2.2.2 = 1)| := by
          simpa using add_le_add_right (mul_le_mul_of_nonneg_right
            (tiledPerturbation_abs_le_abs_lowerHeight cStar n r o.1)
            (abs_nonneg _)) 1
      _ ≤ _ := by
          simpa using add_le_add_right (mul_le_mul_of_nonneg_left
            (hcoeff (o.2.1, o.2.2.1, o.2.2.2 = 1))
            (abs_nonneg (lowerHeight cStar n))) 1
  have hm (r : Fin (lowerCells n) → Bool) :=
    sourceObsLikelihood_measurable a τ (tiledPerturbation cStar n r)
      (tiledPerturbation_measurable cStar n r)
  apply Integrable.of_bound ((hm s).mul (hm t)).aestronglyMeasurable (B ^ 2)
  filter_upwards [] with o
  change |sourceObsLikelihood a τ (tiledPerturbation cStar n s) o *
    sourceObsLikelihood a τ (tiledPerturbation cStar n t) o| ≤ _
  rw [abs_mul]
  have hB0 : 0 ≤ B := by
    unfold B
    positivity
  nlinarith [hbound s o, hbound t o,
    abs_nonneg (sourceObsLikelihood a τ (tiledPerturbation cStar n s) o),
    abs_nonneg (sourceObsLikelihood a τ (tiledPerturbation cStar n t) o),
    sq_nonneg B]
/-- Given [the supplied inputs](hyp:a,cStar,n,s,t,ha,hLs0,hLt0,hn), [the stated result about source likelihood pair integral holds](goal). -/

lemma sourceLikelihood_pair_integral (a τ cStar : ℝ) (n : ℕ)
    (s t : Fin (lowerCells n) → Bool) (ha : 0 < a ∧ a < 1)
    (hLs0 : ∀ o, 0 ≤ sourceObsLikelihood a τ
      (tiledPerturbation cStar n s) o)
    (hLt0 : ∀ o, 0 ≤ sourceObsLikelihood a τ
      (tiledPerturbation cStar n t) o)
    (hn : 0 < n) :
    (∫ o, sourceObsLikelihood a τ (tiledPerturbation cStar n s) o *
        sourceObsLikelihood a τ (tiledPerturbation cStar n t) o
      ∂explicitSourceLaw a (fun _ => 0) (fun _ => 0)) =
      1 + (sourceOverlapCoefficient a τ * lowerHeight cStar n ^ 2 / 2) *
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign s t /
          (lowerCells n : ℝ) := by
  let μ := explicitSourceLaw a (fun _ => 0) (fun _ => 0)
  let fs := sourceObsLikelihood a τ (tiledPerturbation cStar n s)
  let ft := sourceObsLikelihood a τ (tiledPerturbation cStar n t)
  have hfs : Measurable fs := sourceObsLikelihood_measurable a τ _
    (tiledPerturbation_measurable cStar n s)
  have hft : Measurable ft := sourceObsLikelihood_measurable a τ _
    (tiledPerturbation_measurable cStar n t)
  have hnonneg : ∀ o, 0 ≤ fs o * ft o := fun o => mul_nonneg (hLs0 o) (hLt0 o)
  have hk : Measurable (fun x : ℝ =>
      ∑ c : SourceCell, ENNReal.ofReal (sourceCenterMass a c) •
        Measure.dirac (sourceCellObservation x c)) := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro cell hcell
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
    exact measurable_const.mul (measurable_one.indicator
      (hA.preimage (sourceCellObservation_measurable cell)))
  have hinnerReal (x : ℝ) :
      ∑ cell : SourceCell, sourceCenterMass a cell *
          (fs (sourceCellObservation x cell) *
            ft (sourceCellObservation x cell)) =
        1 + tiledPerturbation cStar n s x *
          tiledPerturbation cStar n t x * sourceOverlapCoefficient a τ := by
    change ∑ cell : SourceCell, sourceCenterMass a cell *
        (sourceObsLikelihood a τ (tiledPerturbation cStar n s)
          (sourceCellObservation x cell) *
        sourceObsLikelihood a τ (tiledPerturbation cStar n t)
          (sourceCellObservation x cell)) = _
    simp_rw [sourceObsLikelihood_on_cell]
    exact sourceLikelihood_pair_sum a τ _ _ ha
  have hinner (x : ℝ) :
      ∑ cell : SourceCell, ENNReal.ofReal (sourceCenterMass a cell) *
          ENNReal.ofReal (fs (sourceCellObservation x cell) *
            ft (sourceCellObservation x cell)) =
        ENNReal.ofReal (1 + tiledPerturbation cStar n s x *
          tiledPerturbation cStar n t x * sourceOverlapCoefficient a τ) := by
    calc
      _ = ∑ cell : SourceCell, ENNReal.ofReal
          (sourceCenterMass a cell *
            (fs (sourceCellObservation x cell) *
              ft (sourceCellObservation x cell))) := by
          apply Finset.sum_congr rfl
          intro cell hcell
          rw [ENNReal.ofReal_mul (sourceCenterMass_pos a ha cell).le]
      _ = ENNReal.ofReal (∑ cell : SourceCell,
          sourceCenterMass a cell *
            (fs (sourceCellObservation x cell) *
              ft (sourceCellObservation x cell))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro cell hcell
          exact mul_nonneg (sourceCenterMass_pos a ha cell).le
            (mul_nonneg (hLs0 (sourceCellObservation x cell))
              (hLt0 (sourceCellObservation x cell)))
      _ = _ := by rw [hinnerReal]
  have hreal_nonneg (x : ℝ) : 0 ≤ 1 + tiledPerturbation cStar n s x *
      tiledPerturbation cStar n t x * sourceOverlapCoefficient a τ := by
    rw [← hinnerReal x]
    exact Finset.sum_nonneg fun cell hcell =>
      mul_nonneg (sourceCenterMass_pos a ha cell).le
        (mul_nonneg (hLs0 (sourceCellObservation x cell))
          (hLt0 (sourceCellObservation x cell)))
  letI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hreal_int : Integrable (fun x =>
      1 + tiledPerturbation cStar n s x * tiledPerturbation cStar n t x *
        sourceOverlapCoefficient a τ) (volume.restrict covariateSpace) :=
    (integrable_const 1).add
      ((tiledPerturbation_product_integrable cStar n s t).mul_const _)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg)
    ((hfs.mul hft).aestronglyMeasurable)]
  unfold explicitSourceLaw
  change (∫⁻ o : SourceObs, ENNReal.ofReal (fs o * ft o) ∂
      (volume.restrict covariateSpace).bind fun x =>
        ∑ cell : SourceCell, ENNReal.ofReal (sourceCenterMass a cell) •
          Measure.dirac (sourceCellObservation x cell)).toReal = _
  have hbind := Measure.lintegral_bind
    (m := volume.restrict covariateSpace) hk.aemeasurable
    ((hfs.mul hft).ennreal_ofReal.aemeasurable)
  have hbind' :
      (∫⁻ o : SourceObs, ENNReal.ofReal (fs o * ft o) ∂
        (volume.restrict covariateSpace).bind fun x =>
          ∑ cell : SourceCell, ENNReal.ofReal (sourceCenterMass a cell) •
            Measure.dirac (sourceCellObservation x cell)) =
      ∫⁻ x in covariateSpace,
        ∫⁻ o : SourceObs, ENNReal.ofReal (fs o * ft o) ∂
          ∑ cell : SourceCell, ENNReal.ofReal (sourceCenterMass a cell) •
            Measure.dirac (sourceCellObservation x cell) := by
    simpa only [Pi.mul_apply] using hbind
  rw [hbind']
  have hdirac (x : ℝ) (cell : SourceCell) :
      (∫⁻ o : SourceObs, ENNReal.ofReal (fs o * ft o) ∂
        Measure.dirac (sourceCellObservation x cell)) =
      ENNReal.ofReal (fs (sourceCellObservation x cell) *
        ft (sourceCellObservation x cell)) := by
    exact lintegral_dirac' _ ((hfs.mul hft).ennreal_ofReal)
  simp_rw [lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure]
  simp_rw [hdirac]
  simp_rw [smul_eq_mul]
  change (∫⁻ x in covariateSpace,
    ∑ cell : SourceCell, ENNReal.ofReal (sourceCenterMass a cell) *
      ENNReal.ofReal (fs (sourceCellObservation x cell) *
        ft (sourceCellObservation x cell))).toReal = _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hreal_int
    (Filter.Eventually.of_forall hreal_nonneg)]
  rw [ENNReal.toReal_ofReal (integral_nonneg hreal_nonneg)]
  rw [integral_add (integrable_const 1)
    ((tiledPerturbation_product_integrable cStar n s t).mul_const _),
    integral_mul_const, tiledPerturbation_pair_integral cStar n s t hn]
  simp [covariateSpace]
  ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
