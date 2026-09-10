import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathFactorization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessSpectral

/-! Model-class and gap certificates for the factorization-preserving labelled path. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

/-- A property true at every displayed path atom holds almost everywhere under the path law. -/
-- @node: ae_pathLaw_of_points
lemma ae_pathLaw_of_points (g h : ℝ) (p : FullData 2 2 2 → Prop)
    (hp : ∀ (u : Fin 2) (t x z y0 y1 : Bool), p (pathPoint u t x z y0 y1)) :
    ∀ᵐ w ∂pathLaw g h, p w := by
  rw [pathLaw]
  simp only [ae_finsetSum_measure_iff]
  intro u _ t _ x _ z _ y0 _ y1 _
  by_cases hc : ENNReal.ofReal (pathWeight g h u t x z y0 y1) = 0
  · simp [hc]
  · rw [Measure.ae_ennreal_smul_measure_iff hc, ae_dirac_eq]
    exact hp u t x z y0 y1

set_option maxHeartbeats 2000000 in
-- The explicit inverse-matrix normalization expands into several rational identities.
/-- The constructed reference feature has the normalized constant first coordinate. -/
-- @node: pathReferenceFeature_first_formula
lemma pathReferenceFeature_first_formula (t : Bool) (h : ℝ) (u : Fin 2)
    (hh : |h| ≤ 1 / 100) : pathReferenceFeature t h 0 u = 1 := by
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 15 * h + 4 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 5 * h + 3 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h2 : 2 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3m : 3 - h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h30p : 30 + h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h20p : 20 + h * 75 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h30m : 30 - h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h45m : 45 - h * 75 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0f : 6 / 25 + 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0t : 4 / 25 + 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1f : 6 / 25 - 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1t : 9 / 25 - 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0f' : 6 * 5 + 25 * h * 2 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0t' : 4 * 5 + 25 * 3 * h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1f' : 6 * 5 - 25 * h * 2 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1t' : 9 * 5 - 25 * 3 * h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hweights : pathArmWeights t h = fun u =>
      if t then (if u.val = 0 then 4 / 25 + 3 * h / 5 else 9 / 25 - 3 * h / 5)
      else (if u.val = 0 then 6 / 25 + 2 * h / 5 else 6 / 25 - 2 * h / 5) :=
    funext fun u => pathArmWeights_formula t h u hh
  have hweights0 : pathArmWeights t 0 = fun u =>
      if t then (if u.val = 0 then 4 / 25 else 9 / 25)
      else (if u.val = 0 then 6 / 25 else 6 / 25) := by
    funext u
    simpa using pathArmWeights_formula t 0 u (by norm_num : |(0 : ℝ)| ≤ 1 / 100)
  have hunit : IsUnit (fun u : Fin 2 =>
      if t then (if u.val = 0 then 4 / 25 + 3 * h / 5 else 9 / 25 - 3 * h / 5)
      else (if u.val = 0 then 6 / 25 + 2 * h / 5 else 6 / 25 - 2 * h / 5)) := by
    rw [Pi.isUnit_iff]
    intro v
    rw [isUnit_iff_ne_zero]
    fin_cases v <;> cases t <;> simp <;> nlinarith [hb.1, hb.2]
  change (pathJointProxyMoment t * ((pathTargetFeature h).transpose)⁻¹ *
    (Matrix.diagonal (pathArmWeights t h))⁻¹) (0 : Fin 2) u = 1
  rw [pathTargetTransposeInverse_formula h hh, hweights]
  unfold pathJointProxyMoment
  rw [hweights0, Matrix.inv_diagonal]
  fin_cases u <;> cases t <;>
    simp_all [baseReferenceFeature, pathTargetFeature, Matrix.mul_apply, Ring.inverse] <;>
    simp_rw [inv_eq_one_div] <;>
    field_simp [hp0, hp1, h4, h3, h2, h3m, h30p, h20p, h30m, h45m,
      hw0f, hw0t, hw1f, hw1t] <;>
    try field_simp [h30p, h20p, h30m, h45m, hw0f', hw0t', hw1f', hw1t']
  all_goals ring

set_option maxHeartbeats 2000000 in
-- Expanding all finite latent/proxy cells requires a larger simplification budget.
/-- The path's latent-class conditional target means equal its constructed target feature. -/
-- @node: path_targetFeature
lemma path_targetFeature (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : targetFeature (pathLaw g h) = pathTargetFeature h := by
  have hb := abs_le.mp hh
  have h2 : 2 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 3 - h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hsq : 9 - h * 30 + h ^ 2 * 25 ≠ 0 := by
    rw [show 9 - h * 30 + h ^ 2 * 25 = (3 - h * 5) ^ 2 by ring]
    exact pow_ne_zero _ h3
  ext i u
  rw [targetFeature, conditionalMean_path_latentClass g h hg0 hg1 hh]
  simp_rw [pathWeight]
  simp_rw [pathReferenceFeature_second_formula _ h _ hh]
  simp_rw [pathArmWeights_formula true h _ hh]
  simp only [pathPoint, witnessPoint]
  simp only [sum_mul_bernoulliMass]
  fin_cases i <;> fin_cases u <;>
    simp [pathTargetFeature, vec2, boolReal, bernoulliMass] <;>
    simp_rw [inv_eq_one_div] <;>
    field_simp [h2, h3, hsq]
  all_goals norm_num at * <;> field_simp [h2, h3, hsq] <;> ring

set_option maxHeartbeats 2000000 in
-- Expanding all finite latent-arm/proxy cells requires a larger simplification budget.
/-- The path's latent-arm conditional reference means equal its constructed reference feature. -/
-- @node: path_referenceFeature
lemma path_referenceFeature (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (t : Bool) :
    referenceFeature (pathLaw g h) t = pathReferenceFeature t h := by
  have hb := abs_le.mp hh
  have h2 : 2 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 3 - h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 4 + h * 15 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h5 : 3 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hd30p : 30 + h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hd40 : 40 + h * 250 + h ^ 2 * 375 ≠ 0 := by
    rw [show 40 + h * 250 + h ^ 2 * 375 = (4 + h * 15) * (10 + h * 25) by ring]
    exact mul_ne_zero h4 (by nlinarith [hb.1, hb.2])
  have hd30m : 30 - h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hd135 : 135 - h * 450 + h ^ 2 * 375 ≠ 0 := by
    rw [show 135 - h * 450 + h ^ 2 * 375 = 15 * (3 - h * 5) ^ 2 by ring]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h3)
  have hd90 : 90 + h * 300 + h ^ 2 * 250 ≠ 0 := by
    rw [show 90 + h * 300 + h ^ 2 * 250 = 10 * (3 + h * 5) ^ 2 by ring]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ h5)
  have hd160 : 160 + h * 1600 + h ^ 2 * 5250 + h ^ 3 * 5625 ≠ 0 := by
    rw [show 160 + h * 1600 + h ^ 2 * 5250 + h ^ 3 * 5625 =
      (4 + h * 15) ^ 2 * (10 + h * 25) by ring]
    exact mul_ne_zero (pow_ne_zero _ h4) (by nlinarith [hb.1, hb.2])
  ext i u
  rw [referenceFeature, conditionalMean_path_latentCell g h hg0 hg1 hh]
  have href : pathReferenceFeature t h i u =
      if i.val = 0 then 1 else
        if t then (if u.val = 0 then (225 * h + 28) / (20 * (15 * h + 4)) else 3 / 4)
        else (if u.val = 0 then (35 * h + 9) / (10 * (5 * h + 3)) else 7 / 10) := by
    by_cases hi : i.val = 0
    · rw [if_pos hi]
      have hieq : i = 0 := Fin.ext hi
      subst i
      exact pathReferenceFeature_first_formula t h u hh
    · rw [if_neg hi]
      have hieq : i = 1 := Fin.ext (by omega)
      subst i
      exact pathReferenceFeature_second_formula t h u hh
  rw [href]
  simp_rw [pathWeight]
  simp_rw [pathReferenceFeature_second_formula _ h _ hh]
  simp_rw [pathArmWeights_formula true h _ hh]
  simp only [pathPoint, witnessPoint]
  simp only [sum_mul_bernoulliMass]
  fin_cases i <;> fin_cases u <;> cases t <;>
    simp [pathTargetFeature, vec2, boolReal, bernoulliMass] <;>
    simp_rw [inv_eq_one_div] <;>
    field_simp <;> ring
  all_goals norm_num at * <;>
    field_simp [h2, h3, h4, h5, hd30p, hd40, hd30m, hd135, hd90, hd160] <;> ring

/-- The path obeys observed/potential-outcome consistency. -/
-- @node: path_consistency
lemma path_consistency (g h : ℝ) : CausalConsistency (pathLaw g h) := by
  unfold CausalConsistency
  apply ae_pathLaw_of_points
  intro u t x z y0 y1
  cases t <;> simp [pathPoint, witnessPoint, potential]

/-- The path preserves the constant first target-proxy coordinate. -/
-- @node: path_anchor
lemma path_anchor (g h : ℝ) : AnchorNormalization (pathLaw g h) := by
  unfold AnchorNormalization
  apply ae_pathLaw_of_points
  intro u t x z y0 y1 i hi
  simp [pathPoint, witnessPoint, vec2, hi]

/-- The target proxy remains inside the envelope along the path. -/
-- @node: path_boundedX
lemma path_boundedX (g h : ℝ) : BoundedTargetProxy (L := 2) (pathLaw g h) := by
  unfold BoundedTargetProxy
  apply ae_pathLaw_of_points
  intro u t x z y0 y1
  simp [pathPoint, witnessPoint, vec2, boolReal, Fin.sum_univ_two]
  cases x <;> norm_num [Real.sqrt_le_iff]

/-- Proxy outer products remain inside the envelope along the path. -/
-- @node: path_boundedProxyProduct
lemma path_boundedProxyProduct (g h : ℝ) :
    BoundedProxyProduct (L := 2) (pathLaw g h) := by
  unfold BoundedProxyProduct
  apply ae_pathLaw_of_points
  intro u t x z y0 y1
  simpa [pathPoint, witnessPoint] using witness_outerProduct_norm x z

/-- Outcome-weighted proxy outer products remain inside the envelope along the path. -/
-- @node: path_boundedOutcomeProxyProduct
lemma path_boundedOutcomeProxyProduct (g h : ℝ) :
    BoundedOutcomeProxyProduct (L := 2) (pathLaw g h) := by
  unfold BoundedOutcomeProxyProduct
  apply ae_pathLaw_of_points
  intro u t x z y0 y1
  cases t
  · cases y0
    · change ‖matrixCLM (0 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simp [matrixCLM]
    · change ‖matrixCLM (1 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simpa using witness_outerProduct_norm x z
  · cases y1
    · change ‖matrixCLM (0 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simp [matrixCLM]
    · change ‖matrixCLM (1 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simpa using witness_outerProduct_norm x z

/-- The latent-arm cell masses are exactly the constructed arm weights. -/
-- @node: path_latentCell_mass
lemma path_latentCell_mass (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) (t : Bool) :
    (pathLaw g h).real (latentCell u t) = pathArmWeights t h u := by
  classical
  rw [pathLaw_real g h _ (measurableSet_witness_latentCell u t)]
  simp_rw [ENNReal.toReal_ofReal (pathWeight_nonneg g h hg0 hg1 hh _ _ _ _ _ _)]
  rw [path_sum_restrict_latentCell g h u t (fun _ => (1 : ℝ))]
  simp only [mul_one, pathWeight, sum_mul_bernoulliMass]
  rw [pathArmWeights_formula true h u hh, pathArmWeights_formula t h u hh]
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h2 : 2 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 3 - h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  fin_cases u <;> cases t <;>
    norm_num only [Fin.isValue, Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      bernoulliMass]
  all_goals field_simp [hp0, hp1, h2, h3]
  all_goals have h2' : 2 + 5 * h ≠ 0 := by nlinarith [hb.1, hb.2]
  all_goals have h3' : 3 - 5 * h ≠ 0 := by nlinarith [hb.1, hb.2]
  all_goals field_simp [h2', h3'] <;> ring

/-- Every latent-arm cell retains the required one-tenth probability floor. -/
-- @node: path_latentArmPositivity
lemma path_latentArmPositivity (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : LatentArmPositivity (pi0 := 1 / 10) (pathLaw g h) := by
  intro u t
  rw [path_latentCell_mass g h hg0 hg1 hh]
  rw [pathArmWeights_formula t h u hh]
  have hb := abs_le.mp hh
  fin_cases u <;> cases t <;> simp <;> nlinarith [hb.1, hb.2]

/-- The operator norm of a two-by-two perturbation supported in the lower-right entry
is bounded by the absolute value of that entry. -/
-- @node: path_lowerRight_opNorm
lemma path_lowerRight_opNorm (a : ℝ) :
    ‖matrixCLM (!![(0 : ℝ), 0; 0, a])‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro x
  simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec,
    dotProduct, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hx : |x.ofLp 1| ≤ Real.sqrt (x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x.ofLp 0)])
  rw [Real.sqrt_sq_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

/-- The operator norm of a two-by-two perturbation supported in the lower-left entry
is bounded by the absolute value of that entry. -/
-- @node: path_lowerLeft_opNorm
lemma path_lowerLeft_opNorm (a : ℝ) :
    ‖matrixCLM (!![(0 : ℝ), 0; a, 0])‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro x
  simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec,
    dotProduct, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hx : |x.ofLp 0| ≤ Real.sqrt (x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x.ofLp 1)])
  rw [Real.sqrt_sq_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

/-- The undisplaced target feature has enough strict singular-value slack to absorb
the small labelled-path perturbation. -/
-- @node: pathTargetFeature_zero_strictRank
lemma pathTargetFeature_zero_strictRank :
    (1 / 5 : ℝ) ≤ signalMinSingular (pathTargetFeature 0) := by
  apply signalMinSingular_lower_fin_two _ _ (by norm_num)
  intro x
  simp [pathTargetFeature, Fin.sum_univ_two]
  nlinarith [sq_nonneg (3 * x 0 - 4 * x 1)]

/-- The displaced lower-right target-feature entry remains within one fiftieth of
its undisplaced value. -/
-- @node: pathTargetFeature_entry_displacement
lemma pathTargetFeature_entry_displacement (h : ℝ) (hh : |h| ≤ 1 / 100) :
    |(12 / 25 - h / 5) / (3 / 5 - h) - 4 / 5| ≤ 1 / 50 := by
  have hb := abs_le.mp hh
  have hd : 0 < 3 / 5 - h := by nlinarith
  have hdn : 3 / 5 - h ≠ 0 := ne_of_gt hd
  have heq : (12 / 25 - h / 5) / (3 / 5 - h) - 4 / 5 =
      (3 / 5 * h) / (3 / 5 - h) := by
    calc
      _ = (12 / 25 - h / 5) / (3 / 5 - h) -
          ((4 / 5) * (3 / 5 - h)) / (3 / 5 - h) := by
            rw [mul_div_cancel_right₀ _ hdn]
      _ = ((12 / 25 - h / 5) - (4 / 5) * (3 / 5 - h)) /
          (3 / 5 - h) := div_sub_div_same _ _ _
      _ = _ := by congr 1; ring
  rw [heq, abs_div, abs_of_pos hd, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)]
  rw [div_le_iff₀ hd]
  nlinarith

/-- The target feature retains the one-tenth singular-value margin throughout the
small labelled-path neighborhood. -/
-- @node: pathTargetFeature_rankMargin
lemma pathTargetFeature_rankMargin (h : ℝ) (hh : |h| ≤ 1 / 100) :
    (1 / 10 : ℝ) ≤ signalMinSingular (pathTargetFeature h) := by
  let d := (12 / 25 - h / 5) / (3 / 5 - h) - 4 / 5
  have hdecomp : pathTargetFeature h =
      pathTargetFeature 0 + !![(0 : ℝ), 0; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pathTargetFeature, d] <;> ring
  have hw := singular_value_weyl (j := 1) (pathTargetFeature 0)
    (!![(0 : ℝ), 0; 0, d])
  have hdn : ‖matrixCLM (!![(0 : ℝ), 0; 0, d])‖ ≤ 1 / 50 :=
    (path_lowerRight_opNorm d).trans (pathTargetFeature_entry_displacement h hh)
  rw [← hdecomp] at hw
  have habs := abs_le.mp hw
  have hb := pathTargetFeature_zero_strictRank
  unfold signalMinSingular at *
  linarith

/-- Each undisplaced reference feature has enough strict singular-value slack to
absorb the labelled-path perturbation. -/
-- @node: baseReferenceFeature_strictRank
lemma baseReferenceFeature_strictRank (t : Bool) :
    (1 / 5 : ℝ) ≤ signalMinSingular (baseReferenceFeature t) := by
  apply signalMinSingular_lower_fin_two _ _ (by norm_num)
  intro x
  cases t
  · simp [baseReferenceFeature, Fin.sum_univ_two]
    nlinarith [sq_nonneg (3 * x 0 - 7 * x 1)]
  · simp [baseReferenceFeature, Fin.sum_univ_two]
    nlinarith [sq_nonneg (7 * x 0 - 15 * x 1)]

/-- The varying lower-left reference-feature entry remains within one fiftieth of
its undisplaced value in either treatment arm. -/
-- @node: pathReferenceFeature_entry_displacement
lemma pathReferenceFeature_entry_displacement (t : Bool) (h : ℝ)
    (hh : |h| ≤ 1 / 100) :
    |(if t then (225 * h + 28) / (20 * (15 * h + 4)) - 7 / 20
      else (35 * h + 9) / (10 * (5 * h + 3)) - 3 / 10)| ≤ 1 / 50 := by
  have hb := abs_le.mp hh
  cases t
  · simp only [Bool.false_eq_true, if_false]
    have hd : 0 < 10 * (5 * h + 3) := by nlinarith
    have hdn : 10 * (5 * h + 3) ≠ 0 := ne_of_gt hd
    have heq : (35 * h + 9) / (10 * (5 * h + 3)) - 3 / 10 =
        (20 * h) / (10 * (5 * h + 3)) := by
      calc
        _ = (35 * h + 9) / (10 * (5 * h + 3)) -
            ((3 / 10) * (10 * (5 * h + 3))) / (10 * (5 * h + 3)) := by
              rw [mul_div_cancel_right₀ _ hdn]
        _ = ((35 * h + 9) - (3 / 10) * (10 * (5 * h + 3))) /
            (10 * (5 * h + 3)) := div_sub_div_same _ _ _
        _ = _ := by congr 1; ring
    rw [heq, abs_div, abs_of_pos hd, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20)]
    rw [div_le_iff₀ hd]
    nlinarith
  · simp only [if_true]
    have hd : 0 < 20 * (15 * h + 4) := by nlinarith
    have hdn : 20 * (15 * h + 4) ≠ 0 := ne_of_gt hd
    have heq : (225 * h + 28) / (20 * (15 * h + 4)) - 7 / 20 =
        (120 * h) / (20 * (15 * h + 4)) := by
      calc
        _ = (225 * h + 28) / (20 * (15 * h + 4)) -
            ((7 / 20) * (20 * (15 * h + 4))) / (20 * (15 * h + 4)) := by
              rw [mul_div_cancel_right₀ _ hdn]
        _ = ((225 * h + 28) - (7 / 20) * (20 * (15 * h + 4))) /
            (20 * (15 * h + 4)) := div_sub_div_same _ _ _
        _ = _ := by congr 1; ring
    rw [heq, abs_div, abs_of_pos hd, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 120)]
    rw [div_le_iff₀ hd]
    nlinarith

/-- Both reference features retain the one-tenth singular-value margin throughout
the small labelled-path neighborhood. -/
-- @node: pathReferenceFeature_rankMargin
lemma pathReferenceFeature_rankMargin (t : Bool) (h : ℝ) (hh : |h| ≤ 1 / 100) :
    (1 / 10 : ℝ) ≤ signalMinSingular (pathReferenceFeature t h) := by
  let d := if t then (225 * h + 28) / (20 * (15 * h + 4)) - 7 / 20
    else (35 * h + 9) / (10 * (5 * h + 3)) - 3 / 10
  have hdecomp : pathReferenceFeature t h =
      baseReferenceFeature t + !![(0 : ℝ), 0; d, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> cases t
    all_goals simp [baseReferenceFeature, d,
      pathReferenceFeature_first_formula _ _ _ hh,
      pathReferenceFeature_second_formula _ _ _ hh]
  have hw := singular_value_weyl (j := 1) (baseReferenceFeature t)
    (!![(0 : ℝ), 0; d, 0])
  have hdn : ‖matrixCLM (!![(0 : ℝ), 0; d, 0])‖ ≤ 1 / 50 :=
    (path_lowerLeft_opNorm d).trans (pathReferenceFeature_entry_displacement t h hh)
  rw [← hdecomp] at hw
  have habs := abs_le.mp hw
  have hb := baseReferenceFeature_strictRank t
  unfold signalMinSingular at *
  linarith

/-- The factorization-preserving path has the full proxy-rank certificate required
by the uniformly conditioned model. -/
-- @node: path_proxyRankMargin
lemma path_proxyRankMargin (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : ProxyRankMargin (sigma0 := 1 / 10) (pathLaw g h) := by
  unfold ProxyRankMargin
  rw [show referenceFeature (pathLaw g h) false = pathReferenceFeature false h from
      path_referenceFeature g h hg0 hg1 hh false,
    show referenceFeature (pathLaw g h) true = pathReferenceFeature true h from
      path_referenceFeature g h hg0 hg1 hh true,
    path_targetFeature g h hg0 hg1 hh]
  exact ⟨pathReferenceFeature_rankMargin false h hh,
    pathReferenceFeature_rankMargin true h hh, pathTargetFeature_rankMargin h hh⟩

/-- Every sufficiently small labelled-path displacement remains in the uniformly
conditioned model, uniformly over the displayed gap range. -/
-- @node: path_ucvmwModel
lemma path_ucvmwModel (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg0 hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (pathLaw g h) := by
  letI := pathLaw_isProbabilityMeasure g h hg0 hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  exact
    { coreDomain := by norm_num [CoreParameterDomain]
      referenceProxySeparation := path_referenceProxySeparation g h hg0 hg1 hh
      targetProxySeparation := path_targetProxySeparation g h hg0 hg1 hh
      consistency := path_consistency g h
      latentIgnorability := path_armwiseLatentIgnorability g h hg0 hg1 hh
      anchor := path_anchor g h
      boundedX := path_boundedX g h
      boundedProxyProduct := path_boundedProxyProduct g h
      boundedOutcomeProxyProduct := path_boundedOutcomeProxyProduct g h
      latentArmPositivity := path_latentArmPositivity g h hg0 hg1 hh
      proxyRankMargin := path_proxyRankMargin g h hg0 hg1 hh }

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
