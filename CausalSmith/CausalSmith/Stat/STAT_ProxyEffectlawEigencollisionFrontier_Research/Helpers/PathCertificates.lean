import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessValidity

/-! Paper-local finite-sum and model certificates for the factorization-preserving labelled path. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-! ### Certificates for the labelled path -/

/-- At zero displacement, the labelled path is exactly the collision witness with
effect amplitude `g / 2`. -/
-- @node: pathWeight_zero
lemma pathWeight_zero (g : ℝ) (u : Fin 2) (t x z y0 y1 : Bool) :
    pathWeight g 0 u t x z y0 y1 = witnessWeight (g / 2) u t x z y0 y1 := by
  unfold pathWeight
  rw [pathReferenceFeature_second_formula t 0 u (by norm_num)]
  rw [pathArmWeights_formula true 0 u (by norm_num)]
  fin_cases u <;> cases t <;> cases x <;> cases z <;> cases y0 <;> cases y1 <;>
    norm_num [pathTargetFeature, witnessWeight, bernoulliMass]

/-- The base labelled-path measure is the already validated collision witness. -/
-- @node: pathLaw_zero
lemma pathLaw_zero (g : ℝ) : pathLaw g 0 = witnessLaw (g / 2) := by
  simp_rw [pathLaw, witnessLaw, pathPoint, pathWeight_zero g]

/-- The undisplaced labelled path inherits uniformly conditioned model validity from the
collision witness. -/
-- @node: pathLaw_zero_ucvmwModel
lemma pathLaw_zero_ucvmwModel (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4) :
    letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
      (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (pathLaw g 0) := by
  letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
    (by norm_num [TangentAmplitudeDomain]) (by norm_num)
  letI : IsProbabilityMeasure (witnessLaw (g / 2)) :=
    witnessLaw_isProbabilityMeasure (g / 2) (by positivity) (by linarith)
  have hM := witness_ucvmwModel (g / 2) (by positivity) (by linarith)
  simpa only [pathLaw_zero g] using hM

/-- Every atomic coefficient of the labelled path is nonnegative on the small rational
neighborhood used by the lower-bound construction. -/
-- @node: pathWeight_nonneg
lemma pathWeight_nonneg (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) (t x z y0 y1 : Bool) :
    0 ≤ pathWeight g h u t x z y0 y1 := by
  have hbounds := abs_le.mp hh
  have hpu : ∀ u : Fin 2,
      0 ≤ (if u.val = 0 then 2 / 5 + h else 3 / 5 - h : ℝ) ∧
      (if u.val = 0 then 2 / 5 + h else 3 / 5 - h : ℝ) ≤ 1 := by
    intro v
    fin_cases v <;> simp <;> constructor <;> nlinarith [hbounds.1, hbounds.2]
  have hpt : ∀ u : Fin 2,
      0 ≤ pathArmWeights true h u /
        (if u.val = 0 then 2 / 5 + h else 3 / 5 - h) ∧
      pathArmWeights true h u /
        (if u.val = 0 then 2 / 5 + h else 3 / 5 - h) ≤ 1 := by
    intro v
    rw [pathArmWeights_formula true h v hh]
    fin_cases v <;> simp
    all_goals constructor
    all_goals first
      | apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      | rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpx : ∀ u : Fin 2,
      0 ≤ pathTargetFeature h 1 u ∧ pathTargetFeature h 1 u ≤ 1 := by
    intro v
    fin_cases v
    · norm_num [pathTargetFeature]
    · simp [pathTargetFeature]
      constructor
      · apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      · rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpz : ∀ (t : Bool) (u : Fin 2),
      0 ≤ pathReferenceFeature t h 1 u ∧ pathReferenceFeature t h 1 u ≤ 1 := by
    intro s v
    rw [pathReferenceFeature_second_formula s h v hh]
    fin_cases v <;> cases s <;> simp
    all_goals constructor
    all_goals first
      | apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      | rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpy1 : ∀ u : Fin 2,
      0 ≤ (if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2 : ℝ) ∧
      (if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2 : ℝ) ≤ 1 := by
    intro v
    fin_cases v <;> simp <;> constructor <;> nlinarith
  unfold pathWeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (hpu u).1
            (bernoulliMass_nonneg _ t (hpt u).1 (hpt u).2))
          (bernoulliMass_nonneg _ x (hpx u).1 (hpx u).2))
        (bernoulliMass_nonneg _ z (hpz t u).1 (hpz t u).2))
      (bernoulliMass_nonneg (1 / 4) y0 (by norm_num) (by norm_num)))
    (bernoulliMass_nonneg _ y1 (hpy1 u).1 (hpy1 u).2)

/-- Summing every nuisance coordinate of the labelled path leaves its prescribed latent mass. -/
-- @node: pathWeight_sum_nuisance
lemma pathWeight_sum_nuisance (g h : ℝ) (u : Fin 2) :
    ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h u t x z y0 y1 =
      if u.val = 0 then 2 / 5 + h else 3 / 5 - h := by
  simp only [pathWeight, sum_mul_bernoulliMass]

/-- Restricted event masses under the labelled path reduce to the defining finite sum. -/
-- @node: pathLaw_real
lemma pathLaw_real (g h : ℝ) (A : Set (FullData 2 2 2))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (pathLaw g h).real A =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (pathWeight g h u t x z y0 y1)).toReal *
          if pathPoint u t x z y0 y1 ∈ A then 1 else 0 := by
  classical
  let c : Fin 2 × Bool × Bool × Bool × Bool × Bool → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (pathWeight g h i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1
      i.2.2.2.2.2)
  let p : Fin 2 × Bool × Bool × Bool × Bool × Bool → FullData 2 2 2 := fun i =>
    pathPoint i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2
  have hpath : pathLaw g h = ∑ i, c i • Measure.dirac (p i) := by
    simp only [pathLaw, c, p, Fintype.sum_prod_type]
  rw [show (pathLaw g h).real A = ∫ _ in A, (1 : ℝ) ∂pathLaw g h by simp]
  rw [← integral_indicator hA, hpath, integral_finsetSum_measure]
  · simp only [c, p, Fintype.sum_prod_type, integral_smul_measure, integral_dirac,
      smul_eq_mul, Set.indicator_apply]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp [c])

/-- The observed support point indexed by the four visible Bernoulli coordinates. -/
-- @node: pathObsPoint
def pathObsPoint (t x z y : Bool) : Obs 2 2 :=
  ⟨t, vec2 1 (boolReal x), vec2 1 (boolReal z), boolReal y⟩

/-- Indicator that a visible Bernoulli support point is the requested observed record. -/
-- @node: pathObsIndicator
noncomputable def pathObsIndicator (t x z y : Bool) (o : Obs 2 2) : ℝ := by
  classical
  exact if pathObsPoint t x z y = o then 1 else 0

/-- Singletons of the observed carrier are measurable in its induced Borel structure. -/
-- @node: measurableSet_singleton_obs
lemma measurableSet_singleton_obs (o : Obs 2 2) : MeasurableSet ({o} : Set (Obs 2 2)) := by
  change @MeasurableSet (Obs 2 2)
    (MeasurableSpace.comap Obs.toCoordinates inferInstance) {o}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{Obs.toCoordinates o}, measurableSet_singleton _, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    cases x
    cases o
    simp_all [Obs.toCoordinates]
  · exact fun h => congrArg Obs.toCoordinates h

/-- Every observed-cell mass is the explicit finite sum over the path atoms mapping to that cell. -/
-- @node: pathObservedCellMass_formula
lemma pathObservedCellMass_formula (g h : ℝ) (o : Obs 2 2) :
    pathObservedCellMass g h o =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (pathWeight g h u t x z y0 y1)).toReal *
          pathObsIndicator t x z (if t then y1 else y0) o := by
  classical
  rw [pathObservedCellMass, pathLaw_real]
  · congr 1
  · exact (measurableSet_singleton_obs o).preimage (obsMap_measurable 2 2 2)

/-- The finite observed-cell formula after summing out the inactive potential outcome and the
latent class. -/
-- @node: pathVisibleMass
noncomputable def pathVisibleMass (g h : ℝ) (t x z y : Bool) : ℝ :=
  if t then ∑ u : Fin 2, ∑ y0 : Bool, pathWeight g h u true x z y0 y
  else ∑ u : Fin 2, ∑ y1 : Bool, pathWeight g h u false x z y y1

set_option maxHeartbeats 800000

/-- Exact visible-cell displacement along the labelled path.  The control arm is fixed,
while each treated-arm cell changes by an explicit multiple of `g * h`. -/
-- @node: pathVisibleMass_diff_formula
lemma pathVisibleMass_diff_formula (g h : ℝ) (hh : |h| ≤ 1 / 100)
    (t x z y : Bool) :
    pathVisibleMass g h t x z y - pathVisibleMass g 0 t x z y =
      if t then (if y then -1 else 1) *
        (if x then (if z then 9 / 100 else 3 / 100)
          else (if z then 9 / 25 else 3 / 25)) * g * h
      else 0 := by
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 15 * h + 4 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 5 * h + 3 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4' : 4 + h * 15 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3' : 3 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h2p : 2 + h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3m : 3 - h * 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h50p : 50 + h * 125 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h75m : 75 - h * 125 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h80p : 80 + h * 300 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h30p : 30 + h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h20p : 20 + h * 75 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h30m : 30 - h * 50 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h45m : 45 - h * 75 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hprod : 8 + h * 50 + h ^ 2 * 75 ≠ 0 := by
    rw [show 8 + h * 50 + h ^ 2 * 75 = (2 + h * 5) * (4 + h * 15) by ring]
    exact mul_ne_zero h2p h4'
  cases t <;> cases x <;> cases z <;> cases y
  all_goals
    simp only [pathVisibleMass, Fin.sum_univ_two, Fintype.sum_bool, pathWeight,
      if_false, if_true, bernoulliMass]
    repeat' first
      | rw [pathArmWeights_formula true h 0 hh]
      | rw [pathArmWeights_formula true h 1 hh]
      | rw [pathReferenceFeature_second_formula false h 0 hh]
      | rw [pathReferenceFeature_second_formula false h 1 hh]
      | rw [pathReferenceFeature_second_formula true h 0 hh]
      | rw [pathReferenceFeature_second_formula true h 1 hh]
      | rw [pathArmWeights_formula true 0 0 (by norm_num)]
      | rw [pathArmWeights_formula true 0 1 (by norm_num)]
      | rw [pathReferenceFeature_second_formula false 0 0 (by norm_num)]
      | rw [pathReferenceFeature_second_formula false 0 1 (by norm_num)]
      | rw [pathReferenceFeature_second_formula true 0 0 (by norm_num)]
      | rw [pathReferenceFeature_second_formula true 0 1 (by norm_num)]
  all_goals
    norm_num [pathTargetFeature]
    try simp_rw [inv_eq_one_div]
    field_simp [hp0, hp1, h4, h3, h2p, h3m, h50p, h75m, h80p,
      h30p, h20p, h30m, h45m]
    ring_nf
    field_simp [h2p, h3m, h4, h3, h4', h3', hprod]
    ring

/-- Uniform visible-cell displacement bound, with a numerical constant independent of the cell. -/
-- @node: pathVisibleMass_diff_bound
lemma pathVisibleMass_diff_bound (g h : ℝ) (hg0 : 0 ≤ g) (hh : |h| ≤ 1 / 100)
    (t x z y : Bool) :
    |pathVisibleMass g h t x z y - pathVisibleMass g 0 t x z y| ≤ g * |h| := by
  rw [pathVisibleMass_diff_formula g h hh t x z y]
  cases t <;> cases x <;> cases z <;> cases y
  all_goals
    norm_num only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte,
      if_false, if_true, abs_zero, abs_one, abs_neg]
    repeat' rw [abs_mul]
    try rw [abs_of_nonneg hg0]
    norm_num
    linarith [mul_nonneg hg0 (abs_nonneg h)]

/-- An observed singleton mass is the sum of the sixteen visible Bernoulli-cell masses
selected by that singleton. -/
-- @node: pathObservedCellMass_visible_formula
lemma pathObservedCellMass_visible_formula (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (o : Obs 2 2) :
    pathObservedCellMass g h o =
      ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y : Bool,
        pathVisibleMass g h t x z y * pathObsIndicator t x z y o := by
  classical
  rw [pathObservedCellMass_formula]
  simp_rw [ENNReal.toReal_ofReal (pathWeight_nonneg g h hg0 hg1 hh _ _ _ _ _ _)]
  simp only [pathVisibleMass, pathObsIndicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  cases t
  · simp only [Bool.false_eq_true, if_false]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  · simp only [if_true]
    calc
      (∑ u : Fin 2, ∑ y0 : Bool, ∑ y1 : Bool,
          pathWeight g h u true x z y0 y1 *
            (if pathObsPoint true x z y1 = o then 1 else 0)) =
          ∑ u : Fin 2, ∑ y1 : Bool, ∑ y0 : Bool,
            pathWeight g h u true x z y0 y1 *
              (if pathObsPoint true x z y1 = o then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.sum_comm]
      _ = ∑ y1 : Bool, ∑ u : Fin 2, ∑ y0 : Bool,
            pathWeight g h u true x z y0 y1 *
              (if pathObsPoint true x z y1 = o then 1 else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ y : Bool,
          (∑ u : Fin 2, ∑ y0 : Bool, pathWeight g h u true x z y0 y) *
            (if pathObsPoint true x z y = o then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            split_ifs <;> simp

/-- Uniform observed-singleton displacement bound along the labelled path. -/
-- @node: pathObservedCellMass_diff_bound
lemma pathObservedCellMass_diff_bound (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (o : Obs 2 2) :
    |pathObservedCellMass g h o - pathObservedCellMass g 0 o| ≤ 16 * g * |h| := by
  classical
  rw [pathObservedCellMass_visible_formula g h hg0 hg1 hh o,
    pathObservedCellMass_visible_formula g 0 hg0 hg1 (by norm_num) o]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t : Bool, |∑ x : Bool, ∑ z : Bool, ∑ y : Bool,
        (pathVisibleMass g h t x z y * pathObsIndicator t x z y o -
          pathVisibleMass g 0 t x z y * pathObsIndicator t x z y o)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Bool, ∑ x : Bool, |∑ z : Bool, ∑ y : Bool,
        (pathVisibleMass g h t x z y * pathObsIndicator t x z y o -
          pathVisibleMass g 0 t x z y * pathObsIndicator t x z y o)| := by
      apply Finset.sum_le_sum
      intro t _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, |∑ y : Bool,
        (pathVisibleMass g h t x z y * pathObsIndicator t x z y o -
          pathVisibleMass g 0 t x z y * pathObsIndicator t x z y o)| := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro x _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y : Bool,
        |pathVisibleMass g h t x z y * pathObsIndicator t x z y o -
          pathVisibleMass g 0 t x z y * pathObsIndicator t x z y o| := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Bool, ∑ _x : Bool, ∑ _z : Bool, ∑ _y : Bool, g * |h| := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro y _
      rw [← sub_mul, abs_mul]
      unfold pathObsIndicator
      split_ifs
      · simpa using pathVisibleMass_diff_bound g h hg0 hh t x z y
      · simp [mul_nonneg hg0 (abs_nonneg h)]
    _ = 16 * g * |h| := by simp; ring

/-- Every one of the sixteen visible cells of the base path has a uniform positive mass. -/
-- @node: pathVisibleMass_base_floor
lemma pathVisibleMass_base_floor (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (t x z y : Bool) : 1 / 1000 ≤ pathVisibleMass g 0 t x z y := by
  cases t <;> cases x <;> cases z <;> cases y
  all_goals
    simp [pathVisibleMass, pathWeight, pathTargetFeature,
      pathArmWeights_formula _ 0 _ (by norm_num),
      pathReferenceFeature_second_formula _ 0 _ (by norm_num), bernoulliMass]
    nlinarith

/-- Every represented observed atom of the base path inherits the uniform visible-cell floor. -/
-- @node: pathObservedCellMass_base_floor
lemma pathObservedCellMass_base_floor (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (t x z y : Bool) :
    1 / 1000 ≤ pathObservedCellMass g 0 (pathObsPoint t x z y) := by
  rw [pathObservedCellMass_visible_formula g 0 hg0 hg1 (by norm_num)]
  have hterm : pathVisibleMass g 0 t x z y ≤
      ∑ t' : Bool, ∑ x' : Bool, ∑ z' : Bool, ∑ y' : Bool,
        pathVisibleMass g 0 t' x' z' y' *
          pathObsIndicator t' x' z' y' (pathObsPoint t x z y) := by
    classical
    have hnonneg (t' x' z' y' : Bool) :
        0 ≤ pathVisibleMass g 0 t' x' z' y' *
          pathObsIndicator t' x' z' y' (pathObsPoint t x z y) := by
      unfold pathObsIndicator
      split_ifs
      · exact mul_nonneg (le_trans (by norm_num) (pathVisibleMass_base_floor g hg0 hg1 _ _ _ _))
          (by norm_num)
      · simp
    calc
      pathVisibleMass g 0 t x z y =
          pathVisibleMass g 0 t x z y *
            pathObsIndicator t x z y (pathObsPoint t x z y) := by
              simp [pathObsIndicator]
      _ ≤ ∑ y' : Bool, pathVisibleMass g 0 t x z y' *
            pathObsIndicator t x z y' (pathObsPoint t x z y) :=
          Finset.single_le_sum (fun y' _ => hnonneg t x z y') (Finset.mem_univ y)
      _ ≤ ∑ z' : Bool, ∑ y' : Bool, pathVisibleMass g 0 t x z' y' *
            pathObsIndicator t x z' y' (pathObsPoint t x z y) :=
          Finset.single_le_sum (fun z' _ => Finset.sum_nonneg fun y' _ => hnonneg t x z' y')
            (Finset.mem_univ z)
      _ ≤ ∑ x' : Bool, ∑ z' : Bool, ∑ y' : Bool,
            pathVisibleMass g 0 t x' z' y' *
              pathObsIndicator t x' z' y' (pathObsPoint t x z y) :=
          Finset.single_le_sum
            (fun x' _ => Finset.sum_nonneg fun z' _ => Finset.sum_nonneg fun y' _ =>
              hnonneg t x' z' y') (Finset.mem_univ x)
      _ ≤ ∑ t' : Bool, ∑ x' : Bool, ∑ z' : Bool, ∑ y' : Bool,
            pathVisibleMass g 0 t' x' z' y' *
              pathObsIndicator t' x' z' y' (pathObsPoint t x z y) :=
          Finset.single_le_sum
            (fun t' _ => Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ =>
              Finset.sum_nonneg fun y' _ => hnonneg t' x' z' y') (Finset.mem_univ t)
  exact le_trans (pathVisibleMass_base_floor g hg0 hg1 t x z y) hterm

/- The finite path sum restricted to a latent-class cylinder selects that class. -/
-- @node: path_sum_restrict_latentClass
lemma path_sum_restrict_latentClass (g h : ℝ) (u : Fin 2)
    [dA : DecidablePred (· ∈ latentClass u)] (F : FullData 2 2 2 → ℝ) :
    (∑ v : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h v t x z y0 y1 *
        @ite ℝ (pathPoint v t x z y0 y1 ∈ latentClass u)
          (dA (pathPoint v t x z y0 y1)) (F (pathPoint v t x z y0 y1)) 0) =
    ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h u t x z y0 y1 * F (pathPoint u t x z y0 y1) := by
  classical
  rw [Finset.sum_eq_single u]
  · have hin (t x z y0 y1 : Bool) : pathPoint u t x z y0 y1 ∈ latentClass u := by
      simp [latentClass, pathPoint, witnessPoint]
    simp_rw [if_pos (hin _ _ _ _ _)]
  · intro v _ hvu
    have hout (t x z y0 y1 : Bool) : pathPoint v t x z y0 y1 ∉ latentClass u := by
      simp [latentClass, pathPoint, witnessPoint, hvu]
    simp_rw [if_neg (hout _ _ _ _ _)]
    simp
  · simp

/-- The labelled path has exactly the displaced latent masses prescribed in its construction. -/
-- @node: path_latentMass
lemma path_latentMass (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) :
    latentMass (pathLaw g h) u = if u.val = 0 then 2 / 5 + h else 3 / 5 - h := by
  classical
  rw [latentMass, pathLaw_real g h _ (measurableSet_witness_latentClass u)]
  simp_rw [ENNReal.toReal_ofReal (pathWeight_nonneg g h hg0 hg1 hh _ _ _ _ _ _)]
  rw [path_sum_restrict_latentClass g h u (fun _ => (1 : ℝ))]
  simp only [mul_one]
  exact pathWeight_sum_nuisance g h u

/-- The ordered-mass target moves by exactly twice the absolute tangent displacement. -/
-- @node: path_latentMass_l1_displacement
lemma path_latentMass_l1_displacement (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    (∑ i, |latentMass (pathLaw g h) i - latentMass (pathLaw g 0) i|) = 2 * |h| := by
  simp_rw [path_latentMass g h hg0 hg1 hh,
    path_latentMass g 0 hg0 hg1 (by norm_num)]
  rw [Fin.sum_univ_two]
  norm_num
  ring

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
