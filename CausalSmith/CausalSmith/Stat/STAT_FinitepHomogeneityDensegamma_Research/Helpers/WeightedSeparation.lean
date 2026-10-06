module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MeanErrorBounds

/-! Cell-average positivity and diagonal geometry for the weighted mean separation bound. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A histogram projection is constant on each of its cells. This statement assumes [the hJ condition](hyp:hJ), [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: projOp_eq_on_cell
lemma projOp_eq_on_cell (J : ℕ) (hJ : 0 < J) (f : unitInterval → ℝ)
    (j : Fin J) (x z : unitInterval) (hx : x ∈ cell J j) (hz : z ∈ cell J j) :
    projOp J f x = projOp J f z := by
  unfold projOp
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [histogram_kernel_row J hJ x j hx y, histogram_kernel_row J hJ z j hz y])

/-- Histogram cell averages preserve a two-sided scalar envelope. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: projOp_range_of_range
lemma projOp_range_of_range (J : ℕ) (hJ : 0 < J) (f : unitInterval → ℝ)
    (hf : Integrable f design) (lo hi : ℝ) (hb : ∀ x, lo ≤ f x ∧ f x ≤ hi)
    (x : unitInterval) : lo ≤ projOp J f x ∧ projOp J f x ≤ hi := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hc (c : ℝ) : (∫ z, projKernel J x z*c ∂design) = c := by
    rw [integral_mul_const, (projection_rows J hJ x).1, one_mul]
  have hp (z : unitInterval) : 0 ≤ projKernel J x z := by
    obtain ⟨j, hj, _⟩ := histogram_cell_unique J hJ x
    rw [histogram_kernel_row J hJ x j hj z]
    split_ifs <;> positivity
  have hconst (c : ℝ) : Integrable (fun z => projKernel J x z*c) design :=
    integrable_histogram_row_mul J hJ x _ (integrable_const c)
  constructor
  · rw [← hc lo]
    exact integral_mono (hconst lo) (integrable_histogram_row_mul J hJ x f hf)
      (fun z => mul_le_mul_of_nonneg_left (hb z).1 (hp z))
  · rw [← hc hi]
    exact integral_mono (integrable_histogram_row_mul J hJ x f hf) (hconst hi)
      (fun z => mul_le_mul_of_nonneg_left (hb z).2 (hp z))

/-- A cellwise constant factor can be pulled through a histogram average. This statement assumes [the hJ condition](hyp:hJ), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: projOp_mul_cellwise
lemma projOp_mul_cellwise (J : ℕ) (hJ : 0 < J) (f g : unitInterval → ℝ)
    (hg : ∀ j : Fin J, ∀ x ∈ cell J j, ∀ z ∈ cell J j, g z=g x)
    (x : unitInterval) :
    projOp J (fun z => f z*g z) x = projOp J f x*g x := by
  obtain ⟨j, hj, _⟩ := histogram_cell_unique J hJ x
  unfold projOp
  rw [← integral_mul_const]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [histogram_kernel_row J hJ x j hj z]
  by_cases hz : z ∈ cell J j
  · rw [if_pos hz, hg j x hj z hz]
    ring
  · simp [hz]

/-- Overlap is preserved by the exact propensity projection. This statement assumes [the ho condition](hyp:ho), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: projected_propensity_overlap
lemma projected_propensity_overlap (law : ObservedLaw) (ho : Overlap law)
    (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    1/4 ≤ projOp K law.e x ∧ projOp K law.e x ≤ 3/4 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hi : Integrable (fun x => law.e x) design := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (law.e_range x).1]
      exact (law.e_range x).2)
  exact projOp_range_of_range K hK law.e hi (1/4) (3/4) ho x

/-- The fine-cell average of the original propensity weight is its Bernoulli variance. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: projected_propensity_weight_identity
lemma projected_propensity_weight_identity (law : ObservedLaw) (K : ℕ) (hK : 0 < K)
    (x : unitInterval) :
    projOp K (fun z => law.e z*(1-projOp K law.e z)) x =
      projOp K law.e x*(1-projOp K law.e x) := by
  apply projOp_mul_cellwise K hK
  intro j y hy z hz
  rw [projOp_eq_on_cell K hK law.e j z y hz hy]

/-- Fine-cell average weights are bounded below by three sixteenths. This statement assumes [the ho condition](hyp:ho), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: projected_propensity_weight_range
lemma projected_propensity_weight_range (law : ObservedLaw) (ho : Overlap law)
    (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    3/16 ≤ projOp K (fun z => law.e z*(1-projOp K law.e z)) x ∧
      projOp K (fun z => law.e z*(1-projOp K law.e z)) x ≤ 1/4 := by
  rw [projected_propensity_weight_identity law K hK x]
  have he := projected_propensity_overlap law ho K hK x
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr he.2)]
  · nlinarith [sq_nonneg (projOp K law.e x-1/2)]

/-- The original weight is uniformly bounded without regularity of any clipped mean. This statement assumes [the ho condition](hyp:ho), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: propensity_weight_abs_le
lemma propensity_weight_abs_le (law : ObservedLaw) (ho : Overlap law)
    (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    |law.e x*(1-projOp K law.e x)| ≤ 9/16 := by
  have he := ho x
  have hp := projected_propensity_overlap law ho K hK x
  rw [abs_of_nonneg (by
    exact mul_nonneg (by linarith [he.1]) (by linarith [hp.2]) : 0 ≤ law.e x*(1-projOp K law.e x))]
  nlinarith [mul_le_mul he.2 (show 1-projOp K law.e x ≤ 3/4 by linarith)
    (show 0 ≤ 1-projOp K law.e x by linarith) (by norm_num : (0:ℝ) ≤ 3/4)]

/-- Nested coarse-cell averages retain the fine-cell weight lower bound. This statement assumes [the ho condition](hyp:ho), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: coarse_propensity_weight_range
lemma coarse_propensity_weight_range (law : ObservedLaw) (ho : Overlap law)
    (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K) (x : unitInterval) :
    3/16 ≤ projOp J (fun z => law.e z*(1-projOp K law.e z)) x ∧
      projOp J (fun z => law.e z*(1-projOp K law.e z)) x ≤ 1/4 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let w := fun z => law.e z*(1-projOp K law.e z)
  have hi : Integrable w design := by
    apply (integrable_const (9/16:ℝ)).mono' (by dsimp [w]; fun_prop)
    exact ae_of_all _ (fun z => by simpa [w] using propensity_weight_abs_le law ho K hK z)
  have hpi : Integrable (projOp K w) design := by
    apply (integrable_const (1/4:ℝ)).mono' (by dsimp [w]; fun_prop)
    exact ae_of_all _ (fun z => by
      have hh := projected_propensity_weight_range law ho K hK z
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [w]; linarith [hh.1])]
      exact hh.2)
  rw [← congrFun (projection_nesting J K hJ hJK hK w hi) x]
  exact projOp_range_of_range J hJ (projOp K w) hpi (3/16) (1/4)
    (projected_propensity_weight_range law ho K hK) x

/-- Integrating a scalar coefficient against a feature extracts its cell integral. This statement assumes [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: histogram_coefficient_coordinate
lemma histogram_coefficient_coordinate (J : ℕ) (f : unitInterval → ℝ)
    (hf : Integrable f design) (hfm : Measurable f) (j : Fin J) :
    (∫ x, f x • featureMap J x ∂design) j =
      Real.sqrt J * ∫ x in cell J j, f x ∂design := by
  have hi := integrable_feature_coefficient J f hf hfm
  have he := (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ x, (f x • featureMap J x) j ∂design) =
    (∫ x, f x • featureMap J x ∂design) j at he
  rw [← he, ← integral_const_mul, ← integral_indicator (measurableSet_histogram_cell J j)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    simp only [PiLp.smul_apply, featureMap, PiLp.toLp_apply, smul_eq_mul]
    by_cases hx : x ∈ cell J j <;> simp [hx, mul_comm])

/-- Every positive-rank histogram cell contains a point. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: histogram_cell_nonempty
lemma histogram_cell_nonempty (J : ℕ) (hJ : 0 < J) (j : Fin J) :
    (cell J j).Nonempty := by
  apply nonempty_of_measure_ne_zero (μ := design)
  rw [histogram_cell_volume J hJ j]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

/-- Cellwise constant signals are multiplied diagonally by cell-average weights. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hw condition](hyp:hw), [the hfw condition](hyp:hfw), [the hfm condition](hyp:hfm), [the hwm condition](hyp:hwm), [the hcell condition](hyp:hcell), [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: weighted_histogram_coefficient_coordinate
lemma weighted_histogram_coefficient_coordinate (J : ℕ) (hJ : 0 < J)
    (f w : unitInterval → ℝ) (hf : Integrable f design) (hw : Integrable w design)
    (hfw : Integrable (fun x => w x*f x) design) (hfm : Measurable f) (hwm : Measurable w)
    (hcell : ∀ j : Fin J, ∀ x ∈ cell J j, ∀ z ∈ cell J j, f z=f x)
    (j : Fin J) (x : unitInterval) (hx : x ∈ cell J j) :
    (∫ z, (w z*f z) • featureMap J z ∂design) j =
      projOp J w x*(∫ z, f z • featureMap J z ∂design) j := by
  have hmass : design.real (cell J j) = (J:ℝ)⁻¹ := by
    rw [Measure.real, histogram_cell_volume J hJ j, ENNReal.toReal_ofReal (by positivity)]
  have hfc : (∫ z in cell J j, f z ∂design) = (J:ℝ)⁻¹*f x := by
    calc
      _ = ∫ _z in cell J j, f x ∂design := by
        apply setIntegral_congr_fun (measurableSet_histogram_cell J j)
        intro z hz
        exact hcell j x hx z hz
      _ = _ := by rw [setIntegral_const, hmass, smul_eq_mul]
  have hwfc : (∫ z in cell J j, w z*f z ∂design) =
      (∫ z in cell J j, w z ∂design)*f x := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun (measurableSet_histogram_cell J j)
    intro z hz
    dsimp only
    rw [hcell j x hx z hz]
  have hproj : projOp J w x = (J:ℝ)*∫ z in cell J j, w z ∂design := by
    rw [projOp, ← integral_const_mul, ← integral_indicator (measurableSet_histogram_cell J j)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      dsimp only
      rw [histogram_kernel_row J hJ x j hx z]
      by_cases hz : z ∈ cell J j <;> simp [hz])
  rw [histogram_coefficient_coordinate J _ hfw (hwm.mul hfm),
    histogram_coefficient_coordinate J f hf hfm, hfc, hwfc, hproj]
  field_simp

/-- A positive lower bound on the cell-average weights gives a Euclidean norm lower bound. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hw condition](hyp:hw), [the hfw condition](hyp:hfw), [the hfm condition](hyp:hfm), [the hwm condition](hyp:hwm), [the hcell condition](hyp:hcell), [the hk condition](hyp:hk), [the hlower condition](hyp:hlower). [This is the stated conclusion](goal). -/
-- @node: weighted_histogram_coefficient_norm_ge
lemma weighted_histogram_coefficient_norm_ge (J : ℕ) (hJ : 0 < J)
    (f w : unitInterval → ℝ) (hf : Integrable f design) (hw : Integrable w design)
    (hfw : Integrable (fun x => w x*f x) design) (hfm : Measurable f) (hwm : Measurable w)
    (hcell : ∀ j : Fin J, ∀ x ∈ cell J j, ∀ z ∈ cell J j, f z=f x)
    (k : ℝ) (hk : 0 ≤ k) (hlower : ∀ x, k ≤ projOp J w x) :
    k*‖∫ x, f x • featureMap J x ∂design‖ ≤
      ‖∫ x, (w x*f x) • featureMap J x ∂design‖ := by
  let q : Vec J := ∫ x, f x • featureMap J x ∂design
  let r : Vec J := ∫ x, (w x*f x) • featureMap J x ∂design
  have hcoord (j : Fin J) : (k*q j)^2 ≤ (r j)^2 := by
    obtain ⟨x, hx⟩ := histogram_cell_nonempty J hJ j
    have he := weighted_histogram_coefficient_coordinate J hJ f w hf hw hfw hfm hwm hcell j x hx
    change r j = projOp J w x*q j at he
    rw [he, mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hk (hk.trans (hlower x))).mpr (hlower x)) (sq_nonneg _)
  have hs : (k*‖q‖)^2 ≤ ‖r‖^2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_pow] using hcoord j
  nlinarith [norm_nonneg q, norm_nonneg r, mul_nonneg hk (norm_nonneg q)]

/-- The histogram projection is reconstructed from its coefficient vector. This statement assumes [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: projOp_coefficient_reconstruction
lemma projOp_coefficient_reconstruction (J : ℕ) (f : unitInterval → ℝ)
    (hf : Integrable f design) (hfm : Measurable f) (x : unitInterval) :
    projOp J f x = inner ℝ (∫ z, f z • featureMap J z ∂design) (featureMap J x) := by
  rw [real_inner_comm]
  rw [← integral_inner (integrable_feature_coefficient J f hf hfm)]
  simp only [inner_smul_right, projOp, projKernel, smul_eq_mul, mul_comm]

/-- The raw squared norm splits exactly into histogram coefficient and residual energies. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: histogram_projection_energy
lemma histogram_projection_energy (J : ℕ) (hJ : 0 < J) (f : unitInterval → ℝ)
    (hf : MemLp f 2 design) (hfm : Measurable f) :
    (∫ x, f x^2 ∂design) = ‖∫ x, f x • featureMap J x ∂design‖^2 +
      ∫ x, (f x-projOp J f x)^2 ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hfi := hf.integrable (by norm_num)
  let q : Vec J := ∫ x, f x • featureMap J x ∂design
  have he : projOp J f = fun x => inner ℝ q (featureMap J x) := by
    funext x
    exact projOp_coefficient_reconstruction J f hfi hfm x
  have htop : MemLp (fun x => inner ℝ q (featureMap J x)) ∞ design :=
    (featureMap_memLp_top design J id measurable_id).const_inner q
  have hp : MemLp (projOp J f) 2 design := by
    rw [he]
    exact htop.mono_exponent (by simp)
  have hcross : (∫ x, f x*projOp J f x ∂design) = ‖q‖^2 := by
    rw [he]
    calc
      _ = ∫ x, inner ℝ q (f x • featureMap J x) ∂design := by
        simp only [inner_smul_right, smul_eq_mul, mul_comm]
      _ = inner ℝ q q := integral_inner (integrable_feature_coefficient J f hfi hfm) q
      _ = ‖q‖^2 := real_inner_self_eq_norm_sq q
  have henergy : (∫ x, projOp J f x^2 ∂design) = ‖q‖^2 := by
    rw [he]
    exact feature_isometry J hJ q
  have hres : (∫ x, (f x-projOp J f x)^2 ∂design) =
      (∫ x, f x^2 ∂design)-2*(∫ x, f x*projOp J f x ∂design)+
        ∫ x, projOp J f x^2 ∂design := by
    simp_rw [show ∀ x, (f x-projOp J f x)^2 =
      f x^2-2*(f x*projOp J f x)+projOp J f x^2 by intro x; ring]
    have hprod : Integrable (fun x => f x*projOp J f x) design := hf.integrable_mul hp
    have hsub : Integrable (fun x => f x^2-2*(f x*projOp J f x)) design :=
      hf.integrable_sq.sub (hprod.const_mul 2)
    rw [integral_add hsub hp.integrable_sq,
      integral_sub hf.integrable_sq (hprod.const_mul 2), integral_const_mul]
  rw [hcross, henergy] at hres
  change _ = ‖q‖^2+_
  linarith

/-- Subtracting a constant commutes with a positive-rank histogram projection. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: projOp_sub_const
lemma projOp_sub_const (J : ℕ) (hJ : 0 < J) (f : unitInterval → ℝ)
    (hf : Integrable f design) (c : ℝ) (x : unitInterval) :
    projOp J (fun z => f z-c) x = projOp J f x-c := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  unfold projOp
  simp only [mul_sub]
  rw [integral_sub (integrable_histogram_row_mul J hJ x f hf)
    (integrable_histogram_row_mul J hJ x _ (integrable_const c)),
    integral_mul_const, (projection_rows J hJ x).1, one_mul]

/-- The heterogeneity distance is no larger than the uncentered distance to any constant. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: effect_distance_sq_le_const_energy
lemma effect_distance_sq_le_const_energy (law : ObservedLaw) (hc : EffectCap law) (c : ℝ) :
    hetDist law^2 ≤ ∫ x, (law.tau x-c)^2 ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have ht : MemLp (fun x => law.tau x) 2 design :=
    MemLp.of_bound (by fun_prop) (1/2) (ae_of_all _ (fun x => by simpa using hc x))
  have hi := ht.integrable (by norm_num)
  have expand (a : ℝ) : (∫ x, (law.tau x-a)^2 ∂design) =
      (∫ x, law.tau x^2 ∂design)-2*a*meanTau law+a^2 := by
    simp_rw [show ∀ x, (law.tau x-a)^2 = law.tau x^2-(2*a)*law.tau x+a^2 by intro x; ring]
    have hsub : Integrable (fun x => law.tau x^2-(2*a)*law.tau x) design :=
      ht.integrable_sq.sub (hi.const_mul (2*a))
    rw [integral_add hsub (integrable_const _),
      integral_sub ht.integrable_sq (hi.const_mul (2*a)), integral_const_mul]
    simp [meanTau]
  rw [hetDist, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _)),
    expand, expand]
  nlinarith [sq_nonneg (meanTau law-c)]

/-- Histogram approximation leaves at most the stated Holder error in effect distance. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: effect_histogram_coefficient_distance
lemma effect_histogram_coefficient_distance (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J : ℕ) (hJ : 0 < J) (c : ℝ) :
    hetDist law-20*(J:ℝ)^(-v.γ) ≤
      ‖∫ x, (projOp J law.tau x-c) • featureMap J x ∂design‖ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let f := fun x => law.tau x-c
  have ht : MemLp (fun x => law.tau x) 2 design :=
    MemLp.of_bound (by fun_prop) (1/2) (ae_of_all _ (fun x => by simpa using hm.effectCap x))
  have hf : MemLp f 2 design := ht.sub (memLp_const c)
  have hfi := ht.integrable (by norm_num)
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have he (x : unitInterval) : f x-projOp J f x = law.tau x-projOp J law.tau x := by
    rw [projOp_sub_const J hJ law.tau hfi c x]
    dsimp [f]
    ring
  have hδ : 0 ≤ 20*(J:ℝ)^(-v.γ) := by positivity
  have hb (x : unitInterval) : |f x-projOp J f x| ≤ 20*(J:ℝ)^(-v.γ) := by
    rw [he]
    exact projection_holder_error J hJ v.γ ⟨by linarith [hv.2.2.2.1], hv.2.2.2.2⟩
      law.tau hm.effectSmooth x
  have hres : (∫ x, (f x-projOp J f x)^2 ∂design) ≤ (20*(J:ℝ)^(-v.γ))^2 := by
    calc
      _ ≤ ∫ _x, (20*(J:ℝ)^(-v.γ))^2 ∂design := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) (integrable_const _)
        exact ae_of_all _ (fun x => by simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hb x))
      _ = _ := by simp
  have henergy := histogram_projection_energy J hJ f hf hfm
  have hd := effect_distance_sq_le_const_energy law hm.effectCap c
  have hqeq : (∫ x, f x • featureMap J x ∂design) =
      ∫ x, (projOp J law.tau x-c) • featureMap J x ∂design := by
    have hconst (x : unitInterval) : projOp J (fun _ => (1:ℝ)) x = 1 := by
      simpa [projOp] using (projection_rows J hJ x).1
    have hs := histogram_feature_selfAdjoint_integrable J J hJ hJ (dvd_refl J)
      f (fun _ => (1:ℝ)) hfm measurable_const (integrable_const 1)
      (1/2+|c|) (by positivity) (fun x => by
        dsimp [f]
        exact (abs_sub _ _).trans (by linarith [hm.effectCap x]))
    simp only [hconst, mul_one] at hs
    rw [hs]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      dsimp only
      change projOp J (fun z => law.tau z-c) x • featureMap J x = _
      rw [projOp_sub_const J hJ law.tau hfi c x])
  rw [hqeq] at henergy
  have hdnonneg : 0 ≤ hetDist law := Real.sqrt_nonneg _
  have hqnonneg := norm_nonneg (∫ x, (projOp J law.tau x-c) • featureMap J x ∂design)
  change hetDist law^2 ≤ ∫ x, f x^2 ∂design at hd
  nlinarith

/-- Averaged overlap and Holder approximation separate the weighted original effect vector. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: weighted_effect_coefficient_separation
lemma weighted_effect_coefficient_separation (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K)
    (c : ℝ) (hc : |c| ≤ 1/2) :
    (3/16)*hetDist law-15*(J:ℝ)^(-v.γ) ≤
      ‖∫ x, (law.e x*(1-projOp K law.e x)*(law.tau x-c)) • featureMap J x ∂design‖ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let w := fun x => law.e x*(1-projOp K law.e x)
  let f := fun x => projOp J law.tau x-c
  have hwm : Measurable w := by dsimp [w]; fun_prop
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hwbound (x : unitInterval) : |w x| ≤ 9/16 := propensity_weight_abs_le law hm.overlap K hK x
  have hptbound (x : unitInterval) : |projOp J law.tau x| ≤ 1/2 :=
    projOp_abs_le_ae_bound J hJ law.tau (1/2) (by norm_num) (ae_of_all _ hm.effectCap) x
  have hfbound (x : unitInterval) : |f x| ≤ 1 := by
    exact (abs_sub _ _).trans (by linarith [hptbound x])
  have htbound (x : unitInterval) : |law.tau x-c| ≤ 1 :=
    (abs_sub _ _).trans (by linarith [hm.effectCap x])
  have hwi : Integrable w design :=
    (integrable_const (9/16:ℝ)).mono' hwm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hwbound x))
  have hfi : Integrable f design :=
    (integrable_const (1:ℝ)).mono' hfm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hfbound x))
  have hwfi : Integrable (fun x => w x*f x) design := by
    apply (integrable_const (9/16:ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [mul_le_mul (hwbound x) (hfbound x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/16)])
  have hcell : ∀ j : Fin J, ∀ x ∈ cell J j, ∀ z ∈ cell J j, f z=f x := by
    intro j x hx z hz
    dsimp [f]
    rw [projOp_eq_on_cell J hJ law.tau j z x hz hx]
  have hdiag := weighted_histogram_coefficient_norm_ge J hJ f w hfi hwi hwfi hfm hwm hcell
    (3/16) (by norm_num) (fun x => (coarse_propensity_weight_range law hm.overlap J K hJ hK hJK x).1)
  have hd := effect_histogram_coefficient_distance v hv law hm J hJ c
  let r : Vec J := ∫ x, (w x*f x) • featureMap J x ∂design
  let t : Vec J := ∫ x, (w x*(law.tau x-c)) • featureMap J x ∂design
  have hti : Integrable (fun x => (w x*(law.tau x-c)) • featureMap J x) design :=
    integrable_bounded_feature_coefficient J _ (by fun_prop) (9/16) (fun x => by
      rw [abs_mul]
      nlinarith [mul_le_mul (hwbound x) (htbound x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/16)])
  have hri : Integrable (fun x => (w x*f x) • featureMap J x) design :=
    integrable_feature_coefficient J _ hwfi (hwm.mul hfm)
  have hdiff : t-r = ∫ x, (w x*(law.tau x-projOp J law.tau x)) • featureMap J x ∂design := by
    dsimp [t, r]
    rw [← integral_sub hti hri]
    congr 1
    funext x
    dsimp [f]
    rw [← sub_smul]
    congr 1
    ring
  have herr (x : unitInterval) : |w x*(law.tau x-projOp J law.tau x)| ≤
      (45/4)*(J:ℝ)^(-v.γ) := by
    rw [abs_mul]
    have hholder := projection_holder_error J hJ v.γ
      ⟨by linarith [hv.2.2.2.1], hv.2.2.2.2⟩ law.tau hm.effectSmooth x
    have hh := mul_le_mul (hwbound x) hholder (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/16)
    nlinarith
  have herri : Integrable (fun x => w x*(law.tau x-projOp J law.tau x)) design :=
    (integrable_const ((45/4)*(J:ℝ)^(-v.γ))).mono' (by fun_prop)
      (ae_of_all _ (fun x => by simpa using herr x))
  have herror : ‖t-r‖ ≤ (45/4)*(J:ℝ)^(-v.γ) := by
    rw [hdiff]
    exact histogram_coefficient_norm_le J hJ _ herri (by fun_prop) _ (by positivity) (ae_of_all _ herr)
  have htriangle : ‖r‖ ≤ ‖t‖+‖t-r‖ := by
    calc
      ‖r‖ = ‖t-(t-r)‖ := by congr 1; module
      _ ≤ ‖t‖+‖t-r‖ := norm_sub_le _ _
  change (3/16)*‖∫ x, f x • featureMap J x ∂design‖ ≤ ‖r‖ at hdiag
  change hetDist law-20*(J:ℝ)^(-v.γ) ≤ ‖∫ x, f x • featureMap J x ∂design‖ at hd
  change (3/16)*hetDist law-15*(J:ℝ)^(-v.γ) ≤ ‖t‖
  linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
