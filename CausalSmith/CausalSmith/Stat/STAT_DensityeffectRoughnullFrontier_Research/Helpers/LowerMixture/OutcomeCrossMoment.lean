module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.LocalizedDesign
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OutcomeWeights
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Baseline outcome integration for the actual non-flat lower experiment. The centered
score-pair contract is derived from the constructed density and independent iid
outcomes, then used to identify the posterior likelihood cross moment in (31).
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The actual common outcome law of every null cell. -/
-- @node: lowerBaselineLaw
def lowerBaselineLaw : Measure ℝ :=
  unitVolume.withDensity (fun y => ENNReal.ofReal (baselineDensity y))

/-- The non-flat baseline integrates to one, so its outcome law is a probability law. -/
-- @node: lowerBaselineLaw_probability
instance lowerBaselineLaw_probability : IsProbabilityMeasure lowerBaselineLaw := by
  constructor
  rw [lowerBaselineLaw, withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal lower_baseline_valid.2.2.1
    (Filter.Eventually.of_forall (fun y => show (0 : ℝ) ≤ baselineDensity y by
      linarith [lower_baseline_valid.2.1 y])),
    lower_baseline_valid.2.2.2]
  simp

/-- Integration under the baseline is exactly density-weighted Lebesgue integration. -/
-- @node: lowerBaselineLaw_integral
lemma lowerBaselineLaw_integral (f : ℝ → ℝ) :
    (∫ y, f y ∂lowerBaselineLaw) = ∫ y, baselineDensity y * f y ∂unitVolume := by
  rw [lowerBaselineLaw, integral_withDensity_eq_integral_toReal_smul
    (lower_baseline_valid.1.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (by linarith [lower_baseline_valid.2.1 y])]
  rfl

/-- An outcome sign score divides its signed bump by the actual baseline density. -/
-- @node: lowerOutcomeScore
def lowerOutcomeScore (j : ℕ) (omega : Fin j → Bool) (y : ℝ) : ℝ :=
  signedBumps j omega y / baselineDensity y

/-- Outcome sign scores are measurable. -/
-- @node: measurable_lowerOutcomeScore
@[fun_prop] lemma measurable_lowerOutcomeScore (j : ℕ) (omega : Fin j → Bool) :
    Measurable (lowerOutcomeScore j omega) := by
  unfold lowerOutcomeScore baselineDensity signedBumps
  fun_prop

/-- The positive baseline gives a global bound for every outcome sign score. -/
-- @node: lowerOutcomeScore_abs_le
lemma lowerOutcomeScore_abs_le (j : ℕ) (omega : Fin j → Bool) (y : ℝ) :
    |lowerOutcomeScore j omega y| ≤ 2 := by
  have hb := lower_baseline_valid.2.1 y
  have hp : 0 < baselineDensity y := by linarith
  rw [lowerOutcomeScore, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).2
  linarith [signedBumps_abs_le_one j omega y]

/-- The bounded score is integrable under the normalized baseline. -/
-- @node: lowerOutcomeScore_integrable
lemma lowerOutcomeScore_integrable (j : ℕ) (omega : Fin j → Bool) :
    Integrable (lowerOutcomeScore j omega) lowerBaselineLaw := by
  apply Integrable.of_bound (by fun_prop) 2
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using lowerOutcomeScore_abs_le j omega y)

/-- Each within-record score product is integrable, without an extra moment premise. -/
-- @node: lowerOutcomeScore_pair_integrable
lemma lowerOutcomeScore_pair_integrable (j : ℕ) (omega op : Fin j → Bool) :
    Integrable (fun y => lowerOutcomeScore j omega y * lowerOutcomeScore j op y)
      lowerBaselineLaw := by
  apply Integrable.of_bound (by fun_prop) 4
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul (lowerOutcomeScore_abs_le j omega y)
    (lowerOutcomeScore_abs_le j op y) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Baseline weighting cancels the score denominator and gives exact centering. -/
-- @node: lowerOutcomeScore_centered
lemma lowerOutcomeScore_centered (j : ℕ) (omega : Fin j → Bool) :
    (∫ y, lowerOutcomeScore j omega y ∂lowerBaselineLaw) = 0 := by
  rw [lowerBaselineLaw_integral]
  have he : (fun y => baselineDensity y * lowerOutcomeScore j omega y) =
      signedBumps j omega := by
    funext y
    unfold lowerOutcomeScore
    field_simp [ne_of_gt (show 0 < baselineDensity y by linarith [lower_baseline_valid.2.1 y])]
  rw [he, signedBumps_integral_zero]

/-- The common baseline score overlap is the actual weighted sign overlap (32). -/
-- @node: lowerOutcomeScore_overlap
lemma lowerOutcomeScore_overlap (j : ℕ) (omega op : Fin j → Bool) :
    (∫ y, lowerOutcomeScore j omega y * lowerOutcomeScore j op y ∂lowerBaselineLaw) =
      weightedSignOverlap j (lowerOutcomeWeight j) omega op := by
  rw [lowerBaselineLaw_integral]
  have he : (fun y => baselineDensity y *
      (lowerOutcomeScore j omega y * lowerOutcomeScore j op y)) =
      (fun y => signedBumps j omega y * signedBumps j op y / baselineDensity y) := by
    funext y
    unfold lowerOutcomeScore
    field_simp [ne_of_gt (show 0 < baselineDensity y by linarith [lower_baseline_valid.2.1 y])]
  rw [he, lower_outcome_cross_moment_eq_overlap]

/-- iid baseline outcomes give the independent, centered score pairs required by (31). -/
-- @node: lowerOutcomeScore_centeredOutcomePair
lemma lowerOutcomeScore_centeredOutcomePair (m j : ℕ) (omega op : Fin j → Bool) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.CenteredOutcomePair
      (Measure.pi (fun _ : Fin m => lowerBaselineLaw))
      (fun i y => lowerOutcomeScore j omega (y i))
      (fun i y => lowerOutcomeScore j op (y i))
      (weightedSignOverlap j (lowerOutcomeWeight j) omega op) := by
  refine ⟨iIndepFun_pi (X := fun _ : Fin m => fun y : ℝ =>
    (lowerOutcomeScore j omega y, lowerOutcomeScore j op y))
    (fun _ => by fun_prop), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i)
      |>.integrable_comp_of_integrable (lowerOutcomeScore_integrable j omega)
  · intro i
    exact (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i)
      |>.integrable_comp_of_integrable (lowerOutcomeScore_integrable j op)
  · intro i
    exact (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i)
      |>.integrable_comp_of_integrable (lowerOutcomeScore_pair_integrable j omega op)
  · intro i
    rw [← integral_map (measurable_pi_apply i).aemeasurable (by fun_prop),
      (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i).map_eq]
    exact lowerOutcomeScore_centered j omega
  · intro i
    rw [← integral_map (measurable_pi_apply i).aemeasurable (by fun_prop),
      (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i).map_eq]
    exact lowerOutcomeScore_centered j op
  · intro i
    rw [← integral_map (μ := Measure.pi (fun _ : Fin m => lowerBaselineLaw))
      (φ := fun y : Fin m → ℝ => y i) (f := fun y : ℝ =>
      lowerOutcomeScore j omega y * lowerOutcomeScore j op y)
      (measurable_pi_apply i).aemeasurable (by fun_prop),
      (measurePreserving_eval (fun _ : Fin m => lowerBaselineLaw) i).map_eq]
    exact lowerOutcomeScore_overlap j omega op

/-- Cross moment of the two actual conditional outcome likelihoods at fixed cell design. -/
-- @node: lowerCellOutcomeCrossMoment
def lowerCellOutcomeCrossMoment {m : ℕ} (tau gamma : ℝ) (j : ℕ)
    (omega op : Fin j → Bool)
    (c : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m) : ℝ :=
  ∫ y : Fin m → ℝ,
    cellAlternativeRatio tau gamma c.1 c.2.1 (fun i => lowerOutcomeScore j omega (y i)) *
      cellAlternativeRatio tau gamma c.1 c.2.1 (fun i => lowerOutcomeScore j op (y i))
    ∂Measure.pi (fun _ : Fin m => lowerBaselineLaw)

/-- Actual iid baseline outcomes identify the finite posterior polynomial in (31).
All treated records are selected, as in the actual experiment. -/
-- @node: lowerCellOutcomeCrossMoment_eq_cellOverlap
lemma lowerCellOutcomeCrossMoment_eq_cellOverlap {m : ℕ} (tau gamma : ℝ)
    (ht : |tau| ≤ 1 / 4) (j : ℕ) (omega op : Fin j → Bool)
    (c : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m)
    (hu : ∀ i, |c.1 i| ≤ 1) :
    lowerCellOutcomeCrossMoment tau gamma j omega op c =
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap tau gamma
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op) (c.1, c.2.1, c.2.1) := by
  unfold lowerCellOutcomeCrossMoment
  rw [cellAlternativeRatio_crossMoment _ tau gamma ht c.1 hu c.2.1 _ _ _
    (lowerOutcomeScore_centeredOutcomePair m j omega op)]
  simp only [Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.subsetEnergy,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.selected,
    cellPosteriorCoefficient_eq_posterior]

/-- The conditional likelihood product is integrable under the actual outcome law. -/
-- @node: lowerCellOutcomeLikelihood_pair_integrable
lemma lowerCellOutcomeLikelihood_pair_integrable {m : ℕ} (tau gamma : ℝ)
    (j : ℕ) (omega op : Fin j → Bool)
    (c : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m) :
    Integrable (fun y : Fin m → ℝ =>
      cellAlternativeRatio tau gamma c.1 c.2.1 (fun i => lowerOutcomeScore j omega (y i)) *
        cellAlternativeRatio tau gamma c.1 c.2.1 (fun i => lowerOutcomeScore j op (y i)))
      (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  simp_rw [cellAlternativeRatio_eq_outcomeLikelihood]
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integrable_outcomeLikelihood_pair
    (lowerOutcomeScore_centeredOutcomePair m j omega op) tau gamma (c.1, c.2.1, c.2.1)

/-- The reported actual design always selects exactly the treated records. -/
-- @node: lowerUnitCellDesign_selected_eq_active
lemma lowerUnitCellDesign_selected_eq_active (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (m : ℕ) : ∀ᵐ c ∂lowerUnitCellDesign tau ht m, c.2.2 = c.2.1 := by
  unfold lowerUnitCellDesign
  apply (ae_map_iff (measurable_lowerUnitCellData m).aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Conditional actual outcome cross moments coincide almost everywhere with the
canonical cell polynomial under the actual shared-sign null design. -/
-- @node: lowerCellOutcomeCrossMoment_ae_eq
lemma lowerCellOutcomeCrossMoment_ae_eq (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (gamma : ℝ) (j : ℕ) (omega op : Fin j → Bool) (m : ℕ) :
    lowerCellOutcomeCrossMoment tau gamma j omega op =ᵐ[lowerUnitCellDesign tau ht m]
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap tau gamma
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op) := by
  filter_upwards [lowerUnitCellDesign_valid tau ht m,
    lowerUnitCellDesign_selected_eq_active tau ht m] with c hc he
  have h := lowerCellOutcomeCrossMoment_eq_cellOverlap tau gamma
    (by rw [abs_of_pos ht.1]; exact ht.2) j omega op c hc.1
  have hc' : (c.1, c.2.1, c.2.1) = c := Prod.ext rfl (Prod.ext rfl he.symm)
  simpa only [hc'] using h

/-- Actual conditional cross moments are integrable over the null design at every count. -/
-- @node: lowerCellOutcomeCrossMoment_integrable
lemma lowerCellOutcomeCrossMoment_integrable (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (gamma : ℝ) (j : ℕ) (omega op : Fin j → Bool) (m : ℕ) :
    Integrable (lowerCellOutcomeCrossMoment tau gamma j omega op)
      (lowerUnitCellDesign tau ht m) := by
  exact (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integrable_cellOverlap
    (lowerUnitCellDesign tau ht) (by rw [abs_of_pos ht.1]; exact ht.2)
    (lowerUnitCellDesign_valid tau ht) gamma
    (weightedSignOverlap j (lowerOutcomeWeight j) omega op) m).congr
    (lowerCellOutcomeCrossMoment_ae_eq tau ht gamma j omega op m).symm

/-- Averaging the actual conditional likelihood cross moment over design and Poisson
count gives exactly the coefficient series K(z) in (31). -/
-- @node: lowerCellOutcomeCrossMoment_poisson_average
lemma lowerCellOutcomeCrossMoment_poisson_average (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma : ℝ)
    (j : ℕ) (omega op : Fin j → Bool) :
    (∫ m : ℕ, ∫ c, lowerCellOutcomeCrossMoment tau gamma j omega op c
      ∂lowerUnitCellDesign tau ht m ∂poissonMeasure xi) =
      lowerPoissonOverlap tau ht xi gamma
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op) := by
  rw [lowerPoissonOverlap_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun m => integral_congr_ae
    (lowerCellOutcomeCrossMoment_ae_eq tau ht gamma j omega op m))

/-- The count-averaged conditional cross moment is Poisson-integrable; exchanges in
(31) therefore do not depend on an assumed integrability gate. -/
-- @node: lowerCellOutcomeCrossMoment_poisson_integrable
lemma lowerCellOutcomeCrossMoment_poisson_integrable (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma : ℝ)
    (j : ℕ) (omega op : Fin j → Bool) :
    Integrable (fun m : ℕ => ∫ c, lowerCellOutcomeCrossMoment tau gamma j omega op c
      ∂lowerUnitCellDesign tau ht m) (poissonMeasure xi) := by
  exact (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integrable_conditional_cellOverlap
    (lowerUnitCellDesign tau ht) xi (by rw [abs_of_pos ht.1]; exact ht.2)
    (lowerUnitCellDesign_valid tau ht) gamma
    (weightedSignOverlap j (lowerOutcomeWeight j) omega op)).congr
    (Filter.Eventually.of_forall (fun m => (integral_congr_ae
      (lowerCellOutcomeCrossMoment_ae_eq tau ht gamma j omega op m)).symm))

/-- Independent counts and actual cell designs turn the product of conditional
likelihood cross moments into K(z)^k, with the common outcome signs held fixed. -/
-- @node: lowerCellOutcomeCrossMoment_independent_cells
lemma lowerCellOutcomeCrossMoment_independent_cells (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (gamma : ℝ)
    (k j : ℕ) (omega op : Fin j → Bool) :
    (∫ counts : Fin k → ℕ,
      ∫ cells : (i : Fin k) → Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell (counts i),
        ∏ i : Fin k, lowerCellOutcomeCrossMoment tau gamma j omega op (cells i)
        ∂Measure.pi (fun i => lowerUnitCellDesign tau ht (counts i))
      ∂Measure.pi (fun _ : Fin k => poissonMeasure xi)) =
      lowerPoissonOverlap tau ht xi gamma
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k := by
  simp_rw [integral_fintype_prod_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin k => fun m : ℕ =>
    ∫ c, lowerCellOutcomeCrossMoment tau gamma j omega op c ∂lowerUnitCellDesign tau ht m)]
  simp_rw [lowerCellOutcomeCrossMoment_poisson_average tau ht xi gamma j omega op]
  simp

/-- Positivity of the constructed record laws gives nonnegativity of the actual
localized cell ratio, rather than assuming positivity of an abstract polynomial. -/
-- @node: lower_cell_actual_ratio_nonneg
lemma lower_cell_actual_ratio_nonneg {m : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (x y : Fin m → ℝ) (a : Fin m → Bool) (u : Fin m → ℝ)
    (hcell : ∀ b i, signedBumps k (Function.update lambda r b) (x i) = signValue b * u i) :
    0 ≤ cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) u a
      (fun i => lowerOutcomeScore j omega (y i)) := by
  rw [show (fun i => lowerOutcomeScore j omega (y i)) =
      (fun i => signedBumps j omega (y i) / baselineDensity (y i)) from rfl,
    cellAlternativeRatio_eq_lowerLaw_cellMixture theta k j hp lambda omega r x y a u hcell]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun b _ => Finset.prod_nonneg (fun i _ =>
      lower_alternative_recordDensity_nonneg theta k j hp _ omega _))
  · exact Finset.sum_nonneg (fun b _ => Finset.prod_nonneg (fun i _ =>
      (lower_null_recordDensity_pos theta k j hp _ omega _).le))

/-- The real density quotient of the actual two-sign sample laws is the exact cell
likelihood, including empty cells and closed-cell boundaries. -/
-- @node: lower_cell_sample_density_quotient_toReal
lemma lower_cell_sample_density_quotient_toReal {m : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (x y : Fin m → ℝ) (a : Fin m → Bool) (u : Fin m → ℝ)
    (hcell : ∀ b i, signedBumps k (Function.update lambda r b) (x i) = signValue b * u i) :
    (lowerUniformSampleDensity
        (fun b => lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega)
        m (fun i => (x i, a i, y i)) /
      lowerUniformSampleDensity
        (fun b => lowerNullLaw theta k j hp (Function.update lambda r b) omega)
        m (fun i => (x i, a i, y i))).toReal =
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) u a
        (fun i => lowerOutcomeScore j omega (y i)) := by
  rw [lower_cell_sample_density_quotient theta k j hp lambda omega r
    (fun i => (x i, a i, y i)) u hcell]
  exact ENNReal.toReal_ofReal
    (lower_cell_actual_ratio_nonneg theta k j hp lambda omega r x y a u hcell)

/-- Conditional on localized covariates and assignments, the two actual alternative
sample-density quotients have precisely the cross moment (31) under null outcomes. -/
-- @node: lower_actual_cell_density_cross_moment
lemma lower_actual_cell_density_cross_moment {m : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lambda : Fin k → Bool)
    (omega op : Fin j → Bool) (r : Fin k) (x : Fin m → ℝ) (a : Fin m → Bool)
    (hx : ∀ i, x i ∈ lowerClosedCell k r) :
    (∫ y : Fin m → ℝ,
      (lowerUniformSampleDensity
          (fun b => lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega)
          m (fun i => (x i, a i, y i)) /
        lowerUniformSampleDensity
          (fun b => lowerNullLaw theta k j hp (Function.update lambda r b) omega)
          m (fun i => (x i, a i, y i))).toReal *
      (lowerUniformSampleDensity
          (fun b => lowerAlternativeLaw theta k j hp (Function.update lambda r b) op)
          m (fun i => (x i, a i, y i)) /
        lowerUniformSampleDensity
          (fun b => lowerNullLaw theta k j hp (Function.update lambda r b) op)
          m (fun i => (x i, a i, y i))).toReal
      ∂Measure.pi (fun _ : Fin m => lowerBaselineLaw)) =
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.cellOverlap
        (lowerTau theta k) (lowerGamma theta j)
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op)
        ((fun i => lowerBump ((k : ℝ) * x i - r.val)), a, a) := by
  let u : Fin m → ℝ := fun i => lowerBump ((k : ℝ) * x i - r.val)
  have hcell (b : Bool) (i : Fin m) :
      signedBumps k (Function.update lambda r b) (x i) = signValue b * u i := by
    rw [signedBumps_on_lowerClosedCell k hk r _ _ (hx i)]
    simp [u]
  simp_rw [lower_cell_sample_density_quotient_toReal theta k j hp lambda omega r x _ a u hcell,
    lower_cell_sample_density_quotient_toReal theta k j hp lambda op r x _ a u hcell]
  exact lowerCellOutcomeCrossMoment_eq_cellOverlap (lowerTau theta k) (lowerGamma theta j)
    (by rw [abs_of_nonneg (lowerTau_mem_Icc theta k j hp).1]
        exact (lowerTau_mem_Icc theta k j hp).2)
    j omega op (u, a, a) (fun i => lowerBump_abs_le_one _)

/-- Outcome-sign averaging of the independent-cell conditional likelihood calculation
has the rate budget (43), using the actual baseline weights and singleton bound. -/
-- @node: lowerCellOutcomeCrossMoment_sign_excess_le
lemma lowerCellOutcomeCrossMoment_sign_excess_le (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (hx : (xi : ℝ) ≤ 1)
    (gamma : ℝ) (k j : ℕ) (hj : 0 < j)
    (hr : (xi : ℝ) * gamma ^ 2 ≤ 1)
    (hd : 2 * ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) ≤ 1 / 2)
    (ha : ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
        (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2) ^ 2 ≤ 1 / 2) :
    signPairExpectation j (fun omega op =>
      ∫ counts : Fin k → ℕ,
        ∫ cells : (i : Fin k) → Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell (counts i),
          ∏ i : Fin k, lowerCellOutcomeCrossMoment tau gamma j omega op (cells i)
          ∂Measure.pi (fun i => lowerUnitCellDesign tau ht (counts i))
        ∂Measure.pi (fun _ : Fin k => poissonMeasure xi)) - 1 ≤
      8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
          ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
          (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2) ^ 2 +
        ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4)) := by
  simp_rw [lowerCellOutcomeCrossMoment_independent_cells tau ht xi gamma k j]
  exact lowerPoissonOverlap_actual_weights_excess_le tau ht xi hx gamma k j hj hr hd ha

end CausalSmith.Stat.DensityEffectRoughNull
