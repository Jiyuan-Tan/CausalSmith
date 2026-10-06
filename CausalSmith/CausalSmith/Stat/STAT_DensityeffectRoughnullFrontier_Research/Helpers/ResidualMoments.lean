module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
Explicit arm/outcome conditional integrals for observable residuals and their uniform scalar and
Hilbert moment bounds.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Explicit conditional outcome integral given the covariate. -/
def armOutcomeMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ObsLaw) (g : Omega → E) (x : ℝ) : E :=
  ∑ a : Bool, ∫ y, (pi P a x * P.eta a x y) • g (x,a,y) ∂unitVolume

/-- Clipping places every real input in the prescribed nonempty interval. -/
-- @node: clip_mem_Icc
lemma clip_mem_Icc (lo hi z : ℝ) (h : lo ≤ hi) :
    clip lo hi z ∈ Set.Icc lo hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- The histogram cell selector is measurable. -/
-- @node: measurable_histogram_cell
@[fun_prop] lemma measurable_histogram_cell (k : ℕ) : Measurable (cell k) := by
  unfold cell
  have hf : Measurable (fun x : ℝ => ⌊(k : ℝ) * x⌋₊) :=
    Nat.measurable_floor.comp (by fun_prop)
  fun_prop

/-- For fixed training and covariate, the clipped outcome histogram is measurable. -/
-- @node: measurable_clippedDensityPilot
@[fun_prop] lemma measurable_clippedDensityPilot {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    Measurable (clippedDensityPilot train mx my a x) := by
  have hc : Measurable (fun y => outcomeCellCount train mx my a x y) := by
    let g : ℕ → ℕ := fun c => (Finset.univ.filter (fun i =>
      cell mx (X (train i)) = cell mx x ∧ A (train i) = a ∧
        cell my (Y (train i)) = c)).card
    exact (measurable_of_countable g).comp (measurable_histogram_cell my)
  unfold clippedDensityPilot clip
  split_ifs <;> fun_prop

/-- Clipping bounds the raw outcome histogram before normalization. -/
-- @node: clippedDensityPilot_mem_Icc
lemma clippedDensityPilot_mem_Icc {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x y : ℝ) :
    clippedDensityPilot train mx my a x y ∈ Set.Icc (1 / 8) 8 := by
  exact clip_mem_Icc _ _ _ (by norm_num)

/-- The raw clipped histogram is integrable on the unit outcome domain. -/
-- @node: clippedDensityPilot_integrable
lemma clippedDensityPilot_integrable {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    Integrable (clippedDensityPilot train mx my a x) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 8
  exact Filter.Eventually.of_forall (fun y => by
    have hn : 0 ≤ clippedDensityPilot train mx my a x y := by
      linarith [(clippedDensityPilot_mem_Icc train mx my a x y).1]
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (clippedDensityPilot_mem_Icc train mx my a x y).2)

/-- The normalization integral inherits the clipping bounds. -/
-- @node: clippedDensityPilot_integral_mem_Icc
lemma clippedDensityPilot_integral_mem_Icc {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    (∫ y, clippedDensityPilot train mx my a x y ∂unitVolume) ∈ Set.Icc (1 / 8) 8 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi := clippedDensityPilot_integrable train mx my a x
  constructor
  · simpa using integral_mono (integrable_const (1 / 8 : ℝ)) hi
      (fun y => (clippedDensityPilot_mem_Icc train mx my a x y).1)
  · simpa using integral_mono hi (integrable_const (8 : ℝ))
      (fun y => (clippedDensityPilot_mem_Icc train mx my a x y).2)

/-- The normalized histogram is measurable in its outcome argument. -/
-- @node: measurable_densityPilot_outcome
@[fun_prop] lemma measurable_densityPilot_outcome {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) : Measurable (densityPilot train mx my a x) := by
  unfold densityPilot
  fun_prop

/-- Every normalized pilot density lies between one sixty-fourth and sixty-four. -/
-- @node: densityPilot_mem_Icc
lemma densityPilot_mem_Icc {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x y : ℝ) :
    densityPilot train mx my a x y ∈ Set.Icc (1 / 64) 64 := by
  have hc := clippedDensityPilot_mem_Icc train mx my a x y
  have hd := clippedDensityPilot_integral_mem_Icc train mx my a x
  have hp : 0 < ∫ y, clippedDensityPilot train mx my a x y ∂unitVolume := by
    linarith [hd.1]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [hc.1, hd.2]
  · apply (div_le_iff₀ hp).2
    linarith [hc.2, hd.1]

/-- Normalization preserves integrability of the pilot density. -/
-- @node: densityPilot_integrable
lemma densityPilot_integrable {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    Integrable (densityPilot train mx my a x) unitVolume := by
  exact (clippedDensityPilot_integrable train mx my a x).div_const _

/-- The clipped and normalized pilot integrates to one. -/
-- @node: densityPilot_normalized
lemma densityPilot_normalized {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    (∫ y, densityPilot train mx my a x y ∂unitVolume) = 1 := by
  have hd := clippedDensityPilot_integral_mem_Icc train mx my a x
  have hp : (∫ y, clippedDensityPilot train mx my a x y ∂unitVolume) ≠ 0 := by
    linarith [hd.1]
  simp only [densityPilot, integral_div, div_self hp]

/-- Every training realization produces a propensity pilot in the overlap interval. -/
-- @node: propensityPilot_mem_Icc
lemma propensityPilot_mem_Icc {m : ℕ} (train : Fin m → Omega) (mx : ℕ) (x : ℝ) :
    propensityPilot train mx x ∈ Set.Icc (1 / 4) (3 / 4) := by
  exact clip_mem_Icc _ _ _ (by norm_num)

/-- Both pilot arm probabilities obey the same clipping bounds. -/
-- @node: pilotPi_mem_Icc
lemma pilotPi_mem_Icc {m : ℕ} (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ) :
    pilotPi train mx a x ∈ Set.Icc (1 / 4) (3 / 4) := by
  have h := propensityPilot_mem_Icc train mx x
  cases a <;> simp only [pilotPi, armProbability, Bool.false_eq_true, ↓reduceIte]
  · constructor <;> linarith [h.1, h.2]
  · exact h

/-- Model overlap applies to either observed arm propensity. -/
-- @node: model_pi_mem_Icc
lemma model_pi_mem_Icc (P : ObsLaw) (hModel : Model P) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : pi P a x ∈ Set.Icc (1 / 4) (3 / 4) := by
  have h := hModel.overlap x hx
  cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte]
  · constructor <;> linarith [h.1, h.2]
  · exact h

/-- A clipped inverse-propensity indicator residual has absolute value at most three. -/
-- @node: Rres_abs_le
lemma Rres_abs_le {m : ℕ} (train : Fin m → Omega) (mx : ℕ) (a : Bool) (o : Omega) :
    |Rres train mx a o| ≤ 3 := by
  have h := pilotPi_mem_Icc train mx a (X o)
  have hp : 0 < pilotPi train mx a (X o) := by linarith [h.1]
  rw [Rres, abs_le]
  by_cases ha : A o = a
  · simp only [ha, ↓reduceIte]
    constructor
    · apply (le_div_iff₀ hp).2
      linarith [h.1, h.2]
    · apply (div_le_iff₀ hp).2
      linarith [h.1]
  · simp only [ha, ↓reduceIte]
    constructor
    · apply (le_div_iff₀ hp).2
      linarith [h.1]
    · apply (div_le_iff₀ hp).2
      linarith [h.1]

/-- The relative propensity error is between minus two thirds and two. -/
-- @node: uerr_mem_Icc
lemma uerr_mem_Icc {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : uerr P train mx a x ∈ Set.Icc (-2 / 3) 2 := by
  have h := pilotPi_mem_Icc train mx a x
  have hpi := model_pi_mem_Icc P hModel a x hx
  have hp : 0 < pilotPi train mx a x := by linarith [h.1]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [h.2, hpi.1]
  · apply (div_le_iff₀ hp).2
    linarith [h.1, hpi.2]

/-- In particular the uniform absolute relative propensity error is at most two. -/
-- @node: uerr_abs_le
lemma uerr_abs_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : |uerr P train mx a x| ≤ 2 := by
  have h := uerr_mem_Icc P hModel train mx a x hx
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩

/-- Integrating the observable treatment residual yields the relative propensity error. -/
-- @node: armOutcomeMean_Rres
lemma armOutcomeMean_Rres {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    armOutcomeMean P (Rres train mx a) x = uerr P train mx a x := by
  have h := pilotPi_mem_Icc train mx a x
  have hp : pilotPi train mx a x ≠ 0 := by linarith [h.1]
  change (∑ b : Bool, ∫ y, (pi P b x * P.eta b x y) *
    (((if b = a then 1 else 0) - pilotPi train mx a x) / pilotPi train mx a x)
      ∂unitVolume) = (pi P a x - pilotPi train mx a x) / pilotPi train mx a x
  simp only [integral_mul_const, integral_const_mul,
    P.eta_normalized _ x hx, mul_one, Fintype.sum_bool]
  cases a <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals
    simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte]
    field_simp
    ring

/-- A bounded nonnegative normalized density has squared integral at most its envelope. -/
-- @node: normalized_density_squared_bound
lemma normalized_density_squared_bound (f : ℝ → ℝ) (b : ℝ)
    (hm : Measurable f) (hi : Integrable f unitVolume)
    (hb : ∀ᵐ y ∂unitVolume, 0 ≤ f y ∧ f y ≤ b)
    (hn : (∫ y, f y ∂unitVolume) = 1) :
    Integrable (fun y => (f y) ^ 2) unitVolume ∧ l2Squared f ≤ b := by
  have hdom : ∀ᵐ y ∂unitVolume, ‖(f y) ^ 2‖ ≤ b * f y := by
    filter_upwards [hb] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hy.1, hy.2]
  have hs : Integrable (fun y => (f y) ^ 2) unitVolume :=
    (hi.const_mul b).mono' (by fun_prop) hdom
  refine ⟨hs, ?_⟩
  calc
    l2Squared f ≤ ∫ y, b * f y ∂unitVolume := by
      apply integral_mono_ae hs (hi.const_mul b)
      filter_upwards [hdom] with y hy
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f y))] using hy
    _ = b := by rw [integral_const_mul, hn, mul_one]

/-- The normalized pilot's squared Hilbert norm is at most sixty-four. -/
-- @node: densityPilot_squared_bound
lemma densityPilot_squared_bound {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) (x : ℝ) :
    Integrable (fun y => (densityPilot train mx my a x y) ^ 2) unitVolume ∧
      l2Squared (densityPilot train mx my a x) ≤ 64 := by
  apply normalized_density_squared_bound _ 64
    (measurable_densityPilot_outcome train mx my a x)
    (densityPilot_integrable train mx my a x) _ (densityPilot_normalized train mx my a x)
  exact Filter.Eventually.of_forall (fun y =>
    ⟨by linarith [(densityPilot_mem_Icc train mx my a x y).1],
      (densityPilot_mem_Icc train mx my a x y).2⟩)

/-- The model conditional density has squared Hilbert norm at most four. -/
-- @node: model_density_squared_bound
lemma model_density_squared_bound (P : ObsLaw) (hModel : Model P)
    (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Integrable (fun y => (P.eta a x y) ^ 2) unitVolume ∧
      l2Squared (P.eta a x) ≤ 4 := by
  have hm : Measurable (P.eta a x) :=
    (P.eta_measurable a).comp (measurable_const.prodMk measurable_id)
  apply normalized_density_squared_bound _ 4 hm (P.eta_integrable a x hx) _
    (P.eta_normalized a x hx)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact ⟨P.eta_nonneg a x y hx hy, (hModel.density_envelope a x y hx hy).2⟩

/-- The weighted density error has a uniform Hilbert norm bound, for fixed training. -/
-- @node: verr_l2Norm_le
lemma verr_l2Norm_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) : l2Norm (verr P train mx my a x) ≤ 30 := by
  obtain ⟨hei, he⟩ := model_density_squared_bound P hModel a x hx
  obtain ⟨hhi, hh⟩ := densityPilot_squared_bound train mx my a x
  have hu := uerr_mem_Icc P hModel train mx a x hx
  have hc : (1 + uerr P train mx a x) ^ 2 ≤ 9 := by
    nlinarith [hu.1, hu.2]
  have hupper : Integrable (fun y => 9 * ((P.eta a x y) ^ 2 +
      (densityPilot train mx my a x y) ^ 2)) unitVolume := (hei.add hhi).const_mul 9
  have hdom : ∀ᵐ y ∂unitVolume, (verr P train mx my a x y) ^ 2 ≤
      9 * ((P.eta a x y) ^ 2 + (densityPilot train mx my a x y) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hen := P.eta_nonneg a x y hx hy
    have hhn : 0 ≤ densityPilot train mx my a x y := by
      linarith [(densityPilot_mem_Icc train mx my a x y).1]
    have hd : (P.eta a x y - densityPilot train mx my a x y) ^ 2 ≤
        (P.eta a x y) ^ 2 + (densityPilot train mx my a x y) ^ 2 := by
      nlinarith [mul_nonneg hen hhn]
    dsimp [verr, werr]
    rw [mul_pow]
    calc
      _ ≤ 9 * (P.eta a x y - densityPilot train mx my a x y) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)
  have hm : Measurable (fun y => (verr P train mx my a x y) ^ 2) := by
    have heta : Measurable (P.eta a x) :=
      (P.eta_measurable a).comp (measurable_const.prodMk measurable_id)
    unfold verr werr
    fun_prop
  have hi : Integrable (fun y => (verr P train mx my a x y) ^ 2) unitVolume :=
    hupper.mono' hm.aestronglyMeasurable (by
      filter_upwards [hdom] with y hy
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (verr P train mx my a x y))] using hy)
  have hsq : l2Squared (verr P train mx my a x) ≤ 9 * (4 + 64) := by
    calc
      _ ≤ ∫ y, 9 * ((P.eta a x y) ^ 2 +
          (densityPilot train mx my a x y) ^ 2) ∂unitVolume :=
        integral_mono_ae hi hupper hdom
      _ = 9 * (l2Squared (P.eta a x) + l2Squared (densityPilot train mx my a x)) := by
        unfold l2Squared
        integral_linearity
      _ ≤ _ := by linarith [he, hh]
  apply (Real.sqrt_le_iff).2
  exact ⟨by norm_num, by dsimp [l2Squared] at hsq ⊢; linarith⟩


/-- Histogram cells are measurable, including their endpoint convention. -/
lemma measurableSet_histogramCell (J l : ℕ) : MeasurableSet (histogramCell J l) := by
  exact measurableSet_Icc.inter ((measurable_histogram_cell J) (measurableSet_singleton l))

/-- Each weighted representer coordinate is an integrable cell indicator. -/
-- @node: weighted_phi_coordinate_integrable
lemma weighted_phi_coordinate_integrable (J : ℕ) (f : ℝ → ℝ)
    (hi : Integrable f unitVolume) (i : Fin J) :
    Integrable (fun y => f y * phiCoefficients J y i) unitVolume := by
  have hs : MeasurableSet {y | cell J y = i.val + 1} :=
    (measurable_histogram_cell J) (measurableSet_singleton _)
  have heq : (fun y => f y * phiCoefficients J y i) =
      {y | cell J y = i.val + 1}.indicator (fun y => f y * Real.sqrt J) := by
    funext y
    by_cases hy : cell J y = i.val + 1
    · simp [phiCoefficients, hy]
    · simp [phiCoefficients, hy]
  rw [heq]
  exact (hi.mul_const (Real.sqrt J)).indicator hs


/-- Integrating the histogram representer gives the projection coefficient vector. -/
-- @node: integral_weighted_phiCoefficients
lemma integral_weighted_phiCoefficients (J : ℕ) (f : ℝ → ℝ)
    (hi : Integrable f unitVolume) :
    (∫ y, f y • phiCoefficients J y ∂unitVolume) = coefficients J f := by
  ext i
  rw [eval_integral_piLp (fun i => by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      weighted_phi_coordinate_integrable J f hi i)]
  change (∫ y, f y * (if cell J y = i.val + 1 then Real.sqrt J else 0)
    ∂unitVolume) = Real.sqrt J * ∫ y in histogramCell J (i.val + 1), f y ∂unitVolume
  calc
    _ = ∫ y, (histogramCell J (i.val + 1)).indicator
        (fun y => Real.sqrt J * f y) y ∂unitVolume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      simp only [histogramCell, Set.mem_setOf_eq, hy, true_and, Set.indicator]
      split_ifs <;> ring
    _ = _ := by rw [integral_indicator (measurableSet_histogramCell _ _), integral_const_mul]

/-- The vector-valued weighted histogram representer is integrable coordinatewise. -/
-- @node: weighted_phiCoefficients_integrable
lemma weighted_phiCoefficients_integrable (J : ℕ) (f : ℝ → ℝ)
    (hi : Integrable f unitVolume) :
    Integrable (fun y => f y • phiCoefficients J y) unitVolume := by
  apply Integrable.of_eval_piLp
  intro i
  simpa only [PiLp.smul_apply, smul_eq_mul] using
    weighted_phi_coordinate_integrable J f hi i

/-- Outcome projection coefficients commute with subtraction and constant scaling. -/
-- @node: coefficients_const_mul_sub
lemma coefficients_const_mul_sub (J : ℕ) (c : ℝ) (f g : ℝ → ℝ)
    (hf : Integrable f unitVolume) (hg : Integrable g unitVolume) :
    coefficients J (fun y => c * (f y - g y)) =
      c • (coefficients J f - coefficients J g) := by
  ext i
  change Real.sqrt J * (∫ y in histogramCell J (i.val + 1), c * (f y - g y)
    ∂unitVolume) = c * (Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y
    ∂unitVolume) - Real.sqrt J * (∫ y in histogramCell J (i.val + 1), g y ∂unitVolume))
  rw [integral_const_mul, integral_sub hf.integrableOn hg.integrableOn]
  ring

/-- Integrating a centered outcome representer gives the centered projection. -/
-- @node: integral_centered_phiCoefficients
lemma integral_centered_phiCoefficients (P : ObsLaw) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) (J : ℕ) (b : Hj J) :
    (∫ y, P.eta a x y • (phiCoefficients J y - b) ∂unitVolume) =
      coefficients J (P.eta a x) - b := by
  have hi := P.eta_integrable a x hx
  simp_rw [smul_sub]
  rw [integral_sub (weighted_phiCoefficients_integrable J _ hi) (hi.smul_const b),
    integral_weighted_phiCoefficients J _ hi, integral_smul_const,
    P.eta_normalized a x hx, one_smul]

/-- The conditional observable outcome-residual mean is the weighted density-error projection. -/
-- @node: armOutcomeMean_Vres
lemma armOutcomeMean_Vres {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my J : ℕ) (a : Bool) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    armOutcomeMean P (Vres train mx my J a) x =
      coefficients J (verr P train mx my a x) := by
  have hp : pilotPi train mx a x ≠ 0 := by
    linarith [(pilotPi_mem_Icc train mx a x).1]
  have hc : 1 + uerr P train mx a x = pi P a x / pilotPi train mx a x := by
    unfold uerr
    field_simp
    ring
  rw [show verr P train mx my a x = fun y =>
      (1 + uerr P train mx a x) * (P.eta a x y - densityPilot train mx my a x y) from rfl,
    coefficients_const_mul_sub J _ _ _ (P.eta_integrable a x hx)
      (densityPilot_integrable train mx my a x), hc]
  unfold armOutcomeMean
  simp only [Fintype.sum_bool]
  have hfactor (b : Bool) (y : ℝ) : pi P b x * P.eta b x y *
      (pilotPi train mx b x)⁻¹ = (pi P b x / pilotPi train mx b x) * P.eta b x y := by ring
  cases a <;> simp only [Vres, X, A, Y, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, zero_div, zero_smul, smul_zero, integral_zero, add_zero, zero_add, one_div]
  all_goals
    simp_rw [smul_smul, hfactor, mul_smul]
    rw [integral_smul, integral_centered_phiCoefficients P _ x hx J]
    rfl


end CausalSmith.Stat.DensityEffectRoughNull
