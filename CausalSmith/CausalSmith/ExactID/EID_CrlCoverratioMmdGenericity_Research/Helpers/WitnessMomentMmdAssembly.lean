module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessTransport
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessAssembly
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.ContrastIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability.Stability

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: sparseA
/-- For a [parent coordinate](hyp:x), the [sparse child-weight integral](goal) averages the
squared intervention density against the sparse denominator. -/
def sparseA (x : ℝ) : ℝ :=
  ∫ y in Set.Icc (0 : ℝ) 1,
    exponentialInterventionDensity y ^ 2 /
      (1 + (centeredCoordinate x / 10) * centeredCoordinate y)

-- @node: sparseA_hasDerivAt
/-- At [a point of the unit interval](hyp:hx), the [sparse child-weight integral has the stated
derivative](goal). -/
lemma sparseA_hasDerivAt {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt sparseA
      (-(1 / 5 : ℝ) * ∫ y in Set.Icc (0 : ℝ) 1,
        centeredCoordinate y * sparseWeight (centeredCoordinate x / 10) y) x := by
  change HasDerivAt (fun x : ℝ => ∫ y in Set.Icc (0 : ℝ) 1,
    exponentialInterventionDensity y ^ 2 /
      (1 + (centeredCoordinate x / 10) * centeredCoordinate y)) _ x
  let F : ℝ → ℝ → ℝ := fun x y =>
    exponentialInterventionDensity y ^ 2 /
      (1 + (centeredCoordinate x / 10) * centeredCoordinate y)
  let F' : ℝ → ℝ → ℝ := fun x y =>
    -(1 / 5 : ℝ) * centeredCoordinate y * sparseWeight
      (centeredCoordinate x / 10) y
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hs : Set.Ioo (-1 / 4 : ℝ) (5 / 4) ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_Ioo (by constructor <;> nlinarith [hx.1, hx.2])
  have hden : ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (5 / 4), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < 1 + centeredCoordinate z / 10 * centeredCoordinate y := by
    intro z hz y hy
    have hh := abs_centeredCoordinate_le_one hy
    rw [abs_le] at hh
    have hzcenter : (-3 / 2 : ℝ) < centeredCoordinate z ∧
        centeredCoordinate z < 3 / 2 := by
      unfold centeredCoordinate
      constructor <;> linarith [hz.1, hz.2]
    have hzabs : |centeredCoordinate z| < 3 / 2 := (abs_lt).2 ⟨by linarith, hzcenter.2⟩
    have hyabs : |centeredCoordinate y| ≤ 1 := (abs_le).2 hh
    have habs : |centeredCoordinate z / 10 * centeredCoordinate y| < 3 / 20 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
      calc
        |centeredCoordinate z| / 10 * |centeredCoordinate y| ≤
            |centeredCoordinate z| / 10 * 1 := by gcongr
        _ < 3 / 20 := by nlinarith
    linarith [neg_lt_of_abs_lt habs]
  have hqcont : Continuous exponentialInterventionDensity := by
    unfold exponentialInterventionDensity
    fun_prop
  have hccont : Continuous centeredCoordinate := by
    unfold centeredCoordinate
    fun_prop
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) μ := by
    filter_upwards [hs] with z hz
    have hzcont : ContinuousOn (F z) (Set.Icc (0 : ℝ) 1) := by
      dsimp only [F]
      apply ContinuousOn.div (hqcont.pow 2).continuousOn
        (continuous_const.add (continuous_const.mul hccont)).continuousOn
      intro y hy
      exact (hden z hz y hy).ne'
    exact hzcont.aestronglyMeasurable measurableSet_Icc
  have hF_int : Integrable (F x) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [F]
    apply ContinuousOn.div
    · exact (hqcont.pow 2).continuousOn
    · exact (continuous_const.add (continuous_const.mul hccont)).continuousOn
    · intro y hy
      exact (hden x (by constructor <;> nlinarith [hx.1, hx.2]) y hy).ne'
  have hF'_meas : AEStronglyMeasurable (F' x) μ := by
    have hcont : ContinuousOn (F' x) (Set.Icc (0 : ℝ) 1) := by
      dsimp only [F', sparseWeight]
      apply ContinuousOn.mul (continuous_const.mul hccont).continuousOn
      apply ContinuousOn.div (hqcont.pow 2).continuousOn
        ((continuous_const.add (continuous_const.mul hccont)).pow 2).continuousOn
      intro y hy
      exact pow_ne_zero 2 (hden x (by constructor <;> nlinarith [hx.1, hx.2]) y hy).ne'
    exact hcont.aestronglyMeasurable measurableSet_Icc
  have h_bound : ∀ᵐ y ∂μ, ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (5 / 4), ‖F' z y‖ ≤ (10 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy z hz
    have hh := abs_centeredCoordinate_le_one hy
    have hq := exponentialInterventionDensity_lt_thirteen_div_three hy
    have hqp := exponentialInterventionDensity_pos y
    have hd := hden z hz y hy
    have hdlower : (17 / 20 : ℝ) < 1 + centeredCoordinate z / 10 * centeredCoordinate y := by
      rw [abs_le] at hh
      have hzcenter : (-3 / 2 : ℝ) < centeredCoordinate z ∧
          centeredCoordinate z < 3 / 2 := by
        unfold centeredCoordinate
        constructor <;> linarith [hz.1, hz.2]
      have hzabs : |centeredCoordinate z| < 3 / 2 := (abs_lt).2 ⟨by linarith, hzcenter.2⟩
      have hyabs : |centeredCoordinate y| ≤ 1 := (abs_le).2 hh
      have habs : |centeredCoordinate z / 10 * centeredCoordinate y| < 3 / 20 := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
        calc
          |centeredCoordinate z| / 10 * |centeredCoordinate y| ≤
              |centeredCoordinate z| / 10 * 1 := by gcongr
          _ < 3 / 20 := by nlinarith
      linarith [neg_lt_of_abs_lt habs]
    dsimp only [F', sparseWeight]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, abs_of_pos hqp]
    norm_num only [abs_neg, abs_of_nonneg, one_div]
    rw [show |(1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2| =
        (1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2 by
      exact abs_of_nonneg (sq_nonneg _)]
    have hhs : |centeredCoordinate y| ≤ 1 := hh
    have hnum : exponentialInterventionDensity y ^ 2 < (13 / 3 : ℝ) ^ 2 := by nlinarith
    have hdsq : (17 / 20 : ℝ) ^ 2 <
        (1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2 := by nlinarith
    rw [show (1 / 5 : ℝ) * |centeredCoordinate y| *
        (exponentialInterventionDensity y ^ 2 /
          (1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2) =
        ((1 / 5 : ℝ) * |centeredCoordinate y| *
          exponentialInterventionDensity y ^ 2) /
            (1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2 by ring]
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    nlinarith [sq_nonneg (1 + centeredCoordinate z / 10 * centeredCoordinate y)]
  have hbound_int : Integrable (fun _ : ℝ => (10 : ℝ)) μ := by
    dsimp only [μ]
    exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hdiff : ∀ᵐ y ∂μ, ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (5 / 4),
      HasDerivAt (fun z => F z y) (F' z y) z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy z hz
    have hd := (hden z hz y hy).ne'
    have hh : HasDerivAt (fun z : ℝ => centeredCoordinate z / 10) (1 / 5) z := by
      have hp0 : HasDerivAt (fun u : ℝ => 2 * u - 1) 2 z := by
        convert (hasDerivAt_const_mul (x := z) 2).sub_const 1 using 1
      have hh' := hp0.div_const 10
      apply hh'.congr_deriv
      norm_num
    have hdenDeriv : HasDerivAt
        (fun z : ℝ => 1 + centeredCoordinate z / 10 * centeredCoordinate y)
        ((1 / 5 : ℝ) * centeredCoordinate y) z := by
      simpa using (hh.mul_const (centeredCoordinate y)).const_add 1
    have hnum : HasDerivAt (fun _ : ℝ => exponentialInterventionDensity y ^ 2) 0 z :=
      hasDerivAt_const (x := z) (c := exponentialInterventionDensity y ^ 2)
    have hraw : HasDerivAt
        (fun z : ℝ => exponentialInterventionDensity y ^ 2 /
          (1 + centeredCoordinate z / 10 * centeredCoordinate y))
        ((0 * (1 + centeredCoordinate z / 10 * centeredCoordinate y) -
          exponentialInterventionDensity y ^ 2 *
            ((1 / 5 : ℝ) * centeredCoordinate y)) /
          (1 + centeredCoordinate z / 10 * centeredCoordinate y) ^ 2) z :=
      hnum.div hdenDeriv hd
    dsimp only [F, F', sparseWeight]
    apply hraw.congr_deriv
    field_simp [hd]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) hs hF_meas hF_int
    hF'_meas h_bound hbound_int hdiff
  apply h.2.congr_deriv
  dsimp only [F', μ]
  rw [show (fun y : ℝ => -(1 / 5 : ℝ) * centeredCoordinate y *
      sparseWeight (centeredCoordinate x / 10) y) =
      fun y => -(1 / 5 : ℝ) * (centeredCoordinate y *
        sparseWeight (centeredCoordinate x / 10) y) by funext y; ring]
  rw [MeasureTheory.integral_const_mul]

-- @node: sparseA_deriv_eq
/-- At [a point of the unit interval](hyp:hx), the [derivative of the sparse child-weight
integral equals its centered-weight formula](goal). -/
lemma sparseA_deriv_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv sparseA x =
      -(1 / 5 : ℝ) * ∫ y in Set.Icc (0 : ℝ) 1,
        centeredCoordinate y * sparseWeight (centeredCoordinate x / 10) y :=
  (sparseA_hasDerivAt hx).deriv

-- @node: sparseA_continuousOn
/-- The [sparse child-weight integral is continuous on the unit interval](goal). -/
lemma sparseA_continuousOn : ContinuousOn sparseA (Set.Icc (0 : ℝ) 1) := by
  exact fun x hx => (sparseA_hasDerivAt hx).continuousAt.continuousWithinAt

-- @node: sparseA_deriv_intervalIntegrable
/-- The [derivative of the sparse child-weight integral is interval-integrable](goal). -/
lemma sparseA_deriv_intervalIntegrable :
    IntervalIntegrable (deriv sparseA) volume 0 1 := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simp)
    ((stronglyMeasurable_deriv sparseA).aestronglyMeasurable.restrict) 10 ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  all_goals
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    rw [sparseA_deriv_eq hx']
    rw [norm_mul, Real.norm_eq_abs]
    norm_num only [abs_neg, abs_of_nonneg, one_div]
    have hi : IntegrableOn (fun y => centeredCoordinate y *
        sparseWeight (centeredCoordinate x / 10) y) (Set.Icc (0 : ℝ) 1) := by
      have ha : centeredCoordinate x / 10 ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10) := by
        have hh := abs_centeredCoordinate_le_one hx'
        rw [abs_le] at hh
        exact ⟨by nlinarith [hh.1], by nlinarith [hh.2]⟩
      have hden : ∀ y ∈ Set.Icc (0 : ℝ) 1,
          1 + centeredCoordinate x / 10 * centeredCoordinate y ≠ 0 := by
        intro y hy
        have hh := abs_centeredCoordinate_le_one hy
        rw [abs_le] at hh
        rcases ha with ⟨ha1, ha2⟩
        nlinarith
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.mul (by unfold centeredCoordinate; fun_prop)
      unfold sparseWeight
      apply ContinuousOn.div
      · unfold exponentialInterventionDensity; fun_prop
      · unfold centeredCoordinate; fun_prop
      · intro y hy
        exact pow_ne_zero 2 (hden y hy)
  calc
      (1 / 5 : ℝ) * ‖∫ y in Set.Icc (0 : ℝ) 1,
          centeredCoordinate y * sparseWeight (centeredCoordinate x / 10) y‖ ≤
          (1 / 5 : ℝ) * ∫ y in Set.Icc (0 : ℝ) 1,
            ‖centeredCoordinate y * sparseWeight (centeredCoordinate x / 10) y‖ := by
            gcongr
            exact norm_integral_le_integral_norm _
      _ ≤ (1 / 5 : ℝ) * 50 := by
        gcongr
        calc
          (∫ y in Set.Icc (0 : ℝ) 1,
              ‖centeredCoordinate y * sparseWeight (centeredCoordinate x / 10) y‖) ≤
              ∫ _y in Set.Icc (0 : ℝ) 1, (50 : ℝ) := by
            apply integral_mono_ae hi.norm
              (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
            filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
            have hh := abs_centeredCoordinate_le_one hy
            have hq := exponentialInterventionDensity_lt_thirteen_div_three hy
            have hqp := exponentialInterventionDensity_pos y
            have ha : centeredCoordinate x / 10 ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10) := by
              have hhx := abs_centeredCoordinate_le_one hx'
              rw [abs_le] at hhx
              exact ⟨by nlinarith [hhx.1], by nlinarith [hhx.2]⟩
            have hd : (9 / 10 : ℝ) ≤
                1 + centeredCoordinate x / 10 * centeredCoordinate y := by
              rw [abs_le] at hh
              rcases ha with ⟨ha1, ha2⟩
              nlinarith
            rw [Real.norm_eq_abs, abs_mul]
            simp only [sparseWeight]
            rw [abs_div, abs_pow, abs_of_pos hqp]
            rw [show |(1 + centeredCoordinate x / 10 * centeredCoordinate y) ^ 2| =
                (1 + centeredCoordinate x / 10 * centeredCoordinate y) ^ 2 by
              exact abs_of_nonneg (sq_nonneg _)]
            rw [show |centeredCoordinate y| *
                (exponentialInterventionDensity y ^ 2 /
                  (1 + centeredCoordinate x / 10 * centeredCoordinate y) ^ 2) =
                (|centeredCoordinate y| * exponentialInterventionDensity y ^ 2) /
                  (1 + centeredCoordinate x / 10 * centeredCoordinate y) ^ 2 by ring]
            rw [div_le_iff₀ (sq_pos_of_pos (by linarith))]
            have hqsq : exponentialInterventionDensity y ^ 2 < (13 / 3 : ℝ) ^ 2 := by
              nlinarith
            nlinarith [sq_nonneg (1 + centeredCoordinate x / 10 * centeredCoordinate y)]
          _ = 50 := by simp [Measure.real, Real.volume_Icc]
      _ = 10 := by norm_num

-- @node: neg_cancellationPrimitive_integral_eq_centeredMean
/-- The [integral of the negated cancellation primitive equals its explicit centered mean](goal). -/
lemma neg_cancellationPrimitive_integral_eq_centeredMean :
    (∫ x in Set.Icc (0 : ℝ) 1, -cancellationPrimitive x) =
      1 / (1 - Real.exp (-4)) - 3 / 4 := by
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (u := fun x : ℝ => x) (v := cancellationPrimitive)
    (u' := fun _ => (1 : ℝ))
    (v' := fun x => exponentialInterventionDensity x - 1)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => cancellationPrimitive_hasDerivAt x)
    (continuous_const.intervalIntegrable 0 1)
    ((by unfold exponentialInterventionDensity; fun_prop :
      Continuous (fun x => exponentialInterventionDensity x - 1)).intervalIntegrable 0 1)
  simp only [one_mul, one_mul, zero_mul, sub_zero, cancellationPrimitive_zero] at hip
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_neg]
  have hxq : IntervalIntegrable
      (fun x => x * exponentialInterventionDensity x) volume 0 1 :=
    (by unfold exponentialInterventionDensity; fun_prop :
      Continuous (fun x => x * exponentialInterventionDensity x)).intervalIntegrable 0 1
  have hxone : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hsplit : (∫ x in (0 : ℝ)..1,
      x * (exponentialInterventionDensity x - 1)) =
      (∫ x in (0 : ℝ)..1, x * exponentialInterventionDensity x) -
        ∫ x in (0 : ℝ)..1, x := by
    rw [show (fun x : ℝ => x * (exponentialInterventionDensity x - 1)) =
      fun x => x * exponentialInterventionDensity x - x by funext x; ring,
      intervalIntegral.integral_sub hxq hxone]
  rw [hsplit] at hip
  have hxqeq : (∫ x in (0 : ℝ)..1, x * exponentialInterventionDensity x) =
      1 / (1 - Real.exp (-4)) - 1 / 4 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact exponentialInterventionDensity_firstMoment
  have hid : (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by rw [integral_id]; norm_num
  rw [hxqeq, hid] at hip
  linarith

-- @node: sparse_unreflected_moment_gap
/-- The [unreflected sparse construction has a strictly positive quantitative moment gap](goal). -/
lemma sparse_unreflected_moment_gap :
    (3 / 10000 : ℝ) < ∫ x in Set.Icc (0 : ℝ) 1,
      (1 - exponentialInterventionDensity x) * sparseA x := by
  let C : ℝ := (1 / 6 : ℝ) * ((68 / 9 : ℝ) * (4 / 729) * (100 / 121))
  have hHcont : Continuous cancellationPrimitive := by
    unfold cancellationPrimitive
    fun_prop
  have hqcont : Continuous exponentialInterventionDensity := by
    unfold exponentialInterventionDensity
    fun_prop
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (u := cancellationPrimitive) (v := sparseA)
    (u' := fun x => exponentialInterventionDensity x - 1)
    (v' := deriv sparseA)
    (fun x _ => cancellationPrimitive_hasDerivAt x)
    (fun x hx => by
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      simpa only [sparseA_deriv_eq hx'] using sparseA_hasDerivAt hx')
    ((hqcont.sub continuous_const).intervalIntegrable 0 1)
    sparseA_deriv_intervalIntegrable
  simp only [cancellationPrimitive_zero, zero_mul, sub_self] at hip
  have hgapEq : (∫ x in Set.Icc (0 : ℝ) 1,
      (1 - exponentialInterventionDensity x) * sparseA x) =
      ∫ x in Set.Icc (0 : ℝ) 1, cancellationPrimitive x * deriv sparseA x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [show (fun x : ℝ => (1 - exponentialInterventionDensity x) * sparseA x) =
      fun x => -((exponentialInterventionDensity x - 1) * sparseA x) by funext x; ring,
      intervalIntegral.integral_neg]
    linarith
  rw [hgapEq]
  have hright : IntegrableOn (fun x => cancellationPrimitive x * deriv sparseA x)
      (Set.Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact sparseA_deriv_intervalIntegrable.continuousOn_mul hHcont.continuousOn
  have hleft : IntegrableOn (fun x => (1 / 5 : ℝ) * C * (-cancellationPrimitive x))
      (Set.Icc (0 : ℝ) 1) := by
    exact (continuous_const.mul hHcont.neg).continuousOn.integrableOn_Icc
  have hmono : (∫ x in Set.Icc (0 : ℝ) 1,
      (1 / 5 : ℝ) * C * (-cancellationPrimitive x)) ≤
      ∫ x in Set.Icc (0 : ℝ) 1, cancellationPrimitive x * deriv sparseA x := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hH : cancellationPrimitive x ≤ 0 := (cancellationPrimitive_mem_negUnitInterval hx).2
    have ha : centeredCoordinate x / 10 ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10) := by
      have hh := abs_centeredCoordinate_le_one hx
      rw [abs_le] at hh
      exact ⟨by nlinarith [hh.1], by nlinarith [hh.2]⟩
    have hI := sparseWeight_centered_integral_lower_bound ha
    rw [sparseA_deriv_eq hx]
    dsimp only [C]
    nlinarith
  rw [MeasureTheory.integral_const_mul, neg_cancellationPrimitive_integral_eq_centeredMean] at hmono
  have hcert := sparseWeight_moment_certificate (a := 0) (by norm_num)
  dsimp only [C] at hmono
  have hI0 := sparseWeight_centered_integral_lower_bound
    (show (0 : ℝ) ∈ Set.Icc (-1 / 10) (1 / 10) by norm_num)
  have hgap := exponentialTiltMeanGap_gt
  have hrat := sparseMomentRationalCertificate
  have hexact := sparseMomentCoefficient_exact
  nlinarith

-- @node: sparse_secondMomentContrast_eq_neg_gap
/-- The [sparse witness's second-moment contrast equals the negative analytic gap](goal). -/
lemma sparse_secondMomentContrast_eq_neg_gap (s : SignVector 3) :
    secondMomentContrast
        (canonicalObservedWorld threeNodeDAG (sparseWitness s) (Equiv.refl (Fin 3))) 0 1 =
      -(∫ x in Set.Icc (0 : ℝ) 1,
        (1 - exponentialInterventionDensity x) * sparseA x) := by
  have hpos := sparseWitness_positive_normalized_smooth s
  rw [canonical_secondMomentContrast_eq_integral_for_witness hpos
    (by norm_num : (0 : Fin 3) ≠ 1)]
  let f : LatentState 3 → ℝ := fun v =>
    ((sparseWitness s).q 1 (v 1)) ^ 2 *
      ((sparseWitness s).q 0 (v 0) - (sparseWitness s).p 0 v) *
      (∏ l ∈ (Finset.univ.erase 1).erase 0, (sparseWitness s).p l v) /
        (sparseWitness s).p 1 v
  have hfcont : ContinuousOn f (latentCube 3) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · exact ((hpos.2.2.2.1 1).continuousOn.comp
            ((continuous_apply 1).continuousOn)
            (fun (v : LatentState 3) (hv : v ∈ latentCube 3) =>
              hv 1 (Set.mem_univ 1))).pow 2
        · exact ((hpos.2.2.2.1 0).continuousOn.comp
            ((continuous_apply 0).continuousOn)
            (fun (v : LatentState 3) (hv : v ∈ latentCube 3) =>
              hv 0 (Set.mem_univ 0))).sub
              (hpos.2.2.1 0).continuousOn
      · exact continuousOn_finsetProd _ fun l _ => (hpos.2.2.1 l).continuousOn
    · exact (hpos.2.2.1 1).continuousOn
    · intro v hv
      exact ne_of_gt (hpos.1 1 v hv)
  have hf : Integrable f (volume.restrict (latentCube 3)) :=
    hfcont.integrableOn_compact (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ => isCompact_Icc)
  have hμ : volume.restrict (latentCube 3) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    change volume.restrict (Set.univ.pi fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) = _
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  change (∫ v in latentCube 3, f v) = _
  rw [hμ, integral_fin_three_pi_eq_iterated _ f (by simpa [hμ] using hf)]
  have hone : (volume.restrict (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
    simp [Measure.real, Real.volume_Icc]
  simp only [f, sparseWitness, sparseQ, sparseP,
    Matrix.cons_val_zero, Matrix.cons_val_one, integral_const, hone, one_smul]
  have herase : (Finset.univ.erase (1 : Fin 3)).erase 0 = {2} := by decide
  rw [herase]
  norm_num
  have hrefY (x : ℝ) :
      (∫ y in Set.Icc (0 : ℝ) 1,
        exponentialInterventionDensity (reflectedCoordinate s 1 y) ^ 2 *
          (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) /
          (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s 0 x) *
            centeredCoordinate (reflectedCoordinate s 1 y))) =
      (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) *
        sparseA (reflectedCoordinate s 0 x) := by
    change (∫ y in Set.Icc (0 : ℝ) 1,
      (fun y => exponentialInterventionDensity y ^ 2 *
        (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) /
        (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate y)) (reflectedCoordinate s 1 y)) = _
    have href := integral_reflectedCoordinate s 1
      (fun y => exponentialInterventionDensity y ^ 2 *
        (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) /
        (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate y))
    rw [href]
    unfold sparseA
    rw [show (fun y : ℝ =>
        exponentialInterventionDensity y ^ 2 *
          (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) /
          (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s 0 x) *
            centeredCoordinate y)) =
        fun y => (exponentialInterventionDensity (reflectedCoordinate s 0 x) - 1) *
          (exponentialInterventionDensity y ^ 2 /
            (1 + centeredCoordinate (reflectedCoordinate s 0 x) / 10 *
              centeredCoordinate y)) by funext y; ring,
      MeasureTheory.integral_const_mul]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, one_div]
  simp_rw [hrefY]
  change (∫ x in Set.Icc (0 : ℝ) 1,
    (fun x => (exponentialInterventionDensity x - 1) * sparseA x)
      (reflectedCoordinate s 0 x)) = _
  rw [show (∫ x in Set.Icc (0 : ℝ) 1,
      (fun x => (exponentialInterventionDensity x - 1) * sparseA x)
        (reflectedCoordinate s 0 x)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity x - 1) * sparseA x by
    simpa only using integral_reflectedCoordinate s 0
      (fun x => (exponentialInterventionDensity x - 1) * sparseA x)]
  rw [← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  ring

-- @node: sparse_witness_moment_gap
/-- The [explicit sparse witness has the required strictly positive observed-ratio moment gap](goal). -/
lemma sparse_witness_moment_gap (s : SignVector 3) :
    (3 / 10000 : ℝ) <
      (∫ x, ((canonicalObservedWorld threeNodeDAG (sparseWitness s)
          (Equiv.refl (Fin 3))).ratio 1 x) ^ 2
        ∂(canonicalObservedWorld threeNodeDAG (sparseWitness s)
          (Equiv.refl (Fin 3))).law 0) -
      ∫ x, ((canonicalObservedWorld threeNodeDAG (sparseWitness s)
          (Equiv.refl (Fin 3))).ratio 1 x) ^ 2
        ∂(canonicalObservedWorld threeNodeDAG (sparseWitness s)
          (Equiv.refl (Fin 3))).law (Fin.succ 0) := by
  have hgap := sparse_unreflected_moment_gap
  have hcontrast := sparse_secondMomentContrast_eq_neg_gap s
  unfold secondMomentContrast at hcontrast
  dsimp only [canonicalObservedWorld, Equiv.refl_apply] at hcontrast ⊢
  linarith

-- @node: sparse_witness_mmd_gap
/-- The [explicit sparse witness has the required strictly positive Gaussian-kernel discrepancy](goal). -/
lemma sparse_witness_mmd_gap (s : SignVector 3) :
    (5 / 100000000 : ℝ) < populationDiscrepancy gaussianFeatureMap
      (canonicalObservedWorld threeNodeDAG (sparseWitness s) (Equiv.refl (Fin 3))) 0 1 := by
  let θ := sparseWitness s
  let W := canonicalObservedWorld threeNodeDAG θ (Equiv.refl (Fin 3))
  let μ := observationalRatioLaw W 1
  let ν := interventionalRatioLaw W 0 1
  have hpos : PositiveNormalizedSmoothMechanisms threeNodeDAG θ :=
    sparseWitness_positive_normalized_smooth s
  letI : IsProbabilityMeasure (observationalLaw θ) :=
    observationalLaw_isProbabilityMeasure hpos
  letI : IsProbabilityMeasure (interventionalLaw θ 0) := by
    simpa only [W, canonicalObservedWorld, Equiv.refl_apply] using
      interventionalLaw_isProbabilityMeasure W hpos 0
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (Measure.map (observedLawRatio W.law 1) (observationalLaw θ))
    exact Measure.isProbabilityMeasure_map
      (measurable_observedLawRatio W.law 1).aemeasurable
  letI : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure
      (Measure.map (observedLawRatio W.law 1) (interventionalLaw θ 0))
    exact Measure.isProbabilityMeasure_map
      (measurable_observedLawRatio W.law 1).aemeasurable
  have hobsCube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube 3 :=
    observationalLaw_ae_mem_latentCube hpos
  have hac : interventionalLaw θ 0 ≪ observationalLaw θ := by
    simpa only [W, canonicalObservedWorld, Equiv.refl_apply] using
      interventionalLaw_absolutelyContinuous_observational W hpos 0
  have hintCube : ∀ᵐ v ∂interventionalLaw θ 0, v ∈ latentCube 3 :=
    hac.ae_le hobsCube
  have hratioObs := canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio
    hpos (Equiv.refl (Fin 3)) 1
  have hratioInt : observedLawRatio W.law 1 =ᵐ[interventionalLaw θ 0]
      fun v => θ.q 1 (v 1) / θ.p 1 v := by
    exact hac.ae_eq (by simpa only [W, Equiv.refl_apply] using hratioObs)
  have hμsupport : μ (Set.Icc (0 : ℝ) 5)ᶜ = 0 := by
    dsimp only [μ, observationalRatioLaw]
    rw [Measure.map_apply (measurable_observedLawRatio W.law 1) measurableSet_Icc.compl]
    apply ae_iff.mp
    filter_upwards [hobsCube, hratioObs] with v hv hr
    rw [hr]
    exact ⟨(sparseWitness_child_ratio_bounds s v hv).1.le,
      le_of_lt (sparseWitness_child_ratio_bounds s v hv).2⟩
  have hνsupport : ν (Set.Icc (0 : ℝ) 5)ᶜ = 0 := by
    dsimp only [ν, interventionalRatioLaw]
    change Measure.map (observedLawRatio W.law 1) (interventionalLaw θ 0)
        (Set.Icc (0 : ℝ) 5)ᶜ = 0
    rw [Measure.map_apply (measurable_observedLawRatio W.law 1) measurableSet_Icc.compl]
    apply ae_iff.mp
    filter_upwards [hintCube, hratioInt] with v hv hr
    rw [hr]
    exact ⟨(sparseWitness_child_ratio_bounds s v hv).1.le,
      le_of_lt (sparseWitness_child_ratio_bounds s v hv).2⟩
  have hmom : (3 / 10000 : ℝ) <
      (∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν := by
    rw [canonical_observationalRatioLaw_secondMoment_eq hpos (Equiv.refl (Fin 3)) 1,
      canonical_interventionalRatioLaw_secondMoment_eq hpos (Equiv.refl (Fin 3)) 0 1]
    have hbase := sparse_witness_moment_gap s
    simp only [canonicalObservedWorld, Fin.cases_zero, Fin.cases_succ,
      Equiv.refl_apply] at hbase
    simpa only [μ, ν, θ, W, Equiv.refl_apply] using hbase
  have habs : (3 / 10000 : ℝ) <
      |(∫ r, r ^ 2 ∂μ) - ∫ r, r ^ 2 ∂ν| := by
    rw [abs_of_pos (lt_trans (by norm_num) hmom)]
    exact hmom
  have hlower :=
    CausalSmith.Substrate.GaussianMeanEmbeddingQuantitativeMomentStability.gaussian_meanEmbedding_norm_lowerBound_of_secondMoment_gap
      μ ν hμsupport hνsupport (lt_trans (by norm_num) habs)
  have hrat := sparseMmdRationalCertificate
  rw [← meanEmbedding_gaussianFeatureMap_eq_recovery μ,
    ← meanEmbedding_gaussianFeatureMap_eq_recovery ν] at hlower
  unfold populationDiscrepancy
  nlinarith [hlower.2]

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
