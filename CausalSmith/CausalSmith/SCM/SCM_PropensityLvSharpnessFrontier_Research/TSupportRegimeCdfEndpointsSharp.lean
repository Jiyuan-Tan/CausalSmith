import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CdfMaps
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TBowMixtureCompleteness
import Mathlib.Probability.CDF
import Mathlib.Probability.ConditionalProbability
import Causalean.PO.ID.Partial.Basic

/-! # Sharp CDF endpoints in both support regimes -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open scoped ENNReal

/-- For the specified model objects, [the stated conditions](hyp:he0,he1,hQ), [the stated mathematical relationship holds](goal). -/
-- @node: cdf_mixture_formula
lemma cdf_mixture_formula (e : ℝ) (P R Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R] [IsProbabilityMeasure Q]
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hQ : Q = ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R)
    (y : ℝ) :
    cdf Q y = e * cdf P y + (1 - e) * cdf R y := by
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real, hQ]
  simp only [measureReal_def, Measure.add_apply, Measure.smul_apply, measurableSet_Iic]
  rw [ENNReal.toReal_add]
  · simp [ENNReal.smul_def, ENNReal.toReal_ofReal he0,
      ENNReal.toReal_ofReal (sub_nonneg.mpr he1)]
  all_goals
    exact ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _)

/-- For [the stated conditions](hyp:s,y), [the cdfResidual object](goal) is defined as specified. -/
-- @node: cdfResidual
noncomputable def cdfResidual (s y : ℝ) : Measure ℝ :=
  ENNReal.ofReal s • Measure.dirac y + ENNReal.ofReal (1 - s) • Measure.dirac (y + 1)

/-- For the specified model objects, [the stated conditions](hyp:hs), [the stated mathematical relationship holds](goal). -/
-- @node: cdfResidual_prob
lemma cdfResidual_prob (s y : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (cdfResidual s y) := by
  constructor
  simp only [cdfResidual, Measure.add_apply, Measure.smul_apply, MeasurableSet.univ,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)]
  norm_num

/-- For the specified model objects, [the stated conditions](hyp:hs), [the stated mathematical relationship holds](goal). -/
-- @node: cdfResidual_cdf
lemma cdfResidual_cdf (s y : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cdf (cdfResidual s y) y = s := by
  letI := cdfResidual_prob s y hs
  rw [cdf_eq_real]
  simp [measureReal_def, cdfResidual, hs.1, sub_nonneg.mpr hs.2]

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: mixture_isProbability
lemma mixture_isProbability (e : ℝ) (P R : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IsProbabilityMeasure
      (ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R) := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, MeasurableSet.univ,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add he0 (sub_nonneg.mpr he1)]
  norm_num

/-- For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal). -/
-- @node: oneSided_cdf_range
lemma oneSided_cdf_range (a : Bool) (e : ℝ) (P : Measure ℝ)
    [IsProbabilityMeasure P] (he : StrictPositivity e) (y : ℝ) :
    {r : ℝ | ∃ Q ∈ bowCompatibleOneSidedSet a e P, r = cdf Q y} =
      Set.Icc (e * cdf P y) (e * cdf P y + 1 - e) := by
  rw [(bowCompatibleOneSided_eq_mixtureClassOneSided a e P he).1]
  ext r
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨R, hR, hrep⟩ := hQ.representation (ne_of_lt he.2)
    let _ := hR
    let _ := hQ.candidate_probability
    have hformula := cdf_mixture_formula e P R Q he.1.le he.2.le hrep y
    rw [hformula]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le) (cdf_nonneg R y)]
    · nlinarith [mul_le_mul_of_nonneg_left (cdf_le_one R y)
        (sub_nonneg.mpr he.2.le)]
  · intro hr
    let s := (r - e * cdf P y) / (1 - e)
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [s]
      constructor
      · exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr he.2.le)
      · apply (div_le_one (sub_pos.mpr he.2)).2
        linarith [hr.2]
    let R := cdfResidual s y
    let _ := cdfResidual_prob s y hs
    let Q := ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R
    let _ := mixture_isProbability e P R he.1.le he.2.le
    refine ⟨Q, ?_, ?_⟩
    · exact
        { positivity := Or.inr he
          observed_probability := inferInstance
          candidate_probability := inferInstance
          representation := fun _ => ⟨R, inferInstance, rfl⟩
          boundary := fun h => (ne_of_lt he.2 h).elim }
    · rw [cdf_mixture_formula e P R Q he.1.le he.2.le rfl y,
        cdfResidual_cdf s y hs]
      dsimp [s]
      field_simp [ne_of_gt (sub_pos.mpr he.2)]
      ring

/-- For the specified model objects, [the stated conditions](hyp:hpos), [the stated mathematical relationship holds](goal). -/
-- @node: cond_cdf_one
lemma cond_cdf_one (P : Measure ℝ) [IsProbabilityMeasure P] (y : ℝ)
    (hpos : 0 < cdf P y) :
    cdf P[|Set.Iic y] y = 1 := by
  have hne : P (Set.Iic y) ≠ 0 := by
    rw [← ofReal_cdf P y]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  let _ := cond_isProbabilityMeasure hne
  rw [cdf_eq_real, measureReal_def, cond_apply_self hne (measure_ne_top _ _)]
  norm_num

/-- For the specified model objects, [the stated conditions](hyp:hlt), [the stated mathematical relationship holds](goal). -/
-- @node: cond_cdf_zero
lemma cond_cdf_zero (P : Measure ℝ) [IsProbabilityMeasure P] (y : ℝ)
    (hlt : cdf P y < 1) :
    cdf P[|(Set.Iic y)ᶜ] y = 0 := by
  have hne : P (Set.Iic y)ᶜ ≠ 0 := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
      ← ofReal_cdf P y]
    exact ne_of_gt (tsub_pos_iff_lt.mpr (by
      simpa [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hlt))
  let _ := cond_isProbabilityMeasure hne
  rw [cdf_eq_real, measureReal_def, cond_apply (measurableSet_Iic.compl) P]
  have hinter : (Set.Iic y)ᶜ ∩ Set.Iic y = ∅ := by ext; simp
  rw [hinter]
  simp

/-- For [the stated conditions](hyp:P,y,s), [the dominatedCdfResidual object](goal) is defined as specified. -/
-- @node: dominatedCdfResidual
noncomputable def dominatedCdfResidual (P : Measure ℝ) (y s : ℝ) : Measure ℝ :=
  ENNReal.ofReal s • P[|Set.Iic y] +
    ENNReal.ofReal (1 - s) • P[|(Set.Iic y)ᶜ]

/-- For the specified model objects, [the stated conditions](hyp:hp,hp',hs), [the stated mathematical relationship holds](goal). -/
-- @node: dominatedCdfResidual_prob
lemma dominatedCdfResidual_prob (P : Measure ℝ) [IsProbabilityMeasure P]
    (y s : ℝ) (hp : 0 < cdf P y) (hp' : cdf P y < 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (dominatedCdfResidual P y s) := by
  have hB : P (Set.Iic y) ≠ 0 := by
    rw [← ofReal_cdf P y]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hBc : P (Set.Iic y)ᶜ ≠ 0 := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
      ← ofReal_cdf P y]
    exact ne_of_gt (tsub_pos_iff_lt.mpr (by
      simpa [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hp'))
  let _ := cond_isProbabilityMeasure hB
  let _ := cond_isProbabilityMeasure hBc
  exact mixture_isProbability s P[|Set.Iic y] P[|(Set.Iic y)ᶜ] hs.1 hs.2

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: dominatedCdfResidual_ac
lemma dominatedCdfResidual_ac (P : Measure ℝ) (y s : ℝ) :
    (dominatedCdfResidual P y s).AbsolutelyContinuous P := by
  intro B hPB
  rw [dominatedCdfResidual, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, cond_absolutelyContinuous hPB,
    cond_absolutelyContinuous hPB]
  simp

/-- For the specified model objects, [the stated conditions](hyp:hp,hp',hs), [the stated mathematical relationship holds](goal). -/
-- @node: dominatedCdfResidual_cdf
lemma dominatedCdfResidual_cdf (P : Measure ℝ) [IsProbabilityMeasure P]
    (y s : ℝ) (hp : 0 < cdf P y) (hp' : cdf P y < 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cdf (dominatedCdfResidual P y s) y = s := by
  let _ := dominatedCdfResidual_prob P y s hp hp' hs
  have hB : P (Set.Iic y) ≠ 0 := by
    rw [← ofReal_cdf P y]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hBc : P (Set.Iic y)ᶜ ≠ 0 := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
      ← ofReal_cdf P y]
    exact ne_of_gt (tsub_pos_iff_lt.mpr (by
      simpa [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hp'))
  let _ := cond_isProbabilityMeasure hB
  let _ := cond_isProbabilityMeasure hBc
  rw [cdf_mixture_formula s P[|Set.Iic y] P[|(Set.Iic y)ᶜ]
      (dominatedCdfResidual P y s) hs.1 hs.2 rfl y,
    cond_cdf_one P y hp, cond_cdf_zero P y hp']
  ring

/-- For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal). -/
-- @node: self_mem_mixture
lemma self_mem_mixture (e : ℝ) (P : Measure ℝ) [IsProbabilityMeasure P]
    (he : StrictPositivity e) : P ∈ mixtureClassSet e P := by
  refine
    { positivity := Or.inr he
      observed_probability := inferInstance
      candidate_probability := inferInstance
      representation := fun _ => ⟨P, inferInstance, Measure.AbsolutelyContinuous.rfl, ?_⟩
      boundary := fun _ => rfl }
  ext B hB
  simp only [Measure.add_apply, Measure.smul_apply, hB, smul_eq_mul]
  rw [← add_mul, ← ENNReal.ofReal_add he.1.le (sub_nonneg.mpr he.2.le)]
  norm_num

/-- For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal). -/
-- @node: mutual_cdf_range
lemma mutual_cdf_range (a : Bool) (e : ℝ) (P : Measure ℝ)
    [IsProbabilityMeasure P] (he : StrictPositivity e) (y : ℝ) :
    {r : ℝ | ∃ Q ∈ bowCompatibleSet a e P, r = cdf Q y} =
      Set.Icc (if cdf P y < 1 then e * cdf P y else 1)
        (if cdf P y = 0 then 0 else e * cdf P y + 1 - e) := by
  rw [(bowCompatible_eq_mixtureClass a e P he).1]
  ext r
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨R, hR, hRac, hrep⟩ := hQ.representation (ne_of_lt he.2)
    let _ := hR
    let _ := hQ.candidate_probability
    have hformula := cdf_mixture_formula e P R Q he.1.le he.2.le hrep y
    by_cases hp0 : cdf P y = 0
    · have hPzero : P (Set.Iic y) = 0 := by
        rw [← ofReal_cdf P y, hp0]
        norm_num
      have hRzero := hRac hPzero
      have hRcdf : cdf R y = 0 := by
        rw [cdf_eq_real, measureReal_def, hRzero]
        norm_num
      rw [hformula, hp0, hRcdf]
      simp
    · by_cases hp1 : cdf P y = 1
      · have hPcomp : P (Set.Iic y)ᶜ = 0 := by
          rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
            ← ofReal_cdf P y, hp1]
          norm_num
        have hRcomp := hRac hPcomp
        have hRset_le : R (Set.Iic y) ≤ 1 := by
          calc
            R (Set.Iic y) ≤ R Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hRset_ge : 1 ≤ R (Set.Iic y) := by
          apply tsub_eq_zero_iff_le.mp
          rw [measure_compl measurableSet_Iic (measure_ne_top R (Set.Iic y)),
            measure_univ] at hRcomp
          exact hRcomp
        have hRset : R (Set.Iic y) = 1 := le_antisymm hRset_le hRset_ge
        have hRcdf : cdf R y = 1 := by
          rw [cdf_eq_real, measureReal_def, hRset]
          norm_num
        rw [hformula, hp1, hRcdf]
        norm_num
      · have hpPos : 0 < cdf P y := lt_of_le_of_ne (cdf_nonneg P y) (Ne.symm hp0)
        have hpLt : cdf P y < 1 := lt_of_le_of_ne (cdf_le_one P y) hp1
        rw [if_pos hpLt, if_neg hp0, hformula]
        constructor
        · nlinarith [mul_nonneg (sub_nonneg.mpr he.2.le) (cdf_nonneg R y)]
        · nlinarith [mul_le_mul_of_nonneg_left (cdf_le_one R y)
            (sub_nonneg.mpr he.2.le)]
  · intro hr
    by_cases hp0 : cdf P y = 0
    · have hpLt : cdf P y < 1 := by rw [hp0]; norm_num
      have rr : r = 0 := by simpa [hp0, hpLt] using hr
      exact ⟨P, self_mem_mixture e P he, by simpa [rr, hp0]⟩
    · by_cases hp1 : cdf P y = 1
      · have rr : r = 1 := by simpa [hp1] using hr
        exact ⟨P, self_mem_mixture e P he, by simpa [rr, hp1]⟩
      · have hpPos : 0 < cdf P y := lt_of_le_of_ne (cdf_nonneg P y) (Ne.symm hp0)
        have hpLt : cdf P y < 1 := lt_of_le_of_ne (cdf_le_one P y) hp1
        rw [if_pos hpLt, if_neg hp0] at hr
        let s := (r - e * cdf P y) / (1 - e)
        have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
          dsimp [s]
          constructor
          · exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr he.2.le)
          · apply (div_le_one (sub_pos.mpr he.2)).2
            linarith [hr.2]
        let R := dominatedCdfResidual P y s
        let _ := dominatedCdfResidual_prob P y s hpPos hpLt hs
        let Q := ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R
        let _ := mixture_isProbability e P R he.1.le he.2.le
        refine ⟨Q, ?_, ?_⟩
        · exact
            { positivity := Or.inr he
              observed_probability := inferInstance
              candidate_probability := inferInstance
              representation := fun _ =>
                ⟨R, inferInstance, dominatedCdfResidual_ac P y s, rfl⟩
              boundary := fun h => (ne_of_lt he.2 h).elim }
        · rw [cdf_mixture_formula e P R Q he.1.le he.2.le rfl y,
            dominatedCdfResidual_cdf P y s hpPos hpLt hs]
          dsimp [s]
          field_simp [ne_of_gt (sub_pos.mpr he.2)]
          ring


/-- The unrestricted and mutual-support bow classes have the stated sharp CDF
intervals, including atoms and the probability-zero/one contacts.  For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:support-regime-cdf-endpoints-sharp
theorem support_regime_cdf_endpoints_sharp (a : Bool) (e : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (he : StrictPositivity e) (y : ℝ) :
    {r : ℝ | ∃ Q ∈ bowCompatibleOneSidedSet a e P, r = cdf Q y} =
        Set.Icc (cdfEndpointsOneSided (endpointPropensity e (Or.inl he))
          (cdfProbability P y)).1
          (cdfEndpointsOneSided (endpointPropensity e (Or.inl he))
            (cdfProbability P y)).2 ∧
    {r : ℝ | ∃ Q ∈ bowCompatibleSet a e P, r = cdf Q y} =
        Set.Icc (cdfEndpoints (endpointPropensity e (Or.inl he))
          (cdfProbability P y)).1
          (cdfEndpoints (endpointPropensity e (Or.inl he))
            (cdfProbability P y)).2 := by
  constructor
  · simpa [cdfEndpointsOneSided, endpointPropensity, cdfProbability] using
      oneSided_cdf_range a e P he y
  · rw [mutual_cdf_range a e P he y]
    rfl
  -- @realizes y(real CDF threshold)
  -- @realizes F_P,F_Q(CDF evaluations cdf P y and cdf Q y)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
