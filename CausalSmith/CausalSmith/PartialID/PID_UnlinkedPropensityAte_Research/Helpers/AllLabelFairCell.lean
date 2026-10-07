module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelCouplingRange
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointConstruction
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCellTransport
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelCellScaling

/-! Fair-outcome cell identities for the all-label ambiguity witness. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Pointwise
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcomeReleasedLaw_restrictedOutcomeMap {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J) :
    ((halfOutcomeReleasedLaw H g).restrict
        {z | z.1 = r ∧ z.2.1 = a}).map (fun z => (z.2.2 : ℝ)) =
      (ENNReal.ofReal (armCellMass H g a r) / 2) •
        (Measure.dirac 0 + Measure.dirac 1) := by
  classical
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB]
  rw [Measure.restrict_apply (hB.preimage (by fun_prop))]
  simp [halfOutcomeReleasedLaw, hB]
  rw [Finset.sum_eq_single r]
  · cases a <;>
      by_cases h0 : (0 : ℝ) ∈ B <;>
      by_cases h1 : (1 : ℝ) ∈ B <;>
      simp [Set.indicator, h0, h1]
  · intro b hb hbr
    simp [hbr]
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcomeReleasedLaw_armCellOutcomeLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    armCellOutcomeLaw (halfOutcomeReleasedLaw H g)
        (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg).2.1 a r
        (by
          rw [(halfOutcomeReleasedLaw_cellMasses H g hOverlap hg).2.2.2 a r]
          exact hq) =
      fairBernoulliLaw := by
  let Prel := halfOutcomeReleasedLaw H g
  let hMass := halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
  letI : IsProbabilityMeasure Prel := hMass.2.1
  have hmassReal :
      Prel.real {z | z.1 = r ∧ z.2.1 = a} = armCellMass H g a r :=
    hMass.2.2.2 a r
  have hmass :
      Prel {z | z.1 = r ∧ z.2.1 = a} =
        ENNReal.ofReal (armCellMass H g a r) := by
    calc
      _ = ENNReal.ofReal
          (Prel.real {z | z.1 = r ∧ z.2.1 = a}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := by rw [hmassReal]
  have hq0 : ENNReal.ofReal (armCellMass H g a r) ≠ 0 :=
    by simp [ENNReal.ofReal_eq_zero, not_le.mpr hq]
  unfold armCellOutcomeLaw
  rw [halfOutcomeReleasedLaw_restrictedOutcomeMap H g hOverlap hg a r]
  rw [show (halfOutcomeReleasedLaw H g) {z | z.1 = r ∧ z.2.1 = a} =
      ENNReal.ofReal (armCellMass H g a r) by exact hmass]
  rw [smul_smul]
  unfold fairBernoulliLaw
  congr 1
  rw [div_eq_mul_inv]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma inverseArmProb_mem_admissibleCenters {ε : ℝ}
    (hOverlap : Overlap ε) (a : ArmSpace) (e : ScoreSpace ε) :
    (armProb a e)⁻¹ ∈ Icc ((1 - ε)⁻¹) ε⁻¹ := by
  have hb := projectionArmProb_bounds hOverlap a e
  have hp : 0 < armProb a e := lt_of_lt_of_le hOverlap.1 hb.1
  have hOne : 0 < 1 - ε := by linarith [hOverlap.1, hOverlap.2]
  have hpUpper : armProb a e ≤ 1 - ε := by
    rcases e.property with ⟨he0, he1⟩
    cases a <;> simp [armProb] <;> linarith
  exact ⟨(inv_le_inv₀ hOne hp).2 hpUpper,
    (inv_le_inv₀ hp hOverlap.1).2 hb.1⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellWeightLaw_support_admissibleCenters {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (armCellWeightLaw H inferInstance g hg a r hq)
      (Icc ((1 - ε)⁻¹) ε⁻¹)ᶜ = 0 := by
  let G := armCellScoreLaw H inferInstance g hg a r hq
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hg hOverlap a r hq
  unfold armCellWeightLaw
  rw [Measure.map_apply (measurable_inverseArmProb a) measurableSet_Icc.compl]
  have hpre :
      (fun e : ScoreSpace ε => (armProb a e)⁻¹) ⁻¹'
          (Icc ((1 - ε)⁻¹) ε⁻¹)ᶜ = ∅ := by
    ext e
    simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false,
      iff_false]
    exact fun he => he (inverseArmProb_mem_admissibleCenters hOverlap a e)
  rw [hpre]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,a,b,τ,hμ,hτ0,hτ1), this result [establishes the stated mathematical conclusion](goal). -/
lemma quantile_mem_Icc_of_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b τ : ℝ}
    (hμ : μ (Icc a b)ᶜ = 0) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Causalean.Stat.quantile μ τ ∈ Icc a b := by
  have hcompb : μ (Iic b)ᶜ = 0 := measure_mono_null (by
    intro x hx hxab
    exact hx hxab.2) hμ
  have hmu_b : μ (Iic b) = 1 := by
    have hh := measure_compl (μ := μ) (s := (Iic b)ᶜ)
      (by measurability) (by simp)
    simpa only [compl_compl, hcompb, tsub_zero, measure_univ] using hh
  have hcdfb : cdf μ b = 1 := by
    rw [cdf_eq_real, measureReal_def, hmu_b]
    norm_num
  have hlow (t : ℝ) (ht : t < a) : cdf μ t = 0 := by
    have hh : μ (Iic t) = 0 := measure_mono_null (by
      intro x hx hxab
      exact (not_le_of_gt (lt_of_le_of_lt hx ht)) hxab.1) hμ
    rw [cdf_eq_real, measureReal_def, hh]
    norm_num
  constructor
  · by_contra hn
    have hqa : Causalean.Stat.quantile μ τ < a := lt_of_not_ge hn
    have hle := Causalean.Stat.le_cdf_quantile (μ := μ) hτ1
    rw [hlow _ hqa] at hle
    linarith
  · exact (Causalean.Stat.quantile_le_iff hτ0 hτ1).mpr
      (by rw [hcdfb]; exact hτ1.le)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellWeightLaw_median_mem_admissibleCenters {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    Causalean.Stat.quantile
        (armCellWeightLaw H inferInstance g hg a r hq) (1 / 2) ∈
      Icc ((1 - ε)⁻¹) ε⁻¹ := by
  let G := armCellScoreLaw H inferInstance g hg a r hq
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hg hOverlap a r hq
  letI : IsProbabilityMeasure
      (armCellWeightLaw H inferInstance g hg a r hq) :=
    Measure.isProbabilityMeasure_map (measurable_inverseArmProb a).aemeasurable
  exact quantile_mem_Icc_of_support _
    (armCellWeightLaw_support_admissibleCenters H g hOverlap hg a r hq)
    (by norm_num) (by norm_num)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellWeightLaw_memLp_two {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    MemLp (fun w : ℝ => w) 2
      (armCellWeightLaw H inferInstance g hg a r hq) := by
  let G := armCellScoreLaw H inferInstance g hg a r hq
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hg hOverlap a r hq
  letI : IsProbabilityMeasure
      (armCellWeightLaw H inferInstance g hg a r hq) :=
    Measure.isProbabilityMeasure_map (measurable_inverseArmProb a).aemeasurable
  have hs := armCellWeightLaw_support_admissibleCenters
    H g hOverlap hg a r hq
  have hlower : 0 ≤ (1 - ε)⁻¹ := by
    apply inv_nonneg.mpr
    linarith [hOverlap.1, hOverlap.2]
  have hs' :
      (armCellWeightLaw H inferInstance g hg a r hq)
        (Icc 0 ε⁻¹)ᶜ = 0 := by
    apply measure_mono_null _ hs
    intro w hw hmem
    exact hw ⟨hlower.trans hmem.1, hmem.2⟩
  apply memLp_of_bounded
  · rw [ae_iff]
    exact hs'
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma fairOutcome_normalizedQuantileGap_eq_sInf_absoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    (∫ u in (0 : ℝ)..1,
        generalizedQuantile fairBernoulliLaw u *
          generalizedQuantile
            (armCellWeightLaw H inferInstance g hg a r hq) u) -
      (∫ u in (0 : ℝ)..1,
        generalizedQuantile fairBernoulliLaw u *
          generalizedQuantile
            (armCellWeightLaw H inferInstance g hg a r hq) (1 - u)) =
      sInf {v : ℝ | ∃ c ∈ Icc ((1 - ε)⁻¹) ε⁻¹,
        v = ∫ w, |w - c| ∂
          (armCellWeightLaw H inferInstance g hg a r hq)} := by
  let W := armCellWeightLaw H inferInstance g hg a r hq
  let G := armCellScoreLaw H inferInstance g hg a r hq
  letI : IsProbabilityMeasure G :=
    armCellScoreLaw_isProbabilityMeasure H g hg hOverlap a r hq
  letI : IsProbabilityMeasure W :=
    Measure.isProbabilityMeasure_map (measurable_inverseArmProb a).aemeasurable
  have hYae : ∀ᵐ y ∂fairBernoulliLaw, y ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    simp [fairBernoulliLaw]
  have hY2 : MemLp (fun y : ℝ => y) 2 fairBernoulliLaw := by
    apply memLp_of_bounded
    · exact hYae
    · fun_prop
  have hW2 : MemLp (fun w : ℝ => w) 2 W :=
    armCellWeightLaw_memLp_two H g hOverlap hg a r hq
  have hC : (Icc ((1 - ε)⁻¹) ε⁻¹).Nonempty := by
    refine ⟨Causalean.Stat.quantile W (1 / 2), ?_⟩
    exact armCellWeightLaw_median_mem_admissibleCenters
      H g hOverlap hg a r hq
  have heq :=
    fairBernoulli_monotoneCoupling_gap_eq_sInf_absoluteDeviation
      W hW2 (Icc ((1 - ε)⁻¹) ε⁻¹) hC
      (armCellWeightLaw_median_mem_admissibleCenters
        H g hOverlap hg a r hq)
  rw [product_expectation_comonotoneCoupling_interval
      fairBernoulliLaw W hY2 hW2,
    product_expectation_countermonotoneCoupling_interval
      fairBernoulliLaw W] at heq
  simpa [W] using heq

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma fairOutcome_positiveCell_gap_eq_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    armCellMass H g a r *
      ((∫ u in (0 : ℝ)..1,
          generalizedQuantile fairBernoulliLaw u *
            generalizedQuantile
              (armCellWeightLaw H inferInstance g hg a r hq) u) -
        (∫ u in (0 : ℝ)..1,
          generalizedQuantile fairBernoulliLaw u *
            generalizedQuantile
              (armCellWeightLaw H inferInstance g hg a r hq) (1 - u))) =
      cellAbsoluteDeviation H g a r := by
  let Prel := halfOutcomeReleasedLaw H g
  let hMass := halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
  let W := armCellWeightLaw H inferInstance g hg a r hq
  let A : Set ℝ :=
    {v : ℝ | ∃ c ∈ Icc ((1 - ε)⁻¹) ε⁻¹,
      v = ∫ w, |w - c| ∂W}
  let B : Set ℝ :=
    {v : ℝ | ∃ c ∈ Icc ((1 - ε)⁻¹) ε⁻¹,
      v = ∫ e in cell g r, |1 - c * armProb a e| ∂H}
  have hscale (c : ℝ) :
      armCellMass H g a r * (∫ w, |w - c| ∂W) =
        ∫ e in cell g r, |1 - c * armProb a e| ∂H := by
    exact armCellWeightLaw_absoluteDeviation
      H g Prel hMass hOverlap a r hq c
  have hset : B = armCellMass H g a r • A := by
    ext v
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Set.mem_smul_set]
      refine ⟨∫ w, |w - c| ∂W, ⟨c, hc, rfl⟩, ?_⟩
      simpa [smul_eq_mul] using hscale c
    · intro hv
      rw [Set.mem_smul_set] at hv
      rcases hv with ⟨x, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨c, hc, ?_⟩
      simpa [smul_eq_mul] using hscale c
  rw [fairOutcome_normalizedQuantileGap_eq_sInf_absoluteDeviation
    H g hOverlap hg a r hq]
  unfold cellAbsoluteDeviation
  change armCellMass H g a r * sInf A = sInf B
  rw [hset, Real.sInf_smul_of_nonneg hq.le, smul_eq_mul]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcomeReleasedLaw_positiveCell_gap_eq_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : 0 < armCellMass H g a r) :
    let hMass := halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
    armCellMass H g a r *
      ((∫ u in (0 : ℝ)..1,
          generalizedQuantile
              (armCellOutcomeLaw (halfOutcomeReleasedLaw H g) hMass.2.1 a r
                (by rw [hMass.2.2.2 a r]; exact hq)) u *
            generalizedQuantile
              (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) u) -
        (∫ u in (0 : ℝ)..1,
          generalizedQuantile
              (armCellOutcomeLaw (halfOutcomeReleasedLaw H g) hMass.2.1 a r
                (by rw [hMass.2.2.2 a r]; exact hq)) u *
            generalizedQuantile
              (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) (1 - u))) =
      cellAbsoluteDeviation H g a r := by
  dsimp only
  rw [halfOutcomeReleasedLaw_armCellOutcomeLaw H g hOverlap hg a r hq]
  exact fairOutcome_positiveCell_gap_eq_cellAbsoluteDeviation
    H g hOverlap hg a r hq

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_eq_zero_of_armCellMass_nonpos
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (hq : ¬0 < armCellMass H g a r) :
    cellAbsoluteDeviation H g a r = 0 := by
  have hInt : IntegrableOn (fun e : ScoreSpace ε => armProb a e)
      (cell g r) H := by
    apply Integrable.of_bound
      (by cases a <;> simp [armProb] <;> fun_prop) 1
    filter_upwards [] with e
    rcases e.property with ⟨he0, he1⟩
    cases a <;> simp [armProb, abs_le] <;> constructor <;>
      linarith [hOverlap.1, hOverlap.2]
  have hlower :
      ε * H.real (cell g r) ≤ armCellMass H g a r := by
    have hmono : (∫ _ in cell g r, ε ∂H) ≤
        ∫ e in cell g r, armProb a e ∂H := by
      apply integral_mono (integrable_const ε) hInt
      intro e
      rcases e.property with ⟨he0, he1⟩
      cases a <;> simp [armProb] <;> linarith
    simpa [armCellMass, Measure.real_def, mul_comm] using hmono
  have hq0 : armCellMass H g a r ≤ 0 := le_of_not_gt hq
  have hreal0 : H.real (cell g r) = 0 := by
    have hrealNonneg : 0 ≤ H.real (cell g r) := measureReal_nonneg
    nlinarith [hOverlap.1]
  have hmeasure0 : H (cell g r) = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff _).mp hreal0).resolve_right
      (measure_ne_top H (cell g r))
  have hrestrict : H.restrict (cell g r) = 0 := by
    ext B hB
    rw [Measure.restrict_apply hB]
    exact measure_mono_null inter_subset_right hmeasure0
  have hzero (c : ℝ) :
      (∫ e in cell g r, |1 - c * armProb a e| ∂H) = 0 := by
    change (∫ e, |1 - c * armProb a e| ∂(H.restrict (cell g r))) = 0
    rw [hrestrict]
    simp
  have hC : (Icc ((1 - ε)⁻¹) ε⁻¹).Nonempty := by
    refine ⟨ε⁻¹, ?_, le_rfl⟩
    have hOne : 0 < 1 - ε := by linarith [hOverlap.1, hOverlap.2]
    exact (inv_le_inv₀ hOne hOverlap.1).2 (by linarith [hOverlap.2])
  unfold cellAbsoluteDeviation
  have hset :
      {v : ℝ | ∃ c ∈ Icc ((1 - ε)⁻¹) ε⁻¹,
        v = ∫ e in cell g r, |1 - c * armProb a e| ∂H} = {0} := by
    ext v
    constructor
    · rintro ⟨c, hc, rfl⟩
      simp [hzero c]
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      rcases hC with ⟨c, hc⟩
      exact ⟨c, hc, by rw [hzero c, hv0]⟩
  rw [hset]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcomeReleasedLaw_cellGap_eq_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J) :
    let hMass := halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
    (if hq : 0 < armCellMass H g a r then
        armCellMass H g a r *
          ∫ u in (0 : ℝ)..1,
            generalizedQuantile
                (armCellOutcomeLaw (halfOutcomeReleasedLaw H g) hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq)) u *
              generalizedQuantile
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) u
      else 0) -
      (if hq : 0 < armCellMass H g a r then
        armCellMass H g a r *
          ∫ u in (0 : ℝ)..1,
            generalizedQuantile
                (armCellOutcomeLaw (halfOutcomeReleasedLaw H g) hMass.2.1 a r
                  (by rw [hMass.2.2.2 a r]; exact hq)) u *
              generalizedQuantile
                (armCellWeightLaw H hMass.1 g hMass.2.2.1 a r hq) (1 - u)
      else 0) =
      cellAbsoluteDeviation H g a r := by
  dsimp only
  by_cases hq : 0 < armCellMass H g a r
  · simp only [hq, dif_pos]
    have hpos :=
      halfOutcomeReleasedLaw_positiveCell_gap_eq_cellAbsoluteDeviation
        H g hOverlap hg a r hq
    dsimp only at hpos
    ring_nf at hpos ⊢
    exact hpos
  · simp only [hq, dif_neg, zero_sub]
    simpa [hq] using
      (cellAbsoluteDeviation_eq_zero_of_armCellMass_nonpos
        H g hOverlap hg a r hq).symm

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcome_muUpper_sub_muLower_eq_sum_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g)
    (a : ArmSpace) :
    let hMass := halfOutcomeReleasedLaw_cellMasses H g hOverlap hg
    muUpper H g (halfOutcomeReleasedLaw H g) hMass a -
        muLower H g (halfOutcomeReleasedLaw H g) hMass a =
      ∑ r : LabelSpace J, cellAbsoluteDeviation H g a r := by
  dsimp only
  unfold muUpper muLower
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact halfOutcomeReleasedLaw_cellGap_eq_cellAbsoluteDeviation
    H g hOverlap hg a r

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcome_sharpATELength_eq_sum_cellAbsoluteDeviation
    {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    sharpATELength H g (halfOutcomeReleasedLaw H g)
        (halfOutcomeReleasedLaw_cellMasses H g hOverlap hg) =
      ∑ r : LabelSpace J,
        (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r) := by
  have htrue :=
    halfOutcome_muUpper_sub_muLower_eq_sum_cellAbsoluteDeviation
      H g hOverlap hg true
  have hfalse :=
    halfOutcome_muUpper_sub_muLower_eq_sum_cellAbsoluteDeviation
      H g hOverlap hg false
  dsimp only at htrue hfalse
  unfold sharpATELength
  rw [Finset.sum_add_distrib]
  linarith

end
end CausalSmith.PartialID.UnlinkedPropensityAte
