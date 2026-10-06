module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TAllLabelAmbiguity

/-! Universal point identification is equivalent to score recovery from the label. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: cellAbsoluteDeviation_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_nonneg {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε)
    (a : ArmSpace) (r : LabelSpace J) :
    0 ≤ cellAbsoluteDeviation H g a r := by
  unfold cellAbsoluteDeviation
  apply le_csInf
  · refine ⟨_, ε⁻¹, ?_, rfl⟩
    rcases hOverlap with ⟨hε, hεhalf⟩
    constructor
    · simpa only [one_div] using
        (one_div_le_one_div_of_le hε (show ε ≤ 1 - ε by linarith))
    · exact le_refl _
  · rintro v ⟨c, hc, rfl⟩
    exact integral_nonneg (fun e => abs_nonneg _)

-- @node: cellAbsoluteDeviation_le_integral
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,a,r,c,hc), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_le_integral {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (a : ArmSpace) (r : LabelSpace J) (c : ℝ)
    (hc : c ∈ Set.Icc ((1 - ε)⁻¹) ε⁻¹) :
    cellAbsoluteDeviation H g a r ≤
      ∫ e in cell g r, |1 - c * armProb a e| ∂H := by
  unfold cellAbsoluteDeviation
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨d, hd, rfl⟩
    exact integral_nonneg (fun e => abs_nonneg _)
  · exact ⟨c, hc, rfl⟩

-- @node: cellAbsoluteDeviation_zero_of_ae
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r,c,hc,hae), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_zero_of_ae {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (c : ℝ) (hc : c ∈ Set.Icc ((1 - ε)⁻¹) ε⁻¹)
    (hae : ∀ᵐ e ∂(H.restrict (cell g r)), 1 - c * armProb a e = 0) :
    cellAbsoluteDeviation H g a r = 0 := by
  apply le_antisymm
  · calc
      cellAbsoluteDeviation H g a r ≤
          ∫ e in cell g r, |1 - c * armProb a e| ∂H :=
            cellAbsoluteDeviation_le_integral H g a r c hc
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hae] with e he
        simp [he]
  · exact cellAbsoluteDeviation_nonneg H g hOverlap a r

-- @node: armProb_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,a,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma armProb_bounds {ε : ℝ} (a : ArmSpace) (x : ScoreSpace ε) :
    ε ≤ armProb a x ∧ armProb a x ≤ 1 - ε := by
  rcases x.property with ⟨hxlo, hxhi⟩
  cases a <;> simp [armProb] <;> constructor <;> linarith

-- @node: cellAbsoluteDeviation_zero_of_cellwiseAE
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r,x,hae), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_zero_of_cellwiseAE {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J)
    (x : ScoreSpace ε)
    (hae : ∀ᵐ e ∂(H.restrict (cell g r)), e = x) :
    cellAbsoluteDeviation H g a r = 0 := by
  have hb := armProb_bounds a x
  have hp : 0 < armProb a x := lt_of_lt_of_le hOverlap.1 hb.1
  let c : ℝ := (armProb a x)⁻¹
  have hc : c ∈ Set.Icc ((1 - ε)⁻¹) ε⁻¹ := by
    constructor
    · simpa only [one_div, c] using
        (one_div_le_one_div_of_le hp hb.2)
    · simpa only [one_div, c] using
        (one_div_le_one_div_of_le hOverlap.1 hb.1)
  apply cellAbsoluteDeviation_zero_of_ae H g hOverlap a r c hc
  filter_upwards [hae] with e he
  simp [he, c, inv_mul_cancel₀ hp.ne']

-- @node: cellDeviationIntegral_continuousOn
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellDeviationIntegral_continuousOn {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε)
    (r : LabelSpace J) :
    ContinuousOn (fun c : ℝ =>
      ∫ e in cell g r, |1 - c * armProb true e| ∂H)
      (Set.Icc ((1 - ε)⁻¹) ε⁻¹) := by
  let μ := H.restrict (cell g r)
  let F : ℝ → ScoreSpace ε → ℝ := fun c e => |1 - c * armProb true e|
  have hcont : ContinuousOn (fun c => ∫ e, F c e ∂μ)
      (Set.Icc ((1 - ε)⁻¹) ε⁻¹) := by
    apply continuousOn_of_dominated (bound := fun _ => 1 + ε⁻¹)
    · intro c hc
      dsimp [F]
      simp only [armProb, ↓reduceIte]
      fun_prop
    · intro c hc
      filter_upwards [] with e
      have hp := armProb_bounds true e
      have hp0 : 0 ≤ armProb true e := le_trans (le_of_lt hOverlap.1) hp.1
      have hp1 : armProb true e ≤ 1 := by linarith [hOverlap.1]
      have hc0 : 0 ≤ c :=
        le_trans (le_of_lt (inv_pos.mpr (by linarith [hOverlap.2] : 0 < 1 - ε)))
          (Set.mem_Icc.mp hc).1
      have hc1 : c ≤ ε⁻¹ := (Set.mem_Icc.mp hc).2
      dsimp [F]
      simp only [abs_abs]
      have hprod0 : 0 ≤ c * armProb true e := mul_nonneg hc0 hp0
      have hprod1 : c * armProb true e ≤ ε⁻¹ := by
        calc
          c * armProb true e ≤ c * 1 :=
            mul_le_mul_of_nonneg_left hp1 hc0
          _ = c := by ring
          _ ≤ ε⁻¹ := hc1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact integrable_const _
    · filter_upwards [] with e
      dsimp [F]
      fun_prop
  simpa only [μ, F] using hcont

-- @node: cellAbsoluteDeviation_minimizer
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_minimizer {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε)
    (r : LabelSpace J) :
    ∃ c ∈ Set.Icc ((1 - ε)⁻¹) ε⁻¹,
      cellAbsoluteDeviation H g true r =
        ∫ e in cell g r, |1 - c * armProb true e| ∂H := by
  have hεle : ε ≤ 1 - ε := by linarith [hOverlap.2]
  have hIcc : (1 - ε)⁻¹ ≤ ε⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hOverlap.1 hεle
  let s := Set.Icc ((1 - ε)⁻¹) ε⁻¹
  let f : ℝ → ℝ := fun c => ∫ e in cell g r, |1 - c * armProb true e| ∂H
  have hs : s.Nonempty := ⟨(1 - ε)⁻¹, ⟨le_refl _, hIcc⟩⟩
  obtain ⟨c, hc, heq⟩ :=
    (isCompact_Icc.exists_sInf_image_eq hs
      (cellDeviationIntegral_continuousOn H g hOverlap r))
  refine ⟨c, hc, ?_⟩
  have hset : {v : ℝ | ∃ c ∈ s, v = f c} = f '' s := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
  change sInf {v : ℝ | ∃ c ∈ s, v = f c} = f c
  rw [hset]
  exact heq

-- @node: scoreRecovery_iff_cellwiseAE
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreRecovery_iff_cellwiseAE {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (hg : Measurable g) :
    (∃ h : LabelSpace J → ScoreSpace ε,
      Measurable h ∧ ∀ᵐ e ∂H, e = h (g e)) ↔
    (∀ r : LabelSpace J, 0 < H (cell g r) →
      ∃ x : ScoreSpace ε, ∀ᵐ e ∂(H.restrict (cell g r)), e = x) := by
  classical
  constructor
  · rintro ⟨h, _, hae⟩ r _
    refine ⟨h r, ?_⟩
    filter_upwards [ae_restrict_of_ae hae,
      self_mem_ae_restrict (measurableSet_eq_fun hg measurable_const)] with e he hr
    exact he.trans (congrArg h hr)
  · intro hs
    have hx₀ : ε ≤ 1 - ε := by
      rcases hOverlap with ⟨_, hε⟩
      linarith
    let x₀ : ScoreSpace ε := ⟨ε, ⟨le_refl _, hx₀⟩⟩
    let h : LabelSpace J → ScoreSpace ε := fun r =>
      if hr : 0 < H (cell g r) then Classical.choose (hs r hr) else x₀
    refine ⟨h, measurable_of_finite _, ?_⟩
    have hae : ∀ r : LabelSpace J,
        ∀ᵐ e ∂H, e ∈ cell g r → e = h r := by
      intro r
      by_cases hr : 0 < H (cell g r)
      · have hspec := Classical.choose_spec (hs r hr)
        have hspec' := (ae_restrict_iff' (μ := H)
          (s := cell g r) (measurableSet_eq_fun hg measurable_const)).mp hspec
        simpa [h, hr] using hspec'
      · have hz : H (cell g r) = 0 := le_antisymm (le_of_not_gt hr) bot_le
        have hzero : H.restrict (cell g r) = 0 := Measure.restrict_eq_zero.mpr hz
        have htriv : ∀ᵐ e ∂(H.restrict (cell g r)), e = h r := by
          rw [hzero]
          simp
        exact (ae_restrict_iff' (measurableSet_eq_fun hg measurable_const)).mp htriv
    filter_upwards [Filter.eventually_all.mpr hae] with e he
    exact he (g e) (by simp [cell])

-- @node: thm:universal-point-identification
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
theorem worstCaseAmbiguity_eq_zero_iff {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    (worstCaseAmbiguity H g = 0 ↔
      ∃ h : LabelSpace J → ScoreSpace ε,
        Measurable h ∧ ∀ᵐ e ∂H, e = h (g e)) ∧
    (worstCaseAmbiguity H g = 0 ↔
      ∀ r : LabelSpace J, 0 < H (cell g r) →
        ∃ x : ScoreSpace ε,
          ∀ᵐ e ∂(H.restrict (cell g r)), e = x) := by
  have hcell : worstCaseAmbiguity H g = 0 ↔
      ∀ r : LabelSpace J, 0 < H (cell g r) →
        ∃ x : ScoreSpace ε,
          ∀ᵐ e ∂(H.restrict (cell g r)), e = x := by
    constructor
    · intro hzero
      have hsum := (worstCaseAmbiguity_eq H g hOverlap hg).1
      rw [hsum] at hzero
      have hterm : ∀ r : LabelSpace J,
          cellAbsoluteDeviation H g true r +
            cellAbsoluteDeviation H g false r = 0 := by
        intro r
        have hnonneg (s : LabelSpace J) :
            0 ≤ cellAbsoluteDeviation H g true s +
              cellAbsoluteDeviation H g false s :=
          add_nonneg
            (cellAbsoluteDeviation_nonneg H g hOverlap true s)
            (cellAbsoluteDeviation_nonneg H g hOverlap false s)
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun s : LabelSpace J =>
            cellAbsoluteDeviation H g true s +
              cellAbsoluteDeviation H g false s)
          (by intro s hs; exact hnonneg s)).mp hzero r (Finset.mem_univ r)
      intro r hr
      have hdev : cellAbsoluteDeviation H g true r = 0 := by
        have hnonneg := cellAbsoluteDeviation_nonneg H g hOverlap false r
        have hnonneg' := cellAbsoluteDeviation_nonneg H g hOverlap true r
        linarith [hterm r]
      obtain ⟨c, hc, hmin⟩ :=
        cellAbsoluteDeviation_minimizer H g hOverlap r
      have hint : IntegrableOn
          (fun e : ScoreSpace ε => |1 - c * armProb true e|)
          (cell g r) H := by
        apply Integrable.of_bound (C := 1 + |c|)
          (by simp only [armProb, ↓reduceIte]; fun_prop)
        filter_upwards [] with e
        have hp := armProb_bounds true e
        have hp0 : 0 ≤ armProb true e := le_trans (le_of_lt hOverlap.1) hp.1
        have hp1 : armProb true e ≤ 1 := by linarith [hOverlap.1]
        change ‖|1 - c * armProb true e|‖ ≤ 1 + |c|
        rw [Real.norm_eq_abs, abs_abs]
        calc
          |1 - c * armProb true e| ≤ |(1 : ℝ)| + |c * armProb true e| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (1 : ℝ) 0 (c * armProb true e))
          _ = 1 + |c| * armProb true e := by
            rw [abs_mul, abs_of_nonneg hp0]
            norm_num
          _ ≤ 1 + |c| := by nlinarith [abs_nonneg c]
      have hae : ∀ᵐ e ∂(H.restrict (cell g r)),
          |1 - c * armProb true e| = 0 :=
        (setIntegral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall (fun e => abs_nonneg _)) hint).mp
          (hmin ▸ hdev)
      obtain ⟨x, _, hx⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hr.ne' hae
      refine ⟨x, ?_⟩
      have hcpos : 0 < c :=
        lt_of_lt_of_le (inv_pos.mpr (by linarith [hOverlap.2] : 0 < 1 - ε))
          hc.1
      filter_upwards [hae] with e he
      apply Subtype.ext
      have hxe : 1 - c * (x : ℝ) = 0 := by
        simpa [armProb] using (abs_eq_zero.mp hx)
      have hee : 1 - c * (e : ℝ) = 0 := by
        simpa [armProb] using (abs_eq_zero.mp he)
      have hmul : c * (e : ℝ) = c * (x : ℝ) := by linarith
      exact mul_left_cancel₀ hcpos.ne' hmul
    · intro hs
      obtain ⟨h, _, hae⟩ :=
        (scoreRecovery_iff_cellwiseAE H g hOverlap hg).2 hs
      rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
      apply Finset.sum_eq_zero
      intro r hr
      have hrAE : ∀ᵐ e ∂(H.restrict (cell g r)), e = h r := by
        filter_upwards [ae_restrict_of_ae hae,
          self_mem_ae_restrict (measurableSet_eq_fun hg measurable_const)]
          with e he hmem
        exact he.trans (congrArg h hmem)
      rw [cellAbsoluteDeviation_zero_of_cellwiseAE H g hOverlap true r (h r) hrAE,
        cellAbsoluteDeviation_zero_of_cellwiseAE H g hOverlap false r (h r) hrAE]
      ring
  exact ⟨hcell.trans (scoreRecovery_iff_cellwiseAE H g hOverlap hg).symm, hcell⟩

end CausalSmith.PartialID.UnlinkedPropensityAte
