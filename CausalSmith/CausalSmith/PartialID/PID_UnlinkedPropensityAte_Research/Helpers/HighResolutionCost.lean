module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.AllLabelDefinitions
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.CompandingReleaseGeometry
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelRateLower
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Quantization

/-! Paper-specific paired quantization coefficients and cell costs. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,f,s,x,z), [this definition](goal) introduces the corresponding object. -/
def highResolutionBeta {ε : ℝ} (f : ScoreSpace ε → ℝ)
    (s : Fin 2) (x z : ℝ) : ℝ :=
  if s = 0 then densityExtension f x / (1 - z)
  else densityExtension f x / z

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,x,hx), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionBeta_diagonal {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (x : ℝ) (hx : x ∈ Icc ε (1 - ε)) :
    pairedDiagonalWeight 2 (highResolutionBeta f) x =
      densityExtension f x / (x * (1 - x)) := by
  have hx0 : x ≠ 0 := ne_of_gt (hOverlap.1.trans_le hx.1)
  have hx1 : 1 - x ≠ 0 := ne_of_gt (by linarith [hx.2, hOverlap.1])
  unfold pairedDiagonalWeight highResolutionBeta
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
  field_simp
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfcont,s), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionBeta_continuousOn {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (s : Fin 2) :
    ContinuousOn (fun p : ℝ × ℝ => highResolutionBeta f s p.1 p.2)
      (Icc ε (1 - ε) ×ˢ Icc ε (1 - ε)) := by
  have hnum : ContinuousOn
      (fun p : ℝ × ℝ => densityExtension f p.1)
      (Icc ε (1 - ε) ×ˢ Icc ε (1 - ε)) :=
    (continuousOn_densityExtension hfcont).comp continuousOn_fst
      (fun _ hp => hp.1)
  by_cases hs : s = 0
  · simp only [highResolutionBeta, hs, if_pos]
    apply hnum.div (by fun_prop)
    intro p hp
    linarith [hp.2.2, hOverlap.1]
  · simp only [highResolutionBeta, hs]
    apply hnum.div (by fun_prop)
    intro p hp
    exact ne_of_gt (hOverlap.1.trans_le hp.2.1)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfpos,s,x,z,hx,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionBeta_pos {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfpos : ∀ e, 0 < f e) (s : Fin 2) (x z : ℝ)
    (hx : x ∈ Icc ε (1 - ε)) (hz : z ∈ Icc ε (1 - ε)) :
    0 < highResolutionBeta f s x z := by
  have hfx : 0 < densityExtension f x := by
    rw [densityExtension, dif_pos hx]
    exact hfpos ⟨x, hx⟩
  by_cases hs : s = 0
  · rw [highResolutionBeta, if_pos hs]
    exact div_pos hfx (by linarith [hz.2, hOverlap.1])
  · rw [highResolutionBeta, if_neg hs]
    exact div_pos hfx (hOverlap.1.trans_le hz.1)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_densityExtension {ε : ℝ} (f : ScoreSpace ε → ℝ)
    (hf : Measurable f) : Measurable (densityExtension f) := by
  have hemb : MeasurableEmbedding (Subtype.val : ScoreSpace ε → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hext : Measurable
      (Function.extend (Subtype.val : ScoreSpace ε → ℝ) f (fun _ => 0)) :=
    hemb.measurable_extend hf measurable_const
  convert hext using 1
  funext x
  by_cases hx : x ∈ Icc ε (1 - ε)
  · rw [densityExtension, dif_pos hx]
    exact (hemb.injective.extend_apply f (fun _ => 0) ⟨x, hx⟩).symm
  · rw [densityExtension, dif_neg hx]
    rw [Function.extend_apply' _ _ _ (by
      intro hmem
      rcases hmem with ⟨e, he⟩
      apply hx
      rw [← he]
      exact e.property)]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,g,hg,r,φ,hφ), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreBase_setIntegral_eq_realScoreCell {ε : ℝ} {K : ℕ}
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ e in cell g r, φ (e : ℝ)
      ∂((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ))) =
      ∫ x in realScoreCell g r, φ x := by
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  have hcell : MeasurableSet (cell g r) := measurableSet_eq_fun hg measurable_const
  have himageMeas : MeasurableSet (realScoreCell g r) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hcell
  have hmap := MeasureTheory.setIntegral_map
    (μ := μ) (g := (Subtype.val : ScoreSpace ε → ℝ))
    (f := φ) (s := realScoreCell g r) himageMeas hφ.aestronglyMeasurable
    measurable_subtype_coe.aemeasurable
  have hmapMeasure : Measure.map (Subtype.val : ScoreSpace ε → ℝ) μ =
      volume.restrict (Icc ε (1 - ε)) :=
    map_comap_subtype_coe measurableSet_Icc volume
  rw [hmapMeasure] at hmap
  have himageSub : realScoreCell g r ⊆ Icc ε (1 - ε) := by
    rintro x ⟨e, he, rfl⟩
    exact e.property
  have hrestrict :
      (volume.restrict (Icc ε (1 - ε))).restrict (realScoreCell g r) =
        volume.restrict (realScoreCell g r) :=
    Measure.restrict_restrict_of_subset himageSub
  have hpreimage : cell g r =
      (Subtype.val : ScoreSpace ε → ℝ) ⁻¹' (realScoreCell g r) := by
    ext e
    constructor
    · intro he
      exact ⟨e, he, rfl⟩
    · rintro ⟨e', he', heq⟩
      simpa [Subtype.ext heq] using he'
  rw [hpreimage, ← hmap]
  change (∫ x, φ x
    ∂(volume.restrict (Icc ε (1 - ε))).restrict (realScoreCell g r)) = _
  rw [hrestrict]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,r,z,hz,hOverlap,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma treatedCandidate_eq_highResolutionCellCost {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (z : ℝ) (hz : z ∈ Icc ε (1 - ε))
    (hOverlap : Overlap ε) (hfpos : ∀ e, 0 < f e) :
    (∫ e in cell g r, |1 - z⁻¹ * armProb true e| ∂H) =
      ∫ x in realScoreCell g r,
        highResolutionBeta f 1 x z * |x - z| := by
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  let _ : IsFiniteMeasure μ := rateLower_scoreBaseMeasure_isFinite ε
  let φ : ℝ → ℝ := fun x => highResolutionBeta f 1 x z * |x - z|
  have hfmeas : Measurable f := hDensity.densityLower.1
  have hφmeas : Measurable φ := by
    dsimp [φ, highResolutionBeta]
    exact ((measurable_densityExtension f hfmeas).div_const z).mul
      (by fun_prop)
  have hcell : MeasurableSet (cell g r) := measurableSet_eq_fun hg measurable_const
  have hzpos : 0 < z := hOverlap.1.trans_le hz.1
  have hpoint (e : ScoreSpace ε) :
      f e * |1 - z⁻¹ * armProb true e| = φ (e : ℝ) := by
    have hext : densityExtension f (e : ℝ) = f e := by
      rw [densityExtension, dif_pos e.property]
    have hid : |1 - z⁻¹ * (e : ℝ)| = z⁻¹ * |(e : ℝ) - z| := by
      rw [show 1 - z⁻¹ * (e : ℝ) = -z⁻¹ * ((e : ℝ) - z) by
        field_simp
        ring]
      rw [abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hzpos)]
    simp only [armProb, ↓reduceIte, φ, highResolutionBeta, Fin.isValue,
      one_ne_zero, hext]
    rw [hid]
    ring
  calc
    (∫ e in cell g r, |1 - z⁻¹ * armProb true e| ∂H) =
        ∫ e, (cell g r).indicator
          (fun e => |1 - z⁻¹ * armProb true e|) e ∂H := by
      rw [integral_indicator hcell]
    _ = ∫ e, (ENNReal.ofReal (f e)).toReal *
          (cell g r).indicator
            (fun e => |1 - z⁻¹ * armProb true e|) e ∂μ := by
      rw [hDensity.densityLower.2.1,
        integral_withDensity_eq_integral_toReal_smul
          hfmeas.ennreal_ofReal
          (by simp)]
      simp only [smul_eq_mul]
      rfl
    _ = ∫ e, (cell g r).indicator (fun e => φ (e : ℝ)) e ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with e
      by_cases he : e ∈ cell g r
      · simp only [Set.indicator_of_mem he]
        rw [ENNReal.toReal_ofReal (hfpos e).le, hpoint]
      · simp [Set.indicator_of_notMem he]
    _ = ∫ e in cell g r, φ (e : ℝ) ∂μ := by
      rw [integral_indicator hcell]
    _ = ∫ x in realScoreCell g r, φ x :=
      scoreBase_setIntegral_eq_realScoreCell g hg r φ hφmeas
    _ = ∫ x in realScoreCell g r,
        highResolutionBeta f 1 x z * |x - z| := rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,r,hOverlap,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma treatedCellAbsoluteDeviation_eq_highResolutionInf
    {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (hOverlap : Overlap ε)
    (hfpos : ∀ e, 0 < f e) :
    cellAbsoluteDeviation H g true r =
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 1 x z * |x - z|} := by
  have hε : 0 < ε := hOverlap.1
  have h1ε : 0 < 1 - ε := by linarith [hOverlap.2]
  unfold cellAbsoluteDeviation
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, hvc⟩
    have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.mpr h1ε) hc.1
    let z : ℝ := c⁻¹
    have hz : z ∈ Icc ε (1 - ε) := by
      constructor
      · have h := (inv_le_inv₀ (inv_pos.mpr hε) hcpos).2 hc.2
        simpa [z] using h
      · have h := (inv_le_inv₀ hcpos (inv_pos.mpr h1ε)).2 hc.1
        simpa [z] using h
    refine ⟨z, hz, ?_⟩
    have hzinv : z⁻¹ = c := by
      dsimp [z]
      exact inv_inv c
    have hcandidate := treatedCandidate_eq_highResolutionCellCost
      H f hDensity g hg r z hz hOverlap hfpos
    rw [hzinv] at hcandidate
    exact hvc.trans hcandidate
  · rintro ⟨z, hz, hvz⟩
    have hzpos : 0 < z := hε.trans_le hz.1
    let c : ℝ := z⁻¹
    have hc : c ∈ Icc ((1 - ε)⁻¹) ε⁻¹ := by
      constructor
      · exact (inv_le_inv₀ h1ε hzpos).2 hz.2
      · exact (inv_le_inv₀ hzpos hε).2 hz.1
    refine ⟨c, hc, ?_⟩
    have hcandidate := treatedCandidate_eq_highResolutionCellCost
      H f hDensity g hg r z hz hOverlap hfpos
    exact hvz.trans hcandidate.symm

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,r,z,hz,hOverlap,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma controlCandidate_eq_highResolutionCellCost {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (z : ℝ) (hz : z ∈ Icc ε (1 - ε))
    (hOverlap : Overlap ε) (hfpos : ∀ e, 0 < f e) :
    (∫ e in cell g r, |1 - (1 - z)⁻¹ * armProb false e| ∂H) =
      ∫ x in realScoreCell g r,
        highResolutionBeta f 0 x z * |x - z| := by
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  let _ : IsFiniteMeasure μ := rateLower_scoreBaseMeasure_isFinite ε
  let φ : ℝ → ℝ := fun x => highResolutionBeta f 0 x z * |x - z|
  have hfmeas : Measurable f := hDensity.densityLower.1
  have hφmeas : Measurable φ := by
    dsimp [φ, highResolutionBeta]
    exact ((measurable_densityExtension f hfmeas).div_const (1 - z)).mul
      (by fun_prop)
  have hcell : MeasurableSet (cell g r) := measurableSet_eq_fun hg measurable_const
  have h1zpos : 0 < 1 - z := by linarith [hz.2, hOverlap.1]
  have hpoint (e : ScoreSpace ε) :
      f e * |1 - (1 - z)⁻¹ * armProb false e| = φ (e : ℝ) := by
    have hext : densityExtension f (e : ℝ) = f e := by
      rw [densityExtension, dif_pos e.property]
    have hid : |1 - (1 - z)⁻¹ * (1 - (e : ℝ))| =
        (1 - z)⁻¹ * |(e : ℝ) - z| := by
      rw [show 1 - (1 - z)⁻¹ * (1 - (e : ℝ)) =
          (1 - z)⁻¹ * ((e : ℝ) - z) by
        field_simp
        ring]
      rw [abs_mul, abs_of_pos (inv_pos.mpr h1zpos)]
    simp only [armProb, Bool.false_eq_true, ↓reduceIte, φ,
      highResolutionBeta, Fin.isValue, hext]
    rw [hid]
    ring
  calc
    (∫ e in cell g r, |1 - (1 - z)⁻¹ * armProb false e| ∂H) =
        ∫ e, (cell g r).indicator
          (fun e => |1 - (1 - z)⁻¹ * armProb false e|) e ∂H := by
      rw [integral_indicator hcell]
    _ = ∫ e, (ENNReal.ofReal (f e)).toReal *
          (cell g r).indicator
            (fun e => |1 - (1 - z)⁻¹ * armProb false e|) e ∂μ := by
      rw [hDensity.densityLower.2.1,
        integral_withDensity_eq_integral_toReal_smul
          hfmeas.ennreal_ofReal (by simp)]
      simp only [smul_eq_mul]
      rfl
    _ = ∫ e, (cell g r).indicator (fun e => φ (e : ℝ)) e ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with e
      by_cases he : e ∈ cell g r
      · simp only [Set.indicator_of_mem he]
        rw [ENNReal.toReal_ofReal (hfpos e).le, hpoint]
      · simp [Set.indicator_of_notMem he]
    _ = ∫ e in cell g r, φ (e : ℝ) ∂μ := by
      rw [integral_indicator hcell]
    _ = ∫ x in realScoreCell g r, φ x :=
      scoreBase_setIntegral_eq_realScoreCell g hg r φ hφmeas
    _ = ∫ x in realScoreCell g r,
        highResolutionBeta f 0 x z * |x - z| := rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,r,hOverlap,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma controlCellAbsoluteDeviation_eq_highResolutionInf
    {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (hOverlap : Overlap ε)
    (hfpos : ∀ e, 0 < f e) :
    cellAbsoluteDeviation H g false r =
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 0 x z * |x - z|} := by
  have hε : 0 < ε := hOverlap.1
  have h1ε : 0 < 1 - ε := by linarith [hOverlap.2]
  unfold cellAbsoluteDeviation
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, hvc⟩
    have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.mpr h1ε) hc.1
    let z : ℝ := 1 - c⁻¹
    have hcinvLower : ε ≤ c⁻¹ := by
      have h := (inv_le_inv₀ (inv_pos.mpr hε) hcpos).2 hc.2
      simpa using h
    have hcinvUpper : c⁻¹ ≤ 1 - ε := by
      have h := (inv_le_inv₀ hcpos (inv_pos.mpr h1ε)).2 hc.1
      simpa using h
    have hz : z ∈ Icc ε (1 - ε) := by
      dsimp [z]
      constructor <;> linarith
    refine ⟨z, hz, ?_⟩
    have hzc : (1 - z)⁻¹ = c := by
      dsimp [z]
      rw [sub_sub_cancel, inv_inv]
    have hcandidate := controlCandidate_eq_highResolutionCellCost
      H f hDensity g hg r z hz hOverlap hfpos
    rw [hzc] at hcandidate
    exact hvc.trans hcandidate
  · rintro ⟨z, hz, hvz⟩
    have h1zpos : 0 < 1 - z := by linarith [hz.2, hε]
    let c : ℝ := (1 - z)⁻¹
    have hc : c ∈ Icc ((1 - ε)⁻¹) ε⁻¹ := by
      constructor
      · exact (inv_le_inv₀ h1ε h1zpos).2 (by linarith [hz.1])
      · exact (inv_le_inv₀ h1zpos hε).2 (by linarith [hz.2])
    refine ⟨c, hc, ?_⟩
    have hcandidate := controlCandidate_eq_highResolutionCellCost
      H f hDensity g hg r z hz hOverlap hfpos
    exact hvz.trans hcandidate.symm

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,r,hOverlap,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_cellAbsoluteDeviation_eq_highResolutionInfs
    {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (hOverlap : Overlap ε)
    (hfpos : ∀ e, 0 < f e) :
    cellAbsoluteDeviation H g true r + cellAbsoluteDeviation H g false r =
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 1 x z * |x - z|} +
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 0 x z * |x - z|} := by
  rw [treatedCellAbsoluteDeviation_eq_highResolutionInf
      H f hDensity g hg r hOverlap hfpos,
    controlCellAbsoluteDeviation_eq_highResolutionInf
      H f hDensity g hg r hOverlap hfpos]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
