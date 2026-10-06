module

public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TAllLabelAmbiguity
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelFiniteLower

/-!
Transfer of finite-cell Lebesgue quantization lower bounds to score-law ambiguity.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε), this result [establishes the stated mathematical conclusion](goal). -/
lemma rateLower_scoreBaseMeasure_isFinite (ε : ℝ) :
    IsFiniteMeasure
      ((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)) := by
  refine ⟨?_⟩
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  rw [image_univ, Subtype.range_coe_subtype]
  simp only [Set.ofPred_mem_eq]
  rw [Real.volume_Icc]
  finiteness

/-- For [the specified mathematical inputs](hyp:ε,K,g,r), [this definition](goal) introduces the corresponding object. -/
def realScoreCell {ε : ℝ} {K : ℕ}
    (g : ScoreSpace ε → LabelSpace K) (r : LabelSpace K) : Set ℝ :=
  Subtype.val '' cell g r

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,g,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma realScoreCell_intervalPartition {ε : ℝ} {K : ℕ}
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g) :
    IsIntervalPartition ε (1 - ε) K (realScoreCell g) := by
  have hcoe : MeasurableEmbedding (Subtype.val : ScoreSpace ε → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  refine ⟨?_, ?_, ?_⟩
  · intro r
    apply hcoe.measurableSet_image'
    exact measurableSet_eq_fun hg measurable_const
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with ⟨ei, hei, rfl⟩
    rcases hxj with ⟨ej, hej, heq⟩
    have heij : ei = ej := Subtype.ext heq.symm
    subst ej
    exact hij (hei.symm.trans hej)
  · ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨r, e, he, rfl⟩
      exact e.property
    · intro hx
      let e : ScoreSpace ε := ⟨x, hx⟩
      exact mem_iUnion_of_mem (g e) ⟨e, rfl, rfl⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,g,hg,r,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreBase_setIntegral_abs_eq_realScoreCell {ε : ℝ} {K : ℕ}
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (z : ℝ) :
    (∫ e in cell g r, |(e : ℝ) - z|
      ∂((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ))) =
      ∫ x in realScoreCell g r, |x - z| := by
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  have hcell : MeasurableSet (cell g r) := measurableSet_eq_fun hg measurable_const
  have himageMeas : MeasurableSet (realScoreCell g r) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hcell
  have hmap := MeasureTheory.setIntegral_map
    (μ := μ) (g := (Subtype.val : ScoreSpace ε → ℝ))
    (f := fun x : ℝ => |x - z|) (s := realScoreCell g r) himageMeas
    (by fun_prop) measurable_subtype_coe.aemeasurable
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
  rw [hpreimage]
  rw [← hmap]
  change (∫ x, |x - z|
    ∂(volume.restrict (Icc ε (1 - ε))).restrict (realScoreCell g r)) = _
  rw [hrestrict]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,f,mf,hmf,hf,s,hs,φ,hφ,hφH,hφnonneg), this result [establishes the stated mathematical conclusion](goal). -/
lemma setIntegral_lowerScoreDensity_lower {ε : ℝ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (mf : ℝ) (hmf : 0 < mf)
    (hf : LowerScoreDensity H f mf)
    (s : Set (ScoreSpace ε)) (hs : MeasurableSet s)
    (φ : ScoreSpace ε → ℝ)
    (hφ : IntegrableOn φ s
      ((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)))
    (hφH : IntegrableOn φ s H)
    (hφnonneg : ∀ e ∈ s, 0 ≤ φ e) :
    mf * (∫ e in s, φ e
      ∂((volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ))) ≤
      ∫ e in s, φ e ∂H := by
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  let _ : IsFiniteMeasure μ := rateLower_scoreBaseMeasure_isFinite ε
  have hfMeas : Measurable f := hf.densityLower.1
  have hfLower : ∀ᵐ e ∂μ, mf ≤ f e := hf.densityLower.2.2
  have hfNonneg : ∀ᵐ e ∂μ, 0 ≤ f e :=
    hfLower.mono fun _ he => hmf.le.trans he
  have hindicatorInt : Integrable (s.indicator φ) μ :=
    hφ.integrable_indicator hs
  have hleft : Integrable (fun e => mf * s.indicator φ e) μ :=
    hindicatorInt.const_mul mf
  have hright : Integrable (fun e => f e * s.indicator φ e) μ := by
    have hwith : Integrable (s.indicator φ)
        (μ.withDensity fun e => ENNReal.ofReal (f e)) := by
      rw [← hf.densityLower.2.1]
      exact hφH.integrable_indicator hs
    have hweighted :=
      (integrable_withDensity_iff_integrable_smul'
        hfMeas.ennreal_ofReal (Eventually.of_forall fun _ => by finiteness)).mp hwith
    apply hweighted.congr
    filter_upwards [hfNonneg] with e he
    simp only [smul_eq_mul, ENNReal.toReal_ofReal he]
  rw [← integral_indicator hs, ← integral_indicator hs]
  rw [hf.densityLower.2.1,
    integral_withDensity_eq_integral_toReal_smul
      hfMeas.ennreal_ofReal (Eventually.of_forall fun _ => by finiteness)]
  simp only [smul_eq_mul]
  calc
    mf * ∫ e, s.indicator φ e ∂μ =
        ∫ e, mf * s.indicator φ e ∂μ := by rw [integral_const_mul]
    _ ≤ ∫ e, f e * s.indicator φ e ∂μ := by
      apply integral_mono_ae hleft hright
      filter_upwards [hfLower] with e he
      by_cases hes : e ∈ s
      · simp only [Set.indicator_of_mem hes]
        exact mul_le_mul_of_nonneg_right he (hφnonneg e hes)
      · simp [hes]
    _ = ∫ e, (ENNReal.ofReal (f e)).toReal * s.indicator φ e ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfNonneg] with e he
      rw [ENNReal.toReal_ofReal he]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,f,mf,_hOverlap,hmf,hf,g,hg,r,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCell_absDeviation_lower {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (mf : ℝ) (_hOverlap : Overlap ε) (hmf : 0 < mf)
    (hf : LowerScoreDensity H f mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (r : LabelSpace K) (z : ℝ) :
    mf * (volume.real (realScoreCell g r) ^ 2 / 4) ≤
      ∫ e in cell g r, |(e : ℝ) - z| ∂H := by
  letI : IsProbabilityMeasure H := hf.probability
  let μ : Measure (ScoreSpace ε) :=
    (volume : Measure ℝ).comap (Subtype.val : ScoreSpace ε → ℝ)
  let _ : IsFiniteMeasure μ := rateLower_scoreBaseMeasure_isFinite ε
  have hcell : MeasurableSet (cell g r) := measurableSet_eq_fun hg measurable_const
  have hInt : IntegrableOn (fun e : ScoreSpace ε => |(e : ℝ) - z|) (cell g r) μ := by
    apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + |z| + 1)
    filter_upwards [] with e
    have he := e.property
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |(e : ℝ) - z| ≤ |(e : ℝ)| + |z| := abs_sub _ _
      _ ≤ |ε| + |1 - ε| + |z| + 1 := by
        have heabs : |(e : ℝ)| ≤ |ε| + |1 - ε| := by
          apply abs_le.mpr
          constructor
          · calc
              -(|ε| + |1 - ε|) ≤ -|ε| := by linarith [abs_nonneg (1 - ε)]
              _ ≤ ε := neg_abs_le ε
              _ ≤ (e : ℝ) := he.1
          · calc
              (e : ℝ) ≤ 1 - ε := he.2
              _ ≤ |1 - ε| := le_abs_self (1 - ε)
              _ ≤ |ε| + |1 - ε| := by linarith [abs_nonneg ε]
        linarith
  have hdensity := setIntegral_lowerScoreDensity_lower H f mf hmf hf
    (cell g r) hcell (fun e => |(e : ℝ) - z|) hInt
    (by
      apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + |z| + 1)
      filter_upwards [] with e
      have he := e.property
      rw [Real.norm_eq_abs, abs_abs]
      have heabs : |(e : ℝ)| ≤ |ε| + |1 - ε| := by
        apply abs_le.mpr
        constructor
        · calc
            -(|ε| + |1 - ε|) ≤ -|ε| := by linarith [abs_nonneg (1 - ε)]
            _ ≤ ε := neg_abs_le ε
            _ ≤ (e : ℝ) := he.1
        · calc
            (e : ℝ) ≤ 1 - ε := he.2
            _ ≤ |1 - ε| := le_abs_self (1 - ε)
            _ ≤ |ε| + |1 - ε| := by linarith [abs_nonneg ε]
      linarith [abs_sub (e : ℝ) z])
    (fun _ _ => abs_nonneg _)
  rw [scoreBase_setIntegral_abs_eq_realScoreCell g hg r z] at hdensity
  have hgeom := boundedCell_absDeviation_integral_lower (z := z)
    ((realScoreCell_intervalPartition g hg).1 r)
    (fun x hx => by
      rcases hx with ⟨e, he, rfl⟩
      exact e.property)
  calc
    mf * (volume.real (realScoreCell g r) ^ 2 / 4) ≤
        mf * ∫ x in realScoreCell g r, |x - z| :=
      mul_le_mul_of_nonneg_left hgeom hmf.le
    _ ≤ ∫ e in cell g r, |(e : ℝ) - z| ∂H := hdensity

/-- For [the specified mathematical inputs](hyp:a,c), [this definition](goal) introduces the corresponding object. -/
def reciprocalCenterScore (a : ArmSpace) (c : ℝ) : ℝ :=
  if a then c⁻¹ else 1 - c⁻¹

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,c,hOverlap,hc,a,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma reciprocalDeviation_eq_scoreDistance {ε c : ℝ}
    (hOverlap : Overlap ε) (hc : c ∈ Icc ((1 - ε)⁻¹) ε⁻¹)
    (a : ArmSpace) (e : ScoreSpace ε) :
    |1 - c * armProb a e| = c * |(e : ℝ) - reciprocalCenterScore a c| := by
  have hcpos : 0 < c :=
    (inv_pos.mpr (by linarith [hOverlap.2])).trans_le hc.1
  have hcne : c ≠ 0 := hcpos.ne'
  cases a
  · simp only [armProb, Bool.false_eq_true, ↓reduceIte, reciprocalCenterScore]
    calc
      |1 - c * (1 - (e : ℝ))| = |c * ((e : ℝ) - (1 - c⁻¹))| := by
        congr 1
        field_simp
        ring
      _ = |c| * |(e : ℝ) - (1 - c⁻¹)| := abs_mul _ _
      _ = c * |(e : ℝ) - (1 - c⁻¹)| := by rw [abs_of_pos hcpos]
  · simp only [armProb, ↓reduceIte, reciprocalCenterScore]
    calc
      |1 - c * (e : ℝ)| = |c * ((e : ℝ) - c⁻¹)| := by
        rw [abs_eq_abs]
        right
        field_simp
        ring
      _ = |c| * |(e : ℝ) - c⁻¹| := abs_mul _ _
      _ = c * |(e : ℝ) - c⁻¹| := by rw [abs_of_pos hcpos]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,f,mf,hOverlap,hmf,hf,g,hg,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma cellAbsoluteDeviation_lower_cellLengthSq {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (mf : ℝ) (hOverlap : Overlap ε) (hmf : 0 < mf)
    (hf : LowerScoreDensity H f mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace K) :
    mf * volume.real (realScoreCell g r) ^ 2 / (4 * (1 - ε)) ≤
      cellAbsoluteDeviation H g a r := by
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
  unfold cellAbsoluteDeviation
  apply le_csInf
  · let c : ℝ := ε⁻¹
    refine ⟨∫ e in cell g r, |1 - c * armProb a e| ∂H, c, ?_, rfl⟩
    dsimp [c]
    constructor
    · exact (inv_le_inv₀ hε1 hOverlap.1).mpr (by linarith [hOverlap.2])
    · rfl
  · rintro v ⟨c, hc, rfl⟩
    have hcpos : 0 < c := (inv_pos.mpr hε1).trans_le hc.1
    let z : ℝ := reciprocalCenterScore a c
    have hscore := scoreCell_absDeviation_lower H f mf hOverlap hmf hf
      g hg r z
    have hrewrite :
        (∫ e in cell g r, |1 - c * armProb a e| ∂H) =
          c * ∫ e in cell g r, |(e : ℝ) - z| ∂H := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun (measurableSet_eq_fun hg measurable_const)
      intro e he
      exact reciprocalDeviation_eq_scoreDistance hOverlap hc a e
    rw [hrewrite]
    have hcoeff : (1 - ε)⁻¹ ≤ c := hc.1
    have hdistNonneg : 0 ≤ ∫ e in cell g r, |(e : ℝ) - z| ∂H :=
      integral_nonneg fun _ => abs_nonneg _
    calc
      mf * volume.real (realScoreCell g r) ^ 2 / (4 * (1 - ε)) =
          (1 - ε)⁻¹ * (mf * (volume.real (realScoreCell g r) ^ 2 / 4)) := by
        field_simp
      _ ≤ (1 - ε)⁻¹ * (∫ e in cell g r, |(e : ℝ) - z| ∂H) :=
        mul_le_mul_of_nonneg_left hscore (inv_nonneg.mpr hε1.le)
      _ ≤ c * (∫ e in cell g r, |(e : ℝ) - z| ∂H) :=
        mul_le_mul_of_nonneg_right hcoeff hdistNonneg

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,hOverlap,hmf,K,hK,H,f,hf,g,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma worstCaseAmbiguity_finiteLabel_lower {ε : ℝ}
    (mf : ℝ) (hOverlap : Overlap ε) (hmf : 0 < mf)
    (K : ℕ) (hK : 0 < K)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ) (hf : LowerScoreDensity H f mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g) :
    mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K) ≤
      worstCaseAmbiguity H g := by
  let m : Fin K → ℝ := fun r => volume.real (realScoreCell g r)
  have hpart := realScoreCell_intervalPartition g hg
  have hsum : (∑ r, m r) = 1 - 2 * ε := by
    dsimp [m]
    calc
      (∑ r, volume.real (realScoreCell g r)) =
          volume.real (⋃ r, realScoreCell g r) :=
        (measureReal_iUnion_fintype
          (fun i j hij => hpart.2.1 i j hij) hpart.1
          (fun r => measure_ne_top_of_subset
            (fun x hx => by
              rcases hx with ⟨e, he, rfl⟩
              exact e.property)
            measure_Icc_lt_top.ne)).symm
      _ = volume.real (Icc ε (1 - ε)) := by rw [hpart.2.2]
      _ = 1 - 2 * ε := by
        rw [Real.volume_real_Icc_of_le (by linarith [hOverlap.2])]
        ring
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
  have hqpos : 0 < mf / (1 - ε) := div_pos hmf hε1
  have hsq := sum_cellMass_sq_lower K hK m
  have hcells :
      mf / (1 - ε) * (∑ r, (m r) ^ 2 / 2) ≤
        ∑ r, (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have ht := cellAbsoluteDeviation_lower_cellLengthSq H f mf hOverlap
      hmf hf g hg true r
    have hc := cellAbsoluteDeviation_lower_cellLengthSq H f mf hOverlap
      hmf hf g hg false r
    dsimp [m]
    calc
      mf / (1 - ε) * (volume.real (realScoreCell g r) ^ 2 / 2) =
          mf * volume.real (realScoreCell g r) ^ 2 / (4 * (1 - ε)) +
          mf * volume.real (realScoreCell g r) ^ 2 / (4 * (1 - ε)) := by
        field_simp
        ring
      _ ≤ cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r := add_le_add ht hc
  have hgeom :
      mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K) ≤
        mf / (1 - ε) * (∑ r, (m r) ^ 2 / 2) := by
    rw [← hsum]
    have hhalf : (∑ r, m r) ^ 2 / (2 * K) ≤ ∑ r, (m r) ^ 2 / 2 := by
      calc
        (∑ r, m r) ^ 2 / (2 * K) = ((∑ r, m r) ^ 2 / K) / 2 := by
          field_simp
        _ ≤ (∑ r, (m r) ^ 2) / 2 :=
          div_le_div_of_nonneg_right hsq (by norm_num)
        _ = ∑ r, (m r) ^ 2 / 2 := by rw [Finset.sum_div]
    calc
      mf * (∑ r, m r) ^ 2 / (2 * (1 - ε) * K) =
          mf / (1 - ε) * ((∑ r, m r) ^ 2 / (2 * K)) := by
        field_simp
      _ ≤ mf / (1 - ε) * (∑ r, (m r) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hhalf hqpos.le
  rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
  exact hgeom.trans hcells

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,hOverlap,hmf,K,hK,H,f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma optimalKAmbiguity_finiteLabel_lower {ε : ℝ}
    (mf : ℝ) (hOverlap : Overlap ε) (hmf : 0 < mf)
    (K : ℕ) (hK : 0 < K)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ) (hf : LowerScoreDensity H f mf) :
    mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K) ≤
      optimalKAmbiguity ε K H := by
  unfold optimalKAmbiguity
  apply le_csInf
  · let r0 : LabelSpace K := ⟨0, hK⟩
    let g0 : ScoreSpace ε → LabelSpace K := fun _ => r0
    refine ⟨worstCaseAmbiguity H g0, g0, ?_, rfl⟩
    exact measurable_const
  · rintro d ⟨g, hg, rfl⟩
    exact worstCaseAmbiguity_finiteLabel_lower mf hOverlap hmf K hK H f hf g hg

end

end CausalSmith.PartialID.UnlinkedPropensityAte
