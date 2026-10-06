module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellMoments
public import Mathlib.Probability.Moments.Covariance

/-! # Single-record marked cell covariance bounds -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The source cell mark object](goal) is defined from [the supplied inputs](hyp:i,o). -/

def sourceCellMark (i : Fin 7) (o : SourceObs) : ℝ :=
  if i.val = 1 then boolReal (!o.2.1) else
  if i.val = 2 then boolReal o.2.1 else
  if i.val = 3 then boolReal (!o.2.1) * max 0 (min 1 o.2.2.2) else
  if i.val = 4 then boolReal o.2.1 * max 0 (min 1 o.2.2.2) else
  if i.val = 5 then boolReal (!o.2.1) * boolReal o.2.2.1 else
  if i.val = 6 then boolReal o.2.1 * boolReal o.2.2.1 else 0
/-- [The source cell score object](goal) is defined from [the supplied inputs](hyp:i,K,l,o). -/

noncomputable def sourceCellScore (i : Fin 7) (K : ℕ) (l : Fin K)
    (o : SourceObs) : ℝ := by
  classical
  exact if o.1 ∈ cell K l then sourceCellMark i o else 0
/-- [The target cell score object](goal) is defined from [the supplied inputs](hyp:K,l,x). -/

noncomputable def targetCellScore (K : ℕ) (l : Fin K) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ cell K l then 1 else 0
/-- Given [the supplied inputs](hyp:i,o), [the stated result about source cell mark mem unit interval holds](goal). -/

lemma sourceCellMark_mem_unit_interval (i : Fin 7) (o : SourceObs) :
    sourceCellMark i o ∈ Icc (0 : ℝ) 1 := by
  have hclip (y : ℝ) : max 0 (min 1 y) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  rcases o with ⟨x, z, d, y⟩
  fin_cases i <;> cases z <;> cases d <;>
    simp [sourceCellMark, boolReal, Set.mem_Icc, (hclip y).1, (hclip y).2]
/-- Given [the supplied inputs](hyp:i), [the stated result about measurable source cell mark holds](goal). -/

@[fun_prop]
lemma measurable_sourceCellMark (i : Fin 7) : Measurable (sourceCellMark i) := by
  unfold sourceCellMark
  fin_cases i <;> simp <;> fun_prop
/-- Given [the supplied inputs](hyp:i,K,l), [the stated result about measurable source cell score holds](goal). -/

@[fun_prop]
lemma measurable_sourceCellScore (i : Fin 7) (K : ℕ) (l : Fin K) :
    Measurable (sourceCellScore i K l) := by
  unfold sourceCellScore
  exact Measurable.ite ((measurableSet_cell K l).preimage measurable_fst)
    (measurable_sourceCellMark i) measurable_const
/-- Given [the supplied inputs](hyp:K,l), [the stated result about measurable target cell score holds](goal). -/

@[fun_prop]
lemma measurable_targetCellScore (K : ℕ) (l : Fin K) :
    Measurable (targetCellScore K l) := by
  unfold targetCellScore
  exact Measurable.ite (measurableSet_cell K l) measurable_const measurable_const
/-- Given [the supplied inputs](hyp:i,K,l,o), [the stated result about source cell score mem unit interval holds](goal). -/

lemma sourceCellScore_mem_unit_interval (i : Fin 7) (K : ℕ) (l : Fin K)
    (o : SourceObs) : sourceCellScore i K l o ∈ Icc (0 : ℝ) 1 := by
  unfold sourceCellScore
  split_ifs
  · exact sourceCellMark_mem_unit_interval i o
  · simp
/-- Given [the supplied inputs](hyp:K,l,x), [the stated result about target cell score mem unit interval holds](goal). -/

lemma targetCellScore_mem_unit_interval (K : ℕ) (l : Fin K) (x : ℝ) :
    targetCellScore K l x ∈ Icc (0 : ℝ) 1 := by
  unfold targetCellScore
  split_ifs <;> simp
/-- Given [the supplied inputs](hyp:i,K,l,o), [the stated result about source cell score le indicator holds](goal). -/

lemma sourceCellScore_le_indicator (i : Fin 7) (K : ℕ) (l : Fin K)
    (o : SourceObs) :
    sourceCellScore i K l o ≤
      (Prod.fst ⁻¹' cell K l).indicator (fun _ => (1 : ℝ)) o := by
  unfold sourceCellScore
  by_cases ho : o.1 ∈ cell K l
  · simp [ho, (sourceCellMark_mem_unit_interval i o).2]
  · simp [ho]
/-- Given [the supplied inputs](hyp:K,l,x), [the stated result about target cell score le indicator holds](goal). -/

lemma targetCellScore_le_indicator (K : ℕ) (l : Fin K) (x : ℝ) :
    targetCellScore K l x ≤ (cell K l).indicator (fun _ => (1 : ℝ)) x := by
  unfold targetCellScore
  by_cases hx : x ∈ cell K l <;> simp [hx]
/-- Given [the supplied inputs](hyp:Ω,f,hf,hunit), [the stated result about mem lp two of mem unit interval holds](goal). -/

lemma memLp_two_of_mem_unit_interval
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hunit : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    MemLp f 2 μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hunit x).1]
  exact (hunit x).2
/-- Given [the supplied inputs](hyp:Ω,S,hS,f,hf,hunit,hle), [the stated result about integral bounded score le measure real holds](goal). -/

lemma integral_bounded_score_le_measureReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) {f : Ω → ℝ}
    (hf : Measurable f) (hunit : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hle : ∀ x, f x ≤ S.indicator (fun _ => (1 : ℝ)) x) :
    0 ≤ ∫ x, f x ∂μ ∧ ∫ x, f x ∂μ ≤ μ.real S := by
  have hfint : Integrable f μ :=
    (memLp_two_of_mem_unit_interval hf hunit).integrable (by norm_num)
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  constructor
  · exact integral_nonneg fun x => (hunit x).1
  · rw [← integral_indicator_one hS]
    exact integral_mono hfint hind hle
/-- Given [the supplied inputs](hyp:Ω,S,hS,f,g,hf,hg,hfunit,hgunit,hfsupp,hgsupp,p,hp,hmass), [the stated result about abs covariance bounded on event holds](goal). -/

lemma abs_covariance_bounded_on_event
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfunit : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hgunit : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hfsupp : ∀ x, f x ≤ S.indicator (fun _ => (1 : ℝ)) x)
    (hgsupp : ∀ x, g x ≤ S.indicator (fun _ => (1 : ℝ)) x)
    {p : ℝ} (hp : 0 ≤ p) (hmass : μ.real S ≤ p) :
    |cov[f, g; μ]| ≤ p + p ^ 2 := by
  have hfLp := memLp_two_of_mem_unit_interval (μ := μ) hf hfunit
  have hgLp := memLp_two_of_mem_unit_interval (μ := μ) hg hgunit
  have hfi := integral_bounded_score_le_measureReal (μ := μ) hS hf hfunit hfsupp
  have hgi := integral_bounded_score_le_measureReal (μ := μ) hS hg hgunit hgsupp
  have hfgunit (x : Ω) : f x * g x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (hfunit x).1 (hgunit x).1
    · calc
        f x * g x ≤ f x * 1 := mul_le_mul_of_nonneg_left (hgunit x).2 (hfunit x).1
        _ ≤ 1 := by simpa using (hfunit x).2
  have hfgsupp (x : Ω) : f x * g x ≤ S.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ S
    · simp [hx, (hfgunit x).2]
    · have hf0 : f x = 0 := by
        have := hfsupp x
        simp [hx] at this
        linarith [(hfunit x).1]
      simp [hx, hf0]
  have hfg := integral_bounded_score_le_measureReal (μ := μ) hS
    (hf.mul hg) hfgunit hfgsupp
  have hfg' : 0 ≤ ∫ x, f x * g x ∂μ ∧
      ∫ x, f x * g x ∂μ ≤ μ.real S := by
    simpa [Pi.mul_apply] using hfg
  rw [covariance_eq_sub hfLp hgLp]
  calc
    |∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ| ≤
        |∫ x, f x * g x ∂μ| + |(∫ x, f x ∂μ) * ∫ x, g x ∂μ| := abs_sub _ _
    _ = (∫ x, f x * g x ∂μ) + (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
      rw [abs_of_nonneg hfg'.1, abs_of_nonneg (mul_nonneg hfi.1 hgi.1)]
    _ ≤ p + p ^ 2 := by
      nlinarith [hfi.2.trans hmass, hgi.2.trans hmass, hfg'.2.trans hmass]
/-- Given [the supplied inputs](hyp:Ω,f,g,hf,hg,p,hp,hf0,hg0,hfle,hgle,hcross), [the stated result about abs covariance le sq of cross zero holds](goal). -/

lemma abs_covariance_le_sq_of_cross_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {p : ℝ}
    (hp : 0 ≤ p) (hf0 : 0 ≤ ∫ x, f x ∂μ) (hg0 : 0 ≤ ∫ x, g x ∂μ)
    (hfle : ∫ x, f x ∂μ ≤ p) (hgle : ∫ x, g x ∂μ ≤ p)
    (hcross : ∫ x, f x * g x ∂μ = 0) :
    |cov[f, g; μ]| ≤ p ^ 2 := by
  have hcross' : ∫ x, (f * g) x ∂μ = 0 := by simpa [Pi.mul_apply] using hcross
  rw [covariance_eq_sub hf hg, hcross', zero_sub, abs_neg,
    abs_of_nonneg (mul_nonneg hf0 hg0)]
  nlinarith
/-- Given [the supplied inputs](hyp:Ω,S,T,hS,hT,hST,f,g,hf,hg,hfunit,hgunit,hfsupp,hgsupp,p,hp,hSmass,hTmass), [the stated result about abs covariance bounded on disjoint events holds](goal). -/

lemma abs_covariance_bounded_on_disjoint_events
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : Disjoint S T) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfunit : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hgunit : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hfsupp : ∀ x, f x ≤ S.indicator (fun _ => (1 : ℝ)) x)
    (hgsupp : ∀ x, g x ≤ T.indicator (fun _ => (1 : ℝ)) x)
    {p : ℝ} (hp : 0 ≤ p) (hSmass : μ.real S ≤ p) (hTmass : μ.real T ≤ p) :
    |cov[f, g; μ]| ≤ p ^ 2 := by
  have hfLp := memLp_two_of_mem_unit_interval (μ := μ) hf hfunit
  have hgLp := memLp_two_of_mem_unit_interval (μ := μ) hg hgunit
  have hfi := integral_bounded_score_le_measureReal (μ := μ) hS hf hfunit hfsupp
  have hgi := integral_bounded_score_le_measureReal (μ := μ) hT hg hgunit hgsupp
  have hzero (x : Ω) : f x * g x = 0 := by
    by_cases hxS : x ∈ S
    · have hxT : x ∉ T := Set.disjoint_left.mp hST hxS
      have hg0 : g x = 0 := by
        have := hgsupp x
        simp [hxT] at this
        linarith [(hgunit x).1]
      simp [hg0]
    · have hf0 : f x = 0 := by
        have := hfsupp x
        simp [hxS] at this
        linarith [(hfunit x).1]
      simp [hf0]
  have hcross : ∫ x, f x * g x ∂μ = 0 := by
    simp_rw [hzero]
    simp
  exact abs_covariance_le_sq_of_cross_zero hfLp hgLp hp hfi.1 hgi.1
    (hfi.2.trans hSmass) (hgi.2.trans hTmass) hcross
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l), [the stated result about source event mass le holds](goal). -/

lemma source_event_mass_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (l : Fin K) :
    (sourceObsLaw P).real (Prod.fst ⁻¹' cell K l) ≤ C_f / K := by
  calc
    (sourceObsLaw P).real (Prod.fst ⁻¹' cell K l) =
        (sourceXLaw P (cell K l)).toReal := by
      rw [Measure.real_def, sourceXLaw, Measure.map_apply measurable_fst
        (measurableSet_cell K l)]
    _ ≤ C_f / K := source_cell_mass_le c_f C_f L P n K hP hK l
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,j), [the stated result about source same cell covariance le holds](goal). -/

lemma source_same_cell_covariance_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (l : Fin K) (i j : Fin 7) :
    |cov[sourceCellScore i K l, sourceCellScore j K l; sourceObsLaw P]| ≤
      C_f / K + (C_f / K) ^ 2 := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  apply abs_covariance_bounded_on_event
    ((measurableSet_cell K l).preimage measurable_fst)
    (measurable_sourceCellScore i K l) (measurable_sourceCellScore j K l)
    (sourceCellScore_mem_unit_interval i K l)
    (sourceCellScore_mem_unit_interval j K l)
    (sourceCellScore_le_indicator i K l)
    (sourceCellScore_le_indicator j K l)
  · exact div_nonneg (le_of_lt (lt_trans (by norm_num) hP.sourceBounds.2.1))
      (by positivity)
  · exact source_event_mass_le c_f C_f L P n K hP hK l
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,r,hlr,i,j), [the stated result about source off cell covariance le holds](goal). -/

lemma source_off_cell_covariance_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) {l r : Fin K} (hlr : l ≠ r)
    (i j : Fin 7) :
    |cov[sourceCellScore i K l, sourceCellScore j K r; sourceObsLaw P]| ≤
      (C_f / K) ^ 2 := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  apply abs_covariance_bounded_on_disjoint_events
    ((measurableSet_cell K l).preimage measurable_fst)
    ((measurableSet_cell K r).preimage measurable_fst)
    ((cell_disjoint hK hlr).preimage (Prod.fst : SourceObs → ℝ))
    (measurable_sourceCellScore i K l) (measurable_sourceCellScore j K r)
    (sourceCellScore_mem_unit_interval i K l)
    (sourceCellScore_mem_unit_interval j K r)
    (sourceCellScore_le_indicator i K l)
    (sourceCellScore_le_indicator j K r)
  · exact div_nonneg (le_of_lt (lt_trans (by norm_num) hP.sourceBounds.2.1))
      (by positivity)
  · exact source_event_mass_le c_f C_f L P n K hP hK l
  · exact source_event_mass_le c_f C_f L P n K hP hK r
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l), [the stated result about target same cell covariance le holds](goal). -/

lemma target_same_cell_covariance_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (l : Fin K) :
    |cov[targetCellScore K l, targetCellScore K l; targetXLaw P]| ≤
      C_f / K + (C_f / K) ^ 2 := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  apply abs_covariance_bounded_on_event (measurableSet_cell K l)
    (measurable_targetCellScore K l) (measurable_targetCellScore K l)
    (targetCellScore_mem_unit_interval K l) (targetCellScore_mem_unit_interval K l)
    (targetCellScore_le_indicator K l) (targetCellScore_le_indicator K l)
  · exact div_nonneg (le_of_lt (lt_trans (by norm_num) hP.sourceBounds.2.1))
      (by positivity)
  · exact target_cell_mass_le c_f C_f L P n K hP hK l
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,r,hlr), [the stated result about target off cell covariance le holds](goal). -/

lemma target_off_cell_covariance_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) {l r : Fin K} (hlr : l ≠ r) :
    |cov[targetCellScore K l, targetCellScore K r; targetXLaw P]| ≤
      (C_f / K) ^ 2 := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  apply abs_covariance_bounded_on_disjoint_events
    (measurableSet_cell K l) (measurableSet_cell K r) (cell_disjoint hK hlr)
    (measurable_targetCellScore K l) (measurable_targetCellScore K r)
    (targetCellScore_mem_unit_interval K l) (targetCellScore_mem_unit_interval K r)
    (targetCellScore_le_indicator K l) (targetCellScore_le_indicator K r)
  · exact div_nonneg (le_of_lt (lt_trans (by norm_num) hP.sourceBounds.2.1))
      (by positivity)
  · exact target_cell_mass_le c_f C_f L P n K hP hK l
  · exact target_cell_mass_le c_f C_f L P n K hP hK r

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
