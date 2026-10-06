module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Inference
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawMembership
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelFiniteGeometry

/-! Population bias of the equal-width midpoint inverse-propensity statistic. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,K,z), [this definition](goal) introduces the corresponding object. -/
def midpointWeightedRow (ε : ℝ) (K : ℕ) (z : Observation K) : ℝ :=
  if z.2.1 then
    (z.2.2 : ℝ) / equalWidthMidpoint ε K z.1
  else
    -(z.2.2 : ℝ) / (1 - equalWidthMidpoint ε K z.1)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,n,K,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedCenter_eq_rowMean (ε : ℝ) (n K : ℕ)
    (x : TrialSample n K) :
    midpointWeightedCenter ε n K x =
      (n : ℝ)⁻¹ * ∑ i : Fin n, midpointWeightedRow ε K (x i) := by
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,K,hK,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma score_sub_equalWidthMidpoint_abs_le {ε : ℝ}
    (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K) (e : ScoreSpace ε) :
    |(e : ℝ) - equalWidthMidpoint ε K (equalWidthRelease ε K hK e)| ≤
      (1 - 2 * ε) / (2 * K) := by
  let r := equalWidthRelease ε K hK e
  have he : e ∈ cell (equalWidthRelease ε K hK) r := by
    rfl
  have hb := equalWidthRelease_cell_subset_closedBin hOverlap hK r he
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hw : 0 ≤ (1 - 2 * ε) / K :=
    div_nonneg (by linarith [hOverlap.2]) hKreal.le
  have hhalf : (1 - 2 * ε) / (2 * K) = ((1 - 2 * ε) / K) / 2 := by
    field_simp
  rw [abs_le]
  rw [hhalf]
  constructor <;>
    dsimp [equalWidthMidpoint, r] at hb ⊢ <;>
    ring_nf at hb ⊢ <;>
    linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,K,hK,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidthMidpoint_mem_Icc {ε : ℝ}
    (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K) (r : LabelSpace K) :
    equalWidthMidpoint ε K r ∈ Icc ε (1 - ε) := by
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hwidth : 0 < 1 - 2 * ε := by linarith [hOverlap.2]
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hrK : (r : ℝ) + (1 / 2 : ℝ) ≤ (K : ℝ) := by
    have hrCast : (r : ℝ) + 1 ≤ (K : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr r.isLt)
    linarith
  constructor
  · unfold equalWidthMidpoint
    apply le_add_of_nonneg_right
    exact div_nonneg (mul_nonneg (by linarith) hwidth.le) hKreal.le
  · unfold equalWidthMidpoint
    have hratio : ((r : ℝ) + (1 / 2 : ℝ)) / K ≤ 1 :=
      (div_le_one hKreal).mpr hrK
    calc
      ε + ((r : ℕ) + (1 / 2 : ℝ)) * (1 - 2 * ε) / K =
          ε + (((r : ℝ) + (1 / 2 : ℝ)) / K) * (1 - 2 * ε) := by ring
      _ ≤ ε + 1 * (1 - 2 * ε) := by gcongr
      _ ≤ 1 - ε := by ring_nf; linarith

private lemma midpointWeightedRow_measurable (ε : ℝ) (K : ℕ) :
    Measurable (midpointWeightedRow ε K) := by
  unfold midpointWeightedRow equalWidthMidpoint
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  · fun_prop
  · fun_prop

private lemma assignedLatent_integral_eq_mul_armProb
    {ε : ℝ} {K : ℕ} (P : Measure (FullRow ε K)) [IsProbabilityMeasure P]
    (hOverlap : Overlap ε) (hRandom : RandomizedAssignment P)
    (a : ArmSpace) (φ : ScoreSpace ε × OutcomeSpace × OutcomeSpace → ℝ)
    (hφ : Measurable φ) :
    (∫ x, φ x ∂assignedLatentLaw P a) =
      ∫ x, armProb a x.1 * φ x ∂(P.map latentTriple) := by
  rw [assignedLatentLaw_eq_propensityTiltedLatentLaw P hOverlap hRandom a]
  unfold propensityTiltedLatentLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
    (ae_of_all _ fun _ => by finiteness)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : 0 < armProb a x.1 := by
    rcases x.1.property with ⟨hx₁, hx₂⟩
    cases a <;> simp [armProb] <;> linarith [hOverlap.1]
  rw [ENNReal.toReal_ofReal hp.le]
  simp only [smul_eq_mul]

private def scoreBinMidpoint (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (e : ScoreSpace ε) : ℝ :=
  equalWidthMidpoint ε K (equalWidthRelease ε K hK e)

private def midpointLatentTerm (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (a : ArmSpace) (x : ScoreSpace ε × OutcomeSpace × OutcomeSpace) : ℝ :=
  if a then (x.2.2 : ℝ) / scoreBinMidpoint ε K hK x.1
  else -(x.2.1 : ℝ) / (1 - scoreBinMidpoint ε K hK x.1)

private lemma midpointLatentTerm_measurable (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (a : ArmSpace) : Measurable (midpointLatentTerm ε K hK a) := by
  cases a
  · change Measurable (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
      -(x.2.1 : ℝ) / (1 - scoreBinMidpoint ε K hK x.1))
    unfold scoreBinMidpoint equalWidthMidpoint
    fun_prop
  · change Measurable (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
      (x.2.2 : ℝ) / scoreBinMidpoint ε K hK x.1)
    unfold scoreBinMidpoint equalWidthMidpoint
    fun_prop

private lemma midpointLatentTerm_comp_integrable
    {ε : ℝ} (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K)
    (P : Measure (FullRow ε K)) [IsProbabilityMeasure P] (a : ArmSpace) :
    Integrable (fun ω => midpointLatentTerm ε K hK a (latentTriple ω)) P := by
  apply Integrable.of_bound
    ((midpointLatentTerm_measurable ε K hK a).comp (by
      unfold latentTriple score outcome0 outcome1
      fun_prop)).aestronglyMeasurable ε⁻¹
  filter_upwards [] with ω
  have hm := equalWidthMidpoint_mem_Icc hOverlap K hK
    (equalWidthRelease ε K hK (score ω))
  have hm' : scoreBinMidpoint ε K hK (score ω) ∈ Icc ε (1 - ε) := by
    simpa [scoreBinMidpoint] using hm
  have hε : 0 < ε := hOverlap.1
  have hm0 : 0 < scoreBinMidpoint ε K hK (score ω) := by
    exact hε.trans_le hm'.1
  have hm1 : 0 < 1 - scoreBinMidpoint ε K hK (score ω) := by
    linarith [hm'.2, hOverlap.1]
  cases a
  · change |-(outcome0 ω : ℝ) / (1 - scoreBinMidpoint ε K hK (score ω))| ≤ ε⁻¹
    rw [abs_div, abs_neg, abs_of_nonneg (outcome0 ω).property.1,
      abs_of_pos hm1]
    have hy := (outcome0 ω).property.2
    have hmLower : ε ≤ 1 - scoreBinMidpoint ε K hK (score ω) := by
      linarith [hm'.2]
    have hinv := (inv_le_inv₀ hm1 hε).mpr hmLower
    calc
      (outcome0 ω : ℝ) / (1 - scoreBinMidpoint ε K hK (score ω)) ≤
          1 / (1 - scoreBinMidpoint ε K hK (score ω)) := by
        exact div_le_div_of_nonneg_right hy hm1.le
      _ ≤ ε⁻¹ := by simpa [one_div] using hinv
  · change |(outcome1 ω : ℝ) / scoreBinMidpoint ε K hK (score ω)| ≤ ε⁻¹
    rw [abs_div, abs_of_nonneg (outcome1 ω).property.1, abs_of_pos hm0]
    have hy := (outcome1 ω).property.2
    have hmLower : ε ≤ scoreBinMidpoint ε K hK (score ω) := hm'.1
    have hinv := (inv_le_inv₀ hm0 hε).mpr hmLower
    calc
      (outcome1 ω : ℝ) / scoreBinMidpoint ε K hK (score ω) ≤
          1 / scoreBinMidpoint ε K hK (score ω) := by
        exact div_le_div_of_nonneg_right hy hm0.le
      _ ≤ ε⁻¹ := by simpa [one_div] using hinv

private lemma released_midpointRow_integral_eq_assignedLatent
    {ε : ℝ} (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K)
    (P : Measure (FullRow ε K)) [IsProbabilityMeasure P]
    (hConsistency : Consistency P)
    (hRelease : DeterministicRelease (equalWidthRelease ε K hK) P) :
    (∫ z, midpointWeightedRow ε K z ∂releasedLaw P) =
      (∫ x, midpointLatentTerm ε K hK true x ∂assignedLatentLaw P true) +
        ∫ x, midpointLatentTerm ε K hK false x ∂assignedLatentLaw P false := by
  have hrecord : Measurable (releasedRecord (ε := ε) (J := K)) := by
    unfold releasedRecord label arm observed
    fun_prop
  rw [releasedLaw, integral_map hrecord.aemeasurable
    (midpointWeightedRow_measurable ε K).aestronglyMeasurable]
  have hrewrite :
      (∫ ω, midpointWeightedRow ε K (releasedRecord ω) ∂P) =
        ∫ ω, if arm ω = true then
          midpointLatentTerm ε K hK true (latentTriple ω)
        else midpointLatentTerm ε K hK false (latentTriple ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hConsistency, hRelease] with ω hcons hrel
    cases ha : arm ω
    · have hobs : observed ω = outcome0 ω := by simpa [ha] using hcons
      have ha' : ω.2.2.2.1 = false := by simpa [arm] using ha
      simp only [midpointWeightedRow, releasedRecord]
      rw [show label ω = equalWidthRelease ε K hK (score ω) from hrel, hobs]
      simp [midpointWeightedRow, midpointLatentTerm, scoreBinMidpoint,
        releasedRecord, label, observed, arm, ha', latentTriple]
    · have hobs : observed ω = outcome1 ω := by simpa [ha] using hcons
      have ha' : ω.2.2.2.1 = true := by simpa [arm] using ha
      simp only [midpointWeightedRow, releasedRecord]
      rw [show label ω = equalWidthRelease ε K hK (score ω) from hrel, hobs]
      simp [midpointWeightedRow, midpointLatentTerm, scoreBinMidpoint,
        releasedRecord, label, observed, arm, ha', latentTriple]
  rw [hrewrite]
  let S : Set (FullRow ε K) := {ω | arm ω = true}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
  have htrueInt := midpointLatentTerm_comp_integrable hOverlap K hK P true
  have hfalseInt := midpointLatentTerm_comp_integrable hOverlap K hK P false
  have hpiece := integral_piecewise hS htrueInt.integrableOn
    hfalseInt.integrableOn
  have hSc : Sᶜ = {ω : FullRow ε K | arm ω = false} := by
    ext ω
    cases h : arm ω <;> simp [S, h]
  change (∫ ω, S.piecewise
      (fun ω => midpointLatentTerm ε K hK true (latentTriple ω))
      (fun ω => midpointLatentTerm ε K hK false (latentTriple ω)) ω ∂P) = _
  rw [hpiece, hSc]
  have hlatent : Measurable (latentTriple (ε := ε) (J := K)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  congr 1 <;>
    rw [assignedLatentLaw, integral_map hlatent.aemeasurable
      (midpointLatentTerm_measurable ε K hK _).aestronglyMeasurable]

private def midpointLatentBias (ε : ℝ) (K : ℕ) (hK : 0 < K)
    (x : ScoreSpace ε × OutcomeSpace × OutcomeSpace) : ℝ :=
  ((x.1 : ℝ) - scoreBinMidpoint ε K hK x.1) *
    ((x.2.2 : ℝ) / scoreBinMidpoint ε K hK x.1 +
      (x.2.1 : ℝ) / (1 - scoreBinMidpoint ε K hK x.1))

private lemma midpoint_populationBias_eq_integral
    {ε : ℝ} (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K)
    (P : Measure (FullRow ε K)) [IsProbabilityMeasure P]
    (hRandom : RandomizedAssignment P) (hConsistency : Consistency P)
    (hRelease : DeterministicRelease (equalWidthRelease ε K hK) P) :
    (∫ z, midpointWeightedRow ε K z ∂releasedLaw P) - ate P =
      ∫ x, midpointLatentBias ε K hK x ∂(P.map latentTriple) := by
  have hlatent : Measurable (latentTriple (ε := ε) (J := K)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  let μ := P.map (latentTriple (ε := ε) (J := K))
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hlatent.aemeasurable
  have htermInt (a : ArmSpace) :
      Integrable (midpointLatentTerm ε K hK a) μ := by
    apply (integrable_map_measure
      (midpointLatentTerm_measurable ε K hK a).aestronglyMeasurable
      hlatent.aemeasurable).mpr
    exact midpointLatentTerm_comp_integrable hOverlap K hK P a
  have hpMeas (a : ArmSpace) :
      Measurable (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace => armProb a x.1) := by
    cases a <;> simp [armProb] <;> fun_prop
  have hpBound (a : ArmSpace) :
      ∀ᵐ x ∂μ, ‖armProb a x.1‖ ≤ 1 := by
    filter_upwards [] with x
    have hb := projectionArmProb_bounds hOverlap a x.1
    rw [Real.norm_eq_abs, abs_of_nonneg (hOverlap.1.le.trans hb.1)]
    exact hb.2
  have hweightedInt (a : ArmSpace) : Integrable
      (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
        armProb a x.1 * midpointLatentTerm ε K hK a x) μ :=
    (htermInt a).bdd_mul (hpMeas a).aestronglyMeasurable (hpBound a)
  have hpotentialInt : Integrable
      (fun x : ScoreSpace ε × OutcomeSpace × OutcomeSpace =>
        (x.2.2 : ℝ) - (x.2.1 : ℝ)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [x.2.1.property.2, x.2.2.property.1],
      by linarith [x.2.2.property.2, x.2.1.property.1]⟩
  have hreleased := released_midpointRow_integral_eq_assignedLatent
    hOverlap K hK P hConsistency hRelease
  rw [hreleased,
    assignedLatent_integral_eq_mul_armProb P hOverlap hRandom true
      (midpointLatentTerm ε K hK true) (midpointLatentTerm_measurable ε K hK true),
    assignedLatent_integral_eq_mul_armProb P hOverlap hRandom false
      (midpointLatentTerm ε K hK false) (midpointLatentTerm_measurable ε K hK false)]
  have hate : ate P = ∫ x, ((x.2.2 : ℝ) - (x.2.1 : ℝ)) ∂μ := by
    unfold ate μ
    rw [integral_map hlatent.aemeasurable (by fun_prop)]
    rfl
  rw [hate, ← integral_add (hweightedInt true) (hweightedInt false),
    ]
  change (∫ x,
      (armProb true x.1 * midpointLatentTerm ε K hK true x +
        armProb false x.1 * midpointLatentTerm ε K hK false x) ∂μ) -
      (∫ x, ((x.2.2 : ℝ) - (x.2.1 : ℝ)) ∂μ) =
    ∫ x, midpointLatentBias ε K hK x ∂μ
  have hsumInt : Integrable (fun x =>
      armProb true x.1 * midpointLatentTerm ε K hK true x +
        armProb false x.1 * midpointLatentTerm ε K hK false x) μ :=
    (hweightedInt true).add (hweightedInt false)
  rw [← integral_sub hsumInt hpotentialInt]
  apply integral_congr_ae
  filter_upwards [] with x
  have hm := equalWidthMidpoint_mem_Icc hOverlap K hK
    (equalWidthRelease ε K hK x.1)
  have hm' : scoreBinMidpoint ε K hK x.1 ∈ Icc ε (1 - ε) := by
    simpa [scoreBinMidpoint] using hm
  have hm0 : scoreBinMidpoint ε K hK x.1 ≠ 0 :=
    ne_of_gt (hOverlap.1.trans_le hm'.1)
  have hm1 : 1 - scoreBinMidpoint ε K hK x.1 ≠ 0 := by
    have : scoreBinMidpoint ε K hK x.1 < 1 :=
      hm'.2.trans_lt (by linarith [hOverlap.1])
    linarith
  simp only [armProb, midpointLatentTerm, Bool.false_eq_true, ↓reduceIte]
  unfold midpointLatentBias
  field_simp
  ring

private lemma midpointLatentBias_measurable
    (ε : ℝ) (K : ℕ) (hK : 0 < K) :
    Measurable (midpointLatentBias ε K hK) := by
  unfold midpointLatentBias scoreBinMidpoint equalWidthMidpoint
  fun_prop

private lemma midpointLatentBias_abs_le
    {ε : ℝ} (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K)
    (x : ScoreSpace ε × OutcomeSpace × OutcomeSpace) :
    |midpointLatentBias ε K hK x| ≤
      (1 - 2 * ε) / (2 * K * ε * (1 - ε)) := by
  let m := scoreBinMidpoint ε K hK x.1
  let δ := (1 - 2 * ε) / (2 * K)
  have hmRaw := equalWidthMidpoint_mem_Icc hOverlap K hK
    (equalWidthRelease ε K hK x.1)
  have hm : m ∈ Icc ε (1 - ε) := by
    simpa [m, scoreBinMidpoint] using hmRaw
  have hε : 0 < ε := hOverlap.1
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
  have hm0 : 0 < m := hε.trans_le hm.1
  have hm1 : 0 < 1 - m := by linarith [hm.2, hOverlap.1]
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    apply div_nonneg
    · linarith [hOverlap.2]
    · positivity
  have hscore : |(x.1 : ℝ) - m| ≤ δ := by
    simpa [m, δ, scoreBinMidpoint] using
      score_sub_equalWidthMidpoint_abs_le hOverlap K hK x.1
  have hprod : ε * (1 - ε) ≤ m * (1 - m) := by
    have hnonneg : 0 ≤ (m - ε) * (1 - ε - m) :=
      mul_nonneg (sub_nonneg.mpr hm.1) (sub_nonneg.mpr hm.2)
    nlinarith
  have hinvProd : (m * (1 - m))⁻¹ ≤ (ε * (1 - ε))⁻¹ :=
    (inv_le_inv₀ (mul_pos hm0 hm1) (mul_pos hε hε1)).mpr hprod
  let c := (x.2.2 : ℝ) / m + (x.2.1 : ℝ) / (1 - m)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg (div_nonneg x.2.2.property.1 hm0.le)
      (div_nonneg x.2.1.property.1 hm1.le)
  have hc : c ≤ (m * (1 - m))⁻¹ := by
    have h₁ : (x.2.2 : ℝ) / m ≤ 1 / m :=
      div_le_div_of_nonneg_right x.2.2.property.2 hm0.le
    have h₀ : (x.2.1 : ℝ) / (1 - m) ≤ 1 / (1 - m) :=
      div_le_div_of_nonneg_right x.2.1.property.2 hm1.le
    calc
      c ≤ 1 / m + 1 / (1 - m) := add_le_add h₁ h₀
      _ = (m * (1 - m))⁻¹ := by field_simp; ring
  have hcEnd : c ≤ (ε * (1 - ε))⁻¹ := hc.trans hinvProd
  have hmain : |((x.1 : ℝ) - m) * c| ≤
      δ * (ε * (1 - ε))⁻¹ := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hscore hcEnd hc0 hδ
  change |((x.1 : ℝ) - m) * c| ≤ _
  calc
    |((x.1 : ℝ) - m) * c| ≤ δ * (ε * (1 - ε))⁻¹ := hmain
    _ = (1 - 2 * ε) / (2 * K * ε * (1 - ε)) := by
      dsimp [δ]
      field_simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,K,hK,H,P,hP), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedRow_integral_sub_ate_abs_le
    {ε : ℝ} (hOverlap : Overlap ε) (K : ℕ) (hK : 0 < K)
    (H : Measure (ScoreSpace ε)) (P : Measure (FullRow ε K))
    (hP : P ∈ CausalLaws H (equalWidthRelease ε K hK)) :
    |(∫ z, midpointWeightedRow ε K z ∂releasedLaw P) - ate P| ≤
      (1 - 2 * ε) / (2 * K * ε * (1 - ε)) := by
  letI : IsProbabilityMeasure P := hP.1
  let μ := P.map (latentTriple (ε := ε) (J := K))
  have hlatent : Measurable (latentTriple (ε := ε) (J := K)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hlatent.aemeasurable
  let B := (1 - 2 * ε) / (2 * K * ε * (1 - ε))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    apply div_nonneg
    · linarith [hOverlap.2]
    · have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
      have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
      exact (mul_pos (mul_pos (mul_pos (by norm_num) hKreal) hOverlap.1) hε1).le
  have hbiasInt : Integrable (midpointLatentBias ε K hK) μ := by
    apply Integrable.of_bound
      (midpointLatentBias_measurable ε K hK).aestronglyMeasurable B
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact midpointLatentBias_abs_le hOverlap K hK x
  rw [midpoint_populationBias_eq_integral hOverlap K hK P
    hP.2.randomizedAssignment hP.2.consistency hP.2.deterministicRelease]
  change |∫ x, midpointLatentBias ε K hK x ∂μ| ≤ B
  calc
    |∫ x, midpointLatentBias ε K hK x ∂μ| ≤
        ∫ x, |midpointLatentBias ε K hK x| ∂μ :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _x, B ∂μ := by
      apply integral_mono hbiasInt.abs (integrable_const B)
      exact midpointLatentBias_abs_le hOverlap K hK
    _ = B := by simp

end
end CausalSmith.PartialID.UnlinkedPropensityAte
