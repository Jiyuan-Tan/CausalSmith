module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.InferenceMidpointConcentration

/-! The explicit midpoint-weighted honest interval procedure. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedRow_measurable'' (ε : ℝ) (K : ℕ) :
    Measurable (midpointWeightedRow ε K) := by
  unfold midpointWeightedRow equalWidthMidpoint
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  · fun_prop
  · fun_prop
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,n,K), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedCenter_measurable (ε : ℝ) (n K : ℕ) :
    Measurable (midpointWeightedCenter ε n K) := by
  rw [show midpointWeightedCenter ε n K = fun x : TrialSample n K =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, midpointWeightedRow ε K (x i) from
    funext (midpointWeightedCenter_eq_rowMean ε n K)]
  exact measurable_const.mul (Finset.measurable_fun_sum Finset.univ
    fun i _ => (midpointWeightedRow_measurable'' ε K).comp (measurable_pi_apply i))
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma clampATE_measurable : Measurable clampATE := by
  unfold clampATE
  fun_prop
/-- Given [the stated mathematical inputs and assumptions](hyp:x), this result [establishes the stated mathematical conclusion](goal). -/
lemma clampATE_mem_Icc (x : ℝ) : clampATE x ∈ Icc (-1 : ℝ) 1 := by
  unfold clampATE
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _ )⟩
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,hxy), this result [establishes the stated mathematical conclusion](goal). -/
lemma clampATE_mono {x y : ℝ} (hxy : x ≤ y) :
    clampATE x ≤ clampATE y := by
  unfold clampATE
  exact max_le_max (le_refl (-1 : ℝ)) (min_le_min (le_refl (1 : ℝ)) hxy)
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y), this result [establishes the stated mathematical conclusion](goal). -/
lemma clampATE_abs_sub_le (x y : ℝ) :
    |clampATE x - clampATE y| ≤ |x - y| := by
  unfold clampATE
  calc
    |max (-1) (min 1 x) - max (-1) (min 1 y)| =
        |max (min 1 x) (-1) - max (min 1 y) (-1)| := by
      rw [max_comm (-1), max_comm (-1)]
    _ ≤ |min 1 x - min 1 y| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |x - y| := by
      simpa using (abs_min_sub_min_le_max (1 : ℝ) x 1 y)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,n,K,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedRadius_nonneg {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    0 ≤ midpointWeightedRadius ε α n K := by
  unfold midpointWeightedRadius
  have hlog : 0 ≤ Real.log (4 / α) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hα.1]
    linarith [hα.2]
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
  apply add_nonneg
  · exact mul_nonneg (div_nonneg (by norm_num) hOverlap.1.le)
      (Real.sqrt_nonneg _)
  · apply div_nonneg
    · linarith [hOverlap.2]
    · exact (mul_pos (mul_pos (mul_pos (by norm_num) hKreal) hOverlap.1) hε1).le

/-- For [the specified mathematical inputs](hyp:ε,α,hOverlap,hα,n,K,hn,hK), [this definition](goal) introduces the corresponding object. -/
def midpointInterval {ε α : ℝ} (hOverlap : Overlap ε)
    (hα : 0 < α ∧ α < 1 / 2) (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    IntervalProcedure n K where
  lo x := clampATE
    (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K)
  hi x := clampATE
    (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K)
  measurable_lo := clampATE_measurable.comp
    ((midpointWeightedCenter_measurable ε n K).sub measurable_const)
  measurable_hi := clampATE_measurable.comp
    ((midpointWeightedCenter_measurable ε n K).add measurable_const)
  lower_bound x := (clampATE_mem_Icc _).1
  ordered x := clampATE_mono (by
    have hr := midpointWeightedRadius_nonneg hOverlap hα n K hn hK
    linarith)
  upper_bound x := (clampATE_mem_Icc _).2

/-- Given [overlap, the miscoverage range, positive sample and label sizes, and a released sample](hyp:ε,α,hOverlap,hα,n,K,hn,hK,x), [the midpoint interval's lower endpoint is the clamped midpoint-weighted center minus its prescribed radius](goal). -/
@[simp] lemma midpointInterval_lo {ε α : ℝ} (hOverlap : Overlap ε)
    (hα : 0 < α ∧ α < 1 / 2) (n K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (x : TrialSample n K) :
    (midpointInterval hOverlap hα n K hn hK).lo x = clampATE
      (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K) := rfl

/-- Given [overlap, the miscoverage range, positive sample and label sizes, and a released sample](hyp:ε,α,hOverlap,hα,n,K,hn,hK,x), [the midpoint interval's upper endpoint is the clamped midpoint-weighted center plus its prescribed radius](goal). -/
@[simp] lemma midpointInterval_hi {ε α : ℝ} (hOverlap : Overlap ε)
    (hα : 0 < α ∧ α < 1 / 2) (n K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (x : TrialSample n K) :
    (midpointInterval hOverlap hα n K hn hK).hi x = clampATE
      (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K) := rfl

private lemma ate_mem_Icc (P : Measure (FullRow ε K)) [IsProbabilityMeasure P] :
    ate P ∈ Icc (-1 : ℝ) 1 := by
  unfold ate
  have hInt : Integrable
      (fun ω : FullRow ε K => (outcome1 ω : ℝ) - (outcome0 ω : ℝ)) P := by
    apply Integrable.of_bound (by unfold outcome0 outcome1; fun_prop) 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr
      ⟨by linarith [(outcome1 ω).property.1, (outcome0 ω).property.2],
        by linarith [(outcome1 ω).property.2, (outcome0 ω).property.1]⟩
  constructor
  · calc
      (-1 : ℝ) = ∫ _ω : FullRow ε K, (-1 : ℝ) ∂P := by simp
      _ ≤ ∫ ω, ((outcome1 ω : ℝ) - (outcome0 ω : ℝ)) ∂P := by
        apply integral_mono (integrable_const _) hInt
        intro ω
        linarith [(outcome1 ω).property.1, (outcome0 ω).property.2]
  · calc
      (∫ ω, ((outcome1 ω : ℝ) - (outcome0 ω : ℝ)) ∂P) ≤
          ∫ _ω : FullRow ε K, (1 : ℝ) ∂P := by
        apply integral_mono hInt (integrable_const _)
        intro ω
        linarith [(outcome1 ω).property.2, (outcome0 ω).property.1]
      _ = 1 := by simp

private lemma clampATE_interval_contains {θ lo hi : ℝ}
    (hθ : θ ∈ Icc (-1 : ℝ) 1) (hlo : lo ≤ θ) (hhi : θ ≤ hi) :
    θ ∈ Icc (clampATE lo) (clampATE hi) := by
  unfold clampATE
  constructor
  · exact max_le hθ.1 ((min_le_right 1 lo).trans hlo)
  · exact (le_max_right (-1) (min 1 hi)).trans'
      (le_min hθ.2 hhi)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,n,K,hn,hK,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointInterval_length_le_two_radius {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) (x : TrialSample n K) :
    (midpointInterval hOverlap hα n K hn hK).length x ≤
      2 * midpointWeightedRadius ε α n K := by
  unfold IntervalProcedure.length
  rw [midpointInterval_lo, midpointInterval_hi]
  have hord := (midpointInterval hOverlap hα n K hn hK).ordered x
  calc
    clampATE (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K) -
        clampATE (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K) ≤
      |clampATE (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K) -
        clampATE (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K)| :=
      le_abs_self _
    _ ≤ |(midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K) -
        (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K)| :=
      clampATE_abs_sub_le _ _
    _ = 2 * midpointWeightedRadius ε α n K := by
      rw [abs_of_nonneg]
      · ring
      · have := midpointWeightedRadius_nonneg hOverlap hα n K hn hK
        linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,H,n,K,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma equalWidth_midpointInterval_honest {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    (equalWidthRelease ε K hK, midpointInterval hOverlap hα n K hn hK) ∈
      honestProcedures n K H α := by
  refine ⟨equalWidthRelease_measurable ε K hK, ?_⟩
  intro P hP
  letI : IsProbabilityMeasure P := hP.1
  let Q := releasedLaw P
  have hrecord : Measurable (releasedRecord (ε := ε) (J := K)) := by
    unfold releasedRecord label arm observed
    fun_prop
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, releasedLaw]
    exact Measure.isProbabilityMeasure_map hrecord.aemeasurable
  let μ := Measure.pi (fun _ : Fin n => Q)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let t := (4 / ε) * Real.sqrt (Real.log (4 / α) / n)
  let m := ∫ z, midpointWeightedRow ε K z ∂Q
  let bad : Set (TrialSample n K) :=
    {x | t ≤ |midpointWeightedCenter ε n K x - m|}
  have hbadMeas : MeasurableSet bad := by
    dsimp [bad, t, m]
    exact measurableSet_le measurable_const
      ((midpointWeightedCenter_measurable ε n K).sub measurable_const).abs
  have hbad : μ.real bad ≤ α := by
    dsimp [μ, bad, t, m, Q]
    exact midpointWeightedCenter_deviation_probability_le
      hOverlap hα K n hK hn (releasedLaw P)
  have hgoodProb : 1 - α ≤ μ.real badᶜ := by
    rw [MeasureTheory.measureReal_compl hbadMeas]
    rw [MeasureTheory.probReal_univ]
    linarith
  apply hgoodProb.trans
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro x hx
  have hxdev : |midpointWeightedCenter ε n K x - m| < t := by
    exact not_le.mp hx
  have hbias := midpointWeightedRow_integral_sub_ate_abs_le
    hOverlap K hK H P hP
  change |m - ate P| ≤
    (1 - 2 * ε) / (2 * K * ε * (1 - ε)) at hbias
  have hdist : |midpointWeightedCenter ε n K x - ate P| ≤
      midpointWeightedRadius ε α n K := by
    calc
      |midpointWeightedCenter ε n K x - ate P| ≤
          |midpointWeightedCenter ε n K x - m| + |m - ate P| :=
        abs_sub_le _ _ _
      _ ≤ t + (1 - 2 * ε) / (2 * K * ε * (1 - ε)) :=
        add_le_add hxdev.le hbias
      _ = midpointWeightedRadius ε α n K := by
        rfl
  have hbounds := abs_le.mp hdist
  have hθ := ate_mem_Icc P
  change ate P ∈ Icc
    ((midpointInterval hOverlap hα n K hn hK).lo x)
    ((midpointInterval hOverlap hα n K hn hK).hi x)
  rw [midpointInterval_lo, midpointInterval_hi]
  exact clampATE_interval_contains hθ (by linarith) (by linarith)

/-- For [the specified mathematical inputs](hyp:ε,α), [this definition](goal) introduces the corresponding object. -/
def midpointLengthConstant (ε α : ℝ) : ℝ :=
  (1 - 2 * ε) / (ε * (1 - ε)) +
    (8 / ε) * Real.sqrt (Real.log (4 / α))
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,n,K,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma two_midpointWeightedRadius_le_rate {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    2 * midpointWeightedRadius ε α n K ≤
      midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by
  have hlog : 0 ≤ Real.log (4 / α) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hα.1]
    linarith [hα.2]
  have hε : 0 < ε := hOverlap.1
  have hε1 : 0 < 1 - ε := by linarith [hOverlap.2]
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  let D := (1 - 2 * ε) / (ε * (1 - ε))
  let A := (8 / ε) * Real.sqrt (Real.log (4 / α))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (by linarith [hOverlap.2])
      (mul_pos hε hε1).le
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (div_nonneg (by norm_num) hε.le) (Real.sqrt_nonneg _)
  have hKinv : 0 ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr hKreal.le
  have hninv : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hradius : 2 * midpointWeightedRadius ε α n K =
      A * (Real.sqrt (n : ℝ))⁻¹ + D * (K : ℝ)⁻¹ := by
    unfold midpointWeightedRadius
    rw [Real.sqrt_div hlog]
    dsimp [A, D]
    field_simp
    ring
  rw [hradius]
  change A * (Real.sqrt (n : ℝ))⁻¹ + D * (K : ℝ)⁻¹ ≤
    (D + A) * ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹)
  nlinarith [mul_nonneg hD hninv, mul_nonneg hA hKinv]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,n,K,hn,hK,Q), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointInterval_expectedLength_le {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (Q : Measure (Observation K)) [IsProbabilityMeasure Q] :
    (∫ x, (midpointInterval hOverlap hα n K hn hK).length x
      ∂Measure.pi (fun _ : Fin n => Q)) ≤
      midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by
  let C := midpointInterval hOverlap hα n K hn hK
  let μ := Measure.pi (fun _ : Fin n => Q)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hlenInt : Integrable C.length μ := by
    apply Integrable.of_bound
      (C.measurable_hi.sub C.measurable_lo).aestronglyMeasurable 2
    filter_upwards [] with x
    have hlo := C.lower_bound x
    have hord := C.ordered x
    have hhi := C.upper_bound x
    change |C.hi x - C.lo x| ≤ 2
    rw [abs_of_nonneg (sub_nonneg.mpr hord)]
    linarith
  have hpoint (x : TrialSample n K) :
      C.length x ≤ midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by
    exact (midpointInterval_length_le_two_radius hOverlap hα n K hn hK x).trans
      (two_midpointWeightedRadius_le_rate hOverlap hα n K hn hK)
  change (∫ x, C.length x ∂μ) ≤ _
  calc
    (∫ x, C.length x ∂μ) ≤ ∫ _x, midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) ∂μ := by
      apply integral_mono hlenInt (integrable_const _)
      exact hpoint
    _ = midpointLengthConstant ε α *
        ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,H,n,K,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_equalWidth_midpointInterval {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K) :
    ∃ CI : IntervalProcedure n K,
      (equalWidthRelease ε K hK, CI) ∈ honestProcedures n K H α ∧
      (∀ x, CI.lo x = clampATE
          (midpointWeightedCenter ε n K x - midpointWeightedRadius ε α n K) ∧
        CI.hi x = clampATE
          (midpointWeightedCenter ε n K x + midpointWeightedRadius ε α n K)) ∧
      ∀ P ∈ CausalLaws H (equalWidthRelease ε K hK),
        (∫ x, CI.length x ∂(Measure.pi (fun _ : Fin n => releasedLaw P))) ≤
          midpointLengthConstant ε α *
            ((K : ℝ)⁻¹ + (Real.sqrt (n : ℝ))⁻¹) := by
  let CI := midpointInterval hOverlap hα n K hn hK
  refine ⟨CI, equalWidth_midpointInterval_honest hOverlap hα H n K hn hK,
    ?_, ?_⟩
  · intro x
    exact ⟨rfl, rfl⟩
  · intro P hP
    letI : IsProbabilityMeasure P := hP.1
    have hrecord : Measurable (releasedRecord (ε := ε) (J := K)) := by
      unfold releasedRecord label arm observed
      fun_prop
    letI : IsProbabilityMeasure (releasedLaw P) := by
      unfold releasedLaw
      exact Measure.isProbabilityMeasure_map hrecord.aemeasurable
    exact midpointInterval_expectedLength_le hOverlap hα n K hn hK (releasedLaw P)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
