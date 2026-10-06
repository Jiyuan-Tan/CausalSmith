module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation

/-! # Two-law testing bounds for honest interval length

Coverage is transferred between the full sample-and-seed experiments by total
variation. Intervals covering two effects have length at least their separation,
which yields a lower bound on expected, worst-case, and minimax length.
-/
public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Encoded intervals have length at most the width of the public effect region. [the stated conclusion](goal) holds. -/
-- @node: intervalLength_le_one
lemma intervalLength_le_one (B : EffectInterval) : intervalLength B ≤ 1 := by
  have hlo := B.property.1
  have hhi := B.property.2.1
  unfold intervalLength
  linarith

/-- Membership implies the usual weak endpoint inequalities, including open endpoints. Under the stated assumptions. [The stated hypotheses](hyp:ht) hold, and [the stated conclusion follows](goal). -/
-- @node: intervalSet_endpoint_bounds
lemma intervalSet_endpoint_bounds (B : EffectInterval) (t : ℝ)
    (ht : t ∈ intervalSet B) : B.val.1 ≤ t ∧ t ≤ B.val.2.1 := by
  rcases ht with ⟨hl, hu⟩
  constructor
  · rcases hl with h | ⟨_, h⟩
    · exact h.le
    · exact h.le
  · rcases hu with h | ⟨_, h⟩
    · exact h.le
    · exact h.le

/-- [Any connected encoded interval containing two points spans their separation.](goal) Under [the stated assumptions](hyp:ha,hb). -/
-- @node: intervalLength_ge_separation
lemma intervalLength_ge_separation (B : EffectInterval) (a b : ℝ)
    (ha : a ∈ intervalSet B) (hb : b ∈ intervalSet B) :
    b-a ≤ intervalLength B := by
  obtain ⟨hal, _⟩ := intervalSet_endpoint_bounds B a ha
  obtain ⟨_, hbu⟩ := intervalSet_endpoint_bounds B b hb
  unfold intervalLength
  linarith

/-- [The independent uniform seed and finite iid records form a probability experiment. [the stated conclusion](goal) holds. -/
-- @node: experimentLaw_probability
lemma experimentLaw_probability (P : ObservedLaw) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw P n) := by
  have : IsProbabilityMeasure uniformLaw := by
    constructor
    rw [uniformLaw, comap_subtype_coe_apply measurableSet_Icc]
    rw [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
    norm_num
  unfold experimentLaw Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
  infer_instance

/-- Length is integrable because procedures are measurable and length lies in [0,1]. [the stated conclusion](goal) holds. -/
-- @node: procedure_length_integrable
lemma procedure_length_integrable (P : ObservedLaw) (n : ℕ) (I : Procedure n) :
    Integrable (fun ω => intervalLength (I.output ω)) (experimentLaw P n) := by
  letI := experimentLaw_probability P n
  apply Integrable.of_bound I.length_measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalLength_nonneg _)]
    exact intervalLength_le_one _)

/-- Expected length stays within the public unit width. [the stated conclusion](goal) holds. -/
-- @node: expectedLength_le_one
lemma expectedLength_le_one (P : ObservedLaw) (n : ℕ) (I : Procedure n) :
    expectedLength P n I ≤ 1 := by
  letI := experimentLaw_probability P n
  calc
    expectedLength P n I ≤ ∫ _ω, (1 : ℝ) ∂experimentLaw P n :=
      integral_mono (procedure_length_integrable P n I) (integrable_const 1)
        (fun ω => intervalLength_le_one _)
    _ = 1 := by simp

/-- Every law in the radius slice gives a lower bound on its supremum risk. Under the stated assumptions. [The stated hypotheses](hyp:hP) hold, and [the stated conclusion follows](goal). -/
-- @node: expectedLength_le_worstLength
lemma expectedLength_le_worstLength (P : ObservedLaw) (n : ℕ) (α β r : ℝ)
    (I : Procedure n) (hP : RadiusModel α β r P) :
    expectedLength P n I ≤ worstLength n α β r I := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro l ⟨Q, _, rfl⟩
    exact expectedLength_le_one Q n I
  · exact ⟨P, hP, rfl⟩

/-- [Two coverage events under nearby full experiments give a length lower bound.
The seed is already included in the two laws; independent randomization is allowed. [the documented result](goal) Under [the stated assumptions](hyp:hab,hcover₀,hcover₁,htv). -/
-- @node: twoPoint_expectedLength_lower
lemma twoPoint_expectedLength_lower (P₀ P₁ : ObservedLaw) (n : ℕ)
    (I : Procedure n) (a b coverage₀ coverage₁ tv : ℝ)
    (hab : a ≤ b)
    (hcover₀ : coverage₀ ≤ (experimentLaw P₀ n).real
      {ω | a ∈ intervalSet (I.output ω)})
    (hcover₁ : coverage₁ ≤ (experimentLaw P₁ n).real
      {ω | b ∈ intervalSet (I.output ω)})
    (htv : Causalean.Stat.tvDist (experimentLaw P₀ n) (experimentLaw P₁ n) ≤ tv) :
    (b-a)*(coverage₀+coverage₁-1-tv) ≤ expectedLength P₀ n I := by
  classical
  letI := experimentLaw_probability P₀ n
  letI := experimentLaw_probability P₁ n
  let A := {ω | a ∈ intervalSet (I.output ω)}
  let B := {ω | b ∈ intervalSet (I.output ω)}
  let μ := experimentLaw P₀ n
  have hA : MeasurableSet A := I.coverage_measurable a
  have hB : MeasurableSet B := I.coverage_measurable b
  have htransfer := Causalean.Stat.measureReal_sub_le_tvDist
    (μ := experimentLaw P₀ n) (ν := experimentLaw P₁ n) hB
  have hunion := measureReal_union_add_inter' (μ := μ) (t := B) hA
  have hmass : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  have hboth : coverage₀+coverage₁-1-tv ≤ μ.real (A ∩ B) := by
    dsimp only [μ, A, B] at *
    linarith
  have hint : Integrable ((A ∩ B).indicator (fun _ => b-a)) μ :=
    (integrable_const (b-a)).indicator (hA.inter hB)
  have hpoint : ∀ ω, (A ∩ B).indicator (fun _ => b-a) ω ≤
      intervalLength (I.output ω) := by
    intro ω
    by_cases hω : ω ∈ A ∩ B
    · rw [Set.indicator_of_mem hω]
      exact intervalLength_ge_separation _ _ _ hω.1 hω.2
    · rw [Set.indicator_of_notMem hω]
      exact intervalLength_nonneg _
  calc
    (b-a)*(coverage₀+coverage₁-1-tv) ≤ (b-a)*μ.real (A ∩ B) :=
      mul_le_mul_of_nonneg_left hboth (sub_nonneg.mpr hab)
    _ = ∫ ω, (A ∩ B).indicator (fun _ => b-a) ω ∂μ := by
      rw [integral_indicator (hA.inter hB), setIntegral_const]
      simp [measureReal_def, mul_comm]
    _ ≤ expectedLength P₀ n I :=
      integral_mono hint (procedure_length_integrable P₀ n I) hpoint

/-- [Honest coverage at two model laws turns a testing comparison into a minimax floor.](goal) Under [the stated assumptions](hyp:hP₀,hP₁,horder). Under [the stated assumptions](hyp:htv). -/
-- @node: twoPoint_lengthObjective_lower
lemma twoPoint_lengthObjective_lower (P₀ P₁ : ObservedLaw) (n : ℕ) (α β r tv : ℝ)
    (hP₀ : RadiusModel α β r P₀) (hP₁ : Model α β P₁)
    (horder : effect P₀ ≤ effect P₁)
    (htv : Causalean.Stat.tvDist (experimentLaw P₀ n) (experimentLaw P₁ n) ≤ tv) :
    (effect P₁-effect P₀)*(4/5-tv) ≤ lengthObjective n α β r := by
  apply le_lengthObjective
  intro I hI
  have hcover (P : ObservedLaw) (hP : Model α β P) :
      (9/10 : ℝ) ≤ (experimentLaw P n).real
        {ω | effect P ∈ intervalSet (I.output ω)} := by
    letI := experimentLaw_probability P n
    have h := hI.coverage P hP
    have ht : experimentLaw P n {ω | effect P ∈ intervalSet (I.output ω)} ≠ ⊤ :=
      measure_ne_top _ _
    have := ENNReal.toReal_mono ht h
    norm_num [measureReal_def] at this ⊢
    exact this
  have hbound := twoPoint_expectedLength_lower P₀ P₁ n I
    (effect P₀) (effect P₁) (9/10) (9/10) tv horder
    (hcover P₀ hP₀.toModel) (hcover P₁ hP₁) htv
  have hbound' : (effect P₁-effect P₀)*(4/5-tv) ≤ expectedLength P₀ n I := by
    convert hbound using 1 <;> ring
  exact hbound'.trans (expectedLength_le_worstLength P₀ n α β r I hP₀)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
