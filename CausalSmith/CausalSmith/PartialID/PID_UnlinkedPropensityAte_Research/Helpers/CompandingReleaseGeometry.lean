module

public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.Floor

/-!
Geometry of the ordered companding release used in the unlinked propensity-score ATE analysis.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

variable {ε : ℝ}

/-- Given [the stated mathematical inputs and assumptions](hyp:f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma continuousOn_densityExtension
    {f : ScoreSpace ε → ℝ} (hf : Continuous f) :
    ContinuousOn (densityExtension f) (Icc ε (1 - ε)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert hf using 1
  funext x
  simp [densityExtension, x.property]

/-- Given [the stated mathematical inputs and assumptions](hyp:hOverlap,f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma continuousOn_compandingWeight
    (hOverlap : 0 < ε ∧ ε < 1 / 2) {f : ScoreSpace ε → ℝ}
    (hf : Continuous f) :
    ContinuousOn
      (fun t : ℝ => Real.sqrt (densityExtension f t / (t * (1 - t))))
      (Icc ε (1 - ε)) := by
  have hden : ContinuousOn (fun t : ℝ => t * (1 - t)) (Icc ε (1 - ε)) := by
    fun_prop
  have hden_ne : ∀ t ∈ Icc ε (1 - ε), t * (1 - t) ≠ 0 := by
    intro t ht
    have ht_pos : 0 < t := hOverlap.1.trans_le ht.1
    have ht_lt_one : t < 1 := by linarith [ht.2, hOverlap.1]
    exact (mul_pos ht_pos (sub_pos.mpr ht_lt_one)).ne'
  exact ((continuousOn_densityExtension hf).div hden hden_ne).sqrt

/-- Given [the stated mathematical inputs and assumptions](hyp:hOverlap,f,hf,x,y), this result [establishes the stated mathematical conclusion](goal). -/
lemma compandingWeight_intervalIntegrable
    (hOverlap : 0 < ε ∧ ε < 1 / 2) {f : ScoreSpace ε → ℝ}
    (hf : Continuous f) (x y : ScoreSpace ε) :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (densityExtension f t / (t * (1 - t))))
      volume (x : ℝ) (y : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  exact (continuousOn_compandingWeight hOverlap hf).mono
    (uIcc_subset_Icc x.property y.property)

/-- Given [the stated mathematical inputs and assumptions](hyp:hOverlap,f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma monotone_compandingMass
    (hOverlap : 0 < ε ∧ ε < 1 / 2) {f : ScoreSpace ε → ℝ}
    (hf : Continuous f) : Monotone (compandingMass f) := by
  intro x y hxy
  unfold compandingMass
  have hε_mem : ε ∈ Icc ε (1 - ε) := by
    constructor
    · rfl
    · linarith
  apply intervalIntegral.integral_mono_interval le_rfl x.property.1 hxy
  · exact Eventually.of_forall fun _ => Real.sqrt_nonneg _
  · exact compandingWeight_intervalIntegrable hOverlap hf ⟨ε, hε_mem⟩ y

-- keep: reusable admissibility of Basic.compandingRelease for future ordered-release comparisons.
/-- Given [the stated mathematical inputs and assumptions](hyp:hOverlap,f,hf,_hf_pos,K,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_compandingRelease
    (hOverlap : 0 < ε ∧ ε < 1 / 2) {f : ScoreSpace ε → ℝ}
    (hf : Continuous f) (_hf_pos : ∀ e, 0 < f e) (K : ℕ) (hK : 0 < K) :
    Measurable (compandingRelease f K hK) := by
  have hmass : Measurable (compandingMass f) :=
    (monotone_compandingMass hOverlap hf).measurable
  have hnat : Measurable fun e =>
      min (Nat.floor ((K : ℝ) * compandingMass f e /
        (∫ t in ε..(1 - ε), Real.sqrt (densityExtension f t / (t * (1 - t))))))
        (K - 1) := by
    exact ((measurable_const.mul hmass).div_const
      (∫ t in ε..(1 - ε), Real.sqrt (densityExtension f t / (t * (1 - t)))))
      |>.nat_floor.min measurable_const
  unfold compandingRelease
  apply measurable_to_countable'
  intro r
  convert hnat (measurableSet_singleton (r : ℕ)) using 1
  ext e
  exact Fin.ext_iff

end

end CausalSmith.PartialID.UnlinkedPropensityAte
