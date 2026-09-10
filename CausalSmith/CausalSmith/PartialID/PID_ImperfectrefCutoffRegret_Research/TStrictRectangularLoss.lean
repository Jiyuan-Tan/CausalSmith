import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpRegretFormula
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.FiniteSupport
import Mathlib.Tactic.NormNum

/-! Explicit three-score separation of coherent regret from rectangular envelopes. -/

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def witnessObserved : Measure (ℝ × Bool) :=
  ∑ r : Bool,
    (((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac ((0 : ℝ), r) +
     ((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac ((1 : ℝ), r) +
     ((2 / 5 : NNReal) : ℝ≥0∞) • Measure.dirac ((2 : ℝ), r))

-- @node: def:three-score-witness
set_option linter.flexible false in
noncomputable def witnessW3 : ImperfectReferenceModel :=
  { P := witnessObserved
    isProbability := by
      constructor
      simp [witnessObserved]
      rw [← ENNReal.toNNReal_eq_toNNReal_iff' (by finiteness) (by simp)]
      repeat' rw [ENNReal.toNNReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toNNReal_inv, ENNReal.toNNReal_div,
        ENNReal.toNNReal_ofNat]
      apply NNReal.eq
      norm_num [NNReal.coe_add, NNReal.coe_div]
    alpha := 4 / 5
    alpha_mem_Icc := by norm_num
    beta := 4 / 5
    beta_mem_Icc := by norm_num
    b := 1
    c := 1
    T := {⊥, (1 : EReal), (2 : EReal), ⊤}
    T_nonempty := by exact ⟨⊥, by simp⟩ }
  -- @realizes \(\mathsf W_3\)(three-score rational observed model)

def w3Score : Fin 3 → ℝ := fun j => j.val

def pointwiseEnvelopeCriterion (M : ImperfectReferenceModel) (t : EReal) : ℝ :=
  max 0 (sSup {x : ℝ | ∃ u ∈ M.T, u ≠ t ∧
    x = netValueUpper M u - netValueLower M t})

def StrictRectangularLossConclusion : Prop :=
  ((netValueLower witnessW3 ⊥, netValueUpper witnessW3 ⊥) = (0, 0) ∧
   (netValueLower witnessW3 1, netValueUpper witnessW3 1) = (-1 / 10, 1 / 10) ∧
   (netValueLower witnessW3 2, netValueUpper witnessW3 2) = (-1 / 5, 1 / 5) ∧
   (netValueLower witnessW3 ⊤, netValueUpper witnessW3 ⊤) = (0, 0)) ∧
  (regretAt witnessW3 ⟨⊥, by simp [witnessW3]⟩ = 1 / 5 ∧
   regretAt witnessW3 ⟨1, by simp [witnessW3]⟩ = 1 / 10 ∧
   regretAt witnessW3 ⟨2, by simp [witnessW3]⟩ = 1 / 5 ∧
   regretAt witnessW3 ⟨⊤, by simp [witnessW3]⟩ = 1 / 5 ∧
   optimizerSet witnessW3 = {(1 : EReal)}) ∧
  (pointwiseEnvelopeCriterion witnessW3 ⊥ = 1 / 5 ∧
   pointwiseEnvelopeCriterion witnessW3 1 = 3 / 10 ∧
   pointwiseEnvelopeCriterion witnessW3 2 = 3 / 10 ∧
   pointwiseEnvelopeCriterion witnessW3 ⊤ = 1 / 5 ∧
   {t ∈ witnessW3.T | ∀ u ∈ witnessW3.T,
      pointwiseEnvelopeCriterion witnessW3 t ≤
        pointwiseEnvelopeCriterion witnessW3 u} = {⊥, ⊤}) ∧
  (∃ ε > 0, ∀ M : ImperfectReferenceModel,
    |M.alpha - witnessW3.alpha| < ε → |M.beta - witnessW3.beta| < ε →
    (∀ r j, |stratumMass M r (singletonBorel (w3Score j)) -
      stratumMass witnessW3 r (singletonBorel (w3Score j))| < ε) →
    M.b = witnessW3.b → M.c = witnessW3.c → M.T = witnessW3.T →
    FiniteScoreSupport M 3 w3Score →
    (∃ Q : Measure (ℝ × Bool × Bool), CompatibleLaw M Q) →
    optimizerSet M = {(1 : EReal)} ∧
      {t ∈ M.T | ∀ u ∈ M.T,
        pointwiseEnvelopeCriterion M t ≤ pointwiseEnvelopeCriterion M u} ⊆ {⊥, ⊤})

lemma w3_reference_sensitivity :
    ∃ Q : Measure (ℝ × Bool × Bool), ReferenceSensitivity witnessW3 Q := by
  exact ⟨0, by simp [ReferenceSensitivity]⟩

lemma w3_reference_specificity :
    ∃ Q : Measure (ℝ × Bool × Bool), ReferenceSpecificity witnessW3 Q := by
  exact ⟨0, by simp [ReferenceSpecificity]⟩

lemma w3_youden_pos : InformativeReference witnessW3 := by
  norm_num [InformativeReference, youden, witnessW3]

lemma w3_prevalence_interior : InteriorPrevalence witnessW3 := by
  have hmass : obsMass witnessW3 true = 1 / 2 := by
    rw [obsMass_eq_reference_event]
    simp [witnessW3, witnessObserved, Measure.real]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  have hprev : prevalence witnessW3 = 1 / 2 := by
    rw [prevalence, hmass]
    norm_num [youden, witnessW3]
  rw [InteriorPrevalence, hprev]
  norm_num

lemma w3_finite_support : FiniteScoreSupport witnessW3 3 w3Score := by
  constructor
  · intro i j hij
    simpa [w3Score] using hij
  · have hsupport (c : ℝ≥0∞) (hc : 0 < c) (a : ℝ) :
        (c • Measure.dirac a).support = {a} := by
      ext x
      rw [Measure.mem_support_iff_forall]
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hx
        by_contra hxa
        have hnhds : ({a}ᶜ : Set ℝ) ∈ 𝓝 x :=
          isClosed_singleton.isOpen_compl.mem_nhds (by simpa [hxa])
        have hpos := hx _ hnhds
        simp [Measure.smul_apply, Measure.dirac_apply, hxa] at hpos
      · rintro rfl U hU
        simp [Measure.smul_apply, Measure.dirac_apply, mem_of_mem_nhds hU, hc]
    rw [show scoreMarginal witnessW3 =
        (((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
         ((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
         ((2 / 5 : NNReal) : ℝ≥0∞) • Measure.dirac (2 : ℝ)) +
        (((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
         ((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
         ((2 / 5 : NNReal) : ℝ≥0∞) • Measure.dirac (2 : ℝ)) by
      simp [scoreMarginal, witnessW3, witnessObserved, Measure.map_add,
        Measure.map_smul, measurable_fst]]
    have h20 (a : ℝ) :
        (((1 / 20 : NNReal) : ℝ≥0∞) • Measure.dirac a).support = {a} :=
      hsupport _ (by norm_num) a
    have h25 (a : ℝ) :
        (((2 / 5 : NNReal) : ℝ≥0∞) • Measure.dirac a).support = {a} :=
      hsupport _ (by norm_num) a
    repeat' rw [Measure.support_add]
    simp_rw [h20, h25]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range, w3Score]
    constructor
    · rintro (((rfl | rfl) | rfl) | ((rfl | rfl) | rfl))
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact ⟨2, by norm_num⟩
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact ⟨2, by norm_num⟩
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp

-- @node: prop:strict-rectangular-loss
theorem strict_rectangular_loss (Q : Measure (ℝ × Bool × Bool))
    (hα : ReferenceSensitivity witnessW3 Q)
    (hβ : ReferenceSpecificity witnessW3 Q)
    (hg : InformativeReference witnessW3)
    (hπ : InteriorPrevalence witnessW3)
    (hfinite : FiniteScoreSupport witnessW3 3 w3Score) :
    StrictRectangularLossConclusion := by sorry

theorem strict_rectangular_loss_w3 : StrictRectangularLossConclusion := by
  exact strict_rectangular_loss 0
    (by simp [ReferenceSensitivity])
    (by simp [ReferenceSpecificity])
    w3_youden_pos w3_prevalence_interior w3_finite_support

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
