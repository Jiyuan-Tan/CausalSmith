module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBoundarySingleton
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentMixedSlope
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentProductJetBridge
public import Causalean.Mathlib.Analysis.Calculus.RectangularRemainder
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentSecondDerivative

/-! Finite-moment homogeneity testing: Helpers/ComponentDerivative. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Component discrepancy bounds hold [under the copula-domain conditions](hyp:h), and
[the asserted bounds and vanishing conclusions follow](goal). -/
-- @node: component_discrepancy_bounds
lemma component_discrepancy_bounds (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    ∀ᵐ aug ∂commonAugmentation n K M ε, ∀ C ∈ components n K M aug, ∀ labels,
      |evenDiscrepancy n K M a u aug C labels| ≤ 128*a^2*u^2*(C.card:ℝ)^4*2^C.card ∧
      |oddDiscrepancy n K M a u aug C labels| ≤ 16*a*u*(C.card:ℝ)^2*2^C.card ∧
      (C.card ≤ 1 → evenDiscrepancy n K M a u aug C labels = 0 ∧ oddDiscrepancy n K M a u aug C labels = 0) ∧
      ((C.filter (fun i => aug.2.1 i)).card ≤ 1 → evenDiscrepancy n K M a u aug C labels = 0) ∧
      ((C.filter (fun i => aug.2.1 i)).card = 0 → oddDiscrepancy n K M a u aug C labels = 0) := by
  have hK : 0 < K := by
    have hM := h.2.2.2.2.1
    have hKM := h.2.2.2.1
    omega
  have haI : 0 ≤ a ∧ a ≤ 1/16 :=
    ⟨h.2.2.2.2.2.1.1.le, h.2.2.2.2.2.1.2⟩
  have huI : 0 ≤ u ∧ u ≤ 1/16 :=
    ⟨h.2.2.2.2.2.2.1.1.le, h.2.2.2.2.2.2.1.2⟩
  have hrest : ∀ᵐ aug ∂commonAugmentation n K M ε, ∀ C ∈ components n K M aug, ∀ labels,
      |evenDiscrepancy n K M a u aug C labels| ≤ 128*a^2*u^2*(C.card:ℝ)^4*2^C.card := by
    filter_upwards [] with aug
    intro C _hC labels
    let F := fun b v => evenDiscrepancy n K M b v aug C labels
    let Fa := fun b v => evenDiscrepancyPropensityDerivative n K M b v aug C labels
    let Faa := fun b v => evenProductJet20 n K M b v aug C labels
    let FaaU := fun b v => evenProductJet21 n K M b v aug C labels
    let FaaUU := fun b v => evenProductJet22 n K M b v aug C labels
    let B : ℝ := 512*(C.card:ℝ)^4*2^C.card
    have hp (b : ℝ) (hb : b ∈ Icc 0 a) : 1-b^2 ≠ 0 := by
      have hd := correction_denominator_bounds b ⟨hb.1, hb.2.trans haI.2⟩
      linarith [hd.2.2.1]
    have hFa (b : ℝ) (hb : b ∈ Icc 0 a) :
        HasDerivAt (fun t => F t u) (Fa b u) b :=
      evenDiscrepancy_first_propensity_jet n K M b u (hp b hb) aug C labels
    have hFaa (b : ℝ) (hb : b ∈ Icc 0 a) :
        HasDerivAt (fun t => Fa t u) (Faa b u) b := by
      have hd := evenDiscrepancy_second_propensity_jet n K M b u (hp b hb) aug C labels
      rw [evenDiscrepancyPropensityCurvature_eq_evenProductJet20 n K M b u
        (hp b hb) aug C labels] at hd
      exact hd
    have hFaaU (b : ℝ) (hb : b ∈ Icc 0 a) (v : ℝ) (hv : v ∈ Icc 0 u) :
        HasDerivAt (Faa b) (FaaU b v) v :=
      evenProductJet20_hasDerivAt_outcome n K M b v aug C labels
    have hFaaUU (b : ℝ) (hb : b ∈ Icc 0 a) (v : ℝ) (hv : v ∈ Icc 0 u) :
        HasDerivAt (FaaU b) (FaaUU b v) v :=
      evenProductJet21_hasDerivAt_outcome n K M b v aug C labels
    have hbound (b : ℝ) (hb : b ∈ Icc 0 a) (v : ℝ) (hv : v ∈ Icc 0 u) :
        |FaaUU b v| ≤ B :=
      evenProductJet22_abs_le n K M b v hK
        ⟨hb.1, hb.2.trans haI.2⟩ ⟨hv.1, hv.2.trans huI.2⟩ aug C labels
    have hF0 : F 0 u = 0 :=
      (component_discrepancies_on_axes n K M 0 u aug C labels).2.2.1
    have hFa0 : Fa 0 u = 0 :=
      evenDiscrepancyPropensityDerivative_zero n K M u aug C labels
    have hFaa0 (b : ℝ) (hb : b ∈ Icc 0 a) : Faa b 0 = 0 :=
      evenProductJet20_zero_outcome n K M b ⟨hb.1, hb.2.trans haI.2⟩ aug C labels
    have hFaaU0 (b : ℝ) (hb : b ∈ Icc 0 a) : FaaU b 0 = 0 :=
      evenProductJet21_zero_outcome n K M b ⟨hb.1, hb.2.trans haI.2⟩ aug C labels
    have hr := Causalean.Mathlib.Analysis.Calculus.fourth_rectangular_remainder_bound
      F Fa Faa FaaU FaaUU a u B
      haI.1 huI.1 hFa hFaa hFaaU hFaaUU hbound hF0 hFa0 hFaa0 hFaaU0
    calc
      |evenDiscrepancy n K M a u aug C labels| ≤ B*a^2*u^2/4 := hr
      _ = 128*a^2*u^2*(C.card:ℝ)^4*2^C.card := by dsimp [B]; ring
  have ha : 1-a^2 ≠ 0 := by
    have hh := correction_denominator_bounds a ⟨h.2.2.2.2.2.1.1.le, h.2.2.2.2.2.1.2⟩
    linarith [hh.2.2.1]
  have hsmall := component_discrepancies_small_ae n K M ε a u
    (by have := h.2.2.2.2.1; omega) (by have := h.2.2.2.1; omega) ha
  filter_upwards [hrest, hsmall] with aug hr hs
  intro C hC labels
  have hh := hr C hC labels
  exact ⟨hh, oddDiscrepancy_rectangular_bound n K M a u hK
      ⟨h.2.2.2.2.2.1.1.le, h.2.2.2.2.2.1.2⟩
      ⟨h.2.2.2.2.2.2.1.1.le, h.2.2.2.2.2.2.1.2⟩ aug C labels,
    hs C labels,
    evenDiscrepancy_at_most_one_mark n K M a u aug C labels,
    fun hm => (component_discrepancies_no_marks n K M a u aug C labels hm).2⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
