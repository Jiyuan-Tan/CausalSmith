module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairSingletonMatching

/-! # Fair calibration root selection

The endpoint sign laws give identical Taylor-normalized equations and identical
literal root selectors. Existence and uniqueness in the prescribed bracket
transport to the actual selected root, without assumptions on its value.
-/
public section
noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Endpoint sign averages agree for all amplitudes and centering values. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_endpoint_eq
lemma fairNumerator_endpoint_eq (t δ ξ : ℝ) :
    fairNumerator t δ ξ 0 = fairNumerator t δ ξ 1 := by
  unfold fairNumerator
  rw [fair_endpoint_sign_average (fun z => riskShift t (ξ + δ * z)) 0 (Or.inl rfl),
    fair_endpoint_sign_average (fun z => riskShift t (ξ + δ * z)) 1 (Or.inr rfl)]

/-- Equality of the full numerator functions transports all derivatives in the
integral Taylor extension, including its zero axes. [the documented result](goal) -/
-- @node: fairEquation_endpoints
lemma fairEquation_endpoints (t δ ξ : ℝ) :
    fairEquation t δ ξ 0 = fairEquation t δ ξ 1 := by
  unfold fairEquation
  simp_rw [fairNumerator_endpoint_eq]

/-- Equal endpoint equations give equal literal fair selectors, even on fallback inputs where no bracket root exists. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: fairRoot_endpoints
lemma fairRoot_endpoints (t δ : ℝ) : fairRoot t δ 0 = fairRoot t δ 1 := by
  classical
  exact congrArg (fun F : ℝ → ℝ =>
    if h : ∃ p : ℝ, p ∈ Set.Ioo (3 / 10) (1 / 2) ∧ F p = 0
    then Classical.choose h else 2 / 5)
    (funext (fairEquation_endpoints t δ))

/-- An existing bracket root makes the totalized fair selector a genuine root. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:h). -/
-- @node: fairRoot_spec
lemma fairRoot_spec (t δ u : ℝ)
    (h : ∃ p : ℝ, p ∈ Set.Ioo (3 / 10) (1 / 2) ∧ fairEquation t δ p u = 0) :
    fairRoot t δ u ∈ Set.Ioo (3 / 10) (1 / 2) ∧
      fairEquation t δ (fairRoot t δ u) u = 0 := by
  unfold fairRoot
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The totalized selector stays in its prescribed open bracket on every input;
the fallback center also lies strictly inside that bracket. [the documented result](goal) -/
-- @node: fairRoot_mem_bracket
lemma fairRoot_mem_bracket (t δ u : ℝ) :
    fairRoot t δ u ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2) := by
  classical
  by_cases h : ∃ p : ℝ, p ∈ Set.Ioo (3 / 10) (1 / 2) ∧ fairEquation t δ p u = 0
  · exact (fairRoot_spec t δ u h).1
  · rw [fairRoot, dif_neg h]
    constructor <;> norm_num

/-- A uniquely characterized bracket root is the actual selected center. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,he,hunique) hold, and [the stated conclusion follows](goal). -/
-- @node: fairRoot_eq_of_unique
lemma fairRoot_eq_of_unique (t δ u p : ℝ)
    (hp : p ∈ Set.Ioo (3 / 10) (1 / 2)) (he : fairEquation t δ p u = 0)
    (hunique : ∀ q ∈ Set.Ioo (3 / 10) (1 / 2), fairEquation t δ q u = 0 → q = p) :
    fairRoot t δ u = p := by
  obtain ⟨hBracket, hEquation⟩ := fairRoot_spec t δ u ⟨p, hp, he⟩
  exact hunique _ hBracket hEquation

end CausalSmith.Stat.LogoddsLowsmoothFrontier
