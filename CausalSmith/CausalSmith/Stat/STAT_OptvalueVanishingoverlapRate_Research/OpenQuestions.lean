module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TConsistencyThreshold
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Open leading-constant question
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open Filter
open scoped Topology

/-- For [the displayed parameters](hyp:N,d), [AdmissiblePath](goal) is the object specified by this definition. -/
def AdmissiblePath (N d : ℕ → ℕ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 2 ≤ d k ∧ 0 < ε k ∧ ε k ≤ 1 / 2) ∧
  Tendsto N atTop atTop ∧
  Tendsto d atTop atTop ∧
  Tendsto ε atTop (𝓝 0) ∧
  Tendsto (fun k => (d k : ℝ) /
    ((N k : ℝ) * ε k * logAlphabet (d k))) atTop (𝓝 0)

/-- For no explicit parameters, [DistinctPathLimitsQuestion](goal) is the object specified by this definition. -/
def DistinctPathLimitsQuestion : Prop :=
  ∃ (κ₁ κ₂ : ℝ) (N₁ d₁ N₂ d₂ : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℝ),
    0 < κ₁ ∧ 0 < κ₂ ∧ κ₁ ≠ κ₂ ∧
    AdmissiblePath N₁ d₁ ε₁ ∧ AdmissiblePath N₂ d₂ ε₂ ∧
    Tendsto
      (fun k => ((N₁ k : ℝ) * ε₁ k * logAlphabet (d₁ k) / (d₁ k : ℝ)) *
        minimaxRisk (N₁ k) (d₁ k) (ε₁ k))
      atTop (𝓝 κ₁) ∧
    Tendsto
      (fun k => ((N₂ k : ℝ) * ε₂ k * logAlphabet (d₂ k) / (d₂ k : ℝ)) *
        minimaxRisk (N₂ k) (d₂ k) (ε₂ k))
      atTop (𝓝 κ₂)

/-- For no explicit parameters, [SharpPathConstantQuestion](goal) is the object specified by this definition. -/
def SharpPathConstantQuestion : Prop :=
  ∃ κ : ℝ, 0 < κ ∧
    ∀ (N d : ℕ → ℕ) (ε : ℕ → ℝ),
      AdmissiblePath N d ε →
      Tendsto
        (fun k => ((N k : ℝ) * ε k * logAlphabet (d k) / (d k : ℝ)) *
        minimaxRisk (N k) (d k) (ε k))
        atTop (𝓝 κ)

-- @node: oeq:sharp-path-constant
/-- For no explicit parameters, [PathLimitQuestion](goal) is the object specified by this definition. -/
def PathLimitQuestion : Prop × Prop :=
  (SharpPathConstantQuestion, DistinctPathLimitsQuestion)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
