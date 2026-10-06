module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic

/-! Definitions of the smooth directions used in the lower bound. -/

@[expose] public section

open Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

structure CutoffData (c : ClassConstants) where
  bump : ℝ → ℝ
  chi : ℝ → ℝ
  psi : ℝ → ℝ
  bump_smooth : ContDiff ℝ ∞ bump
  bump_nonneg : ∀ t, 0 ≤ bump t
  bump_nonzero : ∃ t, 0 < bump t
  bump_support : ∀ t, bump t ≠ 0 → t ∈ Set.Ioo 0 1
  bump_compact_inside : ∃ lo hi : ℝ, 0 < lo ∧ hi < 1 ∧
    ∀ t, bump t ≠ 0 → t ∈ Set.Icc lo hi
  chi_smooth : ContDiffOn ℝ ∞ chi (Set.Ici 0)
  chi_zero : ∀ t ∈ Set.Icc (0 : ℝ) 1, chi t = 0
  chi_one : ∀ t, 2 ≤ t → chi t = 1
  psi_smooth : ContDiffOn ℝ ∞ psi (Set.Ici 0)
  psi_support : ∀ t, psi t ≠ 0 → t ∈ Set.Ico 0 c.x0
  psi_compact_inside : ∃ hi : ℝ, hi < c.x0 ∧
    ∀ t, psi t ≠ 0 → t ∈ Set.Icc 0 hi
  psi_one : ∀ t ∈ Set.Icc (0 : ℝ) (c.x0 / 4), psi t = 1

noncomputable def endpointDirection (c : ClassConstants) (cut : CutoffData c)
    (u h t : ℝ) : ℝ :=
  u * h ^ c.beta * cut.bump ((1 - t) / h)

noncomputable def criticalBandwidth (c : ClassConstants) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log n) ^ (-(1 / (2 * c.beta + 2)))

noncomputable def criticalDirection (c : ClassConstants) (cut : CutoffData c)
    (u : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  let x := 1 - t
  if x = 0 then 0 else
    (u / Real.sqrt ((n : ℝ) * Real.log n)) *
      cut.chi (x / criticalBandwidth c n) * cut.psi x / x

-- @node: def:lower-directions
noncomputable def lowerDirections (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) (n : ℕ) (t : ℝ) : ℝ × ℝ :=
  (endpointDirection c cut u h t, criticalDirection c cut u n t)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
