module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PoissonSplit

/-! Good-pilot event for each observed cell. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

/-- All four pilot coordinates fall within one quarter of their local radii. -/
def pilotGood {n d : ℕ} (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (perm : Equiv.Perm (Fin n)) (M : ℕ) (marks : Fin n → Bool)
    (j : Fin d) : Prop :=
  ∀ zeta : Cell,
    |pilotCenter ((n : ℝ) / 8)
        (fun z => markedCellCount sample perm M marks false j z) zeta -
      cellVector P j zeta| ≤
      pilotHalfWidth ((n : ℝ) / 8) d
        (fun z => markedCellCount sample perm M marks false j z) zeta / 4

end CausalSmith.Stat.DiscreteBudgetvalueCurve
