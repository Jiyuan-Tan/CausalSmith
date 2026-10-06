module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.HostileRayleigh

/-! # Hostile thin-slab design and raw Gram degeneration -/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory Filter
open scoped BigOperators

-- @node: prop:hostile-design
/-- The hostile design preserves the global tail envelope but drives the
smallest eigenvalue of its full raw linear Gram to zero. Occupied balanced Grams retain the
deterministic lower bound. -/
theorem hostile_design (d : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q) :
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (volume.restrict (cube d)).real
        {x | hostilePropensity d q x ≤ t} ≤ t ^ q) ∧
    Tendsto (fun j : ℕ => rawHostileMinEigenvalue d j q) atTop (nhds 0) ∧
    (∀ (n j : ℕ) (β : ℝ) (sample : Fin n → Obs d)
      (Q : Fin d → Fin (2 ^ j)),
      0 < minimumCellCount sample true j (polynomialOrder β)
        (normingSubcells d β).radius Q →
      ∀ a : MultiIndex d (polynomialOrder β) → ℝ,
        referenceLowerEigenvalue d (polynomialOrder β) / 2 *
          (∑ i, (a i) ^ 2) ≤
        quadraticForm (balancedGram sample true j (polynomialOrder β)
          (normingSubcells d β).radius Q) a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hsub : {x | hostilePropensity d q x ≤ t} ∩ cube d ⊆
        {x | baselinePropensity d q x ≤ t} ∩ cube d := by
      rintro x ⟨hx, hcube⟩
      exact ⟨(hostilePropensity_ge_baseline_on_cube d q hd hq x hcube).trans hx,
        hcube⟩
    have hfinite : volume
        ({x | baselinePropensity d q x ≤ t} ∩ cube d) ≠ ⊤ := by
      have hcube : volume (cube d) = 1 := by simp [cube, Real.volume_Icc_pi]
      exact ne_top_of_le_ne_top (by simp [hcube])
        (measure_mono Set.inter_subset_right)
    have hmono : (volume.restrict (cube d)).real
        {x | hostilePropensity d q x ≤ t} ≤
        (volume.restrict (cube d)).real
          {x | baselinePropensity d q x ≤ t} := by
      rw [measureReal_restrict_apply' (by simp [cube] : MeasurableSet (cube d)),
        measureReal_restrict_apply' (by simp [cube] : MeasurableSet (cube d))]
      exact measureReal_mono hsub hfinite
    exact hmono.trans (baselinePropensity_sublevel_volume d q hd hq t ht)
  · exact rawHostileMinEigenvalue_tendsto_zero d q hd hq
  · intro n j β sample Q hcount a
    exact balanced_gram sample j β Q hcount a

end CausalSmith.Stat.GlobalTailDesignRobustCate
