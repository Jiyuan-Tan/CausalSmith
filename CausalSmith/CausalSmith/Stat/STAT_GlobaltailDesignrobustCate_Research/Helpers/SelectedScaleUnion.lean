module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountAdmissibility

/-! # Finite union over the actual selected levels

The good analysis-scale event forces a nonempty admissible grid and a selected
level no coarser than the analysis level. Summing the actual quadratic outcome
tails retains both factors needed for the log-free scale summation (10).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal BigOperators

/-- Good-event losses decompose over the finite interval of possible selected
levels. The empty-grid fallback never occurs on this event. -/
-- @node: selectorHandle_goodEvent_le_selectedLevel_sum
lemma selectorHandle_goodEvent_le_selectedLevel_sum {d n : ℕ}
    (P : Law d) (β γ C L M : ℝ) (hP : LawClass d β γ C L M P)
    (hn : 0 < n) (j₀ : ℕ) (hgrid : j₀ ≤ selectorMaxLevel d n β)
    (B t : ℝ) (hB : 0 ≤ B) :
    (P.sample n).real {sample | selectorAdmissible sample j₀ β ∧
      ENNReal.ofReal (B * L * (dyadicWidth j₀) ^ β + t) <
        supLoss (selectorHandle sample β M) P.mu1} ≤
      ∑ j ∈ Finset.Icc j₀ (selectorMaxLevel d n β),
        (P.sample n).real {sample |
          (∃ h : (admissibleLevels sample β).Nonempty,
            (admissibleLevels sample β).max' h = j) ∧
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
            supLoss (selectorHandle sample β M) P.mu1} := by
  classical
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hP.iid hP.consistency
  have : IsProbabilityMeasure (P.sample n) := by
    rw [sample_eq_pi_obs P hP.iid hP.consistency hn]
    infer_instance
  apply (measureReal_mono (show _ ⊆ ⋃ j ∈ Finset.Icc j₀ (selectorMaxLevel d n β),
      {sample : Fin n → Obs d |
        (∃ h : (admissibleLevels sample β).Nonempty,
          (admissibleLevels sample β).max' h = j) ∧
        ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
          supLoss (selectorHandle sample β M) P.mu1} from ?_) (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le _ _)
  intro sample hs
  have hmem := (mem_admissibleLevels_iff sample β j₀).mpr ⟨hgrid, hs.1⟩
  have hne : (admissibleLevels sample β).Nonempty := ⟨j₀, hmem⟩
  let j := (admissibleLevels sample β).max' hne
  have hjlo : j₀ ≤ j := (admissibleLevels sample β).le_max' j₀ hmem
  have hjhi : j ≤ selectorMaxLevel d n β := (selectedLevel_admissible sample β hne).1
  refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
    ⟨Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩, ?_⟩⟩
  refine ⟨⟨hne, rfl⟩, lt_of_le_of_lt ?_ hs.2⟩
  apply ENNReal.ofReal_le_ofReal
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hP.parameters.2.2.2.2.1.le)
  exact Real.rpow_le_rpow (by unfold dyadicWidth; positivity)
    (selectedWidth_le_admissibleWidth sample β hne j₀ hgrid hs.1)
    hP.parameters.2.1.le

end CausalSmith.Stat.GlobalTailDesignRobustCate
