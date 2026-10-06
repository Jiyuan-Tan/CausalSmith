module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ProjectedBandRemainders
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.WeightedObservedMeans

/-! Assembly of the exact observed corrected mean and its universal good-pilot bias bound. -/

public section

noncomputable section
open MeasureTheory

namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The corrected-mean bias bound with the exact public multiplier used by the rule. -/
-- @node: corrected_mean_public_constant
lemma corrected_mean_public_constant :
    ∀ C0 : ℝ, 0 < C0 → -- @realizes C0(arbitrary positive public pilot constant)
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my K L T J q kt,
      MeanRanks mx my K L T J q kt → ∀ train : Fin m → Omega,
      ∀ ν : Measure (SampleSpace (13 * m)), SamplingLaw P (13 * m) ν →
      contrastMean P train mx my L T J q kt - coefficients J (delta P) =
        meanRemainder P train mx my L T J q kt ∧
      (GoodPilot P train C0 mx my → hAllow C0 m mx my ≤ 1 →
        ‖contrastMean P train mx my L T J q kt - coefficients J (delta P)‖ ≤
          BAllow (2 ^ 24) (hAllow C0 m mx my) m K L T q kt) := by
  intro C0 hC0 P hModel m hm mx my K L T J q kt hr train ν hν
  rcases hr with ⟨hmx, hmy, hL, hK, hq, hkt, hJ, hmyL, hzero, hdiv, hdivq⟩
  have hmxpos : 0 < mx := by obtain ⟨r, rfl⟩ := hmx; positivity
  have hqpos : 0 < q := by obtain ⟨r, rfl⟩ := hq; positivity
  have hktpos : ∀ t, t ≤ T → 0 < kt t := by
    intro t ht
    obtain ⟨r, hr⟩ := hkt t ht
    rw [hr]
    positivity
  have hid := contrastMean_eq_meanRemainder P hModel (by omega) train mx my L T J q kt
    hJ hqpos hktpos
  refine ⟨hid, ?_⟩
  intro hG hh
  rw [hid]
  subst J
  exact goodPilot_meanRemainder_norm_le P hModel hm train C0 mx my K L T q kt
    hmxpos hqpos hdivq hmy hL hmyL hktpos hdiv hzero hG hh

/-- The exact residual correction identity and the fourth-order good-pilot norm bound,
with a universal constant placed before every law, resolution and training realization. -/
-- @node: lem:corrected-mean
lemma corrected_mean :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(universal positive moment constant)
    ∀ C0 : ℝ, 0 < C0 → -- @realizes C0(arbitrary positive public pilot constant)
    ∀ P : ObsLaw, Model P → ∀ m, 1 ≤ m → ∀ mx my K L T J q kt,
      MeanRanks mx my K L T J q kt → ∀ train : Fin m → Omega,
      ∀ ν : Measure (SampleSpace (13 * m)), SamplingLaw P (13 * m) ν →
      contrastMean P train mx my L T J q kt - coefficients J (delta P) =
        meanRemainder P train mx my L T J q kt ∧
      (GoodPilot P train C0 mx my → hAllow C0 m mx my ≤ 1 →
        ‖contrastMean P train mx my L T J q kt - coefficients J (delta P)‖ ≤
          BAllow C (hAllow C0 m mx my) m K L T q kt) := by
  exact ⟨2 ^ 24, by norm_num, corrected_mean_public_constant⟩

end CausalSmith.Stat.DensityEffectRoughNull
