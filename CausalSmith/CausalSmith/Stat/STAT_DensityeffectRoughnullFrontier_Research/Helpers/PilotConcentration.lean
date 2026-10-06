module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotPropensityBernstein

/-!
Uniform pilot concentration assembly, with deterministic clipping and normalized
density and propensity Bernstein adapters supplied by the pilot helper chain.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The explicit public pilot constant bounds bad training under the actual sampling law. -/
-- @node: pilot_concentration_public_tail
lemma pilot_concentration_public_tail (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω | ¬GoodPilot P (foldData (13 * m) ω.1 0) (2 ^ 16) mx my} ≤
      zetaAllow m mx my := by
  apply le_trans (pilot_good_sampling_tail_le_count_budget P hModel m mx my hm hmx hmy
    ν hSampling)
  have hp := pilot_propensity_sampling_tail_le P hModel m mx my hm hmx hmy ν hSampling
  rw [zetaAllow, if_neg (by omega)]
  calc
    _ ≤ 2 * (mx : ℝ) * Real.exp (-(m : ℝ) / (32 * mx)) +
        2 * (mx : ℝ) * (m : ℝ) ^ (-30 : ℤ) +
        4 * (mx : ℝ) * my * (m : ℝ) ^ (-30 : ℤ) :=
      add_le_add (add_le_add le_rfl hp) le_rfl
    _ = _ := by ring

-- @node: lem:pilot-concentration
/-- The paper's public pilot constant controls the bad-training probability uniformly;
every realization obeys the deterministic clipping and normalization envelopes. -/
lemma pilot_concentration :
    ∃ C0 : ℝ, 0 < C0 ∧ -- @realizes C0(universal positive pilot constant)
    (∀ m, 3 ≤ m → ∀ P : ObsLaw, Model P → ∀ mx my,
        Dyadic mx → Dyadic my → mx ≤ m →
        ∀ ν : Measure (SampleSpace (13 * m)), SamplingLaw P (13 * m) ν →
        ν.real {ω | ¬GoodPilot P (foldData (13 * m) ω.1 0) C0 mx my} ≤
          zetaAllow m mx my) ∧
    (∀ m mx my, Dyadic mx → Dyadic my →
      (∀ train : Fin m → Omega, ∀ a x, x ∈ Set.Icc 0 1 →
        pilotPi train mx a x ∈ Set.Icc (1 / 4) (3 / 4)) ∧
      (∀ train : Fin m → Omega, ∀ a x y,
        x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        densityPilot train mx my a x y ∈ Set.Icc (1 / 64) 64)) := by
  refine ⟨2 ^ 16, by positivity, ?_⟩
  constructor
  · intro m hm P hModel mx my hmx hmy hmxm ν hSampling
    by_cases hh : 64 ≤ hAllow (2 ^ 16) m mx my
    · have hempty : {ω : SampleSpace (13 * m) |
          ¬GoodPilot P (foldData (13 * m) ω.1 0) (2 ^ 16) mx my} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro ω hbad
        exact hbad (goodPilot_of_large_allowance P hModel _ _ mx my
          (by simpa [roleSize] using hh))
      rw [hempty, measureReal_empty]
      exact zetaAllow_nonneg m mx my
    · have hmxpos : 0 < mx := by
        obtain ⟨l, rfl⟩ := hmx
        exact Nat.pow_pos (by omega)
      have hmypos : 0 < my := by
        obtain ⟨l, rfl⟩ := hmy
        exact Nat.pow_pos (by omega)
      apply le_trans (pilot_good_sampling_tail_le_count_budget P hModel m mx my hm hmxpos hmypos
        ν hSampling)
      have hp := pilot_propensity_sampling_tail_le P hModel m mx my hm hmxpos hmypos ν hSampling
      rw [zetaAllow, if_neg (by omega)]
      calc
        _ ≤ 2 * (mx : ℝ) * Real.exp (-(m : ℝ) / (32 * mx)) +
            2 * (mx : ℝ) * (m : ℝ) ^ (-30 : ℤ) +
            4 * (mx : ℝ) * my * (m : ℝ) ^ (-30 : ℤ) :=
          add_le_add (add_le_add le_rfl hp) le_rfl
        _ = _ := by ring
  · intro m mx my _hmx _hmy
    constructor
    · intro train a x _hx
      exact pilotPi_mem_Icc train mx a x
    · intro train a x y _hx _hy
      exact densityPilot_mem_Icc train mx my a x y

end CausalSmith.Stat.DensityEffectRoughNull
