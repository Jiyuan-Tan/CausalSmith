module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Regions

/-! # Linear rigidity of the five-ray feasible family -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Classical

/-- the [r5 active](goal) is the mathematical object specified below. -/
def r5Active : Finset (Fin 14) := {2, 3, 5, 7, 8}

/-- The four normalization equations leave exactly the expected one-dimensional family on the five active rays. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hβ,hout), [the r5 supported feasible coordinates](goal).

Under the stated assumptions, the r5 supported feasible coordinates. -/
lemma r5_supported_feasible_coordinates (ε : ℝ) (hε : 0 < ε)
    (β : StaircaseWeight) (hβ : staircaseFeasible ε β)
    (hout : ∀ s ∉ r5Active, β s = 0) :
    β 2 = β 3 ∧ β 3 = β 7 ∧ β 5 = β 8 ∧
      (Real.exp ε + 2) * β 2 + (Real.exp ε + 1) * β 5 = 1 := by
  have h0 := hβ.2 0
  have h1 := hβ.2 1
  have h2 := hβ.2 2
  have h3 := hβ.2 3
  simp +decide [staircaseMatrix, patternRay, patternContains, privacyRatio,
    privacyIncrement, r5Active, hout, Fin.sum_univ_succ] at h0 h1 h2 h3
  have he : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
  have h23 : β 2 = β 3 := by nlinarith
  have h37 : β 3 = β 7 := by nlinarith
  have h58 : β 5 = β 8 := by nlinarith
  refine ⟨h23, h37, h58, ?_⟩
  nlinarith

/-- A single binary-ray coordinate determines a feasible weight supported on the five-ray family. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hβ,hγ,hβout,hγout,hfive), [the r5 supported feasible eq of five eq](goal).

Under the stated assumptions, the r5 supported feasible eq of five eq. -/
lemma r5_supported_feasible_eq_of_five_eq (ε : ℝ) (hε : 0 < ε)
    (β γ : StaircaseWeight) (hβ : staircaseFeasible ε β)
    (hγ : staircaseFeasible ε γ)
    (hβout : ∀ s ∉ r5Active, β s = 0)
    (hγout : ∀ s ∉ r5Active, γ s = 0)
    (hfive : β 5 = γ 5) : β = γ := by
  obtain ⟨hβ23, hβ37, hβ58, hβnorm⟩ :=
    r5_supported_feasible_coordinates ε hε β hβ hβout
  obtain ⟨hγ23, hγ37, hγ58, hγnorm⟩ :=
    r5_supported_feasible_coordinates ε hε γ hγ hγout
  have he : 0 < Real.exp ε + 2 := by positivity
  have htwo : β 2 = γ 2 := by nlinarith
  funext s
  by_cases hs : s ∈ r5Active
  · rcases s with ⟨s, hslt⟩
    interval_cases s <;> simp_all [r5Active]
  · rw [hβout s hs, hγout s hs]

end CausalSmith.Stat.LdpAteEfficiencySurface
