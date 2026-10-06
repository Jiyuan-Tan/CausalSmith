module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Regions
public import Causalean.Mathlib.Optimization.FiniteSupport

/-! # Sparse stationary staircase saddles

The finite linear-program support theorem is applied at an attained minimizer
of the upper envelope.  It preserves the four normalization moments, the
stationarity moment, and the information value, leaving at most five active
staircase rays.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

open Causalean.Mathlib.Optimization

/-- Under the supplied quantities and conditions, the exists sparse staircase saddle assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the exists sparse staircase saddle](goal).

Under the stated assumptions, the exists sparse staircase saddle. -/
lemma exists_sparse_staircase_saddle (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ∃ α : StaircaseWeight,
      staircaseFeasible ε α ∧
      Jstar θ p ε =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε α t} ∧
      (weightSupport α).card ≤ 5 := by
  obtain ⟨t, ht⟩ := upperEnvelope_exists_minimizer θ p ε hp hθ hε
  have hleast :
      sInf {u : ℝ | ∃ v : ℝ, u = upperEnvelope θ p ε v} =
        upperEnvelope θ p ε t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact ht u⟩
  have hJ : upperEnvelope θ p ε t = Jstar θ p ε := by
    rw [← hleast, ← finiteOracle_minimax θ p ε hp hθ hε]
  obtain ⟨x, hx, hxopt⟩ :=
    Jstar_exists_optimal_weight θ p ε hp hθ hε.le
  have hxbdd : BddBelow {v : ℝ | ∃ w : ℝ,
      v = informationObjective θ p ε x w} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact informationObjective_nonneg_interior θ p ε hp hθ hε.le x hx u
  have hxlower (u : ℝ) : Jstar θ p ε ≤ informationObjective θ p ε x u := by
    rw [hxopt]
    exact csInf_le hxbdd ⟨u, rfl⟩
  obtain ⟨zmax, hzmax, hzmaximal⟩ :=
    informationObjective_exists_maximizer θ p ε t hε.le
  have hzenvelope : upperEnvelope θ p ε t =
      informationObjective θ p ε zmax t := by
    unfold upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨zmax, hzmax, rfl⟩, by
      rintro _ ⟨z, hz, rfl⟩
      exact hzmaximal z hz⟩
  have hxvalue : informationObjective θ p ε x t = Jstar θ p ε := by
    apply le_antisymm
    · exact (hzmaximal x hx).trans (by rw [← hzenvelope, hJ])
    · exact hxlower t
  have hxmax : ∀ z : StaircaseWeight, (∀ s, 0 ≤ z s) →
      (∀ j, moment (patternRay ε · j) z = 1) →
      moment (patternInformation θ p ε · t) z ≤
        moment (patternInformation θ p ε · t) x := by
    intro z hz hzmom
    have hzfeas : staircaseFeasible ε z := by
      refine ⟨hz, ?_⟩
      intro j
      simpa [moment, staircaseMatrix, mul_comm] using hzmom j
    have hzx := hzmaximal z hzfeas
    rw [← hzenvelope, hJ, ← hxvalue] at hzx
    simpa [moment, informationObjective, mul_comm] using hzx
  have hmoment_slope (a : StaircaseWeight) :
      moment (patternInformationSlope θ p ε · t) a =
        ∑ s : Fin 14, 2 * a s * projectedGradient p ε s t *
          (patternGradient p ε s 0 + patternGradient p ε s 1) /
            patternMass θ p ε s := by
    unfold moment patternInformationSlope
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hxstationary : moment (patternInformationSlope θ p ε · t) x = 0 := by
    have hraw := informationObjective_stationary_of_min θ p ε x t (by
      intro u
      rw [hxvalue]
      exact hxlower u)
    rw [hmoment_slope]
    exact hraw
  obtain ⟨y, hy, hymom, hystat, hyvalue, hycard, _⟩ :=
    exists_sparse_maximizer
      (fun j s => patternRay ε s j) (fun _ => 1)
      (fun s => patternInformationSlope θ p ε s t)
      (fun s => patternInformation θ p ε s t) x hx.1
      (by
        intro j
        simpa [moment, staircaseMatrix, mul_comm] using hx.2 j)
      hxmax
  have hyfeas : staircaseFeasible ε y := by
    refine ⟨hy, ?_⟩
    intro j
    simpa [moment, staircaseMatrix, mul_comm] using hymom j
  have hystationary :
      ∑ s : Fin 14, 2 * y s * projectedGradient p ε s t *
          (patternGradient p ε s 0 + patternGradient p ε s 1) /
            patternMass θ p ε s = 0 := by
    calc
      _ = moment (patternInformationSlope θ p ε · t) y :=
        (hmoment_slope y).symm
      _ = moment (patternInformationSlope θ p ε · t) x := hystat
      _ = 0 := hxstationary
  have hymin := informationObjective_min_of_stationary θ p ε hp hθ hε.le
    y hyfeas t hystationary
  have hyat : informationObjective θ p ε y t = Jstar θ p ε := by
    calc
      informationObjective θ p ε y t =
          moment (patternInformation θ p ε · t) y := by
            simp [informationObjective, moment, mul_comm]
      _ = moment (patternInformation θ p ε · t) x := hyvalue
      _ = informationObjective θ p ε x t := by
            simp [informationObjective, moment, mul_comm]
      _ = Jstar θ p ε := hxvalue
  refine ⟨y, hyfeas, ?_, ?_⟩
  · rw [← hyat]
    symm
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hymin u⟩
  · norm_num at hycard ⊢
    exact hycard

end CausalSmith.Stat.LdpAteEfficiencySurface
