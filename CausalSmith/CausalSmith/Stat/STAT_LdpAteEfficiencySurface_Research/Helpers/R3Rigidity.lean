module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CertificateRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.RegionOpenness

/-! # Rigidity of the three-ray certificate

The strict certificate confines every optimal staircase design to the three
active masks.  At privacy level `log 3`, normalization then fixes all three
weights to `1/5`.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

-- @node: r3Certificate_profile_optimal_and_rigid
/-- Under [the supplied quantities and conditions](hyp:p), [the r3 certificate profile optimal and rigid assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r3Certificate_profile_optimal_and_rigid
    (p μ0 μ1 ε : ℝ) (hx : (p, μ0, μ1, ε) ∈ R3) :
    let θ : TrialParameter := fun k ↦ if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight,
      staircaseFeasible ε α ∧
      activeSupport α ({0, 5, 7} : Finset (Fin 14)) ∧
      (∀ s ∈ ({0, 5, 7} : Finset (Fin 14)), 0 < α s) ∧
      Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε α v} ∧
      ∀ β : StaircaseWeight, staircaseFeasible ε β →
        Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε β v} →
        ∀ s ∉ ({0, 5, 7} : Finset (Fin 14)), β s = 0 := by
  dsimp only
  change 0 < p ∧ p < 1 ∧
      0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧
      ∃ α : StaircaseWeight, ∃ t : ℝ, ∃ η : Fin 4 → ℝ,
        staircaseFeasible ε α ∧
        activeSupport α ({0, 5, 7} : Finset (Fin 14)) ∧
        (∀ s ∈ ({0, 5, 7} : Finset (Fin 14)), 0 < α s) ∧
        (∑ s : Fin 14, α s *
          patternInformationSlope (fun k ↦ if k = 0 then μ0 else μ1)
            p ε s t) = 0 ∧
        (∀ s ∈ ({0, 5, 7} : Finset (Fin 14)),
          dualRay ε η s =
            patternInformation (fun k ↦ if k = 0 then μ0 else μ1) p ε s t) ∧
        (∀ s ∉ ({0, 5, 7} : Finset (Fin 14)),
          patternInformation (fun k ↦ if k = 0 then μ0 else μ1) p ε s t <
            dualRay ε η s) ∧
        (false → ∀ s ∈ ({0, 5, 7} : Finset (Fin 14)),
          ∀ u ∈ ({0, 5, 7} : Finset (Fin 14)), s ≠ u →
            projectedScore (fun k ↦ if k = 0 then μ0 else μ1) p ε s t ≠
              projectedScore (fun k ↦ if k = 0 then μ0 else μ1) p ε u t) at hx
  rcases hx with ⟨hp0, hp1, hμ0, hμ0', hμ1, hμ1', hε,
    α, t, η, hα, hsupp, hpos, hstat, hactive, hinactive, _⟩
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans (fun k ↦ if k = 0 then μ0 else μ1) := by
    change 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1
    exact ⟨hμ0, hμ0', hμ1, hμ1'⟩
  obtain ⟨hopt, hrigid⟩ := strictCertificate_profile_optimal_and_rigid
    (fun k ↦ if k = 0 then μ0 else μ1) p ε hp hθ hε.le
    ({0, 5, 7} : Finset (Fin 14)) α t η hα hsupp hstat hactive hinactive
  exact ⟨α, hα, hsupp, hpos, hopt, hrigid⟩

-- @node: r3_feasible_eq_canonical
/-- the r3 feasible eq canonical assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hβ,hout), [the r3 feasible eq canonical](goal).

Under the stated assumptions, the r3 feasible eq canonical. -/
lemma r3_feasible_eq_canonical (β : StaircaseWeight)
    (hβ : staircaseFeasible (Real.log 3) β)
    (hout : ∀ s ∉ ({0, 5, 7} : Finset (Fin 14)), β s = 0) :
    β = fun s ↦ if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0 := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have h0 := hβ.2 0
  have h1 := hβ.2 1
  have h2 := hβ.2 2
  have h3 := hβ.2 3
  simp +decide [staircaseMatrix, patternRay, patternContains,
    privacyIncrement, privacyRatio, he, Fin.sum_univ_succ, hout] at h0 h1 h2 h3
  funext s
  by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
  · have hs' : s = 0 ∨ s = 5 ∨ s = 7 := by simpa using hs
    rcases hs' with rfl | rfl | rfl <;> simp +decide <;> linarith
  · rw [hout s hs]
    simp [hs]

-- @node: r3Certificate_unique_optimum_log3
/-- Under [the supplied quantities and conditions](hyp:p), [the r3 certificate unique optimum log3 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r3Certificate_unique_optimum_log3
    (p μ0 μ1 : ℝ) (hx : (p, μ0, μ1, Real.log 3) ∈ R3) :
    let θ : TrialParameter := fun k ↦ if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight,
      staircaseFeasible (Real.log 3) α ∧
      activeSupport α ({0, 5, 7} : Finset (Fin 14)) ∧
      Jstar θ p (Real.log 3) = sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p (Real.log 3) α v} ∧
      ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
        Jstar θ p (Real.log 3) = sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p (Real.log 3) β v} →
        β = α := by
  dsimp only
  obtain ⟨α, hα, hsupp, _, hopt, hrigid⟩ :=
    r3Certificate_profile_optimal_and_rigid p μ0 μ1 (Real.log 3) hx
  have houtα : ∀ s ∉ ({0, 5, 7} : Finset (Fin 14)), α s = 0 := by
    intro s hs
    by_contra hn
    exact hs ((hsupp s).mp hn)
  have hαcanonical := r3_feasible_eq_canonical α hα houtα
  refine ⟨α, hα, hsupp, hopt, ?_⟩
  intro β hβ hβopt
  have hβcanonical := r3_feasible_eq_canonical β hβ (hrigid β hβ hβopt)
  exact hβcanonical.trans hαcanonical.symm

end CausalSmith.Stat.LdpAteEfficiencySurface
