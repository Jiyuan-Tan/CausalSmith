module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Regions
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleValue

/-! # Consequences of a strict staircase dual certificate

These lemmas isolate the finite duality step used by the certified support
regions.  Equality in the certificate bound forces every inactive staircase
weight to vanish.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

-- @node: feasible_dualRay_sum_general
/-- the feasible dual ray sum general assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the feasible dual Ray sum general](goal).

Under the stated assumptions, the feasible dual Ray sum general. -/
lemma feasible_dualRay_sum_general (ε : ℝ) (α : StaircaseWeight)
    (hα : staircaseFeasible ε α) (η : Fin 4 → ℝ) :
    (∑ s : Fin 14, α s * dualRay ε η s) = ∑ j : Fin 4, η j := by
  simp only [dualRay, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  change (∑ j : Fin 4, staircaseMatrix ε α j * η j) = ∑ j : Fin 4, η j
  simp only [hα.2, one_mul]

-- @node: certificate_dual_upper_bound
/-- Under the supplied quantities and conditions, the certificate dual upper bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hactive,hinactive,hβ), [the certificate dual upper bound](goal).

Under the stated assumptions, the certificate dual upper bound. -/
lemma certificate_dual_upper_bound (θ : TrialParameter) (p ε t : ℝ)
    (K : Finset (Fin 14)) (η : Fin 4 → ℝ)
    (hactive : ∀ s ∈ K,
      dualRay ε η s = patternInformation θ p ε s t)
    (hinactive : ∀ s ∉ K,
      patternInformation θ p ε s t < dualRay ε η s)
    (β : StaircaseWeight) (hβ : staircaseFeasible ε β) :
    informationObjective θ p ε β t ≤ ∑ j : Fin 4, η j := by
  calc
    informationObjective θ p ε β t =
        ∑ s : Fin 14, β s * patternInformation θ p ε s t := rfl
    _ ≤ ∑ s : Fin 14, β s * dualRay ε η s := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hβ.1 s)
      by_cases hs : s ∈ K
      · exact le_of_eq (hactive s hs).symm
      · exact le_of_lt (hinactive s hs)
    _ = ∑ j : Fin 4, η j := feasible_dualRay_sum_general ε β hβ η

-- @node: certificate_equality_forces_inactive_zero
/-- Under the supplied quantities and conditions, the certificate equality forces inactive zero assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hactive,hinactive,hβ,heq), [the certificate equality forces inactive zero](goal).

Under the stated assumptions, the certificate equality forces inactive zero. -/
lemma certificate_equality_forces_inactive_zero
    (θ : TrialParameter) (p ε t : ℝ)
    (K : Finset (Fin 14)) (η : Fin 4 → ℝ)
    (hactive : ∀ s ∈ K,
      dualRay ε η s = patternInformation θ p ε s t)
    (hinactive : ∀ s ∉ K,
      patternInformation θ p ε s t < dualRay ε η s)
    (β : StaircaseWeight) (hβ : staircaseFeasible ε β)
    (heq : informationObjective θ p ε β t = ∑ j : Fin 4, η j) :
    ∀ s ∉ K, β s = 0 := by
  have hsum :
      (∑ s : Fin 14, β s * patternInformation θ p ε s t) =
        ∑ s : Fin 14, β s * dualRay ε η s := by
    calc
      _ = informationObjective θ p ε β t := rfl
      _ = ∑ j : Fin 4, η j := heq
      _ = _ := (feasible_dualRay_sum_general ε β hβ η).symm
  have hterm (s : Fin 14) :
      β s * patternInformation θ p ε s t ≤ β s * dualRay ε η s := by
    apply mul_le_mul_of_nonneg_left _ (hβ.1 s)
    by_cases hs : s ∈ K
    · exact le_of_eq (hactive s hs).symm
    · exact le_of_lt (hinactive s hs)
  have hterm_eq (s : Fin 14) :
      β s * patternInformation θ p ε s t = β s * dualRay ε η s :=
    (Finset.sum_eq_sum_iff_of_le (fun s _ ↦ hterm s)).mp hsum s
      (Finset.mem_univ s)
  intro s hs
  have hstrict := hinactive s hs
  have hnonneg := hβ.1 s
  have he := hterm_eq s
  nlinarith

-- @node: strictCertificate_profile_optimal_and_rigid
/-- Under the supplied quantities and conditions, the strict certificate profile optimal and rigid assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα,hsupport,hstationary,hactive,hinactive), [the strict Certificate profile optimal and rigid](goal).

Under the stated assumptions, the strict Certificate profile optimal and rigid. -/
lemma strictCertificate_profile_optimal_and_rigid
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (K : Finset (Fin 14)) (α : StaircaseWeight) (t : ℝ)
    (η : Fin 4 → ℝ) (hα : staircaseFeasible ε α)
    (hsupport : activeSupport α K)
    (hstationary : ∑ s : Fin 14,
      α s * patternInformationSlope θ p ε s t = 0)
    (hactive : ∀ s ∈ K,
      dualRay ε η s = patternInformation θ p ε s t)
    (hinactive : ∀ s ∉ K,
      patternInformation θ p ε s t < dualRay ε η s) :
    Jstar θ p ε =
        sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε α v} ∧
      ∀ β : StaircaseWeight, staircaseFeasible ε β →
        Jstar θ p ε =
          sInf {u : ℝ | ∃ v : ℝ,
            u = informationObjective θ p ε β v} →
        ∀ s ∉ K, β s = 0 := by
  have hstat : ∑ s : Fin 14,
      2 * α s * projectedGradient p ε s t *
        (patternGradient p ε s 0 + patternGradient p ε s 1) /
          patternMass θ p ε s = 0 := by
    rw [← hstationary]
    apply Finset.sum_congr rfl
    intro s _
    simp only [patternInformationSlope]
    ring
  have hmin (u : ℝ) :
      informationObjective θ p ε α t ≤ informationObjective θ p ε α u :=
    informationObjective_min_of_stationary θ p ε hp hθ hε α hα t hstat u
  have hprofile :
      sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε α v} =
        informationObjective θ p ε α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro u ⟨v, rfl⟩; exact hmin v⟩
  have hvalue : informationObjective θ p ε α t = ∑ j : Fin 4, η j := by
    calc
      informationObjective θ p ε α t =
          ∑ s : Fin 14, α s * patternInformation θ p ε s t := rfl
      _ = ∑ s : Fin 14, α s * dualRay ε η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ K
        · rw [hactive s hs]
        · have hz : α s = 0 := by
            by_contra hn
            exact hs ((hsupport s).mp hn)
          simp [hz]
      _ = ∑ j : Fin 4, η j :=
        feasible_dualRay_sum_general ε α hα η
  have hJ : Jstar θ p ε =
      sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε α v} := by
    unfold Jstar
    apply IsGreatest.csSup_eq
    refine ⟨⟨α, hα, rfl⟩, ?_⟩
    rintro u ⟨β, hβ, rfl⟩
    have hbelow : BddBelow {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε β v} := by
      refine ⟨0, ?_⟩
      rintro u ⟨v, rfl⟩
      exact informationObjective_nonneg_interior θ p ε hp hθ hε β hβ v
    calc
      sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε β v} ≤
          informationObjective θ p ε β t := csInf_le hbelow ⟨t, rfl⟩
      _ ≤ ∑ j : Fin 4, η j :=
        certificate_dual_upper_bound θ p ε t K η hactive hinactive β hβ
      _ = informationObjective θ p ε α t := hvalue.symm
      _ = sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε α v} := hprofile.symm
  refine ⟨hJ, ?_⟩
  intro β hβ hβopt
  have hbelow : BddBelow {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε β v} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, rfl⟩
    exact informationObjective_nonneg_interior θ p ε hp hθ hε β hβ v
  have hβeq : informationObjective θ p ε β t = ∑ j : Fin 4, η j := by
    apply le_antisymm
    · exact certificate_dual_upper_bound θ p ε t K η hactive hinactive β hβ
    · rw [← hvalue, ← hprofile, ← hJ, hβopt]
      exact csInf_le hbelow ⟨t, rfl⟩
  exact certificate_equality_forces_inactive_zero θ p ε t K η hactive
    hinactive β hβ hβeq

-- @node: r5Certificate_profile_optimal_and_rigid
/-- Under [the supplied quantities and conditions](hyp:p), [the r5 certificate profile optimal and rigid assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r5Certificate_profile_optimal_and_rigid
    (p μ0 μ1 ε : ℝ) (hx : (p, μ0, μ1, ε) ∈ R5) :
    let θ : TrialParameter := fun k ↦ if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight,
      staircaseFeasible ε α ∧
      activeSupport α ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
      (∀ s ∈ ({2, 3, 5, 7, 8} : Finset (Fin 14)), 0 < α s) ∧
      Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε α v} ∧
      ∀ β : StaircaseWeight, staircaseFeasible ε β →
        Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε β v} →
        ∀ s ∉ ({2, 3, 5, 7, 8} : Finset (Fin 14)), β s = 0 := by
  dsimp only
  change 0 < p ∧ p < 1 ∧
      0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧
      ∃ α : StaircaseWeight, ∃ t : ℝ, ∃ η : Fin 4 → ℝ,
        staircaseFeasible ε α ∧
        activeSupport α ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
        (∀ s ∈ ({2, 3, 5, 7, 8} : Finset (Fin 14)), 0 < α s) ∧
        (∑ s : Fin 14, α s *
          patternInformationSlope (fun k ↦ if k = 0 then μ0 else μ1)
            p ε s t) = 0 ∧
        (∀ s ∈ ({2, 3, 5, 7, 8} : Finset (Fin 14)),
          dualRay ε η s =
            patternInformation (fun k ↦ if k = 0 then μ0 else μ1) p ε s t) ∧
        (∀ s ∉ ({2, 3, 5, 7, 8} : Finset (Fin 14)),
          patternInformation (fun k ↦ if k = 0 then μ0 else μ1) p ε s t <
            dualRay ε η s) ∧
        (true → ∀ s ∈ ({2, 3, 5, 7, 8} : Finset (Fin 14)),
          ∀ u ∈ ({2, 3, 5, 7, 8} : Finset (Fin 14)), s ≠ u →
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
    ({2, 3, 5, 7, 8} : Finset (Fin 14)) α t η hα hsupp hstat
    hactive hinactive
  exact ⟨α, hα, hsupp, hpos, hopt, hrigid⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
