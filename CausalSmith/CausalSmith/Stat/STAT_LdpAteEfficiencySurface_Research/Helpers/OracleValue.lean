module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleEnvelope

/-! # Staircase profile values -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

-- @node: informationObjective_profile_upperSemicontinuous
/-- Under the supplied quantities and conditions, the information objective profile upper semicontinuous assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the information Objective profile upper Semicontinuous](goal).

Under the stated assumptions, the information Objective profile upper Semicontinuous. -/
lemma informationObjective_profile_upperSemicontinuous
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε) :
    UpperSemicontinuousOn
      (fun α : StaircaseWeight =>
        ⨅ t : ℝ, informationObjective θ p ε α t) (feasibleSet ε) := by
  apply upperSemicontinuousOn_ciInf
  · intro α hα
    refine ⟨0, ?_⟩
    rintro u ⟨t, rfl⟩
    exact informationObjective_nonneg_interior θ p ε hp hθ hε α hα t
  · intro t
    exact (informationObjective_continuous_weight θ p ε t).continuousOn.upperSemicontinuousOn

-- @node: informationObjective_profile_exists_maximizer
/-- Under the supplied quantities and conditions, the information objective profile exists maximizer assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the information Objective profile exists maximizer](goal).

Under the stated assumptions, the information Objective profile exists maximizer. -/
lemma informationObjective_profile_exists_maximizer
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε) :
    ∃ α : StaircaseWeight, staircaseFeasible ε α ∧
      ∀ β : StaircaseWeight, staircaseFeasible ε β →
        (⨅ t : ℝ, informationObjective θ p ε β t) ≤
          ⨅ t : ℝ, informationObjective θ p ε α t := by
  obtain ⟨α, hα, hmax⟩ :=
    (informationObjective_profile_upperSemicontinuous θ p ε hp hθ hε).exists_isMaxOn
      (staircaseFeasible_nonempty ε) (staircaseFeasible_compact ε hε)
  exact ⟨α, hα, fun β hβ => hmax hβ⟩

-- @node: Jstar_exists_optimal_weight
/-- Under the supplied quantities and conditions, the jstar exists optimal weight assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the Jstar exists optimal weight](goal).

Under the stated assumptions, the Jstar exists optimal weight. -/
lemma Jstar_exists_optimal_weight (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε) :
    ∃ α : StaircaseWeight, staircaseFeasible ε α ∧
      Jstar θ p ε =
        sInf {u : ℝ | ∃ t : ℝ,
          u = informationObjective θ p ε α t} := by
  obtain ⟨α, hα, hmax⟩ :=
    informationObjective_profile_exists_maximizer θ p ε hp hθ hε
  refine ⟨α, hα, ?_⟩
  have hprofile (β : StaircaseWeight) :
      (⨅ t : ℝ, informationObjective θ p ε β t) =
        sInf {u : ℝ | ∃ t : ℝ,
          u = informationObjective θ p ε β t} := by
    rw [show {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε β t} =
      Set.range (informationObjective θ p ε β) from by ext u; simp [eq_comm]]
    rfl
  apply IsGreatest.csSup_eq
  refine ⟨⟨α, hα, rfl⟩, ?_⟩
  rintro u ⟨β, hβ, rfl⟩
  rw [← hprofile β, ← hprofile α]
  exact hmax β hβ

-- @node: Jstar_pos_interior
/-- Under the supplied quantities and conditions, the jstar pos interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the Jstar pos interior](goal).

Under the stated assumptions, the Jstar pos interior. -/
lemma Jstar_pos_interior (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    0 < Jstar θ p ε := by
  let α : StaircaseWeight := fun s =>
    if s ∈ ({0, 1, 3, 7} : Finset (Fin 14)) then
      1 / (Real.exp ε + 3) else 0
  have hα : staircaseFeasible ε α := staircaseFeasible_singleton_design ε
  obtain ⟨t, ht⟩ := informationObjective_exists_minimizer θ p ε
    hp hθ hε.le α hα
  have hmass (s : Fin 14) : 0 < patternMass θ p ε s :=
    patternMass_pos_interior θ p ε hp hθ hε.le s
  have hterm (s : Fin 14) :
      α s * patternInformation θ p ε s t ≤
        informationObjective θ p ε α t := by
    unfold informationObjective
    apply Finset.single_le_sum (s := Finset.univ) (a := s)
      (fun u hu => ?_) (Finset.mem_univ _)
    exact mul_nonneg (hα.1 u)
      (div_nonneg (sq_nonneg _ ) (hmass u).le)
  have h0 : 0 < α 0 * ((privacyIncrement ε * controlProb p) ^ 2 /
      patternMass θ p ε 0) := by
    have hd := privacyIncrement_pos hε
    have hq : 0 < controlProb p := by dsimp [controlProb]; linarith [hp.2]
    have hm := hmass 0
    dsimp [α]
    positivity
  have h7form : patternInformation θ p ε 7 t =
      ((privacyIncrement ε * p) ^ 2 / patternMass θ p ε 7) * (t + 1) ^ 2 := by
    simp +decide [patternInformation, projectedGradient, patternGradient,
      direction, Fin.sum_univ_succ]
    ring
  have h7 : 0 < α 7 * ((privacyIncrement ε * p) ^ 2 /
      patternMass θ p ε 7) := by
    have hd := privacyIncrement_pos hε
    have hm := hmass 7
    have hp0 := hp.1
    dsimp [α]
    positivity
  have hvalue : 0 < informationObjective θ p ε α t := by
    have hnonneg := informationObjective_nonneg_interior θ p ε hp hθ hε.le α hα t
    by_contra hn
    have hz : informationObjective θ p ε α t = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hterm0 := hterm 0
    have hterm7 := hterm 7
    rw [first_pattern_information_quadratic, hz] at hterm0
    rw [h7form, hz] at hterm7
    have ht0 : t = 0 := by
      by_contra htne
      nlinarith [mul_pos h0 (sq_pos_of_ne_zero htne)]
    have ht7 : t + 1 = 0 := by
      by_contra htne
      nlinarith [mul_pos h7 (sq_pos_of_ne_zero htne)]
    linarith
  have hleast :
      sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε α v} =
        informationObjective θ p ε α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro u ⟨v, rfl⟩; exact ht v⟩
  have hbound : informationObjective θ p ε α t ≤ Jstar θ p ε := by
    obtain ⟨γ, hγ, hmax⟩ :=
      informationObjective_profile_exists_maximizer θ p ε hp hθ hε.le
    have hprofile (β : StaircaseWeight) :
        (⨅ v : ℝ, informationObjective θ p ε β v) =
          sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε β v} := by
      rw [show {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε β v} =
        Set.range (informationObjective θ p ε β) from by ext u; simp [eq_comm]]
      rfl
    rw [Jstar, ← hleast]
    apply le_csSup
    · refine ⟨sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε γ v}, ?_⟩
      rintro u ⟨β, hβ, rfl⟩
      rw [← hprofile β, ← hprofile γ]
      exact hmax β hβ
    · exact ⟨α, hα, rfl⟩
  exact lt_of_lt_of_le hvalue hbound

-- @node: Jstar_eq_envelope_of_stationary_maximizer
/-- Under the supplied quantities and conditions, the jstar eq envelope of stationary maximizer assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα,hmax,hstationary), [the Jstar eq envelope of stationary maximizer](goal).

Under the stated assumptions, the Jstar eq envelope of stationary maximizer. -/
lemma Jstar_eq_envelope_of_stationary_maximizer
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (t : ℝ)
    (hmax : ∀ β : StaircaseWeight, staircaseFeasible ε β →
      informationObjective θ p ε β t ≤ informationObjective θ p ε α t)
    (hstationary : (∑ s : Fin 14,
      2 * α s * projectedGradient p ε s t *
        (patternGradient p ε s 0 + patternGradient p ε s 1) /
          patternMass θ p ε s) = 0) :
    Jstar θ p ε =
      sInf {u : ℝ | ∃ v : ℝ, u = upperEnvelope θ p ε v} := by
  have hleast : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε α v} =
      informationObjective θ p ε α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by
      rintro u ⟨v, rfl⟩
      exact informationObjective_min_of_stationary θ p ε hp hθ hε α hα t
        hstationary v⟩
  have hbound : informationObjective θ p ε α t ≤ Jstar θ p ε := by
    obtain ⟨γ, hγ, hγmax⟩ :=
      informationObjective_profile_exists_maximizer θ p ε hp hθ hε
    have hprofile (β : StaircaseWeight) :
        (⨅ v : ℝ, informationObjective θ p ε β v) =
          sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε β v} := by
      rw [show {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε β v} =
        Set.range (informationObjective θ p ε β) from by ext u; simp [eq_comm]]
      rfl
    rw [Jstar, ← hleast]
    apply le_csSup
    · refine ⟨sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε γ v}, ?_⟩
      rintro u ⟨β, hβ, rfl⟩
      rw [← hprofile β, ← hprofile γ]
      exact hγmax β hβ
    · exact ⟨α, hα, rfl⟩
  have henvelope : upperEnvelope θ p ε t =
      informationObjective θ p ε α t := by
    unfold upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨α, hα, rfl⟩, by
      rintro u ⟨β, hβ, rfl⟩
      exact hmax β hβ⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨upperEnvelope θ p ε 0, 0, rfl⟩
    · rintro u ⟨v, rfl⟩
      exact Jstar_le_upperEnvelope θ p ε hp hθ hε v
  · have hlow : BddBelow {u : ℝ | ∃ v : ℝ,
        u = upperEnvelope θ p ε v} := by
        refine ⟨0, ?_⟩
        rintro u ⟨v, rfl⟩
        obtain ⟨β, hβ, hβmax⟩ :=
          informationObjective_exists_maximizer θ p ε v hε
        have heq : upperEnvelope θ p ε v =
            informationObjective θ p ε β v := by
          unfold upperEnvelope
          apply IsGreatest.csSup_eq
          exact ⟨⟨β, hβ, rfl⟩, by
            rintro w ⟨δ, hδ, rfl⟩
            exact hβmax δ hδ⟩
        rw [heq]
        exact informationObjective_nonneg_interior θ p ε hp hθ hε β hβ v
    exact (csInf_le hlow ⟨t, rfl⟩).trans (henvelope.trans_le hbound)


end CausalSmith.Stat.LdpAteEfficiencySurface
