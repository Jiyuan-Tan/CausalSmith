module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CenteredR5Certificate
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.AttainmentRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CertificateRigidity

/-! # Centered five-ray profile rigidity -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 profile optimal unique assertion](goal) holds. -/
lemma centeredR5_profile_optimal_unique (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    staircaseFeasible (Real.log 3) (centeredR5Weight p) ∧
    Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
      sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
        (fun _ => (1 / 2 : ℝ)) p (Real.log 3) (centeredR5Weight p) t} ∧
    ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
      Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
          (fun _ => (1 / 2 : ℝ)) p (Real.log 3) β t} →
      β = centeredR5Weight p := by
  let θ : TrialParameter := fun _ => (1 / 2 : ℝ)
  let α := centeredR5Weight p
  let t := centeredR5Direction p
  let η := centeredR5Dual p
  have hp : InteriorAssignment p := ⟨hp0, by linarith⟩
  have hθ : InteriorMeans θ := by
    dsimp [θ, InteriorMeans]
    norm_num
  have hε : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hα : staircaseFeasible (Real.log 3) α := centeredR5Weight_feasible p hp0 hp1
  have hsupp : activeSupport α r5Active := (centeredR5Weight_active p hp0 hp1).1
  have hstat : ∑ s : Fin 14, α s * patternInformationSlope θ p
      (Real.log 3) s t = 0 := by
    simpa [θ, α, t] using centeredR5Weight_stationary p hp0 hp1
  have hactive : ∀ s ∈ r5Active,
      dualRay (Real.log 3) η s = patternInformation θ p (Real.log 3) s t := by
    intro s hs
    simpa [θ, η, t] using centeredR5_active_dual_equalities p hp0 hp1 s hs
  have hinactive : ∀ s ∉ r5Active,
      patternInformation θ p (Real.log 3) s t < dualRay (Real.log 3) η s := by
    intro s hs
    simpa [θ, η, t] using centeredR5_inactive_dual_slacks p hp0 hp1 s hs
  obtain ⟨hopt, hrigid⟩ := strictCertificate_profile_optimal_and_rigid
    θ p (Real.log 3) hp hθ hε r5Active α t η hα hsupp hstat hactive hinactive
  refine ⟨hα, hopt, ?_⟩
  intro β hβ hβopt
  have hout := hrigid β hβ hβopt
  have hbelow : BddBelow {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p (Real.log 3) β v} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, rfl⟩
    exact informationObjective_nonneg_interior θ p (Real.log 3) hp hθ hε β hβ v
  have hvalue : informationObjective θ p (Real.log 3) α t = ∑ j : Fin 4, η j := by
    calc
      _ = ∑ s : Fin 14, α s * dualRay (Real.log 3) η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ r5Active
        · rw [hactive s hs]
        · have hz : α s = 0 := by
            by_contra hn
            exact hs ((hsupp s).mp hn)
          simp [hz]
      _ = _ := feasible_dualRay_sum_general (Real.log 3) α hα η
  have hprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p (Real.log 3) α v} =
      informationObjective θ p (Real.log 3) α t := by
    apply IsLeast.csInf_eq
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro _ ⟨v, rfl⟩
    have hslope := centeredR5Weight_stationary p hp0 hp1
    exact informationObjective_min_of_stationary θ p (Real.log 3) hp hθ hε α hα t
      (by
        rw [← hslope]
        apply Finset.sum_congr rfl
        intro s _
        simp [θ, α, t, patternInformationSlope]
        ring) v
  have hβat : informationObjective θ p (Real.log 3) β t =
      Jstar θ p (Real.log 3) := by
    apply le_antisymm
    · calc
        _ ≤ ∑ j : Fin 4, η j :=
          certificate_dual_upper_bound θ p (Real.log 3) t r5Active η
            hactive hinactive β hβ
        _ = _ := by rw [← hvalue, ← hprofile, ← hopt]
    · rw [hβopt]
      exact csInf_le hbelow ⟨t, rfl⟩
  have hmin (u : ℝ) : informationObjective θ p (Real.log 3) β t ≤
      informationObjective θ p (Real.log 3) β u := by
    rw [hβat, hβopt]
    exact csInf_le hbelow ⟨u, rfl⟩
  have hraw := informationObjective_stationary_of_min θ p (Real.log 3) β t hmin
  have hslope : ∑ s : Fin 14, β s * patternInformationSlope θ p
      (Real.log 3) s t = 0 := by
    rw [← hraw]
    apply Finset.sum_congr rfl
    intro s _
    simp [patternInformationSlope]
    ring
  exact centeredR5_supported_stationary_eq p hp0 hp1 β hβ
    (by simpa [r5Active] using hout) (by simpa [θ, t] using hslope)

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 output cardinality ge five assertion](goal) holds. For [the displayed quantities and conditions](hyp:Z,Q,hQ,hattain), these specify the stated inputs. -/
lemma centeredR5_outputCardinality_ge_five (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP (Real.log 3) Q)
    (hattain : contrastVariance
      (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) =
        ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3))) :
    5 ≤ outputCardinality (fun _ => (1 / 2 : ℝ)) p Q := by
  let θ : TrialParameter := fun _ => (1 / 2 : ℝ)
  let α0 := centeredR5Weight p
  let t0 := centeredR5Direction p
  let η := centeredR5Dual p
  have hp : InteriorAssignment p := ⟨hp0, by linarith⟩
  have hθ : InteriorMeans θ := by dsimp [θ, InteriorMeans]; norm_num
  have hε : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hα0 : staircaseFeasible (Real.log 3) α0 :=
    centeredR5Weight_feasible p hp0 hp1
  have hsupp0 : activeSupport α0 r5Active :=
    (centeredR5Weight_active p hp0 hp1).1
  have hactive : ∀ s ∈ r5Active,
      dualRay (Real.log 3) η s = patternInformation θ p (Real.log 3) s t0 := by
    intro s hs
    simpa [θ, η, t0] using centeredR5_active_dual_equalities p hp0 hp1 s hs
  have hinactive : ∀ s ∉ r5Active,
      patternInformation θ p (Real.log 3) s t0 < dualRay (Real.log 3) η s := by
    intro s hs
    simpa [θ, η, t0] using centeredR5_inactive_dual_slacks p hp0 hp1 s hs
  have hvalue : informationObjective θ p (Real.log 3) α0 t0 =
      ∑ j : Fin 4, η j := by
    calc
      _ = ∑ s : Fin 14, α0 s * dualRay (Real.log 3) η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ r5Active
        · rw [hactive s hs]
        · have hz : α0 s = 0 := by
            by_contra hn
            exact hs ((hsupp0 s).mp hn)
          simp [hz]
      _ = _ := feasible_dualRay_sum_general (Real.log 3) α0 hα0 η
  obtain ⟨_, hopt, _⟩ := centeredR5_profile_optimal_unique p hp0 hp1
  have hmin0 (u : ℝ) : informationObjective θ p (Real.log 3) α0 t0 ≤
      informationObjective θ p (Real.log 3) α0 u := by
    have hslope := centeredR5Weight_stationary p hp0 hp1
    exact informationObjective_min_of_stationary θ p (Real.log 3) hp hθ hε.le
      α0 hα0 t0 (by
        rw [← hslope]
        apply Finset.sum_congr rfl
        intro s _
        simp [θ, α0, t0, patternInformationSlope]
        ring) u
  have hleast : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p (Real.log 3) α0 v} =
      informationObjective θ p (Real.log 3) α0 t0 := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t0, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hmin0 u⟩
  have hJsum : Jstar θ p (Real.log 3) = ∑ j : Fin 4, η j := by
    rw [hopt, hleast, hvalue]
  have hupper (β : StaircaseWeight) (hβ : staircaseFeasible (Real.log 3) β) :
      informationObjective θ p (Real.log 3) β t0 ≤ Jstar θ p (Real.log 3) := by
    rw [hJsum]
    exact certificate_dual_upper_bound θ p (Real.log 3) t0 r5Active η
      hactive hinactive β hβ
  let epsSeq : ℕ → ℝ := fun _ => Real.log 3
  have hfixed : FixedPrivacy epsSeq (Real.log 3) := ⟨hε, fun _ => rfl⟩
  obtain ⟨β, K, hβ, hK, hfactor, hdiff, hrigid⟩ :=
    staircase_refinement_interior p θ (Real.log 3) hp hθ epsSeq hfixed Q hQ
  have horder (u : ℝ) :
      informationQuadratic (channelFisherInfo θ p Q) (direction u) ≤
        informationQuadratic (informationMatrix θ p (Real.log 3) β) (direction u) := by
    have hn := hdiff.dotProduct_mulVec_nonneg (direction u)
    simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial] at hn ⊢
    linarith
  have hlower (u : ℝ) : Jstar θ p (Real.log 3) ≤
      informationObjective θ p (Real.log 3) β u := by
    calc
      _ ≤ informationQuadratic (channelFisherInfo θ p Q) (direction u) :=
        attainment_forces_direction_lower θ p (Real.log 3) u hp hθ hε Q hQ
          (by simpa [θ] using hattain)
      _ ≤ informationQuadratic (informationMatrix θ p (Real.log 3) β)
          (direction u) := horder u
      _ = informationObjective θ p (Real.log 3) β u := by
        rw [informationObjective_eq_informationQuadratic]
        rfl
  have hβat : informationObjective θ p (Real.log 3) β t0 =
      Jstar θ p (Real.log 3) := le_antisymm (hupper β hβ) (hlower t0)
  have hout : ∀ s ∉ r5Active, β s = 0 :=
    certificate_equality_forces_inactive_zero θ p (Real.log 3) t0 r5Active η
      hactive hinactive β hβ (hβat.trans hJsum)
  have hmin (u : ℝ) : informationObjective θ p (Real.log 3) β t0 ≤
      informationObjective θ p (Real.log 3) β u := by rw [hβat]; exact hlower u
  have hraw := informationObjective_stationary_of_min θ p (Real.log 3) β t0 hmin
  have hslope : ∑ s : Fin 14, β s * patternInformationSlope θ p
      (Real.log 3) s t0 = 0 := by
    rw [← hraw]
    apply Finset.sum_congr rfl
    intro s _
    simp [patternInformationSlope]
    ring
  have hβeq : β = α0 := centeredR5_supported_stationary_eq p hp0 hp1 β hβ
    (by simpa [r5Active] using hout) (by simpa [θ, t0] using hslope)
  have hpos : ∀ s ∈ r5Active, 0 < β s := by
    rw [hβeq]
    exact (centeredR5Weight_active p hp0 hp1).2
  have heq : informationQuadratic (informationMatrix θ p (Real.log 3) β)
      (direction t0) = informationQuadratic (channelFisherInfo θ p Q)
        (direction t0) := by
    have hQlower := attainment_forces_direction_lower θ p (Real.log 3) t0
      hp hθ hε Q hQ (by simpa [θ] using hattain)
    have hβupper : informationQuadratic (informationMatrix θ p (Real.log 3) β)
        (direction t0) ≤ Jstar θ p (Real.log 3) := by
      calc
        _ = informationObjective θ p (Real.log 3) β t0 := by
          rw [informationObjective_eq_informationQuadratic]
          rfl
        _ ≤ _ := hupper β hβ
    exact le_antisymm (hβupper.trans hQlower) (horder t0)
  have hsing : ∀ s ∈ r5Active, ∀ u ∈ r5Active, s ≠ u → K s ⟂ₘ K u := by
    intro s hs u hu hne
    by_contra hn
    have hscore := hrigid t0 heq s u (ne_of_gt (hpos s hs))
      (ne_of_gt (hpos u hu)) hn
    exact centeredR5_active_scores_pairwise_ne p hp0 hp1 s hs u hu hne
      (by simpa [θ, t0] using hscore)
  have hcard := active_card_le_outputCardinality_of_pairwise_singular
    θ p (Real.log 3) hp hθ r5Active β hpos K hK Q hfactor hsing
  norm_num [r5Active] at hcard ⊢
  simpa [θ] using hcard
end CausalSmith.Stat.LdpAteEfficiencySurface
