module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.AttainmentRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CertificateRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R5Continuity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound

/-! # General five-ray certificate rigidity -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Every `R5` certificate has a unique optimal staircase weight, including
away from the centered explicit family. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r5Certificate_unique_optimum
    (p μ0 μ1 ε : ℝ) (hx : (p, μ0, μ1, ε) ∈ R5) :
    let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight,
      staircaseFeasible ε α ∧
      activeSupport α r5Active ∧
      (∀ s ∈ r5Active, 0 < α s) ∧
      Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε α v} ∧
      ∀ β : StaircaseWeight, staircaseFeasible ε β →
        Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε β v} →
        β = α := by
  dsimp only
  change 0 < p ∧ p < 1 ∧
      0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧
      ∃ α : StaircaseWeight, ∃ t : ℝ, ∃ η : Fin 4 → ℝ,
        staircaseFeasible ε α ∧ activeSupport α r5Active ∧
        (∀ s ∈ r5Active, 0 < α s) ∧
        (∑ s : Fin 14, α s * patternInformationSlope
          (fun k => if k = 0 then μ0 else μ1) p ε s t) = 0 ∧
        (∀ s ∈ r5Active, dualRay ε η s =
          patternInformation (fun k => if k = 0 then μ0 else μ1) p ε s t) ∧
        (∀ s ∉ r5Active, patternInformation
          (fun k => if k = 0 then μ0 else μ1) p ε s t < dualRay ε η s) ∧
        (true → ∀ s ∈ r5Active, ∀ u ∈ r5Active, s ≠ u →
          projectedScore (fun k => if k = 0 then μ0 else μ1) p ε s t ≠
            projectedScore (fun k => if k = 0 then μ0 else μ1) p ε u t) at hx
  rcases hx with ⟨hp0, hp1, hμ00, hμ01, hμ10, hμ11, hε,
    α, t, η, hα, hsupp, hpos, hstat, hactive, hinactive, _⟩
  let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
  let x : RegionParameter := (p, μ0, μ1, ε)
  have hxθ : regionTheta x = θ := by
    funext k
    fin_cases k <;> rfl
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans θ := by
    change 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1
    exact ⟨hμ00, hμ01, hμ10, hμ11⟩
  have hm (s : Fin 14) : patternMass θ p ε s ≠ 0 :=
    ne_of_gt (patternMass_pos_interior θ p ε hp hθ hε.le s)
  have hαout : ∀ s ∉ r5Active, α s = 0 := by
    intro s hs
    by_contra hn
    exact hs ((hsupp s).mp hn)
  obtain ⟨hopt, hrigid⟩ := strictCertificate_profile_optimal_and_rigid
    θ p ε hp hθ hε.le r5Active α t η hα hsupp hstat hactive hinactive
  have hcoeff : 0 < r5BinaryCoeff x ∧ 0 < r5TernaryCoeff x :=
    r5Coeffs_pos_of_interior x hp0 hp1 hμ00 hμ01 hμ10 hμ11 hε
  have hobj : r5BinaryObjective x t = r5TernaryObjective x t := by
    apply r5_objectives_eq_of_activeDual x η t
    intro s hs
    simpa only [hxθ] using hactive s hs
  have heq : r5BinaryCoeff x * (p - (1 - 2 * p) * t) ^ 2 =
      r5TernaryCoeff x * (t + 1) ^ 2 := by
    rw [← r5BinaryObjective_eq_quadratic x t (by simpa [hxθ] using hm 5)
        (by simpa [hxθ] using hm 8),
      ← r5TernaryObjective_eq_quadratic x t (by simpa [hxθ] using hm 3)
        (by simpa [hxθ] using hm 7)]
    exact hobj
  have hR : r5TernaryDerivative x t ≠ 0 :=
    r5TernaryDerivative_ne_zero_of_objectives_eq x t hp1 hcoeff.1 hcoeff.2
      (by simpa [hxθ] using hm 3) (by simpa [hxθ] using hm 7) heq
  have hαmix : r5MixtureCoordinate ε α =
      -r5TernaryDerivative x t /
        (r5BinaryDerivative x t - r5TernaryDerivative x t) := by
    have hs := r5_stationarity_eq_mixture x α hε hα hαout t (by
      simpa only [hxθ] using hstat)
    exact (mixture_stationarity_solve hR hs).2
  refine ⟨α, hα, hsupp, hpos, hopt, ?_⟩
  intro β hβ hβopt
  have hβout : ∀ s ∉ r5Active, β s = 0 := hrigid β hβ hβopt
  have hbelow : BddBelow {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε β v} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, rfl⟩
    exact informationObjective_nonneg_interior θ p ε hp hθ hε.le β hβ v
  have hαvalue : informationObjective θ p ε α t = ∑ j : Fin 4, η j := by
    calc
      _ = ∑ s : Fin 14, α s * dualRay ε η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ r5Active
        · rw [hactive s hs]
        · simp [hαout s hs]
      _ = _ := feasible_dualRay_sum_general ε α hα η
  have hαprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε α v} =
      informationObjective θ p ε α t := by
    apply IsLeast.csInf_eq
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact informationObjective_min_of_stationary θ p ε hp hθ hε.le α hα t
      (by
        rw [← hstat]
        apply Finset.sum_congr rfl
        intro s _
        simp [patternInformationSlope]
        ring) v
  have hβat : informationObjective θ p ε β t = Jstar θ p ε := by
    apply le_antisymm
    · calc
        _ ≤ ∑ j : Fin 4, η j :=
          certificate_dual_upper_bound θ p ε t r5Active η hactive hinactive β hβ
        _ = _ := by rw [← hαvalue, ← hαprofile, ← hopt]
    · rw [hβopt]
      exact csInf_le hbelow ⟨t, rfl⟩
  have hβmin (u : ℝ) : informationObjective θ p ε β t ≤
      informationObjective θ p ε β u := by
    rw [hβat, hβopt]
    exact csInf_le hbelow ⟨u, rfl⟩
  have hraw := informationObjective_stationary_of_min θ p ε β t hβmin
  have hβstat : ∑ s : Fin 14, β s * patternInformationSlope θ p ε s t = 0 := by
    rw [← hraw]
    apply Finset.sum_congr rfl
    intro s _
    simp [patternInformationSlope]
    ring
  have hβmix : r5MixtureCoordinate ε β =
      -r5TernaryDerivative x t /
        (r5BinaryDerivative x t - r5TernaryDerivative x t) := by
    have hs := r5_stationarity_eq_mixture x β hε hβ hβout t (by
      simpa only [hxθ] using hβstat)
    exact (mixture_stationarity_solve hR hs).2
  have hfive : β 5 = α 5 := by
    unfold r5MixtureCoordinate at hαmix hβmix
    have hd : 0 < Real.exp ε + 1 := by positivity
    nlinarith
  exact r5_supported_feasible_eq_of_five_eq ε hε β α hβ hα hβout hαout hfive


/-- Every channel attaining an oracle certified by `R5` has at least five
positive output atoms. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hx,Q,hQ,hattain), these specify the stated inputs. -/
lemma r5Certificate_outputCardinality_ge_five
    (p μ0 μ1 ε : ℝ) (hx : (p, μ0, μ1, ε) ∈ R5)
    {Z : Type*} [MeasurableSpace Z] (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP ε Q)
    (hattain : contrastVariance
      (channelFisherInfo (fun k => if k = 0 then μ0 else μ1) p Q) =
        ENNReal.ofReal (Vstar (fun k => if k = 0 then μ0 else μ1) p ε)) :
    5 ≤ outputCardinality (fun k => if k = 0 then μ0 else μ1) p Q := by
  have hxcopy := hx
  change 0 < p ∧ p < 1 ∧
      0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧ _ at hxcopy
  rcases hxcopy with ⟨hp0, hp1, hμ00, hμ01, hμ10, hμ11, hε,
    α0, t, η, hα0, hsupp0, hpos0, hstat0, hactive, hinactive, hdistinct⟩
  let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans θ := by
    change 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1
    exact ⟨hμ00, hμ01, hμ10, hμ11⟩
  obtain ⟨αu, hαu, _, hposu, hoptu, hunique⟩ :=
    r5Certificate_unique_optimum p μ0 μ1 ε hx
  obtain ⟨hopt0, _⟩ := strictCertificate_profile_optimal_and_rigid
    θ p ε hp hθ hε.le r5Active α0 t η hα0 hsupp0 hstat0 hactive hinactive
  have hα0value : informationObjective θ p ε α0 t = ∑ j : Fin 4, η j := by
    calc
      _ = ∑ s : Fin 14, α0 s * dualRay ε η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ r5Active
        · rw [hactive s hs]
        · have hz : α0 s = 0 := by
            by_contra hn
            exact hs ((hsupp0 s).mp hn)
          simp [hz]
      _ = _ := feasible_dualRay_sum_general ε α0 hα0 η
  have hα0min (u : ℝ) : informationObjective θ p ε α0 t ≤
      informationObjective θ p ε α0 u :=
    informationObjective_min_of_stationary θ p ε hp hθ hε.le α0 hα0 t
      (by
        rw [← hstat0]
        apply Finset.sum_congr rfl
        intro s _
        simp [patternInformationSlope]
        ring) u
  have hα0profile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε α0 v} =
      informationObjective θ p ε α0 t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hα0min u⟩
  have hJsum : Jstar θ p ε = ∑ j : Fin 4, η j := by
    rw [hopt0, hα0profile, hα0value]
  have hupper (β : StaircaseWeight) (hβ : staircaseFeasible ε β) :
      informationObjective θ p ε β t ≤ Jstar θ p ε := by
    rw [hJsum]
    exact certificate_dual_upper_bound θ p ε t r5Active η
      hactive hinactive β hβ
  let epsSeq : ℕ → ℝ := fun _ => ε
  have hfixed : FixedPrivacy epsSeq ε := ⟨hε, fun _ => rfl⟩
  obtain ⟨β, K, hβ, hK, hfactor, hdiff, hrigid⟩ :=
    staircase_refinement_interior p θ ε hp hθ epsSeq hfixed Q hQ
  have horder (u : ℝ) :
      informationQuadratic (channelFisherInfo θ p Q) (direction u) ≤
        informationQuadratic (informationMatrix θ p ε β) (direction u) := by
    have hn := hdiff.dotProduct_mulVec_nonneg (direction u)
    simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial] at hn ⊢
    linarith
  have hlower (u : ℝ) : Jstar θ p ε ≤
      informationObjective θ p ε β u := by
    calc
      _ ≤ informationQuadratic (channelFisherInfo θ p Q) (direction u) :=
        attainment_forces_direction_lower θ p ε u hp hθ hε Q hQ (by
          simpa only [θ] using hattain)
      _ ≤ informationQuadratic (informationMatrix θ p ε β) (direction u) := horder u
      _ = informationObjective θ p ε β u := by
        rw [informationObjective_eq_informationQuadratic]
        rfl
  have hβat : informationObjective θ p ε β t = Jstar θ p ε :=
    le_antisymm (hupper β hβ) (hlower t)
  have hβprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε β v} =
      informationObjective θ p ε β t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; rw [hβat]; exact hlower u⟩
  have hβopt : Jstar θ p ε = sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε β v} := by
    rw [hβprofile, hβat]
  have hβeq : β = αu := hunique β hβ hβopt
  have hpos : ∀ s ∈ r5Active, 0 < β s := by
    rw [hβeq]
    exact hposu
  have heq : informationQuadratic (informationMatrix θ p ε β) (direction t) =
      informationQuadratic (channelFisherInfo θ p Q) (direction t) := by
    have hQlower := attainment_forces_direction_lower θ p ε t hp hθ hε Q hQ
      (by simpa only [θ] using hattain)
    have hβupper : informationQuadratic (informationMatrix θ p ε β)
        (direction t) ≤ Jstar θ p ε := by
      calc
        _ = informationObjective θ p ε β t := by
          rw [informationObjective_eq_informationQuadratic]
          rfl
        _ ≤ _ := hupper β hβ
    exact le_antisymm (hβupper.trans hQlower) (horder t)
  have hsing : ∀ s ∈ r5Active, ∀ u ∈ r5Active, s ≠ u → K s ⟂ₘ K u := by
    intro s hs u hu hne
    by_contra hn
    have hscore := hrigid t heq s u (ne_of_gt (hpos s hs))
      (ne_of_gt (hpos u hu)) hn
    exact hdistinct rfl s hs u hu hne (by simpa only [θ] using hscore)
  have hcard := active_card_le_outputCardinality_of_pairwise_singular
    θ p ε hp hθ r5Active β hpos K hK Q hfactor hsing
  have hAcard : r5Active.card = 5 := by decide
  rw [hAcard] at hcard
  norm_num at hcard ⊢
  simpa only [θ] using hcard


/-- The primal witness carried by an `R5` certificate attains the oracle and
has exactly five positive staircase outputs. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r5Certificate_staircase_attains_five
    (p μ0 μ1 ε : ℝ) (hx : (p, μ0, μ1, ε) ∈ R5) :
    let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight, staircaseFeasible ε α ∧
      contrastVariance (informationMatrix θ p ε α) =
        ENNReal.ofReal (Vstar θ p ε) ∧
      outputCardinality θ p (staircaseChannel ε α) = 5 := by
  dsimp only
  change 0 < p ∧ p < 1 ∧
      0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧ _ at hx
  rcases hx with ⟨hp0, hp1, hμ00, hμ01, hμ10, hμ11, hε,
    α, t, η, hα, hsupp, hpos, hstat, hactive, hinactive, _⟩
  let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans θ := by
    change 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1
    exact ⟨hμ00, hμ01, hμ10, hμ11⟩
  obtain ⟨hopt, _⟩ := strictCertificate_profile_optimal_and_rigid
    θ p ε hp hθ hε.le r5Active α t η hα hsupp hstat hactive hinactive
  have hmin (u : ℝ) : informationObjective θ p ε α t ≤
      informationObjective θ p ε α u :=
    informationObjective_min_of_stationary θ p ε hp hθ hε.le α hα t
      (by
        rw [← hstat]
        apply Finset.sum_congr rfl
        intro s _
        simp [patternInformationSlope]
        ring) u
  have hprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p ε α v} =
      informationObjective θ p ε α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hmin u⟩
  have hvalue : informationObjective θ p ε α t = Jstar θ p ε := by
    rw [← hprofile, ← hopt]
  have hquad (u : ℝ) : informationObjective θ p ε α u =
      informationQuadratic (informationMatrix θ p ε α) (direction u) := by
    rw [informationObjective_eq_informationQuadratic]
    rfl
  have hqmin (u : ℝ) :
      informationQuadratic (informationMatrix θ p ε α) (direction t) ≤
        informationQuadratic (informationMatrix θ p ε α) (direction u) := by
    rw [← hquad t, ← hquad u]
    exact hmin u
  have hqpos : 0 < informationQuadratic
      (informationMatrix θ p ε α) (direction t) := by
    rw [← hquad t, hvalue]
    exact Jstar_pos_interior θ p ε hp hθ hε
  have hvariance : contrastVariance (informationMatrix θ p ε α) =
      ENNReal.ofReal (Vstar θ p ε) := by
    rw [contrastVariance_eq_reciprocal_of_minimizer
      (informationMatrix θ p ε α)
      (informationMatrix_posSemidef_interior θ p ε hp hθ hε.le α hα)
      t hqmin hqpos]
    congr 1
    rw [← hquad t, hvalue]
    rfl
  have hsuppcard : (staircaseSupport α).card = 5 := by
    have hs : staircaseSupport α = r5Active := by
      ext s
      simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsupp s
    rw [hs]
    decide
  have hcard : outputCardinality θ p (staircaseChannel ε α) = 5 := by
    rw [outputCardinality_staircase_eq_support_card θ p ε hp hθ α hα.1,
      hsuppcard]
    norm_num
  exact ⟨α, hα, hvariance, hcard⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
