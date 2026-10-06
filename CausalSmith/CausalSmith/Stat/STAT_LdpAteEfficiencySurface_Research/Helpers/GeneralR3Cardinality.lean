module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.AttainmentRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R3Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TThreeOutputRegion

/-! # General three-ray cardinality in the distinct-score neighborhood -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Under the supplied quantities and conditions, the r3 certificate direction eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp0,hp1,hμ00,hμ01,hμ10,hμ11,hε,hα,hsupp,hstat), [the r3 Certificate direction eq](goal).

Under the stated assumptions, the r3 Certificate direction eq. -/
lemma r3Certificate_direction_eq (p μ0 μ1 ε : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ00 : 0 < μ0) (hμ01 : μ0 < 1)
    (hμ10 : 0 < μ1) (hμ11 : μ1 < 1) (hε : 0 < ε)
    (α : StaircaseWeight) (t : ℝ) (hα : staircaseFeasible ε α)
    (hsupp : activeSupport α ({0, 5, 7} : Finset (Fin 14)))
    (hstat : ∑ s : Fin 14, α s * patternInformationSlope
      (fun k => if k = 0 then μ0 else μ1) p ε s t = 0) :
    t = r3Direction p μ0 μ1 ε := by
  have hsupp' : staircaseSupport α = ({0, 5, 7} : Finset (Fin 14)) := by
    ext s
    simpa [staircaseSupport] using hsupp s
  have hαeq := threeMaskWeights_unique ε hε α hα hsupp'
  have hstat' : r3Stationarity p μ0 μ1 ε t = 0 := by
    rw [r3Stationarity, ← hstat]
    apply Finset.sum_congr rfl
    intro s _
    rw [hαeq]
    rfl
  have hc : r3StationarityCoeff p μ0 μ1 ε ≠ 0 :=
    ne_of_gt (r3StationarityCoeff_pos p μ0 μ1 ε
      hp0 hp1 hμ00 hμ01 hμ10 hμ11 hε)
  have hdir := r3Stationarity_r3Direction_eq_zero p μ0 μ1 ε hc
  rw [r3Stationarity_affine] at hstat' hdir
  have hm : (t - r3Direction p μ0 μ1 ε) *
      r3StationarityCoeff p μ0 μ1 ε = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hc)

/-- Under [the supplied quantities and conditions](hyp:p), [the r3 certificate staircase attains three assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma r3Certificate_staircase_attains_three
    (p μ0 μ1 : ℝ) (hx : (p, μ0, μ1, Real.log 3) ∈ R3) :
    let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
    ∃ α : StaircaseWeight, staircaseFeasible (Real.log 3) α ∧
      contrastVariance (informationMatrix θ p (Real.log 3) α) =
        ENNReal.ofReal (Vstar θ p (Real.log 3)) ∧
      outputCardinality θ p (staircaseChannel (Real.log 3) α) = 3 := by
  dsimp only
  obtain ⟨α, hα, hsupp, hopt, _⟩ :=
    r3Certificate_unique_optimum_log3 p μ0 μ1 hx
  change 0 < p ∧ p < 1 ∧ 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧
      0 < Real.log 3 ∧ _ at hx
  rcases hx with ⟨hp0, hp1, hμ00, hμ01, hμ10, hμ11, hε,
    α0, t, η, hα0, hsupp0, _, hstat, hactive, hinactive, _⟩
  let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans θ := ⟨hμ00, hμ01, hμ10, hμ11⟩
  have hαeq : α = α0 := by
    have ha := r3_feasible_eq_canonical α hα (by
      intro s hs
      by_contra hn
      exact hs ((hsupp s).mp hn))
    have hb := r3_feasible_eq_canonical α0 hα0 (by
      intro s hs
      by_contra hn
      exact hs ((hsupp0 s).mp hn))
    exact ha.trans hb.symm
  subst α0
  have hmin (u : ℝ) : informationObjective θ p (Real.log 3) α t ≤
      informationObjective θ p (Real.log 3) α u :=
    informationObjective_min_of_stationary θ p (Real.log 3) hp hθ hε.le α hα t
      (by rw [← hstat]; apply Finset.sum_congr rfl; intro s _;
          simp [patternInformationSlope]; ring) u
  have hprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p (Real.log 3) α v} =
      informationObjective θ p (Real.log 3) α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hmin u⟩
  have hvalue : informationObjective θ p (Real.log 3) α t =
      Jstar θ p (Real.log 3) := by rw [← hprofile, ← hopt]
  have hquad (u : ℝ) : informationObjective θ p (Real.log 3) α u =
      informationQuadratic (informationMatrix θ p (Real.log 3) α) (direction u) := by
    rw [informationObjective_eq_informationQuadratic]
    rfl
  have hqmin (u : ℝ) := show
      informationQuadratic (informationMatrix θ p (Real.log 3) α) (direction t) ≤
        informationQuadratic (informationMatrix θ p (Real.log 3) α) (direction u) by
    rw [← hquad t, ← hquad u]
    exact hmin u
  have hqpos : 0 < informationQuadratic
      (informationMatrix θ p (Real.log 3) α) (direction t) := by
    rw [← hquad t, hvalue]
    exact Jstar_pos_interior θ p (Real.log 3) hp hθ hε
  have hvariance : contrastVariance (informationMatrix θ p (Real.log 3) α) =
      ENNReal.ofReal (Vstar θ p (Real.log 3)) := by
    rw [contrastVariance_eq_reciprocal_of_minimizer
      (informationMatrix θ p (Real.log 3) α)
      (informationMatrix_posSemidef_interior θ p (Real.log 3) hp hθ hε.le α hα)
      t hqmin hqpos]
    congr 1
    rw [← hquad t, hvalue]
    rfl
  have hsuppcard : staircaseSupport α = ({0, 5, 7} : Finset (Fin 14)) := by
    ext s
    simpa [staircaseSupport] using hsupp s
  have hcard : outputCardinality θ p (staircaseChannel (Real.log 3) α) = 3 := by
    rw [outputCardinality_staircase_eq_support_card θ p (Real.log 3) hp hθ α hα.1,
      hsuppcard]
    have hc : ({0, 5, 7} : Finset (Fin 14)).card = 3 := by decide
    rw [hc]
    norm_num
  exact ⟨α, hα, hvariance, hcard⟩

/-- Under [the supplied quantities and conditions](hyp:p), [the r3 certificate output cardinality ge three of distinct assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx,hdistinct,Q,hQ,hattain), these specify the stated inputs. -/
lemma r3Certificate_outputCardinality_ge_three_of_distinct
    (p μ0 μ1 : ℝ) (hx : (p, μ0, μ1, Real.log 3) ∈ R3)
    (hdistinct : ∀ i k : Fin 3, i ≠ k →
      r3ProjectedScoreAt (p, μ0, μ1, Real.log 3) i ≠
        r3ProjectedScoreAt (p, μ0, μ1, Real.log 3) k)
    {Z : Type*} [MeasurableSpace Z] (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP (Real.log 3) Q)
    (hattain : contrastVariance
      (channelFisherInfo (fun k => if k = 0 then μ0 else μ1) p Q) =
        ENNReal.ofReal (Vstar (fun k => if k = 0 then μ0 else μ1)
          p (Real.log 3))) :
    3 ≤ outputCardinality (fun k => if k = 0 then μ0 else μ1) p Q := by
  have hxcopy := hx
  change 0 < p ∧ p < 1 ∧ 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧
      0 < Real.log 3 ∧ _ at hxcopy
  rcases hxcopy with ⟨hp0, hp1, hμ00, hμ01, hμ10, hμ11, hε,
    α, t, η, hα, hsupp, _, hstat, hactive, hinactive, _⟩
  let θ : TrialParameter := fun k => if k = 0 then μ0 else μ1
  let A : Finset (Fin 14) := {0, 5, 7}
  have hp : InteriorAssignment p := ⟨hp0, hp1⟩
  have hθ : InteriorMeans θ := ⟨hμ00, hμ01, hμ10, hμ11⟩
  have ht : t = r3Direction p μ0 μ1 (Real.log 3) :=
    r3Certificate_direction_eq p μ0 μ1 (Real.log 3) hp0 hp1 hμ00 hμ01
      hμ10 hμ11 hε α t hα hsupp hstat
  obtain ⟨hopt, _⟩ := strictCertificate_profile_optimal_and_rigid
    θ p (Real.log 3) hp hθ hε.le A α t η hα hsupp hstat hactive hinactive
  have hmin (u : ℝ) : informationObjective θ p (Real.log 3) α t ≤
      informationObjective θ p (Real.log 3) α u :=
    informationObjective_min_of_stationary θ p (Real.log 3) hp hθ hε.le α hα t
      (by rw [← hstat]; apply Finset.sum_congr rfl; intro s _;
          simp [patternInformationSlope]; ring) u
  have hprofile : sInf {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ p (Real.log 3) α v} =
      informationObjective θ p (Real.log 3) α t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hmin u⟩
  have hvalue : informationObjective θ p (Real.log 3) α t = ∑ j : Fin 4, η j := by
    calc
      _ = ∑ s : Fin 14, α s * dualRay (Real.log 3) η s := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s ∈ A
        · rw [hactive s hs]
        · have hz : α s = 0 := by by_contra hn; exact hs ((hsupp s).mp hn)
          simp [hz]
      _ = _ := feasible_dualRay_sum_general (Real.log 3) α hα η
  have hJsum : Jstar θ p (Real.log 3) = ∑ j : Fin 4, η j := by
    rw [hopt, hprofile, hvalue]
  have hupper : ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
      informationObjective θ p (Real.log 3) β t ≤ Jstar θ p (Real.log 3) := by
    intro β hβ
    rw [hJsum]
    exact certificate_dual_upper_bound θ p (Real.log 3) t A η
      hactive hinactive β hβ
  have hpositive : ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
      informationObjective θ p (Real.log 3) β t = Jstar θ p (Real.log 3) →
      ∀ s ∈ A, 0 < β s := by
    intro β hβ heq
    have hout := certificate_equality_forces_inactive_zero θ p (Real.log 3) t A η
      hactive hinactive β hβ (heq.trans hJsum)
    have hcanonical := r3_feasible_eq_canonical β hβ hout
    intro s hs
    rw [hcanonical]
    change s ∈ ({0, 5, 7} : Finset (Fin 14)) at hs
    simp [hs]
  have hmaskinj : Function.Injective r3Mask := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [r3Mask]
  have htheta : regionTheta (p, μ0, μ1, Real.log 3) = θ := by
    funext k
    fin_cases k <;> rfl
  have hscores : ∀ s ∈ A, ∀ u ∈ A, s ≠ u →
      projectedScore θ p (Real.log 3) s t ≠
        projectedScore θ p (Real.log 3) u t := by
    intro s hs u hu hne
    obtain ⟨i, rfl⟩ : ∃ i : Fin 3, r3Mask i = s := by
      have hs' : s = 0 ∨ s = 5 ∨ s = 7 := by simpa [A] using hs
      rcases hs' with rfl | rfl | rfl
      · exact ⟨0, by simp [r3Mask]⟩
      · exact ⟨1, by simp [r3Mask]⟩
      · exact ⟨2, by simp [r3Mask]⟩
    obtain ⟨k, rfl⟩ : ∃ k : Fin 3, r3Mask k = u := by
      have hu' : u = 0 ∨ u = 5 ∨ u = 7 := by simpa [A] using hu
      rcases hu' with rfl | rfl | rfl
      · exact ⟨0, by simp [r3Mask]⟩
      · exact ⟨1, by simp [r3Mask]⟩
      · exact ⟨2, by simp [r3Mask]⟩
    have hik : i ≠ k := fun e => hne (congrArg r3Mask e)
    have hd := hdistinct i k hik
    rw [r3ProjectedScoreAt_eq, r3ProjectedScoreAt_eq, htheta] at hd
    simpa only [θ, ht] using hd
  have hcard := outputCardinality_ge_of_attainment_direction
    θ p (Real.log 3) t hp hθ hε A hupper hpositive hscores Q hQ
      (by simpa only [θ] using hattain)
  have hAcard : A.card = 3 := by decide
  rw [hAcard] at hcard
  norm_num at hcard ⊢
  simpa only [θ] using hcard

end CausalSmith.Stat.LdpAteEfficiencySurface
