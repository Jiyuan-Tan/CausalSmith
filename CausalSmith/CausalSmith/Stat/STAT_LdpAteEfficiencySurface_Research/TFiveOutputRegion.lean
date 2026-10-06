module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.AttainmentRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CertificateRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CenteredR5Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.GeneralR5Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PostprocessCardinality
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R5Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R5Continuity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Regions
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.TreatmentSwap
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Five-output certificate region

The centered family has a unique five-ray optimum; distinct projected scores
prevent any attaining stationary channel from merging those rays. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface
open ProbabilityTheory

/-- [the r5 nonempty centered assertion](goal) holds. -/
lemma R5_nonempty_centered : R5.Nonempty := by
  refine ⟨((1 / 4 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3), ?_⟩
  exact centeredPoint_mem_R5 (1 / 4) (by norm_num) (by norm_num)

/-- [the centered five output region assertion](goal) holds. -/
lemma centered_five_output_region :
    ∀ p : ℝ, 0 < p → p < (1 / 2 : ℝ) →
      (p, (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5 ∧
      (∃ α : StaircaseWeight,
        staircaseFeasible (Real.log 3) α ∧
        staircaseSupport α = ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
        Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
          sInf {u : ℝ | ∃ t : ℝ,
            u = informationObjective (fun _ => (1 / 2 : ℝ)) p
              (Real.log 3) α t} ∧
        (∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
          Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
            sInf {u : ℝ | ∃ t : ℝ,
              u = informationObjective (fun _ => (1 / 2 : ℝ)) p
                (Real.log 3) β t} → β = α)) ∧
      (∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
        StationaryLDP (Real.log 3) Q →
        contrastVariance (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) =
          ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3)) →
        5 ≤ outputCardinality (fun _ => (1 / 2 : ℝ)) p Q) := by
  intro p hp0 hp1
  refine ⟨centeredPoint_mem_R5 p hp0 hp1, ?_, ?_⟩
  · obtain ⟨hfeas, hopt, hunique⟩ := centeredR5_profile_optimal_unique p hp0 hp1
    refine ⟨centeredR5Weight p, hfeas, ?_, hopt, hunique⟩
    ext s
    simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [r5Active] using (centeredR5Weight_active p hp0 hp1).1 s
  · intro Z _ Q hQ hattain
    exact centeredR5_outputCardinality_ge_five p hp0 hp1 Z Q hQ hattain

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the reflected point mem r5 assertion](goal) holds. -/
lemma reflectedPoint_mem_R5 (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    (1 - p, (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5 := by
  exact centeredPoint_mem_R5 (1 - p) (by linarith) (by linarith)

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the reflected five output region assertion](goal) holds. -/
lemma reflected_five_output_region (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    (∃ α : StaircaseWeight,
      staircaseFeasible (Real.log 3) α ∧
      staircaseSupport α =
        swappedSupport ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
      Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
        sInf {u : ℝ | ∃ t : ℝ,
          u = informationObjective (fun _ => (1 / 2 : ℝ)) p
            (Real.log 3) α t} ∧
      ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
        Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
          sInf {u : ℝ | ∃ t : ℝ,
            u = informationObjective (fun _ => (1 / 2 : ℝ)) p
              (Real.log 3) β t} → β = α) ∧
    ∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
      StationaryLDP (Real.log 3) Q →
      contrastVariance (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) =
        ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3)) →
      5 ≤ outputCardinality (fun _ => (1 / 2 : ℝ)) p Q := by
  let q := 1 - p
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 / 2 := by dsimp [q]; linarith
  obtain ⟨hfeas, hopt, hunique⟩ := centeredR5_profile_optimal_unique q hq0 hq1
  let α0 := centeredR5Weight q
  let α := swapTreatmentWeight α0
  have hα : staircaseFeasible (Real.log 3) α :=
    (staircaseFeasible_swapTreatment _ _).2 hfeas
  have hsupp0 : staircaseSupport α0 = ({2, 3, 5, 7, 8} : Finset (Fin 14)) := by
    ext s
    simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [α0, r5Active] using (centeredR5Weight_active q hq0 hq1).1 s
  have hsupp : staircaseSupport α =
      swappedSupport ({2, 3, 5, 7, 8} : Finset (Fin 14)) := by
    change staircaseSupport (swapTreatmentWeight α0) = _
    rw [staircaseSupport_swapTreatment, hsupp0]
  have hopt' : Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
      sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
        (fun _ => (1 / 2 : ℝ)) p (Real.log 3) α t} := by
    change Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
      sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
        (fun _ => (1 / 2 : ℝ)) p (Real.log 3) (swapTreatmentWeight α0) t}
    rw [centered_Jstar_swapTreatment p, centered_profileSet_swapTreatment]
    convert hopt using 1 <;> dsimp [q] <;> ring
  have hunique' : ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
      Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
          (fun _ => (1 / 2 : ℝ)) p (Real.log 3) β t} → β = α := by
    intro β hβ hβopt
    have hswapopt : Jstar (fun _ => (1 / 2 : ℝ)) q (Real.log 3) =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective
          (fun _ => (1 / 2 : ℝ)) q (Real.log 3)
            (swapTreatmentWeight β) t} := by
      rw [centered_profileSet_swapTreatment]
      calc
        Jstar (fun _ => (1 / 2 : ℝ)) q (Real.log 3) =
            Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) := by
          rw [centered_Jstar_swapTreatment]
          congr 2 <;> dsimp [q] <;> ring
        _ = _ := by
          convert hβopt using 1 <;> dsimp [q] <;> ring
    have heq := hunique (swapTreatmentWeight β)
      ((staircaseFeasible_swapTreatment _ _).2 hβ) hswapopt
    apply swapTreatmentWeight_involutive.injective
    change swapTreatmentWeight β = swapTreatmentWeight α
    have hσα : swapTreatmentWeight α = α0 := by
      change swapTreatmentWeight (swapTreatmentWeight α0) = α0
      exact swapTreatmentWeight_involutive α0
    rw [hσα]
    exact heq
  refine ⟨⟨α, hα, hsupp, hopt', hunique'⟩, ?_⟩
  intro Z _ Q hQ hattain
  have hsQ := stationaryLDP_swapTreatment (Real.log 3) Q hQ
  have hsattain : contrastVariance
      (channelFisherInfo (fun _ => (1 / 2 : ℝ)) q (swapTreatmentChannel Q)) =
      ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) q (Real.log 3)) := by
    rw [show q = 1 - p by rfl, channelFisherInfo_swapTreatment,
      contrastVariance_swapTreatment]
    rw [← centered_Vstar_swapTreatment p]
    exact hattain
  have hcard := centeredR5_outputCardinality_ge_five q hq0 hq1 Z
    (swapTreatmentChannel Q) hsQ hsattain
  rw [show q = 1 - p by rfl, centered_outputCardinality_swapTreatment] at hcard
  exact hcard

/-- [the is open r5 continuous certificate assertion](goal) holds. -/
lemma isOpen_R5_continuousCertificate : IsOpen R5 := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases x with ⟨p, μ0, μ1, ε⟩
  change 0 < p ∧ p < 1 ∧ 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧ _ at hx
  rcases hx with ⟨hp0,hp1,hm00,hm01,hm10,hm11,hε,α,t,η0,
    hα,hsupp,hpos,hstat,hactive,hinactive,hdistinct⟩
  let x0 : RegionParameter := (p,μ0,μ1,ε)
  have hxTheta : regionTheta x0 = (fun k => if k = 0 then μ0 else μ1) := by
    funext k
    fin_cases k <;> rfl
  have hm (s : Fin 14) :
      patternMass (regionTheta x0) x0.1 x0.2.2.2 s ≠ 0 :=
    ne_of_gt (patternMass_pos_of_interior p μ0 μ1 ε
      hp0 hp1 hm00 hm01 hm10 hm11 s)
  have hout : ∀ s ∉ r5Active, α s = 0 := by
    intro s hs
    by_contra hn
    exact hs ((hsupp s).mp hn)
  have hcoeff := r5Coeffs_pos_of_interior x0 hp0 hp1 hm00 hm01 hm10 hm11 hε
  have hobj := r5_objectives_eq_of_activeDual x0 η0 t hactive
  have heq : r5BinaryCoeff x0 * (p - (1 - 2 * p) * t) ^ 2 =
      r5TernaryCoeff x0 * (t + 1) ^ 2 := by
    rw [← r5BinaryObjective_eq_quadratic x0 t (hm 5) (hm 8),
      ← r5TernaryObjective_eq_quadratic x0 t (hm 3) (hm 7)]
    exact hobj
  obtain ⟨σ, hσ, hbranchden, ht0⟩ :=
    exists_r5DirectionBranch_eq x0 t hp1 hcoeff.1 hcoeff.2.le heq
  have ht := continuousAt_r5DirectionBranch x0 σ (ne_of_gt hcoeff.1)
    (hm 3) (hm 5) (hm 7) (hm 8) hbranchden
  have hR : r5TernaryDerivative x0 t ≠ 0 :=
    r5TernaryDerivative_ne_zero_of_objectives_eq x0 t hp1
      hcoeff.1 hcoeff.2 (hm 3) (hm 7) heq
  have hmix := r5_stationarity_eq_mixture x0 α hε hα hout t hstat
  obtain ⟨hderivden0, huformula⟩ := mixture_stationarity_solve hR hmix
  have hderivden : r5BinaryDerivative x0 (r5DirectionBranch σ x0) -
      r5TernaryDerivative x0 (r5DirectionBranch σ x0) ≠ 0 := by
    simpa [ht0] using hderivden0
  have hu := continuousAt_r5ContinuedMixture x0 σ ht
    (hm 2) (hm 3) (hm 5) (hm 7) (hm 8) hderivden
  have hu0 : r5ContinuedMixture σ x0 = r5MixtureCoordinate ε α :=
    r5ContinuedMixture_eq x0 α t σ ht0 hε hα hout hstat hR
  obtain ⟨η, hη, hη0, hdual4⟩ :=
    exists_local_r5Dual x0 (r5DirectionBranch σ) η0 hε ht hm (by
      intro s hs
      rw [hxTheta, ht0]
      exact hactive s (by simpa [r5Active] using hs))
  have hubase := r5MixtureCoordinate_mem_Ioo ε hε α hα hout hpos
  have huIoo : ∀ᶠ y in nhds x0, r5ContinuedMixture σ y ∈ Set.Ioo 0 1 := by
    filter_upwards [continuousAt_const.eventually_lt hu (hu0.symm ▸ hubase.1),
      hu.eventually_lt continuousAt_const (hu0.symm ▸ hubase.2)] with y hy0 hy1
    exact ⟨hy0,hy1⟩
  have hbranchdenEv : ∀ᶠ y in nhds x0,
      1 - 2 * y.1 + σ * r5Scale y ≠ 0 := by
    have hc : ContinuousAt (fun y : RegionParameter =>
        1 - 2 * y.1 + σ * r5Scale y) x0 :=
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_fst)).add
        (continuousAt_const.mul
          (continuousAt_r5Scale x0 (ne_of_gt hcoeff.1)
            (hm 3) (hm 5) (hm 7) (hm 8)))
    exact hc.eventually_ne hbranchden
  have hbasic : ∀ᶠ y in nhds x0,
      0 < y.1 ∧ y.1 < 1 ∧ 0 < y.2.1 ∧ y.2.1 < 1 ∧
      0 < y.2.2.1 ∧ y.2.2.1 < 1 ∧ 0 < y.2.2.2 := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hp0,
      continuousAt_fst.eventually_lt continuousAt_const hp1,
      continuousAt_const.eventually_lt continuousAt_snd.fst hm00,
      continuousAt_snd.fst.eventually_lt continuousAt_const hm01,
      continuousAt_const.eventually_lt continuousAt_snd.snd.fst hm10,
      continuousAt_snd.snd.fst.eventually_lt continuousAt_const hm11,
      continuousAt_const.eventually_lt continuousAt_snd.snd.snd hε] with y
      yp0 yp1 ym00 ym01 ym10 ym11 yε
    exact ⟨yp0,yp1,ym00,ym01,ym10,ym11,yε⟩
  have hinfo (s : Fin 14) : ContinuousAt (fun y : RegionParameter =>
      patternInformation (regionTheta y) y.1 y.2.2.2 s
        (r5DirectionBranch σ y)) x0 :=
    continuousAt_patternInformation_region s _ x0 ht (hm s)
  have hscore (s : Fin 14) : ContinuousAt (fun y : RegionParameter =>
      projectedScore (regionTheta y) y.1 y.2.2.2 s
        (r5DirectionBranch σ y)) x0 :=
    continuousAt_projectedScore_region s _ x0 ht (hm s)
  have hdualcont (s : Fin 14) : ContinuousAt (fun y : RegionParameter =>
      dualRay y.2.2.2 (η y) s) x0 := by
    unfold dualRay
    let f := fun j : Fin 4 => fun y : RegionParameter =>
      patternRay y.2.2.2 s j * η y j
    have hf (j : Fin 4) : ContinuousAt (f j) x0 :=
      (continuous_patternRay_region s j).continuousAt.mul
        ((continuousAt_pi.mp hη) j)
    have hsum : ∀ S : Finset (Fin 4),
        ContinuousAt (fun y => ∑ j ∈ S, f j y) x0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa using
          (continuousAt_const : ContinuousAt (fun _ : RegionParameter => (0 : ℝ)) x0)
      | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          exact (hf a).add ih
    simpa [f] using hsum Finset.univ
  have hslack : ∀ᶠ y in nhds x0, ∀ s : Fin 14, s ∉ r5Active →
      patternInformation (regionTheta y) y.1 y.2.2.2 s
        (r5DirectionBranch σ y) < dualRay y.2.2.2 (η y) s := by
    have hall : ∀ᶠ y in nhds x0, ∀ s ∈ (Finset.univ : Finset (Fin 14)),
        s ∉ r5Active → patternInformation (regionTheta y) y.1 y.2.2.2 s
          (r5DirectionBranch σ y) < dualRay y.2.2.2 (η y) s :=
      (Filter.eventually_all_finset (Finset.univ : Finset (Fin 14))).2
      fun s _ => by
        by_cases hs : s ∈ r5Active
        · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hs))
        · exact ((hinfo s).eventually_lt (hdualcont s)
            (by rw [hxTheta, ht0, hη0]; exact hinactive s hs)).mono
              (fun _ h _ => h)
    exact hall.mono fun _ h s hs => h s (Finset.mem_univ s) hs
  have hdistinctEv : ∀ᶠ y in nhds x0, ∀ s ∈ r5Active, ∀ u ∈ r5Active,
      s ≠ u → projectedScore (regionTheta y) y.1 y.2.2.2 s
        (r5DirectionBranch σ y) ≠ projectedScore (regionTheta y) y.1 y.2.2.2 u
          (r5DirectionBranch σ y) := by
    have hall : ∀ᶠ y in nhds x0, ∀ s ∈ r5Active, ∀ u ∈ r5Active,
        s ≠ u → projectedScore (regionTheta y) y.1 y.2.2.2 s
          (r5DirectionBranch σ y) ≠ projectedScore (regionTheta y) y.1 y.2.2.2 u
            (r5DirectionBranch σ y) :=
      (Filter.eventually_all_finset r5Active).2 fun s hs =>
      (Filter.eventually_all_finset r5Active).2 fun u hu => by
        by_cases hsu : s = u
        · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hsu))
        · have hne := hdistinct rfl s (by simpa [r5Active] using hs)
            u (by simpa [r5Active] using hu) hsu
          have hne' : projectedScore (regionTheta x0) x0.1 x0.2.2.2 s
              (r5DirectionBranch σ x0) ≠
              projectedScore (regionTheta x0) x0.1 x0.2.2.2 u
                (r5DirectionBranch σ x0) := by
            change projectedScore (regionTheta x0) p ε s
                (r5DirectionBranch σ x0) ≠
              projectedScore (regionTheta x0) p ε u
                (r5DirectionBranch σ x0)
            rw [hxTheta, ht0]
            exact hne
          exact ((hscore s).sub (hscore u)).eventually_ne
            (sub_ne_zero.mpr hne') |>.mono
              (fun _ h _ => sub_ne_zero.mp h)
    exact hall
  have hderivdenEv : ∀ᶠ y in nhds x0,
      r5BinaryDerivative y (r5DirectionBranch σ y) -
        r5TernaryDerivative y (r5DirectionBranch σ y) ≠ 0 := by
    have hP := continuousAt_r5BinaryDerivative_comp x0
      (r5DirectionBranch σ) ht (hm 5) (hm 8)
    have hRcont := continuousAt_r5TernaryDerivative_comp x0
      (r5DirectionBranch σ) ht (hm 2) (hm 3) (hm 7)
    exact (hP.sub hRcont).eventually_ne hderivden
  filter_upwards [hbasic, huIoo, hbranchdenEv, hderivdenEv,
    hdual4, hslack, hdistinctEv]
    with y hybasic hyu hyden hyderivden hydual hyslack hydistinct
  rcases y with ⟨q,ν0,ν1,δ⟩
  rcases hybasic with ⟨hq0,hq1,hν00,hν01,hν10,hν11,hδ⟩
  change 0 < q ∧ q < 1 ∧ 0 < ν0 ∧ ν0 < 1 ∧ 0 < ν1 ∧ ν1 < 1 ∧ 0 < δ ∧ _
  let y0 : RegionParameter := (q,ν0,ν1,δ)
  let ty := r5DirectionBranch σ y0
  let uy := r5ContinuedMixture σ y0
  let αy := r5WeightFromCoordinate δ uy
  have hyTheta : regionTheta (q,ν0,ν1,δ) =
      (fun k => if k = 0 then ν0 else ν1) := by
    funext k
    fin_cases k <;> rfl
  rw [hyTheta] at hyslack hydistinct
  refine ⟨hq0,hq1,hν00,hν01,hν10,hν11,hδ,αy,ty,η y0, ?_⟩
  have hmy (s : Fin 14) : patternMass (regionTheta y0) q δ s ≠ 0 :=
    ne_of_gt (patternMass_pos_of_interior q ν0 ν1 δ
      hq0 hq1 hν00 hν01 hν10 hν11 s)
  have hcy := r5Coeffs_pos_of_interior y0 hq0 hq1 hν00 hν01 hν10 hν11 hδ
  have hobjy : r5BinaryObjective y0 ty = r5TernaryObjective y0 ty := by
    rw [r5BinaryObjective_eq_quadratic y0 ty (hmy 5) (hmy 8),
      r5TernaryObjective_eq_quadratic y0 ty (hmy 3) (hmy 7)]
    exact r5DirectionBranch_objectives_eq y0 σ
      (by rcases hσ with rfl | rfl <;> norm_num) hcy.1 hcy.2.le hyden
  unfold r5DualTarget at hydual
  rw [hyTheta] at hydual
  refine ⟨(r5WeightFromCoordinate_feasible δ uy).2
      ⟨hyu.1.le, hyu.2.le⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact r5WeightFromCoordinate_active δ uy hyu
  · exact r5WeightFromCoordinate_pos δ uy hyu
  · exact r5ContinuedWeight_stationary y0 σ (by simpa [y0, ty] using hyderivden)
  · intro s hs
    have hcases : s = 2 ∨ s = 3 ∨ s = 5 ∨ s = 7 ∨ s = 8 := by
      simpa [r5Active] using hs
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · simpa [y0, ty, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
        dotProduct, dualRay, mul_comm] using congrFun hydual 0
    · simpa [y0, ty, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
        dotProduct, dualRay, mul_comm] using congrFun hydual 1
    · simpa [y0, ty, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
        dotProduct, dualRay, mul_comm] using congrFun hydual 2
    · simpa [y0, ty, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
        dotProduct, dualRay, mul_comm] using congrFun hydual 3
    · apply r5_fifthDual_eq y0 (η y0) ty hobjy
      · simpa [y0, ty, hyTheta, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
          dotProduct, dualRay, mul_comm] using congrFun hydual 0
      · simpa [y0, ty, hyTheta, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
          dotProduct, dualRay, mul_comm] using congrFun hydual 1
      · simpa [y0, ty, hyTheta, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
          dotProduct, dualRay, mul_comm] using congrFun hydual 2
      · simpa [y0, ty, hyTheta, r5DualMatrix, r5DualTarget, r5DualMask, Matrix.mulVec,
          dotProduct, dualRay, mul_comm] using congrFun hydual 3
  · simpa [y0, ty, r5Active] using hyslack
  · intro _
    simpa [y0, ty, r5Active] using hydistinct

-- @node: thm:five-output-region
/-- Under the supplied quantities and conditions, the five output region assertion holds. [The five output region](goal).

The five output region. -/
theorem five_output_region :
    IsOpen R5 ∧ R5.Nonempty ∧
    (∀ p : ℝ, 0 < p → p < (1 / 2 : ℝ) →
      (p, (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5 ∧
      (∃ α : StaircaseWeight,
        staircaseFeasible (Real.log 3) α ∧
        staircaseSupport α = ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
        Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
          sInf {u : ℝ | ∃ t : ℝ,
            u = informationObjective (fun _ => (1 / 2 : ℝ)) p
              (Real.log 3) α t} ∧
        (∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
          Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
            sInf {u : ℝ | ∃ t : ℝ,
              u = informationObjective (fun _ => (1 / 2 : ℝ)) p
                (Real.log 3) β t} → β = α)) ∧
      (∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
        StationaryLDP (Real.log 3) Q →
        contrastVariance (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) =
          ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3)) →
        5 ≤ outputCardinality (fun _ => (1 / 2 : ℝ)) p Q)) ∧
    (∀ p : ℝ, (1 / 2 : ℝ) < p → p < 1 →
      (1 - p, (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5 ∧
      (∃ α : StaircaseWeight,
        staircaseFeasible (Real.log 3) α ∧
        staircaseSupport α =
          swappedSupport ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
        Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
          sInf {u : ℝ | ∃ t : ℝ,
            u = informationObjective (fun _ => (1 / 2 : ℝ)) p
              (Real.log 3) α t} ∧
        ∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
          Jstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3) =
            sInf {u : ℝ | ∃ t : ℝ,
              u = informationObjective (fun _ => (1 / 2 : ℝ)) p
                (Real.log 3) β t} → β = α) ∧
      ∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
        StationaryLDP (Real.log 3) Q →
        contrastVariance (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) =
          ENNReal.ofReal (Vstar (fun _ => (1 / 2 : ℝ)) p (Real.log 3)) →
        5 ≤ outputCardinality (fun _ => (1 / 2 : ℝ)) p Q) ∧
    (∀ p μ0 μ1 ε : ℝ, (p, μ0, μ1, ε) ∈ R5 →
      ∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
        StationaryLDP ε Q →
        contrastVariance
          (channelFisherInfo (fun k => if k = 0 then μ0 else μ1) p Q) =
          ENNReal.ofReal (Vstar (fun k => if k = 0 then μ0 else μ1) p ε) →
        5 ≤ outputCardinality (fun k => if k = 0 then μ0 else μ1) p Q) := by
  refine ⟨isOpen_R5_continuousCertificate, R5_nonempty_centered,
    centered_five_output_region, ?_, ?_⟩
  · intro p hp0 hp1
    exact ⟨reflectedPoint_mem_R5 p hp0 hp1,
      reflected_five_output_region p hp0 hp1⟩
  · intro p μ0 μ1 ε hx Z _ Q hQ hattain
    exact r5Certificate_outputCardinality_ge_five p μ0 μ1 ε hx Q hQ hattain

end CausalSmith.Stat.LdpAteEfficiencySurface
