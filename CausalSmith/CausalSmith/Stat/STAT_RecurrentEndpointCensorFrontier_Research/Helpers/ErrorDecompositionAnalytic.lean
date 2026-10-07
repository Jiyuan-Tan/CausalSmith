module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingTarget

/-!
# Analytic helpers for the exact error decomposition

Integrability and quotient FTC facts for the remaining-target bridge.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma poissonRecurrence_intervalIntegrable (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (a : Arm) :
    IntervalIntegrable (P.lam a) volume 0 1 := by
  obtain ⟨hmeas, hnonneg, hfinite⟩ := hPoisson a
  letI : IsFiniteMeasure (recurrenceIntensity P a) := hfinite.choose
  have hmass :
      (∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (P.lam a t) ∂volume) ≠
        (⊤ : ℝ≥0∞) := by
    have htop := measure_ne_top (recurrenceIntensity P a) Set.univ
    simpa [recurrenceIntensity] using htop
  have hint : Integrable (P.lam a)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmeas.aestronglyMeasurable hnonneg).mp hmass
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hint

lemma weightedTarget_intervalIntegrable (c : ClassConstants) (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hBounds : DeathBounds c P) (a : Arm) {h T : ℝ}
    (hh : 0 ≤ h) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    IntervalIntegrable (fun t => continuationWeight (holderOrder c) h t *
      survival P a t * P.lam a t) volume 0 T := by
  have hlam : IntegrableOn (P.lam a) (Set.Ioc (0 : ℝ) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp
      ((poissonRecurrence_intervalIntegrable P hPoisson a).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
        exact Set.Icc_subset_Icc le_rfl hT1))
  have hprim : ContinuousOn (fun t : ℝ => ∫ u in (0 : ℝ)..t, P.hazard a u)
      (Set.Icc (0 : ℝ) 1) :=
    by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        ((hDeath.1 a).absolutelyContinuousOnInterval_intervalIntegral
          (by norm_num : (0 : ℝ) ∈ Set.uIcc 0 1) |>.continuousOn)
  have hsurv : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => Real.exp (-(∫ u in (0 : ℝ)..t,
      P.hazard a u))) _
    exact Real.continuous_exp.comp_continuousOn hprim.neg
  have hw : Measurable (continuationWeight (holderOrder c) h) := by
    unfold continuationWeight
    by_cases hh0 : h = 0
    · simp [hh0]
    · simp only [hh0, ↓reduceIte]
      apply Measurable.add
      · exact measurable_const.ite
          (measurableSet_le measurable_id measurable_const) measurable_const
      · apply ((continuationPoly_continuous _).measurable.comp (by fun_prop)).ite
        exact (measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const)
        exact measurable_const
  let K : ℝ := 1 + ∑ m : Fin (holderOrder c + 1),
    |((continuationGram (holderOrder c))⁻¹.mulVec
      (continuationRhs (holderOrder c))) m| * (2 : ℝ) ^ m.val
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsum_nonneg : 0 ≤ ∑ m : Fin (holderOrder c + 1),
      |((continuationGram (holderOrder c))⁻¹.mulVec
        (continuationRhs (holderOrder c))) m| * (2 : ℝ) ^ m.val := by
    positivity
  have hweight : ∀ t, |continuationWeight (holderOrder c) h t| ≤ K := by
    intro t
    rcases hh.eq_or_lt with rfl | hh
    · simp [continuationWeight, K]
      exact hsum_nonneg
    · exact continuationWeight_abs_le_coeffSum (holderOrder c) hh
  have hmult : AEStronglyMeasurable
      (fun t => continuationWeight (holderOrder c) h t * survival P a t)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    hw.aestronglyMeasurable.restrict.mul
      (hsurv.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
        measurableSet_Ioc (by
          intro t ht
          exact ⟨ht.1.le, ht.2.trans hT1⟩))
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) T),
      ‖continuationWeight (holderOrder c) h t * survival P a t‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    have hs := (survival_bounds_of_deathBounds c P hBounds a
      ⟨ht.1.le, ht.2.trans hT1⟩).2
    have hs0 : 0 ≤ survival P a t := (Real.exp_pos _).le
    calc
      |continuationWeight (holderOrder c) h t| * |survival P a t| ≤ K * 1 :=
        mul_le_mul (hweight t) (by simpa [abs_of_nonneg hs0] using hs)
          (abs_nonneg _) hK
      _ = K := mul_one K
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
    (hlam.bdd_mul hmult hbound)

lemma remainingTarget_ratio_integral_eq_sub (c : ClassConstants) (P : SubjectLaw)
    (hPoisson : PoissonRecurrence P) (hDeath : DeathHazard P)
    (hBounds : DeathBounds c P) (a : Arm) {h U x y : ℝ}
    (hh : 0 ≤ h) (hU : U = 1 - h) (hU0 : 0 ≤ U)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ U) :
    (∫ t in x..y, -(continuationWeight (holderOrder c) h t * P.lam a t) +
      remainingTarget c P a h t / survival P a t * P.hazard a t) =
      remainingTarget c P a h y / survival P a y -
        remainingTarget c P a h x / survival P a x := by
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  let G : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, P.hazard a u
  let A : ℝ → ℝ := fun t => remainingTarget c P a h 0 - ∫ u in (0 : ℝ)..t, target u
  let R : ℝ → ℝ := fun t => Real.exp (G t)
  let F : ℝ → ℝ := fun t => A t * R t
  have hU1 : U ≤ 1 := by rw [hU]; linarith
  have htarget : IntervalIntegrable target volume 0 U := by
    simpa only [target] using
      weightedTarget_intervalIntegrable c P hPoisson hDeath hBounds a hh hU0 hU1
  have hhaz : IntervalIntegrable (P.hazard a) volume 0 U :=
    (hDeath.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl hU1)
  have hA : AbsolutelyContinuousOnInterval A 0 U := by
    have hc : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => remainingTarget c P a h 0) 0 U := by
      rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      exact ⟨1, by norm_num, fun E _ _ => by simpa using hε⟩
    exact hc.sub
      (htarget.absolutelyContinuousOnInterval_intervalIntegral
        (by simp [hU0] : (0 : ℝ) ∈ Set.uIcc 0 U))
  have hG : AbsolutelyContinuousOnInterval G 0 U := by
    exact hhaz.absolutelyContinuousOnInterval_intervalIntegral
      (by simp [hU0] : (0 : ℝ) ∈ Set.uIcc 0 U)
  have hR : AbsolutelyContinuousOnInterval R 0 U := by
    obtain ⟨C, hC⟩ := hG.exists_bound
    have hmap : Set.MapsTo G (Set.uIcc (0 : ℝ) U) (Set.Icc (-C) C) := by
      intro t ht
      have hb := hC t ht
      exact Set.mem_Icc.mpr (by simpa only [Real.norm_eq_abs, abs_le] using hb)
    obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K Real.exp (Set.Icc (-C) C) :=
      ((Real.contDiff_exp (n := 1)).contDiffOn).exists_lipschitzOnWith
        (by norm_num) (convex_Icc _ _) isCompact_Icc
    have hbound := hG.const_mul (K : ℝ)
    unfold AbsolutelyContinuousOnInterval at hbound ⊢
    apply squeeze_zero' ?_ ?_ (by simpa [R] using hbound)
    · exact Filter.Eventually.of_forall
        (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    · rw [Filter.eventually_inf_principal]
      filter_upwards with E hE
      apply Finset.sum_le_sum
      intro i hi
      calc
        dist (R (E.2 i).1) (R (E.2 i).2) ≤
            (K : ℝ) * dist (G (E.2 i).1) (G (E.2 i).2) :=
          hK.dist_le_mul _ (hmap (hE.1 i hi).1) _ (hmap (hE.1 i hi).2)
        _ = dist ((K : ℝ) * G (E.2 i).1) ((K : ℝ) * G (E.2 i).2) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
            abs_of_nonneg K.coe_nonneg]
  have hF : AbsolutelyContinuousOnInterval F 0 U := hA.mul hR
  have hArep : ∀ t ∈ Set.Icc (0 : ℝ) U,
      A t = remainingTarget c P a h t := by
    intro t ht
    have hleft : IntervalIntegrable target volume 0 t :=
      htarget.mono_set (by
        rw [Set.uIcc_of_le hU0, Set.uIcc_of_le ht.1]
        exact Set.Icc_subset_Icc le_rfl ht.2)
    have hright : IntervalIntegrable target volume t U :=
      htarget.mono_set (by
        rw [Set.uIcc_of_le hU0, Set.uIcc_of_le ht.2]
        exact Set.Icc_subset_Icc ht.1 le_rfl)
    have hrem := remainingTarget_integral_eq_sub c P a h 0 t
      (by simpa only [target] using hleft)
      (by simpa only [hU, target] using hright)
    dsimp only [A]
    linarith
  have hFrep : ∀ t ∈ Set.Icc (0 : ℝ) U,
      F t = remainingTarget c P a h t / survival P a t := by
    intro t ht
    rw [show F t = A t * R t by rfl, hArep t ht]
    simp only [R, G, survival, div_eq_mul_inv, Real.exp_neg, inv_inv]
  have hderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc (0 : ℝ) U),
      deriv F t = -(continuationWeight (holderOrder c) h t * P.lam a t) +
        remainingTarget c P a h t / survival P a t * P.hazard a t := by
    filter_upwards [ae_restrict_of_ae htarget.ae_hasDerivAt_integral,
      ae_restrict_of_ae hhaz.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_uIoc]
      with t htarg hhaz' ht
    have htu : t ∈ Set.uIcc (0 : ℝ) U := Set.uIoc_subset_uIcc ht
    have ht' : t ∈ Set.Icc (0 : ℝ) U := by
      simpa [Set.uIcc_of_le hU0] using htu
    have hAd : HasDerivAt A (-target t) t := by
      change HasDerivAt (fun u => remainingTarget c P a h 0 -
        ∫ v in (0 : ℝ)..u, target v) (-target t) t
      exact (htarg htu 0 (by simp [hU0])).const_sub
        (remainingTarget c P a h 0)
    have hGd : HasDerivAt G (P.hazard a t) t := by
      simpa only [G] using hhaz' htu 0 (by simp [hU0])
    have hRd : HasDerivAt R (R t * P.hazard a t) t := by
      change HasDerivAt (fun u => Real.exp (G u))
        (Real.exp (G t) * P.hazard a t) t
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (G t)).comp t hGd
    have hFd := hAd.mul hRd
    change deriv (fun u => A u * R u) t = _
    have hFd' := hFd.deriv
    change deriv (fun u => A u * R u) t =
      -target t * R t + A t * (R t * P.hazard a t) at hFd'
    rw [hFd']
    rw [hArep t ht']
    simp only [target]
    have hRrep : R t = (survival P a t)⁻¹ := by
      simp [R, G, survival, Real.exp_neg]
    rw [hRrep]
    have hspos : survival P a t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  calc
    _ = ∫ t in x..y, deriv F t := by
      symm
      apply intervalIntegral.integral_congr_ae_restrict
      have hsub : Set.uIoc x y ⊆ Set.uIoc (0 : ℝ) U := by
        rw [Set.uIoc_of_le hxy, Set.uIoc_of_le hU0]
        intro t ht
        exact ⟨hx.trans_lt ht.1, ht.2.trans hy⟩
      filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hderiv,
        ae_restrict_mem measurableSet_uIoc] with t hdt ht
      exact hdt
    _ = F y - F x := by
      apply (hF.mono (by
        rw [Set.uIcc_of_le hU0, Set.uIcc_of_le hxy]
        exact Set.Icc_subset_Icc hx hy)).integral_deriv_eq_sub
    _ = _ := by rw [hFrep y ⟨hx.trans hxy, hy⟩, hFrep x ⟨hx, hxy.trans hy⟩]

lemma remainingTarget_ratio_field_intervalIntegrable (c : ClassConstants)
    (P : SubjectLaw) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hBounds : DeathBounds c P) (a : Arm)
    {h T : ℝ} (hh : 0 ≤ h) (hT0 : 0 ≤ T) (hTU : T ≤ 1 - h) :
    IntervalIntegrable (fun t => continuationWeight (holderOrder c) h t *
      P.lam a t) volume 0 T ∧
    IntervalIntegrable (fun t => remainingTarget c P a h t /
      survival P a t * P.hazard a t) volume 0 T := by
  let U : ℝ := 1 - h
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  let A : ℝ → ℝ := fun t => remainingTarget c P a h 0 -
    ∫ u in (0 : ℝ)..t, target u
  have hU0 : 0 ≤ U := hT0.trans hTU
  have hU1 : U ≤ 1 := by dsimp [U]; linarith
  have htargetU : IntervalIntegrable target volume 0 U := by
    simpa only [target] using weightedTarget_intervalIntegrable
      c P hPoisson hDeath hBounds a hh hU0 hU1
  have htarget : IntervalIntegrable target volume 0 T :=
    htargetU.mono_set (by
      rw [Set.uIcc_of_le hU0, Set.uIcc_of_le hT0]
      exact Set.Icc_subset_Icc le_rfl hTU)
  have hhaz : IntervalIntegrable (P.hazard a) volume 0 T :=
    (hDeath.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
      exact Set.Icc_subset_Icc le_rfl (hTU.trans hU1))
  have hAac : AbsolutelyContinuousOnInterval A 0 U := by
    have hc : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => remainingTarget c P a h 0) 0 U := by
      rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      exact ⟨1, by norm_num, fun E _ _ => by simpa using hε⟩
    exact hc.sub (htargetU.absolutelyContinuousOnInterval_intervalIntegral
      (by simp [hU0] : (0 : ℝ) ∈ Set.uIcc 0 U))
  have hArep : ∀ t ∈ Set.Icc (0 : ℝ) U,
      A t = remainingTarget c P a h t := by
    intro t ht
    have hl : IntervalIntegrable target volume 0 t := htargetU.mono_set (by
      rw [Set.uIcc_of_le hU0, Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2)
    have hr : IntervalIntegrable target volume t U := htargetU.mono_set (by
      rw [Set.uIcc_of_le hU0, Set.uIcc_of_le ht.2]
      exact Set.Icc_subset_Icc ht.1 le_rfl)
    have hrem := remainingTarget_integral_eq_sub c P a h 0 t
      (by simpa only [target] using hl)
      (by simpa only [U, target] using hr)
    dsimp only [A]
    linarith
  have hH : ContinuousOn (remainingTarget c P a h) (Set.Icc (0 : ℝ) T) := by
    apply (hAac.continuousOn.mono (by
      rw [Set.uIcc_of_le hU0]
      exact Set.Icc_subset_Icc le_rfl hTU)).congr
    intro t ht
    exact (hArep t ⟨ht.1, ht.2.trans hTU⟩).symm
  have hprim : ContinuousOn (fun t : ℝ => ∫ u in (0 : ℝ)..t, P.hazard a u)
      (Set.Icc (0 : ℝ) T) := by
    simpa [Set.uIcc_of_le hT0] using
      (hhaz.absolutelyContinuousOnInterval_intervalIntegral
        (by simp [hT0] : (0 : ℝ) ∈ Set.uIcc 0 T)).continuousOn
  have hS : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) T) := by
    change ContinuousOn (fun t : ℝ => Real.exp (-(∫ u in (0 : ℝ)..t,
      P.hazard a u))) _
    exact Real.continuous_exp.comp_continuousOn hprim.neg
  have hinvS : ContinuousOn (fun t => (survival P a t)⁻¹) (Set.Icc (0 : ℝ) T) :=
    hS.inv₀ (fun t _ => (Real.exp_pos _).ne')
  have hfirst : IntervalIntegrable
      (fun t => continuationWeight (holderOrder c) h t * P.lam a t)
      volume 0 T := by
    apply (htarget.mul_continuousOn (by
      simpa [Set.uIcc_of_le hT0] using hinvS)).congr
    intro t ht
    have hs : survival P a t ≠ 0 := (Real.exp_pos _).ne'
    simp only [target]
    field_simp
  have hratio : ContinuousOn
      (fun t => remainingTarget c P a h t / survival P a t)
      (Set.Icc (0 : ℝ) T) := by
    exact hH.div hS (fun t _ => (Real.exp_pos _).ne')
  exact ⟨hfirst, hhaz.continuousOn_mul (by
    simpa [Set.uIcc_of_le hT0] using hratio)⟩

-- @node: riskSet_mul_invRisk

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
