module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathCountingProcessFiniteRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FiniteJumpProductRule

/-!
# Fixed-horizon oracle control for the death Kaplan--Meier product

This module isolates the deterministic product-rule identity underlying a
fixed-horizon mean-square analysis of the empirical death survival curve.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The reciprocal paper survival has the hazard-over-survival integral as
its increment on every subinterval of the study window. -/
lemma inverseSurvival_integral_eq_sub (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {T x y : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ T) :
    (∫ t in x..y, P.hazard a t / survival P a t) =
      (survival P a y)⁻¹ - (survival P a x)⁻¹ := by
  let G : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, P.hazard a u
  let F : ℝ → ℝ := fun t => Real.exp (G t)
  have hhaz : IntervalIntegrable (P.hazard a) volume 0 T :=
    (hDeath.1 a).mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
      exact Set.Icc_subset_Icc le_rfl hT1)
  have hG : AbsolutelyContinuousOnInterval G 0 T :=
    hhaz.absolutelyContinuousOnInterval_intervalIntegral
      (by simp [hT0] : (0 : ℝ) ∈ Set.uIcc 0 T)
  have hF : AbsolutelyContinuousOnInterval F 0 T := by
    obtain ⟨C, hC⟩ := hG.exists_bound
    have hmap : Set.MapsTo G (Set.uIcc (0 : ℝ) T) (Set.Icc (-C) C) := by
      intro t ht
      have hb := hC t ht
      exact Set.mem_Icc.mpr (by simpa only [Real.norm_eq_abs, abs_le] using hb)
    obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K Real.exp (Set.Icc (-C) C) :=
      ((Real.contDiff_exp (n := 1)).contDiffOn).exists_lipschitzOnWith
        (by norm_num) (convex_Icc _ _) isCompact_Icc
    have hbound := hG.const_mul (K : ℝ)
    unfold AbsolutelyContinuousOnInterval at hbound ⊢
    apply squeeze_zero' ?_ ?_ (by simpa [F] using hbound)
    · exact Filter.Eventually.of_forall
        (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    · rw [Filter.eventually_inf_principal]
      filter_upwards with E hE
      apply Finset.sum_le_sum
      intro i hi
      calc
        dist (F (E.2 i).1) (F (E.2 i).2) ≤
            (K : ℝ) * dist (G (E.2 i).1) (G (E.2 i).2) :=
          hK.dist_le_mul _ (hmap (hE.1 i hi).1) _ (hmap (hE.1 i hi).2)
        _ = dist ((K : ℝ) * G (E.2 i).1) ((K : ℝ) * G (E.2 i).2) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
            abs_of_nonneg K.coe_nonneg]
  have hderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc (0 : ℝ) T),
      deriv F t = P.hazard a t / survival P a t := by
    filter_upwards [ae_restrict_of_ae hhaz.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_uIoc] with t ht htmem
    have hGd : HasDerivAt G (P.hazard a t) t := by
      simpa only [G] using ht (Set.uIoc_subset_uIcc htmem) 0 (by simp [hT0])
    have hFd : HasDerivAt F (F t * P.hazard a t) t := by
      change HasDerivAt (fun u => Real.exp (G u))
        (Real.exp (G t) * P.hazard a t) t
      simpa only [Function.comp_def] using (Real.hasDerivAt_exp (G t)).comp t hGd
    rw [hFd.deriv]
    simp only [F, G, survival, div_eq_mul_inv, Real.exp_neg, inv_inv]
    ring
  have hsub : Set.uIoc x y ⊆ Set.uIoc (0 : ℝ) T := by
    rw [Set.uIoc_of_le hxy, Set.uIoc_of_le hT0]
    intro t ht
    exact ⟨hx.trans_lt ht.1, ht.2.trans hy⟩
  calc
    _ = ∫ t in x..y, deriv F t := by
      symm
      apply intervalIntegral.integral_congr_ae_restrict
      exact ae_restrict_of_ae_restrict_of_subset hsub hderiv
    _ = F y - F x := by
      apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
      exact hF.mono (by
        rw [Set.uIcc_of_le hT0, Set.uIcc_of_le hxy]
        intro t ht
        exact ⟨hx.trans ht.1, ht.2.trans hy⟩)
    _ = _ := by simp [F, G, survival, Real.exp_neg]

/-- The fixed-horizon compensated death action whose product-rule endpoint is
the empirical Kaplan--Meier survival error. -/
noncomputable def deathKMOracleAction (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) (T : ℝ) : ℝ :=
  (∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
      (s i).exit ≤ T then
        deathKMLeft a s (s i).exit / survival P a (s i).exit *
          invRisk a s (s i).exit else 0) -
    ∫ t in (0 : ℝ)..T, deathKMLeft a s t / survival P a t *
      (if riskSet a s t = 0 then 0 else P.hazard a t)

/-- While the arm risk set remains positive through `T`, the Kaplan--Meier
endpoint error is exactly minus survival at `T` times its compensated oracle
action. -/
lemma deathKM_sub_survival_eq_neg_oracleAction (P : SubjectLaw)
    (hDeath : DeathHazard P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hExit0 : ∀ i : Fin n, 0 ≤ (s i).exit)
    (hRisk : riskSet a s T ≠ 0) :
    deathKM a s T - survival P a T =
      -(survival P a T * deathKMOracleAction P a s T) := by
  let F : ℝ → ℝ := fun t => (survival P a t)⁻¹
  let f : ℝ → ℝ := fun t => P.hazard a t / survival P a t
  have hf : IntervalIntegrable f volume 0 T := by
    have hhaz : IntegrableOn (P.hazard a) (Set.Ioc (0 : ℝ) T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp
        ((hDeath.1 a).mono_set (by
          rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
          exact Set.Icc_subset_Icc le_rfl hT1))
    have hhazI : IntervalIntegrable (P.hazard a) volume 0 T :=
      (hDeath.1 a).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIcc_of_le hT0]
        exact Set.Icc_subset_Icc le_rfl hT1)
    have hprim : ContinuousOn (fun t : ℝ => ∫ u in (0 : ℝ)..t, P.hazard a u)
        (Set.Icc (0 : ℝ) T) := by
      simpa [Set.uIcc_of_le hT0] using
        (hhazI.absolutelyContinuousOnInterval_intervalIntegral
          (by simp [hT0] : (0 : ℝ) ∈ Set.uIcc 0 T)).continuousOn
    have hsurv : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) T) := by
      change ContinuousOn (fun t : ℝ => Real.exp (-(∫ u in (0 : ℝ)..t,
        P.hazard a u))) _
      exact Real.continuous_exp.comp_continuousOn hprim.neg
    have hinv : ContinuousOn (fun t => (survival P a t)⁻¹)
        (Set.Icc (0 : ℝ) T) :=
      hsurv.inv₀ (fun t _ => (Real.exp_pos _).ne')
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hinv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    have hi : IntegrableOn (fun t => (survival P a t)⁻¹ * P.hazard a t)
        (Set.Ioc (0 : ℝ) T) := hhaz.bdd_mul
      (hinv.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
        measurableSet_Ioc (by
        intro t ht
        exact ⟨ht.1.le, ht.2⟩)) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hC t ⟨ht.1.le, ht.2⟩)
    simpa only [f, div_eq_mul_inv, mul_comm] using hi
  have hstep : IntervalIntegrable
      (fun t => deathKMLeft a s t * f t) volume 0 T :=
    deathKMLeft_mul_intervalIntegrable a s f hT0 hf
  have hprod := deathKM_finiteJumpProductRule_of_integral_eq_sub
    a s F f hT0 hExit0
      (fun x y hx hxy hy => inverseSurvival_integral_eq_sub
        P hDeath a hT0 hT1 hx hxy hy) hstep
  have hRiskAll (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) T) :
      riskSet a s t ≠ 0 := by
    rw [Set.uIcc_of_le hT0] at ht
    intro hz
    have hmono : riskSet a s T ≤ riskSet a s t := by
      unfold riskSet
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hi.1, ht.2.trans hi.2⟩
    exact hRisk (Nat.eq_zero_of_le_zero (hz ▸ hmono))
  have hsum :
      (∑ u ∈ (exitTimes s).filter (fun u => u ≤ T),
        deathKMLeft a s u *
          ((1 - invRisk a s u * deathJump a s u) - 1) * F u) =
      -(∑ i : Fin n, if (s i).treatment = a ∧ (s i).deathInd ∧
          (s i).exit ≤ T then deathKMLeft a s (s i).exit /
            survival P a (s i).exit * invRisk a s (s i).exit else 0) := by
    calc
      _ = -(∑ u ∈ (exitTimes s).filter (fun u => u ≤ T),
          (deathKMLeft a s u / survival P a u * invRisk a s u) *
            deathJump a s u) := by
        simp only [F]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = _ := by
        rw [exitTimes_sum_deathJump a s
          (fun u => deathKMLeft a s u / survival P a u * invRisk a s u) T]
  have hint :
      (∫ t in (0 : ℝ)..T, deathKMLeft a s t * f t) =
      ∫ t in (0 : ℝ)..T, deathKMLeft a s t / survival P a t *
        (if riskSet a s t = 0 then 0 else P.hazard a t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [f]
    rw [if_neg (hRiskAll t ht)]
    ring
  rw [hsum, hint] at hprod
  have hF0 : F 0 = 1 := by simp [F, survival]
  have hsT : survival P a T ≠ 0 := (Real.exp_pos _).ne'
  unfold deathKMOracleAction
  rw [hF0] at hprod
  dsimp [F] at hprod
  field_simp [hsT] at hprod ⊢
  linarith

namespace DeathCP

/-- The deterministic reciprocal-survival multiplier for a fixed endpoint. -/
noncomputable def kmOracleWeight (P : SubjectLaw) (a : Arm) (T t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0 : ℝ) T then survival P a T / survival P a t else 0

/-- The canonical predictable integrand representing the fixed-horizon
Kaplan--Meier oracle action. -/
noncomputable def kmOracleIntegrand (P : SubjectLaw) (a : Arm) (T : ℝ)
    {n : ℕ} (t : ℝ) (x : Sample n) : ℝ :=
  kmOracleWeight P a T t * pairDeathKMLeft t x *
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x

/-- The fixed-horizon oracle integrand is left predictable. -/
lemma kmOracleIntegrand_leftPredictable (P : SubjectLaw) (a : Arm) (T : ℝ)
    {n : ℕ} :
    Causalean.Stat.RecurrentEvent.CountingProcess.LeftPredictable
      (kmOracleIntegrand P a T (n := n)) := by
  intro t x y hHist
  unfold kmOracleIntegrand
  rw [pairDeathKMLeft_leftPredictable t x y hHist,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_leftPredictable
      t x y hHist]

/-- The reciprocal-survival multiplier is measurable for model-class laws. -/
lemma measurable_kmOracleWeight (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) : Measurable (kmOracleWeight P a T) := by
  have hsurv : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) T) :=
    (modelClass_survival_continuousOn c P hP a).mono
      (Set.Icc_subset_Icc le_rfl hT1)
  have hratio : ContinuousOn
      (fun t => survival P a T / survival P a t) (Set.Icc (0 : ℝ) T) :=
    continuousOn_const.div hsurv (fun t _ => (Real.exp_pos _).ne')
  unfold kmOracleWeight
  exact hratio.measurable_piecewise continuousOn_const measurableSet_Icc

/-- The fixed-horizon oracle integrand is jointly measurable. -/
lemma kmOracleIntegrand_jointMeasurable (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) {n : ℕ} :
    Measurable (fun p : ℝ × Sample n => kmOracleIntegrand P a T p.1 p.2) := by
  unfold kmOracleIntegrand
  exact (((measurable_kmOracleWeight c P hP a hT0 hT1).comp measurable_fst).mul
    pairDeathKMLeft_jointMeasurable).mul
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable

/-- On the fixed study window, the deterministic oracle multiplier is bounded
by the inverse model-class survival floor. -/
lemma kmOracleWeight_abs_le_exp (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {T t : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) : |kmOracleWeight P a T t| ≤ Real.exp c.dMax := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · have hsTpos : 0 < survival P a T := Real.exp_pos _
    have hstpos : 0 < survival P a t := Real.exp_pos _
    rw [kmOracleWeight, if_pos ht, abs_div,
      abs_of_pos hsTpos, abs_of_pos hstpos]
    have hsT := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨hT0, hT1⟩).2
    have hst := (survival_bounds_of_deathBounds c P hP.deathBounds a
      ⟨ht.1, ht.2.trans hT1⟩).1
    have hpos : 0 < survival P a t := Real.exp_pos _
    calc
      survival P a T / survival P a t ≤ 1 / Real.exp (-c.dMax) :=
        div_le_div₀ zero_le_one hsT (Real.exp_pos _) hst
      _ = Real.exp c.dMax := by rw [Real.exp_neg]; simp
  · simp [kmOracleWeight, ht, Real.exp_pos _ |>.le]

/-- The quadratic-energy density is bounded by the deterministic survival
envelope times the zero-safe inverse risk. -/
lemma kmOracle_energyDensity_le (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {T : ℝ} (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) {n : ℕ} (t : ℝ) (x : Sample n) :
    (kmOracleIntegrand P a T t x) ^ 2 * referenceDeathHazard P a t *
        (∑ i : Fin n,
          Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x) ≤
      (Real.exp c.dMax) ^ 2 * referenceDeathHazard P a t *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
  have hkm := pairDeathKMLeft_mem_Icc t x
  have hrisk :=
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_square_risk t x
  have hweight := kmOracleWeight_abs_le_exp c P hP a hT0 hT1 (t := t)
  have hwSq : (kmOracleWeight P a T t) ^ 2 ≤ (Real.exp c.dMax) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (kmOracleWeight P a T t))
      (Real.exp_pos c.dMax).le).2 hweight
    simpa only [sq_abs] using hs
  have hkmSq : (pairDeathKMLeft t x) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hkm.1 (sub_nonneg.mpr hkm.2)]
  have hhaz : 0 ≤ referenceDeathHazard P a t :=
    referenceDeathHazard_nonneg hP a t
  rw [kmOracleIntegrand]
  calc
    _ = (kmOracleWeight P a T t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        referenceDeathHazard P a t *
          ((Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x) ^ 2 *
            (∑ i : Fin n,
              Causalean.Stat.RecurrentEvent.CountingProcess.riskIndicator i t x)) := by
      ring
    _ = (kmOracleWeight P a T t) ^ 2 * (pairDeathKMLeft t x) ^ 2 *
        referenceDeathHazard P a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      rw [hrisk]
    _ ≤ (Real.exp c.dMax) ^ 2 * 1 * referenceDeathHazard P a t *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x := by
      gcongr
      exact (pairInverseRisk_mem_Icc t x).1
    _ = _ := by ring

end DeathCP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
