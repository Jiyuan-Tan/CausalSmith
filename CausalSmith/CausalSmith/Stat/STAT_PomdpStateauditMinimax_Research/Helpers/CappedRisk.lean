module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.Transfer

/-! # Bounded real-risk bridges for the capped audited experiment. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

-- @node: targetValue_mem_unit_hw
/-- Every Hu--Wager model has target value in the unit interval. -/
lemma targetValue_mem_unit_hw {T nX nH k : Nat} {t0 zeta : ℝ}
    {M : PomdpModel T nX nH k} (hM : HuWagerClass t0 zeta M) :
    targetValue M ∈ Set.Icc (-1 : ℝ) 1 := by
  have hd := (target_stationary_law_of_class M hM.t0_pos hM).1
  have hregr (s : JointState nX nH) : |rewardRegression M s| ≤ 1 := by
    unfold rewardRegression
    calc
      |∑ a : Fin k, M.e s.1 a * ∫ q, q.1 ∂(M.K s a)| ≤
          ∑ a : Fin k, |M.e s.1 a * ∫ q, q.1 ∂(M.K s a)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : Fin k, M.e s.1 a * |∫ q, q.1 ∂(M.K s a)| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul, abs_of_nonneg ((hM.overlap.1 s.1).1 a)]
      _ ≤ ∑ a : Fin k, M.e s.1 a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hM.moment s a).2.2.1
          ((hM.overlap.1 s.1).1 a)
      _ = 1 := by simpa using (hM.overlap.1 s.1).2
  have habs : |targetValue M| ≤ 1 := by
    unfold targetValue
    calc
      |∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s| ≤
          ∑ s, |stationaryLaw (policyKernel M M.e) s * rewardRegression M s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s, stationaryLaw (policyKernel M M.e) s * |rewardRegression M s| := by
        apply Finset.sum_congr rfl
        intro s _
        rw [abs_mul, abs_of_nonneg (hd.1 s)]
      _ ≤ ∑ s, stationaryLaw (policyKernel M M.e) s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hregr s) (hd.1 s)
      _ = 1 := by simpa using hd.2
  exact abs_le.mp habs

-- @node: auditedRisk_nonneg
/-- Audited squared risk is nonnegative. -/
lemma auditedRisk_nonneg {T : Nat} {t0 zeta eta : ℝ}
    (est : AuditedEstimator T) (i : HWIndex T t0 zeta) :
    0 ≤ auditedRisk eta est i := by
  exact integral_nonneg fun _ => sq_nonneg _

-- @node: auditedRisk_le_four
/-- Bounded audited estimators have squared risk at most four. -/
lemma auditedRisk_le_four {T : Nat} {t0 zeta eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T)
    (i : HWIndex T t0 zeta) : auditedRisk eta est i ≤ 4 := by
  let f : AuditedRecord T i.nX i.nH i.k → ℝ :=
    fun w => (est.1 i.nX i.nH i.k i.raw.b i.raw.e w - targetValue i.raw) ^ 2
  have hf (w : AuditedRecord T i.nX i.nH i.k) : f w ≤ 4 := by
    rcases est.2.2 i.nX i.nH i.k i.raw.b i.raw.e w with ⟨hel, heu⟩
    rcases targetValue_mem_unit_hw i.mem with ⟨htl, htu⟩
    dsimp [f]
    nlinarith [mul_nonneg
      (show 0 ≤ est.1 i.nX i.nH i.k i.raw.b i.raw.e w - targetValue i.raw + 2 by
        linarith)
      (show 0 ≤ 2 - (est.1 i.nX i.nH i.k i.raw.b i.raw.e w - targetValue i.raw) by
        linarith)]
  have hmeas : Measurable f := by
    dsimp [f]
    exact ((est.2.1 i.nX i.nH i.k i.raw.b i.raw.e).sub measurable_const).pow_const 2
  letI : IsProbabilityMeasure (auditedLaw eta i.raw) := auditedLaw_prob i.raw eta heta
  have hint : Integrable f (auditedLaw eta i.raw) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 4
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hf w
  unfold auditedRisk Causalean.Stat.sqRisk
  calc
    ∫ w, f w ∂(auditedLaw eta i.raw) ≤
        ∫ _w : AuditedRecord T i.nX i.nH i.k, (4 : ℝ) ∂(auditedLaw eta i.raw) :=
      integral_mono hint (integrable_const 4) hf
    _ = 4 := by simp

-- @node: bddAbove_range_cappedAuditedRisk
/-- Every estimator's capped audited-risk range is bounded above. -/
lemma bddAbove_range_cappedAuditedRisk {T N : Nat} {t0 zeta eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T) :
    BddAbove (Set.range (fun (i : {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N}) =>
      auditedRisk eta est i.1)) := by
  refine ⟨4, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact auditedRisk_le_four heta est i.1

-- @node: sqRiskLIntegral_eq_ofReal_sqRisk
/-- For an integrable squared loss, extended and real squared risk agree. -/
lemma sqRiskLIntegral_eq_ofReal_sqRisk {X : Type*} [MeasurableSpace X]
    (P : Measure X) (est : X → ℝ) (theta : ℝ)
    (hint : Integrable (fun x => (est x - theta) ^ 2) P) :
    Causalean.Stat.sqRiskLIntegral P est theta =
      ENNReal.ofReal (Causalean.Stat.sqRisk P est theta) := by
  unfold Causalean.Stat.sqRiskLIntegral Causalean.Stat.sqRisk
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => sq_nonneg (est x - theta))).symm

end CausalSmith.Stat.PomdpStateauditMinimax
