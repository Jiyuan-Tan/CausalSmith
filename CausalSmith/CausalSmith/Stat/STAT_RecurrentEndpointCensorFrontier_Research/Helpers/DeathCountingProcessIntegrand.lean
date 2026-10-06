module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ErrorDecomposition
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathProductLaw
public import Causalean.Stat.RecurrentEvent.CountingProcess

/-!
# Predictable death Kaplan–Meier integrand on pair samples

This module builds the finite-sample product-limit factor and weighted death
integrand on the canonical counting-process sample used by the reference death
law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The strict-left death product on a canonical pair sample. On paths with
distinct death times this is the paper's grouped Kaplan–Meier product. -/
noncomputable def pairDeathKMLeft {n : ℕ} (t : ℝ)
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) : ℝ :=
  ∏ i : Fin n, if (x i).2 < t ∧ (x i).2 < (x i).1 then
    1 - Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk (x i).2 x else 1

/-- The pair-sample death product is jointly measurable in time and sample. -/
lemma pairDeathKMLeft_jointMeasurable {n : ℕ} :
    Measurable (fun p : ℝ × Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
      pairDeathKMLeft p.1 p.2) := by
  classical
  unfold pairDeathKMLeft
  apply Finset.measurable_prod _
  intro i _
  have hdeath : Measurable (fun p : ℝ ×
      Causalean.Stat.RecurrentEvent.CountingProcess.Sample n => (p.2 i).2) := by
    fun_prop
  have hfailure : Measurable (fun p : ℝ ×
      Causalean.Stat.RecurrentEvent.CountingProcess.Sample n => (p.2 i).1) := by
    fun_prop
  have hcond : MeasurableSet {p : ℝ ×
      Causalean.Stat.RecurrentEvent.CountingProcess.Sample n |
      (p.2 i).2 < p.1 ∧ (p.2 i).2 < (p.2 i).1} := by
    simpa only [Set.ofPred_and] using
      (measurableSet_lt hdeath measurable_fst).inter
        (measurableSet_lt hdeath hfailure)
  exact Measurable.ite hcond
    (measurable_const.sub
      (Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable.comp
      (hdeath.prodMk measurable_snd))) measurable_const

private lemma observedCensorTime_eq_of_histories {n : ℕ}
    {s : ℝ} {x y : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n}
    (hHist : ∀ (i : Fin n) t, t < s →
      Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i t x =
        Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i t y ∧
      Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i t x =
        Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i t y)
    (i : Fin n) (hx : (x i).2 < s ∧ (x i).2 < (x i).1) :
    (y i).2 = (x i).2 ∧ (y i).2 < (y i).1 := by
  have hAtX := (hHist i (x i).2 hx.1).1
  have hxCount : Causalean.Stat.RecurrentEvent.CountingProcess.censorCount
      i (x i).2 x = 1 := by
    simp [Causalean.Stat.RecurrentEvent.CountingProcess.censorCount, hx.2]
  have hyLe : (y i).2 ≤ (x i).2 ∧ (y i).2 < (y i).1 := by
    rw [hxCount] at hAtX
    by_contra h
    simp [Causalean.Stat.RecurrentEvent.CountingProcess.censorCount, h] at hAtX
  have hxy : (x i).2 ≤ (y i).2 := by
    by_contra hnot
    have hyx : (y i).2 < (x i).2 := lt_of_not_ge hnot
    let r := ((y i).2 + (x i).2) / 2
    have hyr : (y i).2 ≤ r := by dsimp [r]; linarith
    have hrx : r < (x i).2 := by dsimp [r]; linarith
    have hrs : r < s := hrx.trans hx.1
    have heq := (hHist i r hrs).1
    have hxZero : Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i r x = 0 := by
      simp [Causalean.Stat.RecurrentEvent.CountingProcess.censorCount, not_le.mpr hrx]
    have hyOne : Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i r y = 1 := by
      simp [Causalean.Stat.RecurrentEvent.CountingProcess.censorCount, hyr, hyLe.2]
    linarith
  exact ⟨le_antisymm hyLe.1 hxy, hyLe.2⟩

/-- The pair-sample strict-left death product is predictable from the strict
past of the canonical event histories. -/
lemma pairDeathKMLeft_leftPredictable {n : ℕ} :
    Causalean.Stat.RecurrentEvent.CountingProcess.LeftPredictable
      (pairDeathKMLeft (n := n)) := by
  classical
  intro s x y hHist
  have hRev : ∀ (i : Fin n) t, t < s →
      Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i t y =
        Causalean.Stat.RecurrentEvent.CountingProcess.censorCount i t x ∧
      Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i t y =
        Causalean.Stat.RecurrentEvent.CountingProcess.failureCount i t x := by
    intro i t ht
    exact ⟨((hHist i t ht).1).symm, ((hHist i t ht).2).symm⟩
  unfold pairDeathKMLeft
  apply Finset.prod_congr rfl
  intro i _
  by_cases hx : (x i).2 < s ∧ (x i).2 < (x i).1
  · obtain ⟨htime, hyEvent⟩ := observedCensorTime_eq_of_histories hHist i hx
    have hxyEvent : (x i).2 < (y i).1 := by simpa [htime] using hyEvent
    have hInv := Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_leftPredictable
      (s := (x i).2) x y
      (fun j t ht => hHist j t (ht.trans hx.1))
    simp only [hx, and_self, ↓reduceIte, htime, hxyEvent, hInv]
  · by_cases hy : (y i).2 < s ∧ (y i).2 < (y i).1
    · obtain ⟨htime, hxEvent⟩ := observedCensorTime_eq_of_histories hRev i hy
      exact False.elim (hx ⟨by simpa [htime] using hy.1, hxEvent⟩)
    · simp [hx, hy]

/-- The canonical zero-safe inverse risk lies in the unit interval. -/
lemma pairInverseRisk_mem_Icc {n : ℕ} (t : ℝ)
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) :
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x ∈
      Set.Icc (0 : ℝ) 1 := by
  by_cases hz : Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x = 0
  · simp [Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk, hz]
  · have hpos : (1 : ℝ) ≤
        Causalean.Stat.RecurrentEvent.CountingProcess.riskSet t x := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    simp only [Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk, hz,
      ↓reduceIte, Set.mem_Icc]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 hpos

/-- The pair-sample product-limit factor lies in the unit interval. -/
lemma pairDeathKMLeft_mem_Icc {n : ℕ} (t : ℝ)
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) :
    pairDeathKMLeft t x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold pairDeathKMLeft
  constructor
  · apply Finset.prod_nonneg
    intro i _
    split_ifs
    · linarith [(pairInverseRisk_mem_Icc (x i).2 x).2]
    · norm_num
  · apply Finset.prod_le_one
    · intro i _
      split_ifs
      · linarith [(pairInverseRisk_mem_Icc (x i).2 x).2]
      · norm_num
    · intro i _
      split_ifs
      · linarith [(pairInverseRisk_mem_Icc (x i).2 x).1]
      · norm_num


/-- The deterministic remaining-target/survival multiplier, extended by zero
outside the estimation horizon. -/
noncomputable def deathTargetWeight (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0 : ℝ) (1 - h) then
    remainingTarget c P a h t / survival P a t else 0

/-- On its estimation interval, the target multiplier is continuous. -/
lemma continuousOn_deathTargetWeight (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ContinuousOn (deathTargetWeight c P a h) (Set.Icc 0 (1 - h)) := by
  let U : ℝ := 1 - h
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  have htarget : IntervalIntegrable target volume 0 U := by
    simpa only [target] using weightedTarget_intervalIntegrable c P
      hP.poissonRecurrence hP.deathHazard hP.deathBounds a hh hU0
      (by dsimp [U]; linarith)
  have htargetOn : IntegrableOn target (Set.Icc (0 : ℝ) U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at htarget
  have hremaining : ContinuousOn (remainingTarget c P a h) (Set.Icc 0 U) := by
    change ContinuousOn (fun t => ∫ u in t..U, target u) (Set.Icc 0 U)
    simpa only [Set.uIcc_of_le hU0] using
      (intervalIntegral.continuousOn_primitive_interval_left
        (a := (0 : ℝ)) (b := U) (by
          simpa only [Set.uIcc_of_le hU0] using htargetOn))
  have hsurvival : ContinuousOn (survival P a) (Set.Icc 0 U) :=
    (modelClass_survival_continuousOn c P hP a).mono
      (Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hratio : ContinuousOn
      (fun t => remainingTarget c P a h t / survival P a t) (Set.Icc 0 U) :=
    hremaining.div hsurvival (fun t _ => (Real.exp_pos _).ne')
  apply hratio.congr
  intro t ht
  simp [deathTargetWeight, show t ∈ Set.Icc (0 : ℝ) (1 - h) by
    simpa only [U] using ht]

/-- On a valid horizon the extended death target weight is measurable. -/
lemma measurable_deathTargetWeight (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Measurable (deathTargetWeight c P a h) := by
  let U : ℝ := 1 - h
  let target : ℝ → ℝ := fun t => continuationWeight (holderOrder c) h t *
    survival P a t * P.lam a t
  have hU0 : 0 ≤ U := by dsimp [U]; linarith
  have htarget : IntervalIntegrable target volume 0 U := by
    simpa only [target] using weightedTarget_intervalIntegrable c P
      hP.poissonRecurrence hP.deathHazard hP.deathBounds a hh hU0
      (by dsimp [U]; linarith)
  have htargetOn : IntegrableOn target (Set.Icc (0 : ℝ) U) := by
    rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hU0] at htarget
  have htargetU : IntegrableOn target (Set.uIcc (0 : ℝ) U) := by
    simpa only [Set.uIcc_of_le hU0] using htargetOn
  have hremaining : ContinuousOn (remainingTarget c P a h) (Set.Icc (0 : ℝ) U) := by
    change ContinuousOn (fun t => ∫ u in t..U, target u) (Set.Icc (0 : ℝ) U)
    simpa only [Set.uIcc_of_le hU0] using
      (intervalIntegral.continuousOn_primitive_interval_left
        (a := (0 : ℝ)) (b := U) htargetU)
  have hsurvival : ContinuousOn (survival P a) (Set.Icc (0 : ℝ) U) :=
    (modelClass_survival_continuousOn c P hP a).mono
      (Set.Icc_subset_Icc le_rfl (by dsimp [U]; linarith))
  have hratio : ContinuousOn
      (fun t => remainingTarget c P a h t / survival P a t)
      (Set.Icc (0 : ℝ) U) :=
    hremaining.div hsurvival (fun t _ => (Real.exp_pos _).ne')
  unfold deathTargetWeight
  exact hratio.measurable_piecewise continuousOn_const measurableSet_Icc

/-- The predictable integrand whose compensated death integral gives the
paper's death-error term on regular sample paths. -/
noncomputable def deathCPIntegrand (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) {n : ℕ} (t : ℝ)
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) : ℝ :=
  deathTargetWeight c P a h t * pairDeathKMLeft t x *
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x

/-- The death counting-process integrand is left predictable. -/
lemma deathCPIntegrand_leftPredictable (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) {n : ℕ} :
    Causalean.Stat.RecurrentEvent.CountingProcess.LeftPredictable
      (deathCPIntegrand c P a h (n := n)) := by
  intro s x y hHist
  unfold deathCPIntegrand
  rw [pairDeathKMLeft_leftPredictable s x y hHist,
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_leftPredictable s x y hHist]

/-- The death counting-process integrand is jointly measurable. -/
lemma deathCPIntegrand_jointMeasurable (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    {n : ℕ} :
    Measurable (fun p : ℝ × Causalean.Stat.RecurrentEvent.CountingProcess.Sample n =>
      deathCPIntegrand c P a h p.1 p.2) := by
  unfold deathCPIntegrand
  exact (((measurable_deathTargetWeight c P hP a hh hh1).comp measurable_fst).mul
    pairDeathKMLeft_jointMeasurable).mul
    Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk_jointMeasurable

/-- The sample-dependent factors cannot enlarge the deterministic target
weight. -/
lemma deathCPIntegrand_abs_le (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (h : ℝ) {n : ℕ} (t : ℝ)
    (x : Causalean.Stat.RecurrentEvent.CountingProcess.Sample n) :
    |deathCPIntegrand c P a h t x| ≤ |deathTargetWeight c P a h t| := by
  rw [deathCPIntegrand, abs_mul, abs_mul]
  have hkm := pairDeathKMLeft_mem_Icc t x
  have hinv := pairInverseRisk_mem_Icc t x
  rw [abs_of_nonneg hkm.1, abs_of_nonneg hinv.1]
  calc
    |deathTargetWeight c P a h t| * pairDeathKMLeft t x *
        Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x
        ≤ |deathTargetWeight c P a h t| * 1 *
          Causalean.Stat.RecurrentEvent.CountingProcess.inverseRisk t x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkm.2 (abs_nonneg _)) hinv.1
    _ ≤ |deathTargetWeight c P a h t| * 1 * 1 :=
      mul_le_mul_of_nonneg_left hinv.2 (mul_nonneg (abs_nonneg _) zero_le_one)
    _ = |deathTargetWeight c P a h t| := by ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
