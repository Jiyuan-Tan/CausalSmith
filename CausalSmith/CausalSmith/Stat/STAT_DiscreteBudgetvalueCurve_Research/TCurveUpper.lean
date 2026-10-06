module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TIntegratedProcessCertificate
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TDualRepresentation
public import Causalean.Stat.Sample.EmpiricalMass

/-! Uniform risk bound for the explicit total curve estimator. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

/-- The four-mass plug-in coordinate is the ordinary empirical mass of its atom. With [the specified inputs and conditions](hyp:n,d,sample,j,z), [the stated relationship holds](goal). -/
-- @node: empiricalCellVector_eq_empiricalMass
lemma empiricalCellVector_eq_empiricalMass {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin d) (z : Cell) :
    empiricalCellVector sample j z =
      Causalean.Stat.empiricalMass sample
        (j, finTwoEquiv z.1, finTwoEquiv z.2) := by
  classical
  unfold empiricalCellVector Causalean.Stat.empiricalMass
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hiff : ((sample i).1 = j ∧ (sample i).2.1 = finTwoEquiv z.1 ∧
      (sample i).2.2 = finTwoEquiv z.2) ↔
      sample i = (j, finTwoEquiv z.1, finTwoEquiv z.2) := by
    cases sample i with
    | mk x ay =>
      cases ay with
      | mk av yv => simp [Prod.mk.injEq]
  by_cases h : sample i = (j, finTwoEquiv z.1, finTwoEquiv z.2) <;>
    simp [h, hiff]

/-- Each plug-in four-mass coordinate has mean-square error at most `1/n`. With [the specified inputs and conditions](hyp:n,d,P,hn,j,z), [the stated relationship holds](goal). -/
-- @node: empiricalCellVector_sq_integral_le
lemma empiricalCellVector_sq_integral_le {n d : ℕ}
    (P : DiscreteLaw d) (hn : 1 ≤ n) (j : Fin d) (z : Cell) :
    (∫ sample : Fin n → Obs d,
      (empiricalCellVector sample j z - cellVector P j z) ^ 2
      ∂productLaw P n) ≤ 1 / (n : ℝ) := by
  classical
  let a : Obs d := (j, finTwoEquiv z.1, finTwoEquiv z.2)
  let p : ℝ := (obsLaw P).real {a}
  have hmean : (∫ sample : Fin n → Obs d,
      Causalean.Stat.empiricalMass sample a ∂productLaw P n) = p := by
    exact Causalean.Stat.integral_empiricalMass (obsLaw P) hn a (MeasurableSet.singleton a)
  have hsq : (∫ sample : Fin n → Obs d,
      Causalean.Stat.empiricalMass sample a ^ 2 ∂productLaw P n) =
        p ^ 2 + (n : ℝ)⁻¹ * (p - p ^ 2) := by
    exact Causalean.Stat.integral_empiricalMass_sq (obsLaw P) hn a
      (MeasurableSet.singleton a)
  have hcell : cellVector P j z = p := by
    change (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal = _
    simp [p, a, obsLaw, Measure.real]
  have hprob : 0 ≤ p ∧ p ≤ 1 := by
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hcell]
  simp_rw [empiricalCellVector_eq_empiricalMass]
  calc
    (∫ sample : Fin n → Obs d,
      (Causalean.Stat.empiricalMass sample a - p) ^ 2 ∂productLaw P n) =
        (n : ℝ)⁻¹ * (p - p ^ 2) := by
      simp_rw [sub_sq]
      have hlin :
          (∫ sample : Fin n → Obs d,
              Causalean.Stat.empiricalMass sample a ^ 2 -
                2 * Causalean.Stat.empiricalMass sample a * p + p ^ 2
                ∂productLaw P n) =
            (∫ sample : Fin n → Obs d,
              Causalean.Stat.empiricalMass sample a ^ 2 ∂productLaw P n) -
              2 * (∫ sample : Fin n → Obs d,
                Causalean.Stat.empiricalMass sample a ∂productLaw P n) * p + p ^ 2 := by
        haveI : IsProbabilityMeasure (productLaw P n) := by
          unfold productLaw
          infer_instance
        rw [integral_add (Integrable.of_finite) (integrable_const _),
          integral_sub (Integrable.of_finite) (Integrable.of_finite),
          integral_mul_const, integral_const_mul, integral_const]
        simp
      rw [hlin, hsq, hmean]
      ring
    _ ≤ 1 / (n : ℝ) := by
      rw [one_div]
      calc
        (n : ℝ)⁻¹ * (p - p ^ 2) ≤ (n : ℝ)⁻¹ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnreal.le)
          nlinarith [sq_nonneg p]
        _ = (n : ℝ)⁻¹ := by ring

/-- Cellwise Lipschitz control of the empirical threshold process. With [the specified inputs and conditions](hyp:n,d,epsilon,he,P,sample,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: empiricalThresholdProcess_error_le
lemma empiricalThresholdProcess_error_le {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    |empiricalThresholdProcess epsilon sample lambda -
        dualProcessReal epsilon P lambda| ≤
      (3 * (1 + epsilon⁻¹) + 1) *
        ∑ j : Fin d, ∑ z : Cell,
          |empiricalCellVector sample j z - cellVector P j z| := by
  have hnonneg (j : Fin d) (z : Cell) :
      0 ≤ empiricalCellVector sample j z := by
    unfold empiricalCellVector
    positivity
  have htrue (j : Fin d) (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hcell (j : Fin d) :
      |thresholdFunReal epsilon lambda (empiricalCellVector sample j) -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤
      (3 * (1 + epsilon⁻¹) + 1) *
        ∑ z : Cell,
          |empiricalCellVector sample j z - cellVector P j z| :=
    budget_thresholdFunReal_pointwise_lipschitz he lambda hlambda _ _
      (hnonneg j) (htrue j)
  have hsum :
      |∑ j : Fin d, (thresholdFunReal epsilon lambda (empiricalCellVector sample j) -
        thresholdFunReal epsilon lambda (cellVector P j))| ≤
      ∑ j : Fin d,
        (3 * (1 + epsilon⁻¹) + 1) *
          ∑ z : Cell,
            |empiricalCellVector sample j z - cellVector P j z| := by
    calc
      _ ≤ ∑ j : Fin d,
          |thresholdFunReal epsilon lambda (empiricalCellVector sample j) -
            thresholdFunReal epsilon lambda (cellVector P j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hcell j)
  simpa [empiricalThresholdProcess, dualProcessReal, dualProcess,
    thresholdFunReal, hlambda, Finset.sum_sub_distrib,
    Finset.mul_sum] using hsum

/-- The empirical threshold process has uniform squared risk of order `d²/n`. With [the specified inputs and conditions](hyp:n,d,epsilon,he,P,hn), [the stated relationship holds](goal). -/
-- @node: empiricalThresholdProcess_uniformRisk_le
lemma empiricalThresholdProcess_uniformRisk_le {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (P : DiscreteLaw d) (hn : 1 ≤ n) :
    (∫ sample : Fin n → Obs d,
      (sSup ((fun lambda : ℝ =>
        |empiricalThresholdProcess epsilon sample lambda -
          dualProcessReal epsilon P lambda|) '' Set.Icc 0 1)) ^ 2
      ∂productLaw P n) ≤
      16 * (d : ℝ) ^ 2 * (3 * (1 + epsilon⁻¹) + 1) ^ 2 / n := by
  let K := 3 * (1 + epsilon⁻¹) + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcard : Fintype.card (Fin d × Cell) = 4 * d := by
    simp [Cell]
    ring
  have hpoint (sample : Fin n → Obs d) :
      (sSup ((fun lambda : ℝ =>
        |empiricalThresholdProcess epsilon sample lambda -
          dualProcessReal epsilon P lambda|) '' Set.Icc 0 1)) ^ 2 ≤
        K ^ 2 * (4 * (d : ℝ)) *
          ∑ j : Fin d, ∑ z : Cell,
            (empiricalCellVector sample j z - cellVector P j z) ^ 2 := by
    let S := ∑ j : Fin d, ∑ z : Cell,
      |empiricalCellVector sample j z - cellVector P j z|
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    have hsup :
        sSup ((fun lambda : ℝ =>
          |empiricalThresholdProcess epsilon sample lambda -
            dualProcessReal epsilon P lambda|) '' Set.Icc 0 1) ≤ K * S := by
      apply csSup_le
      · exact ⟨_, 0, by norm_num, rfl⟩
      · rintro _ ⟨lambda, hlambda, rfl⟩
        exact empiricalThresholdProcess_error_le he P sample lambda hlambda
    have hsup0 : 0 ≤ sSup ((fun lambda : ℝ =>
        |empiricalThresholdProcess epsilon sample lambda -
          dualProcessReal epsilon P lambda|) '' Set.Icc 0 1) := by
      have hb : BddAbove ((fun lambda : ℝ =>
          |empiricalThresholdProcess epsilon sample lambda -
            dualProcessReal epsilon P lambda|) '' Set.Icc 0 1) := by
        refine ⟨K * S, ?_⟩
        rintro _ ⟨lambda, hlambda, rfl⟩
        exact empiricalThresholdProcess_error_le he P sample lambda hlambda
      calc
        0 ≤ |empiricalThresholdProcess epsilon sample 0 -
            dualProcessReal epsilon P 0| := abs_nonneg _
        _ ≤ _ := le_csSup hb (show
          |empiricalThresholdProcess epsilon sample 0 -
            dualProcessReal epsilon P 0| ∈
            ((fun lambda : ℝ =>
              |empiricalThresholdProcess epsilon sample lambda -
                dualProcessReal epsilon P lambda|) '' Set.Icc 0 1) from
                  ⟨0, by norm_num, rfl⟩)
    have hcs : S ^ 2 ≤ 4 * (d : ℝ) *
        ∑ j : Fin d, ∑ z : Cell,
          (empiricalCellVector sample j z - cellVector P j z) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d × Cell)))
        (f := fun x => |empiricalCellVector sample x.1 x.2 - cellVector P x.1 x.2|)
      simpa [S, ← Finset.univ_product_univ, Finset.sum_product, hcard,
        sq_abs, mul_comm (d : ℝ) 4] using h
    calc
      _ ≤ (K * S) ^ 2 := by nlinarith
      _ = K ^ 2 * S ^ 2 := by ring
      _ ≤ K ^ 2 * (4 * (d : ℝ) *
          ∑ j : Fin d, ∑ z : Cell,
            (empiricalCellVector sample j z - cellVector P j z) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcs (sq_nonneg K)
      _ = _ := by ring
  calc
    _ ≤ ∫ sample : Fin n → Obs d,
        K ^ 2 * (4 * (d : ℝ)) *
          ∑ j : Fin d, ∑ z : Cell,
            (empiricalCellVector sample j z - cellVector P j z) ^ 2
        ∂productLaw P n := by
          exact integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = K ^ 2 * (4 * (d : ℝ)) *
        ∑ j : Fin d, ∑ z : Cell,
          (∫ sample : Fin n → Obs d,
            (empiricalCellVector sample j z - cellVector P j z) ^ 2
            ∂productLaw P n) := by
          rw [integral_const_mul]
          congr 1
          rw [integral_finsetSum Finset.univ (by
            intro j _
            exact integrable_finsetSum Finset.univ (fun z _ => Integrable.of_finite))]
          apply Finset.sum_congr rfl
          intro j _
          rw [integral_finsetSum Finset.univ (by
            intro z _
            exact Integrable.of_finite)]
    _ ≤ K ^ 2 * (4 * (d : ℝ)) *
        ∑ j : Fin d, ∑ _z : Cell, (1 / (n : ℝ)) := by
          gcongr
          exact empiricalCellVector_sq_integral_le P hn _ _
    _ = 16 * (d : ℝ) ^ 2 * K ^ 2 / n := by
          simp [Fintype.card_fin, Fintype.card_prod, Cell]
          ring

/-- The empirical threshold path is bounded on the price interval. With [the specified inputs and conditions](hyp:n,d,epsilon,sample), [the stated relationship holds](goal). -/
-- @node: empiricalThresholdProcess_bounded
lemma empiricalThresholdProcess_bounded {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) :
    ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      |empiricalThresholdProcess epsilon sample lambda| ≤ B := by
  have hc : Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      empiricalThresholdProcess epsilon sample lambda) := by
    unfold empiricalThresholdProcess
    apply continuous_finsetSum
    intro j _
    exact thresholdFunReal_continuous_time epsilon (empiricalCellVector sample j)
  obtain ⟨B, hB⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) 1))).exists_bound_of_continuousOn
      (f := fun lambda : Set.Icc (0 : ℝ) 1 =>
        empiricalThresholdProcess epsilon sample lambda) hc.continuousOn
  refine ⟨B, ?_⟩
  intro lambda hlambda
  simpa only [Real.norm_eq_abs] using hB ⟨lambda, hlambda⟩ (Set.mem_univ _)

/-- The averaged threshold path is bounded on the price interval. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,sample), [the stated relationship holds](goal). -/
-- @node: averagedThresholdProcess_bounded
lemma averagedThresholdProcess_bounded {n d : ℕ} (epsilon : ℝ)
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (sample : Fin n → Obs d) :
    ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      |averagedThresholdProcess epsilon sample lambda| ≤ B := by
  have hcell (pilot eval : Cell → ℕ) :
      Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
        jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d pilot eval) := by
    apply jacksonCellStatistic_continuous_time
    intro lambda
    apply pilotRectangle_threshold_pullback_continuousOn he
    · have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    · exact hd
  have hc : Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      averagedThresholdProcess epsilon sample lambda) := by
    unfold averagedThresholdProcess cappedThresholdProcess auxiliaryThresholdProcess
    apply continuous_finsetSum
    intro M _
    apply Continuous.mul continuous_const
    apply Continuous.div_const
    apply continuous_finsetSum
    intro perm _
    apply continuous_finsetSum
    intro marks _
    split_ifs
    · apply continuous_finsetSum
      intro j _
      exact hcell _ _
    · exact continuous_const
  obtain ⟨B, hB⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) 1))).exists_bound_of_continuousOn
      (f := fun lambda : Set.Icc (0 : ℝ) 1 => averagedThresholdProcess epsilon sample lambda)
      hc.continuousOn
  refine ⟨B, ?_⟩
  intro lambda hlambda
  simpa only [Real.norm_eq_abs] using hB ⟨lambda, hlambda⟩ (Set.mem_univ _)

/-- Projection to the unit interval contracts distance to a unit-interval target. With [the specified inputs and conditions](hyp:x,y,hy), [the stated relationship holds](goal). -/
-- @node: clip_unit_distance_le
lemma clip_unit_distance_le (x y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |min 1 (max 0 x) - y| ≤ |x - y| := by
  rcases le_total x 0 with hx | hx
  · simp only [max_eq_left hx, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
      zero_sub, abs_neg]
    rw [abs_of_nonneg hy.1, abs_of_nonpos (by linarith [hy.1])]
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · simp [max_eq_right hx, min_eq_right hx1]
    · simp only [max_eq_right hx, min_eq_left hx1]
      rw [abs_of_nonneg (by linarith [hy.2]), abs_of_nonneg (by linarith [hy.2])]
      linarith

/-- A bounded threshold path gives a lower-bounded dual objective. With [the specified inputs and conditions](hyp:F,b,B,hb,hB), [the stated relationship holds](goal). -/
-- @node: dualObjective_bddBelow_of_bounded
lemma dualObjective_bddBelow_of_bounded (F : ℝ → ℝ) (b B : ℝ)
    (hb : 0 ≤ b) (hB : ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda| ≤ B) :
    BddBelow ((fun lambda : ℝ => b * lambda + F lambda) '' Set.Icc 0 1) := by
  refine ⟨-B, ?_⟩
  rintro y ⟨lambda, hlambda, rfl⟩
  have hlow := (abs_le.mp (hB lambda hlambda)).1
  nlinarith [mul_nonneg hb hlambda.1]

/-- Dual minimization and clipping transfer a uniform price-path error to curve loss. With [the specified inputs and conditions](hyp:d,epsilon,b0,he,he',hd,hb0,Q,hQ,F,hF), [the stated relationship holds](goal). -/
-- @node: clippedDualCurveLoss_le_processError
lemma clippedDualCurveLoss_le_processError {d : ℕ} (epsilon b0 : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hd : 2 ≤ d) (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (Q : PotentialLaw d) (hQ : CausalModelClass epsilon Q)
    (F : ℝ → ℝ)
    (hF : ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda| ≤ B) :
    (⨆ b : Set.Icc b0 (1 - b0),
      (min 1 (max 0 (dualMinimum b.1 F)) - budgetValue Q b.1) ^ 2) ≤
      (sSup ((fun lambda : ℝ =>
        |F lambda - dualProcessReal epsilon (observedMarginal Q) lambda|) ''
          Set.Icc 0 1)) ^ 2 := by
  let G := dualProcessReal epsilon (observedMarginal Q)
  let M := sSup ((fun lambda : ℝ => |F lambda - G lambda|) '' Set.Icc 0 1)
  obtain ⟨BF, hBF⟩ := hF
  obtain ⟨BG, hBG⟩ := dualProcessReal_bounded epsilon (observedMarginal Q)
  have hMbdd : BddAbove ((fun lambda : ℝ => |F lambda - G lambda|) '' Set.Icc 0 1) := by
    refine ⟨BF + BG, ?_⟩
    rintro x ⟨lambda, hlambda, rfl⟩
    calc
      |F lambda - G lambda| ≤ |F lambda| + |G lambda| := by
        simpa using (abs_sub_le (F lambda) 0 (G lambda))
      _ ≤ BF + BG := add_le_add (hBF lambda hlambda) (hBG lambda hlambda)
  have hMnonneg : 0 ≤ M := by
    have h := le_csSup hMbdd (show |F 0 - G 0| ∈
      ((fun lambda : ℝ => |F lambda - G lambda|) '' Set.Icc 0 1) from
        ⟨0, by norm_num, rfl⟩)
    exact (abs_nonneg _).trans h
  have hval := (dual_representation epsilon Q hd hQ he he').1
  let : Nonempty (Set.Icc b0 (1 - b0)) :=
    ⟨⟨b0, ⟨le_refl _, by linarith [hb0.2]⟩⟩⟩
  apply ciSup_le
  intro b
  have hb : b.1 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hb0.1.trans b.2.1, b.2.2.trans (by linarith [hb0.1])⟩
  have hpoint : ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda - G lambda| ≤ M := by
    intro lambda hlambda
    exact le_csSup hMbdd ⟨lambda, hlambda, rfl⟩
  have hmin := dualMinimum_lipschitz b.1 F G M
    (dualObjective_bddBelow_of_bounded F b.1 BF hb.1 hBF)
    (dualObjective_bddBelow_of_bounded G b.1 BG hb.1 hBG) hpoint
  have hclip := clip_unit_distance_le (dualMinimum b.1 F)
    (budgetValue Q b.1) (budgetValue_unit_interval Q b.1 hb)
  rw [hval b.1 hb] at hclip ⊢
  change (min 1 (max 0 (dualMinimum b.1 F)) - dualMinimum b.1 G) ^ 2 ≤ M ^ 2
  have habs : |min 1 (max 0 (dualMinimum b.1 F)) - dualMinimum b.1 G| ≤ M :=
    hclip.trans hmin
  let a := min 1 (max 0 (dualMinimum b.1 F)) - dualMinimum b.1 G
  have hprod : 0 ≤ (M - |a|) * (M + |a|) :=
    mul_nonneg (sub_nonneg.mpr habs) (add_nonneg hMnonneg (abs_nonneg a))
  nlinarith [sq_abs a]

/-- The nonconstant estimator branch inherits the threshold-process loss. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,he,he',hn,hd,hb0,hbranch,Q,hQ,sample), [the stated relationship holds](goal). -/
-- @node: jfEstimator_curveLoss_le_processError
lemma jfEstimator_curveLoss_le_processError {n d : ℕ} (epsilon b0 : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hbranch : ¬(d ≥ boundedAlphabetCutoff ∧ n < (d : ℝ) / logAlphabet d))
    (Q : PotentialLaw d) (hQ : CausalModelClass epsilon Q)
    (sample : Fin n → Obs d) :
    (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 sample b - budgetValue Q b.1) ^ 2) ≤
      (sSup ((fun lambda : ℝ =>
        |estimatedThresholdProcess epsilon sample lambda -
          dualProcessReal epsilon (observedMarginal Q) lambda|) '' Set.Icc 0 1)) ^ 2 := by
  have hF : ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      |estimatedThresholdProcess epsilon sample lambda| ≤ B := by
    by_cases hs : d < boundedAlphabetCutoff
    · simpa [estimatedThresholdProcess, hs] using
        empiricalThresholdProcess_bounded epsilon sample
    · have hd16 : 16 ≤ d := by
        unfold boundedAlphabetCutoff at hs
        omega
      simpa [estimatedThresholdProcess, hs] using
        averagedThresholdProcess_bounded epsilon he hn (by omega : 1 ≤ d) sample
  have hbase := clippedDualCurveLoss_le_processError epsilon b0 he he' hd hb0 Q hQ
    (estimatedThresholdProcess epsilon sample) hF
  simpa [jfEstimator, hbranch, estimatedBudgetValue, dualMinimum] using hbase

/-- In the empirical branch, curve risk is bounded by the empirical process risk. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,he,he',hn,hd,hdsmall,hb0,Q,hQ,mu,hmu), [the stated relationship holds](goal). -/
-- @node: jfEstimator_empiricalCurveRisk_le
lemma jfEstimator_empiricalCurveRisk_le {n d : ℕ} (epsilon b0 : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hdsmall : d < 16)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (Q : PotentialLaw d) (hQ : CausalModelClass epsilon Q)
    (mu : Measure (Fin n → Obs d))
    (hmu : IidSampling (observedMarginal Q) mu) :
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q b.1) ^ 2) ∂mu) ≤
      16 * (d : ℝ) ^ 2 * (3 * (1 + epsilon⁻¹) + 1) ^ 2 / n := by
  rw [IidSampling] at hmu
  subst mu
  have hs : d < boundedAlphabetCutoff := by
    unfold boundedAlphabetCutoff
    exact hdsmall
  have hbranch : ¬(d ≥ boundedAlphabetCutoff ∧ n < (d : ℝ) / logAlphabet d) := by
    simp [Nat.not_le.mpr hs]
  calc
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q b.1) ^ 2)
        ∂productLaw (observedMarginal Q) n) ≤
      ∫ z, (sSup ((fun lambda : ℝ =>
        |empiricalThresholdProcess epsilon z lambda -
          dualProcessReal epsilon (observedMarginal Q) lambda|) '' Set.Icc 0 1)) ^ 2
        ∂productLaw (observedMarginal Q) n := by
          apply integral_mono Integrable.of_finite Integrable.of_finite
          intro z
          simpa [estimatedThresholdProcess, hs] using
            jfEstimator_curveLoss_le_processError epsilon b0 he he' hn hd hb0 hbranch Q hQ z
    _ ≤ _ := empiricalThresholdProcess_uniformRisk_le he (observedMarginal Q) hn

/-- In the Jackson branch, curve risk is bounded by the averaged process risk. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,he,he',hn,hd,hlarge,hb0,Q,hQ,mu,hmu), [the stated relationship holds](goal). -/
-- @node: jfEstimator_averagedCurveRisk_le
lemma jfEstimator_averagedCurveRisk_le {n d : ℕ} (epsilon b0 : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d)
    (hlarge : (d : ℝ) / logAlphabet d ≤ n)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (Q : PotentialLaw d) (hQ : CausalModelClass epsilon Q)
    (mu : Measure (Fin n → Obs d))
    (hmu : IidSampling (observedMarginal Q) mu) :
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q b.1) ^ 2) ∂mu) ≤
      averagedProcessRisk (n := n) epsilon (observedMarginal Q) := by
  rw [IidSampling] at hmu
  subst mu
  have hs : ¬ d < boundedAlphabetCutoff := by
    unfold boundedAlphabetCutoff
    omega
  have hbranch : ¬(d ≥ boundedAlphabetCutoff ∧ n < (d : ℝ) / logAlphabet d) := by
    simp [not_lt.mpr hlarge]
  unfold averagedProcessRisk
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro z
  simpa [estimatedThresholdProcess, hs] using
    jfEstimator_curveLoss_le_processError epsilon b0 he he' hn (by omega : 2 ≤ d)
      hb0 hbranch Q hQ z

/-- The logarithmic scale lies between one and the alphabet size. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: logAlphabet_bounds_curve
lemma logAlphabet_bounds_curve (d : ℕ) (hd : 1 ≤ d) :
    0 < logAlphabet d ∧ logAlphabet d ≤ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : logAlphabet d = 1 + Real.log d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos)]
    simp
  rw [hlog]
  constructor
  · have := Real.log_nonneg hdge
    linarith
  · have := Real.log_le_sub_one_of_pos hdpos
    linarith

/-- The empirical bound has the required logarithmic rate below the cutoff. With [the specified inputs and conditions](hyp:n,d,hn,hd,hdsmall,K), [the stated relationship holds](goal). -/
-- @node: empiricalCurveRate_algebra
lemma empiricalCurveRate_algebra (n d : ℕ) (hn : 1 ≤ n)
    (hd : 2 ≤ d) (hdsmall : d < 16) (K : ℝ) :
    16 * (d : ℝ) ^ 2 * K ^ 2 / n ≤
      (4096 * K ^ 2) * ((d : ℝ) / (n * logAlphabet d)) := by
  obtain ⟨hLpos, hLle⟩ := logAlphabet_bounds_curve d (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdle : (d : ℝ) ≤ 16 := by exact_mod_cast (show d ≤ 16 by omega)
  have hprod : (d : ℝ) * logAlphabet d ≤ 256 := by nlinarith
  calc
    16 * (d : ℝ) ^ 2 * K ^ 2 / n ≤
        (4096 * K ^ 2 * d) / (n * logAlphabet d) := by
      apply (div_le_div_iff₀ hnpos (mul_pos hnpos hLpos)).2
      have h := mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ 16 * (d : ℝ) * K ^ 2 * n by positivity)
      nlinarith
    _ = _ := by ring

/-- The total curve estimator takes values in the unit interval on every branch. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,sample,b), [the stated relationship holds](goal). -/
-- @node: jfEstimator_unit_interval
lemma jfEstimator_unit_interval (n d : ℕ) (epsilon b0 : ℝ)
    (sample : Fin n → Obs d) (b : Set.Icc b0 (1 - b0)) :
    jfEstimator n d epsilon b0 sample b ∈ Set.Icc (0 : ℝ) 1 := by
  unfold jfEstimator
  split_ifs
  · norm_num
  · unfold estimatedBudgetValue
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The clipped estimator has squared uniform loss at most one. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,hb0,Q,sample), [the stated relationship holds](goal). -/
-- @node: jfEstimator_curveLoss_le_one
lemma jfEstimator_curveLoss_le_one (n d : ℕ) (epsilon b0 : ℝ)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (Q : PotentialLaw d) (sample : Fin n → Obs d) :
    (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 sample b - budgetValue Q b.1) ^ 2) ≤ 1 := by
  let : Nonempty (Set.Icc b0 (1 - b0)) :=
    ⟨⟨b0, ⟨le_refl _, by linarith [hb0.2]⟩⟩⟩
  apply ciSup_le
  intro b
  have hb : b.1 ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_trans hb0.1 b.2.1, le_trans b.2.2 (by linarith [hb0.1])⟩
  have hest := jfEstimator_unit_interval n d epsilon b0 sample b
  have hvalue := budgetValue_unit_interval Q b.1 hb
  nlinarith [hest.1, hest.2, hvalue.1, hvalue.2]

/-- Every model has unit-bounded curve risk under the clipped estimator. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,hb0,Q,mu,hmu), [the stated relationship holds](goal). -/
-- @node: jfEstimator_curveRisk_le_one
lemma jfEstimator_curveRisk_le_one (n d : ℕ) (epsilon b0 : ℝ)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (Q : PotentialLaw d) (mu : Measure (Fin n → Obs d))
    (hmu : IidSampling (observedMarginal Q) mu) :
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q b.1) ^ 2) ∂mu) ≤ 1 := by
  rw [IidSampling] at hmu
  subst mu
  let : IsProbabilityMeasure (productLaw (observedMarginal Q) n) := by
    unfold productLaw CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.productLaw
    infer_instance
  calc
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q b.1) ^ 2)
      ∂productLaw (observedMarginal Q) n) ≤
        ∫ _z : Fin n → Obs d, (1 : ℝ) ∂productLaw (observedMarginal Q) n := by
          exact integral_mono Integrable.of_finite (integrable_const 1)
            (jfEstimator_curveLoss_le_one n d epsilon b0 hb0 Q)
    _ = 1 := by simp

/-- The unit risk bound is uniform over the causal model class. With [the specified inputs and conditions](hyp:n,d,epsilon,b0,hb0,mu,hmu), [the stated relationship holds](goal). -/
-- @node: jfEstimator_worstCurveRisk_le_one
lemma jfEstimator_worstCurveRisk_le_one (n d : ℕ) (epsilon b0 : ℝ)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (mu : ModelLaw d epsilon → Measure (Fin n → Obs d))
    (hmu : ∀ Q, IidSampling (observedMarginal Q.1) (mu Q)) :
    sSup (Set.range (fun Q : ModelLaw d epsilon =>
      ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
        (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2)
        ∂mu Q)) ≤ 1 := by
  let risks := Set.range (fun Q : ModelLaw d epsilon =>
    ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2) ∂mu Q)
  by_cases h : risks.Nonempty
  · change sSup risks ≤ 1
    apply csSup_le h
    rintro _ ⟨Q, rfl⟩
    exact jfEstimator_curveRisk_le_one n d epsilon b0 hb0 Q.1 (mu Q) (hmu Q)
  · have hempty : risks = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    change sSup risks ≤ 1
    simp [hempty]

-- @node: thm:curve-upper
/-- The curve upper result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem curve_upper (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, ∀ b0 : ℝ,
      1 ≤ n → 2 ≤ d → b0 ∈ Set.Icc (0 : ℝ) (1 / 2) →
      ∀ mu : ModelLaw d epsilon → Measure (Fin n → Obs d),
        (∀ Q, IidSampling (observedMarginal Q.1) (mu Q)) →
        sSup (Set.range (fun Q : ModelLaw d epsilon =>
          ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
            (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2)
            ∂mu Q)) ≤ C * min 1 ((d : ℝ) / (n * logAlphabet d)) := by
  obtain ⟨C0, hC0pos, _, hcert⟩ := integrated_process_certificate epsilon he he'
  let K : ℝ := 3 * (1 + epsilon⁻¹) + 1
  let C : ℝ := max 1 (max C0 (4096 * K ^ 2))
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : C0 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : 4096 * K ^ 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hCpos, ?_⟩
  intro n d b0 hn hd hb0 mu hmu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hLpos, _⟩ := logAlphabet_bounds_curve d (by omega : 1 ≤ d)
  let r : ℝ := (d : ℝ) / (n * logAlphabet d)
  have hrnonneg : 0 ≤ r := by dsimp [r]; positivity
  let risks := Set.range (fun Q : ModelLaw d epsilon =>
    ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2) ∂mu Q)
  change sSup risks ≤ C * min 1 r
  by_cases hne : risks.Nonempty
  · apply csSup_le hne
    rintro _ ⟨Q, rfl⟩
    have hunit := jfEstimator_curveRisk_le_one n d epsilon b0 hb0 Q.1 (mu Q) (hmu Q)
    by_cases hdsmall : d < 16
    · have hemp := jfEstimator_empiricalCurveRisk_le epsilon b0 he he' hn hd
        hdsmall hb0 Q.1 Q.2 (mu Q) (hmu Q)
      have halg := empiricalCurveRate_algebra n d hn hd hdsmall K
      have hscaled :
          (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
            (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2)
            ∂mu Q) ≤ (4096 * K ^ 2) * r := by
        exact hemp.trans (by simpa [r, K] using halg)
      by_cases hbig : 1 ≤ r
      · rw [min_eq_left hbig]
        nlinarith [hunit, hC1]
      · have hsmall : r ≤ 1 := le_of_not_ge hbig
        rw [min_eq_right hsmall]
        exact hscaled.trans (mul_le_mul_of_nonneg_right hCK hrnonneg)
    · have hd16 : 16 ≤ d := by omega
      by_cases hlarge : (d : ℝ) / logAlphabet d ≤ n
      · have hratio : r ≤ 1 := by
          have hnum := (div_le_iff₀ hLpos).1 hlarge
          apply (div_le_iff₀ (mul_pos hnpos hLpos)).2
          nlinarith
        have hproc := jfEstimator_averagedCurveRisk_le epsilon b0 he he' hn hd16
          hlarge hb0 Q.1 Q.2 (mu Q) (hmu Q)
        obtain ⟨_, _, _, _, _, havg⟩ :=
          hcert n d Q.1 (mu Q) hn hd16 hlarge (hmu Q) Q.2
        rw [min_eq_right hratio]
        calc
          _ ≤ averagedProcessRisk (n := n) epsilon (observedMarginal Q.1) := hproc
          _ ≤ C0 * r := by simpa [r, mul_div_assoc] using havg
          _ ≤ C * r := mul_le_mul_of_nonneg_right hC0 hrnonneg
      · have hnum := (lt_div_iff₀ hLpos).1 (lt_of_not_ge hlarge)
        have hratio : 1 ≤ r := by
          apply (le_div_iff₀ (mul_pos hnpos hLpos)).2
          nlinarith
        rw [min_eq_left hratio]
        nlinarith [hunit, hC1]
  · have hempty : risks = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simpa using mul_nonneg hCpos.le (le_min (by norm_num) hrnonneg)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
