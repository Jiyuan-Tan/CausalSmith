module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridCellAnalysis
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyTransport
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridCalibrationConstants
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLogSchedule
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridEventualCalibration
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPilotAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridExponentialAbsorption
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyLightTail
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyMean
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridBranchMeanAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridMeanAssembly
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridVarianceAssembly
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridDeterministicAbsorption

/-! The unequal-information Poisson hybrid risk bound. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- The displayed light/heavy statistic on the three independent count pools.  [the stated conditions](hyp:n,m,eps,u,t,K) [the stated conclusion](goal). -/
noncomputable def hybridPoissonStatistic {d : Nat} (n m : Nat) (eps u t : Real)
    (K : HybridPoissonCounts d) : Real :=
  clipUnit <| ∑ x : Fin d,
    let jx := (K x false).2.1 + (K x true).2.1
    let s0 : Real := (K x false).1
    let s1 : Real := (K x true).1
    let k0' := (K x false).2.2
    let k1 := (K x true).2.2
    if jx ≤ k0 n m eps then
      s1 / u * factorialLift true (Ldeg n) (Bscale n m eps) t k0' k1 -
      s0 / u * factorialLift false (Ldeg n) (Bscale n m eps) t k0' k1
    else
      s1 / u * (k0' + k1 + 1 : Nat) / (k1 + 1 : Nat) -
      s0 / u * (k0' + k1 + 1 : Nat) / (k0' + 1 : Nat)

/-- Squared error of the calibrated Poisson hybrid, represented on the explicit
independent cell-count experiment.  [the stated conditions](hyp:P,n,m,eps) [the stated conclusion](goal). -/
noncomputable def poissonHybridMSE {d : Nat} (P : DiscreteLaw d)
    (n m : Nat) (eps : Real) : Real :=
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  let tp : Real := (bs.np + bs.mp : Nat) / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  if calibrationPredicate n m eps then
    ∫ K, (hybridPoissonStatistic n m eps u t K - ateFunctional P) ^ 2 ∂
      hybridPoissonCountLaw P u tp t
  else ateFunctional P ^ 2
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma hybridPoissonStatistic_mem_Icc {d : Nat} (n m : Nat) (eps u t : Real)
    (K : HybridPoissonCounts d) :
    hybridPoissonStatistic n m eps u t K ∈ Set.Icc (-1 : Real) 1 := by
  dsimp [hybridPoissonStatistic, clipUnit]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/

lemma poissonHybridMSE_le_four {d : Nat} (P : DiscreteLaw d)
    (n m : Nat) (eps : Real) (hP : ModelClass d eps P) :
    poissonHybridMSE P n m eps ≤ 4 := by
  have htheta := ateFunctional_mem_Icc_neg_one_one P hP.overlap
  by_cases hcal : calibrationPredicate n m eps
  · simp only [poissonHybridMSE, hcal, if_pos]
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let mu := hybridPoissonCountLaw P u tp t
    letI : IsProbabilityMeasure mu := ⟨by
      simp [mu, hybridPoissonCountLaw]⟩
    change (∫ K, (hybridPoissonStatistic n m eps u t K -
      ateFunctional P) ^ 2 ∂mu) ≤ 4
    rcases htheta with ⟨htlo, hthi⟩
    calc
      _ ≤ ∫ _K, (4 : Real) ∂mu := by
        apply integral_mono
        · apply Integrable.of_bound
            ((measurable_of_countable _).aestronglyMeasurable) 4
          filter_upwards [] with K
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          rcases hybridPoissonStatistic_mem_Icc n m eps u t K with ⟨hKlo, hKhi⟩
          nlinarith [sq_nonneg
            (hybridPoissonStatistic n m eps u t K - ateFunctional P)]
        · exact integrable_const 4
        intro K
        rcases hybridPoissonStatistic_mem_Icc n m eps u t K with ⟨hKlo, hKhi⟩
        nlinarith [sq_nonneg
          (hybridPoissonStatistic n m eps u t K - ateFunctional P)]
      _ = 4 := by simp
  · simp [poissonHybridMSE, hcal]
    rcases htheta with ⟨htlo, hthi⟩
    nlinarith [sq_nonneg (ateFunctional P)]

/-- Clipping and the bias--variance identity reduce calibrated risk to the
explicit variance and mean envelopes.  [the stated conditions](hyp:heps,heps2,hn,hP,hcal) [the stated conclusion](goal). -/
lemma poissonHybridMSE_le_variance_add_bias_sq {eps : Real} (heps : 0 < eps)
    (heps2 : eps < 1 / 2) {n m d : Nat} (P : DiscreteLaw d)
    (hn : 1 ≤ n) (hP : ModelClass d eps P)
    (hcal : calibrationPredicate n m eps) :
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    poissonHybridMSE P n m eps ≤
      Var[(fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
          hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x));
        hybridPoissonCountLaw P u tp t] +
      (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
        6 * ((n : Real) ^ 12)⁻¹) ^ 2 := by
  dsimp only
  classical
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  let mu := hybridPoissonCountLaw P u tp t
  let raw := fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
    hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, hybridPoissonCountLaw]
    infer_instance
  have hraw : MemLp raw 2 mu := by
    let muc := fun x : Fin d ↦ Measure.pi fun arm : Bool ↦
      (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x arm))))
    have hx (x : Fin d) : MemLp
        (fun K : HybridPoissonCounts d ↦
          hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x))
        2 (Measure.pi muc) :=
      (hybridSelectedCell_memLp P u tp t (Bscale n m eps)
        (k0 n m eps) (Ldeg n) x).comp_measurePreserving
          (measurePreserving_eval muc x)
    change MemLp (fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
      hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x))
      2 (Measure.pi muc)
    exact memLp_finset_sum _ (fun x _ ↦ hx x)
  have hmean : (∫ K, raw K ∂mu) =
      ∑ x : Fin d, hybridSelectedCellMean P u tp t (Bscale n m eps)
        (k0 n m eps) (Ldeg n) x := by
    have hx (x : Fin d) : Integrable
        (fun K : HybridPoissonCounts d ↦
          hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x)) mu :=
      ((hybridSelectedCell_memLp P u tp t (Bscale n m eps)
        (k0 n m eps) (Ldeg n) x).comp_measurePreserving
          (measurePreserving_eval (fun x : Fin d ↦ Measure.pi fun arm : Bool ↦
            (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
              ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
                (poissonMeasure (Real.toNNReal (t * armMass P x arm))))) x)).integrable
        one_le_two
    change (∫ K, ∑ x : Fin d,
      hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x) ∂mu) = _
    rw [integral_finset_sum _ (fun x _ ↦ hx x)]
    apply Finset.sum_congr rfl
    intro x _
    exact integral_comp_eval
      (measurable_of_countable _).aestronglyMeasurable
  have hbias := calibrated_hybrid_mean_bias_le heps heps2 n m d P hn hP hcal
  have htheta := ateFunctional_mem_Icc_neg_one_one P hP.overlap
  have hsquare : (∫ K, (raw K - ateFunctional P) ^ 2 ∂mu) =
      Var[raw; mu] + ((∫ K, raw K ∂mu) - ateFunctional P) ^ 2 := by
    rw [variance_eq_sub hraw]
    have hs := hraw.integrable_sq
    have hi := hraw.integrable one_le_two
    calc
      _ = (∫ K, raw K ^ 2 ∂mu) -
          2 * ateFunctional P * (∫ K, raw K ∂mu) + ateFunctional P ^ 2 := by
        calc
          _ = ∫ K, (raw K ^ 2 - 2 * ateFunctional P * raw K) +
              ateFunctional P ^ 2 ∂mu := by
            apply integral_congr_ae
            filter_upwards [] with K
            ring
          _ = (∫ K, raw K ^ 2 - 2 * ateFunctional P * raw K ∂mu) +
              ∫ _K, ateFunctional P ^ 2 ∂mu :=
            integral_add (hs.sub (hi.const_mul _)) (integrable_const _)
          _ = _ := by
            rw [integral_sub hs (hi.const_mul _), integral_const_mul,
              integral_const, probReal_univ, one_smul]
      _ = _ := by
        change (∫ K, raw K ^ 2 ∂mu) - 2 * ateFunctional P * (∫ K, raw K ∂mu) +
          ateFunctional P ^ 2 = (∫ K, raw K ^ 2 ∂mu) -
            (∫ K, raw K ∂mu) ^ 2 +
              ((∫ K, raw K ∂mu) - ateFunctional P) ^ 2
        ring
  change poissonHybridMSE P n m eps ≤ Var[raw; mu] +
    (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
      6 * ((n : Real) ^ 12)⁻¹) ^ 2
  simp only [poissonHybridMSE, hcal, if_pos]
  change (∫ K, (clipUnit (raw K) - ateFunctional P) ^ 2 ∂mu) ≤ _
  have hclipInt : Integrable
      (fun K ↦ (clipUnit (raw K) - ateFunctional P) ^ 2) mu := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 4
    filter_upwards [] with K
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc := hybridPoissonStatistic_mem_Icc n m eps u t K
    change clipUnit (raw K) ∈ Set.Icc (-1 : Real) 1 at hc
    rcases hc with ⟨hlo, hhi⟩
    rcases htheta with ⟨htlo, hthi⟩
    nlinarith [sq_nonneg (clipUnit (raw K) - ateFunctional P)]
  calc
    _ ≤ ∫ K, (raw K - ateFunctional P) ^ 2 ∂mu := by
      apply integral_mono
      · exact hclipInt
      · exact (hraw.sub (memLp_const _)).integrable_sq
      intro K
      exact hybrid_clipUnit_sq_sub_le _ _ htheta
    _ = Var[raw; mu] + ((∫ K, raw K ∂mu) - ateFunctional P) ^ 2 := hsquare
    _ ≤ Var[raw; mu] +
        (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
          6 * ((n : Real) ^ 12)⁻¹) ^ 2 := by
      rw [hmean]
      have henv0 : 0 ≤ 2 * d * Bscale n m eps /
          (eps * (Ldeg n : Real) ^ 2) + 6 * ((n : Real) ^ 12)⁻¹ := by
        obtain ⟨_, _, _, hB⟩ := calibrationPredicate_positive_parameters hcal
        positivity
      apply add_le_add le_rfl
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) henv0).2 hbias

-- @node: lem:poisson-hybrid-risk
/-- One constant depending only on overlap controls the calibrated hybrid risk
simultaneously for all sample sizes and alphabets.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma poisson_hybrid_risk {eps : Real} (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (P : DiscreteLaw d),
      1 ≤ n → 2 ≤ d → ModelClass d eps P →
      poissonHybridMSE P n m eps ≤ C * frontierRate n m d := by
  obtain ⟨Ccal, hCcal, hcalrisk⟩ :
      ∃ Ccal : Real, 0 < Ccal ∧ ∀ (n m d : Nat) (P : DiscreteLaw d),
        1 ≤ n → 2 ≤ d → ModelClass d eps P →
        calibrationPredicate n m eps →
        poissonHybridMSE P n m eps ≤ Ccal * frontierRate n m d := by
    obtain ⟨Cvar, hCvar, hvar⟩ := calibrated_hybrid_variance_le heps heps2
    obtain ⟨Cabs, hCabs, habs⟩ :=
      calibrated_envelope_absorption_exists heps hCvar
    refine ⟨max 4 Cabs, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro n m d P hn hd hP hcal
    let r : Real := 1 / (n : Real) + (d : Real) ^ 2 /
      (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2)
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    by_cases hr : 1 ≤ r
    · have hfront : frontierRate n m d = 1 := by
        rw [frontierRate, min_eq_left]
        simpa [r, Nat.cast_add, one_div] using hr
      rw [hfront]
      calc
        poissonHybridMSE P n m eps ≤ 4 := poissonHybridMSE_le_four P n m eps hP
        _ ≤ max 4 Cabs * 1 := by
          simpa using (le_max_left (4 : Real) Cabs)
    · have hrle : r ≤ 1 := le_of_not_ge hr
      have hfront : frontierRate n m d = r := by
        rw [frontierRate, min_eq_right]
        simpa [r, Nat.cast_add, one_div] using hrle
      rw [hfront]
      have hmse := poissonHybridMSE_le_variance_add_bias_sq
        heps heps2 P hn hP hcal
      have hv := hvar n m d P hn hP hcal
      have ha := habs n m d hn hd hcal
      calc
        poissonHybridMSE P n m eps ≤
            Var[(fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
                hybridSelectedCell (k0 n m eps) (Ldeg n)
                  (Bscale n m eps) ((blockSizes n m).M0 / 8)
                  (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8) (K x));
              hybridPoissonCountLaw P ((blockSizes n m).M0 / 8)
                (((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8)
                (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8)] +
              (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
                6 * ((n : Real) ^ 12)⁻¹) ^ 2 := by
          simpa only using hmse
        _ ≤ 4 * starA ^ Ldeg n *
              (min 1 ((d : Real) * Bscale n m eps) /
                  ((blockSizes n m).M0 / 8) +
                (d : Real) * Bscale n m eps ^ 2) +
            Cvar * (((blockSizes n m).M0 / 8 : Real)⁻¹ +
              (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8 : Real)⁻¹) +
            8 * d * Bscale n m eps ^ 2 /
              (eps ^ 2 * (Ldeg n : Real) ^ 4) +
            4 / (eps * (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8)) +
            414 * ((n : Real) ^ 12)⁻¹ +
            (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
              6 * ((n : Real) ^ 12)⁻¹) ^ 2 := by
          exact add_le_add hv le_rfl
        _ ≤ Cabs * r := by simpa only [r] using ha
        _ ≤ max 4 Cabs * r :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hr0
  obtain ⟨n0, hn0, hfail⟩ := calibrationPredicate_failure_bounded heps heps2
  refine ⟨max Ccal (4 * n0), lt_of_lt_of_le hCcal (le_max_left _ _), ?_⟩
  intro n m d P hn hd hP
  by_cases hcal : calibrationPredicate n m eps
  · exact (hcalrisk n m d P hn hd hP hcal).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (frontierRate_mem_Ioc_zero_one n m d hn).1.le)
  · have hnlt : n < n0 := hfail n m hcal
    have hnleR : (n : Real) ≤ n0 := by exact_mod_cast (Nat.le_of_lt hnlt)
    have hnR : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hrpos := (frontierRate_mem_Ioc_zero_one n m d hn).1
    have hinv := inv_n_le_frontierRate n m d hn
    have hone : (1 : Real) ≤ n0 * frontierRate n m d := by
      have hnr : (1 : Real) ≤ n * frontierRate n m d := by
        apply (div_le_iff₀ hnR).1 at hinv
        simpa [mul_comm] using hinv
      exact hnr.trans (mul_le_mul_of_nonneg_right hnleR hrpos.le)
    calc
      poissonHybridMSE P n m eps ≤ 4 := poissonHybridMSE_le_four P n m eps hP
      _ ≤ (4 * n0) * frontierRate n m d := by nlinarith
      _ ≤ max Ccal (4 * n0) * frontierRate n m d :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hrpos.le

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
