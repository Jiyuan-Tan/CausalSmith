module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.ScalarBias

/-! Outer pilot expectation bounds for the scalar Jackson cell bias. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped BigOperators NNReal

/-- The ideal two-pool count law is a probability measure. With [the specified inputs and conditions](hyp:n,d,P), [the stated relationship holds](goal). -/
-- @node: idealCountLaw_isProbabilityMeasure
lemma idealCountLaw_isProbabilityMeasure {n d : Nat} (P : DiscreteLaw d) :
    IsProbabilityMeasure (idealCountLaw (n := n) P) := by
  unfold idealCountLaw
  let onePool : Measure (Fin d → Cell → Nat) := Measure.pi (fun j : Fin d =>
    Measure.pi (fun zeta : Cell => poissonMeasure
      ⟨max 0 (((n : Real) / 8) * cellVector P j zeta), le_max_left 0 _⟩))
  letI : ∀ j : Fin d, ∀ zeta : Cell, IsProbabilityMeasure
      (poissonMeasure ⟨max 0 (((n : Real) / 8) * cellVector P j zeta),
        le_max_left 0 _⟩) := fun j zeta =>
      instIsProbabilityMeasureNatPoissonMeasure
        ⟨max 0 (((n : Real) / 8) * cellVector P j zeta), le_max_left 0 _⟩
  letI : ∀ j : Fin d, IsProbabilityMeasure (Measure.pi (fun zeta : Cell =>
      poissonMeasure ⟨max 0 (((n : Real) / 8) * cellVector P j zeta),
        le_max_left 0 _⟩)) := fun _ => by infer_instance
  letI : IsProbabilityMeasure onePool := by dsimp [onePool]; infer_instance
  change IsProbabilityMeasure (onePool.prod onePool)
  infer_instance

/-- On a probability space, the square of the mean of a nonnegative
square-integrable scalar is at most its second moment. With [the specified inputs and conditions](hyp:Omega,mu,f,hf,hfsq), [the stated relationship holds](goal). -/
-- @node: integral_sq_le_integral_sq_of_nonneg
lemma integral_sq_le_integral_sq_of_nonneg
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (f : Omega → Real)
    (hf : AEStronglyMeasurable f mu)
    (hfsq : Integrable (fun omega => f omega ^ 2) mu) :
    (∫ omega, f omega ∂mu) ^ 2 ≤ ∫ omega, f omega ^ 2 ∂mu := by
  have hmem : MemLp f 2 mu :=
    (memLp_two_iff_integrable_sq hf).2 hfsq
  have hfint : Integrable f mu := hmem.integrable (by norm_num)
  have hcenter : Integrable (fun omega =>
      (f omega - ∫ x, f x ∂mu) ^ 2) mu := by
    simp_rw [sub_sq]
    exact (hfsq.sub ((hfint.const_mul _).mul_const _)).add (integrable_const _)
  have hnonneg : 0 ≤ ∫ omega, (f omega - ∫ x, f x ∂mu) ^ 2 ∂mu :=
    integral_nonneg fun omega => sq_nonneg _
  rw [show (∫ omega, (f omega - ∫ x, f x ∂mu) ^ 2 ∂mu) =
      (∫ omega, f omega ^ 2 ∂mu) - (∫ omega, f omega ∂mu) ^ 2 by
    rw [show (fun omega => (f omega - ∫ x, f x ∂mu) ^ 2) =
        fun omega => f omega ^ 2 -
          (2 * (∫ x, f x ∂mu)) * f omega + (∫ x, f x ∂mu) ^ 2 by
      funext omega
      ring]
    rw [integral_add, integral_sub, integral_const_mul, integral_const]
    · simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      ring
    · exact hfsq
    · exact hfint.const_mul _
    · exact (hfsq.sub (hfint.const_mul _))
    · exact integrable_const _] at hnonneg
  linarith

/-- The first moment of the sum of the four pilot radii is controlled by the
square root of the equation-(21) cell scale. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: pilotRadius_sum_integral_sq_le_cellScale
lemma pilotRadius_sum_integral_sq_le_cellScale
    {n d : Nat} (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    let m : Real := (n : Real) / 8
    let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
    (∫ p, ∑ zeta : Cell,
      pilotRadius m d (curryCountTable p j) zeta ∂mu) ^ 2 ≤
      32 * pilotRadiusConstant ^ 2 * badPilotCellScale (n := n) P j ^ 2 := by
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  let S : ((Fin d × Fin 4) → Nat) → Real := fun p =>
    ∑ zeta : Cell, pilotRadius m d (curryCountTable p j) zeta
  have hsecond := pilotRadius_sum_sq_integral_le_cellScale hn hd P j
  have hmeas : AEStronglyMeasurable S mu :=
    (measurable_of_countable _).aestronglyMeasurable
  calc
    _ ≤ ∫ p, S p ^ 2 ∂mu :=
      integral_sq_le_integral_sq_of_nonneg mu S hmeas (by
        simpa [S, m, rate, mu] using hsecond.1)
    _ ≤ _ := by simpa [S, m, rate, mu] using hsecond.2

/-- Linear first-moment form of the pilot-radius estimate. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: pilotRadius_sum_integral_le_cellScale
lemma pilotRadius_sum_integral_le_cellScale
    {n d : Nat} (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    let m : Real := (n : Real) / 8
    let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
    (∫ p, ∑ zeta : Cell,
      pilotRadius m d (curryCountTable p j) zeta ∂mu) ≤
      Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j := by
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let I : Real := ∫ p, ∑ zeta : Cell,
    pilotRadius m d (curryCountTable p j) zeta ∂mu
  let R : Real := Real.sqrt 32 * pilotRadiusConstant *
    badPilotCellScale (n := n) P j
  have hsq := pilotRadius_sum_integral_sq_le_cellScale hn hd P j
  have hI : 0 ≤ I := integral_nonneg fun p => Finset.sum_nonneg fun z _ =>
    (pilotRadius_pos_of_pos (by dsimp [m]; positivity)
      (show 1 ≤ d by omega) (curryCountTable p j) z).le
  have hscale : 0 ≤ badPilotCellScale (n := n) P j := by
    unfold badPilotCellScale
    have hL : 0 < logAlphabet d := by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      have hdR : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith [Real.log_nonneg hdR]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold pilotRadiusConstant; norm_num))
      hscale
  have hR2 : R ^ 2 =
      32 * pilotRadiusConstant ^ 2 * badPilotCellScale (n := n) P j ^ 2 := by
    dsimp [R]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 32)]
  apply (sq_le_sq₀ hI hR).mp
  rw [hR2]
  simpa [I, m, rate, mu] using hsq

set_option maxHeartbeats 800000 in
-- The nested product-law integrals and pilot-dependent coefficient bound are elaboration intensive.
/-- Integrating the conditional good-pilot scalar bias costs one first moment
of the sum of the four pilot radii. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: flatGoodPilot_conditionalBias_integral_le
lemma flatGoodPilot_conditionalBias_integral_le
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (j : Fin d) (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    ∃ C : Real, 0 < C ∧
      let m : Real := (n : Real) / 8
      let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
      let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
      let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
        fun i e => poissonTableCell j e i
      (∫ p, if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        |(∫ e, jacksonCellStatistic epsilon lambda m d (curryCountTable p j)
            (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| else 0 ∂mu) ≤
        (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
            (d : Real) ^ (1 / 4 : Real) +
          (32 * (3 * (1 + epsilon⁻¹) + 1)) *
            (2 / (jacksonDegree d : Real) +
              1 / (jacksonDegree d : Real) ^ 2)) *
          (Real.sqrt 32 * pilotRadiusConstant) *
          badPilotCellScale (n := n) P j := by
  classical
  obtain ⟨C0, hC0, hcoeff⟩ := jacksonCoefficientBV_pilot_le epsilon he he'
  let A : Real := 32 * (3 * (1 + epsilon⁻¹) + 1)
  let B : Real := 4 * C0 ^ 2 * Real.exp 123 *
      (d : Real) ^ (1 / 16 : Real) / (d : Real) ^ (1 / 4 : Real) +
    A * (2 / (jacksonDegree d : Real) + 1 / (jacksonDegree d : Real) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C0, hC0, ?_⟩
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  let S : ((Fin d × Fin 4) → Nat) → Real := fun p =>
    ∑ zeta : Cell, pilotRadius m d (curryCountTable p j) zeta
  let H : ((Fin d × Fin 4) → Nat) → Real := fun p =>
    if idealPilotGoodBool (n := n) P (curryCountTable p, fun _ _ => 0) j then
      |(∫ e, jacksonCellStatistic epsilon lambda m d (curryCountTable p j)
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
        thresholdFunReal epsilon lambda (cellVector P j)| else 0
  have hSpos (p : (Fin d × Fin 4) → Nat) : 0 < S p :=
    Finset.sum_pos (fun z _ => pilotRadius_pos_of_pos
      (by dsimp [m]; positivity) (show 1 ≤ d by omega) (curryCountTable p j) z)
      (by simp)
  have hpoint (p : (Fin d × Fin 4) → Nat) : H p ≤ B * S p := by
    by_cases hg : idealPilotGood (n := n) P
        (curryCountTable p, fun _ _ => 0) j
    · have hc := goodPilot_jacksonCellStatistic_conditional_bias_le epsilon he hn hd
        P p j hg lambda hlambda C0 hC0.le
        (hcoeff m (by dsimp [m]; positivity) d (show 1 ≤ d by omega)
          (curryCountTable p j))
      have hgb := (idealPilotGoodBool_eq_true P
        (curryCountTable p, fun _ _ => 0) j).2 hg
      rw [show H p = |(∫ e, jacksonCellStatistic epsilon lambda m d
          (curryCountTable p j) (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| by simp [H, hgb]]
      apply hc.trans_eq
      have hSne : S p ≠ 0 := (hSpos p).ne'
      dsimp [B, A, S, m, rate, mu, W]
      field_simp
    · have hgb : idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hg ((idealPilotGoodBool_eq_true P
          (curryCountTable p, fun _ _ => 0) j).1 ht)
      rw [show H p = 0 by simp [H, hgb]]
      exact mul_nonneg hB.le (hSpos p).le
  have hSint : Integrable S mu := by
    have hsecond := pilotRadius_sum_sq_integral_le_cellScale hn hd P j
    have hmeas : AEStronglyMeasurable S mu :=
      (measurable_of_countable _).aestronglyMeasurable
    exact ((memLp_two_iff_integrable_sq hmeas).2 (by
      simpa [S, m, rate, mu] using hsecond.1)).integrable (by norm_num)
  have hHint : Integrable H mu := by
    apply Integrable.mono' (hSint.const_mul B) (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [H]
      split <;> positivity)]
    exact hpoint p
  calc
    _ = ∫ p, H p ∂mu := by rfl
    _ ≤ ∫ p, B * S p ∂mu := integral_mono hHint (hSint.const_mul B) hpoint
    _ = B * ∫ p, S p ∂mu := by rw [integral_const_mul]
    _ ≤ B * (Real.sqrt 32 * pilotRadiusConstant *
        badPilotCellScale (n := n) P j) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      simpa [S, m, rate, mu] using pilotRadius_sum_integral_le_cellScale hn hd P j
    _ = _ := by dsimp [B, A]; ring

/-- At a fixed shadow price, the ideal clipped cell error is integrable. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: idealClippedCell_error_integrable
lemma idealClippedCell_error_integrable
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    Integrable (fun counts =>
      idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j))
      (idealCountLaw (n := n) P) := by
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
    idealCountLaw_isProbabilityMeasure P
  let E := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  let U := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    sSup ((fun t : Real =>
      |idealClippedCellPath (n := n) epsilon t counts j -
        thresholdFunReal epsilon t (cellVector P j)|) '' Set.Icc 0 1)
  have hU2 := idealClippedCell_error_sSup_sq_integrable epsilon he hn hd P j
  have hU2' : Integrable (fun counts => U counts ^ 2)
      (idealCountLaw (n := n) P) := by simpa [U] using hU2
  have hEmeas : AEStronglyMeasurable E (idealCountLaw (n := n) P) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hE2 : Integrable (fun counts => E counts ^ 2)
      (idealCountLaw (n := n) P) := by
    apply Integrable.mono' hU2' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with counts
    have hEU : |E counts| ≤ U counts := by
      dsimp [U, E]
      apply le_csSup
      · exact ⟨_, fun y hy => by
          rcases hy with ⟨t, ht, rfl⟩
          exact idealClippedCell_error_le_badScore he hn hd P counts j t ht⟩
      · exact ⟨lambda, hlambda, rfl⟩
    rw [← sq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |E counts|)]
    exact pow_le_pow_left₀ (abs_nonneg _) hEU 2
  exact ((memLp_two_iff_integrable_sq hEmeas).2 hE2).integrable (by norm_num)

/-- The paper's ideal cell expectation is the iterated flattened pilot and
evaluation Poisson expectation. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: expectedUncappedJacksonCell_eq_flat_iterated
lemma expectedUncappedJacksonCell_eq_flat_iterated
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
    expectedUncappedJacksonCell (n := n) epsilon lambda P j =
      ∫ p, ∫ e, jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
        (curryCountTable p j) (curryCountTable e j) ∂mu ∂mu := by
  dsimp only
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
  let F := fun pe : (((Fin d × Fin 4) → Nat) × ((Fin d × Fin 4) → Nat)) =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let g := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
      (counts.1 j) (counts.2 j)
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
    idealCountLaw_isProbabilityMeasure P
  have herr := idealClippedCell_error_integrable epsilon he hn hd P j lambda hlambda
  have hg : Integrable g (idealCountLaw (n := n) P) := by
    apply (herr.add (integrable_const
      (thresholdFunReal epsilon lambda (cellVector P j)))).congr
    filter_upwards [] with counts
    dsimp [g]
    unfold idealClippedCellPath
    ring
  have hmap : Measure.map F (mu.prod mu) = idealCountLaw (n := n) P := by
    simpa [F, mu, rate] using map_flatIdealCountLaw (n := n) P
  have hflat : Integrable (g ∘ F) (mu.prod mu) := by
    have : Integrable g (Measure.map F (mu.prod mu)) := by simpa [hmap] using hg
    exact this.comp_aemeasurable (by fun_prop)
  unfold expectedUncappedJacksonCell
  calc
    _ = ∫ pe, g (F pe) ∂mu.prod mu := by
      rw [← hmap, integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
    _ = ∫ p, ∫ e, g (F (p, e)) ∂mu ∂mu := integral_prod _ hflat
    _ = _ := by rfl

/-- The absolute bad-pilot contribution to a fixed scalar cell mean is
bounded by the existing equation-(28) cell envelope. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: idealBadPilot_scalarMean_le_envelope
lemma idealBadPilot_scalarMean_le_envelope
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    |∫ counts, (if idealPilotGoodBool (n := n) P counts j then 0 else
      idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j))
      ∂idealCountLaw (n := n) P| ≤ badPilotCellEnvelope (n := n) epsilon P j := by
  classical
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
    idealCountLaw_isProbabilityMeasure P
  let E := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  let B := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then 0 else E counts
  let G := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then 0 else
      sSup ((fun t : Real =>
        |idealClippedCellPath (n := n) epsilon t counts j -
          thresholdFunReal epsilon t (cellVector P j)|) '' Set.Icc 0 1) ^ 2
  have hE := idealClippedCell_error_integrable epsilon he hn hd P j lambda hlambda
  have hB : Integrable B (idealCountLaw (n := n) P) := by
    let A := {counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) |
      idealPilotGoodBool (n := n) P counts j = false}
    have hA : MeasurableSet A := MeasurableSet.of_discrete
    apply (hE.indicator hA).congr
    filter_upwards [] with counts
    by_cases hg : idealPilotGoodBool (n := n) P counts j = true
    · simp [B, A, Set.indicator, hg]
    · have hg' := Bool.eq_false_of_not_eq_true hg
      simp [B, A, E, Set.indicator, hg']
  have hG : Integrable G (idealCountLaw (n := n) P) := by
    simpa [G] using (idealBadPilotCellEnvelope_sq_integral_le he hn hd P j).1
  have hB2 : Integrable (fun counts => B counts ^ 2)
      (idealCountLaw (n := n) P) := by
    apply Integrable.mono' hG (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with counts
    by_cases hg : idealPilotGoodBool (n := n) P counts j = true
    · simp [B, G, hg]
    · have hg' := Bool.eq_false_of_not_eq_true hg
      simp only [B, G, hg', Bool.false_eq_true, if_false]
      have hEU : |E counts| ≤ sSup ((fun t : Real =>
          |idealClippedCellPath (n := n) epsilon t counts j -
            thresholdFunReal epsilon t (cellVector P j)|) '' Set.Icc 0 1) := by
        dsimp [E]
        apply le_csSup
        · exact ⟨_, fun y hy => by
            rcases hy with ⟨t, ht, rfl⟩
            exact idealClippedCell_error_le_badScore he hn hd P counts j t ht⟩
        · exact ⟨lambda, hlambda, rfl⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E counts)), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hEU 2
  have hmeanSq := integral_sq_le_integral_sq_of_nonneg
    (idealCountLaw (n := n) P) B (measurable_of_countable _).aestronglyMeasurable hB2
  have hint : (∫ counts, B counts ^ 2 ∂idealCountLaw (n := n) P) ≤
      ∫ counts, G counts ∂idealCountLaw (n := n) P := by
    exact integral_mono hB2 hG fun counts => by
      by_cases hg : idealPilotGoodBool (n := n) P counts j = true
      · simp [B, G, hg]
      · have hg' := Bool.eq_false_of_not_eq_true hg
        simp only [B, G, hg', Bool.false_eq_true, if_false]
        have hEU : |E counts| ≤ sSup ((fun t : Real =>
            |idealClippedCellPath (n := n) epsilon t counts j -
              thresholdFunReal epsilon t (cellVector P j)|) '' Set.Icc 0 1) := by
          dsimp [E]
          apply le_csSup
          · exact ⟨_, fun y hy => by
              rcases hy with ⟨t, ht, rfl⟩
              exact idealClippedCell_error_le_badScore he hn hd P counts j t ht⟩
          · exact ⟨lambda, hlambda, rfl⟩
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hEU 2
  have hsquare : |∫ counts, B counts ∂idealCountLaw (n := n) P| ^ 2 ≤
      ∫ counts, G counts ∂idealCountLaw (n := n) P := by
    rw [sq_abs]
    exact hmeanSq.trans hint
  have hGideal : (∫ counts, G counts ∂idealCountLaw (n := n) P) =
      ∫ counts, (if idealPilotGood (n := n) P counts j then 0 else
        sSup ((fun t : Real =>
          |idealClippedCellPath (n := n) epsilon t counts j -
            thresholdFunReal epsilon t (cellVector P j)|) '' Set.Icc 0 1) ^ 2)
        ∂idealCountLaw (n := n) P := by
    apply integral_congr_ae
    filter_upwards [] with counts
    by_cases hg : idealPilotGood (n := n) P counts j
    · have hb := (idealPilotGoodBool_eq_true P counts j).2 hg
      simp [G, hg, hb]
    · have hb : idealPilotGoodBool (n := n) P counts j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hg ((idealPilotGoodBool_eq_true P counts j).1 ht)
      simp [G, hg, hb]
  unfold badPilotCellEnvelope
  dsimp [B] at hsquare ⊢
  rw [hGideal] at hsquare
  apply (Real.le_sqrt (abs_nonneg _) (integral_nonneg fun counts => by
    split <;> positivity)).2
  simpa [E] using hsquare

/-- The good-pilot contribution to the ideal scalar cell mean inherits the
flattened conditional bias bound. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: idealGoodPilot_scalarMean_le
lemma idealGoodPilot_scalarMean_le
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (j : Fin d) (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    ∃ C : Real, 0 < C ∧
      |∫ counts, (if idealPilotGoodBool (n := n) P counts j then
        idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j) else 0)
        ∂idealCountLaw (n := n) P| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
          (d : Real) ^ (1 / 4 : Real) +
        (32 * (3 * (1 + epsilon⁻¹) + 1)) *
          (2 / (jacksonDegree d : Real) +
            1 / (jacksonDegree d : Real) ^ 2)) *
        (Real.sqrt 32 * pilotRadiusConstant) *
        badPilotCellScale (n := n) P j := by
  classical
  obtain ⟨C, hC, hflatBound⟩ :=
    flatGoodPilot_conditionalBias_integral_le epsilon he he' hn hd P
      j lambda hlambda
  refine ⟨C, hC, ?_⟩
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
  let F := fun pe : (((Fin d × Fin 4) → Nat) × ((Fin d × Fin 4) → Nat)) =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let E := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  let H := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then E counts else 0
  have hE := idealClippedCell_error_integrable epsilon he hn (show 1 ≤ d by omega)
    P j lambda hlambda
  have hH : Integrable H (idealCountLaw (n := n) P) := by
    let A := {counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) |
      idealPilotGoodBool (n := n) P counts j = true}
    apply (hE.indicator (MeasurableSet.of_discrete : MeasurableSet A)).congr
    filter_upwards [] with counts
    by_cases hg : idealPilotGoodBool (n := n) P counts j = true
    · simp [H, E, A, Set.indicator, hg]
    · have hg' := Bool.eq_false_of_not_eq_true hg
      simp [H, A, Set.indicator, hg']
  have hmap : Measure.map F (mu.prod mu) = idealCountLaw (n := n) P := by
    simpa [F, mu, rate] using map_flatIdealCountLaw (n := n) P
  have hflatInt : Integrable (H ∘ F) (mu.prod mu) := by
    have : Integrable H (Measure.map F (mu.prod mu)) := by simpa [hmap] using hH
    exact this.comp_aemeasurable (by fun_prop)
  have heq : (∫ counts, H counts ∂idealCountLaw (n := n) P) =
      ∫ p, (if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        ∫ e, jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
            (curryCountTable p j) (curryCountTable e j) ∂mu -
          thresholdFunReal epsilon lambda (cellVector P j) else 0) ∂mu := by
    calc
      _ = ∫ pe, H (F pe) ∂mu.prod mu := by
        rw [← hmap, integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
      _ = ∫ p, ∫ e, H (F (p, e)) ∂mu ∂mu := integral_prod _ hflatInt
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with p
        have hgoodEq (e : (Fin d × Fin 4) → Nat) :
            idealPilotGoodBool (n := n) P
              (curryCountTable p, curryCountTable e) j =
            idealPilotGoodBool (n := n) P
              (curryCountTable p, fun _ _ => 0) j := by
          unfold idealPilotGoodBool
          congr 1
        by_cases hg : idealPilotGoodBool (n := n) P
            (curryCountTable p, fun _ _ => 0) j = true
        · simp_rw [H, F, hgoodEq, hg, if_true]
          have hstat : Integrable (fun e =>
              jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
                (curryCountTable p j) (curryCountTable e j)) mu := by
            let c := thresholdFunReal epsilon lambda
              (pilotMidpoint ((n : Real) / 8) d (curryCountTable p j))
            let s := (d : Real) ^ (1 / 4 : Real) * ∑ zeta : Cell,
              pilotRadius ((n : Real) / 8) d (curryCountTable p j) zeta
            have hs : 0 ≤ s := by
              dsimp [s]
              apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
              exact Finset.sum_nonneg fun z _ =>
                (pilotRadius_pos_of_pos (by positivity) (show 1 ≤ d by omega)
                  (curryCountTable p j) z).le
            apply Integrable.mono' (integrable_const (|c| + s))
              (measurable_of_countable _).aestronglyMeasurable
            filter_upwards [] with e
            rw [Real.norm_eq_abs]
            unfold jacksonCellStatistic
            dsimp only
            calc
              _ ≤ |c| + |min s (max (-s)
                  (jacksonCellRaw epsilon lambda (↑n / 8) d
                    (curryCountTable p j) (curryCountTable e j) - c))| :=
                abs_add_le _ _
              _ ≤ |c| + s := by
                exact add_le_add_right (abs_le.2
                  ⟨le_min (neg_le_self hs) (le_max_left _ _), min_le_left _ _⟩) |c|
          dsimp [E]
          unfold idealClippedCellPath
          rw [integral_sub]
          · rw [integral_const]
            simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
          · exact hstat
          · exact integrable_const _
        · have hg' := Bool.eq_false_of_not_eq_true hg
          rw [if_neg hg]
          apply integral_eq_zero_of_ae
          filter_upwards [] with e
          simp [H, F, hgoodEq e, hg']
  rw [show (∫ counts, (if idealPilotGoodBool (n := n) P counts j then
      idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j) else 0)
      ∂idealCountLaw (n := n) P) = ∫ counts, H counts ∂idealCountLaw (n := n) P by rfl,
    heq]
  calc
    _ ≤ ∫ p, if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        |(∫ e, jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
            (curryCountTable p j) (curryCountTable e j) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| else 0 ∂mu := by
      apply (abs_integral_le_integral_abs).trans_eq
      apply integral_congr_ae
      filter_upwards [] with p
      split <;> simp
    _ ≤ _ := by
      change (∫ p, if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        |(∫ e, jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
            (curryCountTable p j) (fun zeta => e (j, CellFourEquiv zeta)) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| else 0 ∂mu) ≤ _
      simpa only [mu, rate, poissonTableCell] using hflatBound

/-- The scalar cell bias is the sum of its good-pilot conditional clipping
contribution and the bad-pilot envelope contribution. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: uncappedJacksonCellBias_le_good_add_badEnvelope
lemma uncappedJacksonCellBias_le_good_add_badEnvelope
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (j : Fin d) (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    ∃ C : Real, 0 < C ∧
      uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
        (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
            (d : Real) ^ (1 / 4 : Real) +
          (32 * (3 * (1 + epsilon⁻¹) + 1)) *
            (2 / (jacksonDegree d : Real) +
              1 / (jacksonDegree d : Real) ^ 2)) *
          (Real.sqrt 32 * pilotRadiusConstant) *
          badPilotCellScale (n := n) P j +
        badPilotCellEnvelope (n := n) epsilon P j := by
  classical
  obtain ⟨C, hC, hgood⟩ :=
    idealGoodPilot_scalarMean_le epsilon he he' hn hd P j lambda hlambda
  refine ⟨C, hC, ?_⟩
  let E := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  let G := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then E counts else 0
  let B := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then 0 else E counts
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
    idealCountLaw_isProbabilityMeasure P
  have hE := idealClippedCell_error_integrable epsilon he hn (show 1 ≤ d by omega)
    P j lambda hlambda
  have hG : Integrable G (idealCountLaw (n := n) P) := by
    let A := {counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) |
      idealPilotGoodBool (n := n) P counts j = true}
    have hA : MeasurableSet A := MeasurableSet.of_discrete
    apply (hE.indicator hA).congr
    filter_upwards [] with counts
    by_cases hg : idealPilotGoodBool (n := n) P counts j = true
    · simp [G, E, A, Set.indicator, hg]
    · have hg' := Bool.eq_false_of_not_eq_true hg
      simp [G, E, A, Set.indicator, hg']
  have hB : Integrable B (idealCountLaw (n := n) P) := by
    exact (hE.sub hG).congr (Filter.Eventually.of_forall fun counts => by
      by_cases hg : idealPilotGoodBool (n := n) P counts j = true
      · simp [E, G, B, hg]
      · have hg' := Bool.eq_false_of_not_eq_true hg
        simp [E, G, B, hg'])
  have hstat : Integrable (fun counts =>
      idealClippedCellPath (n := n) epsilon lambda counts j)
      (idealCountLaw (n := n) P) := by
    apply (hE.add (integrable_const
      (thresholdFunReal epsilon lambda (cellVector P j)))).congr
    filter_upwards [] with counts
    dsimp [E]
    ring
  have hbias : uncappedJacksonCellBias (n := n) epsilon lambda P j =
      |∫ counts, E counts ∂idealCountLaw (n := n) P| := by
    unfold uncappedJacksonCellBias expectedUncappedJacksonCell
    rw [integral_sub]
    · rw [integral_const]
      simp [idealClippedCellPath]
    · simpa [idealClippedCellPath] using hstat
    · exact integrable_const _
  rw [hbias]
  have hsplit : (∫ counts, E counts ∂idealCountLaw (n := n) P) =
      (∫ counts, G counts ∂idealCountLaw (n := n) P) +
        ∫ counts, B counts ∂idealCountLaw (n := n) P := by
    rw [← integral_add hG hB]
    apply integral_congr_ae
    filter_upwards [] with counts
    by_cases hg : idealPilotGoodBool (n := n) P counts j = true
    · simp [E, G, B, hg]
    · have hg' := Bool.eq_false_of_not_eq_true hg
      simp [E, G, B, hg']
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  exact add_le_add hgood
    (idealBadPilot_scalarMean_le_envelope epsilon he hn (show 1 ≤ d by omega)
      P j lambda hlambda)

/-- The logarithmic factor times the negative three-sixteenths power is
uniformly bounded on the paper's large-alphabet branch. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: logAlphabet_mul_rpow_neg_three_sixteenths_le
lemma logAlphabet_mul_rpow_neg_three_sixteenths_le
    {d : Nat} (hd : 16 ≤ d) :
    logAlphabet d * (d : Real) ^ (-(3 / 16 : Real)) ≤ 19 / 3 := by
  have hD : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hD0 : (0 : Real) ≤ d := le_trans (by norm_num) hD
  have hDpos : (0 : Real) < d := lt_of_lt_of_le (by norm_num) hD
  have hpow0 : 0 ≤ (d : Real) ^ (-(3 / 16 : Real)) := Real.rpow_nonneg hD0 _
  have hpowa : (d : Real) ^ (-(3 / 16 : Real)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD
      (by norm_num : (-(3 / 16 : Real)) ≤ 0)
  have hlog := Real.log_le_rpow_div hD0 (show 0 < (3 / 16 : Real) by norm_num)
  have hmul : Real.log d * (d : Real) ^ (-(3 / 16 : Real)) ≤ 16 / 3 := by
    calc
      _ ≤ ((d : Real) ^ (3 / 16 : Real) / (3 / 16 : Real)) *
          (d : Real) ^ (-(3 / 16 : Real)) :=
        mul_le_mul_of_nonneg_right hlog hpow0
      _ = 16 / 3 := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hDpos]
        norm_num
  rw [show logAlphabet d = 1 + Real.log d by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt (lt_of_lt_of_le (by norm_num) hD)),
      Real.log_exp]]
  nlinarith

/-- The logarithm divided by the paper's Jackson degree is uniformly
bounded. With [the specified inputs and conditions](hyp:d), [the stated relationship holds](goal). -/
-- @node: logAlphabet_div_jacksonDegree_le
lemma logAlphabet_div_jacksonDegree_le {d : Nat} :
    logAlphabet d / (jacksonDegree d : Real) ≤ 768 := by
  let L := logAlphabet d
  let q := ⌊jacksonDegreeConstant * L⌋₊
  let K := jacksonDegree d
  have hK2 : (2 : Real) ≤ K := by
    exact_mod_cast (show 2 ≤ K by simp [K, jacksonDegree])
  have hqK : (q : Real) ≤ K := by
    exact_mod_cast (show q ≤ K by
      dsimp [q, K, L]
      exact le_max_right _ _)
  have hfloor := Nat.lt_floor_add_one (jacksonDegreeConstant * L)
  have hscale : L < 512 * ((q : Real) + 1) := by
    change L < 512 * (((⌊jacksonDegreeConstant * L⌋₊ : Nat) : Real) + 1)
    norm_num [jacksonDegreeConstant] at hfloor ⊢
    nlinarith
  have hq1 : (q : Real) + 1 ≤ (3 / 2 : Real) * K := by nlinarith
  have hLK : L ≤ 768 * K := by nlinarith
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hK2)).2 (by nlinarith)

/-- The complete good-pilot clipping coefficient loses one logarithmic
factor uniformly in the alphabet size. With [the specified inputs and conditions](hyp:d,hd,C,A,hC,hA), [the stated relationship holds](goal). -/
-- @node: goodPilot_clippingCoefficient_mul_log_le
lemma goodPilot_clippingCoefficient_mul_log_le
    {d : Nat} (hd : 16 ≤ d) (C A : Real) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    logAlphabet d *
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
          (d : Real) ^ (1 / 4 : Real) +
        A * (2 / (jacksonDegree d : Real) +
          1 / (jacksonDegree d : Real) ^ 2)) ≤
      4 * C ^ 2 * Real.exp 123 * (19 / 3) + A * 1920 := by
  have hDpos : (0 : Real) < d := by positivity
  have hratio : (d : Real) ^ (1 / 16 : Real) / (d : Real) ^ (1 / 4 : Real) =
      (d : Real) ^ (-(3 / 16 : Real)) := by
    rw [← Real.rpow_sub hDpos]
    norm_num
  have hLK := logAlphabet_div_jacksonDegree_le (d := d)
  have hK2 : (2 : Real) ≤ jacksonDegree d := by
    exact_mod_cast (show 2 ≤ jacksonDegree d by simp [jacksonDegree])
  have hL0 : 0 ≤ logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) hDpos.ne', Real.log_exp]
    exact add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega)))
  have hKpos : (0 : Real) < jacksonDegree d := lt_of_lt_of_le (by norm_num) hK2
  have hLK2 : logAlphabet d / (jacksonDegree d : Real) ^ 2 ≤ 384 := by
    calc
      _ = (logAlphabet d / (jacksonDegree d : Real)) /
          (jacksonDegree d : Real) := by field_simp
      _ ≤ 768 / (jacksonDegree d : Real) :=
        div_le_div_of_nonneg_right hLK hKpos.le
      _ ≤ 384 := (div_le_iff₀ hKpos).2 (by nlinarith)
  rw [show 4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
      (d : Real) ^ (1 / 4 : Real) =
      4 * C ^ 2 * Real.exp 123 *
        ((d : Real) ^ (1 / 16 : Real) / (d : Real) ^ (1 / 4 : Real)) by ring,
    hratio]
  have hp := logAlphabet_mul_rpow_neg_three_sixteenths_le hd
  calc
    _ = 4 * C ^ 2 * Real.exp 123 *
          (logAlphabet d * (d : Real) ^ (-(3 / 16 : Real))) +
        A * (2 * (logAlphabet d / (jacksonDegree d : Real)) +
          logAlphabet d / (jacksonDegree d : Real) ^ 2) := by ring
    _ ≤ _ := by gcongr <;> nlinarith

/-- Boundary adaptivity removes the additive empirical-radius floor: inside
the truncated nonnegative confidence interval, the product of the distances
to its endpoints is controlled by the true intensity times the radius level. With [the specified inputs and conditions](hyp:H,delta,x,q,hH,hdelta,hx0,hqmem), [the stated relationship holds](goal). -/
-- @node: truncatedEmpiricalInterval_boundaryProduct_le
lemma truncatedEmpiricalInterval_boundaryProduct_le
    (H delta x q : Real) (hH : 1 ≤ H) (hdelta : 0 < delta) (hx0 : 0 ≤ x)
    (hqmem : q ∈ Set.Icc (max 0 (x - H * (Real.sqrt (x * delta) + delta)))
      (x + H * (Real.sqrt (x * delta) + delta))) :
    (q - max 0 (x - H * (Real.sqrt (x * delta) + delta))) *
        ((x + H * (Real.sqrt (x * delta) + delta)) - q) ≤
      8 * H ^ 2 * q * delta := by
  let s := Real.sqrt (x * delta)
  let h := H * (s + delta)
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x * delta := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hx0 hdelta.le)
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hq0 : 0 ≤ q := le_trans (le_max_left _ _) hqmem.1
  change (q - max 0 (x - h)) * ((x + h) - q) ≤ 8 * H ^ 2 * q * delta
  by_cases hsmall : x ≤ 2 * h
  · have hsdelta : s ≤ (2 * H + 1) * delta := by
      by_contra hnot
      have hlt : (2 * H + 1) * delta < s := lt_of_not_ge hnot
      have hpos : 0 < (2 * H + 1) * delta := by positivity
      have hsquare : ((2 * H + 1) * delta) ^ 2 < s ^ 2 :=
        (sq_lt_sq₀ hpos.le hs0).2 hlt
      dsimp [h] at hsmall
      rw [hs2] at hsquare
      nlinarith
    have hh : h ≤ 2 * H * (H + 1) * delta := by
      dsimp [h]
      have := mul_le_mul_of_nonneg_left hsdelta hH0
      nlinarith
    have hleft : q - max 0 (x - h) ≤ q := by
      linarith [le_max_left (0 : Real) (x - h)]
    have hright : x + h - q ≤ 2 * h := by
      have hlo := hqmem.1
      change max 0 (x - h) ≤ q at hlo
      have hxmh : x - h ≤ q := le_trans (le_max_right _ _) hlo
      linarith
    have hleft0 : 0 ≤ q - max 0 (x - h) := by simpa using hqmem.1
    have hright0 : 0 ≤ x + h - q := by simpa using hqmem.2
    calc
      _ ≤ q * (2 * h) := mul_le_mul hleft hright hright0 hq0
      _ ≤ 8 * H ^ 2 * q * delta := by
        have hqh := mul_le_mul_of_nonneg_left hh hq0
        have hcoef : 4 * H * (H + 1) ≤ 8 * H ^ 2 := by
          nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hH)]
        have hc := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hq0 hdelta.le)
        nlinarith
  · have hlarge : 2 * h < x := lt_of_not_ge hsmall
    have hxmh : 0 < x - h := by linarith
    rw [max_eq_right hxmh.le]
    have hqlo : x - h ≤ q := by
      simpa [h, s, max_eq_right hxmh.le] using hqmem.1
    have hxq : x < 2 * q := by linarith
    have hHdelta_q : H * delta < q := by
      have hhdelta : H * delta ≤ h := by dsimp [h]; nlinarith
      nlinarith
    have hdeltaq : delta ≤ q := by nlinarith
    have hxd : x * delta ≤ 2 * q * delta :=
      mul_le_mul_of_nonneg_right (le_of_lt hxq) hdelta.le
    have hdd : delta ^ 2 ≤ q * delta := by nlinarith
    have hh2 : h ^ 2 ≤ 6 * H ^ 2 * q * delta := by
      dsimp [h]
      rw [mul_pow]
      have hsplus : (s + delta) ^ 2 ≤ 2 * s ^ 2 + 2 * delta ^ 2 := by
        nlinarith [sq_nonneg (s - delta)]
      rw [hs2] at hsplus
      have hmul := mul_le_mul_of_nonneg_left hsplus (sq_nonneg H)
      have hxd' := mul_le_mul_of_nonneg_left hxd (sq_nonneg H)
      have hdd' := mul_le_mul_of_nonneg_left hdd (sq_nonneg H)
      nlinarith
    calc
      (q - (x - h)) * (x + h - q) ≤ h ^ 2 := by
        nlinarith [sq_nonneg (q - x)]
      _ ≤ 8 * H ^ 2 * q * delta := by
        have : 0 ≤ H ^ 2 * q * delta := by positivity
        nlinarith

/-- On a paper good-pilot draw, each physical Jackson boundary product has
the sharp true-rate scale, including at a null coordinate. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealPilotGood_boundaryProduct_le
lemma idealPilotGood_boundaryProduct_le
    {n d : Nat} (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat))
    (j : Fin d) (hgood : idealPilotGood (n := n) P counts j) (zeta : Cell) :
    let m : Real := (n : Real) / 8
    let q := cellVector P j zeta
    let c := pilotMidpoint m d (counts.1 j) zeta
    let r := pilotRadius m d (counts.1 j) zeta
    (q - (c - r)) * ((c + r) - q) ≤
      8 * pilotRadiusConstant ^ 2 * q * (logAlphabet d / m) := by
  dsimp only
  let m : Real := (n : Real) / 8
  let x := pilotCenter m (counts.1 j) zeta
  let q := cellVector P j zeta
  let delta := logAlphabet d / m
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    have : (1 : Real) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg this]
  have hdelta : 0 < delta := div_pos hL hm
  have hx0 : 0 ≤ x := by dsimp [x, pilotCenter]; positivity
  have hmem : q ∈ Set.Icc
      (max 0 (x - pilotRadiusConstant * (Real.sqrt (x * delta) + delta)))
      (x + pilotRadiusConstant * (Real.sqrt (x * delta) + delta)) := by
    have hg := idealPilotGood_center_mem_radius hn P counts j hgood zeta
    rw [abs_le] at hg
    constructor
    · change max 0 (x - pilotRadiusConstant *
          (Real.sqrt (x * delta) + delta)) ≤ q
      have hc : pilotMidpoint m d (counts.1 j) zeta -
          pilotRadius m d (counts.1 j) zeta =
          max 0 (x - pilotRadiusConstant *
            (Real.sqrt (x * delta) + delta)) := by
        dsimp [x, delta]
        unfold pilotMidpoint pilotRadius pilotLower pilotUpper pilotHalfWidth
        ring
      rw [← hc]
      linarith
    · change q ≤ x + pilotRadiusConstant *
          (Real.sqrt (x * delta) + delta)
      have hc : pilotMidpoint m d (counts.1 j) zeta +
          pilotRadius m d (counts.1 j) zeta =
          x + pilotRadiusConstant * (Real.sqrt (x * delta) + delta) := by
        dsimp [x, delta]
        unfold pilotMidpoint pilotRadius pilotLower pilotUpper pilotHalfWidth
        ring
      rw [← hc]
      linarith
  have hp := truncatedEmpiricalInterval_boundaryProduct_le
    pilotRadiusConstant delta x q (by unfold pilotRadiusConstant; norm_num)
      hdelta hx0 hmem
  have hlower : pilotMidpoint m d (counts.1 j) zeta -
      pilotRadius m d (counts.1 j) zeta =
      max 0 (x - pilotRadiusConstant * (Real.sqrt (x * delta) + delta)) := by
    dsimp [x, delta]
    unfold pilotMidpoint pilotRadius pilotLower pilotUpper pilotHalfWidth
    ring
  have hupper : pilotMidpoint m d (counts.1 j) zeta +
      pilotRadius m d (counts.1 j) zeta =
      x + pilotRadiusConstant * (Real.sqrt (x * delta) + delta) := by
    dsimp [x, delta]
    unfold pilotMidpoint pilotRadius pilotLower pilotUpper pilotHalfWidth
    ring
  simpa [m, q, delta, hlower, hupper] using hp

end CausalSmith.Stat.DiscreteBudgetvalueCurve
