module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BadPilotMoment
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.GoodPilotCellOuterMoment

/-! Deterministic clipping bounds for bad pilot cells. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open scoped BigOperators NNReal

/-- Truncating the pilot interval at zero moves its midpoint from the empirical
center by at most the original half-width. With [the specified inputs and conditions](hyp:m,hm,d,hd,pilot,z), [the stated relationship holds](goal). -/
-- @node: pilotMidpoint_sub_center_abs_le_halfWidth
lemma pilotMidpoint_sub_center_abs_le_halfWidth {m : ℝ} (hm : 0 < m)
    {d : ℕ} (hd : 1 ≤ d) (pilot : Cell → ℕ) (z : Cell) :
    |pilotMidpoint m d pilot z - pilotCenter m pilot z| ≤
      pilotHalfWidth m d pilot z := by
  have hc : 0 ≤ pilotCenter m pilot z := by unfold pilotCenter; positivity
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdR]
  have hh : 0 ≤ pilotHalfWidth m d pilot z := by
    unfold pilotHalfWidth pilotRadiusConstant
    positivity
  unfold pilotMidpoint pilotLower pilotUpper
  by_cases h : 0 ≤ pilotCenter m pilot z - pilotHalfWidth m d pilot z
  · rw [max_eq_right h]
    simpa using hh
  · rw [max_eq_left (le_of_not_ge h)]
    rw [abs_le]
    constructor <;> linarith

/-- At every shadow price, clipping bounds a cell error by the empirical
center score and the clipping scale. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: idealClippedCell_error_le_badScore
lemma idealClippedCell_error_le_badScore {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (lambda : ℝ) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    |idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤
      ((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) *
        ∑ z : Cell,
          (|pilotCenter ((n : ℝ) / 8) (counts.1 j) z - cellVector P j z| +
            pilotHalfWidth ((n : ℝ) / 8) d (counts.1 j) z) := by
  let m : ℝ := (n : ℝ) / 8
  let pilot := counts.1 j
  let center := pilotMidpoint m d pilot
  let scale := (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ z : Cell, pilotRadius m d pilot z
  let A : ℝ := 3 * (1 + epsilon⁻¹) + 1
  let S : ℝ := ∑ z : Cell,
    (|pilotCenter m pilot z - cellVector P j z| + pilotHalfWidth m d pilot z)
  have hm : 0 < m := by dsimp [m]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hdR : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hq (z : Cell) : 0 ≤ cellVector P j z := by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity
  have hcenter (z : Cell) : 0 ≤ center z := by
    have hc : 0 ≤ pilotCenter m pilot z := by unfold pilotCenter; positivity
    have hL : 0 < logAlphabet d := by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      have hdR' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith [Real.log_nonneg hdR']
    have hh : 0 ≤ pilotHalfWidth m d pilot z := by
      unfold pilotHalfWidth pilotRadiusConstant
      positivity
    dsimp [center]
    unfold pilotMidpoint pilotLower pilotUpper
    have hlo : 0 ≤ max 0 (pilotCenter m pilot z - pilotHalfWidth m d pilot z) :=
      le_max_left _ _
    linarith
  have hmid (z : Cell) :
      |center z - cellVector P j z| ≤
        |pilotCenter m pilot z - cellVector P j z| +
          pilotHalfWidth m d pilot z := by
    calc
      _ ≤ |center z - pilotCenter m pilot z| +
          |pilotCenter m pilot z - cellVector P j z| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          abs_add_le (center z - pilotCenter m pilot z)
            (pilotCenter m pilot z - cellVector P j z)
      _ ≤ _ := by
        have h := pilotMidpoint_sub_center_abs_le_halfWidth hm hd pilot z
        linarith
  have hthreshold :
      |thresholdFunReal epsilon lambda center -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤ A * S := by
    calc
      _ ≤ A * ∑ z, |center z - cellVector P j z| :=
        budget_thresholdFunReal_pointwise_lipschitz he lambda hlambda
          center (cellVector P j) hcenter hq
      _ ≤ A * S := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact Finset.sum_le_sum fun z _ => hmid z
  have hradius (z : Cell) :
      pilotRadius m d pilot z ≤ pilotHalfWidth m d pilot z :=
    pilotRadius_le_pilotHalfWidth hm hd pilot z
  have hscale : scale ≤ (d : ℝ) ^ (1 / 4 : ℝ) * S := by
    dsimp [scale, S]
    apply mul_le_mul_of_nonneg_left _ hdR
    calc
      (∑ z, pilotRadius m d pilot z) ≤
          ∑ z, pilotHalfWidth m d pilot z :=
        Finset.sum_le_sum fun z _ => hradius z
      _ ≤ ∑ z, (|pilotCenter m pilot z - cellVector P j z| +
          pilotHalfWidth m d pilot z) := by
        apply Finset.sum_le_sum
        intro z _
        linarith [abs_nonneg (pilotCenter m pilot z - cellVector P j z)]
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    exact mul_nonneg hdR (Finset.sum_nonneg fun z _ =>
      (pilotRadius_pos_of_pos hm hd pilot z).le)
  let delta := jacksonCellRaw epsilon lambda m d pilot (counts.2 j) -
    thresholdFunReal epsilon lambda center
  have hclip : |min scale (max (-scale) delta)| ≤ scale := by
    rw [abs_le]
    constructor
    · exact le_min (by linarith) (le_max_left _ _)
    · exact min_le_left _ _
  unfold idealClippedCellPath jacksonCellStatistic
  change |thresholdFunReal epsilon lambda center +
      min scale (max (-scale) delta) -
      thresholdFunReal epsilon lambda (cellVector P j)| ≤ _
  calc
    _ ≤ |thresholdFunReal epsilon lambda center -
          thresholdFunReal epsilon lambda (cellVector P j)| +
        |min scale (max (-scale) delta)| := by
      calc
        _ = |(thresholdFunReal epsilon lambda center -
            thresholdFunReal epsilon lambda (cellVector P j)) +
              min scale (max (-scale) delta)| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ A * S + scale := add_le_add hthreshold hclip
    _ ≤ A * S + (d : ℝ) ^ (1 / 4 : ℝ) * S := by linarith
    _ = (A + (d : ℝ) ^ (1 / 4 : ℝ)) * S := by ring

/-- The continuum supremum of one clipped-cell error is bounded by the same
four-coordinate empirical score as every pointwise error. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts,j), [the stated relationship holds](goal). -/
-- @node: idealClippedCell_sSup_le_badScore
lemma idealClippedCell_sSup_le_badScore {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) :
    sSup ((fun lambda : ℝ =>
      |idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j)|) ''
        Set.Icc 0 1) ≤
      ((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) *
        ∑ z : Cell,
          (|pilotCenter ((n : ℝ) / 8) (counts.1 j) z - cellVector P j z| +
            pilotHalfWidth ((n : ℝ) / 8) d (counts.1 j) z) := by
  apply csSup_le
  · exact ⟨|idealClippedCellPath (n := n) epsilon 0 counts j -
      thresholdFunReal epsilon 0 (cellVector P j)|, ⟨0, by simp, rfl⟩⟩
  · rintro y ⟨lambda, hlambda, rfl⟩
    exact idealClippedCell_error_le_badScore he hn hd P counts j lambda hlambda

/-- In the one-cell pilot/evaluation experiment, the squared bad-pilot
continuum envelope is controlled by the promoted four-coordinate moment. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: localBadPilotCellEnvelope_sq_integral_le
lemma localBadPilotCellEnvelope_sq_integral_le {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    let m : ℝ := (n : ℝ) / 8
    let mNN : ℝ≥0 := Real.toNNReal m
    let q : Fin 4 → ℝ≥0 := fun i =>
      Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
    let μ := poissonTableLaw (fun i => mNN * q i)
    let f : ((Fin 4 → ℕ) × (Fin 4 → ℕ)) → ℝ := fun pe =>
      let counts :=
        (curryCountTable (singleCellCountTable j pe.1),
          curryCountTable (singleCellCountTable j pe.2))
      if idealPilotGoodBool (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1) ^ 2
    Integrable f (μ.prod μ) ∧ (∫ pe, f pe ∂μ.prod μ) ≤
      ((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        ((pilotRadiusConstant / universalH) ^ 2 * productMomentConstant 4 2 *
          Real.exp (-20 * logAlphabet d) *
          badPilotCellScale (n := n) P j ^ 2) := by
  classical
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let mNN : ℝ≥0 := Real.toNNReal m
  let q : Fin 4 → ℝ≥0 := fun i =>
    Real.toNNReal (cellVector P j (CellFourEquiv.symm i))
  let μ := poissonTableLaw (fun i => mNN * q i)
  letI : IsProbabilityMeasure μ := by dsimp [μ, poissonTableLaw]; infer_instance
  let B : ℝ := (3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)
  let scoreSq : (Fin 4 → ℕ) → ℝ := fun p =>
    if (∀ z : Cell,
        |pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| ≤
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z / 4)
    then 0 else
      (∑ z : Cell,
        (|pilotCenter m (fun z => p (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth m d (fun z => p (CellFourEquiv z)) z)) ^ 2
  have hscoreInt : Integrable scoreSq μ := by
    simpa [scoreSq, μ, q, m, mNN] using
      pilotCell_badScore_sq_integrable P j hn hd
  have hdomInt : Integrable (fun pe : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      B ^ 2 * scoreSq pe.1) (μ.prod μ) := by
    have hp : Integrable (fun pe : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
        scoreSq pe.1) (μ.prod μ) := by
      change Integrable (scoreSq ∘ Prod.fst) (μ.prod μ)
      exact ((measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp
        (measurable_of_countable scoreSq).aestronglyMeasurable).2 hscoreInt
    exact hp.const_mul _
  have hpoint (pe : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :
      (let counts :=
        (curryCountTable (singleCellCountTable j pe.1),
          curryCountTable (singleCellCountTable j pe.2))
       if idealPilotGoodBool (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1) ^ 2) ≤ B ^ 2 * scoreSq pe.1 := by
    dsimp only
    let counts :=
      (curryCountTable (singleCellCountTable j pe.1),
        curryCountTable (singleCellCountTable j pe.2))
    have hcell : counts.1 j = fun z => pe.1 (CellFourEquiv z) := by
      funext z
      simp [counts, curryCountTable, singleCellCountTable]
    have hgood : idealPilotGood (n := n) P counts j ↔
        ∀ z : Cell,
          |pilotCenter m (fun z => pe.1 (CellFourEquiv z)) z - cellVector P j z| ≤
            pilotHalfWidth m d (fun z => pe.1 (CellFourEquiv z)) z / 4 := by
      unfold idealPilotGood
      simpa [m, hcell]
    by_cases hg : idealPilotGood (n := n) P counts j
    · have hgb : idealPilotGoodBool (n := n) P counts j = true :=
        (idealPilotGoodBool_eq_true P counts j).2 hg
      rw [hgb, if_pos rfl]
      have hs : scoreSq pe.1 = 0 := by
        dsimp [scoreSq]
        rw [if_pos (hgood.mp hg)]
      rw [hs]
      positivity
    · have hgb : idealPilotGoodBool (n := n) P counts j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun hb => hg ((idealPilotGoodBool_eq_true P counts j).1 hb)
      rw [hgb, if_neg (by decide)]
      have hs : scoreSq pe.1 =
          (∑ z : Cell,
            (|pilotCenter m (fun z => pe.1 (CellFourEquiv z)) z -
                cellVector P j z| +
              pilotHalfWidth m d (fun z => pe.1 (CellFourEquiv z)) z)) ^ 2 := by
        dsimp [scoreSq]
        rw [if_neg (fun h => hg (hgood.mpr h))]
      rw [hs]
      have hsup := idealClippedCell_sSup_le_badScore he hn hd P counts j
      have hpilot : curryCountTable (singleCellCountTable j pe.1) j =
          fun z => pe.1 (CellFourEquiv z) := by
        funext z
        simp [curryCountTable, singleCellCountTable]
      rw [hcell] at hsup
      have hB0 : 0 ≤ B := by dsimp [B]; positivity
      have hS0 : 0 ≤ ∑ z : Cell,
          (|pilotCenter m (fun z => pe.1 (CellFourEquiv z)) z - cellVector P j z| +
            pilotHalfWidth m d (fun z => pe.1 (CellFourEquiv z)) z) := by
        apply Finset.sum_nonneg
        intro z _
        have hm : 0 < m := by dsimp [m]; positivity
        have hh : 0 ≤ pilotHalfWidth m d (fun z => pe.1 (CellFourEquiv z)) z :=
          le_trans (pilotRadius_pos_of_pos hm hd _ z).le
            (pilotRadius_le_pilotHalfWidth hm hd _ z)
        positivity
      let Sset := (fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1
      have hSbdd : BddAbove Sset := by
        refine ⟨B * ∑ z : Cell,
          (|pilotCenter m (fun z => pe.1 (CellFourEquiv z)) z - cellVector P j z| +
            pilotHalfWidth m d (fun z => pe.1 (CellFourEquiv z)) z), ?_⟩
        rintro y ⟨lambda, hlambda, rfl⟩
        have h := idealClippedCell_error_le_badScore he hn hd P counts j lambda hlambda
        rw [hcell] at h
        simpa [B, m, counts] using h
      have hzeroMem : |idealClippedCellPath (n := n) epsilon 0 counts j -
          thresholdFunReal epsilon 0 (cellVector P j)| ∈ Sset :=
        ⟨0, by simp, rfl⟩
      have hsup0 : 0 ≤ sSup Sset :=
        le_trans (abs_nonneg _) (le_csSup hSbdd hzeroMem)
      have hsquared := (sq_le_sq₀ hsup0 (mul_nonneg hB0 hS0)).2
        (by simpa [Sset, counts, B, m] using hsup)
      simpa [Sset, counts, mul_pow] using hsquared
  have hfInt : Integrable (fun pe : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      let counts :=
        (curryCountTable (singleCellCountTable j pe.1),
          curryCountTable (singleCellCountTable j pe.2))
      if idealPilotGoodBool (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1) ^ 2) (μ.prod μ) := by
    apply hdomInt.mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with pe
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint pe
    · dsimp only
      split_ifs <;> positivity
  refine ⟨hfInt, ?_⟩
  calc
    _ ≤ ∫ pe, B ^ 2 * scoreSq pe.1 ∂μ.prod μ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun pe => by
          dsimp only
          split_ifs <;> positivity)
        hdomInt (Filter.Eventually.of_forall hpoint)
    _ = B ^ 2 * ∫ p, scoreSq p ∂μ := by
      rw [integral_const_mul, integral_fun_fst]
      simp
    _ ≤ B ^ 2 * ((pilotRadiusConstant / universalH) ^ 2 *
        productMomentConstant 4 2 * Real.exp (-20 * logAlphabet d) *
        badPilotCellScale (n := n) P j ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      simpa [scoreSq, μ, q, m, mNN] using
        pilotCell_badScore_sq_integral_le P j hn hd

/-- The local bad-pilot envelope estimate transports to the paper's full
curried ideal count experiment. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealBadPilotCellEnvelope_sq_integral_le
lemma idealBadPilotCellEnvelope_sq_integral_le {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    Integrable (fun counts =>
      if idealPilotGoodBool (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1) ^ 2) (idealCountLaw (n := n) P) ∧
    (∫ counts,
      (if idealPilotGoodBool (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1) ^ 2) ∂idealCountLaw (n := n) P) ≤
      ((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        ((pilotRadiusConstant / universalH) ^ 2 * productMomentConstant 4 2 *
          Real.exp (-20 * logAlphabet d) *
          badPilotCellScale (n := n) P j ^ 2) := by
  classical
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let μcell := poissonTableLaw (rate j)
  letI : IsProbabilityMeasure μ := by dsimp [μ, poissonTableLaw]; infer_instance
  let F : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) →
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) := fun pe =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let block : ((Fin d × Fin 4) → ℕ) → (Fin 4 → ℕ) := poissonTableCell j
  let g : ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → ℝ := fun counts =>
    if idealPilotGoodBool (n := n) P counts j then 0 else
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1) ^ 2
  let ell : ((Fin 4 → ℕ) × (Fin 4 → ℕ)) → ℝ := fun pe =>
    let counts :=
      (curryCountTable (singleCellCountTable j pe.1),
        curryCountTable (singleCellCountTable j pe.2))
    if idealPilotGoodBool (n := n) P counts j then 0 else
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1) ^ 2
  have hrate (i : Fin 4) : rate j i =
      Real.toNNReal ((n : ℝ) / 8) *
        Real.toNNReal (cellVector P j (CellFourEquiv.symm i)) := by
    apply NNReal.eq
    have hq : 0 ≤ cellVector P j (CellFourEquiv.symm i) := by
      change 0 ≤ (P.pmf
        (j, finTwoEquiv (CellFourEquiv.symm i).1,
          finTwoEquiv (CellFourEquiv.symm i).2)).toReal
      positivity
    simp [rate, idealFlatRate, Real.coe_toNNReal, hq,
      show 0 ≤ (n : ℝ) / 8 by positivity]
    exact mul_nonneg (by positivity) hq
  have hlocalPkg : Integrable ell (μcell.prod μcell) ∧
      (∫ pe, ell pe ∂μcell.prod μcell) ≤
      ((3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        ((pilotRadiusConstant / universalH) ^ 2 * productMomentConstant 4 2 *
          Real.exp (-20 * logAlphabet d) *
          badPilotCellScale (n := n) P j ^ 2) := by
    have hrates : rate j = fun i =>
        Real.toNNReal ((n : ℝ) / 8) *
          Real.toNNReal (cellVector P j (CellFourEquiv.symm i)) :=
      funext hrate
    rw [show μcell = poissonTableLaw (fun i =>
        Real.toNNReal ((n : ℝ) / 8) *
          Real.toNNReal (cellVector P j (CellFourEquiv.symm i))) by
      simp [μcell, hrates]]
    simpa [ell] using localBadPilotCellEnvelope_sq_integral_le he hn hd P j
  have hlocal := hlocalPkg.2
  have hblockMeas : Measurable block := by
    dsimp [block, poissonTableCell]
    fun_prop
  have hblockMap : Measure.map block μ = μcell := by
    simpa [block, μ, μcell] using
      (poissonTable_eval_cell_law rate j).map_eq
  have hpairMap : Measure.map (Prod.map block block) (μ.prod μ) =
      μcell.prod μcell := by
    rw [← Measure.map_prod_map μ μ hblockMeas hblockMeas,
      hblockMap]
  have hidentify (pe : (((Fin d × Fin 4) → ℕ) ×
      ((Fin d × Fin 4) → ℕ))) : g (F pe) = ell (block pe.1, block pe.2) := by
    let fullCounts := (curryCountTable pe.1, curryCountTable pe.2)
    let cellCounts :=
      (curryCountTable (singleCellCountTable j (block pe.1)),
        curryCountTable (singleCellCountTable j (block pe.2)))
    have hp : curryCountTable pe.1 j =
        curryCountTable (singleCellCountTable j (block pe.1)) j := by
      apply curryCountTable_eq_at_of_poissonTableCell_eq
      simp [block]
    have heval : curryCountTable pe.2 j =
        curryCountTable (singleCellCountTable j (block pe.2)) j := by
      apply curryCountTable_eq_at_of_poissonTableCell_eq
      simp [block]
    have hgood : idealPilotGoodBool (n := n) P fullCounts j =
        idealPilotGoodBool (n := n) P cellCounts j := by
      unfold idealPilotGoodBool
      congr 1
      apply propext
      unfold idealPilotGood
      rw [show fullCounts.1 j = cellCounts.1 j by exact hp]
    have hpath (lambda : ℝ) :
        idealClippedCellPath (n := n) epsilon lambda fullCounts j =
          idealClippedCellPath (n := n) epsilon lambda cellCounts j := by
      unfold idealClippedCellPath
      rw [show fullCounts.1 j = cellCounts.1 j by exact hp,
        show fullCounts.2 j = cellCounts.2 j by exact heval]
    change (if idealPilotGoodBool (n := n) P fullCounts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda fullCounts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) ^ 2) =
      (if idealPilotGoodBool (n := n) P cellCounts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda cellCounts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) ^ 2)
    rw [hgood]
    simp_rw [hpath]
  have hF : Measurable F := by fun_prop
  have hg : Measurable g := measurable_of_countable _
  have hell : Measurable ell := measurable_of_countable _
  have hmap : Measure.map F (μ.prod μ) = idealCountLaw (n := n) P := by
    simpa [F, μ, rate] using map_flatIdealCountLaw (n := n) P
  have hellMap : Integrable ell
      (Measure.map (Prod.map block block) (μ.prod μ)) := by
    rw [hpairMap]
    exact hlocalPkg.1
  have hflatEll : Integrable (ell ∘ Prod.map block block) (μ.prod μ) :=
    hellMap.comp_aemeasurable (by fun_prop)
  have hflatG : Integrable (g ∘ F) (μ.prod μ) := by
    apply hflatEll.congr
    exact Filter.Eventually.of_forall fun pe => (hidentify pe).symm
  have hgMap : Integrable g (Measure.map F (μ.prod μ)) :=
    (integrable_map_measure hg.aestronglyMeasurable hF.aemeasurable).2 hflatG
  have hgIdeal : Integrable g (idealCountLaw (n := n) P) := by
    rw [← hmap]
    exact hgMap
  refine ⟨hgIdeal, ?_⟩
  calc
    _ = ∫ pe, g (F pe) ∂μ.prod μ := by
      rw [← hmap, integral_map hF.aemeasurable hg.aestronglyMeasurable]
    _ = ∫ pe, ell (Prod.map block block pe) ∂μ.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hidentify
    _ = ∫ pe, ell pe ∂μcell.prod μcell := by
      rw [← hpairMap, integral_map (by fun_prop) hell.aestronglyMeasurable]
    _ ≤ _ := hlocal

/-- Equation (28): one epsilon-dependent constant controls every bad-pilot
cell envelope in the full ideal count experiment. With [the specified inputs and conditions](hyp:epsilon,he), [the stated relationship holds](goal). -/
-- @node: badPilotCellEnvelope_le
lemma badPilotCellEnvelope_le (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (j : Fin d),
        badPilotCellEnvelope (n := n) epsilon P j ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) *
            Real.exp (-10 * logAlphabet d) *
            badPilotCellScale (n := n) P j := by
  classical
  let A : ℝ := 3 * (1 + epsilon⁻¹) + 1
  let K : ℝ := (pilotRadiusConstant / universalH) ^ 2 *
    productMomentConstant 4 2
  let C : ℝ := (A + 1) * Real.sqrt K
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by
    dsimp [K]
    have hpilot : 0 < pilotRadiusConstant := by
      unfold pilotRadiusConstant
      norm_num
    exact mul_pos (sq_pos_of_pos (div_pos hpilot universalH_pos))
      (productMomentConstant_pos 4 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n d hn hd P j
  let r : ℝ := (d : ℝ) ^ (1 / 4 : ℝ)
  let E : ℝ := Real.exp (-10 * logAlphabet d)
  let S : ℝ := badPilotCellScale (n := n) P j
  let I : ℝ := ∫ counts,
    (if idealPilotGoodBool (n := n) P counts j then 0 else
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1) ^ 2) ∂idealCountLaw (n := n) P
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 1 ≤ r := by
    dsimp [r]
    exact Real.one_le_rpow hdR (by norm_num)
  have hB : A + r ≤ (A + 1) * r := by
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hr)]
  have hB0 : 0 ≤ A + r := by positivity
  have hcoef : (A + r) ^ 2 ≤ (A + 1) ^ 2 * r ^ 2 := by
    have := pow_le_pow_left₀ hB0 hB 2
    nlinarith
  have hS : 0 ≤ S := by
    dsimp [S, badPilotCellScale]
    have hm : 0 < (n : ℝ) / 8 := by positivity
    have hL : 0 < logAlphabet d := by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      linarith [Real.log_nonneg hdR]
    positivity
  have hI : I ≤ (A + r) ^ 2 *
      (K * Real.exp (-20 * logAlphabet d) * S ^ 2) := by
    dsimp [I, A, r, K, S]
    simpa [mul_assoc] using
      (idealBadPilotCellEnvelope_sq_integral_le he hn hd P j).2
  have htail0 : 0 ≤ K * Real.exp (-20 * logAlphabet d) * S ^ 2 := by
    positivity
  have hI' : I ≤ (A + 1) ^ 2 * r ^ 2 *
      (K * Real.exp (-20 * logAlphabet d) * S ^ 2) :=
    le_trans hI (mul_le_mul_of_nonneg_right hcoef htail0)
  have hr2 : r ^ 2 = (d : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  have hE2 : E ^ 2 = Real.exp (-20 * logAlphabet d) := by
    dsimp [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrtK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hy : 0 ≤ C * r * E * S := by positivity
  have hIy : I ≤ (C * r * E * S) ^ 2 := by
    calc
      I ≤ (A + 1) ^ 2 * r ^ 2 *
          (K * Real.exp (-20 * logAlphabet d) * S ^ 2) := hI'
      _ = (C * r * E * S) ^ 2 := by
        simp only [mul_pow]
        rw [show C = (A + 1) * Real.sqrt K by rfl, mul_pow,
          hsqrtK, hE2]
        ring
  have hbool : (∫ counts,
      ((if idealPilotGood (n := n) P counts j then 0 else
        sSup ((fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j)|) ''
            Set.Icc 0 1)) ^ 2) ∂idealCountLaw (n := n) P) = I := by
    dsimp [I]
    apply integral_congr_ae
    filter_upwards [] with counts
    by_cases hg : idealPilotGood (n := n) P counts j
    · have hb := (idealPilotGoodBool_eq_true P counts j).2 hg
      simp [hg, hb]
    · have hb : idealPilotGoodBool (n := n) P counts j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hg ((idealPilotGoodBool_eq_true P counts j).1 ht)
      simp [hg, hb]
  unfold badPilotCellEnvelope
  rw [hbool]
  exact (Real.sqrt_le_left hy).2 hIy

/-- Equation (28) also supplies the squared-norm integrability of each
bad-pilot cell Path required by later Bochner arguments. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealBadPilotCellPath_norm_sq_integrable
lemma idealBadPilotCellPath_norm_sq_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    Integrable (fun counts =>
      ‖idealPilotErrorCellPath epsilon P counts j false
        (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false)‖ ^ 2)
      (idealCountLaw (n := n) P) := by
  classical
  let hcont := fun counts =>
    idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false
  let envelopeSq := fun counts :
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) =>
    if idealPilotGoodBool (n := n) P counts j then 0 else
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1) ^ 2
  have henv : Integrable envelopeSq (idealCountLaw (n := n) P) := by
    simpa [envelopeSq] using
      (idealBadPilotCellEnvelope_sq_integral_le he hn hd P j).1
  apply henv.congr
  filter_upwards [] with counts
  rw [idealPilotErrorCellPath_norm_eq_sSup epsilon P counts j false (hcont counts)]
  by_cases hg : idealPilotGood (n := n) P counts j
  · have hb := (idealPilotGoodBool_eq_true P counts j).2 hg
    simp [envelopeSq, hb, idealPilotErrorCell, hg]
  · have hb : idealPilotGoodBool (n := n) P counts j = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun ht => hg ((idealPilotGoodBool_eq_true P counts j).1 ht)
    simp [envelopeSq, hb, idealPilotErrorCell, idealClippedCellPath, hg]

/-- The finite sum of bad-pilot cell squared Path norms is integrable. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). -/
-- @node: idealBadPilotCellPath_norm_sq_sum_integrable
lemma idealBadPilotCellPath_norm_sq_sum_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) :
    Integrable (fun counts => ∑ j : Fin d,
      ‖idealPilotErrorCellPath epsilon P counts j false
        (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j false)‖ ^ 2)
      (idealCountLaw (n := n) P) := by
  apply integrable_finsetSum
  intro j _
  exact idealBadPilotCellPath_norm_sq_integrable epsilon he hn hd P j

/-- For an arbitrary discrete law, the unrestricted squared supremum error of
one clipped ideal cell is integrable; no overlap estimate is needed. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealClippedCell_error_sSup_sq_integrable
lemma idealClippedCell_error_sSup_sq_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    Integrable (fun counts =>
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1) ^ 2) (idealCountLaw (n := n) P) := by
  classical
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let μcell := poissonTableLaw (rate j)
  letI : IsProbabilityMeasure μ := by dsimp [μ, poissonTableLaw]; infer_instance
  let F : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) →
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) := fun pe =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let block : ((Fin d × Fin 4) → ℕ) → (Fin 4 → ℕ) := poissonTableCell j
  let scoreSq : (Fin 4 → ℕ) → ℝ := fun p =>
    (∑ z : Cell,
      (|pilotCenter ((n : ℝ) / 8) (fun z => p (CellFourEquiv z)) z -
          cellVector P j z| +
        pilotHalfWidth ((n : ℝ) / 8) d
          (fun z => p (CellFourEquiv z)) z)) ^ 2
  let g : ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → ℝ := fun counts =>
    sSup ((fun lambda : ℝ =>
      |idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) ^ 2
  have hrate (i : Fin 4) : rate j i =
      Real.toNNReal ((n : ℝ) / 8) *
        Real.toNNReal (cellVector P j (CellFourEquiv.symm i)) := by
    apply NNReal.eq
    have hq : 0 ≤ cellVector P j (CellFourEquiv.symm i) := by
      change 0 ≤ (P.pmf
        (j, finTwoEquiv (CellFourEquiv.symm i).1,
          finTwoEquiv (CellFourEquiv.symm i).2)).toReal
      positivity
    simp [rate, idealFlatRate, hq, show 0 ≤ (n : ℝ) / 8 by positivity]
    exact mul_nonneg (by positivity) hq
  have hrates : rate j = fun i =>
      Real.toNNReal ((n : ℝ) / 8) *
        Real.toNNReal (cellVector P j (CellFourEquiv.symm i)) := funext hrate
  have hscoreCell : Integrable scoreSq μcell := by
    rw [show μcell = poissonTableLaw (fun i =>
        Real.toNNReal ((n : ℝ) / 8) *
          Real.toNNReal (cellVector P j (CellFourEquiv.symm i))) by
      simp [μcell, hrates]]
    simpa [scoreSq] using pilotCell_score_sq_integrable P j hn hd
  have hblockMeas : Measurable block := by
    dsimp [block, poissonTableCell]
    fun_prop
  have hblockMap : Measure.map block μ = μcell := by
    simpa [block, μ, μcell] using
      (poissonTable_eval_cell_law rate j).map_eq
  have hscoreFull : Integrable (scoreSq ∘ block) μ := by
    have hmapped : Integrable scoreSq (Measure.map block μ) := by
      rw [hblockMap]
      exact hscoreCell
    exact hmapped.comp_aemeasurable hblockMeas.aemeasurable
  have hscoreProd : Integrable (fun pe :
      ((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ) =>
      scoreSq (block pe.1)) (μ.prod μ) := by
    change Integrable ((scoreSq ∘ block) ∘ Prod.fst) (μ.prod μ)
    exact ((measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp
      (measurable_of_countable (scoreSq ∘ block)).aestronglyMeasurable).2 hscoreFull
  let B : ℝ := (3 * (1 + epsilon⁻¹) + 1) + (d : ℝ) ^ (1 / 4 : ℝ)
  have hdomInt : Integrable (fun pe :
      ((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ) =>
      B ^ 2 * scoreSq (block pe.1)) (μ.prod μ) := hscoreProd.const_mul _
  have hpoint (pe : ((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) :
      g (F pe) ≤ B ^ 2 * scoreSq (block pe.1) := by
    have hcell : curryCountTable pe.1 j =
        fun z => block pe.1 (CellFourEquiv z) := by
      funext z
      simp [block, curryCountTable, poissonTableCell]
    have hFcell : (F pe).1 j = fun z => block pe.1 (CellFourEquiv z) := by
      simpa [F] using hcell
    have hsup := idealClippedCell_sSup_le_badScore he hn hd P (F pe) j
    rw [hFcell] at hsup
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hS0 : 0 ≤ ∑ z : Cell,
        (|pilotCenter ((n : ℝ) / 8)
            (fun z => block pe.1 (CellFourEquiv z)) z - cellVector P j z| +
          pilotHalfWidth ((n : ℝ) / 8) d
            (fun z => block pe.1 (CellFourEquiv z)) z) := by
      apply Finset.sum_nonneg
      intro z _
      have hh : 0 ≤ pilotHalfWidth ((n : ℝ) / 8) d
          (fun z => block pe.1 (CellFourEquiv z)) z :=
        le_trans (pilotRadius_pos_of_pos (by positivity) hd _ z).le
          (pilotRadius_le_pilotHalfWidth (by positivity) hd _ z)
      positivity
    have hsetBdd : BddAbove ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda (F pe) j -
          thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) :=
      ⟨B * Real.sqrt (scoreSq (block pe.1)), by
        rintro y ⟨lambda, hlambda, rfl⟩
        have hp := idealClippedCell_error_le_badScore he hn hd P (F pe) j lambda hlambda
        rw [hFcell] at hp
        have hsqrt : Real.sqrt (scoreSq (block pe.1)) =
            ∑ z : Cell,
              (|pilotCenter ((n : ℝ) / 8)
                  (fun z => block pe.1 (CellFourEquiv z)) z - cellVector P j z| +
                pilotHalfWidth ((n : ℝ) / 8) d
                  (fun z => block pe.1 (CellFourEquiv z)) z) := by
          dsimp [scoreSq]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hS0]
        simpa [B, hsqrt] using hp⟩
    have hzeroMem : |idealClippedCellPath (n := n) epsilon 0 (F pe) j -
        thresholdFunReal epsilon 0 (cellVector P j)| ∈
        (fun lambda : ℝ =>
          |idealClippedCellPath (n := n) epsilon lambda (F pe) j -
            thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1 :=
      ⟨0, by simp, rfl⟩
    have hsup0 : 0 ≤ sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda (F pe) j -
          thresholdFunReal epsilon lambda (cellVector P j)|) '' Set.Icc 0 1) :=
      le_trans (abs_nonneg _) (le_csSup hsetBdd hzeroMem)
    dsimp [g, scoreSq]
    have hsquared := (sq_le_sq₀ hsup0 (mul_nonneg hB0 hS0)).2
      (by simpa [B] using hsup)
    simpa [mul_pow] using hsquared
  have hflat : Integrable (g ∘ F) (μ.prod μ) := by
    apply hdomInt.mono' (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun pe => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpoint pe
      · dsimp [g]
        positivity
  have hF : Measurable F := by fun_prop
  have hg : Measurable g := measurable_of_countable _
  have hmap : Measure.map F (μ.prod μ) = idealCountLaw (n := n) P := by
    simpa [F, μ, rate] using map_flatIdealCountLaw (n := n) P
  have hmapped : Integrable g (Measure.map F (μ.prod μ)) :=
    (integrable_map_measure hg.aestronglyMeasurable hF.aemeasurable).2 hflat
  rw [hmap] at hmapped
  exact hmapped

end CausalSmith.Stat.DiscreteBudgetvalueCurve
