module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.ScalarBiasOuter

/-! Sharp boundary-product bounds for the scalar Jackson bias. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Mathlib.Analysis.JacksonApproximation
open scoped BigOperators NNReal

/-- Each coordinate of a cell vector is bounded by the total cell mass. With [the specified inputs and conditions](hyp:d,P,j,zeta), [the stated relationship holds](goal). -/
-- @node: cellVector_le_cellMass
lemma cellVector_le_cellMass {d : Nat} (P : DiscreteLaw d) (j : Fin d)
    (zeta : Cell) : cellVector P j zeta ≤ cellMass P j := by
  have hsum : ∑ z : Cell, cellVector P j z = cellMass P j := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    simp [cellMass, cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass,
      finTwoEquiv]
    ring
  rw [← hsum]
  exact Finset.single_le_sum (fun z _ => by
    change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
    positivity) (Finset.mem_univ zeta)

/-- The sum of the four good-pilot physical boundary products has the sharp
true cell-mass scale. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealPilotGood_boundarySqrt_sum_le
lemma idealPilotGood_boundarySqrt_sum_le
    {n d : Nat} (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d)
    (counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat))
    (j : Fin d) (hgood : idealPilotGood (n := n) P counts j) :
    let m : Real := (n : Real) / 8
    let c := pilotMidpoint m d (counts.1 j)
    let r := pilotRadius m d (counts.1 j)
    let q := cellVector P j
    ∑ i : Fin 4, Real.sqrt
        ((q (CellFourEquiv.symm i) -
            (c (CellFourEquiv.symm i) - r (CellFourEquiv.symm i))) *
          ((c (CellFourEquiv.symm i) + r (CellFourEquiv.symm i)) -
            q (CellFourEquiv.symm i))) ≤
      4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
        (logAlphabet d / m)) := by
  dsimp only
  have hL : 0 ≤ logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    have : (1 : Real) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg this]
  have hdelta0 : 0 ≤ logAlphabet d / ((n : Real) / 8) := by positivity
  calc
    _ ≤ ∑ _i : Fin 4, Real.sqrt
        (8 * pilotRadiusConstant ^ 2 * cellMass P j *
          (logAlphabet d / ((n : Real) / 8))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.sqrt_le_sqrt
      exact (idealPilotGood_boundaryProduct_le hn hd P counts j hgood
        (CellFourEquiv.symm i)).trans (by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left
              (cellVector_le_cellMass P j (CellFourEquiv.symm i)) (by positivity)
          · exact hdelta0)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; simp

/-- The good-pilot Jackson approximation keeps the boundary-adaptive term
separate from the second-order radius term. With [the specified inputs and conditions](hyp:n,d,epsilon,he,lambda,hlambda,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: goodPilot_localJacksonPolynomial_boundary_sharp
lemma goodPilot_localJacksonPolynomial_boundary_sharp
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (lambda : Real)
    (hlambda : lambda ∈ Set.Icc (0 : Real) 1) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat)) (j : Fin d)
    (hgood : idealPilotGood (n := n) P counts j) :
    let m : Real := (n : Real) / 8
    let center := pilotMidpoint m d (counts.1 j)
    let radius := pilotRadius m d (counts.1 j)
    let q := cellVector P j
    |thresholdFunReal epsilon lambda center +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i))
            (fun i => q (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d) center radius) -
        thresholdFunReal epsilon lambda q| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
            (logAlphabet d / m)) / (jacksonDegree d : Real) +
          (∑ zeta : Cell, radius zeta) / (jacksonDegree d : Real) ^ 2) := by
  dsimp only
  have hbase := goodPilot_localJacksonPolynomial_boundary_adaptive epsilon he
    lambda hlambda hn (show 1 ≤ d by omega) P counts j hgood
  have hsqrt := idealPilotGood_boundarySqrt_sum_le hn (show 1 ≤ d by omega)
    P counts j hgood
  let K : Real := jacksonDegree d
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (show 0 < jacksonDegree d by simp [jacksonDegree])
  have hradius : (∑ i : Fin 4, pilotRadius ((n : Real) / 8) d
      (counts.1 j) (CellFourEquiv.symm i)) =
      ∑ zeta : Cell, pilotRadius ((n : Real) / 8) d (counts.1 j) zeta :=
    Equiv.sum_comp CellFourEquiv.symm _
  calc
    _ ≤ 32 * (3 * (1 + epsilon⁻¹) + 1) * ∑ i : Fin 4,
        (Real.sqrt
            ((cellVector P j (CellFourEquiv.symm i) -
                (pilotMidpoint ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i) -
                  pilotRadius ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i))) *
              ((pilotMidpoint ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i) +
                  pilotRadius ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i)) -
                cellVector P j (CellFourEquiv.symm i))) / K +
          pilotRadius ((n : Real) / 8) d (counts.1 j)
            (CellFourEquiv.symm i) / K ^ 2) := by simpa [K] using hbase
    _ = 32 * (3 * (1 + epsilon⁻¹) + 1) *
        ((∑ i : Fin 4, Real.sqrt
            ((cellVector P j (CellFourEquiv.symm i) -
                (pilotMidpoint ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i) -
                  pilotRadius ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i))) *
              ((pilotMidpoint ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i) +
                  pilotRadius ((n : Real) / 8) d (counts.1 j)
                    (CellFourEquiv.symm i)) -
                cellVector P j (CellFourEquiv.symm i)))) / K +
          (∑ zeta : Cell, pilotRadius ((n : Real) / 8) d
            (counts.1 j) zeta) / K ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        hradius]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [K] using add_le_add_left (div_le_div_of_nonneg_right hsqrt hK.le)
        ((∑ zeta : Cell, pilotRadius ((n : Real) / 8) d
          (counts.1 j) zeta) / K ^ 2)

set_option maxHeartbeats 1000000 in
-- The exact factorial mean unfolds a nested finite product law.
/-- Conditional good-pilot scalar bias with the physical boundary term kept
separate from the second-order radius term. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood), [the shadow-price range](hyp:hlambda), [the positive envelope constant](hyp:hC), and [the coefficient envelope](hyp:hcoeff). -/
-- @node: goodPilot_jacksonCellStatistic_conditional_bias_sharp
lemma goodPilot_jacksonCellStatistic_conditional_bias_sharp
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → Nat) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (C : Real) (hC : 0 ≤ C)
    (hcoeff : jacksonCoefficientBV epsilon ((n : Real) / 8) d
        (curryCountTable p j) ≤
      C * (∑ zeta : Cell,
        pilotRadius ((n : Real) / 8) d (curryCountTable p j) zeta) *
        Real.exp (12 * jacksonDegree d)) :
    let m : Real := (n : Real) / 8
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
      fun i e => poissonTableCell j e i
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    |(∫ e, jacksonCellStatistic epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2) /
        ((d : Real) ^ (1 / 4 : Real) *
          ∑ zeta, pilotRadius m d pilot zeta) +
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
            (logAlphabet d / m)) / (jacksonDegree d : Real) +
          (∑ zeta, pilotRadius m d pilot zeta) /
            (jacksonDegree d : Real) ^ 2) := by
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) mu := by
    simpa [W, mu, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) p (j, i)
  have hWindep : iIndepFun W mu := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) mu = poissonTableLaw (rate j) := by
        simpa [W, mu] using (poissonTable_eval_cell_law rate rate p j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) mu) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have hclip := goodPilot_jacksonCellStatistic_mean_sub_raw_mean_le epsilon he
    hn hd P p j hgood lambda hlambda C hC hcoeff
  have hmean := jacksonCellRaw_mean mu epsilon he lambda hlambda m
    (by dsimp [m]; positivity) d (show 1 ≤ d by omega) pilot W (rate j)
    hWlaw hWindep
  have hrate (i : Fin 4) : (rate j i : Real) / m =
      cellVector P j (CellFourEquiv.symm i) := by
    have hq : 0 ≤ cellVector P j (CellFourEquiv.symm i) := ENNReal.toReal_nonneg
    dsimp [rate, idealFlatRate, m]
    rw [max_eq_left (mul_nonneg (by positivity) hq)]
    field_simp
  have hmean' : (∫ e, jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) =
      thresholdFunReal epsilon lambda (pilotMidpoint m d pilot) +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
            (fun i => pilotRadius m d pilot (CellFourEquiv.symm i))
            (fun i => cellVector P j (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d)
            (pilotMidpoint m d pilot) (pilotRadius m d pilot)) := by
    rw [hmean]
    congr 2
    rw [show (fun i => ((rate j i : Real) / m -
          pilotMidpoint m d pilot (CellFourEquiv.symm i)) /
        pilotRadius m d pilot (CellFourEquiv.symm i)) =
      normalizedPoint
        (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
        (fun i => pilotRadius m d pilot (CellFourEquiv.symm i))
        (fun i => cellVector P j (CellFourEquiv.symm i)) by
      funext i
      simp only [normalizedPoint, hrate]]
  have hboundary := goodPilot_localJacksonPolynomial_boundary_sharp epsilon he
    lambda hlambda hn hd P (curryCountTable p, fun _ _ => 0) j hgood
  let A : Real := ∫ e, jacksonCellStatistic epsilon lambda m d pilot
    (fun zeta => W (CellFourEquiv zeta) e) ∂mu
  let R : Real := ∫ e, jacksonCellRaw epsilon lambda m d pilot
    (fun zeta => W (CellFourEquiv zeta) e) ∂mu
  let T : Real := thresholdFunReal epsilon lambda (cellVector P j)
  change |A - T| ≤ _
  have hclip' : |A - R| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2) /
        ((d : Real) ^ (1 / 4 : Real) *
          ∑ zeta, pilotRadius m d pilot zeta) := by
    simpa [A, R, m, rate, mu, pilot, W] using hclip
  have hboundary' : |R - T| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
            (logAlphabet d / m)) / (jacksonDegree d : Real) +
          (∑ zeta, pilotRadius m d pilot zeta) /
            (jacksonDegree d : Real) ^ 2) := by
    dsimp [R, T]
    rw [hmean']
    simpa [m, pilot] using hboundary
  calc
    |A - T| = |(A - R) + (R - T)| := by congr 1 <;> ring
    _ ≤ |A - R| + |R - T| := abs_add_le _ _
    _ ≤ _ := add_le_add hclip' hboundary'

set_option maxHeartbeats 800000 in
-- The pilot/evaluation product integral and coefficient specialization are expensive.
/-- Integrating the sharp conditional bias over the pilot table costs only
the first moment of the radius sum; the boundary product is deterministic. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,C,hC,hcoeff,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: flatGoodPilot_conditionalBias_integral_sharp
lemma flatGoodPilot_conditionalBias_integral_sharp
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (C : Real) (hC : 0 < C)
    (hcoeff : ∀ (m : Real), 0 < m → ∀ (d : Nat), 1 ≤ d →
      ∀ pilot,
      jacksonCoefficientBV epsilon m d pilot ≤
        C * (∑ zeta : Cell, pilotRadius m d pilot zeta) *
          Real.exp (12 * jacksonDegree d))
    (j : Fin d) (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
      let m : Real := (n : Real) / 8
      let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
      let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
      let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
        fun i e => poissonTableCell j e i
      let R := Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j
      (∫ p, if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        |(∫ e, jacksonCellStatistic epsilon lambda m d (curryCountTable p j)
            (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| else 0 ∂mu) ≤
        (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
            (d : Real) ^ (1 / 4 : Real)) * R +
          32 * (3 * (1 + epsilon⁻¹) + 1) *
            (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
                (logAlphabet d / m)) / (jacksonDegree d : Real) +
              R / (jacksonDegree d : Real) ^ 2) := by
  classical
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  let S : ((Fin d × Fin 4) → Nat) → Real := fun p =>
    ∑ zeta : Cell, pilotRadius m d (curryCountTable p j) zeta
  let R : Real := Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j
  let B : Real := 4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
    (d : Real) ^ (1 / 4 : Real)
  let A : Real := 32 * (3 * (1 + epsilon⁻¹) + 1)
  let D : Real := 4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
    (logAlphabet d / m)) / (jacksonDegree d : Real)
  let H : ((Fin d × Fin 4) → Nat) → Real := fun p =>
    if idealPilotGoodBool (n := n) P (curryCountTable p, fun _ _ => 0) j then
      |(∫ e, jacksonCellStatistic epsilon lambda m d (curryCountTable p j)
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
        thresholdFunReal epsilon lambda (cellVector P j)| else 0
  have hSpos (p : (Fin d × Fin 4) → Nat) : 0 ≤ S p :=
    Finset.sum_nonneg fun z _ => (pilotRadius_pos_of_pos
      (by dsimp [m]; positivity) (show 1 ≤ d by omega) (curryCountTable p j) z).le
  have hSstrict (p : (Fin d × Fin 4) → Nat) : 0 < S p :=
    Finset.sum_pos (fun z _ => pilotRadius_pos_of_pos
      (by dsimp [m]; positivity) (show 1 ≤ d by omega) (curryCountTable p j) z)
      (by simp)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (p : (Fin d × Fin 4) → Nat) :
      H p ≤ B * S p + A * (D + S p / (jacksonDegree d : Real) ^ 2) := by
    by_cases hg : idealPilotGood (n := n) P
        (curryCountTable p, fun _ _ => 0) j
    · have hc := goodPilot_jacksonCellStatistic_conditional_bias_sharp epsilon he
        hn hd P p j hg lambda hlambda C hC.le
        (hcoeff m (by dsimp [m]; positivity) d (show 1 ≤ d by omega)
          (curryCountTable p j))
      have hgb := (idealPilotGoodBool_eq_true P
        (curryCountTable p, fun _ _ => 0) j).2 hg
      rw [show H p = |(∫ e, jacksonCellStatistic epsilon lambda m d
          (curryCountTable p j) (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| by simp [H, hgb]]
      apply hc.trans_eq
      dsimp [B, A, D, S, m, rate, mu, W]
      field_simp [(hSstrict p).ne']
    · have hgb : idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hg ((idealPilotGoodBool_eq_true P
          (curryCountTable p, fun _ _ => 0) j).1 ht)
      rw [show H p = 0 by simp [H, hgb]]
      exact add_nonneg (mul_nonneg hB0 (hSpos p))
        (mul_nonneg hA0 (add_nonneg hD0 (div_nonneg (hSpos p) (sq_nonneg _))))
  have hSint : Integrable S mu := by
    have hsecond := pilotRadius_sum_sq_integral_le_cellScale hn hd P j
    exact ((memLp_two_iff_integrable_sq
      (measurable_of_countable _).aestronglyMeasurable).2 (by
        simpa [S, m, rate, mu] using hsecond.1)).integrable (by norm_num)
  have hmajor : Integrable (fun p => B * S p +
      A * (D + S p / (jacksonDegree d : Real) ^ 2)) mu := by fun_prop
  have hpart : Integrable (fun p => D + S p / (jacksonDegree d : Real) ^ 2) mu :=
    (integrable_const D).add (hSint.div_const _)
  have hHint : Integrable H mu := by
    apply Integrable.mono' hmajor (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [H]; split <;> positivity)]
    exact hpoint p
  calc
    _ = ∫ p, H p ∂mu := by rfl
    _ ≤ ∫ p, (B * S p + A *
        (D + S p / (jacksonDegree d : Real) ^ 2)) ∂mu :=
      integral_mono hHint hmajor hpoint
    _ = B * (∫ p, S p ∂mu) + A *
        (D + (∫ p, S p ∂mu) / (jacksonDegree d : Real) ^ 2) := by
      rw [integral_add (hSint.const_mul B) (hpart.const_mul A),
        integral_const_mul, integral_const_mul,
        integral_add (integrable_const D) (hSint.div_const _),
        integral_const, integral_div]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ B * R + A * (D + R / (jacksonDegree d : Real) ^ 2) := by
      have hSR : (∫ p, S p ∂mu) ≤ R := by
        simpa [S, R, m, rate, mu] using pilotRadius_sum_integral_le_cellScale hn hd P j
      gcongr
    _ = _ := by rfl


/-- Any flattened good-pilot scalar bound transports unchanged to the paper's
curried ideal count law. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j,lambda,hlambda,R), [the stated relationship holds](goal). The argument assumes [the flattened-law bound](hyp:hflatBound). -/
-- @node: idealGoodPilot_scalarMean_le_of_flat
lemma idealGoodPilot_scalarMean_le_of_flat
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) (R : Real)
    (hflatBound :
      let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
      let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
      let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
        fun i e => poissonTableCell j e i
      (∫ p, if idealPilotGoodBool (n := n) P
          (curryCountTable p, fun _ _ => 0) j then
        |(∫ e, jacksonCellStatistic epsilon lambda ((n : Real) / 8) d
            (curryCountTable p j) (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
          thresholdFunReal epsilon lambda (cellVector P j)| else 0 ∂mu) ≤ R) :
    |∫ counts, (if idealPilotGoodBool (n := n) P counts j then
      idealClippedCellPath (n := n) epsilon lambda counts j -
        thresholdFunReal epsilon lambda (cellVector P j) else 0)
      ∂idealCountLaw (n := n) P| ≤ R := by
  classical
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

/-- The sharp flattened good-pilot bias bound under the ideal count law. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,C,hC,hcoeff,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: idealGoodPilot_scalarMean_sharp
lemma idealGoodPilot_scalarMean_sharp
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (C : Real) (hC : 0 < C)
    (hcoeff : ∀ (m : Real), 0 < m → ∀ (d : Nat), 1 ≤ d →
      ∀ pilot,
      jacksonCoefficientBV epsilon m d pilot ≤
        C * (∑ zeta : Cell, pilotRadius m d pilot zeta) *
          Real.exp (12 * jacksonDegree d))
    (j : Fin d) (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
      let m : Real := (n : Real) / 8
      let R := Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j
      |∫ counts, (if idealPilotGoodBool (n := n) P counts j then
          idealClippedCellPath (n := n) epsilon lambda counts j -
            thresholdFunReal epsilon lambda (cellVector P j) else 0)
          ∂idealCountLaw (n := n) P| ≤
        (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
            (d : Real) ^ (1 / 4 : Real)) * R +
          32 * (3 * (1 + epsilon⁻¹) + 1) *
            (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
                (logAlphabet d / m)) / (jacksonDegree d : Real) +
              R / (jacksonDegree d : Real) ^ 2) := by
  have hflat := flatGoodPilot_conditionalBias_integral_sharp
    epsilon he he' hn hd P C hC hcoeff j lambda hlambda
  exact idealGoodPilot_scalarMean_le_of_flat epsilon he hn (show 1 ≤ d by omega)
    P j lambda hlambda _ hflat

/-- Two logarithmic factors are absorbed by the negative power supplied by
the factorial clipping term. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: logAlphabet_sq_mul_rpow_neg_three_sixteenths_le
lemma logAlphabet_sq_mul_rpow_neg_three_sixteenths_le
    {d : Nat} (hd : 16 ≤ d) :
    logAlphabet d ^ 2 * (d : Real) ^ (-(3 / 16 : Real)) ≤ (35 / 3 : Real) ^ 2 := by
  have hD : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hD0 : (0 : Real) ≤ d := le_trans (by norm_num) hD
  have hDpos : (0 : Real) < d := lt_of_lt_of_le (by norm_num) hD
  let a : Real := 3 / 32
  have ha : 0 < a := by dsimp [a]; norm_num
  have hp0 : 0 ≤ (d : Real) ^ (-a) := Real.rpow_nonneg hD0 _
  have hp1 : (d : Real) ^ (-a) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD
      (show -a ≤ 0 by dsimp [a]; norm_num)
  have hlog := Real.log_le_rpow_div hD0 ha
  have hmul : Real.log d * (d : Real) ^ (-a) ≤ 32 / 3 := by
    calc
      _ ≤ ((d : Real) ^ a / a) * (d : Real) ^ (-a) :=
        mul_le_mul_of_nonneg_right hlog hp0
      _ = 32 / 3 := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hDpos]
        dsimp [a]
        norm_num
  have hsingle : logAlphabet d * (d : Real) ^ (-a) ≤ 35 / 3 := by
    rw [show logAlphabet d = 1 + Real.log d by
      unfold logAlphabet
      rw [Real.log_mul (Real.exp_ne_zero 1) hDpos.ne', Real.log_exp]]
    nlinarith
  have hsingle0 : 0 ≤ logAlphabet d * (d : Real) ^ (-a) := by
    have hL : 0 ≤ logAlphabet d := by
      unfold logAlphabet
      rw [Real.log_mul (Real.exp_ne_zero 1) hDpos.ne', Real.log_exp]
      positivity
    positivity
  have hsq := (sq_le_sq₀ hsingle0 (by norm_num : (0 : Real) ≤ 35 / 3)).2 hsingle
  have hpEq : (d : Real) ^ (-(3 / 16 : Real)) = ((d : Real) ^ (-a)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
    dsimp [a]
    norm_num
  calc
    _ = (logAlphabet d * (d : Real) ^ (-a)) ^ 2 := by
      rw [hpEq, mul_pow]
    _ ≤ _ := hsq

/-- The cell scale is at most two logarithmic factors times the scalar target
rate. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: badPilotCellScale_le_log_sq_mul_scalarRate
lemma badPilotCellScale_le_log_sq_mul_scalarRate
    {n d : Nat} (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    badPilotCellScale (n := n) P j ≤ logAlphabet d ^ 2 *
      (Real.sqrt (cellMass P j / (((n : Real) / 8) * logAlphabet d)) +
        1 / (((n : Real) / 8) * logAlphabet d)) := by
  let m : Real := (n : Real) / 8
  let L := logAlphabet d
  let q := cellMass P j
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast hd))
  have hq : 0 ≤ q := by
    dsimp [q]
    have hsum : ∑ z : Cell, cellVector P j z = cellMass P j := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fin.sum_univ_two]
      simp [cellMass, cellVector,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass, finTwoEquiv]
      ring
    rw [← hsum]
    exact Finset.sum_nonneg fun z _ => by
      change 0 ≤ (P.pmf (j, finTwoEquiv z.1, finTwoEquiv z.2)).toReal
      positivity
  have ha : 0 ≤ q * L / m := by positivity
  have hb : 0 ≤ q / (m * L) := by positivity
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hsqrt : Real.sqrt (q * L / m) ≤ L ^ 2 * Real.sqrt (q / (m * L)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [hsqa, mul_pow, hsqb]
    field_simp
    have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hLsq)]
  unfold badPilotCellScale
  change Real.sqrt (q * L / m) + L / m ≤
    L ^ 2 * (Real.sqrt (q / (m * L)) + 1 / (m * L))
  calc
    _ ≤ L ^ 2 * Real.sqrt (q / (m * L)) + L ^ 2 * (1 / (m * L)) := by
      apply add_le_add hsqrt
      field_simp
      exact le_rfl
    _ = _ := by ring

/-- The bad-pilot exponential envelope absorbs the two logarithmic factors
needed to convert the cell scale to the scalar target rate. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: badPilot_exponential_mul_log_sq_le
lemma badPilot_exponential_mul_log_sq_le {d : Nat} (hd : 16 ≤ d) :
    (d : Real) ^ (1 / 4 : Real) * Real.exp (-10 * logAlphabet d) *
        logAlphabet d ^ 2 ≤ (35 / 3 : Real) ^ 2 := by
  have hD : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hDpos : (0 : Real) < d := lt_of_lt_of_le (by norm_num) hD
  have hL : logAlphabet d = 1 + Real.log d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) hDpos.ne', Real.log_exp]
  have hexp : Real.exp (-10 * logAlphabet d) ≤ (d : Real) ^ (-1 : Real) := by
    rw [Real.rpow_neg_one, ← Real.exp_log hDpos, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [hL]
    linarith [Real.log_nonneg hD]
  have hcoef0 : 0 ≤ (d : Real) ^ (1 / 4 : Real) * logAlphabet d ^ 2 := by positivity
  have hpow : (d : Real) ^ (1 / 4 : Real) * (d : Real) ^ (-1 : Real) =
      (d : Real) ^ (-(3 / 4 : Real)) := by
    rw [← Real.rpow_add hDpos]
    norm_num
  calc
    _ = ((d : Real) ^ (1 / 4 : Real) * logAlphabet d ^ 2) *
        Real.exp (-10 * logAlphabet d) := by ring
    _ ≤ ((d : Real) ^ (1 / 4 : Real) * logAlphabet d ^ 2) *
        (d : Real) ^ (-1 : Real) := mul_le_mul_of_nonneg_left hexp hcoef0
    _ = logAlphabet d ^ 2 * ((d : Real) ^ (1 / 4 : Real) *
        (d : Real) ^ (-1 : Real)) := by ring
    _ = logAlphabet d ^ 2 * (d : Real) ^ (-(3 / 4 : Real)) := by rw [hpow]
    _ ≤ logAlphabet d ^ 2 * (d : Real) ^ (-(3 / 16 : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
      · positivity
    _ ≤ _ := logAlphabet_sq_mul_rpow_neg_three_sixteenths_le hd

/-- Splitting the ideal scalar error by the pilot event bounds its bias by
the absolute good mean plus the existing bad-pilot envelope. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j,lambda,hlambda), [the stated relationship holds](goal). -/
-- @node: uncappedJacksonCellBias_le_goodMean_add_badEnvelope
lemma uncappedJacksonCellBias_le_goodMean_add_badEnvelope
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d) (j : Fin d)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1) :
    uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
      |∫ counts, (if idealPilotGoodBool (n := n) P counts j then
        idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j) else 0)
        ∂idealCountLaw (n := n) P| +
      badPilotCellEnvelope (n := n) epsilon P j := by
  classical
  let E := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    idealClippedCellPath (n := n) epsilon lambda counts j -
      thresholdFunReal epsilon lambda (cellVector P j)
  let G := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then E counts else 0
  let B := fun counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat) =>
    if idealPilotGoodBool (n := n) P counts j then 0 else E counts
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) :=
    idealCountLaw_isProbabilityMeasure P
  have hE := idealClippedCell_error_integrable epsilon he hn hd P j lambda hlambda
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
  exact add_le_add_right
    (idealBadPilot_scalarMean_le_envelope epsilon he hn hd P j lambda hlambda) _

/-- The boundary square-root term divided by the Jackson degree has the
frozen scalar rate. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: sharpBoundary_div_degree_le_scalarRate
lemma sharpBoundary_div_degree_le_scalarRate
    {n d : Nat} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
        (logAlphabet d / ((n : Real) / 8))) / (jacksonDegree d : Real) ≤
      (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) *
        (Real.sqrt (cellMass P j /
          (((n : Real) / 8) * logAlphabet d)) +
          1 / (((n : Real) / 8) * logAlphabet d)) := by
  let m : Real := (n : Real) / 8
  let L := logAlphabet d
  let q := cellMass P j
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 0 < L := by
    dsimp [L]
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    exact le_trans ENNReal.toReal_nonneg
      (cellVector_le_cellMass P j ((0 : Fin 2), (0 : Fin 2)))
  have hA : 0 ≤ 8 * pilotRadiusConstant ^ 2 := by positivity
  have hqL : 0 ≤ q * L / m := by positivity
  have hqdiv : 0 ≤ q / (m * L) := by positivity
  have hsqrtq : Real.sqrt (q * L / m) =
      L * Real.sqrt (q / (m * L)) := by
    have ha := Real.sq_sqrt hqL
    have hb := Real.sq_sqrt hqdiv
    have hr : (L * Real.sqrt (q / (m * L))) ^ 2 = q * L / m := by
      rw [mul_pow, hb]
      field_simp
    exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp (ha.trans hr.symm)
  have hsqrtA : Real.sqrt ((8 * pilotRadiusConstant ^ 2) * (q * L / m)) =
      Real.sqrt (8 * pilotRadiusConstant ^ 2) * Real.sqrt (q * L / m) := by
    rw [Real.sqrt_mul hA]
  have hK : (0 : Real) < jacksonDegree d := by
    exact_mod_cast (show 0 < jacksonDegree d by simp [jacksonDegree])
  have hLK := logAlphabet_div_jacksonDegree_le (d := d)
  dsimp [m, L, q] at hsqrtA hsqrtq ⊢
  rw [show 8 * pilotRadiusConstant ^ 2 * cellMass P j *
      (logAlphabet d / ((n : Real) / 8)) =
      (8 * pilotRadiusConstant ^ 2) *
        (cellMass P j * logAlphabet d / ((n : Real) / 8)) by ring]
  rw [hsqrtA, hsqrtq]
  have hmain : L / (jacksonDegree d : Real) *
      Real.sqrt (q / (m * L)) ≤
      768 * Real.sqrt (q / (m * L)) :=
    mul_le_mul_of_nonneg_right hLK (Real.sqrt_nonneg _)
  have htarget0 : 0 ≤ 1 / (m * L) := by positivity
  have hmain' := mul_le_mul_of_nonneg_left hmain
    (Real.sqrt_nonneg (8 * pilotRadiusConstant ^ 2))
  calc
    Real.sqrt (8 * pilotRadiusConstant ^ 2) *
        (L * Real.sqrt (q / (m * L))) / (jacksonDegree d : Real) =
      Real.sqrt (8 * pilotRadiusConstant ^ 2) *
        ((L / (jacksonDegree d : Real)) * Real.sqrt (q / (m * L))) := by ring
    _ ≤ Real.sqrt (8 * pilotRadiusConstant ^ 2) *
        (768 * Real.sqrt (q / (m * L))) := hmain'
    _ ≤ _ := by
      have hs : Real.sqrt (cellMass P j /
          (((n : Real) / 8) * logAlphabet d)) ≤
          Real.sqrt (cellMass P j /
            (((n : Real) / 8) * logAlphabet d)) +
            1 / (((n : Real) / 8) * logAlphabet d) := by
        dsimp [m, L] at htarget0
        exact le_add_of_nonneg_right htarget0
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
        (mul_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : Real) ≤ 768))

/-- The second-order radius term divided by the squared Jackson degree also
has the frozen scalar rate. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: badPilotCellScale_div_degree_sq_le_scalarRate
lemma badPilotCellScale_div_degree_sq_le_scalarRate
    {n d : Nat} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    badPilotCellScale (n := n) P j / (jacksonDegree d : Real) ^ 2 ≤
      768 ^ 2 * (Real.sqrt (cellMass P j /
        (((n : Real) / 8) * logAlphabet d)) +
        1 / (((n : Real) / 8) * logAlphabet d)) := by
  have hs := badPilotCellScale_le_log_sq_mul_scalarRate hn (show 1 ≤ d by omega) P j
  have hLK := logAlphabet_div_jacksonDegree_le (d := d)
  have hK : (0 : Real) < jacksonDegree d := by
    exact_mod_cast (show 0 < jacksonDegree d by simp [jacksonDegree])
  have hL : 0 ≤ logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hsq : logAlphabet d ^ 2 / (jacksonDegree d : Real) ^ 2 ≤ 768 ^ 2 := by
    rw [show logAlphabet d ^ 2 / (jacksonDegree d : Real) ^ 2 =
      (logAlphabet d / (jacksonDegree d : Real)) ^ 2 by ring]
    exact (sq_le_sq₀ (div_nonneg hL hK.le) (by norm_num)).2 hLK
  have hT : 0 ≤ Real.sqrt (cellMass P j /
      (((n : Real) / 8) * logAlphabet d)) +
      1 / (((n : Real) / 8) * logAlphabet d) := by positivity
  calc
    _ ≤ (logAlphabet d ^ 2 *
        (Real.sqrt (cellMass P j / (((n : Real) / 8) * logAlphabet d)) +
          1 / (((n : Real) / 8) * logAlphabet d))) /
        (jacksonDegree d : Real) ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = (logAlphabet d ^ 2 / (jacksonDegree d : Real) ^ 2) *
        (Real.sqrt (cellMass P j / (((n : Real) / 8) * logAlphabet d)) +
          1 / (((n : Real) / 8) * logAlphabet d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq hT

/-- A single epsilon-dependent constant controls the uncapped scalar cell
bias at the paper's square-root rate. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: uncappedJacksonCellBias_le_rate
lemma uncappedJacksonCellBias_le_rate (epsilon : Real) (he : 0 < epsilon)
    (he' : epsilon < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ {n d : Nat}, 1 ≤ n → 16 ≤ d →
      ∀ (P : DiscreteLaw d) (j : Fin d) (lambda : Real),
      lambda ∈ Set.Icc (0 : Real) 1 →
      uncappedJacksonCellBias (n := n) epsilon lambda P j ≤
        C * (Real.sqrt (cellMass P j /
          (((n : Real) / 8) * logAlphabet d)) +
          1 / (((n : Real) / 8) * logAlphabet d)) := by
  obtain ⟨C₀, hC₀, hcoeff⟩ := jacksonCoefficientBV_pilot_le epsilon he he'
  obtain ⟨Cb, hCb, hbad⟩ := badPilotCellEnvelope_le epsilon he
  let A : Real := 32 * (3 * (1 + epsilon⁻¹) + 1)
  let R₀ : Real := Real.sqrt 32 * pilotRadiusConstant
  let M : Real := (35 / 3 : Real) ^ 2
  let C : Real :=
    4 * C₀ ^ 2 * Real.exp 123 * R₀ * M +
      A * (4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) +
        R₀ * 768 ^ 2) + Cb * M + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR₀ : 0 ≤ R₀ := by
    dsimp [R₀]
    unfold pilotRadiusConstant
    positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : 0 < C := by dsimp [C, A, R₀, M]; positivity
  refine ⟨C, hC, ?_⟩
  intro n d hn hd P j lambda hlambda
  let T : Real := Real.sqrt (cellMass P j /
      (((n : Real) / 8) * logAlphabet d)) +
    1 / (((n : Real) / 8) * logAlphabet d)
  have hL : 0 < logAlphabet d := by
    unfold logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    positivity
  have hT : 0 ≤ T := by
    dsimp [T]
    exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsplit := uncappedJacksonCellBias_le_goodMean_add_badEnvelope
    epsilon he hn (show 1 ≤ d by omega) P j lambda hlambda
  have hgood := idealGoodPilot_scalarMean_sharp epsilon he he' hn hd P
    C₀ hC₀ hcoeff j lambda hlambda
  have hs := badPilotCellScale_le_log_sq_mul_scalarRate hn
    (show 1 ≤ d by omega) P j
  have hp := logAlphabet_sq_mul_rpow_neg_three_sixteenths_le hd
  have hpow : (d : Real) ^ (1 / 16 : Real) /
      (d : Real) ^ (1 / 4 : Real) =
      (d : Real) ^ (-(3 / 16 : Real)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity : (0 : Real) ≤ d),
      ← Real.rpow_add (by positivity : (0 : Real) < d)]
    norm_num
  have hfirst :
      (4 * C₀ ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
          (d : Real) ^ (1 / 4 : Real)) *
        (Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j) ≤
      (4 * C₀ ^ 2 * Real.exp 123 * R₀ * M) * T := by
    rw [show 4 * C₀ ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
        (d : Real) ^ (1 / 4 : Real) =
        4 * C₀ ^ 2 * Real.exp 123 *
          ((d : Real) ^ (1 / 16 : Real) / (d : Real) ^ (1 / 4 : Real)) by ring,
      hpow]
    have hx : logAlphabet d ^ 2 * (d : Real) ^ (-(3 / 16 : Real)) ≤ M := by
      simpa [M] using hp
    have hscaled : (d : Real) ^ (-(3 / 16 : Real)) *
        badPilotCellScale (n := n) P j ≤ M * T := by
      calc
        _ ≤ (d : Real) ^ (-(3 / 16 : Real)) *
            (logAlphabet d ^ 2 * T) :=
          mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by positivity) _)
        _ = (logAlphabet d ^ 2 * (d : Real) ^ (-(3 / 16 : Real))) * T := by ring
        _ ≤ M * T := mul_le_mul_of_nonneg_right hx hT
    have hQ : 0 ≤ 4 * C₀ ^ 2 * Real.exp 123 * R₀ := by positivity
    calc
      _ = (4 * C₀ ^ 2 * Real.exp 123 * R₀) *
          ((d : Real) ^ (-(3 / 16 : Real)) *
            badPilotCellScale (n := n) P j) := by simp [R₀]; ring
      _ ≤ (4 * C₀ ^ 2 * Real.exp 123 * R₀) * (M * T) :=
        mul_le_mul_of_nonneg_left hscaled hQ
      _ = _ := by ring
  have hsqrt := sharpBoundary_div_degree_le_scalarRate hn hd P j
  have hradius := badPilotCellScale_div_degree_sq_le_scalarRate hn hd P j
  have hboundary : A *
      (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
          (logAlphabet d / ((n : Real) / 8))) / (jacksonDegree d : Real) +
        (Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j) /
          (jacksonDegree d : Real) ^ 2) ≤
      A * (4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) +
        R₀ * 768 ^ 2) * T := by
    have hrad : (Real.sqrt 32 * pilotRadiusConstant *
        badPilotCellScale (n := n) P j) / (jacksonDegree d : Real) ^ 2 ≤
        (R₀ * 768 ^ 2) * T := by
      calc
        _ = R₀ * (badPilotCellScale (n := n) P j /
            (jacksonDegree d : Real) ^ 2) := by simp [R₀]; ring
        _ ≤ R₀ * (768 ^ 2 * T) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ A * ((4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) +
          R₀ * 768 ^ 2) * T) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have hsqrt4 := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : Real) ≤ 4)
        calc
          _ = 4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
              (logAlphabet d / ((n : Real) / 8))) / (jacksonDegree d : Real)) +
              (Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j) /
                (jacksonDegree d : Real) ^ 2 := by ring
          _ ≤ 4 * ((Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) * T) +
              (R₀ * 768 ^ 2) * T := add_le_add hsqrt4 hrad
          _ = (4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) +
              R₀ * 768 ^ 2) * T := by ring
      _ = _ := by ring
  have hbad0 := hbad hn (show 1 ≤ d by omega) P j
  have hbadRate : badPilotCellEnvelope (n := n) epsilon P j ≤ Cb * M * T := by
    calc
      _ ≤ Cb * (d : Real) ^ (1 / 4 : Real) *
          Real.exp (-10 * logAlphabet d) * badPilotCellScale (n := n) P j := hbad0
      _ ≤ Cb * (d : Real) ^ (1 / 4 : Real) *
          Real.exp (-10 * logAlphabet d) * (logAlphabet d ^ 2 * T) := by gcongr
      _ = Cb * ((d : Real) ^ (1 / 4 : Real) *
          Real.exp (-10 * logAlphabet d) * logAlphabet d ^ 2) * T := by ring
      _ ≤ Cb * M * T := by
        gcongr
        simpa [M] using badPilot_exponential_mul_log_sq_le hd
  dsimp only at hgood
  calc
    _ ≤ _ := hsplit
    _ ≤ ((4 * C₀ ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) /
          (d : Real) ^ (1 / 4 : Real)) *
          (Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j) +
        A * (4 * Real.sqrt (8 * pilotRadiusConstant ^ 2 * cellMass P j *
          (logAlphabet d / ((n : Real) / 8))) / (jacksonDegree d : Real) +
          (Real.sqrt 32 * pilotRadiusConstant * badPilotCellScale (n := n) P j) /
            (jacksonDegree d : Real) ^ 2)) +
        badPilotCellEnvelope (n := n) epsilon P j := by
          simpa [A] using add_le_add hgood
            (le_refl (badPilotCellEnvelope (n := n) epsilon P j))
    _ ≤ (4 * C₀ ^ 2 * Real.exp 123 * R₀ * M) * T +
        A * (4 * (Real.sqrt (8 * pilotRadiusConstant ^ 2) * 768) +
          R₀ * 768 ^ 2) * T + Cb * M * T := by gcongr
    _ ≤ C * T := by dsimp [C]; nlinarith

end CausalSmith.Stat.DiscreteBudgetvalueCurve
