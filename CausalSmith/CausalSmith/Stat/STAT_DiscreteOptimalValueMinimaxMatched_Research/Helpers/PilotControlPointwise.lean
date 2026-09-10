import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotLocalizedScale

/-! Final pilot-failure estimate and assembly of the cellwise factorial risk theorem. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: canonicalJacksonCellError_le_normalizedAggregateScore
/-- The clipped cell estimator's pointwise error is controlled by the promoted
self-normalized aggregate pilot score, uniformly in the evaluation counts. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalJacksonCellError_le_normalizedAggregateScore
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot eval : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j) :
    |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q| ≤
      2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) *
        Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot := by
  let Q := pilotRectangle canonicalJacksonTuning m d pilot
  let center := rectangleCenter Q
  let radius := rectangleRadius Q
  let S := ∑ j : Cell, radius j
  let score := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
    (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot
  have hcenter_nonneg : ∀ j, 0 ≤ center j := by
    intro j
    have hlo := pilotRectangle_nonneg canonicalJacksonTuning m d pilot j
    have hvalid := pilotRectangle_valid canonicalJacksonTuning m d pilot hm j
    dsimp [center, Q, rectangleCenter]
    nlinarith
  have hfactor : 0 ≤ 1 + epsilon⁻¹ := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => by
    exact le_of_lt (pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd j)
  have hdpow : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
    apply Real.one_le_rpow
    · exact_mod_cast hd
    · norm_num
  have hclip :
      |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
          globalCellValue epsilon center| ≤
        d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * S) := by
    rw [jacksonCellStatistic_eq_clipAround]
    exact abs_clipAround_sub_center_le_radius _ _ _ (by positivity)
  have hlip := globalCellValue_lipschitz hepsilon center q hcenter_nonneg hq
  have hgeom : l1CellDistance center q + S ≤ score := by
    exact canonicalPilotGeometry_le_normalizedAggregateScore m hm d hd pilot q hq
  have hdist : 0 ≤ l1CellDistance center q := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hscore : 0 ≤ score := le_trans (add_nonneg hdist hS) hgeom
  calc
    |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon q| ≤
      |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
        globalCellValue epsilon center| +
      |globalCellValue epsilon center - globalCellValue epsilon q| := by
        simpa only [sub_add_sub_cancel] using abs_add_le
          (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            globalCellValue epsilon center)
          (globalCellValue epsilon center - globalCellValue epsilon q)
    _ ≤ d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * S) +
        (1 + epsilon⁻¹) * l1CellDistance center q := add_le_add hclip hlip
    _ ≤ 2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) * score := by
      have hSle : S ≤ score := by linarith
      have hdistle : l1CellDistance center q ≤ score := by linarith
      have hfacscore : 0 ≤ (1 + epsilon⁻¹) * score := mul_nonneg hfactor hscore
      have hfirst : d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * S) ≤
          d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * score) := by gcongr
      have hsecond : (1 + epsilon⁻¹) * l1CellDistance center q ≤
          d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * score) := by
        calc
          (1 + epsilon⁻¹) * l1CellDistance center q ≤
              (1 + epsilon⁻¹) * score := by gcongr
          _ = 1 * ((1 + epsilon⁻¹) * score) := by ring
          _ ≤ d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * score) :=
            mul_le_mul_of_nonneg_right hdpow hfacscore
      calc
        d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * S) +
            (1 + epsilon⁻¹) * l1CellDistance center q ≤
            d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * score) +
              d ^ (1 / 4 : ℝ) * ((1 + epsilon⁻¹) * score) :=
                add_le_add hfirst hsecond
        _ = 2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) * score := by ring

-- @node: canonicalPilotFailureIntegrand_le_badScore
/-- The first-moment pilot-failure integrand is bounded pointwise by the
promoted bad-event aggregate score. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotFailureIntegrand_le_badScore
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot eval : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j) :
    (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)).indicator
        (fun _pilot =>
          |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            globalCellValue epsilon q|) pilot ≤
      2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) *
        (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)).indicator
          (fun pilot =>
            Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
              (fun j (w : Cell → ℕ) => w j)
              Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
              (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot) pilot := by
  let bad := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
    (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)
  by_cases hbad : pilot ∈ bad
  · simp only [bad, Set.indicator_of_mem hbad]
    exact canonicalJacksonCellError_le_normalizedAggregateScore
      epsilon m hepsilon hm d hd pilot eval q hq
  · simp only [bad, Set.indicator_of_notMem hbad, mul_zero, le_refl]

-- @node: canonicalPilotFailureSqIntegrand_le_badScoreSq
/-- The squared pilot-failure integrand is bounded pointwise by the square of
the promoted bad-event aggregate score. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotFailureSqIntegrand_le_badScoreSq
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot eval : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j) :
    (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)).indicator
        (fun _pilot =>
          (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            globalCellValue epsilon q) ^ 2) pilot ≤
      (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)) ^ 2 *
        (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)).indicator
          (fun pilot =>
            Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
              (fun j (w : Cell → ℕ) => w j)
              Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
              (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot ^ 2) pilot := by
  let bad := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
    (fun j (w : Cell → ℕ) => w j)
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
    (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal)
  by_cases hbad : pilot ∈ bad
  · simp only [bad, Set.indicator_of_mem hbad]
    have h := canonicalJacksonCellError_le_normalizedAggregateScore
      epsilon m hepsilon hm d hd pilot eval q hq
    have hfactor : 0 ≤ 2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) := by positivity
    have hscore : 0 ≤
        Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
          (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot := by
      have hL : 0 ≤ logAlphabet d := by
        rw [logAlphabet]
        exact Real.log_nonneg (by
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
          have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff.mpr (by norm_num))
          nlinarith [mul_le_mul he hd1 (by norm_num) (by positivity)])
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
      apply Finset.sum_nonneg
      intro j _hj
      exact add_nonneg (abs_nonneg _) (mul_nonneg (le_of_lt
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH_pos) (by
          unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius
          exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg hL (by positivity))))
    calc
      (jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
          globalCellValue epsilon q) ^ 2 =
          |jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm -
            globalCellValue epsilon q| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) *
          Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
            (fun j (w : Cell → ℕ) => w j)
            Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
            (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hfactor hscore)).2 h
      _ = (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)) ^ 2 *
          Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
            (fun j (w : Cell → ℕ) => w j)
            Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
            (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot ^ 2 := by ring
  · simp only [bad, Set.indicator_of_notMem hbad, mul_zero, le_refl]

-- @node: canonicalJacksonDegree_log_le
/-- The deliberately small canonical Jackson constant still gives a degree
large enough, up to a universal factor, to absorb one logarithmic level. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalJacksonDegree_log_le (d : ℕ) :
    logAlphabet d ≤ 100000 * (jacksonDegree canonicalJacksonTuning d + 1) := by
  have h := Nat.lt_floor_add_one
    ((1 / 100000 : ℝ) * logAlphabet d)
  have hfloor : ⌊(1 / 100000 : ℝ) * logAlphabet d⌋₊ ≤
      jacksonDegree canonicalJacksonTuning d := by
    unfold jacksonDegree
    rw [show canonicalJacksonTuning.jacksonDegreeConstant = (1 / 100000 : ℝ) by
      rw [canonicalJacksonTuning]]
    exact Nat.le_max_right _ _
  have hcast : (⌊(1 / 100000 : ℝ) * logAlphabet d⌋₊ : ℝ) ≤
      jacksonDegree canonicalJacksonTuning d := by exact_mod_cast hfloor
  nlinarith

-- @node: canonicalPilotGoodRadiusSum_le
/-- On a good pilot, the sum of the four random rectangle radii has the local
square-root-plus-linear scale, uniformly down to zero cell masses. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotGoodRadiusSum_le
    (m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) :
    ∑ j : Cell, rectangleRadius
        (pilotRectangle canonicalJacksonTuning m d pilot) j ≤
      2000000 * (Real.sqrt ((∑ j : Cell, q j) * logAlphabet d / m) +
        logAlphabet d / m) := by
  let tau := logAlphabet d / m
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]
  have htau : 0 < tau := div_pos hL hm
  have hcoord (j : Cell) :
      rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j ≤
        2048 * Real.sqrt (q j * tau) + 308224 * tau := by
    let c := pilotCenter m pilot j
    let s := Real.sqrt (c * tau)
    let h := pilotRadius canonicalJacksonTuning m d pilot j
    have hc : 0 ≤ c := by dsimp [c, pilotCenter]; positivity
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = c * tau := by
      dsimp [s]
      rw [Real.sq_sqrt] <;> positivity
    have hh : h = 1024 * (s + tau) := by
      simp [h, pilotRadius, canonicalJacksonTuning,
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH, s, tau, c]
      congr 2
      ring
    have hyoung : s ≤ c / 512 + 128 * tau := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (c / 512 - 128 * tau)]
    have hqle : c ≤ q j + h / 4 := by
      have := (abs_le.mp (hgood j)).2
      linarith
    have hcle : c ≤ 2 * q j + 66048 * tau := by
      rw [hh] at hqle
      nlinarith
    have hqsqrt : Real.sqrt (q j * tau) ^ 2 = q j * tau := by
      rw [Real.sq_sqrt]
      exact mul_nonneg (hq j) (le_of_lt htau)
    have hs_le : s ≤ 2 * Real.sqrt (q j * tau) + 300 * tau := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hctau : c * tau ≤ (2 * q j + 66048 * tau) * tau :=
          mul_le_mul_of_nonneg_right hcle (le_of_lt htau)
        nlinarith [hctau, hqsqrt,
          mul_nonneg (Real.sqrt_nonneg (q j * tau)) (le_of_lt htau)]
    have hr := (pilotRectangle_radius_bounds
      canonicalJacksonTuning m d pilot hm hd j).2
    change rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j ≤ h at hr
    rw [hh] at hr
    nlinarith
  calc
    ∑ j : Cell, rectangleRadius
        (pilotRectangle canonicalJacksonTuning m d pilot) j ≤
        ∑ j : Cell, (2048 * Real.sqrt (q j * tau) + 308224 * tau) :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ ≤ 2000000 * (Real.sqrt ((∑ j : Cell, q j) * tau) + tau) := by
      have hsqrtSum : (∑ j : Cell, Real.sqrt (q j * tau)) ≤
          2 * Real.sqrt ((∑ j : Cell, q j) * tau) := by
        have hsum0 : 0 ≤ ∑ j : Cell, Real.sqrt (q j * tau) :=
          Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
        have hqsum0 : 0 ≤ (∑ j : Cell, q j) * tau :=
          mul_nonneg (Finset.sum_nonneg fun j _ => hq j) (le_of_lt htau)
        apply (sq_le_sq₀ hsum0 (by positivity)).mp
        calc
          (∑ j : Cell, Real.sqrt (q j * tau)) ^ 2 ≤
              4 * ∑ j : Cell, (Real.sqrt (q j * tau)) ^ 2 := by
            simpa [Cell] using Causalean.Mathlib.Analysis.weighted_inner_sq_le
              (Finset.univ : Finset Cell) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
              (fun j => Real.sqrt (q j * tau)) (fun _ _ => by norm_num)
          _ = (2 * Real.sqrt ((∑ j : Cell, q j) * tau)) ^ 2 := by
            simp_rw [Real.sq_sqrt (mul_nonneg (hq _) (le_of_lt htau))]
            rw [show ∑ x : Cell, q x * tau = (∑ x : Cell, q x) * tau by
              rw [Finset.sum_mul]]
            rw [show (2 * Real.sqrt ((∑ j : Cell, q j) * tau)) ^ 2 =
              4 * Real.sqrt ((∑ j : Cell, q j) * tau) ^ 2 by ring,
              Real.sq_sqrt hqsum0]
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
      norm_num [Cell]
      nlinarith [hsqrtSum, Real.sqrt_nonneg ((∑ j : Cell, q j) * tau)]
    _ = _ := by
      dsimp [tau]
      congr 1
      congr 1
      ring_nf

-- @node: canonicalJacksonCoefficientGrowth
/-- The chosen degree constant makes the squared coefficient envelope and
factorial-moment exponential fit strictly inside the stated `d^(1/16)` loss. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalJacksonCoefficientGrowth (d : ℕ) (hd : 1 ≤ d) :
    (((2 : ℝ) ^ 60) ^ (2 * jacksonDegree canonicalJacksonTuning d)) *
        Real.exp (16 * (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2 /
          logAlphabet d) ≤
      Real.exp 1000 * d ^ (1 / 16 : ℝ) := by
  let L := logAlphabet d
  let K := jacksonDegree canonicalJacksonTuning d
  have hdpos : (0 : ℝ) < d := by positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by
    exact_mod_cast hd)
  have hL_eq : L = 1 + Real.log (d : ℝ) := by
    dsimp [L, logAlphabet]
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
  have hL : 1 ≤ L := by rw [hL_eq]; linarith
  have hfloor : (⌊(1 / 100000 : ℝ) * L⌋₊ : ℝ) ≤
      (1 / 100000 : ℝ) * L := Nat.floor_le (by positivity)
  have hK : (K : ℝ) ≤ 2 + L / 100000 := by
    dsimp [K, jacksonDegree]
    rw [show canonicalJacksonTuning.jacksonDegreeConstant = (1 / 100000 : ℝ) by
      rw [canonicalJacksonTuning]]
    rw [Nat.cast_max]
    apply max_le
    · linarith
    · exact hfloor.trans (by linarith)
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hKsq : (K : ℝ) ^ 2 ≤ L * (5 + L / 10000000000) := by
    have hsquare := (sq_le_sq₀ hK0 (by positivity)).2 hK
    nlinarith
  have hKsqdiv : (K : ℝ) ^ 2 / L ≤ 5 + L / 10000000000 :=
    (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hL)).2 (by nlinarith [hKsq])
  have hexponent : 120 * (K : ℝ) + 16 * (K : ℝ) ^ 2 / L ≤
      1000 + Real.log (d : ℝ) / 16 := by
    have hlog : Real.log (d : ℝ) = L - 1 := by linarith [hL_eq]
    rw [hlog]
    calc
      120 * (K : ℝ) + 16 * (K : ℝ) ^ 2 / L ≤
          120 * (2 + L / 100000) + 16 * (5 + L / 10000000000) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hK (by norm_num)
        · calc
            16 * (K : ℝ) ^ 2 / L = 16 * ((K : ℝ) ^ 2 / L) := by ring
            _ ≤ 16 * (5 + L / 10000000000) :=
              mul_le_mul_of_nonneg_left hKsqdiv (by norm_num)
      _ ≤ 1000 + (L - 1) / 16 := by
        norm_num
        nlinarith [hL]
  have hpow : (((2 : ℝ) ^ 60) ^ (2 * K)) ≤ Real.exp (120 * (K : ℝ)) := by
    calc
      (((2 : ℝ) ^ 60) ^ (2 * K)) = (2 : ℝ) ^ (120 * K) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (Real.exp 1) ^ (120 * K) := by
        exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _ = Real.exp (120 * (K : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
  calc
    (((2 : ℝ) ^ 60) ^ (2 * K)) *
        Real.exp (16 * (K : ℝ) ^ 2 / L) ≤
        Real.exp (120 * (K : ℝ)) * Real.exp (16 * (K : ℝ) ^ 2 / L) := by
      gcongr
    _ = Real.exp (120 * (K : ℝ) + 16 * (K : ℝ) ^ 2 / L) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (1000 + Real.log (d : ℝ) / 16) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp 1000 * d ^ (1 / 16 : ℝ) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hdpos]
      congr 2
      ring

-- @node: canonicalGoodPilotFactorialLift_sq_le
/-- On a good pilot, the centered factorial lift of the chosen Jackson
polynomial has the required local product-Poisson second moment. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalGoodPilotFactorialLift_sq_le
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) :
    let Q := pilotRectangle canonicalJacksonTuning m d pilot
    let p := jacksonTensorPolynomial epsilon
      (jacksonDegree canonicalJacksonTuning d)
      (jacksonDegree_ge_two canonicalJacksonTuning d) Q
      (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
      (pilotRectangle_nonneg canonicalJacksonTuning m d pilot)
    ∫ eval : Cell → ℕ,
        factorialPolynomialLift m p eval (rectangleCenter Q) (rectangleRadius Q)
          (globalCellValue epsilon (rectangleCenter Q)) ^ 2
      ∂Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal) ≤
      Real.exp 1000 * d ^ (1 / 16 : ℝ) *
        ((1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius Q j) ^ 2 := by
  dsimp only
  let Q := pilotRectangle canonicalJacksonTuning m d pilot
  let K := jacksonDegree canonicalJacksonTuning d
  let p := jacksonTensorPolynomial epsilon K
    (jacksonDegree_ge_two canonicalJacksonTuning d) Q
    (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
    (pilotRectangle_nonneg canonicalJacksonTuning m d pilot)
  have hr : ∀ j, 0 < rectangleRadius Q j :=
    pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd
  have hmem : ∀ j, |q j - rectangleCenter Q j| ≤ rectangleRadius Q j := by
    intro j
    have hj := pilotGoodEvent_mem_pilotRectangle
      canonicalJacksonTuning m d pilot q hq hgood j
    rw [abs_le]
    simp only [Q, rectangleCenter, rectangleRadius] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  have hratio : ∀ j, q j / (m * rectangleRadius Q j ^ 2) ≤
      1 / logAlphabet d := by
    exact canonicalPilot_noiseToRadius_le m hm d hd pilot q hgood
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]
  have henv := jacksonCenteredNormalizedPolynomial_coeffL1_le
    epsilon hepsilon K (jacksonDegree_ge_two canonicalJacksonTuning d) Q
    (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
    (pilotRectangle_nonneg canonicalJacksonTuning m d pilot) hr
  have hbase := factorialPolynomialLift_sq_le_coeffL1
    m q (rectangleCenter Q) (rectangleRadius Q) (1 / logAlphabet d)
    hm hq hr hmem hratio (by positivity) p
    (globalCellValue epsilon (rectangleCenter Q)) (2 * K)
    (fun alpha halpha j => (henv.2 alpha halpha j).trans (by
      exact_mod_cast (by omega : 2 * (K - 1) ≤ 2 * K)))
  have hbase' :
      (∫ eval : Cell → ℕ,
        factorialPolynomialLift m p eval (rectangleCenter Q) (rectangleRadius Q)
          (globalCellValue epsilon (rectangleCenter Q)) ^ 2
        ∂Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)) ≤
      (∑ alpha ∈ (centeredNormalizedPolynomial p (rectangleCenter Q)
        (rectangleRadius Q) (globalCellValue epsilon (rectangleCenter Q))).support,
        |(centeredNormalizedPolynomial p (rectangleCenter Q)
          (rectangleRadius Q) (globalCellValue epsilon (rectangleCenter Q))).coeff alpha|) ^ 2 *
        Real.exp (4 * (2 * (K : ℝ)) ^ 2 * (1 / logAlphabet d)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbase
  refine hbase'.trans ?_
  have hgrowth := canonicalJacksonCoefficientGrowth d hd
  have hfac : 0 ≤ 1 + epsilon⁻¹ := by positivity
  have hS : 0 ≤ ∑ j : Cell, rectangleRadius Q j :=
    Finset.sum_nonneg fun j _ => le_of_lt (hr j)
  have hpoweq : ((((2 : ℝ) ^ 60) ^ K) ^ 2) =
      ((2 : ℝ) ^ 60) ^ (2 * K) := by
    calc
      ((((2 : ℝ) ^ 60) ^ K) ^ 2) = ((2 : ℝ) ^ 60) ^ (K * 2) := by
        rw [pow_mul]
      _ = ((2 : ℝ) ^ 60) ^ (2 * K) := by rw [Nat.mul_comm]
  calc
    (∑ alpha ∈ (centeredNormalizedPolynomial p (rectangleCenter Q)
        (rectangleRadius Q) (globalCellValue epsilon (rectangleCenter Q))).support,
        |(centeredNormalizedPolynomial p (rectangleCenter Q)
          (rectangleRadius Q) (globalCellValue epsilon (rectangleCenter Q))).coeff alpha|) ^ 2 *
        Real.exp (4 * (2 * K : ℝ) ^ 2 * (1 / logAlphabet d)) ≤
      ((((2 : ℝ) ^ 60) ^ K * (1 + epsilon⁻¹) *
        ∑ j : Cell, rectangleRadius Q j) ^ 2) *
        Real.exp (4 * (2 * (K : ℝ)) ^ 2 * (1 / logAlphabet d)) := by
          gcongr
          exact henv.1
    _ = ((((2 : ℝ) ^ 60) ^ (2 * K)) *
          Real.exp (16 * (K : ℝ) ^ 2 / logAlphabet d)) *
        ((1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius Q j) ^ 2 := by
          have hexpeq : Real.exp (4 * (2 * (K : ℝ)) ^ 2 *
              (1 / logAlphabet d)) =
              Real.exp (16 * (K : ℝ) ^ 2 / logAlphabet d) := by
            congr 1
            field_simp
            ring
          rw [mul_pow, mul_pow, hpoweq]
          rw [hexpeq]
          ring
    _ ≤ Real.exp 1000 * d ^ (1 / 16 : ℝ) *
        ((1 + epsilon⁻¹) * ∑ j : Cell, rectangleRadius Q j) ^ 2 := by
          gcongr

-- @node: canonicalGoodPilotConditionalBias
/-- Conditional on a good pilot, Jackson approximation plus clipping gives
the local bias bound before averaging over the pilot. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated cj condition holds](hyp:hCj), and [the polynomial has the stated approximation guarantee](hyp:happrox), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalGoodPilotConditionalBias
    (epsilon m : ℝ) (hepsilon : 0 < epsilon) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot : Cell → ℕ) (q : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j)
    (Cj : ℝ) (hCj : 0 < Cj)
    (happrox : ∀ (K : ℕ) (Q : Rectangle) (hK : 2 ≤ K) (hQ : Q.Valid)
      (hQ0 : ∀ j, 0 ≤ Q.1 j), (∀ j, 0 < rectangleRadius Q j) →
      ∀ v, inRectangle Q v →
        |MvPolynomial.eval v (jacksonTensorPolynomial epsilon K hK Q hQ hQ0) -
          globalCellValue epsilon v| ≤ Cj * jacksonPointwiseScale Q K v)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) :
    let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
    |(∫ eval : Cell → ℕ,
        jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm ∂μe) -
        globalCellValue epsilon q| ≤
      Cj * ∑ j : Cell,
        (10000000 * Real.sqrt (q j * (logAlphabet d / m)) /
            jacksonDegree canonicalJacksonTuning d +
          rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j /
            (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2) +
      Real.exp 1000 * (1 + epsilon⁻¹) * d ^ (-3 / 16 : ℝ) *
        ∑ j : Cell, rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j := by
  dsimp only
  let Q := pilotRectangle canonicalJacksonTuning m d pilot
  let center := rectangleCenter Q
  let radius := rectangleRadius Q
  let K := jacksonDegree canonicalJacksonTuning d
  let p := jacksonTensorPolynomial epsilon K
    (jacksonDegree_ge_two canonicalJacksonTuning d) Q
    (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
    (pilotRectangle_nonneg canonicalJacksonTuning m d pilot)
  let centerValue := globalCellValue epsilon center
  let lift := fun eval : Cell → ℕ =>
    factorialPolynomialLift m p eval center radius centerValue
  let raw := fun eval : Cell → ℕ => centerValue + lift eval
  let S := ∑ j : Cell, radius j
  let scale := (1 + epsilon⁻¹) * S
  let clipRadius := d ^ (1 / 4 : ℝ) * scale
  let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  have hr : ∀ j, 0 < radius j :=
    pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd
  have hS : 0 < S := Finset.sum_pos (fun j _ => hr j) (Finset.univ_nonempty)
  have hfac : 0 < 1 + epsilon⁻¹ := by positivity
  have hclipRadius : 0 < clipRadius := by
    dsimp [clipRadius, scale]
    positivity
  have hliftInt : Integrable lift μe := by
    dsimp [lift, μe]
    simp only [factorialPolynomialLift]
    apply integrable_finsetSum
    intro alpha _halpha
    exact (normalizedCenteredFactorialMonomial_memLp_two
      m q center radius hr alpha).integrable one_le_two |>.const_mul _
  have hliftSqInt : Integrable (fun eval => (lift eval) ^ 2) μe := by
    exact (memLp_two_iff_integrable_sq hliftInt.aestronglyMeasurable).mp
      (by
        dsimp [lift, μe]
        exact memLp_finsetSum _ fun alpha halpha =>
          (normalizedCenteredFactorialMonomial_memLp_two
            m q center radius hr alpha).const_mul _)
  have hliftMean : ∫ eval, lift eval ∂μe = MvPolynomial.eval q p - centerValue := by
    exact factorialPolynomialLift_expectation m hm q center radius hq hr p centerValue
  have hstat (eval : Cell → ℕ) :
      jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm =
        clipAround centerValue clipRadius (raw eval) := by
    rw [jacksonCellStatistic_eq_clipAround]
  have hdisp (eval : Cell → ℕ) :
      |clipAround centerValue clipRadius (raw eval) - raw eval| ≤
        (lift eval) ^ 2 / clipRadius := by
    simpa [raw, lift] using
      abs_clipAround_sub_self_le_sq_div centerValue clipRadius (raw eval) hclipRadius
  have hdispInt : Integrable
      (fun eval => clipAround centerValue clipRadius (raw eval) - raw eval) μe := by
    apply (hliftSqInt.div_const clipRadius).mono'
    · fun_prop
    · filter_upwards with eval
      simpa only [Real.norm_eq_abs] using hdisp eval
  have hrawInt : Integrable raw μe := (integrable_const centerValue).add hliftInt
  have hmeanDecomp :
      (∫ eval, jacksonCellStatistic canonicalJacksonTuning epsilon d m pilot eval hm ∂μe) -
          globalCellValue epsilon q =
        (MvPolynomial.eval q p - globalCellValue epsilon q) +
          ∫ eval, (clipAround centerValue clipRadius (raw eval) - raw eval) ∂μe := by
    simp_rw [hstat]
    rw [show (fun eval => clipAround centerValue clipRadius (raw eval)) =
        fun eval => raw eval + (clipAround centerValue clipRadius (raw eval) - raw eval) by
      funext eval; ring]
    rw [integral_add hrawInt hdispInt, integral_add, hliftMean]
    · simp only [integral_const, probReal_univ, one_smul]
      ring
    · exact integrable_const centerValue
    · exact hliftInt
  have hqmem := pilotGoodEvent_mem_pilotRectangle
    canonicalJacksonTuning m d pilot q hq hgood
  have happ0 := happrox K Q (jacksonDegree_ge_two canonicalJacksonTuning d)
    (pilotRectangle_valid canonicalJacksonTuning m d pilot hm)
    (pilotRectangle_nonneg canonicalJacksonTuning m d pilot) hr q
      (fun j => hqmem j)
  have hscale : jacksonPointwiseScale Q K q ≤ ∑ j : Cell,
      (10000000 * Real.sqrt (q j * (logAlphabet d / m)) / (K : ℝ) +
        radius j / (K : ℝ) ^ 2) := by
    unfold jacksonPointwiseScale
    have hKpos : (0 : ℝ) < K := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
        (jacksonDegree_ge_two canonicalJacksonTuning d))
    apply Finset.sum_le_sum
    intro j _
    apply add_le_add
    · exact div_le_div_of_nonneg_right
        (by simpa [Q] using
          (canonicalPilotGoodSqrtWidth_le m hm d hd pilot q hq hgood j))
        (le_of_lt hKpos)
    · rfl
  have happ : |MvPolynomial.eval q p - globalCellValue epsilon q| ≤
      Cj * ∑ j : Cell,
        (10000000 * Real.sqrt (q j * (logAlphabet d / m)) / (K : ℝ) +
          radius j / (K : ℝ) ^ 2) := by
    refine happ0.trans ?_
    exact mul_le_mul_of_nonneg_left hscale (le_of_lt hCj)
  have hl2 := canonicalGoodPilotFactorialLift_sq_le
    epsilon m hepsilon hm d hd pilot q hq hgood
  have hintDisp : |∫ eval, (clipAround centerValue clipRadius (raw eval) - raw eval) ∂μe| ≤
      Real.exp 1000 * (1 + epsilon⁻¹) * d ^ (-3 / 16 : ℝ) * S := by
    calc
      |∫ eval, (clipAround centerValue clipRadius (raw eval) - raw eval) ∂μe| ≤
          ∫ eval, |clipAround centerValue clipRadius (raw eval) - raw eval| ∂μe :=
        abs_integral_le_integral_abs
      _ ≤ ∫ eval, (lift eval) ^ 2 / clipRadius ∂μe := by
        exact integral_mono hdispInt.abs (hliftSqInt.div_const _) hdisp
      _ = (∫ eval, (lift eval) ^ 2 ∂μe) / clipRadius := by rw [integral_div]
      _ ≤ (Real.exp 1000 * d ^ (1 / 16 : ℝ) * scale ^ 2) / clipRadius := by
        gcongr
      _ = Real.exp 1000 * (1 + epsilon⁻¹) * d ^ (-3 / 16 : ℝ) * S := by
        dsimp [clipRadius, scale]
        rw [show (-3 / 16 : ℝ) = 1 / 16 - 1 / 4 by norm_num,
          Real.rpow_sub (by positivity : (0 : ℝ) < d)]
        field_simp
  rw [hmeanDecomp]
  refine (abs_add_le _ _).trans ?_
  calc
      |MvPolynomial.eval q p - globalCellValue epsilon q| +
        |∫ eval, clipAround centerValue clipRadius (raw eval) - raw eval ∂μe| ≤
      Cj * ∑ j : Cell,
        (10000000 * Real.sqrt (q j * (logAlphabet d / m)) / (K : ℝ) +
          radius j / (K : ℝ) ^ 2) +
        Real.exp 1000 * (1 + epsilon⁻¹) * d ^ (-3 / 16 : ℝ) * S :=
          add_le_add happ hintDisp
    _ = _ := by rfl


end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
