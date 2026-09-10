import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotControlIntegration

/-! Final assembly of the cellwise factorial risk theorem. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option maxHeartbeats 1000000 in
-- The final assembly needs the larger budget for nested integral and finite-sum normalizations.
-- @node: lem:centered-factorial-pilot-control
/-- If [the product experiment has the stated independent-sampling law](hyp:h_iid), then [the canonical Jackson tuning simultaneously provides the stated pilot/evaluation laws, factorial moment identities, and uniform bias, variance, and pilot-failure bounds](goal). -/
lemma centered_factorial_pilot_control
    (h_iid : ∀ {d n : ℕ} (P : DiscreteLaw d), IidSampling P (productLaw P n)) :
    ∃ tuning : JacksonTuning, tuning = canonicalJacksonTuning ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ Cepsilon : ℝ, 0 < Cepsilon ∧
    ∀ (n d : ℕ) (P : DiscreteLaw d), (hn : 0 < n) → ObservedModelClass epsilon P →
      let m : ℝ := n / 8
      let hm : 0 < m := by exact div_pos (Nat.cast_pos.mpr hn) (by norm_num)
      Measure.map Prod.fst (uncappedMarkedCountLaw n P) =
          ProbabilityTheory.poissonMeasure (Real.toNNReal ((n : ℝ) / 4)) ∧
      Measure.map Prod.snd (uncappedMarkedCountLaw n P) = pilotEvaluationTableLaw m P ∧
      (∀ x : Fin d, Measure.map (fun z => (z.1 x, z.2 x))
          (pilotEvaluationTableLaw m P) = pilotEvaluationLaw m (cellVector P x)) ∧
      (∀ (x : Fin d) (pilot : Cell → ℕ) (j : Cell) (z : ℝ) (h t : ℕ),
        conditionalEvaluationExpectation m (cellVector P x) pilot (fun eval =>
            centeredFactorial m h (eval j) z) = (cellVector P x j - z) ^ h ∧
        conditionalEvaluationExpectation m (cellVector P x) pilot (fun eval =>
            centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z) =
          ∑ l ∈ Finset.range (min h t + 1),
            (Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
              (cellVector P x j / m) ^ l *
                (cellVector P x j - z) ^ (h + t - 2 * l)) ∧
      ∀ x : Fin d,
      |cellStatisticExpectation tuning epsilon d m (cellVector P x) hm -
          globalCellValue epsilon (cellVector P x)| ≤
        Cepsilon * (Real.sqrt (cellMass P x / (m * logAlphabet d)) +
          1 / (m * logAlphabet d)) ∧
      cellStatisticVariance tuning epsilon d m (cellVector P x) hm ≤
        Cepsilon * d ^ (1 / 16 : ℝ) *
          (cellMass P x * logAlphabet d / m + logAlphabet d ^ 2 / m ^ 2) ∧
      pilotFailureContribution tuning epsilon d m (cellVector P x) hm ≤
        Cepsilon * (Real.sqrt (cellMass P x / (m * logAlphabet d)) +
          1 / (m * logAlphabet d)) ∧
      pilotFailureSecondMomentContribution tuning epsilon d m (cellVector P x) hm ≤
        Cepsilon * d ^ (1 / 16 : ℝ) *
          (cellMass P x * logAlphabet d / m + logAlphabet d ^ 2 / m ^ 2) := by
  classical
  rcases simultaneous_jackson_certificate with ⟨_A, _hA, hcertificate⟩
  refine ⟨canonicalJacksonTuning, rfl, ?_⟩
  intro epsilon hepsilon hepsilonHalf
  rcases hcertificate epsilon hepsilon hepsilonHalf with ⟨Cj, hCj, hcert⟩
  let C1 := Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 1
  let C2 := Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 2
  let F := 1 + epsilon⁻¹
  let Cepsilon := 1 +
    (50000000000000000 * Cj + 450000000 * Real.exp 1000 * F) + 450 * F * C1 +
    8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 + 8 * F ^ 2 * C2
  have hF : 0 < F := by dsimp [F]; positivity
  have hC1 : 0 < C1 := by
    exact Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant_pos 4 1
  have hC2 : 0 < C2 := by
    exact Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant_pos 4 2
  have hCepsilon : 0 < Cepsilon := by
    have hJ : 0 ≤ 50000000000000000 * Cj + 450000000 * Real.exp 1000 * F := by positivity
    have h1 : 0 ≤ 450 * F * C1 := by positivity
    have h2 : 0 ≤ 8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 := by positivity
    have h3 : 0 ≤ 8 * F ^ 2 * C2 :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F)) (le_of_lt hC2)
    have htail : 0 ≤
        (50000000000000000 * Cj + 450000000 * Real.exp 1000 * F) + 450 * F * C1 +
        8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 + 8 * F ^ 2 * C2 := by
      linarith
    dsimp [Cepsilon]
    linarith
  refine ⟨Cepsilon, hCepsilon, ?_⟩
  intro n d P hn _hmodel
  dsimp only
  let m : ℝ := n / 8
  have hm : 0 < m := div_pos (Nat.cast_pos.mpr hn) (by norm_num)
  refine ⟨uncappedMarkedCountLaw_count n P, ?_, pilotEvaluationTableLaw_cell m P,
    ?_, ?_⟩
  · simpa [m] using uncappedMarkedCountLaw_table n P
  · intro x pilot j z h t
    have hq : ∀ k, 0 ≤ cellVector P x k := by
      intro k
      exact ENNReal.toReal_nonneg
    exact ⟨conditionalEvaluationExpectation_centeredFactorial
      m hm (cellVector P x) hq pilot j z h,
      conditionalEvaluationExpectation_centeredFactorial_mul
        m hm (cellVector P x) hq pilot j z h t⟩
  · intro x
    let q := cellVector P x
    let target := globalCellValue epsilon q
    let L := logAlphabet d
    let v := Real.sqrt (cellMass P x * L / m) + L / m
    let μp := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
    let μe := Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
    let stat := fun z : (Cell → ℕ) × (Cell → ℕ) =>
      jacksonCellStatistic canonicalJacksonTuning epsilon d m z.1 z.2 hm
    let err := fun z : (Cell → ℕ) × (Cell → ℕ) => stat z - target
    let good := {pilot : Cell → ℕ |
      pilotGoodEvent canonicalJacksonTuning m d pilot q}
    have hd : 1 ≤ d := Fin.pos_iff_nonempty.mpr ⟨x⟩
    have hq : ∀ j, 0 ≤ q j := fun _ => ENNReal.toReal_nonneg
    have hsumq : ∑ j : Cell, q j = cellMass P x := by
      dsimp [q]
      rw [Fintype.sum_prod_type]
      simp_rw [Fin.sum_univ_two]
      simp [cellVector, cellMass, finTwoEquiv]
      ring
    have hmass : 0 ≤ cellMass P x := by
      rw [← hsumq]
      exact Finset.sum_nonneg fun j _ => hq j
    have hL : 0 < L := by
      dsimp [L, logAlphabet]
      apply Real.log_pos
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]
    have hL1 : 1 ≤ L := by
      dsimp [L, logAlphabet]
      rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
      linarith [Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
    have hsqrtScaleEq : Real.sqrt (cellMass P x * L / m) =
        L * Real.sqrt (cellMass P x / (m * L)) := by
      have ha0 : 0 ≤ cellMass P x / (m * L) := by positivity
      calc
        Real.sqrt (cellMass P x * L / m) =
            Real.sqrt ((cellMass P x / (m * L)) * L ^ 2) := by
              congr 1
              field_simp
        _ = Real.sqrt (cellMass P x / (m * L)) * Real.sqrt (L ^ 2) :=
          Real.sqrt_mul ha0 _
        _ = L * Real.sqrt (cellMass P x / (m * L)) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hL]
          ring
    have hv0 : 0 ≤ v := by dsimp [v]; positivity
    have hgoodMeas : MeasurableSet good := (Set.to_countable good).measurableSet
    let score := Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
      (fun j (w : Cell → ℕ) => w j)
      Causalean.Stat.Concentration.PoissonSelfNormalized.universalH L
      m.toNNReal (fun j => (q j).toNNReal)
    let Afail := 2 * d ^ (1 / 4 : ℝ) * F
    have hAfail : 0 ≤ Afail := by dsimp [Afail]; positivity
    have hscore0 (pilot : Cell → ℕ) : 0 ≤ score pilot := by
      dsimp [score]
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
      apply Finset.sum_nonneg
      intro j _hj
      unfold Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation
        Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
      positivity
    have hscoreLp : MemLp score 2 μp := by
      simpa [score, μp, L] using
        canonicalNormalizedAggregateScore_memLp_two m hm d hd q hq
    have herrPoint (z : (Cell → ℕ) × (Cell → ℕ)) : |err z| ≤ Afail * score z.1 := by
      simpa [err, stat, target, Afail, F, score, L] using
        canonicalJacksonCellError_le_normalizedAggregateScore
          epsilon m hepsilon hm d hd z.1 z.2 q hq
    have herrLp : MemLp err 2 (μp.prod μe) := by
      have hdom := (hscoreLp.const_mul Afail).comp_fst μe
      apply hdom.mono (by fun_prop)
      filter_upwards with z
      simpa only [Real.norm_eq_abs, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hAfail, abs_of_nonneg (hscore0 z.1)] using herrPoint z
    have herrInt : Integrable err (μp.prod μe) := herrLp.integrable one_le_two
    have herrSqInt : Integrable (fun z => err z ^ 2) (μp.prod μe) := herrLp.integrable_sq
    have hbiasDecomp :
        |cellStatisticExpectation canonicalJacksonTuning epsilon d m q hm - target| ≤
          (50000000000000000 * Cj + 450000000 * Real.exp 1000 * F) *
            (Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)) +
          pilotFailureContribution canonicalJacksonTuning epsilon d m q hm := by
      let ce := fun pilot : Cell → ℕ => ∫ eval, err (pilot, eval) ∂μe
      let r := Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)
      let Bgood := (50000000000000000 * Cj +
        450000000 * Real.exp 1000 * F) * r
      let goodProd : Set ((Cell → ℕ) × (Cell → ℕ)) := {z | z.1 ∈ good}
      have hgoodProdMeas : MeasurableSet goodProd :=
        hgoodMeas.preimage measurable_fst
      have hceGood (pilot : Cell → ℕ) (hp : pilot ∈ good) : |ce pilot| ≤ Bgood := by
        have hb := canonicalGoodPilotConditionalBias epsilon m hepsilon hm d hd
          pilot q hq Cj hCj (fun K Q hK hQ hQ0 hQr v hv =>
            (hcert K Q hK hQ hQ0 hQr).2.1 v hv) hp
        have hS := canonicalPilotGoodRadiusSum_le m hm d hd pilot q hq hp
        have hlogs := canonicalLogPowerBounds d hd
        have hlogs2 := canonicalLogSquaredPowerBounds d hd
        dsimp [ce, err, stat, target] at hb ⊢
        have herrPilotInt : Integrable (fun eval => err (pilot, eval)) μe := by
          apply (integrable_const (Afail * score pilot)).mono'
          · fun_prop
          · filter_upwards with eval
            simpa only [Real.norm_eq_abs, abs_of_nonneg hAfail,
              abs_of_nonneg (hscore0 pilot)] using herrPoint (pilot, eval)
        have hstatPilotInt : Integrable (fun eval => stat (pilot, eval)) μe := by
          exact herrPilotInt.add (integrable_const target) |>.congr
            (Filter.Eventually.of_forall fun eval => by dsimp [err]; ring)
        have hceEq : (∫ eval, err (pilot, eval) ∂μe) =
            (∫ eval, stat (pilot, eval) ∂μe) - target := by
          rw [show (fun eval => err (pilot, eval)) =
              fun eval => stat (pilot, eval) - target by funext eval; rfl,
            integral_sub hstatPilotInt (integrable_const target), integral_const,
            probReal_univ, one_smul]
        have hS' : ∑ j : Cell, rectangleRadius
            (pilotRectangle canonicalJacksonTuning m d pilot) j ≤ 2000000 * v := by
          simpa [v, L, hsumq] using hS
        have hL1 : 1 ≤ L := by
          dsimp [L, logAlphabet]
          rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
          linarith [Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
        have hsqrtEq := hsqrtScaleEq
        have hvle : v ≤ L ^ 2 * r := by
          dsimp [v, r]
          rw [hsqrtEq]
          have ha := Real.sqrt_nonneg (cellMass P x / (m * L))
          have hLL : L ≤ L ^ 2 := by nlinarith
          have hmul := mul_le_mul_of_nonneg_right hLL ha
          have hbEq : L ^ 2 * (1 / (m * L)) = L / m := by
            field_simp [ne_of_gt hL, ne_of_gt hm]
          calc
            L * Real.sqrt (cellMass P x / (m * L)) + L / m ≤
                L ^ 2 * Real.sqrt (cellMass P x / (m * L)) + L / m := by
                  linarith
            _ = L ^ 2 * (Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)) := by
              rw [mul_add, hbEq]
        have hKpos : (0 : ℝ) < jacksonDegree canonicalJacksonTuning d := by
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
            (jacksonDegree_ge_two canonicalJacksonTuning d))
        have hfirst : Real.sqrt (cellMass P x * L / m) /
              jacksonDegree canonicalJacksonTuning d ≤
            150000 * Real.sqrt (cellMass P x / (m * L)) := by
          rw [hsqrtEq]
          have := mul_le_mul_of_nonneg_right hlogs.1
            (Real.sqrt_nonneg (cellMass P x / (m * L)))
          calc
            L * Real.sqrt (cellMass P x / (m * L)) /
                jacksonDegree canonicalJacksonTuning d =
              (L / jacksonDegree canonicalJacksonTuning d) *
                Real.sqrt (cellMass P x / (m * L)) := by ring
            _ ≤ _ := this
        have hLKsq : (L / (jacksonDegree canonicalJacksonTuning d : ℝ)) ^ 2 ≤
            150000 ^ 2 := (sq_le_sq₀ (by positivity) (by norm_num)).2 hlogs.1
        have hsecond : (L / m) / (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2 ≤
            22500000000 * (1 / (m * L)) := by
          have ht := mul_le_mul_of_nonneg_right hLKsq (by positivity : 0 ≤ 1 / (m * L))
          field_simp [ne_of_gt hL, ne_of_gt hm, ne_of_gt hKpos] at ht ⊢
          nlinarith
        have hsqrtSum : (∑ j : Cell, Real.sqrt (q j * (L / m))) ≤
            2 * Real.sqrt (cellMass P x * L / m) := by
          have hs := sum_cell_sqrt_mul_le q hq (L / m) (by positivity)
          rw [hsumq] at hs
          convert hs using 1 <;> ring
        have hlocal : (∑ j : Cell,
              (10000000 * Real.sqrt (q j * (L / m)) /
                  jacksonDegree canonicalJacksonTuning d +
                rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j /
                  (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2)) ≤
            22000000 * Real.sqrt (cellMass P x * L / m) /
                jacksonDegree canonicalJacksonTuning d +
              2000000 * (L / m) /
                (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2 := by
          let K : ℝ := jacksonDegree canonicalJacksonTuning d
          let a := Real.sqrt (cellMass P x * L / m)
          let b := L / m
          have hK1 : 1 ≤ K := by
            dsimp [K]
            exact_mod_cast (le_trans (by omega : 1 ≤ 2)
              (jacksonDegree_ge_two canonicalJacksonTuning d))
          have ha0 : 0 ≤ a := Real.sqrt_nonneg _
          have haK : a / K ^ 2 ≤ a / K := by
            exact div_le_div_of_nonneg_left ha0 (by positivity)
              (by nlinarith [sq_nonneg (K - 1)])
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
          rw [show (∑ j : Cell, 10000000 * Real.sqrt (q j * (L / m))) =
              10000000 * ∑ j : Cell, Real.sqrt (q j * (L / m)) by
                rw [Finset.mul_sum]]
          have hs1 := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrtSum (by norm_num : (0 : ℝ) ≤ 10000000))
            (by positivity : 0 ≤ K)
          have hs2 := div_le_div_of_nonneg_right hS' (by positivity : 0 ≤ K ^ 2)
          have hs2' : (∑ j : Cell, rectangleRadius
                (pilotRectangle canonicalJacksonTuning m d pilot) j) / K ^ 2 ≤
              2000000 * (a + b) / K ^ 2 := by
            simpa [v, a, b] using hs2
          dsimp [K, a, b] at haK hs1 hs2' ⊢
          ring_nf at haK hs1 hs2' ⊢
          linarith [haK, hs1, hs2']
        have happ : Cj * (22000000 * Real.sqrt (cellMass P x * L / m) /
              jacksonDegree canonicalJacksonTuning d +
            2000000 * (L / m) / (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2) ≤
            50000000000000000 * Cj * r := by
          have hfirst' := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 22000000)
          have hsecond' := mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 2000000)
          have hinner : 22000000 * Real.sqrt (cellMass P x * L / m) /
                jacksonDegree canonicalJacksonTuning d +
              2000000 * (L / m) / (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2 ≤
              50000000000000000 * r := by
            dsimp [r]
            calc
              22000000 * Real.sqrt (cellMass P x * L / m) /
                    jacksonDegree canonicalJacksonTuning d +
                  2000000 * (L / m) /
                    (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2 ≤
                22000000 * (150000 * Real.sqrt (cellMass P x / (m * L))) +
                  2000000 * (22500000000 * (1 / (m * L))) := by
                    simpa [mul_div_assoc] using add_le_add hfirst' hsecond'
              _ ≤ 50000000000000000 *
                  (Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)) := by
                    nlinarith [Real.sqrt_nonneg (cellMass P x / (m * L)),
                      div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
                        (mul_nonneg (le_of_lt hm) (le_of_lt hL))]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hinner (le_of_lt hCj)
        have hclip : Real.exp 1000 * F * d ^ (-3 / 16 : ℝ) *
              (∑ j : Cell, rectangleRadius
                (pilotRectangle canonicalJacksonTuning m d pilot) j) ≤
            450000000 * Real.exp 1000 * F * r := by
          have hcoef : 0 ≤ Real.exp 1000 * F * d ^ (-3 / 16 : ℝ) := by positivity
          calc
            Real.exp 1000 * F * d ^ (-3 / 16 : ℝ) *
                (∑ j : Cell, rectangleRadius
                  (pilotRectangle canonicalJacksonTuning m d pilot) j) ≤
              (Real.exp 1000 * F * d ^ (-3 / 16 : ℝ)) * (2000000 * v) :=
                mul_le_mul_of_nonneg_left hS' hcoef
            _ ≤ (Real.exp 1000 * F * d ^ (-3 / 16 : ℝ)) *
                (2000000 * (L ^ 2 * r)) := by gcongr
            _ = 2000000 * Real.exp 1000 * F *
                (L ^ 2 * d ^ (-3 / 16 : ℝ)) * r := by ring
            _ ≤ 2000000 * Real.exp 1000 * F * 225 * r := by
              gcongr
              simpa [L] using hlogs2.1
            _ = 450000000 * Real.exp 1000 * F * r := by ring
        rw [hceEq]
        refine hb.trans ?_
        have happLocal := mul_le_mul_of_nonneg_left hlocal (le_of_lt hCj)
        calc
          Cj * ∑ j : Cell,
                (10000000 * Real.sqrt (q j * (logAlphabet d / m)) /
                    jacksonDegree canonicalJacksonTuning d +
                  rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j /
                    (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2) +
              Real.exp 1000 * (1 + epsilon⁻¹) * d ^ (-3 / 16 : ℝ) *
                ∑ j : Cell, rectangleRadius
                  (pilotRectangle canonicalJacksonTuning m d pilot) j ≤
            Cj * (22000000 * Real.sqrt (cellMass P x * L / m) /
                jacksonDegree canonicalJacksonTuning d +
              2000000 * (L / m) /
                (jacksonDegree canonicalJacksonTuning d : ℝ) ^ 2) +
              Real.exp 1000 * F * d ^ (-3 / 16 : ℝ) *
                ∑ j : Cell, rectangleRadius
                  (pilotRectangle canonicalJacksonTuning m d pilot) j := by
                    simpa [L, F] using add_le_add happLocal
                      (le_refl (Real.exp 1000 * F * d ^ (-3 / 16 : ℝ) *
                        ∑ j : Cell, rectangleRadius
                          (pilotRectangle canonicalJacksonTuning m d pilot) j))
          _ ≤ 50000000000000000 * Cj * r +
              450000000 * Real.exp 1000 * F * r := add_le_add happ hclip
          _ = Bgood := by dsimp [Bgood]; ring
      have hbadInt : Integrable (goodProdᶜ.indicator (fun z => |err z|)) (μp.prod μe) :=
        herrInt.abs.indicator hgoodProdMeas.compl
      have hceInt := herrInt.integral_prod_left
      have hsplitPoint (pilot : Cell → ℕ) : |ce pilot| ≤
          Bgood + ∫ eval, goodProdᶜ.indicator (fun z => |err z|) (pilot, eval) ∂μe := by
        by_cases hp : pilot ∈ good
        · have hnonneg : 0 ≤ ∫ eval, goodProdᶜ.indicator (fun z => |err z|) (pilot, eval) ∂μe :=
            integral_nonneg fun eval => by
              by_cases hz : (pilot, eval) ∈ goodProdᶜ <;> simp [hz]
          linarith [hceGood pilot hp]
        · have hinner : Integrable (fun eval => err (pilot, eval)) μe := by
            apply (integrable_const (Afail * score pilot)).mono'
            · fun_prop
            · filter_upwards with eval
              rw [Real.norm_eq_abs]
              exact herrPoint (pilot, eval)
          have habs := abs_integral_le_integral_abs (μ := μe) (f := fun eval => err (pilot, eval))
          have hcomp : ∀ eval, goodProdᶜ.indicator (fun z => |err z|) (pilot, eval) =
              |err (pilot, eval)| := by intro eval; simp [goodProd, hp]
          simp_rw [hcomp]
          exact habs.trans (le_add_of_nonneg_left (by dsimp [Bgood]; positivity))
      have hceAbsInt : Integrable (fun pilot => |ce pilot|) μp := hceInt.abs
      have hrightInt : Integrable (fun pilot => Bgood +
          ∫ eval, goodProdᶜ.indicator (fun z => |err z|) (pilot, eval) ∂μe) μp :=
        (integrable_const Bgood).add hbadInt.integral_prod_left
      have hinter := integral_mono hceAbsInt hrightInt hsplitPoint
      have hmeanEq : cellStatisticExpectation canonicalJacksonTuning epsilon d m q hm - target =
          ∫ pilot, ce pilot ∂μp := by
        unfold cellStatisticExpectation pilotEvaluationLaw
        have hstatInt : Integrable stat (μp.prod μe) := by
          exact herrInt.add (integrable_const target) |>.congr
            (Filter.Eventually.of_forall fun z => by dsimp [err, stat, target]; ring)
        rw [show (∫ z, stat z ∂μp.prod μe) - target =
          ∫ z, err z ∂μp.prod μe by
            rw [show err = fun z => stat z - target by rfl,
              integral_sub hstatInt (integrable_const target), integral_const,
              probReal_univ, one_smul]]
        exact MeasureTheory.integral_prod err herrInt
      have hbadEq : (∫ z, goodProdᶜ.indicator (fun z => |err z|) z ∂μp.prod μe) =
          pilotFailureContribution canonicalJacksonTuning epsilon d m q hm := by
        unfold pilotFailureContribution pilotEvaluationLaw
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        by_cases hp : pilotGoodEvent canonicalJacksonTuning m d z.1 q <;>
          simp [goodProd, good, hp, err, stat, target]
      rw [hmeanEq]
      refine abs_integral_le_integral_abs.trans (hinter.trans ?_)
      calc
        (∫ pilot, Bgood + ∫ eval,
            goodProdᶜ.indicator (fun z => |err z|) (pilot, eval) ∂μe ∂μp) =
            Bgood + ∫ z, goodProdᶜ.indicator (fun z => |err z|) z ∂μp.prod μe := by
              rw [integral_add (integrable_const Bgood) hbadInt.integral_prod_left]
              simp only [integral_const, probReal_univ, one_smul]
              rw [← MeasureTheory.integral_prod _ hbadInt]
        _ = Bgood + pilotFailureContribution
            canonicalJacksonTuning epsilon d m q hm := by
              rw [hbadEq]
        _ ≤ _ := by
          dsimp [Bgood, r]
          exact le_rfl
    have hmseDecomp :
        ∫ z, err z ^ 2 ∂μp.prod μe ≤
          4 * Real.exp 1000 * d ^ (1 / 16 : ℝ) *
            (F * 2000000 * v) ^ 2 +
          pilotFailureSecondMomentContribution canonicalJacksonTuning epsilon d m q hm := by
      let Vgood := 4 * Real.exp 1000 * d ^ (1 / 16 : ℝ) * (F * 2000000 * v) ^ 2
      let goodProd : Set ((Cell → ℕ) × (Cell → ℕ)) := {z | z.1 ∈ good}
      have hgoodProdMeas : MeasurableSet goodProd :=
        hgoodMeas.preimage measurable_fst
      have hpoint (pilot : Cell → ℕ) :
          ∫ eval, err (pilot, eval) ^ 2 ∂μe ≤
            Vgood + ∫ eval, goodProdᶜ.indicator (fun z => err z ^ 2) (pilot, eval) ∂μe := by
        by_cases hp : pilot ∈ good
        · have hvb := canonicalGoodPilotConditionalMSE epsilon m hepsilon hm d hd
            pilot q hq hp
          have hS := canonicalPilotGoodRadiusSum_le m hm d hd pilot q hq hp
          have hfacS : F * (∑ j : Cell, rectangleRadius
              (pilotRectangle canonicalJacksonTuning m d pilot) j) ≤ F * 2000000 * v := by
            simpa [v, L, hsumq, mul_assoc] using mul_le_mul_of_nonneg_left hS (le_of_lt hF)
          have hvb' : (∫ eval, err (pilot, eval) ^ 2 ∂μe) ≤ Vgood := by
            have hleft : 0 ≤ F * (∑ j : Cell, rectangleRadius
                (pilotRectangle canonicalJacksonTuning m d pilot) j) := by
              apply mul_nonneg (le_of_lt hF)
              exact Finset.sum_nonneg fun j _ =>
                le_of_lt (pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd j)
            have hsquares := (sq_le_sq₀ hleft (by positivity)).2 hfacS
            exact hvb.trans (mul_le_mul_of_nonneg_left hsquares (by positivity))
          exact hvb'.trans (le_add_of_nonneg_right
              (integral_nonneg fun eval =>
              Set.indicator_nonneg (fun z _ => sq_nonneg (err z)) _))
        · have heq : ∀ eval, goodProdᶜ.indicator (fun z => err z ^ 2) (pilot, eval) =
              err (pilot, eval) ^ 2 := by intro eval; simp [goodProd, hp]
          simp_rw [heq]
          exact le_add_of_nonneg_left (by dsimp [Vgood]; positivity)
      have hbadSqInt : Integrable (goodProdᶜ.indicator (fun z => err z ^ 2)) (μp.prod μe) :=
        herrSqInt.indicator hgoodProdMeas.compl
      have hbadSqEq : (∫ z, goodProdᶜ.indicator (fun z => err z ^ 2) z ∂μp.prod μe) =
          pilotFailureSecondMomentContribution canonicalJacksonTuning epsilon d m q hm := by
        unfold pilotFailureSecondMomentContribution pilotEvaluationLaw
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        by_cases hp : pilotGoodEvent canonicalJacksonTuning m d z.1 q <;>
          simp [goodProd, good, hp, err, stat, target]
      calc
        (∫ z, err z ^ 2 ∂μp.prod μe) =
            ∫ pilot, ∫ eval, err (pilot, eval) ^ 2 ∂μe ∂μp :=
              MeasureTheory.integral_prod _ herrSqInt
        _ ≤ ∫ pilot, (Vgood + ∫ eval,
            goodProdᶜ.indicator (fun z => err z ^ 2) (pilot, eval) ∂μe) ∂μp := by
              exact integral_mono herrSqInt.integral_prod_left
                ((integrable_const Vgood).add hbadSqInt.integral_prod_left) hpoint
        _ = Vgood + pilotFailureSecondMomentContribution
            canonicalJacksonTuning epsilon d m q hm := by
              rw [integral_add, integral_const, probReal_univ, one_smul,
                ← MeasureTheory.integral_prod _ hbadSqInt]
              · rw [hbadSqEq]
              · exact integrable_const Vgood
              · exact hbadSqInt.integral_prod_left
        _ = _ := by rfl
    have hfail := canonicalPilotFailureBounds epsilon m hepsilon hm d hd q hq
    have hlogs := canonicalLogPowerBounds d hd
    have hbase : 0 ≤ cellMass P x * L / m + L ^ 2 / m ^ 2 := by positivity
    have hvSq : v ^ 2 ≤ 2 * (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
      have hsqrt : Real.sqrt (cellMass P x * L / m) ^ 2 = cellMass P x * L / m := by
        rw [Real.sq_sqrt]
        positivity
      have hfrac : (L / m) ^ 2 = L ^ 2 / m ^ 2 := by ring
      dsimp [v]
      rw [add_sq, hsqrt, hfrac]
      nlinarith [sq_nonneg (Real.sqrt (cellMass P x * L / m) - L / m)]
    have hbiasFinal : |cellStatisticExpectation canonicalJacksonTuning epsilon d m q hm - target| ≤
        Cepsilon * (Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)) := by
      let r := Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)
      have hlogs2 := canonicalLogSquaredPowerBounds d hd
      have hsqrtEq := hsqrtScaleEq
      have hL1 : 1 ≤ L := by
        dsimp [L, logAlphabet]
        rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
        linarith [Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d)]
      have hvle : v ≤ L ^ 2 * r := by
        dsimp [v, r]
        rw [hsqrtEq]
        have ha := Real.sqrt_nonneg (cellMass P x / (m * L))
        have hLa : L * Real.sqrt (cellMass P x / (m * L)) ≤
            L ^ 2 * Real.sqrt (cellMass P x / (m * L)) := by
          apply mul_le_mul_of_nonneg_right _ ha
          nlinarith
        have hfrac : L ^ 2 * (1 / (m * L)) = L / m := by
          field_simp [ne_of_gt hL, ne_of_gt hm]
        rw [mul_add, hfrac]
        linarith
      have hbadAbs : 2 * d ^ (1 / 4 : ℝ) * F * C1 *
          Real.exp (-20 * L) * v ≤ 450 * F * C1 * r := by
        have hcoef : 0 ≤ 2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L) := by
          positivity
        calc
          2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L) * v ≤
              (2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L)) *
                (L ^ 2 * r) := mul_le_mul_of_nonneg_left hvle hcoef
          _ = (L ^ 2 * d ^ (1 / 4 : ℝ) * Real.exp (-20 * L)) *
                (2 * F * C1 * r) := by ring
          _ ≤ 225 * (2 * F * C1 * r) := by
            exact mul_le_mul_of_nonneg_right (by simpa [L] using hlogs2.2) (by positivity)
          _ = 450 * F * C1 * r := by ring
      have hfail1 : pilotFailureContribution canonicalJacksonTuning epsilon d m q hm ≤
          450 * F * C1 * r := by
        exact hfail.1.trans (by simpa [L, F, v, r, hsumq] using hbadAbs)
      refine hbiasDecomp.trans (le_trans (add_le_add_right hfail1 _) ?_)
      have hr0 : 0 ≤ r := by dsimp [r]; positivity
      change (50000000000000000 * Cj + 450000000 * Real.exp 1000 * F) * r +
          450 * F * C1 * r ≤ Cepsilon * r
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ hr0
      dsimp [Cepsilon]
      have hterm1 : 0 ≤ 8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg 1000))
          (sq_nonneg F)) (sq_nonneg (2000000 : ℝ))
      have hterm2 : 0 ≤ 8 * F ^ 2 * C2 :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F)) (le_of_lt hC2)
      have hrest : 0 ≤ 1 + 8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 +
          8 * F ^ 2 * C2 := by linarith
      linarith
    have hmseFinal : (∫ z, err z ^ 2 ∂μp.prod μe) ≤
        Cepsilon * d ^ (1 / 16 : ℝ) *
          (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
      refine hmseDecomp.trans (le_trans (add_le_add_right hfail.2 _) ?_)
      have hbad2 := mul_le_mul_of_nonneg_right hlogs.2.2.2
        (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * F ^ 2) (le_of_lt hC2))
          (sq_nonneg v))
      have hvgood : 4 * Real.exp 1000 * (d : ℝ) ^ (1 / 16 : ℝ) *
          (F * 2000000 * v) ^ 2 ≤
          8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 *
            (d : ℝ) ^ (1 / 16 : ℝ) *
              (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
        have hc : 0 ≤ 4 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 *
            (d : ℝ) ^ (1 / 16 : ℝ) := by positivity
        calc
          4 * Real.exp 1000 * (d : ℝ) ^ (1 / 16 : ℝ) *
              (F * 2000000 * v) ^ 2 =
            (4 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 *
              (d : ℝ) ^ (1 / 16 : ℝ)) * v ^ 2 := by ring
          _ ≤ (4 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 *
              (d : ℝ) ^ (1 / 16 : ℝ)) *
                (2 * (cellMass P x * L / m + L ^ 2 / m ^ 2)) :=
                mul_le_mul_of_nonneg_left hvSq hc
          _ = _ := by ring
      have hbadFinal :
          (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)) ^ 2 * C2 *
              Real.exp (-20 * logAlphabet d) *
              (Real.sqrt ((∑ j : Cell, q j) * logAlphabet d / m) +
                logAlphabet d / m) ^ 2 ≤
            8 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) *
              (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
        calc
          (2 * d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹)) ^ 2 * C2 *
                Real.exp (-20 * logAlphabet d) *
                (Real.sqrt ((∑ j : Cell, q j) * logAlphabet d / m) +
                  logAlphabet d / m) ^ 2 =
              d ^ (1 / 2 : ℝ) * Real.exp (-20 * logAlphabet d) *
                (4 * F ^ 2 * C2 * v ^ 2) := by
                  have hdpow : ((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
                      d ^ (1 / 2 : ℝ) := by
                    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ d)]
                    norm_num
                  rw [mul_pow, mul_pow, hdpow, hsumq]
                  dsimp [F, v, L]
                  ring
          _ ≤ d ^ (1 / 16 : ℝ) * (4 * F ^ 2 * C2 * v ^ 2) := hbad2
          _ = (4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ)) * v ^ 2 := by ring
          _ ≤ (4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ)) *
              (2 * (cellMass P x * L / m + L ^ 2 / m ^ 2)) := by
                have hc : 0 ≤ 4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) := by
                  have h4F : 0 ≤ 4 * F ^ 2 :=
                    mul_nonneg (by norm_num) (sq_nonneg F)
                  have h4FC2 : 0 ≤ 4 * F ^ 2 * C2 :=
                    mul_nonneg h4F (le_of_lt hC2)
                  exact mul_nonneg h4FC2 (Real.rpow_nonneg (by positivity) _)
                exact mul_le_mul_of_nonneg_left hvSq hc
          _ = 8 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) *
              (cellMass P x * L / m + L ^ 2 / m ^ 2) := by ring
      refine (add_le_add hvgood hbadFinal).trans ?_
      have hcoef : 8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 +
          8 * F ^ 2 * C2 ≤ Cepsilon := by
        dsimp [Cepsilon]
        have hrest : 0 ≤ 1 + (50000000000000000 * Cj +
            450000000 * Real.exp 1000 * F) + 450 * F * C1 := by positivity
        linarith
      have hmult : 0 ≤ d ^ (1 / 16 : ℝ) *
          (cellMass P x * L / m + L ^ 2 / m ^ 2) :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) hbase
      calc
        8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 * d ^ (1 / 16 : ℝ) *
                (cellMass P x * L / m + L ^ 2 / m ^ 2) +
              8 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) *
                (cellMass P x * L / m + L ^ 2 / m ^ 2) =
            (8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 + 8 * F ^ 2 * C2) *
              (d ^ (1 / 16 : ℝ) *
                (cellMass P x * L / m + L ^ 2 / m ^ 2)) := by ring
        _ ≤ Cepsilon * (d ^ (1 / 16 : ℝ) *
              (cellMass P x * L / m + L ^ 2 / m ^ 2)) :=
          mul_le_mul_of_nonneg_right hcoef hmult
        _ = Cepsilon * d ^ (1 / 16 : ℝ) *
              (cellMass P x * L / m + L ^ 2 / m ^ 2) := by ring
    have hvar : cellStatisticVariance canonicalJacksonTuning epsilon d m q hm ≤
        ∫ z, err z ^ 2 ∂μp.prod μe := by
      unfold cellStatisticVariance cellStatisticExpectation pilotEvaluationLaw
      have hstatMeas : AEStronglyMeasurable stat (μp.prod μe) := by
        have ht := herrLp.aestronglyMeasurable.add_const target
        exact ht.congr (Filter.Eventually.of_forall fun z => by
          dsimp [err, stat, target]
          ring)
      rw [← variance_eq_integral hstatMeas.aemeasurable]
      have hv := variance_le_expectation_sq (μ := μp.prod μe)
        (X := err) herrLp.aestronglyMeasurable
      have hshift := variance_sub_const (μ := μp.prod μe)
        (X := stat) hstatMeas target
      dsimp [err] at hv
      rw [hshift] at hv
      exact hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [m, q, target, L, F] using hbiasFinal
    · exact hvar.trans (by simpa [q, L] using hmseFinal)
    · have hlogs2 := canonicalLogSquaredPowerBounds d hd
      let r := Real.sqrt (cellMass P x / (m * L)) + 1 / (m * L)
      have hvle : v ≤ L ^ 2 * r := by
        dsimp [v, r]
        rw [hsqrtScaleEq]
        have ha := Real.sqrt_nonneg (cellMass P x / (m * L))
        have hLa : L * Real.sqrt (cellMass P x / (m * L)) ≤
            L ^ 2 * Real.sqrt (cellMass P x / (m * L)) := by
          apply mul_le_mul_of_nonneg_right _ ha
          nlinarith [hL1]
        have hfrac : L ^ 2 * (1 / (m * L)) = L / m := by
          field_simp [ne_of_gt hL, ne_of_gt hm]
        rw [mul_add, hfrac]
        linarith
      have hbad : 2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L) * v ≤
          450 * F * C1 * r := by
        have hcoef : 0 ≤ 2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L) := by
          positivity
        calc
          2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L) * v ≤
              (2 * d ^ (1 / 4 : ℝ) * F * C1 * Real.exp (-20 * L)) *
                (L ^ 2 * r) := mul_le_mul_of_nonneg_left hvle hcoef
          _ = (L ^ 2 * d ^ (1 / 4 : ℝ) * Real.exp (-20 * L)) *
                (2 * F * C1 * r) := by ring
          _ ≤ 225 * (2 * F * C1 * r) :=
            mul_le_mul_of_nonneg_right (by simpa [L] using hlogs2.2) (by positivity)
          _ = 450 * F * C1 * r := by ring
      refine hfail.1.trans (by simpa [L, F, C1, v, r, hsumq] using hbad) |>.trans ?_
      have hr0 : 0 ≤ r := by dsimp [r]; positivity
      have hcoef : 450 * F * C1 ≤ Cepsilon := by
        dsimp [Cepsilon]
        have htermJ : 0 ≤ 50000000000000000 * Cj +
            450000000 * Real.exp 1000 * F := by positivity
        have htermV : 0 ≤ 8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg 1000))
            (sq_nonneg F)) (sq_nonneg (2000000 : ℝ))
        have htermB : 0 ≤ 8 * F ^ 2 * C2 :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F)) (le_of_lt hC2)
        linarith
      simpa [F, C1, r, L, m] using mul_le_mul_of_nonneg_right hcoef hr0
    · calc
        pilotFailureSecondMomentContribution canonicalJacksonTuning epsilon d m q hm ≤
            (2 * d ^ (1 / 4 : ℝ) * F) ^ 2 * C2 * Real.exp (-20 * L) * v ^ 2 := by
              simpa [L, F, C2, hsumq] using hfail.2
        _ = 4 * F ^ 2 * C2 *
            (d ^ (1 / 2 : ℝ) * Real.exp (-20 * L)) * v ^ 2 := by
              have hdpow : ((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
                  (d : ℝ) ^ (1 / 2 : ℝ) := by
                rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ d)]
                norm_num
              rw [mul_pow, mul_pow, hdpow]
              ring
        _ ≤ 4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) * v ^ 2 := by
              have hc : 0 ≤ 4 * F ^ 2 * C2 * v ^ 2 :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F))
                  (le_of_lt hC2)) (sq_nonneg v)
              calc
                4 * F ^ 2 * C2 *
                    (d ^ (1 / 2 : ℝ) * Real.exp (-20 * L)) * v ^ 2 =
                    (4 * F ^ 2 * C2 * v ^ 2) *
                      (d ^ (1 / 2 : ℝ) * Real.exp (-20 * L)) := by ring
                _ ≤ (4 * F ^ 2 * C2 * v ^ 2) * d ^ (1 / 16 : ℝ) :=
                  mul_le_mul_of_nonneg_left hlogs.2.2.2 hc
                _ = 4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) * v ^ 2 := by ring
        _ ≤ 8 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) *
            (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
              have hc : 0 ≤ 4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F))
                  (le_of_lt hC2)) (Real.rpow_nonneg (by positivity) _)
              calc
                4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) * v ^ 2 ≤
                    (4 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ)) *
                      (2 * (cellMass P x * L / m + L ^ 2 / m ^ 2)) :=
                        mul_le_mul_of_nonneg_left hvSq hc
                _ = 8 * F ^ 2 * C2 * d ^ (1 / 16 : ℝ) *
                    (cellMass P x * L / m + L ^ 2 / m ^ 2) := by ring
        _ ≤ Cepsilon * d ^ (1 / 16 : ℝ) *
            (cellMass P x * L / m + L ^ 2 / m ^ 2) := by
              have hcoef : 8 * F ^ 2 * C2 ≤ Cepsilon := by
                dsimp [Cepsilon]
                have hrest : 0 ≤ 1 + (50000000000000000 * Cj +
                    450000000 * Real.exp 1000 * F) + 450 * F * C1 +
                    8 * Real.exp 1000 * F ^ 2 * 2000000 ^ 2 := by positivity
                linarith
              have hmult : 0 ≤ d ^ (1 / 16 : ℝ) *
                  (cellMass P x * L / m + L ^ 2 / m ^ 2) :=
                mul_nonneg (Real.rpow_nonneg (by positivity) _) hbase
              simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hmult

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
