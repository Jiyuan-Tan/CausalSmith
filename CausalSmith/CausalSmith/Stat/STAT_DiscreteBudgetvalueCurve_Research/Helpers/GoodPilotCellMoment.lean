module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BVMaximal

/-! Deterministic target correction and full good-pilot cell moments. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Stat.Concentration.BoundedVariation
open Causalean.Stat.Concentration.Poisson

/-- The promoted measurability of total variation makes the paper's path-size
functional Borel measurable on the continuous-path space. [The stated relationship holds](goal). -/
-- @node: measurable_pathSize_run
lemma measurable_pathSize_run : Measurable (pathSize : Path → ℝ) := by
  letI : BorelSpace Path := ⟨rfl⟩
  unfold pathSize
  exact continuous_norm.measurable.add measurable_pathTV

/-- Adding a fixed continuous path preserves measurability of squared path
size for a measurable random path. With [the specified inputs and conditions](hyp:Omega,F,hF,g), [the stated relationship holds](goal). -/
-- @node: measurable_pathSize_sq_add_const
lemma measurable_pathSize_sq_add_const {Omega : Type*} [MeasurableSpace Omega]
    (F : Omega → Path) (hF : Measurable F) (g : Path) :
    Measurable (fun omega => pathSize (F omega + g) ^ 2) := by
  letI : BorelSpace Path := ⟨rfl⟩
  exact (measurable_pathSize_run.comp (hF.add measurable_const)).pow_const 2

/-- Path size is subadditive on bounded-variation paths. With [the specified inputs and conditions](hyp:f,g,hf,hg), [the stated relationship holds](goal). -/
-- @node: pathSize_add_le
lemma pathSize_add_le (f g : Path) (hf : eVariationOn f Set.univ < ⊤)
    (hg : eVariationOn g Set.univ < ⊤) :
    pathSize (f + g) ≤ pathSize f + pathSize g := by
  have hvarneg : eVariationOn (fun t => -g t) Set.univ =
      eVariationOn g Set.univ := by
    unfold eVariationOn
    congr 1 with p
    congr 1 with i
    show edist (-(g (p.2.1 (i + 1)))) (-(g (p.2.1 i))) =
      edist (g (p.2.1 (i + 1))) (g (p.2.1 i))
    exact edist_neg_neg (G := ℝ) _ _
  have hvarneg' : eVariationOn (-g) Set.univ = eVariationOn g Set.univ := by
    change eVariationOn (fun t => -g t) Set.univ = _
    exact hvarneg
  have hneg : eVariationOn (-g) Set.univ < ⊤ := by
    rw [hvarneg']
    exact hg
  have hsizeNeg : pathSize (-g) = pathSize g := by
    unfold pathSize pathTV
    rw [norm_neg, hvarneg']
  have h := pathSize_sub_le f (-g) hf hneg
  simpa only [sub_neg_eq_add, hsizeNeg] using h

/-- The deterministic threshold discrepancy between a pilot midpoint and the
true cell vector, viewed as a path on the threshold interval. -/
-- @node: idealGoodThresholdCorrectionPath
noncomputable def idealGoodThresholdCorrectionPath {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (pilot : Cell → ℕ) (j : Fin d) : Path :=
  ⟨fun lambda : Time =>
      thresholdFunReal epsilon lambda
          (pilotMidpoint ((n : ℝ) / 8) d pilot) -
        thresholdFunReal epsilon lambda (cellVector P j),
    (thresholdFunReal_continuous_time epsilon
      (pilotMidpoint ((n : ℝ) / 8) d pilot)).sub
      (thresholdFunReal_continuous_time epsilon (cellVector P j))⟩

/-- The deterministic threshold correction always has finite variation. With [the specified inputs and conditions](hyp:n,d,epsilon,P,pilot,j), [the stated relationship holds](goal). -/
-- @node: idealGoodThresholdCorrectionPath_bv
lemma idealGoodThresholdCorrectionPath_bv {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (pilot : Cell → ℕ) (j : Fin d) :
    eVariationOn (idealGoodThresholdCorrectionPath (n := n) epsilon P pilot j)
      Set.univ < ⊤ := by
  let u := pilotMidpoint ((n : ℝ) / 8) d pilot
  let v := cellVector P j
  have hlip := (thresholdFunReal_lipschitz_time epsilon u).sub
    (thresholdFunReal_lipschitz_time epsilon v)
  have hid : BoundedVariationOn (id : Time → Time) Set.univ := by
    have hm : Monotone (fun t : Time => (t : ℝ)) := fun s t hst => hst
    exact MonotoneOn.boundedVariationOn (hm.monotoneOn _)
      (fun t _ => abs_le.2 ⟨by linarith [t.property.1], t.property.2⟩)
  apply lt_top_iff_ne_top.mpr
  simpa [idealGoodThresholdCorrectionPath, u, v, BoundedVariationOn,
    Function.comp_def] using hlip.comp_boundedVariationOn hid

/-- On a good pilot cell, the deterministic target correction has path size
at most an epsilon-dependent constant times the sum of pilot radii. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: idealGoodThresholdCorrectionPath_size_le
lemma idealGoodThresholdCorrectionPath_size_le
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      ∀ (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d),
      idealPilotGood (n := n) P counts j →
      pathSize (idealGoodThresholdCorrectionPath (n := n) epsilon P (counts.1 j) j) ≤
        C * ∑ zeta : Cell,
          pilotRadius ((n : ℝ) / 8) d (counts.1 j) zeta := by
  obtain ⟨C₀, hC₀, hthreshold⟩ := thresholdFun_bv_lipschitz epsilon he he'
  refine ⟨2 * C₀ + 1, by linarith, ?_⟩
  intro n d hn hd P counts j hgood
  let u := pilotMidpoint ((n : ℝ) / 8) d (counts.1 j)
  let v := cellVector P j
  let f := idealGoodThresholdCorrectionPath (n := n) epsilon P (counts.1 j) j
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg this]
  have hu (zeta : Cell) : 0 ≤ u zeta := by
    dsimp [u, pilotMidpoint]
    have hlo : 0 ≤ pilotLower ((n : ℝ) / 8) d (counts.1 j) zeta :=
      le_max_left _ _
    have hup : 0 ≤ pilotUpper ((n : ℝ) / 8) d (counts.1 j) zeta := by
      unfold pilotUpper pilotCenter pilotHalfWidth pilotRadiusConstant
      positivity
    positivity
  have hv (zeta : Cell) : 0 ≤ v zeta := ENNReal.toReal_nonneg
  have hlip := (thresholdFunReal_lipschitz_time epsilon u).sub
    (thresholdFunReal_lipschitz_time epsilon v)
  have hid : BoundedVariationOn (id : Time → Time) Set.univ := by
    have hm : Monotone (fun t : Time => (t : ℝ)) := fun s t hst => hst
    exact MonotoneOn.boundedVariationOn (hm.monotoneOn _)
      (fun t _ => abs_le.2 ⟨by linarith [t.property.1], t.property.2⟩)
  have hfBV : eVariationOn f Set.univ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa [f, idealGoodThresholdCorrectionPath, u, v, BoundedVariationOn,
      Function.comp_def] using hlip.comp_boundedVariationOn hid
  have hbv := hthreshold u v hu hv
  have hdist : (∑ zeta : Cell, |u zeta - v zeta|) ≤
      ∑ zeta : Cell, pilotRadius ((n : ℝ) / 8) d (counts.1 j) zeta := by
    apply Finset.sum_le_sum
    intro zeta hzeta
    simpa [u, v, abs_sub_comm] using
      idealPilotGood_center_mem_radius hn P counts j hgood zeta
  have hbase := pathSize_le_two_endpointVariation f hfBV
  have heq : |f timeZero| + pathTV f =
      bvNorm (fun lambda => thresholdFunReal epsilon lambda u -
        thresholdFunReal epsilon lambda v) := by
    change |thresholdFunReal epsilon 0 u - thresholdFunReal epsilon 0 v| +
      (eVariationOn (fun lambda : Time =>
        thresholdFunReal epsilon lambda u - thresholdFunReal epsilon lambda v)
        Set.univ).toReal = _
    unfold bvNorm
    congr 1
    exact congrArg ENNReal.toReal (eVariationOn_time_eq_Icc
      (fun lambda : ℝ => thresholdFunReal epsilon lambda u -
        thresholdFunReal epsilon lambda v))
  rw [heq] at hbase
  have hCdist := (hbv.trans (mul_le_mul_of_nonneg_left hdist hC₀))
  have hS : 0 ≤ ∑ zeta : Cell,
      pilotRadius ((n : ℝ) / 8) d (counts.1 j) zeta :=
    Finset.sum_nonneg fun z _ =>
      (pilotRadius_pos_of_pos (by positivity) (show 1 ≤ d by omega)
        (counts.1 j) z).le
  nlinarith

/-- With a fixed good pilot table, the complete ideal cell-error path is the
sum of its factorial evaluation path and deterministic target correction. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,e,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealGoodCellErrorPath_eq_factorial_add_correction
lemma idealGoodCellErrorPath_eq_factorial_add_correction
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p e : (Fin d × Fin 4) → ℕ) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, curryCountTable e) j) :
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
      fun i table => poissonTableCell j table i
    let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
      (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
      (show 1 ≤ d by omega) pilot lambda
    idealPilotErrorCellPath epsilon P (curryCountTable p, curryCountTable e) j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P (curryCountTable p, curryCountTable e) j true) =
      localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
          (pilotMidpoint ((n : ℝ) / 8) d pilot)
          (pilotRadius ((n : ℝ) / 8) d pilot)
          (by unfold jacksonDegree; omega) hpull (le_refl _) W ((n : ℝ) / 8)
          ((d : ℝ) ^ (1 / 4 : ℝ) *
            ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta) e +
        idealGoodThresholdCorrectionPath (n := n) epsilon P pilot j := by
  dsimp only
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
    fun i table => poissonTableCell j table i
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
    (show 1 ≤ d by omega) pilot lambda
  ext lambda
  have hstat := jacksonCellStatistic_eq_localJacksonFourPoissonFactorialPath
    epsilon ((n : ℝ) / 8) d pilot W (by unfold jacksonDegree; omega) hpull e lambda
  have heval : (fun zeta => W (CellFourEquiv zeta) e) = curryCountTable e j := by
    funext zeta
    rfl
  rw [heval] at hstat
  change idealPilotErrorCell (n := n) epsilon lambda P
      (curryCountTable p, curryCountTable e) j true = _
  simp only [idealPilotErrorCell, hgood, if_pos, ContinuousMap.add_apply]
  change jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d pilot
      (curryCountTable e j) - thresholdFunReal epsilon lambda (cellVector P j) = _
  change _ = localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
      (pilotMidpoint ((n : ℝ) / 8) d pilot)
      (pilotRadius ((n : ℝ) / 8) d pilot) _ hpull _ W ((n : ℝ) / 8)
      _ e lambda + (thresholdFunReal epsilon lambda
        (pilotMidpoint ((n : ℝ) / 8) d pilot) -
          thresholdFunReal epsilon lambda (cellVector P j))
  linarith

/-- Pointwise on a good pilot cell, the complete ideal error path is bounded
by the factorial path size plus an epsilon-dependent radius-sum correction. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,p,e,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealGoodCellErrorPath_size_le
lemma idealGoodCellErrorPath_size_le
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (p e : (Fin d × Fin 4) → ℕ) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, curryCountTable e) j) :
    ∃ C : ℝ, 0 < C ∧
      let pilot := curryCountTable p j
      let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
        fun i table => poissonTableCell j table i
      let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
        (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
        (show 1 ≤ d by omega) pilot lambda
      pathSize (idealPilotErrorCellPath epsilon P
          (curryCountTable p, curryCountTable e) j true
          (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
            P (curryCountTable p, curryCountTable e) j true)) ≤
        pathSize (localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
          (pilotMidpoint ((n : ℝ) / 8) d pilot)
          (pilotRadius ((n : ℝ) / 8) d pilot)
          (by unfold jacksonDegree; omega) hpull (le_refl _) W ((n : ℝ) / 8)
          ((d : ℝ) ^ (1 / 4 : ℝ) *
            ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta) e) +
        C * ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta := by
  obtain ⟨C, hC, hcorr⟩ := idealGoodThresholdCorrectionPath_size_le
    epsilon he he'
  have hcorr := hcorr hn hd P (curryCountTable p, curryCountTable e) j hgood
  refine ⟨C, hC, ?_⟩
  dsimp only
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
    fun i table => poissonTableCell j table i
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
    (show 1 ≤ d by omega) pilot lambda
  let fact := localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
    (pilotMidpoint ((n : ℝ) / 8) d pilot)
    (pilotRadius ((n : ℝ) / 8) d pilot)
    (by unfold jacksonDegree; omega) hpull (le_refl _) W ((n : ℝ) / 8)
    ((d : ℝ) ^ (1 / 4 : ℝ) *
      ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta) e
  let corr := idealGoodThresholdCorrectionPath (n := n) epsilon P pilot j
  have hgood0 : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j := by
    simpa [idealPilotGood] using hgood
  have hpkg := goodPilot_localJacksonFourPoissonFactorialPath_sq_bound
    epsilon he hn hd P p j hgood0
  have hfactBV : eVariationOn fact Set.univ < ⊤ := by
    simpa [fact, pilot, W, hpull] using hpkg.2.1 e
  have hcorrBV : eVariationOn corr Set.univ < ⊤ := by
    exact idealGoodThresholdCorrectionPath_bv epsilon P pilot j
  have hadd := pathSize_add_le fact corr hfactBV hcorrBV
  have heq := idealGoodCellErrorPath_eq_factorial_add_correction
    epsilon he hn hd P p e j hgood
  rw [heq]
  have hc : pathSize fact + pathSize corr ≤ pathSize fact +
      C * ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta :=
    by
      have := add_le_add_right (by simpa [corr, pilot] using hcorr) (pathSize fact)
      simpa [add_comm] using this
  exact hadd.trans (by simpa [fact, pilot, W, hpull] using hc)

/-- Conditional on a fixed good pilot table, the full cell-error path has the
paper's equation (21) squared path-size scale. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: goodPilot_fullCellErrorPath_sq_integral_le
lemma goodPilot_fullCellErrorPath_sq_integral_le
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      ∀ (p : (Fin d × Fin 4) → ℕ) (j : Fin d),
      idealPilotGood (n := n) P (curryCountTable p, fun _ _ => 0) j →
      let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
        idealFlatRate (n := n) P iz.1 iz.2)
      Integrable (fun e => pathSize (idealPilotErrorCellPath epsilon P
          (curryCountTable p, curryCountTable e) j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P
            (curryCountTable p, curryCountTable e) j true)) ^ 2) mu ∧
      (∫ e, pathSize (idealPilotErrorCellPath epsilon P
          (curryCountTable p, curryCountTable e) j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P
            (curryCountTable p, curryCountTable e) j true)) ^ 2 ∂mu) ≤
        C * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∑ zeta : Cell,
            pilotRadius ((n : ℝ) / 8) d (curryCountTable p j) zeta) ^ 2 := by
  obtain ⟨Ccoef, hCcoef, hcoef⟩ := jacksonCoefficientBV_pilot_le epsilon he he'
  obtain ⟨Cc, hCc, hcorrAll⟩ := idealGoodThresholdCorrectionPath_size_le
    epsilon he he'
  let Cf : ℝ := 4 * Ccoef ^ 2 * Real.exp 123
  refine ⟨2 * Cf + 2 * Cc ^ 2, by dsimp [Cf]; positivity, ?_⟩
  intro n d hn hd P p j hgood
  let m : ℝ := (n : ℝ) / 8
  let pilot := curryCountTable p j
  let S : ℝ := ∑ zeta : Cell, pilotRadius m d pilot zeta
  let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
    fun i table => poissonTableCell j table i
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := m) he (by positivity)
    (show 1 ≤ d by omega) pilot lambda
  let fact : ((Fin d × Fin 4) → ℕ) → Path := fun e =>
    localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
      (pilotMidpoint m d pilot) (pilotRadius m d pilot)
      (by unfold jacksonDegree; omega) hpull (le_refl _) W m
      ((d : ℝ) ^ (1 / 4 : ℝ) * S) e
  let corr : Path := idealGoodThresholdCorrectionPath (n := n) epsilon P pilot j
  let err : ((Fin d × Fin 4) → ℕ) → Path := fun e =>
    idealPilotErrorCellPath epsilon P (curryCountTable p, curryCountTable e) j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
        P (curryCountTable p, curryCountTable e) j true)
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
    idealFlatRate (n := n) P iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  have hfactBound := goodPilot_localJacksonFourPoissonFactorialPath_sq_integral_le
    epsilon he hn hd P p j hgood Ccoef hCcoef.le
      (hcoef ((n : ℝ) / 8) (by positivity) d (by omega)
        (curryCountTable p j))
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hgood0 : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j := hgood
  have hcorrBound := hcorrAll hn hd P
    (curryCountTable p, fun _ _ => 0) j hgood0
  have hpkg := goodPilot_localJacksonFourPoissonFactorialPath_sq_bound
    epsilon he hn hd P p j hgood
  have hfactMeas : Measurable fact := by
    simpa [fact, m, pilot, S, W, hpull, mu] using hpkg.1
  have hfactBV (e) : eVariationOn (fact e) Set.univ < ⊤ := by
    simpa [fact, m, pilot, S, W, hpull, mu] using hpkg.2.1 e
  have hfactInt : Integrable (fun e => pathSize (fact e) ^ 2) mu := by
    simpa [fact, m, pilot, S, W, hpull, mu] using hpkg.2.2
  have hcorrBV : eVariationOn corr Set.univ < ⊤ := by
    exact idealGoodThresholdCorrectionPath_bv epsilon P pilot j
  have hcorrSize : pathSize corr ≤ Cc * S := by
    simpa [corr, S, m, pilot] using hcorrBound
  have herrEq (e) : err e = fact e + corr := by
    simpa [err, fact, corr, m, pilot, S, W, hpull] using
      (idealGoodCellErrorPath_eq_factorial_add_correction
        epsilon he hn hd P p e j (by simpa [idealPilotGood] using hgood))
  have herrMeas : Measurable err := by
    letI : BorelSpace Path := ⟨rfl⟩
    rw [show err = fun e => fact e + corr by
      funext e
      exact herrEq e]
    exact hfactMeas.add measurable_const
  have herrSqMeas : Measurable (fun e => pathSize (err e) ^ 2) :=
    (measurable_pathSize_run.comp herrMeas).pow_const 2
  have hpoint (e) : pathSize (err e) ^ 2 ≤
      2 * pathSize (fact e) ^ 2 + 2 * (Cc * S) ^ 2 := by
    have hsize : pathSize (err e) ≤ pathSize (fact e) + Cc * S := by
      rw [herrEq]
      exact (pathSize_add_le (fact e) corr (hfactBV e) hcorrBV).trans
        (add_le_add_right hcorrSize _)
    have hnonneg : 0 ≤ pathSize (err e) := pathSize_nonneg _
    have hright : 0 ≤ pathSize (fact e) + Cc * S := hnonneg.trans hsize
    have hsquare : pathSize (err e) ^ 2 ≤
        (pathSize (fact e) + Cc * S) ^ 2 :=
      (sq_le_sq₀ hnonneg hright).2 hsize
    nlinarith [sq_nonneg (pathSize (fact e) - Cc * S),
      hsquare]
  have henvInt : Integrable
      (fun e => 2 * pathSize (fact e) ^ 2 + 2 * (Cc * S) ^ 2) mu :=
    (hfactInt.const_mul 2).add (integrable_const _)
  have herrInt : Integrable (fun e => pathSize (err e) ^ 2) mu := by
    apply henvInt.mono' herrSqMeas.aestronglyMeasurable
    filter_upwards [] with e
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint e
  refine ⟨by simpa [err] using herrInt, ?_⟩
  change (∫ e, pathSize (err e) ^ 2 ∂mu) ≤
    (2 * Cf + 2 * Cc ^ 2) * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2
  have hint := integral_mono herrInt henvInt hpoint
  have hfactBound' : (∫ e, pathSize (fact e) ^ 2 ∂mu) ≤
      Cf * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2 := by
    simpa [fact, m, pilot, S, W, hpull, mu] using hfactBound
  have hdpow : 1 ≤ (d : ℝ) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
  calc
    (∫ e, pathSize (err e) ^ 2 ∂mu) ≤
        ∫ e, (2 * pathSize (fact e) ^ 2 + 2 * (Cc * S) ^ 2) ∂mu := hint
    _ = 2 * (∫ e, pathSize (fact e) ^ 2 ∂mu) + 2 * (Cc * S) ^ 2 := by
      rw [integral_add, integral_const_mul, integral_const,
        probReal_univ, one_smul]
      · exact hfactInt.const_mul 2
      · exact integrable_const _
    _ ≤ 2 * (Cf * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2) +
        2 * (Cc * S) ^ 2 := by gcongr
    _ ≤ (2 * Cf + 2 * Cc ^ 2) * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2 := by
      have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
      nlinarith [mul_le_mul_of_nonneg_right hdpow (sq_nonneg Cc)]

end CausalSmith.Stat.DiscreteBudgetvalueCurve
