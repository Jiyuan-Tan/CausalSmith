module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Causalean.Stat.Nonparametric.HistogramRegression.CubicalRisk
public import Mathlib.MeasureTheory.Function.Floor

/-! # Pilot histogram risk -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 : ℝ}

open MeasureTheory

open Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

/-- Every coordinate of the histogram cell index is measurable. -/
-- @node: histogramCell_coord_measurable
@[fun_prop]
lemma histogramCell_coord_measurable (m d : ℕ) (β : ℝ) (i : Fin d) :
    Measurable (fun x : XSpace d => histogramCell m d β x i) := by
  unfold histogramCell
  fun_prop

/-- The full histogram cell index is measurable. -/
-- @node: histogramCell_measurable
@[fun_prop]
lemma histogramCell_measurable (m d : ℕ) (β : ℝ) :
    Measurable (histogramCell m d β) := by
  rw [measurable_pi_iff]
  exact histogramCell_coord_measurable m d β

/-- The histogram score is jointly measurable in the pilot sample and target covariate. -/
-- @node: histogramScore_measurable
@[fun_prop]
lemma histogramScore_measurable (m d : ℕ) (β : ℝ) :
    Measurable (fun z : PilotSample m d × XSpace d => histogramScore β z.1 z.2) := by
  let same : PilotSample m d × XSpace d → Fin m → Prop :=
    fun z r => histogramCell m d β (z.1 r).1 = histogramCell m d β z.2
  have hsame (r : Fin m) : MeasurableSet {z | same z r} := by
    exact measurableSet_eq_fun
      ((histogramCell_measurable m d β).comp (by fun_prop))
      ((histogramCell_measurable m d β).comp measurable_snd)
  let count : PilotSample m d × XSpace d → ℕ :=
    fun z => ∑ r : Fin m, if same z r then 1 else 0
  let total : PilotSample m d × XSpace d → ℝ :=
    fun z => ∑ r : Fin m, if same z r then (z.1 r).2.2 else 0
  have hcount : Measurable count := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (hsame r) measurable_const measurable_const
  have htotal : Measurable total := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (hsame r) (by fun_prop) measurable_const
  have hformula :
      (fun z : PilotSample m d × XSpace d => histogramScore β z.1 z.2) =
        fun z => if count z = 0 then 1 / 2 else clip01 (total z / count z) := by
    funext z
    simp only [histogramScore]
    rw [show count z = ((Finset.univ : Finset (Fin m)).filter
        (fun r => histogramCell m d β (z.1 r).1 = histogramCell m d β z.2)).card by
      simp [count, same]]
    rw [show total z = ∑ r ∈ (Finset.univ : Finset (Fin m)).filter
        (fun r => histogramCell m d β (z.1 r).1 = histogramCell m d β z.2),
          (z.1 r).2.2 by
      simp only [total, same]
      rw [Finset.sum_filter]]
  rw [hformula]
  apply Measurable.ite (measurableSet_eq_fun hcount measurable_const)
  · fun_prop
  · unfold clip01
    fun_prop

-- @node: clip01_sq_error_le
lemma clip01_sq_error_le (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (clip01 t - y) ^ 2 ≤ (t - y) ^ 2 := by
  unfold clip01
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · simp [max_eq_right ht0, min_eq_right ht1]
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      simp [max_eq_right ht0, min_eq_left ht1']
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1') (sub_nonneg.mpr hy1)]
  · have ht0' : t ≤ 0 := le_of_not_ge ht0
    simp [max_eq_left ht0']
    nlinarith [mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (neg_nonneg.mpr ht0'))]

-- @node: histogram_empty_cell_probability_bound
lemma histogram_empty_cell_probability_bound (m : ℕ) (p : ℝ)
    (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) ^ m ≤ 1 / (m + 1 : ℝ) := by
  have hq : 0 ≤ 1 - p := by linarith
  have hmain : ∀ n : ℕ, (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpow : 0 ≤ (1 - p) ^ n := pow_nonneg hq _
      have hstep :
          (1 - p) * (1 + ((n + 1 : ℕ) : ℝ) * p) ≤
            1 + (n : ℝ) * p := by
        push_cast
        nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg p)]
      calc
        (1 - p) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℝ) * p) =
            (1 - p) ^ n * ((1 - p) * (1 + ((n + 1 : ℕ) : ℝ) * p)) := by
              rw [pow_succ]
              ring
        _ ≤ (1 - p) ^ n * (1 + (n : ℝ) * p) :=
          mul_le_mul_of_nonneg_left hstep hpow
        _ ≤ 1 := ih
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hmpos).2
  have hpow : 0 ≤ (1 - p) ^ m := pow_nonneg hq _
  have hfactor : ((m : ℝ) + 1) * p ≤ 1 + (m : ℝ) * p := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hfactor hpow, hmain m]

/-- The coordinatewise clamp supplies a measurable totalized cube covariate. -/
-- @node: pilotCubeClamp
@[no_expose]
def pilotCubeClamp (x : XSpace d) : Cube d :=
  ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩

/-- Clamping fixes every covariate already in the unit cube. -/
-- @node: pilotCubeClamp_eq
lemma pilotCubeClamp_eq (x : XSpace d) (hx : x ∈ cube d) :
    (pilotCubeClamp x).val.ofLp = x := by
  funext i
  simp [pilotCubeClamp, max_eq_right (hx i).1, min_eq_right (hx i).2]

/-- The paper's bin count is the substrate mesh count at its optimized bandwidth. -/
-- @node: histogramBins_eq_meshCount
lemma histogramBins_eq_meshCount (m d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hm : 1 ≤ m) :
    histogramBins m d beta = meshCount (optimizedBandwidth d beta m) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hden : 0 < 2 * beta + (d : ℝ) := by positivity
  have hinv : (optimizedBandwidth d beta m)⁻¹ =
      (m : ℝ) ^ (1 / (2 * beta + d)) := by
    unfold optimizedBandwidth
    rw [← Real.rpow_neg hmpos.le]
    congr 1
    ring
  simp [histogramBins, meshCount, hinv]

/-- The paper's score restricted to the cube has the substrate's metric Hölder bound. -/
-- @node: paperCubeScore_holder
lemma paperCubeScore_holder (g : XSpace d → ℝ) (hholder : HolderScore g L β) :
    ∀ x y : Cube d,
      |g x.val.ofLp - g y.val.ofLp| ≤ L * (dist x y) ^ β := by
  intro x y
  have hx : x.val.ofLp ∈ cube d := x.property
  have hy : y.val.ofLp ∈ cube d := y.property
  have hdist : euclideanDistance x.val.ofLp y.val.ofLp = dist x y := by
    change Real.sqrt (∑ i, (x.val.ofLp i - y.val.ofLp i) ^ 2) = dist x.val y.val
    rw [EuclideanSpace.dist_eq]
    congr 2
    funext i
    rw [Real.dist_eq, sq_abs]
  rw [← hdist]
  exact hholder x.val.ofLp hx y.val.ofLp hy

/-- A positive-exponent Hölder paper score is measurable on the cube. -/
-- @node: measurable_paperCubeScore
lemma measurable_paperCubeScore (g : XSpace d → ℝ) (hL : 0 < L) (hβ : 0 < β)
    (hholder : HolderScore g L β) :
    Measurable (fun x : Cube d => g x.val.ofLp) := by
  apply Continuous.measurable
  rw [continuous_iff_continuousAt]
  intro x
  change Filter.Tendsto (fun y : Cube d => g y.val.ofLp) (nhds x) (nhds (g x.val.ofLp))
  rw [tendsto_iff_dist_tendsto_zero]
  have ht : Filter.Tendsto (fun y : Cube d => L * (dist y x) ^ β) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun y : Cube d => L * (dist y x) ^ β) x := by
      exact continuousAt_const.mul
        ((continuousAt_id.dist continuousAt_const).rpow_const (.inr hβ.le))
    convert hc.tendsto using 1
    simp [hβ.ne']
  refine squeeze_zero' (Filter.Eventually.of_forall fun y => dist_nonneg) ?_ ht
  exact Filter.Eventually.of_forall fun y => by
    simpa [Real.dist_eq, abs_sub_comm] using paperCubeScore_holder g hholder y x

/-- The fair treatment coin has total mass one. -/
-- @node: histogram_fairCoin_probability
lemma histogram_fairCoin_probability : IsProbabilityMeasure fairCoin := by
  constructor
  simpa [fairCoin] using ENNReal.inv_two_add_inv_two

/-- Covariates from a regular score model lie in the paper cube almost surely. -/
-- @node: regularScore_covariate_mem_cube_ae
lemma regularScore_covariate_mem_cube_ae (P : Measure (UnitRecord d))
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ∀ᵐ u ∂P, u.1 ∈ cube d := by
  have hcube : MeasurableSet (cube d) := by
    unfold cube
    measurability
  have hm : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube d := by
    change cube d ∈ ae (P.map Prod.fst)
    rw [mem_ae_iff]
    apply hmodel.covariate_density.2.1
    simp [cubeMeasure, hcube]
  exact ae_of_ae_map measurable_fst.aemeasurable hm

/-- Under a fair independent treatment coin, the observed response has conditional
mean equal to the paper's half-sum regression, expressed on the totalized cube. -/
-- @node: latentPilot_conditionalMean
lemma latentPilot_conditionalMean (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ConditionalMean (P.prod fairCoin)
      (fun ua => pilotCubeClamp ua.1.1)
      (fun ua => if ua.2 then ua.1.2.2 else ua.1.2.1)
      (fun x => g x.val.ofLp) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure fairCoin := histogram_fairCoin_probability
  let Y : UnitRecord d × Bool → ℝ :=
    fun ua => if ua.2 then ua.1.2.2 else ua.1.2.1
  let X : UnitRecord d × Bool → Cube d := fun ua => pilotCubeClamp ua.1.1
  let gc : Cube d → ℝ := fun x => g x.val.ofLp
  have hYmeas : Measurable Y := by
    dsimp [Y]
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton true)
    · fun_prop
    · fun_prop
  have hYbound : ∀ᵐ ua ∂P.prod fairCoin, Y ua ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmodel.bounded_outcomes] with u hu
    filter_upwards [] with a
    cases a with
    | false => simpa [Y] using hu.1
    | true => simpa [Y] using hu.2
  have hYint : Integrable Y (P.prod fairCoin) := by
    refine (integrable_const (1 : ℝ)).mono' hYmeas.aestronglyMeasurable ?_
    filter_upwards [hYbound] with ua hua
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hua.1], by linarith [hua.2]⟩
  have hXcube := regularScore_covariate_mem_cube_ae P hmodel
  have hgcP : Integrable (fun u : UnitRecord d => gc (pilotCubeClamp u.1)) P := by
    have hreg0 : Integrable (regression0 P) P := integrable_condExp
    have hreg1 : Integrable (regression1 P) P := integrable_condExp
    have havg : Integrable (fun u => (regression1 P u + regression0 P u) / 2) P :=
      (hreg1.add hreg0).div_const 2
    have hgraw : Integrable (fun u : UnitRecord d => g u.1) P := by
      exact havg.congr (Filter.EventuallyEq.symm hmodel.half_sum_version)
    refine hgraw.congr ?_
    filter_upwards [hXcube] with u hu
    simp [gc, pilotCubeClamp_eq u.1 hu]
  refine ⟨hYint, hgcP.comp_fst fairCoin, ?_⟩
  intro s hs
  let T : Set (XSpace d) := pilotCubeClamp ⁻¹' s
  let S : Set (UnitRecord d) := Prod.fst ⁻¹' T
  have hclamp : Measurable (pilotCubeClamp (d := d)) := by
    unfold pilotCubeClamp
    fun_prop
  have hT : MeasurableSet T := hs.preimage hclamp
  have hS : MeasurableSet S := hT.preimage measurable_fst
  have hpre : X ⁻¹' s = S ×ˢ (Set.univ : Set Bool) := by
    ext ua
    simp [X, S, T]
  have hcoin (u : UnitRecord d) :
      (∫ a, Y (u, a) ∂fairCoin) = (u.2.2 + u.2.1) / 2 := by
    have hifalse : Integrable (fun a => Y (u, a)) (Measure.dirac false) := by
      simp [Y]
    have hitrue : Integrable (fun a => Y (u, a)) (Measure.dirac true) := by
      simp [Y]
    rw [fairCoin, integral_add_measure
        (hifalse.smul_measure (by norm_num)) (hitrue.smul_measure (by norm_num)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    norm_num [Y, ENNReal.toReal_inv]
    ring
  have hleft :
      (∫ ua in X ⁻¹' s, Y ua ∂P.prod fairCoin) =
        ∫ u in S, (u.2.2 + u.2.1) / 2 ∂P := by
    rw [hpre, setIntegral_prod Y hYint.integrableOn]
    apply setIntegral_congr_fun hS
    intro u _
    change (∫ y in (Set.univ : Set Bool), Y (u, y) ∂fairCoin) = _
    simp only [setIntegral_univ]
    exact hcoin u
  have hright :
      (∫ ua in X ⁻¹' s, gc (X ua) ∂P.prod fairCoin) =
        ∫ u in S, gc (pilotCubeClamp u.1) ∂P := by
    rw [hpre, setIntegral_prod (fun ua => gc (X ua))
      (hgcP.comp_fst fairCoin).integrableOn]
    apply setIntegral_congr_fun hS
    intro u _
    change (∫ y in (Set.univ : Set Bool), gc (X (u, y)) ∂fairCoin) = _
    simp only [setIntegral_univ]
    change (∫ _ : Bool, gc (pilotCubeClamp u.1) ∂fairCoin) = _
    rw [integral_const]
    have hmass : fairCoin.real Set.univ = 1 := by
      simpa [Measure.real] using congrArg ENNReal.toReal
        (show fairCoin Set.univ = 1 from measure_univ)
    rw [hmass, one_smul]
  have hY0 : Integrable (fun u : UnitRecord d => u.2.1) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmodel.bounded_outcomes] with u hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
  have hY1 : Integrable (fun u : UnitRecord d => u.2.2) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmodel.bounded_outcomes] with u hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩
  have hScomap : MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] S :=
    ⟨T, hT, rfl⟩
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace (UnitRecord d)) := measurable_fst.comap_le
  have hreg0 : (∫ u in S, regression0 P u ∂P) = ∫ u in S, u.2.1 ∂P := by
    exact setIntegral_condExp hm hY0 hScomap
  have hreg1 : (∫ u in S, regression1 P u ∂P) = ∫ u in S, u.2.2 ∂P := by
    exact setIntegral_condExp hm hY1 hScomap
  have havg :
      (∫ u in S, (u.2.2 + u.2.1) / 2 ∂P) =
        ∫ u in S, (regression1 P u + regression0 P u) / 2 ∂P := by
    calc
      _ = ((∫ u in S, u.2.2 ∂P) + ∫ u in S, u.2.1 ∂P) / 2 := by
        rw [integral_div, integral_add hY1.integrableOn hY0.integrableOn]
      _ = ((∫ u in S, regression1 P u ∂P) +
          ∫ u in S, regression0 P u ∂P) / 2 := by rw [hreg1, hreg0]
      _ = _ := by
        rw [integral_div]
        congr 1
        exact (integral_add integrable_condExp.integrableOn
          integrable_condExp.integrableOn).symm
  have hscore :
      (∫ u in S, (regression1 P u + regression0 P u) / 2 ∂P) =
        ∫ u in S, g u.1 ∂P := by
    exact integral_congr_ae (ae_restrict_of_ae
      (Filter.EventuallyEq.symm hmodel.half_sum_version))
  have hclamp_score : (∫ u in S, g u.1 ∂P) =
      ∫ u in S, gc (pilotCubeClamp u.1) ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hXcube] with u hu
    simp [gc, pilotCubeClamp_eq u.1 hu]
  rw [hleft, hright, havg, hscore, hclamp_score]

/-- The two clipping conventions used by the paper and substrate coincide. -/
-- @node: substrate_clip_eq_clip01
lemma substrate_clip_eq_clip01 (t : ℝ) : clip t = clip01 t := by
  unfold clip clip01
  rcases le_total t 0 with ht | ht
  · simp only [min_eq_right (ht.trans zero_le_one), max_eq_left ht,
      min_eq_right zero_le_one]
  · rcases le_total t 1 with ht1 | ht1
    · simp [max_eq_right ht, min_eq_right ht1]
    · simp [min_eq_left ht1, max_eq_right (zero_le_one.trans ht1)]

/-- On supported covariates, substrate cube labels have the paper histogram-cell values. -/
-- @node: cubeLabel_val_eq_histogramCell
lemma cubeLabel_val_eq_histogramCell (m d : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m) (x : XSpace d) (hx : x ∈ cube d) :
    (fun i => (cubeLabel (optimizedBandwidth d beta m) (pilotCubeClamp x) i).val) =
      histogramCell m d beta x := by
  funext i
  simp [cubeLabel, histogramCell, histogramBins_eq_meshCount m d beta hbeta hm,
    pilotCubeClamp_eq x hx, min_comm]

/-- The substrate histogram on latent unit/coin observations is exactly the paper estimator. -/
-- @node: latent_histogram_eq_histogramScore
lemma latent_histogram_eq_histogramScore (m d : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m)
    (z : Fin m → UnitRecord d × Bool) (x : XSpace d)
    (hz : ∀ r, (z r).1.1 ∈ cube d) (hx : x ∈ cube d) :
    histogram (cubeLabel (optimizedBandwidth d beta m))
        (fun ua : UnitRecord d × Bool => pilotCubeClamp ua.1.1)
        (fun ua => if ua.2 then ua.1.2.2 else ua.1.2.1) (1 / 2) z
        (pilotCubeClamp x) =
      histogramScore beta (fun r => observedPilot (z r).1 (z r).2) x := by
  classical
  have hcell (r : Fin m) :
      (cubeLabel (optimizedBandwidth d beta m) (pilotCubeClamp (z r).1.1) =
        cubeLabel (optimizedBandwidth d beta m) (pilotCubeClamp x)) ↔
      histogramCell m d beta (z r).1.1 = histogramCell m d beta x := by
    constructor <;> intro h
    · simpa [cubeLabel_val_eq_histogramCell m d beta hbeta hm (z r).1.1 (hz r),
          cubeLabel_val_eq_histogramCell m d beta hbeta hm x hx] using
        congrArg (fun f => fun i => (f i).val) h
    · funext i
      apply Fin.ext
      exact (congrFun (cubeLabel_val_eq_histogramCell m d beta hbeta hm
        (z r).1.1 (hz r)) i).trans ((congrFun h i).trans
          (congrFun (cubeLabel_val_eq_histogramCell m d beta hbeta hm x hx) i).symm)
  unfold histogram histogramScore cellEstimate cellCount cellSum observedPilot
  simp only [hcell]
  split_ifs with hempty
  · rfl
  · rw [substrate_clip_eq_clip01]
    simp [Finset.sum_filter]

/-- On cube-supported observed pilot samples, the substrate estimator is the
paper histogram score. -/
-- @node: pilot_histogram_eq_histogramScore
lemma pilot_histogram_eq_histogramScore (m d : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m) (p : PilotSample m d) (x : XSpace d)
    (hp : ∀ r, (p r).1 ∈ cube d) (hx : x ∈ cube d) :
    histogram (cubeLabel (optimizedBandwidth d beta m))
        (fun v : PilotRecord d => pilotCubeClamp v.1) (fun v => v.2.2)
        (1 / 2) p (pilotCubeClamp x) = histogramScore beta p x := by
  let z : Fin m → UnitRecord d × Bool := fun r =>
    (((p r).1, (p r).2.2, (p r).2.2), (p r).2.1)
  simpa [histogram, cellEstimate, cellCount, cellSum, z, observedPilot] using
    latent_histogram_eq_histogramScore m d beta hbeta hm z x hp hx

/-- The observed pilot law inherits the cube conditional mean from the latent
unit/coin product law. -/
-- @node: pilotUnitLaw_conditionalMean
lemma pilotUnitLaw_conditionalMean (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ConditionalMean (pilotUnitLaw P)
      (fun v : PilotRecord d => pilotCubeClamp v.1) (fun v => v.2.2)
      (fun x => g x.val.ofLp) := by
  let phi : UnitRecord d × Bool → PilotRecord d := fun ua => observedPilot ua.1 ua.2
  let Xp : PilotRecord d → Cube d := fun v => pilotCubeClamp v.1
  let Yp : PilotRecord d → ℝ := fun v => v.2.2
  let gc : Cube d → ℝ := fun x => g x.val.ofLp
  have hphi : Measurable phi := by
    dsimp [phi, observedPilot]
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton true)
    · fun_prop
    · fun_prop
  have hXp : Measurable Xp := by
    dsimp [Xp]
    unfold pilotCubeClamp
    fun_prop
  have hYp : Measurable Yp := by fun_prop
  have hgc : Measurable gc := measurable_paperCubeScore g
    hmodel.parameters.2.2.2.1 hmodel.parameters.2.1 hmodel.holder_score
  have hlatent := latentPilot_conditionalMean P g hmodel
  have hlaw : pilotUnitLaw P = (P.prod fairCoin).map phi := by
    rfl
  rw [hlaw]
  have hYint : Integrable Yp ((P.prod fairCoin).map phi) :=
    (integrable_map_measure hYp.aestronglyMeasurable hphi.aemeasurable).2 hlatent.1
  have hgint : Integrable (fun v => gc (Xp v)) ((P.prod fairCoin).map phi) :=
    (integrable_map_measure (hgc.comp hXp).aestronglyMeasurable hphi.aemeasurable).2
      hlatent.2.1
  refine ⟨hYint, hgint, ?_⟩
  intro s hs
  change (∫ v in Xp ⁻¹' s, Yp v ∂(P.prod fairCoin).map phi) =
    ∫ v in Xp ⁻¹' s, gc (Xp v) ∂(P.prod fairCoin).map phi
  have hpre : phi ⁻¹' (Xp ⁻¹' s) =
      (fun ua : UnitRecord d × Bool => pilotCubeClamp ua.1.1) ⁻¹' s := by
    rfl
  calc
    _ = ∫ ua in phi ⁻¹' (Xp ⁻¹' s), Yp (phi ua) ∂P.prod fairCoin :=
      setIntegral_map (hs.preimage hXp) hYp.aestronglyMeasurable hphi.aemeasurable
    _ = ∫ ua in phi ⁻¹' (Xp ⁻¹' s), gc (Xp (phi ua)) ∂P.prod fairCoin := by
      rw [hpre]
      simpa [phi, Xp, Yp, gc, observedPilot] using hlatent.2.2 s hs
    _ = _ := (setIntegral_map (hs.preimage hXp) (hgc.comp hXp).aestronglyMeasurable
      hphi.aemeasurable).symm

/-- Observing a latent unit under its treatment coin is measurable. -/
-- @node: measurable_observedPilot_pair
lemma measurable_observedPilot_pair : Measurable
    (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
  unfold observedPilot
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.ite
  · exact measurable_snd (measurableSet_singleton true)
  · fun_prop
  · fun_prop

/-- The observed one-pilot law is a probability law whenever the unit law is. -/
-- @node: histogram_pilotUnitLaw_probability
lemma histogram_pilotUnitLaw_probability (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P) : IsProbabilityMeasure (pilotUnitLaw P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure fairCoin := histogram_fairCoin_probability
  unfold pilotUnitLaw
  exact Measure.isProbabilityMeasure_map measurable_observedPilot_pair.aemeasurable

/-- Regular-model pilot covariates remain cube-supported after observation. -/
-- @node: pilotUnitLaw_covariate_mem_cube_ae
lemma pilotUnitLaw_covariate_mem_cube_ae (P : Measure (UnitRecord d))
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ∀ᵐ v ∂pilotUnitLaw P, v.1 ∈ cube d := by
  have hset : MeasurableSet {v : PilotRecord d | v.1 ∈ cube d} := by
    unfold cube
    measurability
  unfold pilotUnitLaw
  change ∀ᵐ v ∂(P.prod fairCoin).map (fun ua => observedPilot ua.1 ua.2),
    v ∈ {v : PilotRecord d | v.1 ∈ cube d}
  apply (ae_map_iff (μ := P.prod fairCoin)
    (f := fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2)
    measurable_observedPilot_pair.aemeasurable hset).2
  change ∀ᵐ ua ∂P.prod fairCoin,
    observedPilot ua.1 ua.2 ∈ {v : PilotRecord d | v.1 ∈ cube d}
  rw [Measure.ae_prod_iff_ae_ae (hset.preimage measurable_observedPilot_pair)]
  filter_upwards [regularScore_covariate_mem_cube_ae P hmodel] with u hu
  filter_upwards [] with a
  simpa [observedPilot] using hu

/-- Regular-model observed pilot responses stay in the unit interval. -/
-- @node: pilotUnitLaw_response_mem_Icc_ae
lemma pilotUnitLaw_response_mem_Icc_ae (P : Measure (UnitRecord d))
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ∀ᵐ v ∂pilotUnitLaw P, v.2.2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hset : MeasurableSet {v : PilotRecord d | v.2.2 ∈ Set.Icc (0 : ℝ) 1} := by
    measurability
  unfold pilotUnitLaw
  change ∀ᵐ v ∂(P.prod fairCoin).map (fun ua => observedPilot ua.1 ua.2),
    v ∈ {v : PilotRecord d | v.2.2 ∈ Set.Icc (0 : ℝ) 1}
  apply (ae_map_iff (μ := P.prod fairCoin)
    (f := fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2)
    measurable_observedPilot_pair.aemeasurable hset).2
  change ∀ᵐ ua ∂P.prod fairCoin,
    observedPilot ua.1 ua.2 ∈ {v : PilotRecord d | v.2.2 ∈ Set.Icc (0 : ℝ) 1}
  rw [Measure.ae_prod_iff_ae_ae (hset.preimage measurable_observedPilot_pair)]
  filter_upwards [hmodel.bounded_outcomes] with u hu
  filter_upwards [] with a
  cases a with
  | false => simpa [observedPilot] using hu.1
  | true => simpa [observedPilot] using hu.2

/-- For regular models, the paper's integrated pilot loss is exactly the
substrate cubical-histogram risk. -/
-- @node: histogram_l2_integral_eq_cubical_risk
lemma histogram_l2_integral_eq_cubical_risk (m d : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m) (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hmodel : RegularScoreModel P g L beta cX CX cg Cg) :
    (∫ pilot, ∫ u, (histogramScore beta pilot u.1 - g u.1) ^ 2 ∂P
      ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P)) =
    Causalean.Stat.Nonparametric.HistogramRegression.risk (pilotUnitLaw P) (Measure.pi fun _ : Fin m => pilotUnitLaw P)
      (cubeLabel (optimizedBandwidth d beta m))
      (fun v : PilotRecord d => pilotCubeClamp v.1) (fun v => v.2.2) (1 / 2)
      (fun x => g x.val.ofLp) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure fairCoin := histogram_fairCoin_probability
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  let Xp : PilotRecord d → Cube d := fun v => pilotCubeClamp v.1
  let Yp : PilotRecord d → ℝ := fun v => v.2.2
  let gc : Cube d → ℝ := fun x => g x.val.ofLp
  let label : Cube d → (Fin d → Fin (meshCount (optimizedBandwidth d beta m))) :=
    cubeLabel (optimizedBandwidth d beta m)
  have hXp : Measurable Xp := by
    dsimp [Xp]
    unfold pilotCubeClamp
    fun_prop
  have hYp : Measurable Yp := by fun_prop
  have hgc : Measurable gc := measurable_paperCubeScore g
    hmodel.parameters.2.2.2.1 hbeta hmodel.holder_score
  have hpilot := pilotUnitLaw_covariate_mem_cube_ae P hmodel
  have hsamples : ∀ᵐ p ∂Measure.pi (fun _ : Fin m => pilotUnitLaw P),
      ∀ r, (p r).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hpilot
  unfold Causalean.Stat.Nonparametric.HistogramRegression.risk
  apply integral_congr_ae
  filter_upwards [hsamples] with p hp
  let H : PilotRecord d → ℝ := fun v =>
    (histogram label Xp Yp (1 / 2) p (Xp v) - gc (Xp v)) ^ 2
  have hH : Measurable H := by
    dsimp [H]
    exact (((measurable_histogram label Xp Yp (1 / 2)
      (measurable_cubeLabel d (optimizedBandwidth d beta m)) hXp hYp).comp
        (measurable_const.prodMk hXp)).sub (hgc.comp hXp)).pow_const 2
  have hmap : pilotUnitLaw P = (P.prod fairCoin).map
      (fun ua => observedPilot ua.1 ua.2) := rfl
  rw [hmap, integral_map measurable_observedPilot_pair.aemeasurable hH.aestronglyMeasurable]
  have hfun : (fun ua : UnitRecord d × Bool => H (observedPilot ua.1 ua.2)) =
      fun ua => (histogram label Xp Yp (1 / 2) p (pilotCubeClamp ua.1.1) -
        gc (pilotCubeClamp ua.1.1)) ^ 2 := by
    funext ua
    rfl
  rw [hfun]
  let K : UnitRecord d → ℝ := fun u =>
    (histogram label Xp Yp (1 / 2) p (pilotCubeClamp u.1) -
      gc (pilotCubeClamp u.1)) ^ 2
  change (∫ u, (histogramScore beta p u.1 - g u.1) ^ 2 ∂P) =
    ∫ ua, K ua.1 ∂P.prod fairCoin
  rw [integral_fun_fst]
  have hmass : fairCoin.real Set.univ = 1 := by
    simpa [Measure.real] using congrArg ENNReal.toReal
      (show fairCoin Set.univ = 1 from measure_univ)
  rw [hmass, one_smul]
  apply integral_congr_ae
  filter_upwards [regularScore_covariate_mem_cube_ae P hmodel] with u hu
  dsimp [K]
  rw [pilot_histogram_eq_histogramScore m d beta hbeta hm p u.1 hp hu]
  simp [gc, pilotCubeClamp_eq u.1 hu]

/-- The clipped paper histogram always takes values in the unit interval. -/
lemma histogramScore_mem_Icc (beta : ℝ) (p : PilotSample m d) (x : XSpace d) :
    histogramScore beta p x ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [histogramScore]
  split_ifs
  · norm_num
  · unfold clip01
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The joint squared error of the paper histogram is integrable under an iid
pilot sample and an independent fresh unit. -/
lemma integrable_histogramScore_sq_error (m d : ℕ) (beta : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m) (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hmodel : RegularScoreModel P g L beta cX CX cg Cg) :
    Integrable (Function.uncurry fun pilot u =>
      (g u.1 - histogramScore beta pilot u.1) ^ 2)
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod P) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  let μp := Measure.pi fun _ : Fin m => pilotUnitLaw P
  let Xp : PilotRecord d → Cube d := fun v => pilotCubeClamp v.1
  let Yp : PilotRecord d → ℝ := fun v => v.2.2
  let gc : Cube d → ℝ := fun x => g x.val.ofLp
  let label : Cube d → (Fin d → Fin (meshCount (optimizedBandwidth d beta m))) :=
    cubeLabel (optimizedBandwidth d beta m)
  let K : PilotSample m d × UnitRecord d → ℝ := fun q =>
    (gc (pilotCubeClamp q.2.1) -
      histogram label Xp Yp (1 / 2) q.1 (pilotCubeClamp q.2.1)) ^ 2
  have hXp : Measurable Xp := by
    dsimp [Xp]
    unfold pilotCubeClamp
    fun_prop
  have hYp : Measurable Yp := by fun_prop
  have hgc : Measurable gc := measurable_paperCubeScore g
    hmodel.parameters.2.2.2.1 hbeta hmodel.holder_score
  have hclamp : Measurable (fun u : UnitRecord d => pilotCubeClamp u.1) := by
    unfold pilotCubeClamp
    fun_prop
  have hK : Measurable K := by
    dsimp [K]
    exact ((hgc.comp (hclamp.comp measurable_snd)).sub
      ((measurable_histogram label Xp Yp (1 / 2)
        (measurable_cubeLabel d (optimizedBandwidth d beta m)) hXp hYp).comp
        (measurable_fst.prodMk (hclamp.comp measurable_snd)))).pow_const 2
  have hpilots : ∀ᵐ p ∂μp, ∀ r, (p r).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => pilotUnitLaw_covariate_mem_cube_ae P hmodel
  have hunits := regularScore_covariate_mem_cube_ae P hmodel
  have hpilots_prod : ∀ᵐ q ∂μp.prod P, ∀ r, (q.1 r).1 ∈ cube d := by
    have hmapped : ∀ᵐ p ∂Measure.map Prod.fst (μp.prod P),
        ∀ r, (p r).1 ∈ cube d :=
      (Measure.quasiMeasurePreserving_fst (μ := μp) (ν := P)).absolutelyContinuous.ae_le
        hpilots
    exact ae_of_ae_map measurable_fst.aemeasurable hmapped
  have hunits_prod : ∀ᵐ q ∂μp.prod P, q.2.1 ∈ cube d := by
    have hmapped : ∀ᵐ u ∂Measure.map Prod.snd (μp.prod P), u.1 ∈ cube d :=
      (Measure.quasiMeasurePreserving_snd (μ := μp) (ν := P)).absolutelyContinuous.ae_le
        hunits
    exact ae_of_ae_map measurable_snd.aemeasurable hmapped
  have heq : (Function.uncurry fun pilot u =>
      (g u.1 - histogramScore beta pilot u.1) ^ 2) =ᵐ[μp.prod P] K := by
    filter_upwards [hpilots_prod, hunits_prod] with q hp hu
    dsimp [K, gc]
    rw [pilot_histogram_eq_histogramScore m d beta hbeta hm q.1 q.2.1 hp hu,
      pilotCubeClamp_eq q.2.1 hu]
    rfl
  have hY0 : Integrable (fun u : UnitRecord d => u.2.1) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmodel.bounded_outcomes] with u hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
  have hY1 : Integrable (fun u : UnitRecord d => u.2.2) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hmodel.bounded_outcomes] with u hu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩
  have hreg0lo : 0 ≤ᵐ[P] regression0 P := by
    exact condExp_nonneg (hmodel.bounded_outcomes.mono fun u hu => hu.1.1)
  have hreg1lo : 0 ≤ᵐ[P] regression1 P := by
    exact condExp_nonneg (hmodel.bounded_outcomes.mono fun u hu => hu.2.1)
  have hreg0hi : regression0 P ≤ᵐ[P] fun _ => 1 := by
    have h := condExp_mono (m := MeasurableSpace.comap Prod.fst inferInstance)
      hY0 (integrable_const (1 : ℝ))
      (hmodel.bounded_outcomes.mono fun u hu => hu.1.2)
    simpa [regression0, condExp_const measurable_fst.comap_le] using h
  have hreg1hi : regression1 P ≤ᵐ[P] fun _ => 1 := by
    have h := condExp_mono (m := MeasurableSpace.comap Prod.fst inferInstance)
      hY1 (integrable_const (1 : ℝ))
      (hmodel.bounded_outcomes.mono fun u hu => hu.2.2)
    simpa [regression1, condExp_const measurable_fst.comap_le] using h
  have hgbound : ∀ᵐ u ∂P, g u.1 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hmodel.half_sum_version, hreg0lo, hreg1lo, hreg0hi, hreg1hi]
      with u hg h0lo h1lo h0hi h1hi
    simp only [Pi.zero_apply] at h0lo h1lo
    rw [hg]
    constructor <;> linarith
  have hgbound_prod : ∀ᵐ q ∂μp.prod P, g q.2.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hmapped : ∀ᵐ u ∂Measure.map Prod.snd (μp.prod P),
        g u.1 ∈ Set.Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := μp) (ν := P)).absolutelyContinuous.ae_le
        hgbound
    exact ae_of_ae_map measurable_snd.aemeasurable hmapped
  refine (integrable_const (1 : ℝ)).mono' (hK.aestronglyMeasurable.congr heq.symm) ?_
  filter_upwards [hgbound_prod] with q hg
  have hh := histogramScore_mem_Icc beta q.1 q.2.1
  rcases hg with ⟨hg0, hg1⟩
  rcases hh with ⟨hh0, hh1⟩
  change ‖(g q.2.1 - histogramScore beta q.1 q.2.1) ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hlo : -1 ≤ g q.2.1 - histogramScore beta q.1 q.2.1 := by linarith
  have hhi : g q.2.1 - histogramScore beta q.1 q.2.1 ≤ 1 := by linarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 +
    (g q.2.1 - histogramScore beta q.1 q.2.1)) (by linarith : 0 ≤ 1 -
    (g q.2.1 - histogramScore beta q.1 q.2.1))]

lemma histogram_l2_rate (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m : ℕ, 1 ≤ m →
      ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg →
      (∫ pilot, ∫ u,
          (histogramScore β pilot u.1 - g u.1) ^ 2 ∂P
        ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P)) ≤
        C * (m : ℝ) ^ (-2 * β / (2 * β + d)) := by
  let C : ℝ := 2 * L ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) + 6 * (2 : ℝ) ^ d
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m hm P g hmodel
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  let Xp : PilotRecord d → Cube d := fun v => pilotCubeClamp v.1
  let Yp : PilotRecord d → ℝ := fun v => v.2.2
  let gc : Cube d → ℝ := fun x => g x.val.ofLp
  have hXp : Measurable Xp := by
    dsimp [Xp]
    unfold pilotCubeClamp
    fun_prop
  have hYp : Measurable Yp := by fun_prop
  have hgc : Measurable gc := measurable_paperCubeScore g
    hmodel.parameters.2.2.2.1 hβ hmodel.holder_score
  have hr := optimized_cubical_histogram_risk_le (m := m) (d := d)
    (pilotUnitLaw P) Xp Yp gc (1 / 2) β L hXp hYp hgc
    (pilotUnitLaw_response_mem_Icc_ae P hmodel) (by norm_num)
    (pilotUnitLaw_conditionalMean P g hmodel) hβ hmodel.parameters.2.2.2.1.le hm
    (paperCubeScore_holder g hmodel.holder_score)
  rw [histogram_l2_integral_eq_cubical_risk m d β hβ hm P g hmodel]
  have hexp : -(2 * β / (2 * β + (d : ℝ))) =
      -2 * β / (2 * β + (d : ℝ)) := by ring
  rw [hexp] at hr
  simpa [C, Xp, Yp, gc] using hr

end

end CausalSmith.Experimentation.PilotscorePairingFrontier
