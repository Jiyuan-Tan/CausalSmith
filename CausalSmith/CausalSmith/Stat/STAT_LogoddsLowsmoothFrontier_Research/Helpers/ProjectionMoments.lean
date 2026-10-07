module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionOrthogonality
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean
public import Causalean.Tactic.IntegralLinearity

/-! # Projection statistic moments

Disintegration and iid coordinate transport give the exact mean and bias.
The first uncentered projection has squared energy at most one, and the
symmetric kernel has squared energy at most its rank. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Every subtype cosine mode is continuous. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: cosineBasis_continuous
@[fun_prop]
lemma cosineBasis_continuous (j : ℕ) : Continuous (cosineBasis j) := by
  unfold cosineBasis
  split_ifs <;> fun_prop

/-- Borel tests integrate through the four-cell law whenever their weighted slices are integrable. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hDesign,hf,hi) hold, and [the stated conclusion follows](goal). -/
-- @node: integral_observed_cells_borel
lemma integral_observed_cells_borel (P : ObservedLaw) (hDesign : UniformDesign P)
    (f : Record → ℝ) (hf : Measurable f)
    (hi : ∀ a y, Integrable (fun x => P.cells a y x * f (x,a,y)) uniformLaw) :
    (∫ o, f o ∂P.measure) =
      ∑ a : Bool, ∑ y : Bool, ∫ x, P.cells a y x * f (x,a,y) ∂uniformLaw := by
  have hm (a y : Bool) : Measurable (fun x => ENNReal.ofReal (P.cells a y x)) :=
    ENNReal.measurable_ofReal.comp (P.continuous_cells a y).measurable
  have hi' (a y : Bool) : Integrable f
      (Measure.map (fun x : Covariate => (x,a,y))
        (uniformLaw.withDensity (fun x => ENNReal.ofReal (P.cells a y x)))) := by
    apply (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2
    apply (integrable_withDensity_iff_integrable_smul' (hm a y)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
    simpa only [ENNReal.toReal_ofReal (P.interior_cells a y _).1.le, smul_eq_mul, Function.comp_def] using hi a y
  rw [P.disintegration, hDesign]
  unfold jointLaw
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum_measure (fun y _ => hi' a y)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (hm a y)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (P.interior_cells a y _).1.le, smul_eq_mul]
  · intro a ha
    exact integrable_finsetSum_measure.2 (fun y _ => hi' a y)

/-- [Disintegration identifies the design-weighted mean of every Borel bounded mark.](goal) Under [the stated assumptions](hyp:hDesign,g,hg,hgi). -/
-- @node: boundedMark_integral_covariate
lemma boundedMark_integral_covariate (P : ObservedLaw) (hDesign : UniformDesign P)
    (W : BoundedMark) (g : Covariate → ℝ) (hg : Measurable g)
    (hgi : Integrable g uniformLaw) :
    (∫ o, W.value o * g (covariate o) ∂P.measure) =
      uniformInner (conditionalMarkMean P W) g := by
  have hm := W.measurable_value
  have hi (a y : Bool) :
      Integrable (fun x => P.cells a y x * (W.value (x,a,y) * g x)) uniformLaw := by
    have hw : Measurable (fun x : Covariate => P.cells a y x * W.value (x,a,y)) := by
      have hc := (P.continuous_cells a y).measurable
      fun_prop
    have hb : ∀ x : Covariate, ‖P.cells a y x * W.value (x,a,y)‖ ≤ (1 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (P.interior_cells a y x).1.le (W.range_value _).1)]
      exact (mul_le_of_le_one_right (P.interior_cells a y x).1.le
        (W.range_value _).2).trans (P.interior_cells a y x).2.le
    exact (hgi.bdd_mul (c := 1) hw.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).congr
        (Filter.Eventually.of_forall (fun x => by ring))
  rw [integral_observed_cells_borel P hDesign _ (by unfold covariate; fun_prop) hi]
  unfold uniformInner conditionalMarkMean
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun a ha => integrable_finsetSum _ (fun y hy =>
    (hi a y).congr (Filter.Eventually.of_forall (fun x => by ring))))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum _ (fun y hy =>
    (hi a y).congr (Filter.Eventually.of_forall (fun x => by ring)))]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  funext x
  simp only [covariate]
  ring

/-- [Products of a Borel bounded mark and a continuous record function are integrable.](goal) Under [the stated assumptions](hyp:g,hg). -/
-- @node: boundedMark_mul_continuous_integrable
lemma boundedMark_mul_continuous_integrable (P : ObservedLaw) (W : BoundedMark)
    (g : Record → ℝ) (hg : Continuous g) :
    Integrable (fun o => W.value o * g o) P.measure := by
  apply (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).bdd_mul
    (c := 1) W.measurable_value.aestronglyMeasurable
  filter_upwards [] with o
  rw [Real.norm_eq_abs, abs_of_nonneg (W.range_value o).1]
  exact (W.range_value o).2

/-- [Integrating one asymmetric kernel slice gives the projected conditional mark mean.](goal) Under [the stated assumptions](hyp:hDesign,x). -/
-- @node: projectionKernel_mark_integral
lemma projectionKernel_mark_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (V : BoundedMark) (k : ℕ) (x : Covariate) :
    (∫ p, projectionKernel k x (covariate p) * V.value p ∂P.measure) =
      cosineProjection k (conditionalMarkMean P V) x := by
  have hc (j : ℕ) : Continuous (cosineBasis j) := by
    unfold cosineBasis
    split_ifs <;> fun_prop
  have hi (j : ℕ) : Integrable (fun p => cosineBasis j (covariate p) * V.value p) P.measure := by
    simpa only [mul_comm] using boundedMark_mul_continuous_integrable P V
      (fun p => cosineBasis j (covariate p)) ((hc j).comp (by unfold covariate; fun_prop))
  unfold projectionKernel cosineProjection
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j hj => ((hi j).const_mul _).congr
    (Filter.Eventually.of_forall (fun p => by ring)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (fun p => cosineBasis j x * cosineBasis j (covariate p) * V.value p) =
    (fun p => cosineBasis j x * (V.value p * cosineBasis j (covariate p))) by funext p; ring,
    integral_const_mul, boundedMark_integral_covariate P hDesign V _ (hc j).measurable
      (cosineBasis_integrable j)]
  ring

/-- [The first uncentered Hoeffding projection is the average of the two projected marks.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_integral_right
lemma symmetricProjectionKernel_integral_right (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (o : Record) :
    (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure) =
      (W.value o * cosineProjection k (conditionalMarkMean P V) (covariate o) +
        V.value o * cosineProjection k (conditionalMarkMean P W) (covariate o)) / 2 := by
  have hc : Continuous (fun p : Record => projectionKernel k (covariate o) (covariate p)) := by
    unfold projectionKernel covariate
    fun_prop
  have hi (B : BoundedMark) :
      Integrable (fun p => projectionKernel k (covariate o) (covariate p) * B.value p) P.measure := by
    simpa only [mul_comm] using boundedMark_mul_continuous_integrable P B _ hc
  have he (p : Record) : symmetricProjectionKernel k W.value V.value o p =
      (W.value o * (projectionKernel k (covariate o) (covariate p) * V.value p) +
        V.value o * (projectionKernel k (covariate o) (covariate p) * W.value p)) / 2 := by
    unfold symmetricProjectionKernel
    ring
  simp_rw [he]
  rw [integral_div, integral_add ((hi V).const_mul _) ((hi W).const_mul _),
    integral_const_mul, integral_const_mul,
    projectionKernel_mark_integral P hDesign V, projectionKernel_mark_integral P hDesign W]

/-- [Independence and finite cosine orthogonality give the mean of the symmetric kernel.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_integral
lemma symmetricProjectionKernel_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ o, ∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure ∂P.measure) =
      uniformInner (cosineProjection k (conditionalMarkMean P W))
        (cosineProjection k (conditionalMarkMean P V)) := by
  letI : IsProbabilityMeasure uniformLaw := hDesign ▸
    Measure.isProbabilityMeasure_map (by unfold covariate; fun_prop : Measurable covariate).aemeasurable
  have hc (B : BoundedMark) : Continuous (cosineProjection k (conditionalMarkMean P B)) := by
    unfold cosineProjection
    fun_prop
  have hi (B D : BoundedMark) : Integrable
      (fun o => B.value o * cosineProjection k (conditionalMarkMean P D) (covariate o)) P.measure :=
    boundedMark_mul_continuous_integrable P B _ ((hc D).comp (by unfold covariate; fun_prop))
  have hp (B : BoundedMark) : Integrable (cosineProjection k (conditionalMarkMean P B)) uniformLaw :=
    (hc B).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [symmetricProjectionKernel_integral_right P hDesign W V k]
  rw [integral_div, integral_add (hi W V) (hi V W),
    boundedMark_integral_covariate P hDesign W _ (hc V).measurable (hp V),
    boundedMark_integral_covariate P hDesign V _ (hc W).measurable (hp W),
    uniformInner_cosineProjection k _ _
      (fun j => conditionalMarkMean_mul_integrable P W (cosineBasis_integrable j)),
    uniformInner_cosineProjection k _ _
      (fun j => conditionalMarkMean_mul_integrable P V (cosineBasis_integrable j)),
    cosineProjection_uniformInner]
  have hs : (∑ j ∈ Finset.range k,
      uniformInner (conditionalMarkMean P V) (cosineBasis j) *
        uniformInner (conditionalMarkMean P W) (cosineBasis j)) =
      ∑ j ∈ Finset.range k,
        uniformInner (conditionalMarkMean P W) (cosineBasis j) *
          uniformInner (conditionalMarkMean P V) (cosineBasis j) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring

/-- [The symmetric marked kernel is Borel measurable on the record pair space. [the documented result](goal) -/
-- @node: symmetricProjectionKernel_measurable
@[fun_prop]
lemma symmetricProjectionKernel_measurable (k : ℕ) (W V : BoundedMark) :
    Measurable (fun z : Record × Record => symmetricProjectionKernel k W.value V.value z.1 z.2) := by
  have hW := W.measurable_value
  have hV := V.measurable_value
  unfold symmetricProjectionKernel projectionKernel covariate
  fun_prop

/-- Bounded marks preserve integrability of the symmetric kernel under two independent records. [the stated conclusion](goal) holds. -/
-- @node: symmetricProjectionKernel_integrable
lemma symmetricProjectionKernel_integrable (P : ObservedLaw) (k : ℕ) (W V : BoundedMark) :
    Integrable (fun z : Record × Record => symmetricProjectionKernel k W.value V.value z.1 z.2)
      (P.measure.prod P.measure) := by
  have hc : Continuous (fun z : Record × Record =>
      projectionKernel k (covariate z.1) (covariate z.2)) := by
    unfold projectionKernel covariate
    fun_prop
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := P.measure.prod P.measure)
  have hm (B : BoundedMark) (o : Record) : ‖B.value o‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (B.range_value o).1]
    exact (B.range_value o).2
  have ht (B D : BoundedMark) : Integrable (fun z : Record × Record =>
      projectionKernel k (covariate z.1) (covariate z.2) * B.value z.1 * D.value z.2)
      (P.measure.prod P.measure) := by
    have hB : Measurable (fun z : Record × Record => B.value z.1) :=
      B.measurable_value.comp measurable_fst
    have hD : Measurable (fun z : Record × Record => D.value z.2) :=
      D.measurable_value.comp measurable_snd
    have hb := hi.bdd_mul hB.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hm B z.1))
    have hd := hb.bdd_mul hD.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hm D z.2))
    exact hd.congr (Filter.Eventually.of_forall (fun z => by ring))
  exact ((ht W V).add (ht V W)).div_const 2 |>.congr
    (Filter.Eventually.of_forall (fun z => by unfold symmetricProjectionKernel; dsimp; ring))

/-- Averaging over all distinct ordered iid coordinates preserves the two-record mean. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hn,hH,hInt) hold, and [the stated conclusion follows](goal). -/
-- @node: integral_orderedPair_average
lemma integral_orderedPair_average (P : ObservedLaw) (n : ℕ) (hn : 2 ≤ n)
    (H : Record → Record → ℝ)
    (hH : Measurable (fun z : Record × Record => H z.1 z.2))
    (hInt : Integrable (fun z : Record × Record => H z.1 z.2) (P.measure.prod P.measure)) :
    (∫ o, ((n : ℝ) * ((n : ℝ)-1))⁻¹ *
      ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
        H (o ij.1) (o ij.2) ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      ∫ z : Record × Record, H z.1 z.2 ∂(P.measure.prod P.measure) := by
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    infer_instance
  let s := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)
  have hcoord : iIndepFun (fun a : Fin n => fun o : Fin n → Record => o a) μ := by
    simpa [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
      (iIndepFun_pi (μ := fun _ : Fin n => P.measure)
        (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair (ij : Fin n × Fin n) (hij : ij ∈ s) :
      μ.map (fun o => (o ij.1, o ij.2)) = P.measure.prod P.measure := by
    have hne : ij.1 ≠ ij.2 := (Finset.mem_filter.mp hij).2
    simpa only [(measurePreserving_eval (fun _ : Fin n => P.measure) ij.1).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P.measure) ij.2).map_eq,
      μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
      ((hcoord.indepFun hne).map_prod_eq_prod_map_map
        (measurable_pi_apply ij.1).aemeasurable (measurable_pi_apply ij.2).aemeasurable)
  have hi (ij : Fin n × Fin n) (hij : ij ∈ s) : Integrable
      (fun o => H (o ij.1) (o ij.2)) μ := by
    have hm : Measurable (fun o : Fin n → Record => (o ij.1, o ij.2)) := by fun_prop
    have hp : Integrable (fun z : Record × Record => H z.1 z.2)
        (μ.map (fun o => (o ij.1, o ij.2))) := by rw [hpair ij hij]; exact hInt
    exact hp.comp_measurable hm
  have hcard : (s.card : ℝ) = (n : ℝ) * ((n : ℝ)-1) := by
    have hs : s = (Finset.univ : Finset (Fin n)).offDiag := by
      ext ij
      simp [s, Finset.mem_offDiag]
    rw [hs, Finset.offDiag_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by nlinarith : n ≤ n*n), Nat.cast_mul]
    ring
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  change (∫ o, _ * ∑ ij ∈ s, H (o ij.1) (o ij.2) ∂μ) = _
  rw [integral_const_mul, integral_finsetSum s hi]
  have he (ij : Fin n × Fin n) (hij : ij ∈ s) :
      (∫ o, H (o ij.1) (o ij.2) ∂μ) =
        ∫ z : Record × Record, H z.1 z.2 ∂(P.measure.prod P.measure) :=
    Causalean.Stat.UStatistic.LocalizedVariance.integral_two_coordinates_integrable
      P.measure (Finset.mem_filter.mp hij).2 H hH
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [inv_mul_cancel_left₀ (mul_ne_zero hn0 hn1)]

/-- [The original finite-sample ordered statistic has the projected conditional-means inner product.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionStatistic_integral
lemma projectionStatistic_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o, projectionStatistic n k W.value V.value o
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      uniformInner (cosineProjection k (conditionalMarkMean P W))
        (cosineProjection k (conditionalMarkMean P V)) := by
  simp_rw [projectionStatistic_eq_symmetric]
  rw [integral_orderedPair_average P n hn _ (symmetricProjectionKernel_measurable k W V)
    (symmetricProjectionKernel_integrable P k W V),
    integral_prod _ (symmetricProjectionKernel_integrable P k W V)]
  exact symmetricProjectionKernel_integral P hDesign W V k

/-- [The finite-sample projection statistic has exactly the orthogonal residual bias.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionStatistic_bias
lemma projectionStatistic_bias (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    uniformInner (conditionalMarkMean P W) (conditionalMarkMean P V) -
      (∫ o, projectionStatistic n k W.value V.value o
        ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
    uniformInner
      (fun x => conditionalMarkMean P W x - cosineProjection k (conditionalMarkMean P W) x)
      (fun x => conditionalMarkMean P V x - cosineProjection k (conditionalMarkMean P V) x) := by
  rw [projectionStatistic_integral P hDesign W V k n hn]
  exact conditionalMarkMean_residual_inner P W V k

/-- [Uniform design transports every continuous covariate integral to the record law.](goal) Under [the stated assumptions](hyp:hDesign,f,hf). -/
-- @node: integral_continuous_covariate
lemma integral_continuous_covariate (P : ObservedLaw) (hDesign : UniformDesign P)
    (f : Covariate → ℝ) (hf : Continuous f) :
    (∫ o, f (covariate o) ∂P.measure) = ∫ x, f x ∂uniformLaw := by
  rw [← hDesign, integral_map (by unfold covariate; fun_prop) hf.aestronglyMeasurable]

/-- [The first uncentered projection is dominated by the average projected-mark energies.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_first_sq_le
lemma symmetricProjectionKernel_first_sq_le (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (o : Record) :
    (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure)^2 ≤
      ((cosineProjection k (conditionalMarkMean P V) (covariate o))^2 +
        (cosineProjection k (conditionalMarkMean P W) (covariate o))^2) / 2 := by
  rw [symmetricProjectionKernel_integral_right P hDesign W V k o]
  have hm (B : BoundedMark) : (B.value o)^2 ≤ 1 := by
    have hb := B.range_value o
    nlinarith
  have hW := mul_le_mul_of_nonneg_right (hm W)
    (sq_nonneg (cosineProjection k (conditionalMarkMean P V) (covariate o)))
  have hV := mul_le_mul_of_nonneg_right (hm V)
    (sq_nonneg (cosineProjection k (conditionalMarkMean P W) (covariate o)))
  have hd := sq_nonneg
    (W.value o * cosineProjection k (conditionalMarkMean P V) (covariate o) -
      V.value o * cosineProjection k (conditionalMarkMean P W) (covariate o))
  nlinarith

/-- [The squared first projection is integrable under the record law.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_first_sq_integrable
lemma symmetricProjectionKernel_first_sq_integrable (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    Integrable (fun o => (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure)^2)
      P.measure := by
  have hc (B : BoundedMark) : Continuous (cosineProjection k (conditionalMarkMean P B)) := by
    unfold cosineProjection
    fun_prop
  have hb : Continuous (fun o : Record =>
      ((cosineProjection k (conditionalMarkMean P V) (covariate o))^2 +
        (cosineProjection k (conditionalMarkMean P W) (covariate o))^2) / 2) := by
    unfold covariate
    fun_prop
  have hm : Measurable (fun o : Record =>
      (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure)^2) := by
    simp_rw [symmetricProjectionKernel_integral_right P hDesign W V k]
    have hw := W.measurable_value
    have hv := V.measurable_value
    unfold covariate
    fun_prop
  apply (hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact symmetricProjectionKernel_first_sq_le P hDesign W V k o

/-- [Centering the first projection subtracts the squared kernel mean from its energy.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_first_centered_energy
lemma symmetricProjectionKernel_first_centered_energy (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    let τ := uniformInner (cosineProjection k (conditionalMarkMean P W))
      (cosineProjection k (conditionalMarkMean P V))
    (∫ o, ((∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure) - τ)^2
      ∂P.measure) =
      (∫ o, (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure)^2
        ∂P.measure) - τ^2 := by
  dsimp only
  let f := fun o => ∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure
  let τ := uniformInner (cosineProjection k (conditionalMarkMean P W))
    (cosineProjection k (conditionalMarkMean P V))
  have hf : Integrable f P.measure := by
    dsimp [f]
    simp_rw [symmetricProjectionKernel_integral_right P hDesign W V k]
    have hc (B : BoundedMark) : Continuous (cosineProjection k (conditionalMarkMean P B)) := by
      unfold cosineProjection
      fun_prop
    exact ((boundedMark_mul_continuous_integrable P W _
      ((hc V).comp (by unfold covariate; fun_prop))).add
      (boundedMark_mul_continuous_integrable P V _
        ((hc W).comp (by unfold covariate; fun_prop)))).div_const 2
  have hsq : Integrable (fun o => (f o)^2) P.measure :=
    symmetricProjectionKernel_first_sq_integrable P hDesign W V k
  have hmean : (∫ o, f o ∂P.measure) = τ := symmetricProjectionKernel_integral P hDesign W V k
  change (∫ o, (f o - τ)^2 ∂P.measure) = (∫ o, (f o)^2 ∂P.measure) - τ^2
  have he (o : Record) : (f o - τ)^2 = (f o)^2 - 2 * τ * f o + τ^2 := by ring
  simp_rw [he]
  integral_linearity
  rw [hmean, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

/-- [Its uncentered first projection has squared energy at most one.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_first_energy_le_one
lemma symmetricProjectionKernel_first_energy_le_one (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ o, (∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure)^2
      ∂P.measure) ≤ 1 := by
  have hc (B : BoundedMark) : Continuous (cosineProjection k (conditionalMarkMean P B)) := by
    unfold cosineProjection
    fun_prop
  have hbound : Continuous (fun o : Record =>
      ((cosineProjection k (conditionalMarkMean P V) (covariate o))^2 +
        (cosineProjection k (conditionalMarkMean P W) (covariate o))^2) / 2) := by
    unfold covariate
    fun_prop
  have hi := hbound.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := P.measure)
  have hfirst := symmetricProjectionKernel_first_sq_integrable P hDesign W V k
  apply (integral_mono hfirst hi (symmetricProjectionKernel_first_sq_le P hDesign W V k)).trans
  have hiB (B : BoundedMark) : Integrable
      (fun o => (cosineProjection k (conditionalMarkMean P B) (covariate o))^2) P.measure := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold covariate
    fun_prop
  rw [integral_div, integral_add (hiB V) (hiB W),
    integral_continuous_covariate P hDesign (fun x => (cosineProjection k (conditionalMarkMean P V) x)^2) (by fun_prop),
    integral_continuous_covariate P hDesign (fun x => (cosineProjection k (conditionalMarkMean P W) x)^2) (by fun_prop)]
  have hV := conditionalMarkMean_projection_energy_le_one P hDesign V k
  have hW := conditionalMarkMean_projection_energy_le_one P hDesign W k
  simp only [uniformInner, ← pow_two] at hV hW
  linarith

/-- [The centered first Hoeffding projection has squared energy at most one.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: symmetricProjectionKernel_first_centered_energy_le_one
lemma symmetricProjectionKernel_first_centered_energy_le_one (P : ObservedLaw)
    (hDesign : UniformDesign P) (W V : BoundedMark) (k : ℕ) :
    (∫ o, ((∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure) -
      uniformInner (cosineProjection k (conditionalMarkMean P W))
        (cosineProjection k (conditionalMarkMean P V)))^2 ∂P.measure) ≤ 1 := by
  rw [symmetricProjectionKernel_first_centered_energy P hDesign W V k]
  exact (sub_le_self _ (sq_nonneg _)).trans
    (symmetricProjectionKernel_first_energy_le_one P hDesign W V k)

/-- [The square of the symmetric marked kernel is integrable by its continuous kernel envelope. [the stated conclusion](goal) holds. -/
-- @node: symmetricProjectionKernel_sq_integrable
lemma symmetricProjectionKernel_sq_integrable (P : ObservedLaw) (k : ℕ) (W V : BoundedMark) :
    Integrable (fun z : Record × Record => (symmetricProjectionKernel k W.value V.value z.1 z.2)^2)
      (P.measure.prod P.measure) := by
  have hc : Continuous (fun z : Record × Record =>
      (projectionKernel k (covariate z.1) (covariate z.2))^2) := by
    unfold projectionKernel covariate
    fun_prop
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mono'
    ((symmetricProjectionKernel_measurable k W V).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact symmetricProjectionKernel_sq_le k W V z.1 z.2

/-- Uniform-design transport and finite cosine orthogonality bound the marked kernel energy by k. Under the stated assumptions. [The stated hypotheses](hyp:hDesign) hold, and [the stated conclusion follows](goal). -/
-- @node: symmetricProjectionKernel_energy_le_rank
lemma symmetricProjectionKernel_energy_le_rank (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ z : Record × Record, (symmetricProjectionKernel k W.value V.value z.1 z.2)^2
      ∂(P.measure.prod P.measure)) ≤ (k : ℝ) := by
  have hc : Continuous (fun z : Record × Record =>
      (projectionKernel k (covariate z.1) (covariate z.2))^2) := by
    unfold projectionKernel covariate
    fun_prop
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := P.measure.prod P.measure)
  apply (integral_mono (symmetricProjectionKernel_sq_integrable P k W V) hi
    (fun z => symmetricProjectionKernel_sq_le k W V z.1 z.2)).trans_eq
  rw [integral_prod _ hi]
  have hs (o : Record) :
      (∫ p, (projectionKernel k (covariate o) (covariate p))^2 ∂P.measure) =
        ∑ j ∈ Finset.range k, (cosineBasis j (covariate o))^2 := by
    rw [integral_continuous_covariate P hDesign (fun x => (projectionKernel k (covariate o) x)^2) (by unfold projectionKernel; fun_prop),
      projectionKernel_sq_integral_right]
  simp_rw [hs]
  rw [integral_continuous_covariate P hDesign (fun x => ∑ j ∈ Finset.range k, (cosineBasis j x)^2) (by fun_prop)]
  simpa only [projectionKernel_sq_integral_right] using projectionKernel_sq_integral k

end CausalSmith.Stat.LogoddsLowsmoothFrontier
