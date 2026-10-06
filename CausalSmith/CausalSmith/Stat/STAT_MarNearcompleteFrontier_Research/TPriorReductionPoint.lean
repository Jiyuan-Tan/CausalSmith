module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TNormalizedConverse
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.TParametricFloor
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Fuzzy-prior and interval lower-bound reduction

This is the paper's reduction from the normalized paired prior and one-cell
parametric floor to the combined point and interval lower frontiers.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

/-- Mixing the legal iid sample laws under a prior gives a probability law. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π). -/
-- @node: priorPredictive_isProbability
lemma priorPredictive_isProbability (n d : ℕ) (q : ℝ)
    (π : PMF (ClassLaw d q)) :
    IsProbabilityMeasure (priorPredictive n d q π) := by
  unfold priorPredictive
  have hsample : Measurable (fun P : ClassLaw d q => samplePi P.val n) := by
    intro s hs
    trivial
  have hsample_prob (P : ClassLaw d q) :
      IsProbabilityMeasure (samplePi P.val n) := by
    unfold samplePi
    infer_instance
  exact isProbabilityMeasure_bind hsample.aemeasurable
    (Filter.Eventually.of_forall hsample_prob)

-- @node: priorPredictive_event_eq_integral
/-- A predictive event has probability equal to its prior-averaged sample probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π), [the specified input `E`](hyp:E). -/
lemma priorPredictive_event_eq_integral (n d : ℕ) (q : ℝ)
    (π : PMF (ClassLaw d q)) (E : Set (Fin n → Obs d)) :
    (priorPredictive n d q π).real E =
      ∫ P, (samplePi P.val n).real E ∂π.toMeasure := by
  let K : ClassLaw d q → Measure (Fin n → Obs d) := fun P => samplePi P.val n
  have hK : Measurable K := by
    intro s hs
    trivial
  have hprob : ∀ P, IsProbabilityMeasure (K P) := by
    intro P
    dsimp [K, samplePi]
    infer_instance
  haveI : IsProbabilityMeasure (priorPredictive n d q π) :=
    priorPredictive_isProbability n d q π
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  let f : (Fin n → Obs d) → ℝ := E.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hE
  have hfint : Integrable f (priorPredictive n d q π) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        simp only [f, Set.indicator]
        split <;> simp)
  calc
    (priorPredictive n d q π).real E =
        ∫ z in E, (1 : ℝ) ∂(priorPredictive n d q π) := by simp
    _ = ∫ z, f z ∂(priorPredictive n d q π) := by rw [integral_indicator hE]
    _ = ∫ P, ∫ z, f z ∂K P ∂π.toMeasure := by
      simpa [priorPredictive, K] using
        (Causalean.Mathlib.MeasureTheory.integral_bind hK hfint)
    _ = ∫ P, (samplePi P.val n).real E ∂π.toMeasure := by
      congr 1
      funext P
      rw [show f = E.indicator (fun _ => (1 : ℝ)) from rfl,
        integral_indicator hE]
      simp [K]

/-- Total variation transfers any sample-event lower bound between the two mixtures. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `πminus`](hyp:πminus), [the specified input `πplus`](hyp:πplus), [the specified input `htv`](hyp:htv), [the specified input `E`](hyp:E). -/
-- @node: priorPredictive_event_transfer
lemma priorPredictive_event_transfer {n d : ℕ} {q β : ℝ}
    (πminus πplus : PMF (ClassLaw d q))
    (htv : Causalean.Stat.tvDist
      (priorPredictive n d q πminus) (priorPredictive n d q πplus) ≤ β)
    (E : Set (Fin n → Obs d)) :
    (priorPredictive n d q πminus).real E - β ≤
      (priorPredictive n d q πplus).real E := by
  haveI := priorPredictive_isProbability n d q πminus
  haveI := priorPredictive_isProbability n d q πplus
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have h := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := priorPredictive n d q πminus)
    (ν := priorPredictive n d q πplus) hE
  have hdiff := (abs_le.mp h).2
  linarith

-- @node: priorPredictive_separated_intersection
/-- Two high-probability hits under the fuzzy priors overlap under the plus mixture. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `β`](hyp:β). Given [the specified input `πminus`](hyp:πminus), [the specified input `πplus`](hyp:πplus), [the specified input `htv`](hyp:htv), [the specified input `Eleft`](hyp:Eleft), [the specified input `Eright`](hyp:Eright), [the specified input `hleft`](hyp:hleft), [the specified input `hright`](hyp:hright). -/
lemma priorPredictive_separated_intersection {n d : ℕ} {q α β : ℝ}
    (πminus πplus : PMF (ClassLaw d q))
    (htv : Causalean.Stat.tvDist
      (priorPredictive n d q πminus) (priorPredictive n d q πplus) ≤ β)
    (Eleft Eright : Set (Fin n → Obs d))
    (hleft : 1 - α - β ≤ (priorPredictive n d q πminus).real Eleft)
    (hright : 1 - α - β ≤ (priorPredictive n d q πplus).real Eright) :
    1 - 2 * α - 3 * β ≤
      (priorPredictive n d q πplus).real (Eleft ∩ Eright) := by
  letI := priorPredictive_isProbability n d q πplus
  have htransfer := priorPredictive_event_transfer πminus πplus htv Eleft
  have hmeas : MeasurableSet Eright := (Set.toFinite Eright).measurableSet
  have hfinite : (priorPredictive n d q πplus) (Eleft ∪ Eright) ≠ ⊤ := by
    exact measure_ne_top _ _
  have hsum := measureReal_union_add_inter hmeas
    (show (priorPredictive n d q πplus) Eleft ≠ ⊤ by exact measure_ne_top _ _)
    (show (priorPredictive n d q πplus) Eright ≠ ⊤ by exact measure_ne_top _ _)
  have hunion : (priorPredictive n d q πplus).real (Eleft ∪ Eright) ≤ 1 := by
    simpa using (measureReal_mono (Set.subset_univ _) hfinite)
  linarith

/-- Fixed fuzzy-hypothesis tolerance for point risk. -/
noncomputable def pointBeta : ℝ := 1 / 16
/-- [The fixed point-risk tolerance lies strictly between zero and one quarter](goal). -/
lemma pointBeta_valid : pointBeta ∈ Set.Ioo 0 ((1 : ℝ) / 4) := by
  unfold pointBeta
  constructor <;> norm_num

/-- Tolerance used in the honest-interval reduction. -/
noncomputable def intervalBeta (α : ℝ) : ℝ := (1 - 2 * α) / 8
/-- For [a confidence level strictly between zero and one half](hyp:hα), [the interval-risk tolerance lies strictly between zero and one quarter](goal). -/
lemma intervalBeta_valid (α : ℝ) (hα : α ∈ Set.Ioo 0 ((1 : ℝ) / 2)) :
    intervalBeta α ∈ Set.Ioo 0 ((1 : ℝ) / 4) := by
  rcases hα with ⟨hα0, hα1⟩
  unfold intervalBeta
  constructor <;> linarith

-- @node: gScale_nonneg_of_q
/-- The missingness scale is nonnegative on the model's arrival-floor range. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma gScale_nonneg_of_q (n d : ℕ) (q : ℝ)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    0 ≤ gScale n d q := by
  have hδ : 0 ≤ delta q := by
    unfold delta
    linarith [hq.2]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ ell n := le_of_lt (by
    unfold ell
    apply Real.log_pos
    have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith)
  unfold gScale
  exact mul_nonneg hδ (le_min (by norm_num) (div_nonneg hd (mul_nonneg hn hL)))

-- @node: pointRate_from_floor_and_separation
/-- The parametric floor and the separation bound combine into the point-risk rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c0`](hyp:c0), [the specified input `cSep`](hyp:cSep), [the specified input `R`](hyp:R), [the specified input `hn`](hyp:hn), [the specified input `hc0`](hyp:hc0), [the specified input `hcSep`](hyp:hcSep), [the specified input `n`](hyp:n), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hfloor`](hyp:hfloor), [the specified input `hsep`](hyp:hsep). -/
lemma pointRate_from_floor_and_separation (n d : ℕ) (q c0 cSep R : ℝ)
    (hn : 1 ≤ n) (hc0 : 0 ≤ c0) (hcSep : 0 ≤ cSep)
    (hfloor : c0 / (n : ℝ) ≤ R)
    (hsep : gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      cSep * gScale n d q ^ 2 ≤ R) :
    min c0 cSep / 2 * rate n d q ≤ R := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hx : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hy : 0 ≤ gScale n d q ^ 2 := sq_nonneg _
  have hc0' : min c0 cSep / 2 ≤ c0 / 2 := by
    linarith [min_le_left c0 cSep]
  have hcSep' : min c0 cSep / 2 ≤ cSep / 2 := by
    linarith [min_le_right c0 cSep]
  have hcmin : 0 ≤ min c0 cSep / 2 := by
    exact div_nonneg (le_min hc0 hcSep) (by norm_num)
  by_cases hlarge : 1 / (n : ℝ) ≤ gScale n d q ^ 2
  · have h := hsep hlarge
    rw [rate]
    calc
      min c0 cSep / 2 * (1 / (n : ℝ) + gScale n d q ^ 2) ≤
          min c0 cSep / 2 * (2 * gScale n d q ^ 2) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hcmin
      _ ≤ cSep * gScale n d q ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith :
          0 ≤ cSep - 2 * (min c0 cSep / 2))) hy]
      _ ≤ R := h
  · have hsmall : gScale n d q ^ 2 ≤ 1 / (n : ℝ) := le_of_lt (lt_of_not_ge hlarge)
    rw [rate]
    calc
      min c0 cSep / 2 * (1 / (n : ℝ) + gScale n d q ^ 2) ≤
          min c0 cSep / 2 * (2 * (1 / (n : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hcmin
      _ ≤ c0 * (1 / (n : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith :
          0 ≤ c0 - 2 * (min c0 cSep / 2))) hx]
      _ = c0 / (n : ℝ) := by ring
      _ ≤ R := hfloor

-- @node: intervalRate_from_floor_and_separation
/-- The parametric floor and separated-prior bound combine into the interval rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c0`](hyp:c0), [the specified input `cSep`](hyp:cSep), [the specified input `R`](hyp:R), [the specified input `hn`](hyp:hn), [the specified input `hc0`](hyp:hc0), [the specified input `hcSep`](hyp:hcSep), [the specified input `hfloor`](hyp:hfloor), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hsep`](hyp:hsep), [the specified input `hq`](hyp:hq). -/
lemma intervalRate_from_floor_and_separation (n d : ℕ) (q c0 cSep R : ℝ)
    (hn : 1 ≤ n) (hc0 : 0 ≤ c0) (hcSep : 0 ≤ cSep)
    (hfloor : c0 / Real.sqrt n ≤ R)
    (hsep : gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      cSep * gScale n d q ≤ R)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    min c0 cSep / 2 * Real.sqrt (rate n d q) ≤ R := by
  have hg : 0 ≤ gScale n d q := gScale_nonneg_of_q n d q hq
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hroot_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos)
  have hx : 0 ≤ (1 : ℝ) / n := by positivity
  have hrate : 0 ≤ rate n d q := by unfold rate; positivity
  have hsqrt : 0 ≤ Real.sqrt (rate n d q) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (rate n d q) ^ 2 = rate n d q := Real.sq_sqrt hrate
  have hc : 0 ≤ min c0 cSep / 2 := by positivity
  by_cases hlarge : 1 / (n : ℝ) ≤ gScale n d q ^ 2
  · have hbound : Real.sqrt (rate n d q) ≤ 2 * gScale n d q := by
      rw [rate]
      rw [rate] at hsqrt_sq
      nlinarith only [hsqrt_sq, hlarge, hg, hsqrt]
    calc
      min c0 cSep / 2 * Real.sqrt (rate n d q) ≤
          min c0 cSep / 2 * (2 * gScale n d q) :=
            mul_le_mul_of_nonneg_left hbound hc
      _ ≤ cSep * gScale n d q := by
        nlinarith [min_le_right c0 cSep]
      _ ≤ R := hsep hlarge
  · have hsmall : gScale n d q ^ 2 ≤ 1 / (n : ℝ) := le_of_lt (lt_of_not_ge hlarge)
    have hbound : Real.sqrt (rate n d q) ≤ 2 / Real.sqrt n := by
      rw [rate]
      rw [rate] at hsqrt_sq
      have hrecip : (1 : ℝ) / n = 1 / Real.sqrt n ^ 2 := by rw [hroot_sq]
      rw [hrecip] at hsmall hsqrt_sq
      rw [hrecip]
      have hpow : (1 : ℝ) / Real.sqrt n ^ 2 =
          (1 / Real.sqrt n) ^ 2 := by ring
      rw [hpow] at hsmall hsqrt_sq ⊢
      have hy : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
      have hs : 0 ≤ Real.sqrt ((1 / Real.sqrt n) ^ 2 + gScale n d q ^ 2) :=
        Real.sqrt_nonneg _
      have htwo : 2 / Real.sqrt n = 2 * (1 / Real.sqrt n) := by ring
      rw [htwo]
      nlinarith only [hsqrt_sq, hsmall, hs, hy]
    calc
      min c0 cSep / 2 * Real.sqrt (rate n d q) ≤
          min c0 cSep / 2 * (2 / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hbound hc
      _ ≤ c0 / Real.sqrt n := by
        have hmin : min c0 cSep ≤ c0 := min_le_left _ _
        calc
          min c0 cSep / 2 * (2 / Real.sqrt n) =
              min c0 cSep / Real.sqrt n := by ring
          _ ≤ c0 / Real.sqrt n :=
            div_le_div_of_nonneg_right hmin (le_of_lt hroot)
      _ ≤ R := hfloor

/-- Prior mass of a target failure is the complement of target success. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π). -/
-- @node: priorEventMass_complement
lemma priorEventMass_complement {d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (E : ClassLaw d q → Prop) :
    priorEventMass d q π (fun P => ¬ E P) =
      1 - priorEventMass d q π E := by
  classical
  unfold priorEventMass
  have hE : MeasurableSet {P : ClassLaw d q | E P} := trivial
  simpa only [show {P : ClassLaw d q | ¬ E P} = {P | E P}ᶜ by rfl,
    probReal_univ] using (measureReal_compl hE :
      π.toMeasure.real {P : ClassLaw d q | E P}ᶜ =
        π.toMeasure.real Set.univ - π.toMeasure.real {P | E P})

/-- A prior concentration certificate bounds the complementary target event. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `E`](hyp:E), [the specified input `hgood`](hyp:hgood), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `π`](hyp:π). -/
-- @node: priorEventMass_failure_le
lemma priorEventMass_failure_le {d : ℕ} {q β : ℝ}
    (π : PMF (ClassLaw d q)) (E : ClassLaw d q → Prop)
    (hgood : 1 - β ≤ priorEventMass d q π E) :
    priorEventMass d q π (fun P => ¬ E P) ≤ β := by
  rw [priorEventMass_complement]
  linarith

/-- A test that selects the right hypothesis incurs the separation loss on a left target. Given [the specified input `t`](hyp:t), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the specified input `ht`](hyp:ht), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ), [the specified input `hθ`](hyp:hθ). -/
-- @node: squaredLoss_of_left_target_and_right_test
lemma squaredLoss_of_left_target_and_right_test (t θ m a : ℝ)
    (ha : 0 ≤ a) (hθ : θ ≤ m - a) (ht : m ≤ t) :
    a ^ 2 ≤ (t - θ) ^ 2 := by
  have hsep : a ≤ t - θ := by linarith
  nlinarith [sq_nonneg (t - θ - a)]

/-- A test that selects the left hypothesis incurs the separation loss on a right target. Given [the specified input `t`](hyp:t), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the specified input `ht`](hyp:ht), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ), [the specified input `hθ`](hyp:hθ). -/
-- @node: squaredLoss_of_right_target_and_left_test
lemma squaredLoss_of_right_target_and_left_test (t θ m a : ℝ)
    (ha : 0 ≤ a) (hθ : m + a ≤ θ) (ht : t ≤ m) :
    a ^ 2 ≤ (t - θ) ^ 2 := by
  have hsep : a ≤ θ - t := by linarith
  nlinarith [sq_nonneg (θ - t - a)]

/-- A pointwise nonnegative loss bound on a sample event passes to its probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `a`](hyp:a), [the specified input `hf`](hyp:hf), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). Given [the specified input `E`](hyp:E), [the specified input `f`](hyp:f). -/
-- @node: sampleIntegral_ge_event
lemma sampleIntegral_ge_event {n d : ℕ} (P : FullLaw d)
    (E : Set (Fin n → Obs d)) (f : (Fin n → Obs d) → ℝ) (a : ℝ)
    (hf : ∀ o, 0 ≤ f o)
    (hE : ∀ o ∈ E, a ≤ f o) :
    a * (samplePi P n).real E ≤ ∫ o, f o ∂samplePi P n := by
  letI : IsProbabilityMeasure (samplePi P n) := by
    unfold samplePi
    infer_instance
  have hmeas : MeasurableSet E := (Set.toFinite E).measurableSet
  have hpoint (o : Fin n → Obs d) : E.indicator (fun _ => a) o ≤ f o := by
    by_cases ho : o ∈ E
    · simpa [Set.indicator, ho] using hE o ho
    · simpa [Set.indicator, ho] using hf o
  have hint : Integrable (E.indicator (fun _ : Fin n → Obs d => a))
      (samplePi P n) := Integrable.of_finite
  have hfint : Integrable f (samplePi P n) := Integrable.of_finite
  have hbound := integral_mono hint hfint hpoint
  simpa [integral_indicator hmeas, mul_comm] using hbound

/-- A right decision costs the squared separation on every left-target law. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `T`](hyp:T), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the stated mathematical conclusion holds](goal). Given [the specified input `hτ`](hyp:hτ). -/
-- @node: leftPrior_sampleRisk_lower
lemma leftPrior_sampleRisk_lower {n d : ℕ} (P : FullLaw d)
    (T : Estimator n d) (m a : ℝ) (ha : 0 ≤ a)
    (hτ : tau P ≤ m - a) :
    a ^ 2 * (samplePi P n).real {o | m ≤ T o} ≤
      ∫ o, (T o - tau P) ^ 2 ∂samplePi P n := by
  apply sampleIntegral_ge_event P {o | m ≤ T o}
    (fun o => (T o - tau P) ^ 2) (a ^ 2) (fun o => sq_nonneg _)
  intro o ho
  exact squaredLoss_of_left_target_and_right_test (T o) (tau P) m a ha hτ ho

/-- A left decision costs the squared separation on every right-target law. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `T`](hyp:T), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the stated mathematical conclusion holds](goal). Given [the specified input `hτ`](hyp:hτ). -/
-- @node: rightPrior_sampleRisk_lower
lemma rightPrior_sampleRisk_lower {n d : ℕ} (P : FullLaw d)
    (T : Estimator n d) (m a : ℝ) (ha : 0 ≤ a)
    (hτ : m + a ≤ tau P) :
    a ^ 2 * (samplePi P n).real {o | T o ≤ m} ≤
      ∫ o, (T o - tau P) ^ 2 ∂samplePi P n := by
  apply sampleIntegral_ge_event P {o | T o ≤ m}
    (fun o => (T o - tau P) ^ 2) (a ^ 2) (fun o => sq_nonneg _)
  intro o ho
  exact squaredLoss_of_right_target_and_left_test (T o) (tau P) m a ha hτ ho

/-- A concentrated prior turns a sample-event loss into a Bayes-risk bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `Good`](hyp:Good), [the specified input `loss`](hyp:loss), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the specified input `hgood`](hyp:hgood), [the specified input `hlossint`](hyp:hlossint), [the specified input `hloss_nonneg`](hyp:hloss_nonneg), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `π`](hyp:π), [the specified input `E`](hyp:E), [the specified input `hloss_good`](hyp:hloss_good). -/
-- @node: priorAverage_eventRisk_lower
lemma priorAverage_eventRisk_lower {n d : ℕ} {q β : ℝ}
    (π : PMF (ClassLaw d q)) (E : Set (Fin n → Obs d))
    (Good : ClassLaw d q → Prop) (loss : ClassLaw d q → ℝ)
    (a : ℝ) (ha : 0 ≤ a)
    (hgood : 1 - β ≤ priorEventMass d q π Good)
    (hlossint : Integrable loss π.toMeasure)
    (hloss_nonneg : ∀ P, 0 ≤ loss P)
    (hloss_good : ∀ P, Good P →
      a * (samplePi P.val n).real E ≤ loss P) :
    a * ((priorPredictive n d q π).real E - β) ≤
      ∫ P, loss P ∂π.toMeasure := by
  classical
  let f : ClassLaw d q → ℝ := fun P => (samplePi P.val n).real E
  let bad : ClassLaw d q → ℝ := fun P =>
    if Good P then 0 else 1
  have hbad : (∫ P, bad P ∂π.toMeasure) ≤ β := by
    have hfail := priorEventMass_failure_le π Good hgood
    have hbad_eq : (∫ P, bad P ∂π.toMeasure) =
        priorEventMass d q π (fun P => ¬ Good P) := by
      unfold priorEventMass
      have hmeas : MeasurableSet {P : ClassLaw d q | ¬ Good P} := trivial
      have hpoint : bad = {P : ClassLaw d q | ¬ Good P}.indicator (fun _ => 1) := by
        funext P
        by_cases h : Good P <;> simp [bad, Set.indicator, h]
      change (∫ P, bad P ∂π.toMeasure) = π.toMeasure.real {P | ¬ Good P}
      rw [hpoint, integral_indicator hmeas]
      simp
    exact hbad_eq.trans_le hfail
  have hf_le (P : ClassLaw d q) : f P ≤ 1 := by
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    exact measureReal_le_one
  have hpoint (P : ClassLaw d q) : a * f P - a * bad P ≤ loss P := by
    by_cases h : Good P
    · simpa [bad, h, f] using hloss_good P h
    · have hnonneg := hloss_nonneg P
      have := mul_le_mul_of_nonneg_left (hf_le P) ha
      simp [bad, h]
      linarith
  have hfint : Integrable f π.toMeasure := by
    have hm : Measurable f := by intro s hs; trivial
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with P
    have hnonneg : 0 ≤ f P := measureReal_nonneg
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hf_le P⟩
  have hbadint : Integrable bad π.toMeasure := by
    have hm : Measurable bad := by intro s hs; trivial
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with P
    by_cases h : Good P <;> simp [bad, h]
  have hbound : (∫ P, a * f P - a * bad P ∂π.toMeasure) ≤
      ∫ P, loss P ∂π.toMeasure :=
    integral_mono (hfint.const_mul a |>.sub (hbadint.const_mul a))
      hlossint hpoint
  have hpred := priorPredictive_event_eq_integral n d q π E
  have hlin : (∫ P, a * f P - a * bad P ∂π.toMeasure) =
      a * (priorPredictive n d q π).real E -
        a * (∫ P, bad P ∂π.toMeasure) := by
    rw [integral_sub (hfint.const_mul a) (hbadint.const_mul a)]
    simp only [integral_const_mul]
    rw [hpred]
  rw [hlin] at hbound
  have := mul_le_mul_of_nonneg_left hbad ha
  nlinarith

/-- The bounded squared loss can be averaged under any legal-law prior. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `T`](hyp:T), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π). -/
-- @node: pointRisk_integrable_prior
lemma pointRisk_integrable_prior {n d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (T : Estimator n d) :
    Integrable (fun P : ClassLaw d q =>
      ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n) π.toMeasure := by
  have hmeas : Measurable (fun P : ClassLaw d q =>
      ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n) := by
    intro s hs
    trivial
  apply Integrable.of_bound hmeas.aestronglyMeasurable 4
  filter_upwards [] with P
  haveI : IsProbabilityMeasure (samplePi P.val n) := by
    unfold samplePi
    infer_instance
  have hlo : 0 ≤ ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n :=
    integral_nonneg (fun o => sq_nonneg _)
  have hhi : (∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n) ≤ 4 := by
    have hpoint (o : Fin n → Obs d) :
        (T o - tau P.val) ^ 2 ≤ 4 := by
      have hT := T.range o
      have hτ := tau_range P.val
      rcases hT with ⟨hT0, hT1⟩
      rcases hτ with ⟨hτ0, hτ1⟩
      nlinarith [sq_nonneg (T o + 1), sq_nonneg (1 - T o),
        sq_nonneg (tau P.val + 1), sq_nonneg (1 - tau P.val)]
    have hInt : Integrable (fun o : Fin n → Obs d =>
        (T o - tau P.val) ^ 2) (samplePi P.val n) := Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 4) hpoint)
  simp only [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, hhi⟩

/-- Two concentrated target priors force the sum of their Bayes squared risks. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `T`](hyp:T), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `ha`](hyp:ha), [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `πminus`](hyp:πminus), [the specified input `πplus`](hyp:πplus), [the specified input `htv`](hyp:htv), [the specified input `hminus`](hyp:hminus), [the specified input `hplus`](hyp:hplus). -/
-- @node: priorPointTest_BayesSum_lower
lemma priorPointTest_BayesSum_lower {n d : ℕ} {q β : ℝ}
    (πminus πplus : PMF (ClassLaw d q)) (T : Estimator n d)
    (m a : ℝ) (ha : 0 ≤ a)
    (htv : Causalean.Stat.tvDist
      (priorPredictive n d q πminus) (priorPredictive n d q πplus) ≤ β)
    (hminus : 1 - β ≤ priorEventMass d q πminus
      (fun P => tau P.val ≤ m - a))
    (hplus : 1 - β ≤ priorEventMass d q πplus
      (fun P => m + a ≤ tau P.val)) :
    a ^ 2 * (1 - 3 * β) ≤
      (∫ P : ClassLaw d q, ∫ o, (T o - tau P.val) ^ 2
        ∂samplePi P.val n ∂πminus.toMeasure) +
      (∫ P : ClassLaw d q, ∫ o, (T o - tau P.val) ^ 2
        ∂samplePi P.val n ∂πplus.toMeasure) := by
  let E : Set (Fin n → Obs d) := {o | m ≤ T o}
  let loss : ClassLaw d q → ℝ := fun P =>
    ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n
  have hloss_nonneg (P : ClassLaw d q) : 0 ≤ loss P :=
    integral_nonneg (fun o => sq_nonneg _)
  have hleft : a ^ 2 * ((priorPredictive n d q πminus).real E - β) ≤
      ∫ P, loss P ∂πminus.toMeasure := by
    apply priorAverage_eventRisk_lower πminus E
      (fun P => tau P.val ≤ m - a) loss (a ^ 2) (sq_nonneg _) hminus
      (pointRisk_integrable_prior πminus T) hloss_nonneg
    intro P hP
    exact leftPrior_sampleRisk_lower P.val T m a ha hP
  have hright : a ^ 2 * ((priorPredictive n d q πplus).real Eᶜ - β) ≤
      ∫ P, loss P ∂πplus.toMeasure := by
    apply priorAverage_eventRisk_lower πplus Eᶜ
      (fun P => m + a ≤ tau P.val) loss (a ^ 2) (sq_nonneg _) hplus
      (pointRisk_integrable_prior πplus T) hloss_nonneg
    intro P hP
    apply sampleIntegral_ge_event P.val Eᶜ
      (fun o => (T o - tau P.val) ^ 2) (a ^ 2) (fun o => sq_nonneg _)
    intro o ho
    apply squaredLoss_of_right_target_and_left_test (T o) (tau P.val) m a ha hP
    have : ¬ m ≤ T o := ho
    linarith
  haveI := priorPredictive_isProbability n d q πminus
  haveI := priorPredictive_isProbability n d q πplus
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have htvE := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := priorPredictive n d q πminus)
    (ν := priorPredictive n d q πplus) hE
  have htransfer :
      (priorPredictive n d q πminus).real E +
        (priorPredictive n d q πplus).real Eᶜ ≥ 1 - β := by
    rw [probReal_compl_eq_one_sub hE]
    have := (abs_le.mp htvE).1
    linarith
  dsimp [loss] at hleft hright ⊢
  nlinarith

/-- A connected interval hitting both separated target regions has length at least `2a`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `I`](hyp:I), [the specified input `o`](hyp:o), [the specified input `m`](hyp:m), [the specified input `a`](hyp:a), [the specified input `xL`](hyp:xL), [the specified input `xR`](hyp:xR), [the specified input `hleft`](hyp:hleft), [the specified input `hright`](hyp:hright), [the stated mathematical conclusion holds](goal). Given [the specified input `hL`](hyp:hL), [the specified input `hR`](hyp:hR). -/
-- @node: interval_length_of_separated_hits
lemma interval_length_of_separated_hits {n d : ℕ} (I : IntervalProc n d)
    (o : Fin n → Obs d) (m a xL xR : ℝ)
    (hL : xL ∈ Set.Icc (I.lo o) (I.hi o))
    (hR : xR ∈ Set.Icc (I.lo o) (I.hi o))
    (hleft : xL ≤ m - a) (hright : m + a ≤ xR) :
    2 * a ≤ I.hi o - I.lo o := by
  rcases hL with ⟨hlo, _⟩
  rcases hR with ⟨_, hhi⟩
  linarith

-- @node: pointMinimaxRisk_lower_of_pair
/-- A two-law risk bound passes through the supremum and estimator infimum. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the specified input `Pminus`](hyp:Pminus), [the specified input `Pplus`](hyp:Pplus), [the stated mathematical conclusion holds](goal). Given [the specified input `h`](hyp:h). -/
lemma pointMinimaxRisk_lower_of_pair {n d : ℕ} {q c : ℝ}
    (Pminus Pplus : ClassLaw d q)
    (h : ∀ T : Estimator n d,
      c ≤ max
        (∫ o, (T o - tau Pminus.val) ^ 2 ∂samplePi Pminus.val n)
        (∫ o, (T o - tau Pplus.val) ^ 2 ∂samplePi Pplus.val n)) :
    c ≤ pointMinimaxRisk n d q := by
  letI : Nonempty (Estimator n d) :=
    ⟨⟨fun _ => 0, measurable_const, fun _ => by constructor <;> norm_num⟩⟩
  unfold pointMinimaxRisk
  refine le_ciInf fun T => ?_
  have hb : BddAbove (Set.range fun P : ClassLaw d q =>
      ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n) := by
    refine ⟨4, ?_⟩
    rintro y ⟨P, rfl⟩
    letI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hrange (o : Fin n → Obs d) :
        (T o - tau P.val) ^ 2 ≤ 4 := by
      have hT := T.range o
      have hτ := tau_range P.val
      rcases hT with ⟨hT0, hT1⟩
      rcases hτ with ⟨hτ0, hτ1⟩
      nlinarith [sq_nonneg (T o + 1), sq_nonneg (1 - T o),
        sq_nonneg (tau P.val + 1), sq_nonneg (1 - tau P.val)]
    have hInt : Integrable (fun o => (T o - tau P.val) ^ 2)
        (samplePi P.val n) := Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 4) hrange)
  have hm :
      (∫ o, (T o - tau Pminus.val) ^ 2 ∂samplePi Pminus.val n) ≤
        ⨆ P : ClassLaw d q,
          ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n :=
    le_ciSup hb Pminus
  have hp :
      (∫ o, (T o - tau Pplus.val) ^ 2 ∂samplePi Pplus.val n) ≤
        ⨆ P : ClassLaw d q,
          ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n :=
    le_ciSup hb Pplus
  exact (h T).trans (max_le hm hp)

-- @node: lengthMinimaxRisk_lower_of_law
/-- A fixed legal law gives a lower bound on every honest interval's worst-law length. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α), [the specified input `hα`](hyp:hα). Given [the specified input `h`](hyp:h). -/
lemma lengthMinimaxRisk_lower_of_law {n d : ℕ} {q α c : ℝ}
    (P : ClassLaw d q) (hα : 0 ≤ α)
    (h : ∀ I : HonestIntervalClass n d q α,
      c ≤ ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P.val n) :
    c ≤ lengthMinimaxRisk n d q α := by
  let Iall : IntervalProc n d :=
    ⟨fun _ => -1, fun _ => 1, measurable_const, measurable_const,
      fun _ => by constructor <;> norm_num⟩
  letI : Nonempty (HonestIntervalClass n d q α) :=
    ⟨⟨Iall, fun P' => by
      haveI : IsProbabilityMeasure (samplePi P'.val n) := by
        unfold samplePi
        infer_instance
      have hτ := tau_range P'.val
      have hevent : {o : Fin n → Obs d |
          tau P'.val ∈ Set.Icc (Iall.lo o) (Iall.hi o)} = Set.univ := by
        ext o
        simp [Iall, hτ]
      rw [hevent, probReal_univ]
      linarith⟩⟩
  unfold lengthMinimaxRisk
  refine le_ciInf fun I => ?_
  have hb : BddAbove (Set.range fun P' : ClassLaw d q =>
      ∫ o, (I.val.hi o - I.val.lo o) ∂samplePi P'.val n) := by
    refine ⟨2, ?_⟩
    rintro y ⟨P', rfl⟩
    letI : IsProbabilityMeasure (samplePi P'.val n) := by
      unfold samplePi
      infer_instance
    have hrange (o : Fin n → Obs d) :
        I.val.hi o - I.val.lo o ≤ 2 := by
      have hI := I.val.bounds o
      linarith
    have hInt : Integrable (fun o => I.val.hi o - I.val.lo o)
        (samplePi P'.val n) := Integrable.of_finite
    simpa using (integral_mono hInt (integrable_const 2) hrange)
  exact (h I).trans (le_ciSup hb P)

-- @node: priorAverage_le_of_pointwise
/-- A pointwise risk bound also bounds its average under any legal-law prior. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `f`](hyp:f), [the specified input `R`](hyp:R), [the specified input `hf`](hyp:hf), [the specified input `hR`](hyp:hR), [the stated mathematical conclusion holds](goal). Given [the specified input `π`](hyp:π). -/
lemma priorAverage_le_of_pointwise {d : ℕ} {q : ℝ}
    (π : PMF (ClassLaw d q)) (f : ClassLaw d q → ℝ) (R : ℝ)
    (hf : Integrable f π.toMeasure) (hR : ∀ P, f P ≤ R) :
    (∫ P, f P ∂π.toMeasure) ≤ R := by
  haveI : IsProbabilityMeasure π.toMeasure := inferInstance
  simpa using (integral_mono hf (integrable_const R) hR)

/-- A Bayes-risk lower bound under two legal priors passes to minimax risk. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `c`](hyp:c), [the stated mathematical conclusion holds](goal). Given [the specified input `πminus`](hyp:πminus), [the specified input `πplus`](hyp:πplus), [the specified input `h`](hyp:h). -/
-- @node: pointMinimaxRisk_lower_of_priors
lemma pointMinimaxRisk_lower_of_priors {n d : ℕ} {q c : ℝ}
    (πminus πplus : PMF (ClassLaw d q))
    (h : ∀ T : Estimator n d,
      2 * c ≤
        (∫ P : ClassLaw d q, ∫ o, (T o - tau P.val) ^ 2
          ∂samplePi P.val n ∂πminus.toMeasure) +
        (∫ P : ClassLaw d q, ∫ o, (T o - tau P.val) ^ 2
          ∂samplePi P.val n ∂πplus.toMeasure)) :
    c ≤ pointMinimaxRisk n d q := by
  letI : Nonempty (Estimator n d) :=
    ⟨⟨fun _ => 0, measurable_const, fun _ => by constructor <;> norm_num⟩⟩
  unfold pointMinimaxRisk
  refine le_ciInf fun T => ?_
  let risk : ClassLaw d q → ℝ := fun P =>
    ∫ o, (T o - tau P.val) ^ 2 ∂samplePi P.val n
  have hb : BddAbove (Set.range risk) := by
    refine ⟨4, ?_⟩
    rintro y ⟨P, rfl⟩
    haveI : IsProbabilityMeasure (samplePi P.val n) := by
      unfold samplePi
      infer_instance
    have hpoint (o : Fin n → Obs d) : (T o - tau P.val) ^ 2 ≤ 4 := by
      have hT := T.range o
      have hτ := tau_range P.val
      rcases hT with ⟨hT0, hT1⟩
      rcases hτ with ⟨hτ0, hτ1⟩
      nlinarith [sq_nonneg (T o + 1), sq_nonneg (1 - T o),
        sq_nonneg (tau P.val + 1), sq_nonneg (1 - tau P.val)]
    have hInt : Integrable (fun o : Fin n → Obs d =>
        (T o - tau P.val) ^ 2) (samplePi P.val n) := Integrable.of_finite
    simpa [risk] using (integral_mono hInt (integrable_const 4) hpoint)
  let R : ℝ := ⨆ P : ClassLaw d q, risk P
  have hpoint (P : ClassLaw d q) : risk P ≤ R := le_ciSup hb P
  have hm := priorAverage_le_of_pointwise πminus risk R
    (pointRisk_integrable_prior πminus T) hpoint
  have hp := priorAverage_le_of_pointwise πplus risk R
    (pointRisk_integrable_prior πplus T) hpoint
  have hbayes := h T
  dsimp [risk, R] at hm hp ⊢
  linarith

/-- The normalized converse gives the stated `13/32` point-risk coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hlarge`](hyp:hlarge). -/
-- @node: priorPointRisk_separation
lemma priorPointRisk_separation (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hlarge : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) :
    (13 / 32 : ℝ) * converseConstant pointBeta pointBeta_valid ^ 2 *
      gScale n d q ^ 2 ≤ pointMinimaxRisk n d q := by
  obtain ⟨πminus, πplus, htv, m, hm, hp⟩ :=
    (converseConstant_spec pointBeta pointBeta_valid).2 n d q hn hd hq hlarge
  let a := converseConstant pointBeta pointBeta_valid * gScale n d q
  have ha : 0 ≤ a := mul_nonneg
    (le_of_lt (converseConstant_spec pointBeta pointBeta_valid).1)
    (gScale_nonneg_of_q n d q hq)
  apply pointMinimaxRisk_lower_of_priors πminus πplus
  intro T
  have hsum := priorPointTest_BayesSum_lower πminus πplus T m a ha htv hm hp
  dsimp [a, pointBeta] at hsum ⊢
  nlinarith

end CausalSmith.Stat.MarNearcompleteFrontier
