module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.CrossRegularity
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.NoCommonJumps
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PathwiseCrossAlgebra

/-!
# Strict-past cross products for full-sample predictable integrands

This generalizes the public counting-process cross-prefix proof pattern to
finite recurrent-event paths. A product expansion and compensation of its two
predictable cross payoffs establish orthogonality without integral independence.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- On paths with disjoint stopped subject jumps, the product of their
compensated integrals equals two oriented cross jump sums minus their two
oriented compensator integrals. [The sample model and payoff](hyp:S,H), [left
predictability](hyp:hH), [boundedness](hyp:hbound), [the two indices and
path](hyp:i,j,x), and [their disjoint jumps](hyp:hdisjoint) give [the
pathwise product expansion](goal). -/
theorem SampleModel.subject_product_pathwise (S : SampleModel n Ω μ)
    (H : ℝ → (Fin n → Ω) → ℝ) (hH : S.LeftPredictable H)
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C) (i j : Fin n)
    (x : Fin n → Ω)
    (hdisjoint : Disjoint ((S.process i).eventTimes x) ((S.process j).eventTimes x)) :
    S.subjectIntegral H i x * S.subjectIntegral H j x =
      (S.process i).jumpIntegral (S.crossPayoff H j) (S.process i).horizon x +
      (S.process j).jumpIntegral (S.crossPayoff H i) (S.process j).horizon x -
      (S.process i).energyIntegral (S.crossPayoff H j) (S.process i).horizon x -
      (S.process j).energyIntegral (S.crossPayoff H i) (S.process j).horizon x := by
  /- Instantiate finiteJump_sum_product on the two event sets, and
     finiteJump_sum_integral_product in both orientations with the respective
     H-weighted rates. Use integral_prefix_product for the two continuous
     parts. Every component horizon is S.horizon by process_horizon.
     The existing square_pathwise proof gives the local measurability,
     bounded strict-prefix and continuous-prefix integrability needed to
     distribute subtraction through the two time integrals. Assemble the
     identities with finite-sum linearity and ring; no moment premise enters.
     All three deterministic prerequisites in PathwiseCrossAlgebra are now
     proved. This is the only open proof in the dependency closure.

     Work at a fixed x with T := S.horizon, E := (S.process i).eventTimes x,
     F := (S.process j).eventTimes x, f t := H t x * rate_i t and
     g t := H t x * rate_j t. Weighted-rate integrability follows exactly
     as hf in Model.square_pathwise (joint measurability from predictability,
     dominated by |C| times the integrable absolute rate). Strict jump-prefix
     functions are measurable finite sums of Ioi indicators and bounded by
     the finite sum of absolute event payoffs. Continuous prefixes are
     continuous on Icc 0 T by the interval primitive theorem, hence bounded;
     their products with either weighted rate are integrable. These facts
     justify integral_sub when expanding each cross energy payoff.

     Model.events_in_horizon removes each t ≤ horizon event filter. The
     mixed sum/integral identities are instantiated twice; the continuous
     product identity supplies both continuous-prefix terms. Normalize
     crossPayoff, prefixIntegral, energyIntegral and the common horizons,
     distribute finite sums and the justified time subtractions, then ring
     with the four deterministic equalities. Do not add any hypothesis or
     invoke probabilistic independence in this pathwise proof. -/
  classical
  let T := S.horizon
  let E (k : Fin n) := (S.process k).eventTimes x
  let r (k : Fin n) (t : ℝ) :=
    (S.process k).atRisk t x * (S.process k).intensity t x
  let f (k : Fin n) (t : ℝ) := H t x * r k t
  let J (k : Fin n) (t : ℝ) := ∑ s ∈ (E k).filter (fun s => s < t), H s x
  let A (k : Fin n) (t : ℝ) := ∫ s in Set.Ioc 0 t, f k s ∂volume
  have hT : 0 ≤ T := S.horizon_pos.le
  have hE (k : Fin n) (t : ℝ) (ht : t ∈ E k) : 0 < t ∧ t ≤ T := by
    simpa only [S.process_horizon] using (S.process k).events_in_horizon x t ht
  have hfilter (k : Fin n) : (E k).filter (fun t => t ≤ T) = E k :=
    Finset.filter_eq_self.mpr (fun t ht => (hE k t ht).2)
  have hHm : Measurable (fun t => H t x) :=
    ((S.process i).predictable_joint_measurable H (S.process_predictable H hH i)).comp
      (measurable_id.prodMk measurable_const)
  obtain ⟨C, hC⟩ := hbound
  have hf (k : Fin n) : IntegrableOn (f k) (Set.Ioc 0 T) volume := by
    have hrm : Measurable (r k) :=
      ((S.process k).atRisk_joint_measurable.comp
        (measurable_id.prodMk measurable_const)).mul
      ((S.process k).intensity_joint_measurable.comp
        (measurable_id.prodMk measurable_const))
    have hr : Integrable (r k) (volume.restrict (Set.Ioc 0 T)) := by
      simpa only [S.process_horizon, r, T, IntegrableOn] using (S.process k).rate_integrable x
    apply Integrable.mono' (hr.abs.const_mul |C|)
    · exact (hHm.mul hrm).aestronglyMeasurable
    · filter_upwards with t
      simp only [Real.norm_eq_abs, f, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hC t x).trans (le_abs_self C))
        (abs_nonneg (r k t))
  have hJm (k : Fin n) : Measurable (J k) := by
    dsimp [J]
    simp_rw [Finset.sum_filter]
    apply Finset.measurable_sum
    intro s hs
    exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hJbound (k : Fin n) (t : ℝ) : |J k t| ≤ ∑ s ∈ E k, |H s x| := by
    calc
      _ ≤ ∑ s ∈ (E k).filter (fun s => s < t), |H s x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro s hs hns; exact abs_nonneg _)
  have hJf (k l : Fin n) :
      IntegrableOn (fun t => J k t * f l t) (Set.Ioc 0 T) volume := by
    apply (hf l).bdd_mul (c := ∑ s ∈ E k, |H s x|) (hJm k).aestronglyMeasurable
    filter_upwards with t
    simpa only [Real.norm_eq_abs] using hJbound k t
  have hAf (k l : Fin n) :
      IntegrableOn (fun t => A k t * f l t) (Set.Ioc 0 T) volume := by
    let B : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f k s
    have hki : IntervalIntegrable (f k) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hf k)
    have hli : IntervalIntegrable (f l) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hf l)
    have hB : ContinuousOn B (Set.uIcc 0 T) :=
      (hki.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
    have hb := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      (hli.continuousOn_mul hB)
    apply hb.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [B, A, intervalIntegral.integral_of_le ht.1.le]
  have hcross (k l : Fin n) :
      (S.process k).energyIntegral (S.crossPayoff H l) (S.process k).horizon x =
      (∫ t in Set.Ioc 0 T, J l t * f k t ∂volume) -
      ∫ t in Set.Ioc 0 T, A l t * f k t ∂volume := by
    unfold Model.energyIntegral SampleModel.crossPayoff Model.prefixIntegral
    rw [S.process_horizon k]
    calc
      _ = ∫ t in Set.Ioc 0 T, (J l t * f k t - A l t * f k t) ∂volume := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [J, A, f, r, E, Model.energyIntegral]
        ring
      _ = _ := integral_sub (hJf l k) (hAf l k)
  have hj := finiteJump_sum_product (E i) (E j) (fun t => H t x)
    (fun t => H t x) hdisjoint
  have hij := finiteJump_sum_integral_product (E i) (fun t => H t x)
    (f j) T hT (hE i) (hf j)
  have hji := finiteJump_sum_integral_product (E j) (fun t => H t x)
    (f i) T hT (hE j) (hf i)
  have ha := integral_prefix_product (f i) (f j) T hT (hf i) (hf j)
  rw [hcross i j, hcross j i]
  unfold SampleModel.subjectIntegral Model.stochasticIntegral Model.jumpIntegral
    Model.energyIntegral SampleModel.crossPayoff Model.prefixIntegral
  simp only [S.process_horizon]
  change ((∑ s ∈ (E i).filter (fun t => t ≤ T), H s x) - A i T) *
    ((∑ s ∈ (E j).filter (fun t => t ≤ T), H s x) - A j T) =
    (∑ s ∈ (E i).filter (fun t => t ≤ T), H s x * (J j s - A j s)) +
    (∑ s ∈ (E j).filter (fun t => t ≤ T), H s x * (J i s - A i s)) -
    ((∫ t in Set.Ioc 0 T, J j t * f i t ∂volume) -
      ∫ t in Set.Ioc 0 T, A j t * f i t ∂volume) -
    ((∫ t in Set.Ioc 0 T, J i t * f j t ∂volume) -
      ∫ t in Set.Ioc 0 T, A i t * f j t ∂volume)
  rw [hfilter i, hfilter j]
  simp only [mul_sub, Finset.sum_sub_distrib]
  dsimp only [J, A] at ⊢
  nlinarith [hj, hij, hji, ha]

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
