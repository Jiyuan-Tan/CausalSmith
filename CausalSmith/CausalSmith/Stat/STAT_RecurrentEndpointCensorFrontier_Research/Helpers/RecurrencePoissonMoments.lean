module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Main
public import Causalean.Stat.RecurrentEvent.PoissonCampbell
public import Mathlib.Probability.Moments.Variance

/-!
# Campbell and second moments for recurrence scores

Convert the nonnegative finite-Poisson Campbell formula into a signed
expectation identity, with integrability proved from that of the point score.
The compensated second moment equals the point-score energy, and independent
subject scores have additive energy. These calculations apply conditionally on
the independent exposure array; they preserve the full time-dependent score.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

variable {X : Type*} [MeasurableSpace X]

/-- A measurable point score has a measurable finite-configuration sum. -/
-- @node: measurable_recurrence_poisson_sum
@[fun_prop] lemma measurable_recurrence_poisson_sum (f : X → ℝ)
    (hf : Measurable f) :
    Measurable (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i)) := by
  classical
  intro t ht
  change @MeasurableSet _
    (⨅ n, (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n))
    ((fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i)) ⁻¹' t)
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((fun x : Fin n → X => ∑ i, f (x i)) ⁻¹' t)
  exact (Finset.measurable_sum _
    (fun i _ => hf.comp (measurable_pi_apply i))) ht

/-- Nonnegative integrable scores have integrable Poisson sums and the
expected sum is the rate times the point-score expectation. -/
-- @node: recurrence_poisson_sum_nonneg_moment
lemma recurrence_poisson_sum_nonneg_moment (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f P) (hn : ∀ x, 0 ≤ f x) :
    Integrable (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i))
      (finitePoissonSampleLaw P rate) ∧
    (∫ s, ∑ i : Fin s.1, f (s.2 i) ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ) * ∫ x, f x ∂P := by
  classical
  have hm := measurable_recurrence_poisson_sum f hf
  have hs (s : FiniteSample X) : 0 ≤ ∑ i : Fin s.1, f (s.2 i) :=
    Finset.sum_nonneg (fun i _ => hn _)
  have hc : (∫⁻ s, ENNReal.ofReal (∑ i : Fin s.1, f (s.2 i))
      ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (f x) ∂P := by
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hn _)]
    rw [Causalean.Stat.RecurrentEvent.finitePoissonSample_lintegral_sum P rate
      _ (hf.ennreal_ofReal), lintegral_smul_measure, smul_eq_mul]
  have hi : Integrable (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i))
      (finitePoissonSampleLaw P rate) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [Real.norm_of_nonneg (hs _)]
    rw [hc]
    exact ENNReal.mul_lt_top (by simp) (by
      simpa only [Real.norm_of_nonneg (hn _)] using
        ((hasFiniteIntegral_iff_norm f).mp hfi.hasFiniteIntegral))
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hs)
    hm.aestronglyMeasurable, hc, ENNReal.toReal_mul]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn)
    hf.aestronglyMeasurable]
  simp

/-- An integrable signed score has an integrable Poisson sum whose mean
is the intensity-weighted mean of the score. -/
-- @node: recurrence_poisson_sum_signed_campbell
lemma recurrence_poisson_sum_signed_campbell (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f P) :
    Integrable (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i))
      (finitePoissonSampleLaw P rate) ∧
    (∫ s, ∑ i : Fin s.1, f (s.2 i) ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ) * ∫ x, f x ∂P := by
  classical
  obtain ⟨hp, hep⟩ := recurrence_poisson_sum_nonneg_moment P rate
    (fun x => max (f x) 0) (by fun_prop) hfi.pos_part
    (fun x => le_max_right _ _)
  obtain ⟨hm, hem⟩ := recurrence_poisson_sum_nonneg_moment P rate
    (fun x => max (-f x) 0) (by fun_prop) hfi.neg_part
    (fun x => le_max_right _ _)
  have hd (x : X) : f x = max (f x) 0 - max (-f x) 0 := by
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr
        (le_of_not_ge hx))]; ring
  have hsum : (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i)) =
      fun s => (∑ i : Fin s.1, max (f (s.2 i)) 0) -
        ∑ i : Fin s.1, max (-f (s.2 i)) 0 := by
    funext s
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hd (s.2 i))
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact hp.sub hm
  rw [hsum, integral_sub hp hm, hep, hem, ← mul_sub]
  congr 1
  rw [← integral_sub hfi.pos_part hfi.neg_part]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (hd x).symm)

/-- The compensated signed Poisson score is integrable and centered. -/
-- @node: recurrence_poisson_compensated_mean_zero
lemma recurrence_poisson_compensated_mean_zero (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f P) :
    Integrable (fun s : FiniteSample X =>
      (∑ i : Fin s.1, f (s.2 i)) - (rate : ℝ) * ∫ x, f x ∂P)
        (finitePoissonSampleLaw P rate) ∧
    (∫ s, (∑ i : Fin s.1, f (s.2 i)) - (rate : ℝ) * ∫ x, f x ∂P
      ∂finitePoissonSampleLaw P rate) = 0 := by
  obtain ⟨hi, he⟩ := recurrence_poisson_sum_signed_campbell P rate f hf hfi
  refine ⟨hi.sub (integrable_const _), ?_⟩
  rw [integral_sub hi (integrable_const _), he, integral_const]
  simp

/-- The expected diagonal energy of a weighted Poisson sum is the rate
times the point-score squared integral. No endpoint supremum is taken. -/
-- @node: recurrence_poisson_diagonal_energy
lemma recurrence_poisson_diagonal_energy (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) P) :
    Integrable (fun s : FiniteSample X => ∑ i : Fin s.1, f (s.2 i) ^ 2)
      (finitePoissonSampleLaw P rate) ∧
    (∫ s, ∑ i : Fin s.1, f (s.2 i) ^ 2 ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ) * ∫ x, f x ^ 2 ∂P := by
  exact recurrence_poisson_sum_nonneg_moment P rate (fun x => f x ^ 2)
    (by fun_prop) hf2 (fun x => sq_nonneg _)

/-- The independent auxiliary Poisson count has unit rate and second moment two. -/
-- @node: recurrence_poisson_unit_count_second_moment
lemma recurrence_poisson_unit_count_second_moment :
    (∫ t : FiniteSample Unit, (t.1 : ℝ) ^ 2
      ∂finitePoissonSampleLaw (Measure.dirac ()) 1) = 2 := by
  have hm := finitePoissonSampleLaw_map_count (Measure.dirac ()) (1 : ℝ≥0)
  have ht := integral_map measurable_finiteSample_count.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun n : ℕ => (n : ℝ) ^ 2)
      (Measure.map FiniteSample.count
        (finitePoissonSampleLaw (Measure.dirac ()) 1)))
  rw [hm] at ht
  simpa [FiniteSample.count, Nat.cast_ofNat,
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment,
    show (1 : ℝ) + 1 = 2 by norm_num]
    using ht.symm

/-- The raw second moment of a weighted Poisson sum consists of its diagonal
energy and the squared mean. The independent auxiliary stream is eliminated
using its exact count second moment. -/
-- @node: recurrence_poisson_sum_second_moment
lemma recurrence_poisson_sum_second_moment (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) P) :
    Integrable (fun s : FiniteSample X => (∑ i : Fin s.1, f (s.2 i)) ^ 2)
      (finitePoissonSampleLaw P rate) ∧
    (∫ s, (∑ i : Fin s.1, f (s.2 i)) ^ 2 ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ) * ∫ x, f x ^ 2 ∂P +
        ((rate : ℝ) * ∫ x, f x ∂P) ^ 2 := by
  classical
  let Q : Measure Unit := Measure.dirac ()
  let K : X → Unit → ℝ := fun x _ => f x
  let μ := finitePoissonSampleLaw P rate
  let ν := finitePoissonSampleLaw Q 1
  let S (s : FiniteSample X) : ℝ := ∑ i : Fin s.1, f (s.2 i)
  have hK : Measurable (Function.uncurry K) := by fun_prop
  have hK2 : Integrable (fun p : X × Unit => K p.1 p.2 ^ 2) (P.prod Q) :=
    hf2.comp_fst Q
  have hp := Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integrable_pairSum_sq
    P Q rate 1 K hK hK2
  have he := Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_pairSum_sq
    P Q rate 1 K hK hK2
  have hpair (s : FiniteSample X) (t : FiniteSample Unit) :
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum K s t ^ 2 =
        S s ^ 2 * (t.1 : ℝ) ^ 2 := by
    simp only [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum,
      K, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, S, mul_pow]
    ring
  have hinner (s : FiniteSample X) :
      (∫ t, Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum K s t ^ 2
        ∂ν) = S s ^ 2 * 2 := by
    simp_rw [hpair]
    rw [integral_const_mul]
    exact congrArg (S s ^ 2 * ·) recurrence_poisson_unit_count_second_moment
  have hi : Integrable (fun s => S s ^ 2) μ := by
    have hi := hp.integral_prod_left
    change Integrable (fun s => ∫ t,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum K s t ^ 2 ∂ν) μ at hi
    simp_rw [hinner] at hi
    have := hi.mul_const (1 / 2 : ℝ)
    convert this using 1
    ext s
    ring
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hp] at he
  change (∫ s, ∫ t,
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum K s t ^ 2 ∂ν ∂μ) = _ at he
  simp_rw [hinner] at he
  rw [integral_mul_const] at he
  simp only [K, Q, integral_dirac, NNReal.coe_one, mul_one, one_pow] at he
  simp_rw [integral_const_mul, integral_mul_const] at he
  simp only [← pow_two] at he
  change (∫ s, S s ^ 2 ∂μ) = _
  nlinarith [he]

/-- The centered weighted Poisson score has exactly its diagonal energy as
second moment. In particular, no supremum of the time-dependent score enters
the bound. -/
-- @node: recurrence_poisson_compensated_second_moment
lemma recurrence_poisson_compensated_second_moment (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (f : X → ℝ)
    (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) P) :
    Integrable (fun s : FiniteSample X =>
      ((∑ i : Fin s.1, f (s.2 i)) - (rate : ℝ) * ∫ x, f x ∂P) ^ 2)
        (finitePoissonSampleLaw P rate) ∧
    (∫ s, ((∑ i : Fin s.1, f (s.2 i)) - (rate : ℝ) * ∫ x, f x ∂P) ^ 2
      ∂finitePoissonSampleLaw P rate) =
      (rate : ℝ) * ∫ x, f x ^ 2 ∂P := by
  have hfi : Integrable f P :=
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2).integrable
      (by norm_num)
  obtain ⟨hi, he⟩ := recurrence_poisson_sum_signed_campbell P rate f hf hfi
  obtain ⟨hi2, he2⟩ := recurrence_poisson_sum_second_moment P rate f hf hf2
  let m : ℝ := (rate : ℝ) * ∫ x, f x ∂P
  let S (s : FiniteSample X) : ℝ := ∑ i : Fin s.1, f (s.2 i)
  have hpoly (s : FiniteSample X) :
      (S s - m) ^ 2 = S s ^ 2 - 2 * m * S s + m ^ 2 := by ring
  have hlin : Integrable (fun s => 2 * m * S s)
      (finitePoissonSampleLaw P rate) := hi.const_mul _
  have hconst : Integrable (fun _ : FiniteSample X => m ^ 2)
      (finitePoissonSampleLaw P rate) := integrable_const _
  have hsub : Integrable (fun s => S s ^ 2 - 2 * m * S s)
      (finitePoissonSampleLaw P rate) := hi2.sub hlin
  have hint : Integrable (fun s => (S s - m) ^ 2)
      (finitePoissonSampleLaw P rate) := by
    simp_rw [hpoly]
    exact (hi2.sub hlin).add hconst
  refine ⟨hint, ?_⟩
  change (∫ s, (S s - m) ^ 2 ∂finitePoissonSampleLaw P rate) = _
  simp_rw [hpoly]
  rw [integral_add hsub hconst]
  change (∫ s, S s ^ 2 - 2 * m * S s ∂finitePoissonSampleLaw P rate) +
    (∫ _ : FiniteSample X, m ^ 2 ∂finitePoissonSampleLaw P rate) = _
  change Integrable (fun s => S s ^ 2) (finitePoissonSampleLaw P rate) at hi2
  rw [integral_sub hi2 hlin,
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  change (∫ s, S s ^ 2 ∂finitePoissonSampleLaw P rate) -
    2 * m * (∫ s, S s ∂finitePoissonSampleLaw P rate) + m ^ 2 = _
  rw [he2, he]
  dsimp only [m]
  ring

/-- For a fixed exposure array, independent recurrence configurations have
additive compensated energy, even when each subject has a different score. -/
-- @node: recurrence_poisson_iid_compensated_second_moment
lemma recurrence_poisson_iid_compensated_second_moment (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hf2 : ∀ i, Integrable (fun x => f i x ^ 2) P) :
    Integrable (fun z : Fin n → FiniteSample X =>
      (∑ j : Fin n, ((∑ i : Fin (z j).1, f j ((z j).2 i)) -
        (rate : ℝ) * ∫ x, f j x ∂P)) ^ 2)
      (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) ∧
    (∫ z : Fin n → FiniteSample X,
      (∑ j : Fin n, ((∑ i : Fin (z j).1, f j ((z j).2 i)) -
        (rate : ℝ) * ∫ x, f j x ∂P)) ^ 2
      ∂Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) =
      ∑ j : Fin n, (rate : ℝ) * ∫ x, f j x ^ 2 ∂P := by
  classical
  let μ := finitePoissonSampleLaw P rate
  let C (j : Fin n) (s : FiniteSample X) : ℝ :=
    (∑ i : Fin s.1, f j (s.2 i)) - (rate : ℝ) * ∫ x, f j x ∂P
  have hC (j : Fin n) : Measurable (C j) :=
    (measurable_recurrence_poisson_sum (f j) (hf j)).sub measurable_const
  have hC2 (j : Fin n) : Integrable (fun s => C j s ^ 2) μ :=
    (recurrence_poisson_compensated_second_moment P rate (f j) (hf j) (hf2 j)).1
  have hLp (j : Fin n) : MemLp (C j) 2 μ :=
    (memLp_two_iff_integrable_sq (hC j).aestronglyMeasurable).2 (hC2 j)
  have hmean (j : Fin n) : (∫ s, C j s ∂μ) = 0 := by
    have hfi := ((memLp_two_iff_integrable_sq (hf j).aestronglyMeasurable).2
      (hf2 j)).integrable (by norm_num)
    exact (recurrence_poisson_compensated_mean_zero P rate (f j) (hf j) hfi).2
  have he (j : Fin n) : (∫ s, C j s ^ 2 ∂μ) =
      (rate : ℝ) * ∫ x, f j x ^ 2 ∂P :=
    (recurrence_poisson_compensated_second_moment P rate (f j) (hf j) (hf2 j)).2
  have hcoord (j : Fin n) : MemLp (fun z : Fin n → FiniteSample X => C j (z j))
      2 (Measure.pi (fun _ : Fin n => μ)) :=
    (hLp j).comp_measurePreserving (measurePreserving_eval _ j)
  have hsum : MemLp (fun z : Fin n → FiniteSample X => ∑ j, C j (z j))
      2 (Measure.pi (fun _ : Fin n => μ)) := by
    exact memLp_finsetSum _ (fun j _ => hcoord j)
  have hsummean : (∫ z : Fin n → FiniteSample X, ∑ j, C j (z j)
      ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
    rw [integral_finsetSum _ (fun j _ => (hcoord j).integrable (by norm_num))]
    have hproj (j : Fin n) :
        (∫ z : Fin n → FiniteSample X, C j (z j)
          ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
      have hp := measurePreserving_eval (μ := fun _ : Fin n => μ) j
      rw [← integral_map hp.measurable.aemeasurable (hC j).aestronglyMeasurable,
        hp.map_eq, hmean]
    simp only [hproj, Finset.sum_const_zero]
  refine ⟨hsum.integrable_sq, ?_⟩
  have hv := variance_sum_pi hLp
  have hvs : variance (fun z : Fin n → FiniteSample X => ∑ j, C j (z j))
      (Measure.pi (fun _ : Fin n => μ)) =
        ∫ z : Fin n → FiniteSample X, (∑ j, C j (z j)) ^ 2
          ∂Measure.pi (fun _ : Fin n => μ) := by
    rw [variance_eq_integral hsum.aemeasurable, hsummean]
    simp only [sub_zero]
  have hvj (j : Fin n) : variance (C j) μ =
      (rate : ℝ) * ∫ x, f j x ^ 2 ∂P := by
    rw [variance_eq_integral (hC j).aemeasurable, hmean]
    simp only [sub_zero]
    exact he j
  change (∫ z : Fin n → FiniteSample X, (∑ j, C j (z j)) ^ 2
    ∂Measure.pi (fun _ : Fin n => μ)) = _
  rw [← hvs]
  have hfun : (∑ j : Fin n, fun z : Fin n → FiniteSample X => C j (z j)) =
      (fun z : Fin n → FiniteSample X => ∑ j, C j (z j)) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hfun] at hv
  rw [hv]
  exact Finset.sum_congr rfl (fun j _ => hvj j)

/-- The compensated recurrence score for an exposure-dependent array of
point scores. Each subject retains its own time-dependent score. -/
-- @node: recurrenceExposureScore
noncomputable def recurrenceExposureScore {E : Type*} (P : Measure X)
    (rate : ℝ≥0) (n : ℕ) (f : E → Fin n → X → ℝ)
    (e : E) (z : Fin n → FiniteSample X) : ℝ :=
  ∑ j : Fin n, ((∑ i : Fin (z j).1, f e j ((z j).2 i)) -
    (rate : ℝ) * ∫ x, f e j x ∂P)

/-- Independent compensated subject scores sum to an integrable centered
score for each fixed exposure array. -/
-- @node: recurrence_poisson_iid_compensated_mean_zero
lemma recurrence_poisson_iid_compensated_mean_zero (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ j, Measurable (f j)) (hfi : ∀ j, Integrable (f j) P) :
    Integrable (recurrenceExposureScore P rate n (fun _ : Unit => f) ())
      (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) ∧
    (∫ z, recurrenceExposureScore P rate n (fun _ : Unit => f) () z
      ∂Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) = 0 := by
  classical
  let μ := finitePoissonSampleLaw P rate
  let C (j : Fin n) (s : FiniteSample X) : ℝ :=
    (∑ i : Fin s.1, f j (s.2 i)) - (rate : ℝ) * ∫ x, f j x ∂P
  have hC (j : Fin n) : Measurable (C j) :=
    (measurable_recurrence_poisson_sum (f j) (hf j)).sub measurable_const
  have hi (j : Fin n) : Integrable (C j) μ :=
    (recurrence_poisson_compensated_mean_zero P rate (f j) (hf j) (hfi j)).1
  have he (j : Fin n) : (∫ s, C j s ∂μ) = 0 :=
    (recurrence_poisson_compensated_mean_zero P rate (f j) (hf j) (hfi j)).2
  have hp (j : Fin n) := measurePreserving_eval (μ := fun _ : Fin n => μ) j
  have hcoord (j : Fin n) : Integrable (fun z : Fin n → FiniteSample X => C j (z j))
      (Measure.pi (fun _ : Fin n => μ)) :=
    (hp j).integrable_comp_of_integrable (hi j)
  have hmean (j : Fin n) :
      (∫ z : Fin n → FiniteSample X, C j (z j)
        ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
    rw [← integral_map (hp j).measurable.aemeasurable (hC j).aestronglyMeasurable,
      (hp j).map_eq, he]
  constructor
  · exact integrable_finsetSum Finset.univ (fun j _ => hcoord j)
  · change (∫ z : Fin n → FiniteSample X, ∑ j : Fin n, C j (z j)
      ∂Measure.pi (fun _ : Fin n => μ)) = 0
    rw [integral_finsetSum Finset.univ (fun j _ => hcoord j)]
    simp only [hmean, Finset.sum_const_zero]

/-- Averaging the conditional Poisson energy over independent random exposures
preserves the point-score energy inside the exposure integral. Tonelli requires
no prior global integrability of the compensated score. -/
-- @node: recurrence_poisson_random_exposure_lintegral_energy
lemma recurrence_poisson_random_exposure_lintegral_energy
    {E : Type*} [MeasurableSpace E] (Q : Measure E) (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ)
    (f : E → Fin n → X → ℝ)
    (hf : ∀ e j, Measurable (f e j))
    (hf2 : ∀ e j, Integrable (fun x => f e j x ^ 2) P)
    (hscore : Measurable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2)) :
    (∫⁻ p : E × (Fin n → FiniteSample X),
      ENNReal.ofReal (recurrenceExposureScore P rate n f p.1 p.2 ^ 2)
      ∂Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) =
    ∫⁻ e, ENNReal.ofReal (∑ j : Fin n,
      (rate : ℝ) * ∫ x, f e j x ^ 2 ∂P) ∂Q := by
  rw [lintegral_prod _ ((hscore.pow_const 2).ennreal_ofReal.aemeasurable)]
  apply lintegral_congr
  intro e
  obtain ⟨hi, he⟩ := recurrence_poisson_iid_compensated_second_moment
    P rate n (f e) (hf e) (hf2 e)
  change (∫⁻ z, ENNReal.ofReal (recurrenceExposureScore P rate n f e z ^ 2)
    ∂Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) = _
  unfold recurrenceExposureScore
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z => sq_nonneg _)), he]

/-- Integrability of the averaged point-score energy gives integrability and
an exact second moment for the full random-exposure recurrence score. -/
-- @node: recurrence_poisson_random_exposure_second_moment
lemma recurrence_poisson_random_exposure_second_moment
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [SFinite Q] (P : Measure X)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ)
    (f : E → Fin n → X → ℝ)
    (hf : ∀ e j, Measurable (f e j))
    (hf2 : ∀ e j, Integrable (fun x => f e j x ^ 2) P)
    (hscore : Measurable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2))
    (henergy : Integrable (fun e => ∑ j : Fin n,
      (rate : ℝ) * ∫ x, f e j x ^ 2 ∂P) Q) :
    Integrable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2 ^ 2)
      (Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) ∧
    (∫ p : E × (Fin n → FiniteSample X),
      recurrenceExposureScore P rate n f p.1 p.2 ^ 2
      ∂Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) =
    ∫ e, ∑ j : Fin n, (rate : ℝ) * ∫ x, f e j x ^ 2 ∂P ∂Q := by
  have hlocal (e : E) := recurrence_poisson_iid_compensated_second_moment
    P rate n (f e) (hf e) (hf2 e)
  have hi : Integrable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2 ^ 2)
      (Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) := by
    apply (integrable_prod_iff (hscore.pow_const 2).aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (fun e => (hlocal e).1), ?_⟩
    have hnorm (e : E) :
        (∫ z, ‖recurrenceExposureScore P rate n f e z ^ 2‖
          ∂Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) =
        ∑ j : Fin n, (rate : ℝ) * ∫ x, f e j x ^ 2 ∂P := by
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (hlocal e).2
    simp_rw [hnorm]
    exact henergy
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun e => (hlocal e).2))

/-- The random-exposure recurrence score is integrable and centered whenever
its averaged point-score energy is integrable. Independence enters through the
product law; centering is proved for each exposure array before averaging. -/
-- @node: recurrence_poisson_random_exposure_mean_zero
lemma recurrence_poisson_random_exposure_mean_zero
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (P : Measure X) [IsProbabilityMeasure P] (rate : ℝ≥0) (n : ℕ)
    (f : E → Fin n → X → ℝ)
    (hf : ∀ e j, Measurable (f e j))
    (hf2 : ∀ e j, Integrable (fun x => f e j x ^ 2) P)
    (hscore : Measurable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2))
    (henergy : Integrable (fun e => ∑ j : Fin n,
      (rate : ℝ) * ∫ x, f e j x ^ 2 ∂P) Q) :
    Integrable (fun p : E × (Fin n → FiniteSample X) =>
      recurrenceExposureScore P rate n f p.1 p.2)
      (Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) ∧
    (∫ p : E × (Fin n → FiniteSample X),
      recurrenceExposureScore P rate n f p.1 p.2
      ∂Q.prod (Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate))) = 0 := by
  have hi2 := (recurrence_poisson_random_exposure_second_moment
    Q P rate n f hf hf2 hscore henergy).1
  have hi := ((memLp_two_iff_integrable_sq hscore.aestronglyMeasurable).2
    hi2).integrable (by norm_num)
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have hmean (e : E) :
      (∫ z, recurrenceExposureScore P rate n f e z
        ∂Measure.pi (fun _ : Fin n => finitePoissonSampleLaw P rate)) = 0 := by
    have hfi (j : Fin n) : Integrable (f e j) P :=
      ((memLp_two_iff_integrable_sq (hf e j).aestronglyMeasurable).2
        (hf2 e j)).integrable (by norm_num)
    exact (recurrence_poisson_iid_compensated_mean_zero
      P rate n (f e) (hf e) hfi).2
  simp_rw [hmean]
  exact integral_zero _ _

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
