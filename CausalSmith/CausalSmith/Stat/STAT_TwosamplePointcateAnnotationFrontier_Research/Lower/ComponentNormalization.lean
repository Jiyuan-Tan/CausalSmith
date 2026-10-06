module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.ComponentHellinger

/-!
# Normalization of conditional component densities

Each record likelihood integrates to one against fair observed spins.
Independent fair spins therefore normalize every selected record product and
its finite prior mixture, as required by the MC32 product-distance argument.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A labeled likelihood has total mass one under the two fair reference spins.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the label likelihood integral one conclusion](goal) holds. -/
lemma labelLikelihood_integral_one {d : ℕ} (P : PrimitiveLaw d) (x : Cov d)
    (he : P.e x ∈ Icc (0:ℝ) 1)
    (hm : ∀ arm : Bool, (if arm then P.mu1 x else P.mu0 x) ∈ Icc (0:ℝ) 1) :
    ∫ s, labelLikelihood P x s ∂fairObserved = 1 := by
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, labelLikelihood]
  rw [bern_singleton_toReal_spin _ he, bern_singleton_toReal_spin _ he]
  simp only [Bool.false_eq_true, if_false, if_true]
  have hm0 : P.mu0 x ∈ Icc (0:ℝ) 1 := hm false
  have hm1 : P.mu1 x ∈ Icc (0:ℝ) 1 := hm true
  rw [bern_singleton_toReal_spin _ hm0, bern_singleton_toReal_spin _ hm0,
    bern_singleton_toReal_spin _ hm1, bern_singleton_toReal_spin _ hm1]
  norm_num [fairObserved, bern, Measure.real, Measure.prod_apply, thetaSign]
  <;> ring

/-- An auxiliary likelihood has total mass one under a fair treatment spin.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input he](hyp:he), [the auxiliary likelihood integral one conclusion](goal) holds. -/
lemma auxiliaryLikelihood_integral_one {d : ℕ} (P : PrimitiveLaw d) (x : Cov d)
    (he : P.e x ∈ Icc (0:ℝ) 1) :
    ∫ s, auxiliaryLikelihood P x s ∂bern (1/2) = 1 := by
  letI := bern_probability (1/2) (by norm_num)
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Fintype.sum_bool, auxiliaryLikelihood]
  rw [bern_singleton_toReal_spin _ he, bern_singleton_toReal_spin _ he]
  norm_num [bern, Measure.real, thetaSign]
  <;> ring

/-- A selected product of record likelihoods is normalized by independent fair spins,
including when no records are selected.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the record likelihood product integral one conclusion](goal) holds. -/
lemma recordLikelihood_product_integral_one {d n m : ℕ} (P : PrimitiveLaw d)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m)))
    (he : ∀ i, P.e (x i) ∈ Icc (0:ℝ) 1)
    (hm : ∀ i (arm : Bool),
      (if arm then P.mu1 (x i) else P.mu0 (x i)) ∈ Icc (0:ℝ) 1) :
    ∫ s : RecordSpins n m, (∏ i ∈ V, recordLikelihood P x s i)
      ∂(Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2))) = 1 := by
  classical
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  have hsplit (s : RecordSpins n m) :
      (∏ i ∈ V, recordLikelihood P x s i) =
      (∏ i : Fin n, if Fin.castAdd m i ∈ V then
        labelLikelihood P (x (Fin.castAdd m i)) (s.1 i) else 1) *
      (∏ j : Fin m, if Fin.natAdd n j ∈ V then
        auxiliaryLikelihood P (x (Fin.natAdd n j)) (s.2 j) else 1) := by
    have hv : (∏ i, if i ∈ V then recordLikelihood P x s i else 1) =
        ∏ i ∈ V, recordLikelihood P x s i := by
      rw [← Finset.prod_filter]
      congr 1
      ext i
      simp
    rw [← hv, Fin.prod_univ_add]
    simp [recordLikelihood]
  simp_rw [hsplit]
  rw [integral_prod_mul
    (fun sl : Fin n → Bool × Bool => ∏ i, if Fin.castAdd m i ∈ V then
      labelLikelihood P (x (Fin.castAdd m i)) (sl i) else 1)
    (fun st : Fin m → Bool => ∏ j, if Fin.natAdd n j ∈ V then
      auxiliaryLikelihood P (x (Fin.natAdd n j)) (st j) else 1),
    integral_fintype_prod_eq_prod (fun (i : Fin n) s => if Fin.castAdd m i ∈ V then
      labelLikelihood P (x (Fin.castAdd m i)) s else 1),
    integral_fintype_prod_eq_prod (fun (j : Fin m) s => if Fin.natAdd n j ∈ V then
      auxiliaryLikelihood P (x (Fin.natAdd n j)) s else 1)]
  have hl (i : Fin n) :
      (∫ s, (if Fin.castAdd m i ∈ V then
        labelLikelihood P (x (Fin.castAdd m i)) s else 1) ∂fairObserved) = 1 := by
    split_ifs
    · exact labelLikelihood_integral_one P _ (he _) (hm _)
    · simp
  have ht (j : Fin m) :
      (∫ s, (if Fin.natAdd n j ∈ V then
        auxiliaryLikelihood P (x (Fin.natAdd n j)) s else 1) ∂bern (1/2)) = 1 := by
    split_ifs
    · exact auxiliaryLikelihood_integral_one P _ (he _)
    · rw [integral_const, probReal_univ, one_smul]
  simp only [hl, ht, Finset.prod_const_one, one_mul]

/-- Averaging normalized selected record products over a probability prior gives
normalized component densities, even for the empty selected set.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input hw](hyp:hw), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the component density integral one conclusion](goal) holds. -/
lemma componentDensity_integral_one {d n m : ℕ} (H : MarkedPriors d) (theta : Bool)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m)))
    (hw : ∑ sigma, H.weight theta sigma = 1)
    (he : ∀ sigma i, (H.law theta sigma).e (x i) ∈ Icc (0:ℝ) 1)
    (hm : ∀ sigma i (arm : Bool),
      (if arm then (H.law theta sigma).mu1 (x i) else
        (H.law theta sigma).mu0 (x i)) ∈ Icc (0:ℝ) 1) :
    ∫ s : RecordSpins n m, componentDensity H theta x V s
      ∂(Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2))) = 1 := by
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  unfold componentDensity
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, recordLikelihood_product_integral_one _ x V
    (he _) (hm _), mul_one]
  exact hw

/-- The prescribed marked construction normalizes every component for every
covariate vector; probability clipping supplies valid margins without extra premises.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input V](hyp:V), [the marked component density integral one conclusion](goal) holds. -/
lemma marked_componentDensity_integral_one {d n m : ℕ} (h delta a b : ℝ)
    (theta : Bool) (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m))) :
    ∫ s : RecordSpins n m, componentDensity (markedHandle d h delta a b) theta x V s
      ∂(Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2))) = 1 := by
  apply componentDensity_integral_one
  · exact (marked_prior_mass d h delta theta).2
  · intro sigma i
    exact probabilityClip_mem _
  · intro sigma i arm
    cases arm <;> exact probabilityClip_mem _

/-- Prior averages of nonnegative record likelihoods are nonnegative densities.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input hw](hyp:hw), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input s](hyp:s), [the component density nonneg conclusion](goal) holds. -/
lemma componentDensity_nonneg {d n m : ℕ} (H : MarkedPriors d) (theta : Bool)
    (hw : ∀ sigma, 0 ≤ H.weight theta sigma)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m))) (s : RecordSpins n m) :
    0 ≤ componentDensity H theta x V s := by
  unfold componentDensity
  apply Finset.sum_nonneg
  intro sigma _
  apply mul_nonneg (hw sigma)
  apply Finset.prod_nonneg
  intro i _
  induction i using Fin.addCases with
  | left j => simp only [recordLikelihood, Fin.addCases_left, labelLikelihood]; positivity
  | right j => simp only [recordLikelihood, Fin.addCases_right, auxiliaryLikelihood]; positivity

/-- Each marked component density defines a probability law on the common fair
spin reference, supplying the normalization required by Hellinger subadditivity.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input V](hyp:V), [the marked component density probability conclusion](goal) holds. -/
lemma marked_componentDensity_probability {d n m : ℕ} (h delta a b : ℝ)
    (theta : Bool) (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m))) :
    IsProbabilityMeasure
      (((Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2)))).withDensity
          (fun s => ENNReal.ofReal
            (componentDensity (markedHandle d h delta a b) theta x V s))) := by
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
      (Filter.Eventually.of_forall (fun s => componentDensity_nonneg _ theta
        (marked_prior_mass d h delta theta).1 x V s)),
    marked_componentDensity_integral_one]
  exact ENNReal.ofReal_one

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
