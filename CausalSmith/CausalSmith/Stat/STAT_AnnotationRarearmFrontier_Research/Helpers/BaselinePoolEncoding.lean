module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Baseline
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePrefixCounts

/-!
Exact identifications of the baseline's array block counts with ordered-prefix histograms.
These identities provide the deterministic count bridge for finite-pool risk transfer.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory

open scoped BigOperators NNReal

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- An ordered block is represented as a finite sample without changing its order. -/
-- @node: baselineBlockPrefix
def baselineBlockPrefix {X : Type*} [MeasurableSpace X] {n : Nat} (s : Fin n → X)
    (offset r : Nat) (hr : offset + r ≤ n) : FiniteSample X :=
  ⟨r, fun i => s ⟨offset + i.val, by omega⟩⟩

/-- [Under the stated inputs and conditions](hyp:X,n,s,hr,x,offset,r), Histogram counts of an ordered block equal the corresponding array filter counts.  This gives [the stated result](goal).-/
-- @node: baseline_block_histogram
lemma baseline_block_histogram {X : Type*} [MeasurableSpace X] [DecidableEq X] {n : Nat}
    (s : Fin n → X) (offset r : Nat) (hr : offset + r ≤ n) (x : X) :
    finiteSampleHistogram (baselineBlockPrefix s offset r hr).points x =
      (Finset.univ.filter fun i => offset ≤ i.val ∧ i.val < offset + r ∧ s i = x).card := by
  classical
  rw [← Fintype.card_subtype]
  unfold finiteSampleHistogram
  change Fintype.card {i : Fin r // s ⟨offset + i.val, by omega⟩ = x} = _
  apply Fintype.card_congr
  refine
    { toFun := fun i => ⟨⟨offset + i.1.val, by omega⟩, ?_⟩
      invFun := fun i => ⟨⟨i.1.val - offset, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · dsimp
    exact ⟨by omega, by omega, i.2⟩
  · have hi := i.2
    omega
  · have hi := i.2
    simpa [baselineBlockPrefix, Nat.add_sub_of_le hi.1] using hi.2.2
  · intro i
    apply Subtype.ext
    apply Fin.ext
    simp
  · intro i
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_sub_of_le i.2.1

/-- [Under the stated inputs and conditions](hyp:s,hr,j,n,d,offset,r,a,y), The baseline's complete-record block counter is the exact ordered-block histogram.  This gives [the stated result](goal).-/
-- @node: baseline_labeled_block_histogram
lemma baseline_labeled_block_histogram {n d : Nat} (s : Fin n → Obs d)
    (offset r : Nat) (hr : offset + r ≤ n) (j : Fin d) (a y : Bool) :
    finiteSampleHistogram (baselineBlockPrefix s offset r hr).points (j,a,y) =
      labeledBlockCount s offset r j a y :=
  baseline_block_histogram s offset r hr (j,a,y)

/-- [Under the stated inputs and conditions](hyp:s,hr,j,a,m,d,offset,r), The baseline's auxiliary block counter is the exact ordered-block histogram.  This gives [the stated result](goal).-/
-- @node: baseline_auxiliary_block_histogram
lemma baseline_auxiliary_block_histogram {m d : Nat} (s : Fin m → AuxObs d)
    (offset r : Nat) (hr : offset + r ≤ m) (j : Fin d) (a : Bool) :
    finiteSampleHistogram (baselineBlockPrefix s offset r hr).points (j,a) =
      auxiliaryBlockCount s offset r j a :=
  baseline_block_histogram s offset r hr (j,a)

/-- [Under the stated inputs and conditions](hyp:X,r,s,x), A histogram can be evaluated as a sum of unit contributions over array positions.  This gives [the stated result](goal).-/
-- @node: baseline_histogram_sum
lemma baseline_histogram_sum {X : Type*} [DecidableEq X] {r : Nat}
    (s : Fin r → X) (x : X) :
    finiteSampleHistogram s x = ∑ i, if s i = x then 1 else 0 := by
  classical
  simp [finiteSampleHistogram, Fintype.card_subtype, Finset.sum_boole]

/-- [Under the stated inputs and conditions](hyp:X,s,w,x,r,v), Concatenating two arrays adds their histogram counts.  This gives [the stated result](goal).-/
-- @node: baseline_histogram_append
lemma baseline_histogram_append {X : Type*} [DecidableEq X] {r v : Nat}
    (s : Fin r → X) (w : Fin v → X) (x : X) :
    finiteSampleHistogram (Fin.append s w) x =
      finiteSampleHistogram s x + finiteSampleHistogram w x := by
  classical
  simp only [baseline_histogram_sum]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- [Under the stated inputs and conditions](hyp:s,j,a,r,d), Projecting away the binary outcome adds the two outcome-marked counts.  This gives [the stated result](goal).-/
-- @node: baseline_projected_histogram
lemma baseline_projected_histogram {r d : Nat} (s : Fin r → Obs d)
    (j : Fin d) (a : Bool) :
    finiteSampleHistogram (fun i => ((s i).1, (s i).2.1)) (j,a) =
      finiteSampleHistogram s (j,a,false) + finiteSampleHistogram s (j,a,true) := by
  classical
  simp only [baseline_histogram_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j', a', y⟩ := s i
  cases y <;> simp

/-- The baseline's auxiliary prefix concatenates projected complete records and auxiliary records
in precisely the order used by the array implementation. -/
-- @node: baselineAuxiliaryPrefix
def baselineAuxiliaryPrefix {n m d : Nat} (s : Sample n m d)
    (lo size ao r : Nat) (hl : lo + min r size ≤ n) (ha : ao + (r - size) ≤ m) :
    FiniteSample (AuxObs d) :=
  let l := baselineBlockPrefix s.1 lo (min r size) hl
  let v := baselineBlockPrefix s.2 ao (r - size) ha
  ⟨min r size + (r - size), Fin.append (fun i => ((l.points i).1, (l.points i).2.1)) v.points⟩

/-- [Under the stated inputs and conditions](hyp:s,hl,ha,n,m,d,lo,size,ao,r), The concatenated auxiliary prefix has the requested length, including either empty part.  This gives [the stated result](goal).-/
-- @node: baseline_auxiliary_prefix_count
lemma baseline_auxiliary_prefix_count {n m d : Nat} (s : Sample n m d)
    (lo size ao r : Nat) (hl : lo + min r size ≤ n) (ha : ao + (r - size) ≤ m) :
    (baselineAuxiliaryPrefix s lo size ao r hl ha).count = r := by
  change min r size + (r - size) = r
  omega

/-- [Under the stated inputs and conditions](hyp:s,hl,ha,j,a,n,m,d,lo,size,ao,r), The baseline's pooled arm counter is exactly the histogram of its concatenated prefix.  This gives [the stated result](goal).-/
-- @node: baseline_pooled_arm_histogram
lemma baseline_pooled_arm_histogram {n m d : Nat} (s : Sample n m d)
    (lo size ao r : Nat) (hl : lo + min r size ≤ n) (ha : ao + (r - size) ≤ m)
    (j : Fin d) (a : Bool) :
    finiteSampleHistogram (baselineAuxiliaryPrefix s lo size ao r hl ha).points (j,a) =
      pooledArmCount s lo size ao r j a := by
  have hfalse := baseline_labeled_block_histogram s.1 lo (min r size) hl j a false
  have htrue := baseline_labeled_block_histogram s.1 lo (min r size) hl j a true
  have haux := baseline_auxiliary_block_histogram s.2 ao (r - size) ha j a
  simp only [baselineBlockPrefix, FiniteSample.points, FiniteSample.count] at hfalse htrue haux
  simp only [baselineAuxiliaryPrefix, baselineBlockPrefix, FiniteSample.points, FiniteSample.count]
  rw [baseline_histogram_append, baseline_projected_histogram, hfalse, htrue, haux]
  rfl

/-- [Under the stated inputs and conditions](hyp:s,hr,hl,ha,n,m,d,r,v), The array baseline prefix statistic is exactly the clipped ordered-prefix statistic.
The complete and auxiliary histogram identities retain every arm contribution.  This gives [the stated result](goal).-/
-- @node: baseline_prefix_statistic_eq_ordered
lemma baseline_prefix_statistic_eq_ordered {n m d : Nat} (s : Sample n m d)
    (r v : Nat) (hr : 0 + r ≤ n)
    (hl : n / 2 + min v (n - n / 2) ≤ n)
    (ha : 0 + (v - (n - n / 2)) ≤ m) :
    baselinePrefixStatistic r v s =
      baselineOrderedPrefixStatistic ((n / 2 : Nat) / 8 : NNReal)
        (baselineBlockPrefix s.1 0 r hr,
          baselineAuxiliaryPrefix s (n / 2) (n - n / 2) 0 v hl ha) := by
  have hZ (a : Bool) (j : Fin d) := baseline_labeled_block_histogram s.1 0 r hr j a true
  have hK (a : Bool) (j : Fin d) :=
    baseline_pooled_arm_histogram s (n / 2) (n - n / 2) 0 v hl ha j a
  unfold baselineOrderedPrefixStatistic baselinePrefixCounts
  simp only [Sum.elim_inl, Sum.elim_inr, hZ, hK,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  simp only [baselinePrefixStatistic, Finset.sum_sub_distrib]


/-- [Under the stated inputs and conditions](hyp:F,u,t,h,g), Integrating a zero-overflow two-prefix statistic gives exactly the finite product
of Poisson weights. No continuity or nonzero cell mass is needed.  This gives [the stated result](goal).-/
-- @node: baseline_truncated_poisson_integral
lemma baseline_truncated_poisson_integral (u t : NNReal) (h g : Nat)
    (F : Nat → Nat → Real) :
    (∫ k : Nat × Nat, if k.1 ≤ h ∧ k.2 ≤ g then F k.1 k.2 else 0
      ∂((poissonMeasure u).prod (poissonMeasure t))) =
      ∑ r ∈ Finset.range (h + 1), ∑ v ∈ Finset.range (g + 1),
        Real.exp (-(u : Real) - (t : Real)) *
          ((u : Real) ^ r / (r.factorial : Real)) *
          ((t : Real) ^ v / (v.factorial : Real)) * F r v := by
  classical
  let s := (Finset.range (h + 1)).product (Finset.range (g + 1))
  have hind : (fun k : Nat × Nat => if k.1 ≤ h ∧ k.2 ≤ g then F k.1 k.2 else 0) =
      (s : Set (Nat × Nat)).indicator (fun k => F k.1 k.2) := by
    funext k
    simp [s, Set.indicator, Nat.lt_succ_iff]
  rw [hind, integral_indicator s.measurableSet, setIntegral_finset s IntegrableOn.finset]
  dsimp only [s]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro v _
  have hmass : ((poissonMeasure u).prod (poissonMeasure t)).real {(r,v)} =
      (poissonMeasure u).real {r} * (poissonMeasure t).real {v} := by
    simp only [Measure.real_def, ← Set.singleton_prod_singleton,
      Measure.prod_prod, ENNReal.toReal_mul]
  rw [smul_eq_mul, hmass, poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- [Under the stated inputs and conditions](hyp:s,hn,n,m,d), The baseline's finite average is the expectation of its array prefix statistic
with exactly zero output when either Poisson request exceeds its pool.  This gives [the stated result](goal).-/
-- @node: baseline_estimator_eq_poisson_integral
lemma baseline_estimator_eq_poisson_integral {n m d : Nat} (s : Sample n m d)
    (hn : 6 ≤ n) :
    baselineEstimator n m d s =
      ∫ k : Nat × Nat,
        if k.1 ≤ n / 2 ∧ k.2 ≤ n - n / 2 + m then
          baselinePrefixStatistic k.1 k.2 s else 0
        ∂((poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
          (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))) := by
  rw [baseline_truncated_poisson_integral _ _ _ _
    (fun r v => baselinePrefixStatistic r v s)]
  simp only [baselineEstimator, if_neg (show ¬ n < 6 by omega),
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]


/-- On the original arrays, either requested prefix overflow resets the baseline to zero. -/
-- @node: baselineCappedArrayStatistic
noncomputable def baselineCappedArrayStatistic {n m d : Nat} (s : Sample n m d)
    (k : Nat × Nat) : Real :=
  if k.1 ≤ n / 2 ∧ k.2 ≤ n - n / 2 + m then
    baselinePrefixStatistic k.1 k.2 s else 0

/-- [Under the stated inputs and conditions](hyp:s,k,n,m,d), Every original-array capped statistic lies in the clipping interval.  This gives [the stated result](goal).-/
-- @node: baseline_capped_array_mem_Icc
lemma baseline_capped_array_mem_Icc {n m d : Nat} (s : Sample n m d) (k : Nat × Nat) :
    baselineCappedArrayStatistic s k ∈ Set.Icc (-1) 1 := by
  unfold baselineCappedArrayStatistic
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · norm_num

/-- [Under the stated inputs and conditions](hyp:s,hn,theta,n,m,d), Conditional Poisson averaging contracts the squared loss at every original array.  This gives [the stated result](goal).-/
-- @node: baseline_averaging_sq_loss_le
lemma baseline_averaging_sq_loss_le {n m d : Nat} (s : Sample n m d)
    (hn : 6 ≤ n) (theta : Real) :
    (baselineEstimator n m d s - theta) ^ 2 ≤
      ∫ k : Nat × Nat, (baselineCappedArrayStatistic s k - theta) ^ 2
        ∂((poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
          (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))) := by
  let nu := (poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
    (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))
  have hm : Measurable (baselineCappedArrayStatistic s) := by fun_prop
  have hb : Causalean.Stat.UniformlyBounded (baselineCappedArrayStatistic s) :=
    ⟨1, by norm_num, fun k => abs_le.mpr (baseline_capped_array_mem_Icc s k)⟩
  have hj := Causalean.Stat.sqLoss_kernelMean_le (Kernel.const Unit nu) hm hb theta ()
  rw [baseline_estimator_eq_poisson_integral s hn]
  simpa only [Causalean.Stat.kernelMean, Kernel.const_apply, baselineCappedArrayStatistic,
    nu] using hj

/-- [Under the stated inputs and conditions](hyp:P,hn,n,m,d), Conditional averaging also contracts squared risk under the original experiment's
finite-data distribution. This step does not require a pool-law identification.  This gives [the stated result](goal).-/
-- @node: baseline_averaging_sq_risk_le
lemma baseline_averaging_sq_risk_le {n m d : Nat} (P : DiscreteLaw d) (hn : 6 ≤ n) :
    Causalean.Stat.sqRisk (annotationLaw P n m) (baselineEstimator n m d) (ateFunctional P) ≤
      Causalean.Stat.sqRisk ((annotationLaw P n m).prod
        ((poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
          (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))))
        (fun z => baselineCappedArrayStatistic z.1 z.2) (ateFunctional P) := by
  let nu := (poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
    (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have htheta := ateFunctional_mem_Icc P
  have hm : Measurable (fun z : Sample n m d × (Nat × Nat) =>
      (baselineCappedArrayStatistic z.1 z.2 - ateFunctional P) ^ 2) := by fun_prop
  have hi : Integrable (fun z : Sample n m d × (Nat × Nat) =>
      (baselineCappedArrayStatistic z.1 z.2 - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod nu) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc := baseline_capped_array_mem_Icc z.1 z.2
    nlinarith [hc.1, hc.2, htheta.1, htheta.2]
  unfold Causalean.Stat.sqRisk
  rw [integral_prod _ hi]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hi.integral_prod_left
    (Filter.Eventually.of_forall (fun s => baseline_averaging_sq_loss_le s hn _))


/-- [Under the stated inputs and conditions](hyp:P,n,m,d), The independent uniform seed has no effect on the risk of the data-only baseline.  This gives [the stated result](goal).-/
-- @node: baseline_ruleRisk_eq_sqRisk
lemma baseline_ruleRisk_eq_sqRisk (n m d : Nat) (P : DiscreteLaw d) :
    ruleRisk (liftRule (baselineEstimator n m d)) P =
      Causalean.Stat.sqRisk (annotationLaw P n m) (baselineEstimator n m d) (ateFunctional P) := by
  let : IsProbabilityMeasure seedLaw := ⟨by
    norm_num [seedLaw, Real.volume_Icc]⟩
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have hm : Measurable (fun z : Sample n m d × Real =>
      (baselineEstimator n m d z.1 - ateFunctional P) ^ 2) := by fun_prop
  have hi : Integrable (fun z : Sample n m d × Real =>
      (baselineEstimator n m d z.1 - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod seedLaw) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hc := baselineEstimator_mem_Icc n m d z.1
    have ht := ateFunctional_mem_Icc P
    nlinarith [hc.1, hc.2, ht.1, ht.2]
  unfold ruleRisk liftRule Causalean.Stat.sqRisk
  rw [integral_prod _ hi]
  simp

/-- [Under the stated inputs and conditions](hyp:P,hn,n,m,d), The original randomized-rule risk is bounded by the loss of the zero-overflow
prefix statistic before averaging over its independent Poisson requests.  This gives [the stated result](goal).-/
-- @node: baseline_ruleRisk_le_capped_array_risk
lemma baseline_ruleRisk_le_capped_array_risk {n m d : Nat} (P : DiscreteLaw d)
    (hn : 6 ≤ n) :
    ruleRisk (liftRule (baselineEstimator n m d)) P ≤
      Causalean.Stat.sqRisk ((annotationLaw P n m).prod
        ((poissonMeasure ((n / 2 : Nat) / 8 : NNReal)).prod
          (poissonMeasure ((n - n / 2 + m : Nat) / 8 : NNReal))))
        (fun z => baselineCappedArrayStatistic z.1 z.2) (ateFunctional P) := by
  rw [baseline_ruleRisk_eq_sqRisk]
  exact baseline_averaging_sq_risk_le P hn

end CausalSmith.Stat.AnnotationRarearmFrontier
