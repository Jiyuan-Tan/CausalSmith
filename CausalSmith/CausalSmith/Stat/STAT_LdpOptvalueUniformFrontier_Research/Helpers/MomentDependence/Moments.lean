module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.Counting
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PrivateMoments
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.TSignedCausalBridge
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Moments.Variance

/-!
# Helpers/MomentDependence/Moments

Finite original-record private value frontiers: Helpers/MomentDependence/Moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n m d : ℕ}
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the function f](hyp:f). [Expectations on finite message blocks](goal). -/
def blockMean (P : Measure (FullRecord d)) (eps : ℝ) (f : (Fin m → Fin d → Bool) → ℝ) : ℝ :=
  ∫ z, f z ∂(vectorBlockLaw P eps m)
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the function f](hyp:f). [Variance on finite message blocks](goal). -/
def blockVar (P : Measure (FullRecord d)) (eps : ℝ) (f : (Fin m → Fin d → Bool) → ℝ) : ℝ :=
  ∫ z, (f z - blockMean (m := m) P eps f)^2 ∂(vectorBlockLaw P eps m)
/-- Fix [the privacy budget](hyp:eps), [the function g](hyp:g), [the coordinate index](hyp:j), and [the function z](hyp:z). [Own-column statistics](goal). -/
def columnStatistic (eps : ℝ) (g : Fin d → (Fin m → ℝ) → ℝ)
    (j : Fin d) (z : Fin m → Fin d → Bool) : ℝ :=
  g j (fun i => scaledMessages eps z i j)
  -- @realizes g(deterministic functions) @realizes T^{\mathrm{col}}(g_j(W_column))
/-- [Squaring a scaled sign removes all dependence on the released bit](goal). -/
-- @node: scaledMessages_sq
lemma scaledMessages_sq (eps : ℝ) (z : Fin m → Fin d → Bool)
    (i : Fin m) (j : Fin d) :
    (scaledMessages eps z i j)^2 = (noiseScale d eps)^2 := by
  unfold scaledMessages signVal
  cases z i j <;> simp

/-- [The second scaled-message moment is the squared noise scale](goal). -/
-- @node: blockMean_scaledMessages_sq
lemma blockMean_scaledMessages_sq (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (i : Fin m) (j : Fin d) :
    blockMean P eps (fun z => (scaledMessages eps z i j)^2) = (noiseScale d eps)^2 := by
  letI := vectorBlockLaw_probability P eps m
  simp [blockMean, scaledMessages_sq]

/-- Assume [the stated hjj condition](hyp:hjj). [Uniform signs have zero mixed second moment in distinct coordinates](goal). -/
-- @node: sum_vector_two_signs
lemma sum_vector_two_signs (j j' : Fin d) (hjj : j ≠ j') :
    ∑ z : Fin d → Bool, signVal (z j) * signVal (z j') = 0 := by
  classical
  apply Finset.sum_ninvolution (fun z => Function.update z j (!(z j)))
  · intro z
    simp only [Function.update_self, Function.update_of_ne hjj.symm]
    cases hj : z j <;> cases hj' : z j' <;> simp [signVal, hj, hj']
  · intro z _ heq
    have h := congrFun heq j
    cases hz : z j <;> simp [hz] at h
  · intro z
    exact Finset.mem_univ _
  · intro z
    ext l
    by_cases h : l = j
    · subst l
      simp
    · simp [Function.update_of_ne h]

/-- [Global sign reversal cancels every product of three signs, including repeated indices](goal). -/
-- @node: sum_vector_three_signs
lemma sum_vector_three_signs (j j' l : Fin d) :
    ∑ z : Fin d → Bool, signVal (z j) * signVal (z j') * signVal (z l) = 0 := by
  classical
  apply Finset.sum_ninvolution (fun z i => !(z i))
  · intro z
    cases hj : z j <;> cases hj' : z j' <;> cases hl : z l <;>
      norm_num [signVal, hj, hj', hl]
  · intro z _ heq
    have h := congrFun heq j
    cases hz : z j <;> simp [hz] at h
  · intro z
    exact Finset.mem_univ _
  · intro z
    ext i
    simp

/-- Assume [the stated hjj condition](hyp:hjj). [Cancellation of both the uniform and affine parts of a channel's cross moment](goal). -/
-- @node: sum_vectorMass_cross
lemma sum_vectorMass_cross (eps : ℝ) (o : ObsRecord d)
    (j j' : Fin d) (hjj : j ≠ j') :
    ∑ z : Fin d → Bool, vectorMass eps o z * (signVal (z j) * signVal (z j')) = 0 := by
  have hexpand : ∀ z : Fin d → Bool,
      vectorMass eps o z * (signVal (z j) * signVal (z j')) =
        (2 : ℝ)^(-(d : ℤ)) * (signVal (z j) * signVal (z j')) +
        ((2 : ℝ)^(-(d : ℤ)) * privacyDelta eps * obsSign o) *
          (signVal (z j) * signVal (z j') * signVal (z o.1)) := by
    intro z
    unfold vectorMass
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_vector_two_signs j j' hjj, sum_vector_three_signs]
  ring

/-- Assume [the stated hjj condition](hyp:hjj). [A channel row has zero cross-coordinate sign expectation for every original record](goal). -/
-- @node: vectorKernel_cross_sign_integral
lemma vectorKernel_cross_sign_integral (eps : ℝ) (o : ObsRecord d)
    (j j' : Fin d) (hjj : j ≠ j') :
    (∫ z, signVal (z j) * signVal (z j') ∂vectorKernel d eps o) = 0 := by
  letI := vectorKernel_markov d eps
  rw [integral_fintype Integrable.of_finite]
  change (∑ z, (atomLaw (vectorMass eps o)).real {z} *
    (signVal (z j) * signVal (z j'))) = 0
  simp only [measureReal_def, atomLaw_singleton,
    ENNReal.toReal_ofReal (vectorMass_nonneg eps o _), smul_eq_mul]
  exact sum_vectorMass_cross eps o j j' hjj

/-- Assume [the stated hjj condition](hyp:hjj). [Averaging channel rows preserves the zero cross-coordinate expectation](goal). -/
-- @node: vectorMessageLaw_cross_sign_integral
lemma vectorMessageLaw_cross_sign_integral (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (j j' : Fin d) (hjj : j ≠ j') :
    (∫ z, signVal (z j) * signVal (z j') ∂vectorMessageLaw P eps) = 0 := by
  letI := vectorMessageLaw_probability P eps
  letI := vectorKernel_markov d eps
  letI : IsProbabilityMeasure (observedLaw P) := by
    unfold observedLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  change (∫ z, signVal (z j) * signVal (z j')
    ∂((vectorKernel d eps) ∘ₖ Kernel.const Unit (observedLaw P)) ()) = 0
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [vectorKernel_cross_sign_integral eps _ j j' hjj]
  simp

/-- Assume [the stated hjj condition](hyp:hjj). [The independent row law transfers the channel cross moment to scaled block messages](goal). -/
-- @node: blockMean_scaledMessages_cross
lemma blockMean_scaledMessages_cross (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (i : Fin m) (j j' : Fin d) (hjj : j ≠ j') :
    blockMean P eps (fun z => scaledMessages eps z i j * scaledMessages eps z i j') = 0 := by
  letI := vectorMessageLaw_probability P eps
  unfold blockMean vectorBlockLaw scaledMessages
  rw [integral_comp_eval (μ := fun _ : Fin m => vectorMessageLaw P eps) (i := i) (f := fun z : Fin d → Bool =>
    noiseScale d eps * signVal (z j) * (noiseScale d eps * signVal (z j'))) (by fun_prop)]
  have hfactor : ∀ z : Fin d → Bool,
      noiseScale d eps * signVal (z j) * (noiseScale d eps * signVal (z j')) =
        (noiseScale d eps)^2 * (signVal (z j) * signVal (z j')) := by
    intro z
    ring
  simp_rw [hfactor]
  rw [integral_const_mul, vectorMessageLaw_cross_sign_integral P eps j j' hjj, mul_zero]

/-- [Products using distinct participant rows factor under the independent block law](goal). -/
-- @node: blockMean_scaledMessages_product
lemma blockMean_scaledMessages_product (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (J : Finset (Fin m)) (j : Fin d) :
    blockMean P eps (fun z => ∏ i ∈ J, scaledMessages eps z i j) =
      (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^J.card := by
  classical
  letI := vectorMessageLaw_probability P eps
  unfold blockMean vectorBlockLaw scaledMessages
  simp_rw [← Finset.prod_ite_mem_eq J]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin m => vectorMessageLaw P eps)
    (fun (i : Fin m) (z : Fin d → Bool) => if i ∈ J then
    noiseScale d eps * signVal (z j) else 1)]
  have hrow : ∀ i : Fin m,
      (∫ z, (if i ∈ J then noiseScale d eps * signVal (z j) else 1)
        ∂vectorMessageLaw P eps) =
      if i ∈ J then (∫ z, noiseScale d eps * signVal (z j)
        ∂vectorMessageLaw P eps) else 1 := by
    intro i
    split_ifs <;> simp
  simp_rw [hrow]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

/-- Assume [the stated hkm condition](hyp:hkm). [Averaging distinct-row products gives the corresponding power of the one-row mean](goal). -/
-- @node: blockMean_privateMoment_eq_rowMean_pow
lemma blockMean_privateMoment_eq_rowMean_pow (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (k : ℕ) (hkm : k ≤ m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => privateMoment (scaledMessages eps z) k j) =
      (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^k := by
  classical
  letI := vectorBlockLaw_probability P eps m
  unfold blockMean privateMoment
  rw [integral_const_mul, integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hterm : ∀ J ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (∫ z, ∏ i ∈ J, scaledMessages eps z i j ∂vectorBlockLaw P eps m) =
      (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^k := by
    intro J hJ
    change blockMean P eps (fun z => ∏ i ∈ J, scaledMessages eps z i j) = _
    rw [blockMean_scaledMessages_product, (Finset.mem_powersetCard.mp hJ).2]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hchoose : (Nat.choose m k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkm).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hchoose, one_mul]

/-- [A selected participant has the common one-row mean](goal). -/
-- @node: blockMean_scaledMessages_eq_rowMean
lemma blockMean_scaledMessages_eq_rowMean (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (i : Fin m) (j : Fin d) :
    blockMean P eps (fun z => scaledMessages eps z i j) =
      ∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps := by
  letI := vectorMessageLaw_probability P eps
  unfold blockMean vectorBlockLaw scaledMessages
  exact integral_comp_eval (μ := fun _ : Fin m => vectorMessageLaw P eps)
    (i := i) (f := fun z : Fin d → Bool => noiseScale d eps * signVal (z j))
    Integrable.of_finite.aestronglyMeasurable

/-- [A channel row biases precisely the coordinate named by its original input](goal). -/
-- @node: vectorKernel_sign_integral
lemma vectorKernel_sign_integral (eps : ℝ) (o : ObsRecord d) (j : Fin d) :
    (∫ z, signVal (z j) ∂vectorKernel d eps o) =
      if o.1 = j then privacyDelta eps * obsSign o else 0 := by
  classical
  letI := vectorKernel_markov d eps
  rw [integral_fintype Integrable.of_finite]
  change (∑ z, (atomLaw (vectorMass eps o)).real {z} * signVal (z j)) = _
  simp only [measureReal_def, atomLaw_singleton,
    ENNReal.toReal_ofReal (vectorMass_nonneg eps o _), smul_eq_mul]
  have hexpand : ∀ z : Fin d → Bool,
      vectorMass eps o z * signVal (z j) =
        (2 : ℝ)^(-(d : ℤ)) * signVal (z j) +
        ((2 : ℝ)^(-(d : ℤ)) * privacyDelta eps * obsSign o) *
          (signVal (z o.1) * signVal (z j)) := by
    intro z
    unfold vectorMass
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_vector_coordinate_sign, mul_zero, zero_add]
  by_cases h : o.1 = j
  · have hsquare : ∀ z : Fin d → Bool, signVal (z j) * signVal (z j) = 1 := by
      intro z
      cases z j <;> norm_num [signVal]
    simp_rw [h, hsquare]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, mul_one, if_true,
      zpow_neg, zpow_natCast]
    field_simp
    push_cast
    ring
  · rw [sum_vector_two_signs o.1 j h]
    simp [h]

/-- [Averaging the original-input rows expresses a coordinate bias as a signed cell integral](goal). -/
-- @node: vectorMessageLaw_sign_integral
lemma vectorMessageLaw_sign_integral (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (j : Fin d) :
    (∫ z, signVal (z j) ∂vectorMessageLaw P eps) =
      privacyDelta eps * ∫ w, if cell w = j then obsSign (observe w) else 0 ∂P := by
  letI := vectorMessageLaw_probability P eps
  letI := vectorKernel_markov d eps
  letI : IsProbabilityMeasure (observedLaw P) := by
    unfold observedLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  change (∫ z, signVal (z j)
    ∂((vectorKernel d eps) ∘ₖ Kernel.const Unit (observedLaw P)) ()) = _
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [vectorKernel_sign_integral]
  have hfactor : ∀ o : ObsRecord d,
      (if o.1 = j then privacyDelta eps * obsSign o else 0) =
      privacyDelta eps * (if o.1 = j then obsSign o else 0) := by
    intro o
    split_ifs <;> ring
  simp_rw [hfactor]
  rw [integral_const_mul]
  congr 1
  unfold observedLaw
  change (∫ o, if o.1 = j then obsSign o else 0 ∂P.map observe) = _
  rw [integral_map (by fun_prop) (by fun_prop)]
  rfl

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The signed causal bridge identifies the scaled one-row coordinate mean. The causal input mean is supplied by the proved `signedCellMean_eq_contrast`](goal). -/
-- @node: vectorMessageLaw_scaled_sign_integral
lemma vectorMessageLaw_scaled_sign_integral (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (j : Fin d) :
    (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps) = contrast P j := by
  letI := vectorMessageLaw_probability P eps
  have hdelta : privacyDelta eps ≠ 0 := by
    rw [privacyDelta_exp_formula]
    exact div_ne_zero (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr heps)))
      (ne_of_gt (by positivity))
  have hdreal : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  have hcell := signedCellMean_eq_contrast P hP j
  unfold signedCellMean at hcell
  rw [hP.uniform j] at hcell
  have hmean : (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) =
      contrast P j / d := by
    apply (div_eq_iff (inv_ne_zero hdreal)).mp at hcell
    simpa [div_eq_mul_inv] using hcell
  rw [integral_const_mul, vectorMessageLaw_sign_integral, hmean]
  unfold noiseScale
  field_simp

/-- [The degree-zero distinct-person statistic is identically one](goal). -/
-- @node: privateMoment_zero
lemma privateMoment_zero (W : Fin m → Fin d → ℝ) (j : Fin d) :
    privateMoment W 0 j = 1 := by
  simp [privateMoment]
/-- [The degree-one statistic is the average of the scaled participant messages](goal). -/
-- @node: privateMoment_one
lemma privateMoment_one (W : Fin m → Fin d → ℝ) (j : Fin d) :
    privateMoment W 1 j = (m : ℝ)⁻¹ * ∑ i, W i j := by
  classical
  simp [privateMoment, Finset.powersetCard_one, Finset.sum_image]
/-- Assume [the stated hii condition](hyp:hii). [Independent distinct rows factor their common-coordinate cross moment](goal). -/
-- @node: blockMean_scaledMessages_distinct_rows
lemma blockMean_scaledMessages_distinct_rows (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (i i' : Fin m) (hii : i ≠ i') (j : Fin d) :
    blockMean P eps (fun z => scaledMessages eps z i j * scaledMessages eps z i' j) =
      (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^2 := by
  classical
  have h := blockMean_scaledMessages_product P eps {i, i'} j
  simpa [Finset.prod_insert, hii] using h
/-- [The squared column sum separates the diagonal noise terms from distinct-row means](goal). -/
-- @node: blockMean_scaledMessages_sum_sq
lemma blockMean_scaledMessages_sum_sq (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (∑ i, scaledMessages eps z i j)^2) =
      (m : ℝ) * (noiseScale d eps)^2 + (m : ℝ) * (m-1 : ℝ) *
        (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^2 := by
  classical
  letI := vectorBlockLaw_probability P eps m
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  unfold blockMean
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hrow : ∀ i i' : Fin m,
      (∫ z, scaledMessages eps z i j * scaledMessages eps z i' j
        ∂vectorBlockLaw P eps m) =
      (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^2 +
        if i' = i then (noiseScale d eps)^2 -
          (∫ z, noiseScale d eps * signVal (z j) ∂vectorMessageLaw P eps)^2 else 0 := by
    intro i i'
    by_cases h : i' = i
    · subst i'
      rw [if_pos rfl]
      have hs := blockMean_scaledMessages_sq P eps i j
      simp only [blockMean, pow_two] at hs
      rw [hs]
      ring
    · rw [if_neg h]
      have hs := blockMean_scaledMessages_distinct_rows P eps i i' (Ne.symm h) j
      simpa [blockMean] using hs
  simp_rw [hrow]
  simp [Finset.sum_add_distrib]
  ring
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The squared first private moment has the exact iid mean-square formula](goal). -/
-- @node: blockMean_privateMoment_one_sq
lemma blockMean_privateMoment_one_sq (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) 1 j)^2) =
      (contrast P j)^2 + ((noiseScale d eps)^2 - (contrast P j)^2)/m := by
  simp_rw [privateMoment_one, mul_pow]
  unfold blockMean
  rw [integral_const_mul]
  change ((m : ℝ)⁻¹)^2 *
    blockMean P eps (fun z => (∑ i, scaledMessages eps z i j)^2) = _
  rw [blockMean_scaledMessages_sum_sq, vectorMessageLaw_scaled_sign_integral P hP eps heps hd j]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  <;> ring
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The exact first-moment formula implies the declared degree-one second-moment bound](goal). -/
-- @node: blockMean_privateMoment_one_sq_le
lemma blockMean_privateMoment_one_sq_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) 1 j)^2) ≤
      (contrast P j)^2 + 2*(noiseScale d eps)^2/m := by
  rw [blockMean_privateMoment_one_sq P hP eps heps hd hm j]
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (noiseScale d eps), sq_nonneg (contrast P j)]
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The product of two subset statistics factors into its one-row moments](goal). -/
-- @node: blockMean_scaledMessages_subset_product
lemma blockMean_scaledMessages_subset_product (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (J K : Finset (Fin m)) (j : Fin d) :
    blockMean P eps (fun z => (∏ i ∈ J, scaledMessages eps z i j) *
      (∏ i ∈ K, scaledMessages eps z i j)) =
      ∏ i : Fin m, if i ∈ J then
        (if i ∈ K then (noiseScale d eps)^2 else contrast P j)
        else (if i ∈ K then contrast P j else 1) := by
  classical
  letI := vectorMessageLaw_probability P eps
  unfold blockMean vectorBlockLaw scaledMessages
  simp_rw [← Finset.prod_ite_mem_eq J, ← Finset.prod_ite_mem_eq K, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin m => vectorMessageLaw P eps)
    (fun (i : Fin m) (z : Fin d → Bool) =>
      (if i ∈ J then noiseScale d eps * signVal (z j) else 1) *
      (if i ∈ K then noiseScale d eps * signVal (z j) else 1))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K
  · simp only [hJ, hK, ↓reduceIte]
    have hs : ∀ z : Fin d → Bool,
        (noiseScale d eps * signVal (z j)) * (noiseScale d eps * signVal (z j)) =
        (noiseScale d eps)^2 := by
      intro z
      cases z j <;> simp [signVal, pow_two]
    simp_rw [hs]
    simp
  · simp only [hJ, hK, ↓reduceIte, mul_one]
    exact vectorMessageLaw_scaled_sign_integral P hP eps heps hd j
  · simp only [hJ, hK, ↓reduceIte, one_mul]
    exact vectorMessageLaw_scaled_sign_integral P hP eps heps hd j
  · simp [hJ, hK]
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Shared participant rows contribute squared noise and unshared rows contribute contrast powers](goal). -/
-- @node: blockMean_scaledMessages_subset_overlap
lemma blockMean_scaledMessages_subset_overlap (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (J K : Finset (Fin m)) (j : Fin d) :
    blockMean P eps (fun z => (∏ i ∈ J, scaledMessages eps z i j) *
      (∏ i ∈ K, scaledMessages eps z i j)) =
      ((noiseScale d eps)^2)^(J ∩ K).card *
        (contrast P j)^((J \ K).card + (K \ J).card) := by
  classical
  rw [blockMean_scaledMessages_subset_product P hP eps heps hd J K j]
  have hf : ∀ i : Fin m,
      (if i ∈ J then (if i ∈ K then (noiseScale d eps)^2 else contrast P j)
        else (if i ∈ K then contrast P j else 1)) =
      (if i ∈ J ∩ K then (noiseScale d eps)^2 else 1) *
        (if i ∈ J \ K then contrast P j else 1) *
        (if i ∈ K \ J then contrast P j else 1) := by
    intro i
    by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K <;> simp [hJ, hK]
  simp_rw [hf, Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]
  rw [pow_add]
  ring
/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The squared private moment is the normalized finite sum over subset overlaps](goal). -/
-- @node: blockMean_privateMoment_sq_overlap_sum
lemma blockMean_privateMoment_sq_overlap_sum (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (k : ℕ) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) k j)^2) =
      ((Nat.choose m k : ℝ)⁻¹)^2 *
        ∑ J ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∑ K ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            ((noiseScale d eps)^2)^(J ∩ K).card *
              (contrast P j)^((J \ K).card + (K \ J).card) := by
  classical
  letI := vectorBlockLaw_probability P eps m
  have hexpand : ∀ z : Fin m → Fin d → Bool,
      (privateMoment (scaledMessages eps z) k j)^2 =
      ((Nat.choose m k : ℝ)⁻¹)^2 *
        ∑ J ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          ∑ K ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            (∏ i ∈ J, scaledMessages eps z i j) *
              (∏ i ∈ K, scaledMessages eps z i j) := by
    intro z
    unfold privateMoment
    rw [mul_pow]
    congr 1
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  unfold blockMean
  simp_rw [hexpand]
  rw [integral_const_mul, integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro K hK
  exact blockMean_scaledMessages_subset_overlap P hP eps heps hd J K j

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [the stated hkm condition](hyp:hkm). [The exact overlap expansion and finite inclusion bound give the second moment for every degree, without dividing by the cell contrast](goal). -/
-- @node: blockMean_privateMoment_sq_le
lemma blockMean_privateMoment_sq_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (hm : 0 < m) (k : ℕ) (hkm : 2*k ≤ m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) k j)^2) ≤
      ((contrast P j)^2 + 2*k*(noiseScale d eps)^2/m)^k := by
  by_cases hk0 : k = 0
  · subst k
    letI := vectorBlockLaw_probability P eps m
    simp [blockMean, privateMoment_zero]
  by_cases hk1 : k = 1
  · subst k
    simpa using blockMean_privateMoment_one_sq_le P hP eps heps hd hm j
  rw [blockMean_privateMoment_sq_overlap_sum P hP eps heps hd k j]
  have hterm : ∀ J ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      ∀ K ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (contrast P j)^((J \ K).card + (K \ J).card) =
          ((contrast P j)^2)^(k-(J ∩ K).card) := by
    intro J hJ K hK
    have hJcard := (Finset.mem_powersetCard.mp hJ).2
    have hKcard := (Finset.mem_powersetCard.mp hK).2
    have hleft : (J \ K).card = k-(J ∩ K).card := by
      rw [← Finset.sdiff_inter_self_left, Finset.card_sdiff_of_subset
        Finset.inter_subset_left, hJcard]
    have hright : (K \ J).card = k-(J ∩ K).card := by
      rw [← Finset.sdiff_inter_self_left, Finset.card_sdiff_of_subset
        Finset.inter_subset_left, hKcard, Finset.inter_comm]
    rw [hleft, hright, ← pow_mul]
    congr 1
    omega
  simp_rw [Finset.sum_congr rfl (fun J hJ =>
    Finset.sum_congr rfl (fun K hK => congrArg
      (fun x => ((noiseScale d eps)^2)^(J ∩ K).card * x) (hterm J hJ K hK)))]
  simpa using overlap_average_le (Finset.univ : Finset (Fin m)) k
    (by simpa using hm) (by simpa using hkm)
    ((contrast P j)^2) ((noiseScale d eps)^2) (sq_nonneg _) (sq_nonneg _)

/-- Assume [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [a privacy budget in the interval from zero to one](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), and [a block no larger than the sample](hyp:hmn). [First, second, cross and distinct-person power moments of the vector channel](goal). -/
-- @node: vector_private_moments
lemma vector_private_moments (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : eps ∈ Set.Ioc 0 1) (hd : 2 ≤ d) (hm : 0 < m) (hmn : m ≤ n) :
    NoninteractiveClass (vectorProtocol n d eps) eps ∧
    (∀ (i : Fin m) (j : Fin d),
      blockMean (m := m) P eps (fun z => scaledMessages eps z i j) = contrast P j ∧
      blockMean (m := m) P eps (fun z => (scaledMessages eps z i j)^2) = (noiseScale d eps)^2) ∧
    (∀ (i : Fin m) (j j' : Fin d), j ≠ j' →
      blockMean (m := m) P eps (fun z => scaledMessages eps z i j * scaledMessages eps z i j')
        = 0) ∧
    (∀ k : ℕ, k ≤ m → ∀ j : Fin d,
      blockMean (m := m) P eps (fun z => privateMoment (scaledMessages eps z) k j) = (contrast
        P j)^k) ∧
    (∀ k : ℕ, 2*k ≤ m → ∀ j : Fin d,
      blockMean (m := m) P eps (fun z => (privateMoment (scaledMessages eps z) k j)^2) ≤
        ((contrast P j)^2 + 2*k*(noiseScale d eps)^2/m)^k) := by
  have hfirst : ∀ (i : Fin m) (j : Fin d),
      blockMean P eps (fun z => scaledMessages eps z i j) = contrast P j := by
    intro i j
    rw [blockMean_scaledMessages_eq_rowMean]
    exact vectorMessageLaw_scaled_sign_integral P hP eps heps.1 hd j
  refine ⟨vectorProtocol_noninteractive n d eps heps.1.le, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨hfirst i j, blockMean_scaledMessages_sq P eps i j⟩
  · intro i j j' hjj
    exact blockMean_scaledMessages_cross P eps i j j' hjj
  · intro k hkm j
    rw [blockMean_privateMoment_eq_rowMean_pow P eps k hkm j]
    have hrow := hfirst ⟨0, hm⟩ j
    rw [blockMean_scaledMessages_eq_rowMean] at hrow
    rw [hrow]
  · intro k hkm j
    exact blockMean_privateMoment_sq_le P hP eps heps.1 hd hm k hkm j


end CausalSmith.Stat.LdpOptvalueUniformFrontier
