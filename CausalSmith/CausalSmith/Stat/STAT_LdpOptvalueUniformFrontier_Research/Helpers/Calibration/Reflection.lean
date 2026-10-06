module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.HybridBasics

/-!
# Reflection of hybrid column statistics

The explicit Chebyshev approximation is even. Reflecting the bits in both blocks
therefore preserves the hybrid column statistic, including threshold ties. The affine
row integral identifies the reflected vector law, its iid block product, and the
independent two-block law; hybrid means and variances are invariant.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- [Only even Chebyshev orders occur in the explicit approximation](goal). -/
-- @node: chebyshevAbsPoly_eval_neg
lemma chebyshevAbsPoly_eval_neg (D : ℕ) (x : ℝ) :
    (chebyshevAbsPoly D).eval (-x) = (chebyshevAbsPoly D).eval x := by
  simp only [chebyshevAbsPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [Polynomial.Chebyshev.T_eval_neg]

/-- [Negating the input multiplies each monomial coefficient by its parity sign](goal). -/
-- @node: reflection_coeff_comp_neg_X
lemma reflection_coeff_comp_neg_X (p : Polynomial ℝ) (v : ℕ) :
    (p.comp (-Polynomial.X)).coeff v = (-1 : ℝ)^v * p.coeff v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n a =>
    have hpow : (-Polynomial.X : Polynomial ℝ)^n = Polynomial.C ((-1 : ℝ)^n) * Polynomial.X^n := by
      calc
        _ = (Polynomial.C (-1 : ℝ) * Polynomial.X)^n := by congr 1; simp
        _ = _ := by rw [mul_pow, ← Polynomial.C_pow]
    rw [Polynomial.monomial_comp, hpow]
    simp only [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
    by_cases h : n = v
    · subst v; simp [mul_comm]
    · simp [h, Ne.symm h]

/-- [The parity-weighted coefficients of the even approximation are unchanged](goal). -/
-- @node: chebyshevAbsPoly_coeff_parity
lemma chebyshevAbsPoly_coeff_parity (D v : ℕ) :
    (-1 : ℝ)^v * (chebyshevAbsPoly D).coeff v = (chebyshevAbsPoly D).coeff v := by
  have hp : (chebyshevAbsPoly D).comp (-Polynomial.X) = chebyshevAbsPoly D := by
    apply Polynomial.eq_of_infinite_eval_eq
    have heq : {x : ℝ | ((chebyshevAbsPoly D).comp (-Polynomial.X)).eval x =
        (chebyshevAbsPoly D).eval x} = Set.univ := by
      ext x
      simp [chebyshevAbsPoly_eval_neg]
    rw [heq]
    exact Set.infinite_univ
  rw [← reflection_coeff_comp_neg_X, hp]

/-- [Every distinct-person product acquires the sign of its degree under reflection](goal). -/
-- @node: privateMoment_neg
lemma privateMoment_neg (W : Fin m → Fin d → ℝ) (k : ℕ) (j : Fin d) :
    privateMoment (fun i j => -W i j) k j = (-1 : ℝ)^k * privateMoment W k j := by
  classical
  unfold privateMoment
  rw [mul_comm ((-1 : ℝ)^k), mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  have hcard := (Finset.mem_powersetCard.mp hJ).2
  simpa only [Finset.prod_neg, hcard] using
    (mul_comm ((-1 : ℝ)^k) (∏ i ∈ J, W i j))

/-- [Reflecting every released bit negates every scaled entry](goal). -/
-- @node: scaledMessages_not
lemma scaledMessages_not (eps : ℝ) (z : Fin m → Fin d → Bool) (i : Fin m) (j : Fin d) :
    scaledMessages eps (fun i j => !(z i j)) i j = -scaledMessages eps z i j := by
  cases h : z i j <;> simp [scaledMessages, signVal, h]

/-- [The pilot and evaluation means change sign under bit reflection](goal). -/
-- @node: scaledColumnMean_not
lemma scaledColumnMean_not (eps : ℝ) (z : Fin m → Fin d → Bool) (j : Fin d) :
    scaledColumnMean eps j (fun i j => !(z i j)) = -scaledColumnMean eps j z := by
  simp [scaledColumnMean, scaledMessages_not, Finset.sum_neg_distrib]

/-- [Parity of the coefficients cancels parity of the reflected private moments](goal). -/
-- @node: polynomialEstimate_not
lemma polynomialEstimate_not (eps a : ℝ) (D : ℕ) (j : Fin d)
    (z : Fin m → Fin d → Bool) :
    polynomialEstimate eps a D j (fun i j => !(z i j)) = polynomialEstimate eps a D j z := by
  have hW : scaledMessages eps (fun i j => !(z i j)) = fun i j => -scaledMessages eps z i j := by
    funext i j
    exact scaledMessages_not eps z i j
  unfold polynomialEstimate
  rw [hW]
  simp_rw [privateMoment_neg]
  apply Finset.sum_congr rfl
  intro v hv
  have hp := chebyshevAbsPoly_coeff_parity D v
  calc
    _ = ((-1 : ℝ)^v * (chebyshevAbsPoly D).coeff v) *
        a^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j := by ring
    _ = _ := by rw [hp]

/-- [Simultaneous reflection preserves both hybrid branches and threshold ties](goal). -/
-- @node: hybridColumn_not
lemma hybridColumn_not (eps : ℝ) (D : ℕ) (j : Fin d)
    (z : (Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) :
    hybridColumn eps D j ((fun i j => !(z.1 i j)), (fun i j => !(z.2 i j))) =
      hybridColumn eps D j z := by
  unfold hybridColumn
  simp only [scaledColumnMean_not, abs_neg, polynomialEstimate_not]
  split
  · rfl
  · by_cases hp : 0 < scaledColumnMean eps j z.1
    · simp [hp, show ¬scaledColumnMean eps j z.1 < 0 by linarith]
    · by_cases hn : scaledColumnMean eps j z.1 < 0
      · simp [hp, hn, show 0 < -scaledColumnMean eps j z.1 by linarith]
      · have hz : scaledColumnMean eps j z.1 = 0 := by linarith
        simp [hz]

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [dimension at least two](hyp:hd). [Averaging an original-record vector row has an affine integral determined by the contrasts](goal). -/
-- @node: vectorMessageLaw_integral_affine
lemma vectorMessageLaw_integral_affine (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (hd : 2 ≤ d)
    (f : (Fin d → Bool) → ℝ) :
    (∫ z, f z ∂vectorMessageLaw P eps) =
      (2 : ℝ)^(-(d : ℤ)) * (∑ z, f z) +
      (2 : ℝ)^(-(d : ℤ)) * privacyDelta eps *
        ∑ j, (contrast P j / d) * (∑ z, signVal (z j) * f z) := by
  letI := vectorKernel_markov d eps
  letI : IsProbabilityMeasure (observedLaw P) := by
    unfold observedLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  change (∫ z, f z ∂((vectorKernel d eps) ∘ₖ Kernel.const Unit (observedLaw P)) ()) = _
  rw [Kernel.integral_comp Integrable.of_finite]
  have hrow (o : ObsRecord d) :
      (∫ z, f z ∂vectorKernel d eps o) =
        (2 : ℝ)^(-(d : ℤ)) * (∑ z, f z) +
        (2 : ℝ)^(-(d : ℤ)) * privacyDelta eps *
          ∑ j : Fin d, (if o.1 = j then obsSign o else 0) *
            (∑ z, signVal (z j) * f z) := by
    rw [integral_fintype Integrable.of_finite]
    change (∑ z, (atomLaw (vectorMass eps o)).real {z} * f z) = _
    simp only [measureReal_def, atomLaw_singleton,
      ENNReal.toReal_ofReal (vectorMass_nonneg eps o _), smul_eq_mul]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [vectorMass, mul_add, add_mul, one_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  simp_rw [hrow]
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const,
    integral_const_mul, integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp only [probReal_univ, one_smul]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const]
  have hcell := signedCellMean_eq_contrast P hP j
  unfold signedCellMean at hcell
  rw [hP.uniform j] at hcell
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hmean : (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) =
      contrast P j / d := by
    apply (div_eq_iff (inv_ne_zero hdR)).mp at hcell
    simpa [div_eq_mul_inv] using hcell
  simp only [Kernel.const_apply]
  unfold observedLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) * _ = _
  rw [hmean]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [Negating all contrasts reflects every released vector bit in a one-row experiment](goal). -/
-- @node: vectorMessageLaw_integral_not
lemma vectorMessageLaw_integral_not (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) (f : (Fin d → Bool) → ℝ) :
    (∫ z, f (fun j => !(z j)) ∂vectorMessageLaw P eps) =
      ∫ z, f z ∂vectorMessageLaw P' eps := by
  classical
  let e : (Fin d → Bool) ≃ (Fin d → Bool) :=
    ⟨fun z j => !(z j), fun z j => !(z j), by intro z; ext j; simp,
      by intro z; ext j; simp⟩
  have hsum : (∑ z : Fin d → Bool, f (fun j => !(z j))) = ∑ z, f z := e.sum_comp f
  have hsign (j : Fin d) :
      (∑ z : Fin d → Bool, signVal (z j) * f (fun j => !(z j))) = -(∑ z, signVal (z j) * f z) := by
    have h := e.sum_comp (fun (z : Fin d → Bool) => signVal (z j) * f z)
    have hn (z : Fin d → Bool) : signVal (!(z j)) = -signVal (z j) := by
      cases z j <;> norm_num [signVal]
    change (∑ z : Fin d → Bool, signVal (!(z j)) * f (fun j => !(z j))) = _ at h
    simp_rw [hn, neg_mul, Finset.sum_neg_distrib] at h
    linarith
  rw [vectorMessageLaw_integral_affine P hP eps hd,
    vectorMessageLaw_integral_affine P' hP' eps hd, hsum]
  simp_rw [hsign, hx, neg_div, mul_neg, neg_mul]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [The reflected vector-message pushforward is the law with opposite contrasts](goal). -/
-- @node: vectorMessageLaw_map_not
lemma vectorMessageLaw_map_not (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) :
    (vectorMessageLaw P eps).map (fun z j => !(z j)) = vectorMessageLaw P' eps := by
  classical
  letI := vectorMessageLaw_probability P eps
  letI := vectorMessageLaw_probability P' eps
  ext E hE
  have h := vectorMessageLaw_integral_not P P' hP hP' eps hd hx
    (E.indicator (fun _ => (1 : ℝ)))
  rw [← integral_map (Measurable.of_discrete.aemeasurable) (by fun_prop)] at h
  simp only [integral_indicator hE, integral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply_univ] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [Reflection commutes with the iid product of participant rows](goal). -/
-- @node: vectorBlockLaw_map_not
lemma vectorBlockLaw_map_not (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) :
    (vectorBlockLaw P eps m).map (fun z i j => !(z i j)) = vectorBlockLaw P' eps m := by
  letI := vectorMessageLaw_probability P eps
  unfold vectorBlockLaw
  rw [Measure.pi_map_pi (fun _ => (show Measurable
    (fun z : Fin d → Bool => fun j => !(z j)) by fun_prop).aemeasurable)]
  simp_rw [vectorMessageLaw_map_not P P' hP hP' eps hd hx]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [Reflecting both independent blocks gives the hybrid law with opposite contrasts](goal). -/
-- @node: hybridLaw_map_not
lemma hybridLaw_map_not (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) :
    (hybridLaw P eps m).map
      (fun z => ((fun i j => !(z.1 i j)), (fun i j => !(z.2 i j)))) =
      hybridLaw P' eps m := by
  letI := vectorBlockLaw_probability P eps m
  unfold hybridLaw
  change Measure.map (Prod.map (fun z i j => !(z i j)) (fun z i j => !(z i j)))
    ((vectorBlockLaw P eps m).prod (vectorBlockLaw P eps m)) = _
  rw [← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete]
  rw [vectorBlockLaw_map_not P P' hP hP' eps hd hx]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [The hybrid mean is unchanged by reversing the entire contrast vector](goal). -/
-- @node: hybridMean_reflection
lemma hybridMean_reflection (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) (D : ℕ) (j : Fin d) :
    hybridMean (m := m) P' eps (hybridColumn eps D j) =
      hybridMean (m := m) P eps (hybridColumn eps D j) := by
  unfold hybridMean
  rw [← hybridLaw_map_not P P' hP hP' eps hd hx,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  simp_rw [hybridColumn_not]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [the causal-model conditions for the second law](hyp:hP'), [dimension at least two](hyp:hd), and [the stated hx condition](hyp:hx). [The hybrid variance is unchanged by reversing the entire contrast vector](goal). -/
-- @node: hybridVar_reflection
lemma hybridVar_reflection (P P' : Measure (FullRecord d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hP : CausalModel P) (hP' : CausalModel P') (eps : ℝ) (hd : 2 ≤ d)
    (hx : ∀ j, contrast P' j = -contrast P j) (D : ℕ) (j : Fin d) :
    hybridVar (m := m) P' eps (hybridColumn eps D j) =
      hybridVar (m := m) P eps (hybridColumn eps D j) := by
  unfold hybridVar
  rw [hybridMean_reflection P P' hP hP' eps hd hx,
    ← hybridLaw_map_not P P' hP hP' eps hd hx,
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  simp_rw [hybridColumn_not]

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Reversing a causal contrast vector preserves the symmetric construction's parameter cube](goal). -/
-- @node: neg_contrast_mem_parameterCube
lemma neg_contrast_mem_parameterCube (P : Measure (FullRecord d)) (hP : CausalModel P) :
    (fun j => -contrast P j) ∈ parameterCube d := by
  intro j
  have h := contrast_mem_parameterCube P hP j
  constructor <;> linarith [h.1, h.2]

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [dimension at least two](hyp:hd). [The symmetric law built from the reversed contrast has exactly that contrast](goal). -/
-- @node: symmetricLaw_neg_contrast
lemma symmetricLaw_neg_contrast (P : Measure (FullRecord d)) (hP : CausalModel P)
    (hd : 2 ≤ d) (j : Fin d) :
    contrast (symmetricLaw (fun j => -contrast P j)) j = -contrast P j := by
  change armMean (symmetricLaw (fun j => -contrast P j)) true j -
    armMean (symmetricLaw (fun j => -contrast P j)) false j = -contrast P j
  rw [symmetricLaw_armMean _ (neg_contrast_mem_parameterCube P hP) (by omega),
    symmetricLaw_armMean _ (neg_contrast_mem_parameterCube P hP) (by omega)]
  norm_num [signVal]
  <;> ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier
