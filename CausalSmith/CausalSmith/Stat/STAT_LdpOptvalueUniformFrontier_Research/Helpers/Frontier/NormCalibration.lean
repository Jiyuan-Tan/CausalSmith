module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.BlockSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Assembly
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellError

/-!
# Squared-error calibration of the concrete norm statistics

The structural moment computation agrees with the calibrated polynomial statistic.
Finite averaging and the bias--variance identity give its global polynomial MSE.
Selecting the actual evaluation and disjoint pilot rows transfers all three norm
calibrations to the attaining transcript.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n m d : ℕ}

/-- [The executable structural moment recursion computes the calibrated statistic exactly](goal). -/
-- @node: frontierPolynomialEstimate_eq_polynomialEstimate
lemma frontierPolynomialEstimate_eq_polynomialEstimate (eps a : ℝ) (D : ℕ)
    (j : Fin d) (z : Fin m → Fin d → Bool) :
    frontierPolynomialEstimate eps a D j z = polynomialEstimate eps a D j z := by
  unfold frontierPolynomialEstimate polynomialEstimate
  simp_rw [privateMoment_eq_recursion]

/-- [Centered finite-block error splits into variance and squared bias](goal). -/
-- @node: blockMean_sq_error_eq_variance_add_bias
lemma blockMean_sq_error_eq_variance_add_bias
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (eps x : ℝ)
    (f : (Fin m → Fin d → Bool) → ℝ) :
    blockMean P eps (fun z => (f z - x)^2) =
      blockVar P eps f + (blockMean P eps f - x)^2 := by
  letI := vectorBlockLaw_probability P eps m
  have hv := variance_eq_sub (μ := vectorBlockLaw P eps m)
    (X := fun z => f z - x) (MemLp.of_discrete)
  rw [variance_sub_const (by fun_prop) x, variance_eq_integral (by fun_prop)] at hv
  have hm : (∫ z, f z - x ∂vectorBlockLaw P eps m) = blockMean P eps f - x := by
    unfold blockMean
    integral_linearity
    simp
  rw [hm] at hv
  change blockVar P eps f = blockMean P eps (fun z => (f z - x)^2) -
    (blockMean P eps f - x)^2 at hv
  linarith

/-- Assume [positive dimension](hyp:hd) and [the stated hbias condition](hyp:hbias). [Column bias bounds persist under finite averaging without independent columns](goal). -/
-- @node: blockMean_average_bias_le
lemma blockMean_average_bias_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps B : ℝ) (hd : 0 < d) (f : Fin d → (Fin m → Fin d → Bool) → ℝ)
    (theta : Fin d → ℝ)
    (hbias : ∀ j, abs (blockMean P eps (f j) - abs (theta j)) ≤ B) :
    |blockMean P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) - signedNorm theta| ≤ B := by
  letI := vectorBlockLaw_probability P eps m
  have havg : blockMean P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) =
      (d : ℝ)⁻¹ * ∑ j, blockMean P eps (f j) := by
    unfold blockMean
    integral_linearity
  rw [havg, signedNorm, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (d : ℝ)⁻¹)]
  calc
    _ ≤ (d : ℝ)⁻¹ * ∑ j, abs (blockMean P eps (f j) - abs (theta j)) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ _j : Fin d, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hbias j)) (by positivity)
    _ = B := by simp [ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd)]

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [positive block size](hyp:hm), [a block no larger than the sample](hyp:hmn), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated degree condition](hyp:hDegree). [The roadmap's global polynomial MSE applies to the actual recursive computation](goal). -/
-- @node: frontierPolynomial_average_mse_bound
lemma frontierPolynomial_average_mse_bound
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (hAllowed : Allowed n d eps) (hm : 0 < m) (hmn : m ≤ n)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hmD : 2*D ≤ m)
    (hDegree : (D : ℝ) ≤ (1/1024 : ℝ) * logDim d /
      Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) :
    blockMean (m := m) P eps (fun z => ((d : ℝ)⁻¹ *
      ∑ j, frontierPolynomialEstimate eps (1/2) D j z - signedNorm (contrast P))^2) ≤
      Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d))/(2*d) +
        (1/(D+1 : ℝ))^2 := by
  simp_rw [frontierPolynomialEstimate_eq_polynomialEstimate]
  obtain ⟨hbias, hvar⟩ := (finite_private_polynomial_calibration hMean hCheb S hIID
    P hP eps hAllowed hm hmn).1 D hEven hD hmD hDegree
  have hb := blockMean_average_bias_le P eps (1/(D+1 : ℝ))
    (by have := hAllowed.2.1; omega) (fun j => polynomialEstimate eps (1/2) D j)
    (contrast P) hbias
  have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
  simp only [← pow_two, sq_abs] at hbsq
  rw [blockMean_sq_error_eq_variance_add_bias]
  exact add_le_add hvar hbsq

/-- Assume [positive dimension](hyp:hd). [Cauchy--Schwarz bounds a squared finite average by the average squared error](goal). -/
-- @node: finite_average_sq_le
lemma finite_average_sq_le (hd : 0 < d) (x : Fin d → ℝ) :
    ((d : ℝ)⁻¹ * ∑ j, x j)^2 ≤ (d : ℝ)⁻¹ * ∑ j, (x j)^2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcs : (∑ j, x j)^2 ≤ (d : ℝ) * ∑ j, (x j)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun _ => (1 : ℝ)) x
  calc
    _ = (d : ℝ)⁻¹^2 * (∑ j, x j)^2 := mul_pow _ _ _
    _ ≤ (d : ℝ)⁻¹^2 * ((d : ℝ) * ∑ j, (x j)^2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by field_simp

/-- [Absolute value is a contraction in squared error at every true column mean](goal). -/
-- @node: abs_sub_abs_sq_le
lemma abs_sub_abs_sq_le (x y : ℝ) : (|x| - |y|)^2 ≤ (x-y)^2 := by
  have h := abs_abs_sub_abs_le x y
  have hsq := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, sq_abs] using hsq

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [positive block size](hyp:hm). [The roadmap's absolute evaluation means have signed-norm MSE at most sigma squared](goal). -/
-- @node: absolute_column_average_mse_bound
lemma absolute_column_average_mse_bound
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m) :
    blockMean (m := m) P eps (fun z => ((d : ℝ)⁻¹ *
      ∑ j, |scaledColumnMean eps j z| - signedNorm (contrast P))^2) ≤
        sigmaSquared d m eps := by
  letI := vectorBlockLaw_probability P eps m
  have hpoint (z : Fin m → Fin d → Bool) :
      ((d : ℝ)⁻¹ * ∑ j, |scaledColumnMean eps j z| - signedNorm (contrast P))^2 ≤
      (d : ℝ)⁻¹ * ∑ j, (scaledColumnMean eps j z - contrast P j)^2 := by
    unfold signedNorm
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact (finite_average_sq_le (by omega) _).trans
      (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => abs_sub_abs_sq_le _ _)) (by positivity))
  have hcol (j : Fin d) :
      blockMean (m := m) P eps (fun z => (scaledColumnMean eps j z - contrast P j)^2) ≤
        sigmaSquared d m eps := by
    rw [blockMean_sq_error_eq_variance_add_bias,
      blockMean_scaledColumnMean P hP eps heps hd hm]
    simpa using blockVar_scaledColumnMean_le P hP eps heps hd hm j
  calc
    _ ≤ blockMean P eps (fun z => (d : ℝ)⁻¹ *
        ∑ j, (scaledColumnMean eps j z - contrast P j)^2) :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite) hpoint
    _ = (d : ℝ)⁻¹ * ∑ j,
        blockMean P eps (fun z => (scaledColumnMean eps j z - contrast P j)^2) := by
      unfold blockMean
      integral_linearity
      rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    _ ≤ (d : ℝ)⁻¹ * ∑ _j : Fin d, sigmaSquared d m eps :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcol j)) (by positivity)
    _ = _ := by simp [ne_of_gt (show (0 : ℝ) < d by exact_mod_cast (by omega : 0 < d))]

/-- Assume [the stated hb condition](hyp:hb). [On the global branch the concrete transcript norm is exactly the calibrated recursive average](goal). -/
-- @node: frontierNormEstimate_globalPoly
lemma frontierNormEstimate_globalPoly (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .globalPoly)
    (z : ProtocolTranscript (frontierProtocol n d eps)) :
    frontierNormEstimate n d eps z = (d : ℝ)⁻¹ * ∑ j,
      polynomialEstimate eps (frontierResources n d eps).radius
        (frontierResources n d eps).degree j
        (frontierBlock n d eps ((frontierResources n d eps).m0 +
          (frontierResources n d eps).m) z) := by
  simp only [frontierNormEstimate, hb, frontierPolynomialEstimate_eq_polynomialEstimate]

/-- Assume [the stated hb condition](hyp:hb). [On the absolute-mean branch the concrete transcript norm is the calibrated mean statistic](goal). -/
-- @node: frontierNormEstimate_absMean
lemma frontierNormEstimate_absMean (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .absMean)
    (z : ProtocolTranscript (frontierProtocol n d eps)) :
    frontierNormEstimate n d eps z = (d : ℝ)⁻¹ * ∑ j,
      |scaledColumnMean eps j (frontierBlock n d eps
        ((frontierResources n d eps).m0 + (frontierResources n d eps).m) z)| := by
  simp only [frontierNormEstimate, hb]

/-- Assume [the stated hn condition](hyp:hn). [The disjoint pilot and evaluation extracts have the independent hybrid expectation](goal). -/
-- @node: frontierBlocks_integral
lemma frontierBlocks_integral (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (f : ((Fin (n / 3) → Fin d → Bool) × (Fin (n / 3) → Fin d → Bool)) → ℝ) :
    (∫ z, f (frontierBlock n d eps (frontierResources n d eps).m0 z,
      frontierBlock n d eps ((frontierResources n d eps).m0 +
        (frontierResources n d eps).m) z)
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) =
        hybridMean P eps f := by
  let g : Fin (n / 3 + n / 3) → Fin n := fun i =>
    ⟨(frontierResources n d eps).m0 + i.val, by
      have hi := i.isLt
      simp only [frontierResources]
      omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [g] at this
    omega
  have hlaw := frontier_vector_selection_law eps hn P g hg
    (fun i => by dsimp [g]; omega)
  have htransfer :
      (∫ z, f (splitHybridRows (fun i => (z (g i)).2))
        ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) =
      blockMean P eps (fun z => f (splitHybridRows z)) := by
    unfold blockMean
    rw [← hlaw]
    exact (integral_map
      (μ := Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i)))
      (φ := fun z i => (z (g i)).2) (f := fun z => f (splitHybridRows z))
      ((measurable_pi_lambda _ (fun i =>
        measurable_snd.comp (measurable_pi_apply (g i)))).aemeasurable)
      (by fun_prop)).symm
  have hpair (z : Fin n → FrontierMessage d) :
      (frontierBlock n d eps (frontierResources n d eps).m0 z,
        frontierBlock n d eps ((frontierResources n d eps).m0 +
          (frontierResources n d eps).m) z) =
      splitHybridRows (fun i => (z (g i)).2) := by
    apply Prod.ext
    · funext i
      have hi : (frontierResources n d eps).m0 + i.val < n := by
        have := i.isLt
        simp only [frontierResources]
        omega
      simp only [frontierBlock, messageAt, hi, ↓reduceDIte, splitHybridRows]
      rfl
    · funext i
      have hi : (frontierResources n d eps).m0 +
          (frontierResources n d eps).m + i.val < n := by
        have := i.isLt
        simp only [frontierResources]
        omega
      simp only [frontierBlock, messageAt, hi, ↓reduceDIte, splitHybridRows]
      congr 2
      apply Fin.ext
      simp [g, frontierResources, Nat.add_assoc, Nat.add_comm]
  simp_rw [hpair]
  exact htransfer.trans (hybridMean_eq_combined_blockMean P eps f).symm

/-- Assume [the stated hn condition](hyp:hn), [the stated hb condition](hyp:hb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hm condition](hyp:hm). [The actual absolute-mean transcript branch inherits its calibrated norm MSE](goal). -/
-- @node: frontierNormEstimate_absMean_mse
lemma frontierNormEstimate_absMean_mse (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hb : (frontierResources n d eps).branch = .absMean)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < n / 3) :
    (∫ z, (frontierNormEstimate n d eps z - signedNorm (contrast P))^2
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) ≤
        sigmaSquared d (n / 3) eps := by
  have hstat (z : Fin n → FrontierMessage d) := frontierNormEstimate_absMean n d eps hb z
  simp_rw [hstat]
  have htransfer := frontierBlock_integral n d eps hn P
    ((frontierResources n d eps).m0 + (frontierResources n d eps).m)
    (by simp only [frontierResources]; omega)
    (by simp only [frontierResources]; omega)
    (fun z => ((d : ℝ)⁻¹ * ∑ j, |scaledColumnMean eps j z| -
      signedNorm (contrast P))^2)
  exact htransfer.le.trans (absolute_column_average_mse_bound P hP eps heps hd hm)

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated hn condition](hyp:hn), [the stated hb condition](hyp:hb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hm condition](hyp:hm), [the stated even condition](hyp:hEven), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated degree condition](hyp:hDegree). [The actual global-polynomial transcript branch inherits its calibrated norm MSE](goal). -/
-- @node: frontierNormEstimate_globalPoly_mse
lemma frontierNormEstimate_globalPoly_mse
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hb : (frontierResources n d eps).branch = .globalPoly)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hAllowed : Allowed n d eps) (hm : 0 < n / 3)
    (hEven : Even (frontierResources n d eps).degree)
    (hD : 2 ≤ (frontierResources n d eps).degree)
    (hmD : 2*(frontierResources n d eps).degree ≤ n / 3)
    (hDegree : ((frontierResources n d eps).degree : ℝ) ≤
      (1/1024 : ℝ) * logDim d /
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d)) :
    (∫ z, (frontierNormEstimate n d eps z - signedNorm (contrast P))^2
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) ≤
      Real.exp (9*(frontierResources n d eps).degree*
        Real.log (Real.exp 1 + sigmaSquared d (n / 3) eps * logDim d))/(2*d) +
        (1/((frontierResources n d eps).degree+1 : ℝ))^2 := by
  have hradius : (frontierResources n d eps).radius = (1/2 : ℝ) := by
    by_cases hsmall : logDim d < 4096
    · simp [frontierResources, hn, hsmall] at hb
    · by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
      · simp [frontierResources, hn, hsmall, hdense] at hb
      · simp [frontierResources, hdense]
  have hstat (z : Fin n → FrontierMessage d) := frontierNormEstimate_globalPoly n d eps hb z
  simp_rw [hstat, hradius,
    ← frontierPolynomialEstimate_eq_polynomialEstimate]
  have htransfer := frontierBlock_integral n d eps hn P
    ((frontierResources n d eps).m0 + (frontierResources n d eps).m)
    (by simp only [frontierResources]; omega)
    (by simp only [frontierResources]; omega)
    (fun z => ((d : ℝ)⁻¹ * ∑ j, frontierPolynomialEstimate eps (1/2)
      (frontierResources n d eps).degree j z - signedNorm (contrast P))^2)
  exact htransfer.le.trans (frontierPolynomial_average_mse_bound hMean hCheb S hIID P hP
    eps hAllowed hm (by omega) _ hEven hD hmD hDegree)

/-- Assume [the stated hb condition](hyp:hb). [On the hybrid branch the transcript computation is the calibrated pilot rule](goal). -/
-- @node: frontierNormEstimate_hybrid
lemma frontierNormEstimate_hybrid (n d : ℕ) (eps : ℝ)
    (hb : (frontierResources n d eps).branch = .hybrid)
    (z : Fin n → FrontierMessage d) :
    frontierNormEstimate n d eps z = (d : ℝ)⁻¹ * ∑ j,
      hybridColumn eps (frontierResources n d eps).degree j
        (frontierBlock n d eps (frontierResources n d eps).m0 z,
          frontierBlock n d eps ((frontierResources n d eps).m0 +
            (frontierResources n d eps).m) z) := by
  have hradius : (frontierResources n d eps).radius =
      2*(frontierResources n d eps).threshold := by
    by_cases hsmall : logDim d < 4096
    · by_cases hn : n = 2
      · simp [frontierResources, hn] at hb
      · simp [frontierResources, hn, hsmall] at hb
    · by_cases hdense : (d : ℝ)^2 * logDim d ≤ (n : ℝ)*eps^2
      · simp [frontierResources, hdense]
        ring
      · by_cases hn : n = 2
        · simp [frontierResources, hn] at hb
        · simp only [frontierResources, hn, hsmall, hdense, ↓reduceIte] at hb
          split_ifs at hb
  simp only [frontierNormEstimate, hb]
  apply congrArg ((d : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro j _
  simp only [hybridColumn, frontierPolynomialEstimate_eq_polynomialEstimate]
  rw [hradius]
  rfl

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated hn condition](hyp:hn), [the stated hb condition](hyp:hb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hm condition](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated hm d condition](hyp:hmD). [The actual hybrid transcript branch inherits its finite calibrated norm MSE](goal). -/
-- @node: frontierNormEstimate_hybrid_mse
lemma frontierNormEstimate_hybrid_mse
    (hMean : BoundedMeanConcentration) (hCheb : CaiLowChebyshevApproximation)
    (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (hb : (frontierResources n d eps).branch = .hybrid)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hAllowed : Allowed n d eps) (hm : 0 < n / 3) (hL : 4096 ≤ logDim d)
    (hD : (frontierResources n d eps).degree = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊)
    (hmD : 2*(frontierResources n d eps).degree ≤ n / 3) :
    (∫ z, (frontierNormEstimate n d eps z - signedNorm (contrast P))^2
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) ≤
        500000000 * sigmaSquared d (n / 3) eps / logDim d := by
  simp_rw [frontierNormEstimate_hybrid n d eps hb]
  have htransfer := frontierBlocks_integral n d eps hn P
    (fun z => ((d : ℝ)⁻¹ * ∑ j, hybridColumn eps
      (frontierResources n d eps).degree j z - signedNorm (contrast P))^2)
  exact htransfer.le.trans (hybrid_average_mse_bound hMean hCheb S hIID P hP eps
    hAllowed hm _ hL hD hmD (by omega))

/-- Assume [the stated hn condition](hyp:hn), [the causal-model conditions for the data law](hyp:hP), and [dimension at least two](hyp:hd). [Projection and the signed causal bridge reduce value error to baseline and norm errors](goal). -/
-- @node: frontierEstimate_sq_error_le_components
lemma frontierEstimate_sq_error_le_components (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hd : 2 ≤ d) (z : ProtocolTranscript (frontierProtocol n d eps)) :
    (frontierEstimate n d eps (z,(0 : Fin 1),0) - value P)^2 ≤
      2*(frontierBaselineEstimate n d eps z - baseline P)^2 +
        (1/2 : ℝ)*(frontierNormEstimate n d eps z - signedNorm (contrast P))^2 := by
  have hv := causal_value_range P hP (by omega)
  simp only [frontierEstimate, hn, ↓reduceIte]
  apply (twoCell_projection_sq_le _ _ hv).trans
  rw [causal_value_decomposition P hP hd]
  nlinarith [sq_nonneg ((frontierBaselineEstimate n d eps z - baseline P) -
    (frontierNormEstimate n d eps z - signedNorm (contrast P))/2)]

/-- Assume [the stated hn condition](hyp:hn), [the causal-model conditions for the data law](hyp:hP), and [dimension at least two](hyp:hd). [Finite-product value risk is controlled by the two actual component MSEs](goal). -/
-- @node: frontier_product_risk_le_components
lemma frontier_product_risk_le_components (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (hd : 2 ≤ d) (L : Measure (Fin n → FrontierMessage d)) [IsFiniteMeasure L] :
    (∫⁻ z, ENNReal.ofReal ((frontierEstimate n d eps (z,(0 : Fin 1),0) - value P)^2) ∂L) ≤
      ENNReal.ofReal (2*(∫ z, (frontierBaselineEstimate n d eps z - baseline P)^2 ∂L) +
        (1/2 : ℝ)*(∫ z, (frontierNormEstimate n d eps z - signedNorm (contrast P))^2 ∂L)) := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (2*(frontierBaselineEstimate n d eps z - baseline P)^2 +
        (1/2 : ℝ)*(frontierNormEstimate n d eps z - signedNorm (contrast P))^2) ∂L := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (frontierEstimate_sq_error_le_components n d eps hn P hP hd z)
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite)
        (Filter.Eventually.of_forall (fun z => by positivity))]
      congr 1
      have hB : Integrable (fun z : Fin n → FrontierMessage d =>
          2*(frontierBaselineEstimate n d eps z - baseline P)^2) L := Integrable.of_finite
      have hF : Integrable (fun z : Fin n → FrontierMessage d =>
          (1/2 : ℝ)*(frontierNormEstimate n d eps z - signedNorm (contrast P))^2) L :=
        Integrable.of_finite
      integral_linearity

end CausalSmith.Stat.LdpOptvalueUniformFrontier
