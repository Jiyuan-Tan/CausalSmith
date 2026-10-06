module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Average
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Combined

/-!
# Finite polynomial calibration assembly

Apply the arbitrary-column dependence bound to the combined pilot and evaluation
rows, then add the squared average bias to obtain the finite hybrid MSE bound.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n m d : ℕ}

/-- Assume [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [a privacy budget in the interval from zero to one](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [a block no larger than the sample](hyp:hTwoBlocks), and [the stated hvar condition](hyp:hvar). [The dependence lemma controls the average hybrid variance on the combined rows](goal). -/
-- @node: hybrid_average_variance_le
lemma hybrid_average_variance_le (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : eps ∈ Set.Ioc 0 1) (hd : 2 ≤ d)
    (hm : 0 < m) (hTwoBlocks : 2*m ≤ n) (D : ℕ) (V : ℝ)
    (hvar : ∀ j : Fin d, hybridVar (m := m) P eps (hybridColumn eps D j) ≤ V) :
    hybridVar (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, hybridColumn eps D j z) ≤
      2*V/d := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hdep := (private_moment_and_dependence (m := m+m) S hIID P hP eps heps hd
    (by omega) (by omega)).2.2.2.2.2 (combinedHybridStatistic (m := m) eps D)
    (fun j => by fun_prop)
  have h := hdep.2
  have hcol (j : Fin d) : columnStatistic eps (combinedHybridStatistic (m := m) eps D) j =
      fun z => hybridColumn eps D j (splitHybridRows z) := by
    funext z
    exact (hybridColumn_eq_combined_columnStatistic eps D j z).symm
  simp_rw [hcol] at h
  rw [← hybridVar_eq_combined_blockVar P eps
    (fun z => (d : ℝ)⁻¹ * ∑ j, hybridColumn eps D j z)] at h
  simp_rw [← hybridVar_eq_combined_blockVar] at h
  have hs : sSup (Set.range (fun j : Fin d =>
      hybridVar (m := m) P eps (hybridColumn eps D j))) ≤ V := by
    apply csSup_le
    · exact Set.range_nonempty (fun j : Fin d =>
        hybridVar (m := m) P eps (hybridColumn eps D j))
    · rintro _ ⟨j, rfl⟩
      exact hvar j
  calc
    _ ≤ (2/(d : ℝ)) * sSup (Set.range (fun j =>
        hybridVar (m := m) P eps (hybridColumn eps D j))) := h
    _ ≤ (2/(d : ℝ)) * V := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), [the stated hm d condition](hyp:hmD), and [a block no larger than the sample](hyp:hTwoBlocks). [Combined-row variance and the calibrated bias give the roadmap's final hybrid MSE](goal). -/
-- @node: hybrid_average_mse_bound
lemma hybrid_average_mse_bound (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation) (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (hAllowed : Allowed n d eps) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hmD : 2*D ≤ m)
    (hTwoBlocks : 2*m ≤ n) :
    hybridMean (m := m) P eps (fun z => ((d : ℝ)⁻¹ * (∑ j, hybridColumn eps D j z) -
      signedNorm (contrast P))^2) ≤ 500000000 * sigmaSquared d m eps / logDim d := by
  have hvar := hybrid_average_variance_le S hIID P hP eps hAllowed.2.2 hAllowed.2.1
    hm hTwoBlocks D (400*sigmaSquared d m eps*logDim d*Real.exp (logDim d/100))
    (fun j => hybrid_variance_bound hMean hCheb P hP eps hAllowed.2.2.1
      hAllowed.2.1 hm D hL hD hmD j)
  have hd : 2 ≤ d := hAllowed.2.1
  have henv := hybrid_average_variance_envelope_le (m := m) (d := d) eps (by omega) hL
  have hvar' : hybridVar (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, hybridColumn eps D j z) ≤
      3200*sigmaSquared d m eps/logDim d := by
    apply hvar.trans
    convert henv using 1 <;> first | rfl | ring
  have hbias := hybrid_average_bias_sq_bound hMean hCheb P hP eps hAllowed.2.2.1
    hAllowed.2.1 hm D hL hD (by omega)
  have hmse := hybrid_mse_le_variance_add_bias_bounds P eps (signedNorm (contrast P))
    _ _ _ hvar' hbias
  have hs : 0 ≤ sigmaSquared d m eps / logDim d := by
    unfold sigmaSquared
    positivity
  calc
    _ ≤ 3200*sigmaSquared d m eps/logDim d +
        400000000*sigmaSquared d m eps/logDim d := hmse
    _ = 400003200 * (sigmaSquared d m eps/logDim d) := by ring
    _ ≤ 500000000 * (sigmaSquared d m eps/logDim d) :=
      mul_le_mul_of_nonneg_right (by norm_num) hs
    _ = _ := by ring

-- @node: lem:finite-private-polynomial-calibration
/-- [Bounded mean concentration](hyp:hMean_of_gate),
[Chebyshev approximation](hyp:hCheb_of_gate), [iid sampling](hyp:hIID),
[causal-model validity](hyp:hP), [allowed resources](hyp:hAllowed), and
[positive block size within the sample](hyp:hm,hmn) imply [both the global-polynomial
and hybrid finite calibration bounds](goal). -/
lemma finite_private_polynomial_calibration
    (hMean_of_gate : BoundedMeanConcentration) (hCheb_of_gate : CaiLowChebyshevApproximation)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (hAllowed : Allowed n d eps) (hm : 0 < m) (hmn : m ≤ n) :
    (∀ D : ℕ, Even D → 2 ≤ D → 2*D ≤ m →
      (D : ℝ) ≤ (1/1024 : ℝ) * logDim d /
        Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d) →
      (∀ j : Fin d, abs (blockMean (m := m) P eps (polynomialEstimate eps (1/2) D j) - abs
        (contrast P j)) ≤
        1/(D+1)) ∧
      blockVar (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, polynomialEstimate eps (1/2) D j z) ≤
        Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d))/(2*d)) ∧
    (∀ D : ℕ, 4096 ≤ logDim d → D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊ →
      2*D ≤ m → 2*m ≤ n →
      (∀ j : Fin d,
        abs (hybridMean (m := m) P eps (hybridColumn eps D j) - abs (contrast P j)) ≤
          20000*Real.sqrt (sigmaSquared d m eps)/Real.sqrt (logDim d) ∧
        hybridVar (m := m) P eps (hybridColumn eps D j) ≤
          400*sigmaSquared d m eps * logDim d * Real.exp (logDim d/100)) ∧
      hybridMean (m := m) P eps (fun z => ((d : ℝ)⁻¹ * (∑ j, hybridColumn eps D j z) -
        signedNorm (contrast P))^2) ≤ 500000000 * sigmaSquared d m eps/logDim d) := by
  constructor
  · intro D hEven hD hmD hDegree
    exact global_polynomial_calibration_of_gate hCheb_of_gate hMean_of_gate
      S hIID P hP eps hAllowed hm hmn D hEven hD hmD hDegree
  · intro D hL hDegree hmD hTwoBlocks
    constructor
    · intro j
      exact ⟨hybrid_bias_bound hMean_of_gate hCheb_of_gate P hP eps
        hAllowed.2.2.1 hAllowed.2.1 hm D hL hDegree (by omega) j,
        hybrid_variance_bound hMean_of_gate hCheb_of_gate P hP eps
        hAllowed.2.2.1 hAllowed.2.1 hm D hL hDegree hmD j⟩
    · exact hybrid_average_mse_bound hMean_of_gate hCheb_of_gate S hIID P hP eps
        hAllowed hm D hL hDegree hmD hTwoBlocks

end CausalSmith.Stat.LdpOptvalueUniformFrontier
