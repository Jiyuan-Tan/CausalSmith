module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.CenteredProducts

/-!
# Tilted Walsh moments

Exact orthogonality and cross-column moments for the finite product basis.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n m d : ℕ}
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), [the coordinate index](hyp:j), [the finite index set J](hyp:J), and [the function z](hyp:z). [Standardized tilted sign product basis within a column](goal). -/
-- @node: columnWalsh
def columnWalsh (P : Measure (FullRecord d)) (eps : ℝ) (j : Fin d)
    (J : Finset (Fin m)) (z : Fin m → Fin d → Bool) : ℝ :=
  ∏ i ∈ J, (scaledMessages eps z i j - contrast P j) /
    Real.sqrt ((noiseScale d eps)^2 - (contrast P j)^2)

/-- [The integral block variance agrees with Mathlib's variance on this finite space](goal). -/
-- @node: blockVar_eq_variance
lemma blockVar_eq_variance (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (f : (Fin m → Fin d → Bool) → ℝ) :
    blockVar P eps f = variance f (vectorBlockLaw P eps m) := by
  rw [variance_eq_integral (by fun_prop)]
  rfl

/-- [The covariance diagonal is exactly the block variance](goal). -/
-- @node: blockCov_self
lemma blockCov_self (P : Measure (FullRecord d)) (eps : ℝ)
    (f : (Fin m → Fin d → Bool) → ℝ) : blockCov P eps f f = blockVar P eps f := by
  simp only [blockCov, blockVar, pow_two]

/-- [Finite covariance expansion of the average, with no independence between columns](goal). -/
-- @node: blockVar_average_eq_covariance_sum
lemma blockVar_average_eq_covariance_sum (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (f : Fin d → (Fin m → Fin d → Bool) → ℝ) :
    blockVar P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) =
      ((d : ℝ)⁻¹)^2 * ∑ j, ∑ j', blockCov P eps (f j) (f j') := by
  letI := vectorBlockLaw_probability P eps m
  rw [blockVar_eq_variance, variance_const_mul,
    variance_fun_sum (fun _ => MemLp.of_discrete)]
  rfl

/-- Assume [a positive privacy budget](hyp:heps) and [positive dimension](hyp:hd). [The signed-vector scale exceeds the number of cells](goal). -/
-- @node: noiseScale_gt_dimension
lemma noiseScale_gt_dimension (eps : ℝ) (heps : 0 < eps) (hd : 0 < d) :
    (d : ℝ) < noiseScale d eps := by
  have hdelta : 0 < privacyDelta eps := by
    rw [privacyDelta_exp_formula]
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr heps)) (by positivity)
  have hlt := (privacyDelta_bounds eps heps.le).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold noiseScale
  apply (lt_div_iff₀ hdelta).mpr
  nlinarith

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The variance of a scaled sign is strictly positive throughout the causal cube](goal). -/
-- @node: column_scale_variance_pos
lemma column_scale_variance_pos (P : Measure (FullRecord d)) (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (j : Fin d) :
    0 < (noiseScale d eps)^2 - (contrast P j)^2 := by
  have hb := noiseScale_gt_dimension (d := d) eps heps (by omega)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht := contrast_mem_parameterCube P hP j
  have hs : 0 ≤ (1/2 - contrast P j) * (contrast P j + 1/2) :=
    mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
  nlinarith

/-- [Normalized products are centered column products divided by their scale power](goal). -/
-- @node: columnWalsh_eq_centeredColumnProduct
lemma columnWalsh_eq_centeredColumnProduct (P : Measure (FullRecord d)) (eps : ℝ)
    (j : Fin d) (J : Finset (Fin m)) (z : Fin m → Fin d → Bool) :
    columnWalsh P eps j J z = centeredColumnProduct P eps j J z /
      (Real.sqrt ((noiseScale d eps)^2 - (contrast P j)^2))^J.card := by
  simp [columnWalsh, centeredColumnProduct, centeredRow, scaledMessages,
    Finset.prod_div_distrib]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated jk condition](hyp:hJK). [Unequal Walsh subsets have zero mixed moment in any pair of columns](goal). -/
-- @node: blockMean_columnWalsh_mul_ne
lemma blockMean_columnWalsh_mul_ne (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j j' : Fin d) (J K : Finset (Fin m)) (hJK : J ≠ K) :
    blockMean P eps (fun z => columnWalsh P eps j J z * columnWalsh P eps j' K z) = 0 := by
  simp_rw [columnWalsh_eq_centeredColumnProduct, div_mul_div_comm]
  unfold blockMean
  rw [integral_div]
  change blockMean P eps (fun z => centeredColumnProduct P eps j J z *
    centeredColumnProduct P eps j' K z) / _ = 0
  rw [blockMean_centeredColumnProduct_mul_ne P hP eps heps hd j j' J K hJK, zero_div]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Every Walsh product has unit second moment, including the empty subset](goal). -/
-- @node: blockMean_columnWalsh_sq
lemma blockMean_columnWalsh_sq (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j : Fin d) (J : Finset (Fin m)) :
    blockMean P eps (fun z => (columnWalsh P eps j J z)^2) = 1 := by
  simp_rw [columnWalsh_eq_centeredColumnProduct, div_pow]
  unfold blockMean
  rw [integral_div]
  change blockMean P eps (fun z => (centeredColumnProduct P eps j J z)^2) / _ = 1
  rw [blockMean_centeredColumnProduct_sq P hP eps heps hd]
  have hv := column_scale_variance_pos P hP eps heps hd j
  rw [← pow_mul, mul_comm J.card 2, pow_mul, Real.sq_sqrt hv.le]
  exact div_self (pow_ne_zero _ hv.ne')

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated j condition](hyp:hJ). [Nonempty Walsh products are centered](goal). -/
-- @node: blockMean_columnWalsh_nonempty
lemma blockMean_columnWalsh_nonempty (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j : Fin d) (J : Finset (Fin m)) (hJ : J.Nonempty) :
    blockMean P eps (columnWalsh P eps j J) = 0 := by
  have h := blockMean_columnWalsh_mul_ne P hP eps heps hd j j J ∅ hJ.ne_empty
  change blockMean P eps (fun z => columnWalsh P eps j J z) = 0
  simpa only [columnWalsh, Finset.prod_empty, mul_one] using h

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The finite within-column product family is orthonormal](goal). -/
-- @node: blockMean_columnWalsh_orthonormal
lemma blockMean_columnWalsh_orthonormal (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j : Fin d) (J K : Finset (Fin m)) :
    blockMean P eps (fun z => columnWalsh P eps j J z * columnWalsh P eps j K z) =
      if J = K then 1 else 0 := by
  classical
  by_cases hJK : J = K
  · subst K
    simpa only [if_true, ← pow_two] using blockMean_columnWalsh_sq P hP eps heps hd j J
  · rw [if_neg hJK]
    exact blockMean_columnWalsh_mul_ne P hP eps heps hd j j J K hJK

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [Equal-subset cross-column Walsh moments are powers of the exact row correlation](goal). -/
-- @node: blockMean_columnWalsh_cross
lemma blockMean_columnWalsh_cross (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j j' : Fin d) (hjj : j ≠ j') (J : Finset (Fin m)) :
    blockMean P eps (fun z => columnWalsh P eps j J z * columnWalsh P eps j' J z) =
      (-(contrast P j * contrast P j') /
        Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
          ((noiseScale d eps)^2 - (contrast P j')^2)))^J.card := by
  simp_rw [columnWalsh_eq_centeredColumnProduct, div_mul_div_comm]
  unfold blockMean
  rw [integral_div]
  change blockMean P eps (fun z => centeredColumnProduct P eps j J z *
    centeredColumnProduct P eps j' J z) / _ = _
  rw [blockMean_centeredColumnProduct_cross P hP eps heps hd j j' hjj,
    ← mul_pow, ← Real.sqrt_mul (column_scale_variance_pos P hP eps heps hd j).le,
    div_pow]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
