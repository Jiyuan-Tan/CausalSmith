module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.AffineCovariance

/-!
# Centered finite column products

Independence of participant rows diagonalizes the centered product moments, both
within one column and between distinct columns. These are the finite Walsh
calculations used by the column covariance proof.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), [the coordinate index](hyp:j), and [the function z](hyp:z). [The centered scaled sign in a single released row](goal). -/
-- @node: centeredRow
def centeredRow (P : Measure (FullRecord d)) (eps : ℝ) (j : Fin d)
    (z : Fin d → Bool) : ℝ := noiseScale d eps * signVal (z j) - contrast P j

/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), [the coordinate index](hyp:j), [the finite index set J](hyp:J), and [the function z](hyp:z). [A product of centered entries indexed by a participant subset](goal). -/
-- @node: centeredColumnProduct
def centeredColumnProduct (P : Measure (FullRecord d)) (eps : ℝ)
    (j : Fin d) (J : Finset (Fin m)) (z : Fin m → Fin d → Bool) : ℝ :=
  ∏ i ∈ J, centeredRow P eps j (z i)

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Centering removes the one-row mean](goal). -/
-- @node: integral_centeredRow
lemma integral_centeredRow (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (j : Fin d) :
    (∫ z, centeredRow P eps j z ∂vectorMessageLaw P eps) = 0 := by
  letI := vectorMessageLaw_probability P eps
  unfold centeredRow
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    vectorMessageLaw_scaled_sign_integral P hP eps heps hd]
  simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The centered one-row second moment is its exact variance](goal). -/
-- @node: integral_centeredRow_sq
lemma integral_centeredRow_sq (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (j : Fin d) :
    (∫ z, (centeredRow P eps j z)^2 ∂vectorMessageLaw P eps) =
      (noiseScale d eps)^2 - (contrast P j)^2 := by
  letI := vectorMessageLaw_probability P eps
  have hp (z : Fin d → Bool) : (noiseScale d eps * signVal (z j))^2 =
      (noiseScale d eps)^2 := by cases z j <;> simp [signVal]
  have heq (z : Fin d → Bool) : (centeredRow P eps j z)^2 =
      (noiseScale d eps)^2 - 2*contrast P j * (noiseScale d eps * signVal (z j)) +
        (contrast P j)^2 := by unfold centeredRow; nlinarith [hp z]
  have hmean (l : Fin d) := vectorMessageLaw_scaled_sign_integral P hP eps heps hd l
  simp only [integral_const_mul] at hmean
  simp_rw [heq]
  simp (disch := exact Integrable.of_finite) only [integral_add, integral_sub,
    integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hmean j]
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [Distinct centered row coordinates have the negative product of contrasts as their moment](goal). -/
-- @node: integral_centeredRow_cross
lemma integral_centeredRow_cross (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j j' : Fin d) (hjj : j ≠ j') :
    (∫ z, centeredRow P eps j z * centeredRow P eps j' z ∂vectorMessageLaw P eps) =
      -(contrast P j * contrast P j') := by
  letI := vectorMessageLaw_probability P eps
  have heq (z : Fin d → Bool) : centeredRow P eps j z * centeredRow P eps j' z =
      (noiseScale d eps)^2 * (signVal (z j) * signVal (z j')) -
        contrast P j' * (noiseScale d eps * signVal (z j)) -
        contrast P j * (noiseScale d eps * signVal (z j')) +
        contrast P j * contrast P j' := by unfold centeredRow; ring
  have hmean (l : Fin d) := vectorMessageLaw_scaled_sign_integral P hP eps heps hd l
  simp only [integral_const_mul] at hmean
  simp_rw [heq]
  simp (disch := exact Integrable.of_finite) only [integral_add, integral_sub,
    integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [vectorMessageLaw_cross_sign_integral P eps j j' hjj,
    hmean j, hmean j']
  ring

/-- [Products over iid rows factor into their centered one-row moments](goal). -/
-- @node: blockMean_centeredColumnProduct_mul
lemma blockMean_centeredColumnProduct_mul (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) (j j' : Fin d) (J K : Finset (Fin m)) :
    blockMean P eps (fun z => centeredColumnProduct P eps j J z *
      centeredColumnProduct P eps j' K z) =
      ∏ i : Fin m, ∫ z, (if i ∈ J then centeredRow P eps j z else 1) *
        (if i ∈ K then centeredRow P eps j' z else 1) ∂vectorMessageLaw P eps := by
  classical
  letI := vectorMessageLaw_probability P eps
  unfold blockMean vectorBlockLaw centeredColumnProduct
  simp_rw [← Finset.prod_ite_mem_eq J, ← Finset.prod_ite_mem_eq K,
    ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin m => vectorMessageLaw P eps)
    (fun (i : Fin m) (z : Fin d → Bool) =>
      (if i ∈ J then centeredRow P eps j z else 1) *
      (if i ∈ K then centeredRow P eps j' z else 1))

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated jk condition](hyp:hJK). [Unequal participant subsets have zero mixed moment, even across different columns](goal). -/
-- @node: blockMean_centeredColumnProduct_mul_ne
lemma blockMean_centeredColumnProduct_mul_ne (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j j' : Fin d) (J K : Finset (Fin m)) (hJK : J ≠ K) :
    blockMean P eps (fun z => centeredColumnProduct P eps j J z *
      centeredColumnProduct P eps j' K z) = 0 := by
  classical
  rw [blockMean_centeredColumnProduct_mul]
  have hex : ∃ i, (i ∈ J ∧ i ∉ K) ∨ (i ∉ J ∧ i ∈ K) := by
    by_contra h
    apply hJK
    ext i
    have hi := not_exists.mp h i
    tauto
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with ⟨hJ,hK⟩ | ⟨hJ,hK⟩
  · simpa only [hJ, hK, ↓reduceIte, mul_one] using integral_centeredRow P hP eps heps hd j
  · simpa only [hJ, hK, ↓reduceIte, one_mul] using integral_centeredRow P hP eps heps hd j'

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Equal-subset within-column moments are powers of the coordinate variance](goal). -/
-- @node: blockMean_centeredColumnProduct_sq
lemma blockMean_centeredColumnProduct_sq (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j : Fin d) (J : Finset (Fin m)) :
    blockMean P eps (fun z => (centeredColumnProduct P eps j J z)^2) =
      ((noiseScale d eps)^2 - (contrast P j)^2)^J.card := by
  classical
  letI := vectorMessageLaw_probability P eps
  rw [show (fun z => (centeredColumnProduct P eps j J z)^2) =
    (fun z => centeredColumnProduct P eps j J z * centeredColumnProduct P eps j J z)
    from by funext z; exact pow_two _]
  rw [blockMean_centeredColumnProduct_mul]
  have hrow (i : Fin m) :
      (∫ z, (if i ∈ J then centeredRow P eps j z else 1) *
        (if i ∈ J then centeredRow P eps j z else 1) ∂vectorMessageLaw P eps) =
      if i ∈ J then (noiseScale d eps)^2 - (contrast P j)^2 else 1 := by
    by_cases hi : i ∈ J
    · simpa only [hi, ↓reduceIte, ← pow_two] using integral_centeredRow_sq P hP eps heps hd j
    · simp [hi]
  simp_rw [hrow]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [Equal-subset cross-column moments are powers of the exact one-row covariance](goal). -/
-- @node: blockMean_centeredColumnProduct_cross
lemma blockMean_centeredColumnProduct_cross (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j j' : Fin d) (hjj : j ≠ j') (J : Finset (Fin m)) :
    blockMean P eps (fun z => centeredColumnProduct P eps j J z *
      centeredColumnProduct P eps j' J z) = (-(contrast P j * contrast P j'))^J.card := by
  classical
  letI := vectorMessageLaw_probability P eps
  rw [blockMean_centeredColumnProduct_mul]
  have hrow (i : Fin m) :
      (∫ z, (if i ∈ J then centeredRow P eps j z else 1) *
        (if i ∈ J then centeredRow P eps j' z else 1) ∂vectorMessageLaw P eps) =
      if i ∈ J then -(contrast P j * contrast P j') else 1 := by
    by_cases hi : i ∈ J
    · simpa only [hi, ↓reduceIte] using integral_centeredRow_cross P hP eps heps hd j j' hjj
    · simp [hi]
  simp_rw [hrow]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
