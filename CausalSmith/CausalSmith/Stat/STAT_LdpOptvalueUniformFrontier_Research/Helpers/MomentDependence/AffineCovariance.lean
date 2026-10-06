module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.Moments
public import Causalean.Tactic.IntegralLinearity

/-!
# Affine column covariance

Exact covariance and variance calculations for affine functions of a single private row.
These give the degree-zero and one-row cases of the finite Walsh covariance argument.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the function f and the function g](hyp:f,g). [Covariance on the finite message block](goal). -/
-- @node: blockCov
def blockCov (P : Measure (FullRecord d)) (eps : ℝ)
    (f g : (Fin m → Fin d → Bool) → ℝ) : ℝ :=
  ∫ z, (f z - blockMean (m := m) P eps f) * (g z - blockMean (m := m) P eps g) ∂(vectorBlockLaw
    P eps m)

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [The private block mean of an affine coordinate is its affine contrast](goal). -/
-- @node: blockMean_affine_scaled
lemma blockMean_affine_scaled (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (i : Fin m) (j : Fin d) (a c : ℝ) :
    blockMean P eps (fun z => a + c * scaledMessages eps z i j) = a + c * contrast P j := by
  letI := vectorBlockLaw_probability P eps m
  have hmean := blockMean_scaledMessages_eq_rowMean P eps i j
  rw [vectorMessageLaw_scaled_sign_integral P hP eps heps hd j] at hmean
  unfold blockMean at hmean ⊢
  integral_linearity
  rw [hmean]
  simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Centered affine coordinates have the exact scaled-coordinate variance](goal). -/
-- @node: blockVar_affine_scaled
lemma blockVar_affine_scaled (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (i : Fin m) (j : Fin d) (a c : ℝ) :
    blockVar P eps (fun z => a + c * scaledMessages eps z i j) =
      c^2 * ((noiseScale d eps)^2 - (contrast P j)^2) := by
  letI := vectorBlockLaw_probability P eps m
  have hmean := blockMean_scaledMessages_eq_rowMean P eps i j
  rw [vectorMessageLaw_scaled_sign_integral P hP eps heps hd j] at hmean
  have hsecond := blockMean_scaledMessages_sq P eps i j
  unfold blockMean at hmean hsecond
  unfold blockVar
  rw [blockMean_affine_scaled P hP eps heps hd]
  have hp (z : Fin m → Fin d → Bool) :
      (a + c * scaledMessages eps z i j - (a + c * contrast P j))^2 =
      c^2 * (scaledMessages eps z i j)^2 -
        (2*c^2*contrast P j) * scaledMessages eps z i j + c^2*(contrast P j)^2 := by ring
  simp_rw [hp]
  simp (disch := exact Integrable.of_finite) only [integral_add, integral_sub,
    integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hmean, hsecond]
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the stated hjj condition](hyp:hjj). [Distinct affine coordinates have covariance coming solely from their nonzero means](goal). -/
-- @node: blockCov_affine_scaled
lemma blockCov_affine_scaled (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (i : Fin m) (j j' : Fin d) (hjj : j ≠ j') (a c a' c' : ℝ) :
    blockCov P eps (fun z => a + c * scaledMessages eps z i j)
      (fun z => a' + c' * scaledMessages eps z i j') =
        -(c*c' * contrast P j * contrast P j') := by
  letI := vectorBlockLaw_probability P eps m
  have hmean (l : Fin d) := blockMean_scaledMessages_eq_rowMean P eps i l
  simp_rw [vectorMessageLaw_scaled_sign_integral P hP eps heps hd] at hmean
  have hcross := blockMean_scaledMessages_cross P eps i j j' hjj
  unfold blockMean at hmean hcross
  unfold blockCov
  rw [blockMean_affine_scaled P hP eps heps hd,
    blockMean_affine_scaled P hP eps heps hd]
  have hp (z : Fin m → Fin d → Bool) :
      (a + c * scaledMessages eps z i j - (a + c * contrast P j)) *
      (a' + c' * scaledMessages eps z i j' - (a' + c' * contrast P j')) =
      (c*c') * (scaledMessages eps z i j * scaledMessages eps z i j') -
      (c*c'*contrast P j') * scaledMessages eps z i j -
      (c*c'*contrast P j) * scaledMessages eps z i j' + c*c'*contrast P j*contrast P j' := by ring
  simp_rw [hp]
  simp (disch := exact Integrable.of_finite) only [integral_add, integral_sub,
    integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hmean j, hmean j', hcross]
  ring

/-- Assume [the stated hb condition](hyp:hb). [A nonzero scaled sign supports affine interpolation of any one-row column statistic](goal). -/
-- @node: columnStatistic_one_affine
lemma columnStatistic_one_affine (eps : ℝ) (hb : noiseScale d eps ≠ 0)
    (g : Fin d → (Fin 1 → ℝ) → ℝ) (j : Fin d) :
    ∃ a c : ℝ, columnStatistic eps g j =
      (fun z : Fin 1 → Fin d → Bool => a + c * scaledMessages eps z 0 j) := by
  let p := g j (fun _ => noiseScale d eps)
  let q := g j (fun _ => -noiseScale d eps)
  refine ⟨(p+q)/2, (p-q)/(2*noiseScale d eps), ?_⟩
  funext z
  have hcol : (fun i : Fin 1 => scaledMessages eps z i j) =
      (fun _ : Fin 1 => noiseScale d eps * signVal (z 0 j)) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  unfold columnStatistic
  rw [hcol]
  change g j (fun _ => noiseScale d eps * signVal (z 0 j)) = _
  cases hz : z 0 j <;> simp only [scaledMessages, hz, signVal, Bool.false_eq_true,
    ↓reduceIte, mul_neg_one, mul_one]
  · change q = _
    field_simp
    <;> ring
  · change p = _
    field_simp
    <;> ring

/-- [On an empty block every column statistic is constant](goal). -/
-- @node: columnStatistic_zero_constant
lemma columnStatistic_zero_constant (eps : ℝ)
    (g : Fin d → (Fin 0 → ℝ) → ℝ) (j : Fin d) :
    columnStatistic eps g j = (fun _ : Fin 0 → Fin d → Bool => g j (fun _ => 0)) := by
  funext z
  unfold columnStatistic
  congr 1
  funext i
  exact Fin.elim0 i

/-- [A constant statistic has zero covariance with every finite block statistic](goal). -/
-- @node: blockCov_const_left
lemma blockCov_const_left (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps a : ℝ) (f : (Fin m → Fin d → Bool) → ℝ) :
    blockCov P eps (fun _ => a) f = 0 := by
  letI := vectorBlockLaw_probability P eps m
  simp [blockCov, blockMean]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
