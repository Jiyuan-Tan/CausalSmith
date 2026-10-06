module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.WalshMoments
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite Walsh expansion

Completeness of the tilted Boolean product basis and exact expansions of column statistics.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), [the coordinate index](hyp:j), [the finite index set J](hyp:J), and [the function x](hyp:x). [The tilted Walsh product as a function of one Boolean column](goal). -/
-- @node: booleanColumnWalsh
def booleanColumnWalsh (P : Measure (FullRecord d)) (eps : ℝ) (j : Fin d)
    (J : Finset (Fin m)) (x : Fin m → Bool) : ℝ :=
  ∏ i ∈ J, (noiseScale d eps * signVal (x i) - contrast P j) /
    Real.sqrt ((noiseScale d eps)^2 - (contrast P j)^2)

/-- [Pulling a Boolean Walsh function back to released rows gives the column basis](goal). -/
-- @node: booleanColumnWalsh_pullback
lemma booleanColumnWalsh_pullback (P : Measure (FullRecord d)) (eps : ℝ) (j : Fin d)
    (J : Finset (Fin m)) (z : Fin m → Fin d → Bool) :
    booleanColumnWalsh P eps j J (fun i => z i j) = columnWalsh P eps j J z := by
  rfl

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Orthogonality detects every coefficient, so the Boolean product functions are independent](goal). -/
-- @node: booleanColumnWalsh_linearIndependent
lemma booleanColumnWalsh_linearIndependent (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (j : Fin d) :
    LinearIndependent ℝ (booleanColumnWalsh (m := m) P eps j) := by
  classical
  letI := vectorBlockLaw_probability P eps m
  rw [Fintype.linearIndependent_iff]
  intro c hc J
  have hzero (z : Fin m → Fin d → Bool) :
      (∑ K : Finset (Fin m), c K * columnWalsh P eps j K z) = 0 := by
    have h := congrFun hc (fun i => z i j)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      booleanColumnWalsh_pullback, Pi.zero_apply] using h
  have h := congrArg (fun f : (Fin m → Fin d → Bool) → ℝ => blockMean P eps f)
    (show (fun z => (∑ K : Finset (Fin m), c K * columnWalsh P eps j K z) *
      columnWalsh P eps j J z) = fun _ => 0 by funext z; rw [hzero z, zero_mul])
  simp only [Finset.sum_mul] at h
  simp only [mul_assoc, blockMean] at h
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)] at h
  simp only [integral_const_mul, integral_zero] at h
  change (∑ K : Finset (Fin m), c K * blockMean P eps
    (fun z => columnWalsh P eps j K z * columnWalsh P eps j J z)) = 0 at h
  simp_rw [blockMean_columnWalsh_orthonormal P hP eps heps hd] at h
  simpa using h

/-- Fix [the probability law P](hyp:P), [the causal-model conditions for the data law](hyp:hP), [the privacy budget](hyp:eps), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the coordinate index](hyp:j). [Counting Boolean configurations makes the independent product family a full basis](goal). -/
-- @node: booleanColumnWalshBasis
def booleanColumnWalshBasis (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (j : Fin d) :
    Module.Basis (Finset (Fin m)) ℝ ((Fin m → Bool) → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (booleanColumnWalsh_linearIndependent P hP eps heps hd j) (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [Fintype.card_finset, Fintype.card_fun])

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Every statistic of one column has a finite tilted Walsh expansion](goal). -/
-- @node: columnStatistic_walsh_expansion
lemma columnStatistic_walsh_expansion (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (g : Fin d → (Fin m → ℝ) → ℝ) (j : Fin d) :
    ∃ c : Finset (Fin m) → ℝ, ∀ z,
      columnStatistic eps g j z = ∑ J, c J * columnWalsh P eps j J z := by
  classical
  let B := booleanColumnWalshBasis (m := m) P hP eps heps hd j
  let f : (Fin m → Bool) → ℝ := fun x => g j (fun i => noiseScale d eps * signVal (x i))
  refine ⟨fun J => B.repr f J, ?_⟩
  intro z
  have h := congrFun (B.sum_repr f) (fun i => z i j)
  have hB : ∀ J, B J = booleanColumnWalsh P eps j J := by
    intro J
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) J
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hB,
    booleanColumnWalsh_pullback] at h
  exact h.symm


/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Only the empty Walsh subset contributes to a column mean](goal). -/
-- @node: blockMean_walsh_sum
lemma blockMean_walsh_sum (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j : Fin d) (c : Finset (Fin m) → ℝ) :
    blockMean P eps (fun z => ∑ J, c J * columnWalsh P eps j J z) = c ∅ := by
  classical
  letI := vectorBlockLaw_probability P eps m
  have hmean (J : Finset (Fin m)) : blockMean P eps (columnWalsh P eps j J) =
      if J = ∅ then 1 else 0 := by
    by_cases hJ : J = ∅
    · subst J
      simp [columnWalsh, blockMean]
    · rw [if_neg hJ]
      exact blockMean_columnWalsh_nonempty P hP eps heps hd j J
        (Finset.nonempty_iff_ne_empty.mpr hJ)
  unfold blockMean
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_const_mul]
  change (∑ J, c J * blockMean P eps (columnWalsh P eps j J)) = _
  simp_rw [hmean]
  simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [Centering deletes precisely the empty-subset coefficient in the finite expansion](goal). -/
-- @node: columnStatistic_centered_walsh_expansion
lemma columnStatistic_centered_walsh_expansion (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (g : Fin d → (Fin m → ℝ) → ℝ) (j : Fin d) :
    ∃ c : Finset (Fin m) → ℝ, c ∅ = 0 ∧ ∀ z,
      columnStatistic eps g j z - blockMean P eps (columnStatistic eps g j) =
        ∑ J, c J * columnWalsh P eps j J z := by
  classical
  obtain ⟨c, hc⟩ := columnStatistic_walsh_expansion P hP eps heps hd g j
  have hmean : blockMean P eps (columnStatistic eps g j) = c ∅ := by
    rw [show columnStatistic eps g j = (fun z => ∑ J, c J * columnWalsh P eps j J z)
      from funext hc]
    exact blockMean_walsh_sum P hP eps heps hd j c
  refine ⟨fun J => c J - if J = ∅ then c ∅ else 0, by simp, ?_⟩
  intro z
  rw [hmean, hc]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp [ite_mul, columnWalsh]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), and [dimension at least two](hyp:hd). [All off-diagonal subset terms vanish in the product of two finite expansions](goal). -/
-- @node: blockMean_walsh_sum_mul
lemma blockMean_walsh_sum_mul (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j j' : Fin d) (c c' : Finset (Fin m) → ℝ) :
    blockMean P eps (fun z => (∑ J, c J * columnWalsh P eps j J z) *
      (∑ K, c' K * columnWalsh P eps j' K z)) =
      ∑ J, c J * c' J * blockMean P eps
        (fun z => columnWalsh P eps j J z * columnWalsh P eps j' J z) := by
  classical
  letI := vectorBlockLaw_probability P eps m
  simp only [Finset.sum_mul, Finset.mul_sum, blockMean]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro J _
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have halg (K : Finset (Fin m)) (z : Fin m → Fin d → Bool) :
      c K * columnWalsh P eps j K z * (c' J * columnWalsh P eps j' J z) =
      (c K * c' J) * (columnWalsh P eps j K z * columnWalsh P eps j' J z) := by ring
  simp_rw [halg, integral_const_mul]
  change (∑ K, (c K * c' J) * blockMean P eps
    (fun z => columnWalsh P eps j K z * columnWalsh P eps j' J z)) = _
  rw [Finset.sum_eq_single J]
  · rfl
  · intro K _ hK
    rw [blockMean_columnWalsh_mul_ne P hP eps heps hd j j' K J hK, mul_zero]
  · simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), and [the function hf](hyp:hf). [Parseval's identity expresses each centered column variance as a finite sum of squares](goal). -/
-- @node: blockVar_walsh_expansion
lemma blockVar_walsh_expansion (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j : Fin d) (f : (Fin m → Fin d → Bool) → ℝ) (c : Finset (Fin m) → ℝ)
    (hf : ∀ z, f z - blockMean P eps f = ∑ J, c J * columnWalsh P eps j J z) :
    blockVar P eps f = ∑ J, (c J)^2 := by
  change blockMean P eps (fun z => (f z - blockMean P eps f)^2) = _
  simp_rw [hf, pow_two]
  rw [blockMean_walsh_sum_mul P hP eps heps hd]
  simp_rw [blockMean_columnWalsh_orthonormal P hP eps heps hd]
  simp

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [the stated hjj condition](hyp:hjj), [the function hf](hyp:hf), and [the function hf'](hyp:hf'). [Cross-column covariance is the diagonal coefficient sum weighted by row-correlation powers](goal). -/
-- @node: blockCov_walsh_expansion
lemma blockCov_walsh_expansion (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (j j' : Fin d) (hjj : j ≠ j') (f f' : (Fin m → Fin d → Bool) → ℝ)
    (c c' : Finset (Fin m) → ℝ)
    (hf : ∀ z, f z - blockMean P eps f = ∑ J, c J * columnWalsh P eps j J z)
    (hf' : ∀ z, f' z - blockMean P eps f' = ∑ J, c' J * columnWalsh P eps j' J z) :
    blockCov P eps f f' = ∑ J, c J * c' J *
      (-(contrast P j * contrast P j') /
        Real.sqrt (((noiseScale d eps)^2 - (contrast P j)^2) *
          ((noiseScale d eps)^2 - (contrast P j')^2)))^J.card := by
  change blockMean P eps (fun z => (f z - blockMean P eps f) *
    (f' z - blockMean P eps f')) = _
  simp_rw [hf, hf']
  rw [blockMean_walsh_sum_mul P hP eps heps hd]
  simp_rw [blockMean_columnWalsh_cross P hP eps heps hd j j' hjj]


/-- Assume [the stated hc condition](hyp:hc) and [the stated hr condition](hyp:hr). [Cauchy–Schwarz bounds the diagonal expansion after the constant coefficient is removed](goal). -/
-- @node: walsh_diagonal_sum_abs_le
lemma walsh_diagonal_sum_abs_le (c c' : Finset (Fin m) → ℝ) (hc : c ∅ = 0)
    (r : ℝ) (hr : |r| ≤ 1) :
    |∑ J, c J * c' J * r^J.card| ≤
      |r| * Real.sqrt ((∑ J, (c J)^2) * ∑ J, (c' J)^2) := by
  classical
  have hp : ∀ k : ℕ, |r|^(k+1) ≤ |r| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        _ ≤ |r| * |r| := mul_le_mul_of_nonneg_right ih (abs_nonneg r)
        _ ≤ |r| := by nlinarith [abs_nonneg r]
  have hterm (J : Finset (Fin m)) :
      |c J * c' J * r^J.card| ≤ |r| * (|c J| * |c' J|) := by
    by_cases hJ : J = ∅
    · subst J
      simp [hc]
    · have hcard : J.card ≠ 0 := by simpa using hJ
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard
      rw [abs_mul, abs_mul, abs_pow, hk]
      have h := mul_le_mul_of_nonneg_left (hp k) (mul_nonneg (abs_nonneg (c J)) (abs_nonneg (c' J)))
      simpa [mul_comm] using h
  have hCS : (∑ J, |c J| * |c' J|) ≤
      Real.sqrt ((∑ J, (c J)^2) * ∑ J, (c' J)^2) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Finset (Fin m))) (fun J => |c J|) (fun J => |c' J|)
  calc
    _ ≤ ∑ J, |c J * c' J * r^J.card| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ J, |r| * (|c J| * |c' J|) := Finset.sum_le_sum (fun J _ => hterm J)
    _ = |r| * ∑ J, |c J| * |c' J| := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hCS (abs_nonneg _)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
