module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.PartBCore

/-!
The Part B chaining estimate bounds the signed empirical increment sum by dyadic
radius decrements weighted by logarithmic covering complexity.

The finite-class construction and clean Massart reduction live in
`PartBCore`; this module exposes the resulting chaining bound.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

variable {c : ℝ}

/-- For [a function class evaluated on a finite sample](hyp:Z,m,ι,F,S), [a positive empirical
radius](hyp:c), [positivity of that radius](hyp:c_pos), [total boundedness of the empirical
class](hyp:h'), [a terminal chaining level](hyp:n), [positive sample size](hyp:m_pos), and [a
uniform empirical-radius bound](hyp:cs), [the sum of expected signed chaining increments is
bounded by the corresponding sum of dyadic radius decrements times logarithmic covering
complexities](goal). -/
lemma partB_bound (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) *
      ((chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j) (S i)))) ≤
    ∑ j : Fin n, 6 * (ej c (j + 1) - ej c (j + 2)) *
      (√(4 * Real.log (coveringNumber' h' (ej c (j + 1)))) / ((Real.sqrt m))) := by
  calc
  _ ≤ ∑ j : Fin n,
      (Finset.sup' (incrementPairFinset c_pos h' n j)
        (incrementPairFinset_nonempty c_pos h' n j)
        fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) *
        (√(2 * Real.log (coveringNumber' h' (ej c (j + 1)) *
          coveringNumber' h' (ej c j)))) / ↑m := by
    by_cases n_pos : 0 < n
    · exact partB_sum_bound_via_massart c_pos h' n m_pos cs n_pos
    · simp at n_pos
      rw [n_pos]
      simp
  _ = ∑ j : Fin n,
      (Finset.sup' (incrementPairFinset c_pos h' n j)
        (incrementPairFinset_nonempty c_pos h' n j)
        fun hk ↦ (√(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m) *
        (√(2 * Real.log (coveringNumber' h' (ej c (j + 1)) *
          coveringNumber' h' (ej c j)))) := by
    apply congrArg
    ext j
    rw [<- div_mul_eq_mul_div]
    rw [Mathlib.Tactic.LinearCombination.mul_eq_const]
    rw [Finset.sup'_div₀]
    exact Nat.cast_nonneg m
  _ ≤ ∑ j : Fin n,
      ((6 * (ej c (j + 1) - ej c (j + 2)) / Real.sqrt m) *
        (√(2 * Real.log ((coveringNumber' h' (ej c (j + 1))) *
          (coveringNumber' h' (ej c j)))))) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    apply mul_le_mul_of_nonneg_right
      -- The remaining estimate follows from the pair-class representation.
    · have r0 (hk : (Z → ℝ) × (Z → ℝ))
          (hk0 : hk ∈ incrementPairFinset c_pos h' n j) :
          ∃ fh, (chainApprox c_pos h' fh (j + 1), chainApprox c_pos h' fh j) = hk := by
        dsimp [incrementPairFinset] at hk0
        simp at hk0
        dsimp [incrementPairSet] at hk0
        exact hk0
      have fh (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ incrementPairFinset c_pos h' n j) : ι :=
        Classical.choose (r0 hk hk0)
      suffices ∀ (hk : (Z → ℝ) × (Z → ℝ))
          (hk0 : hk ∈ incrementPairFinset c_pos h' n j),
          (√(∑ i, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m ≤
            6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) / Real.sqrt m from by
        rw [Finset.sup'_le_iff]
        exact this
      intro hk hk0
      have hk1 : hk ∈ incrementPairSet c_pos h' n j := by
        dsimp [incrementPairFinset] at hk0
        simp at hk0
        exact hk0
      dsimp [incrementPairSet] at hk1
      obtain ⟨x, fhx⟩ := hk1
      have r :
          √(∑ i, ((hk.1 - hk.2) (S i)) ^ 2) ≤
            √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) +
              √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) := by
        let ai : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun i ↦ (hk.1 - (F x)) (S i)
        let aj : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun i ↦ (hk.2 - (F x)) (S i)
        have norm_calc : ‖ai - aj‖ = √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2) := by
          calc
          _ =  √(∑ j : Fin m, ‖ai j - aj j‖ ^ 2) := by
            exact (EuclideanSpace.norm_eq (ai - aj))
          _ = _ := by dsimp [ai, aj]; simp
        calc
        _ = ‖ai - aj‖ := by
          dsimp [ai, aj, norm]
          simp
          rw [Real.sqrt_eq_rpow];simp
        _ = ‖ai + (-aj)‖ := rfl
        _ ≤ ‖ai‖ + ‖(-aj)‖ := norm_add_le ai (-aj)
        _ = ‖ai‖ + ‖aj‖ := by simp
        _ = _ := by
          apply Mathlib.Tactic.LinearCombination.add_eq_eq
          · dsimp [ai, norm]
            simp
            rw [Real.sqrt_eq_rpow];simp
          · dsimp [aj, norm]
            simp
            rw [Real.sqrt_eq_rpow];simp
      have r' :
          √(∑ i, ((hk.1 - hk.2) (S i)) ^ 2) / ↑m ≤
            √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m +
              √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m := by
        have :
            (√(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) +
                √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2)) / ↑m =
              √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m +
                √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m := by
          ring
        rw [← this]
        exact div_le_div_of_nonneg_right r (Nat.cast_nonneg m)
      apply le_trans r'
      have rp :
          6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) / Real.sqrt m =
            (ej c (j + 1) / Real.sqrt m) + (ej c j / Real.sqrt m) := by
        suffices
            6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) =
              ej c (j + 1) + ej c j from by
          rw [this]
          exact add_div (ej c ((j : ℕ) + 1)) (ej c (j : ℕ)) (Real.sqrt m)
        have t (j : ℕ) : 2 * ej c ((j : ℕ) + 1) = ej c (j : ℕ) := by
          have two_ne_zero' : (2 : ℝ) ≠ 0 := two_ne_zero
          calc
            2 * ej c ((j : ℕ) + 1)
                = 2 * (c / (2 ^ ((j : ℕ) + 1) : ℝ)) := by rfl
            _ = 2 * (c / ((2 ^ (j : ℕ) : ℝ) * 2)) := by
                  simp [pow_succ]
            _ = (2 * c) / ((2 ^ (j : ℕ) : ℝ) * 2) := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using
                    (mul_div_assoc (2 : ℝ) c ((2 ^ (j : ℕ) : ℝ) * 2)).symm
            _ = (c * 2) / ((2 ^ (j : ℕ) : ℝ) * 2) := by
                  simp [mul_comm]
            _ = c / (2 ^ (j : ℕ) : ℝ) := mul_div_mul_right c (2 ^ j) two_ne_zero'
            _ = ej c (j : ℕ) := by
                  simp [ej]
        calc
          _ = 6 * ej c ((j : ℕ) + 1) - 6 * ej c ((j : ℕ) + 2) := by
            simp [mul_sub]
        _ = 6 * ej c ((j : ℕ) + 1) - 3 * ej c ((j : ℕ) + 1) := by
          have ht : 6 * ej c ((j : ℕ) + 2) = 3 * ej c ((j : ℕ) + 1) := by
            have h := t ((j : ℕ) + 1)
            have h' : 2 * ej c ((j : ℕ) + 2) = ej c ((j : ℕ) + 1) := by
              simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using h
            have h'' := congrArg (fun x : ℝ => (3 : ℝ) * x) h'
            calc
              6 * ej c ((j : ℕ) + 2) = 3 * (2 * ej c ((j : ℕ) + 2)) := by ring
              _ = 3 * ej c ((j : ℕ) + 1) := by
                simpa using h''
          simp [ht]
        -- Equivalent dyadic-expression rewrite used in the integral comparison step.
        _ = 3 * ej c ((j : ℕ) + 1) := by
          linarith
        _ = ej c ((j : ℕ) + 1) + 2 * ej c ((j : ℕ) + 1) := by
          linarith
        _ = _ := by
          refine add_left_cancel_iff.mpr ?_
          rw [t]
      have r0 : √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m ≤ ej c (j + 1) / Real.sqrt m := by
        suffices √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2 / ↑m) ≤ ej c (j + 1) from by
          rw [<- Finset.sum_div] at this
          simp at this
          have u :
              √(∑ i, (hk.1 - F x) (S i) ^ 2) / ↑m =
                (√(∑ i, (hk.1 - F x) (S i) ^ 2) / √↑m) / √↑m := by
            field_simp
            congr
            apply Real.sq_sqrt
            exact Nat.cast_nonneg m
          rw [u]
          apply div_le_div_of_nonneg_right this
          simp
        have gh : hk.1 = chainApprox c_pos h' x ((j : ℕ) + 1) := by rw [<- fhx]
        rw [gh]
        have :
            √(∑ i, (chainApprox c_pos h' x ((j : ℕ) + 1) - F x) (S i) ^ 2 /
              ↑m) =
              empiricalDist S (F x) (chainApprox c_pos h' x ((j : ℕ) + 1)) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ
                (fun i ↦ (chainApprox c_pos h' x (↑j + 1) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact empiricalDist_to_chainApprox_le_ej c_pos h' x ((j : ℕ) + 1) cs
      have r1 : √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m ≤ ej c j / Real.sqrt m := by
        suffices √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2 / ↑m) ≤ ej c j from by
          rw [<- Finset.sum_div] at this
          simp at this
          have u :
              √(∑ i, (hk.2 - F x) (S i) ^ 2) / ↑m =
                (√(∑ i, (hk.2 - F x) (S i) ^ 2) / √↑m) / √↑m := by
            field_simp
            congr
            apply Real.sq_sqrt
            exact Nat.cast_nonneg m
          rw [u]
          apply div_le_div_of_nonneg_right this
          simp
        have gh : hk.2 = chainApprox c_pos h' x j := by rw [<- fhx]
        rw [gh]
        have :
            √(∑ i, (chainApprox c_pos h' x j - F x) (S i) ^ 2 / ↑m) =
              empiricalDist S (F x) (chainApprox c_pos h' x j) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ
                (fun i ↦ (chainApprox c_pos h' x (↑j) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact empiricalDist_to_chainApprox_le_ej c_pos h' x j cs
      rw [rp]
      apply add_le_add r0 r1
    · exact
      Real.sqrt_nonneg
        (2 * Real.log
          (↑(coveringNumber' h' (ej c ((j : ℕ) + 1))) *
            ↑(coveringNumber' h' (ej c (j : ℕ)))))
  _ = ∑ j : Fin n,
      ((6 * (ej c (j + 1) - ej c (j + 2))) *
        (√(2 * Real.log ((coveringNumber' h' (ej c (j + 1))) *
          (coveringNumber' h' (ej c j))))) / (Real.sqrt m)) := by
    apply congrArg
    ext j
    field_simp
  _ ≤ ∑ j : Fin n,
      ((6 * (ej c (j + 1) - ej c (j + 2))) *
        (√(2 * Real.log ((coveringNumber' h' (ej c (j + 1))) *
          (coveringNumber' h' (ej c (j + 1)))))) / (Real.sqrt m)) := by
    refine Finset.sum_le_sum ?_
    intro s si
    refine div_le_div_of_nonneg_right ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · have NonemptyFS : Nonempty (EmpiricalFunctionSpace F S) := by
          rename_i h
          obtain ⟨i⟩ := h
          use i
        apply Real.sqrt_le_sqrt
        refine (mul_le_mul_iff_of_pos_left (by simp)).mpr ?_
        apply Real.log_le_log
        refine Left.mul_pos ?_ ?_
        repeat (norm_cast; apply coveringNumber'_nonzero; simp; apply ej_pos c_pos)
        refine (mul_le_mul_iff_of_pos_left (by
          norm_cast
          apply coveringNumber'_nonzero
          simp
          apply ej_pos c_pos)).mpr ?_
        · norm_cast
          apply coveringNumber'_antitone
          repeat (apply ej_pos c_pos)
          dsimp [ej]
          refine (div_le_div_iff_of_pos_left c_pos ?_ ?_).mpr ?_
          repeat simp
          refine (pow_le_pow_iff_right₀ ?_).mpr ?_
          repeat simp
      · refine Left.mul_nonneg (by simp) ?_
        simp
        dsimp [ej]
        refine (div_le_div_iff_of_pos_left c_pos ?_ ?_).mpr ?_
        repeat simp
        refine (pow_le_pow_iff_right₀ ?_).mpr ?_
        repeat simp
    simp
  _ = ∑ j : Fin n,
      6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) *
        (√(4 * Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))) /
          (Real.sqrt m)) := by
    repeat apply congrArg
    ext j
    -- Factor out the covering number calculation
    have covering_calc :
        √(Real.log ((coveringNumber' h' (ej c ((j : ℕ) + 1))) *
          (coveringNumber' h' (ej c ((j : ℕ) + 1))))) =
        √(2 * Real.log (coveringNumber' h' (ej c ((j : ℕ) + 1)))) := by
      calc
      _ = √(Real.log ((coveringNumber' h' (ej c ((j : ℕ) + 1))) ^ 2)) := by
        repeat apply congrArg
        symm
        norm_cast
        exact pow_two ↑(coveringNumber' h' (ej c (j + 1)))
      _ = √(2 * Real.log (coveringNumber' h' (ej c ((j : ℕ) + 1)))) := by
        rw [Real.log_pow]
        norm_cast
      _ = _ := by simp
    have : √(4 * Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))) = √2 * √(2 * Real.log ↑(coveringNumber' h' (ej c ((j : ℕ) + 1)))) := by
      simp
      rw [<- mul_assoc]
      simp
      left
      rw [← (by norm_num : (2 : ℝ) ^ 2 = 4), Real.sqrt_sq]
      simp
    rw [this, <- covering_calc]
    rw [mul_div_assoc]
    apply congrArg
    have : √(2 * Real.log (↑(coveringNumber' h' (ej c ((j : ℕ) + 1))) * ↑(coveringNumber' h' (ej c ((j : ℕ) + 1))))) =
      √2 * √(Real.log (↑(coveringNumber' h' (ej c ((j : ℕ) + 1))) * ↑(coveringNumber' h' (ej c ((j : ℕ) + 1))))) := by
      simp
    rw [this]
  -- Convert the Part A/Part B bound into the final finite-sum expression.

end Empirical
end Causalean.Stat.Concentration
