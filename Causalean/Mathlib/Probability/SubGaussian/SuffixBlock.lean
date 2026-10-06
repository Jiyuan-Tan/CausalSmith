module
public import Causalean.Mathlib.Probability.SubGaussian.Prefix

/-!
# One block of an ordered Gaussian suffix

This module bounds the integrated Gaussian tails from the indices in one
interval `[L, 2 L)`.  It is the local estimate used to sum the full suffix
over dyadic blocks.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory

/-- For [a decay exponent](hyp:α) satisfying [strict positivity](hyp:hα), [there
is a positive constant](goal) that bounds every integrable Gaussian tail block
with a positive scale by its local scale and square-root logarithmic factor.

Proof strategy: there are at most `L` indices in the block.  For each of them,
`(m/(k+1))^α ≤ (m/L)^α`, so the sum is pointwise bounded by
`2 L exp (-t²/(2 σ² (m/L)^α))`.  Apply `clipped_gaussian_integral` at scale
`σ (m/L)^(α/2)`.  Prove integrability of the original clipped sum by the
integrability of its finitely many Gaussian terms. -/
theorem gaussian_suffix_block_integral (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m L : ℕ) (σ : ℝ), 1 ≤ m → m ≤ L → 0 < σ →
        let g : ℝ → ℝ := fun t =>
          min 1 (∑ k : Fin N,
            if L ≤ k.val + 1 ∧ k.val + 1 < 2 * L then
              2 * Real.exp (-(t ^ 2) /
                (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))
            else 0)
        IntegrableOn g (Set.Ioi (0 : ℝ)) volume ∧
          ∫ t in Set.Ioi (0 : ℝ), g t ≤
            C * σ * ((m : ℝ) / (L : ℝ)) ^ (α / 2) *
              Real.sqrt (1 + Real.log (L : ℝ)) := by
  obtain ⟨C, hC, hclip⟩ := clipped_gaussian_integral
  refine ⟨C, hC, ?_⟩
  intro N m L σ hm hmL hσ
  dsimp
  let S : Finset (Fin N) := Finset.univ.filter
    (fun k => L ≤ k.val + 1 ∧ k.val + 1 < 2 * L)
  let a : ℝ := σ * ((m : ℝ) / (L : ℝ)) ^ (α / 2)
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have ha : 0 < a := by dsimp [a]; positivity
  have hcard : S.card ≤ L := by
    have hle : S.card ≤ (Finset.Ico L (2 * L)).card := by
      apply Finset.card_le_card_of_injOn (fun k : Fin N => k.val + 1)
      · intro k hk
        simpa [S, Finset.mem_Ico] using (Finset.mem_filter.mp hk).2
      · intro k hk j hj heq
        apply Fin.ext
        exact Nat.add_right_cancel heq
    rw [Nat.card_Ico] at hle
    omega
  have hS (t : ℝ) :
      (∑ k : Fin N,
        if L ≤ k.val + 1 ∧ k.val + 1 < 2 * L then
          2 * Real.exp (-(t ^ 2) /
            (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) else 0) =
      ∑ k ∈ S, 2 * Real.exp (-(t ^ 2) /
        (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) := by
    simp [S, Finset.sum_filter]
  have hterm (k : Fin N) : Integrable
      (fun t : ℝ => 2 * Real.exp (-(t ^ 2) /
        (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))) volume := by
    have hb : 0 < (1 / (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α) : ℝ) := by
      positivity
    have hi := (integrable_exp_neg_mul_sq hb).const_mul (2 : ℝ)
    convert hi using 1
    ext t
    congr 1
    ring
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ k ∈ S, 2 * Real.exp (-(t ^ 2) /
        (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)))
      (Set.Ioi (0 : ℝ)) volume := by
    exact (integrable_finsetSum S (fun k _ => hterm k)).integrableOn
  have hgi : IntegrableOn (fun t : ℝ =>
      min 1 (∑ k : Fin N,
        if L ≤ k.val + 1 ∧ k.val + 1 < 2 * L then
          2 * Real.exp (-(t ^ 2) /
            (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) else 0))
      (Set.Ioi (0 : ℝ)) volume := by
    simp_rw [hS]
    apply hsum.mono'
    · fun_prop
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact min_le_right _ _
  have ha2 : a ^ 2 = σ ^ 2 * ((m : ℝ) / (L : ℝ)) ^ α := by
    dsimp [a]
    rw [mul_pow, ← Real.rpow_mul_natCast (le_of_lt (div_pos hmreal hLreal))]
    congr 1
    ring
  have hpoint (t : ℝ) :
      min 1 (∑ k : Fin N,
        if L ≤ k.val + 1 ∧ k.val + 1 < 2 * L then
          2 * Real.exp (-(t ^ 2) /
            (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) else 0) ≤
      min 1 (2 * (L : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2))) := by
    rw [hS]
    have hbound (k : Fin N) (hk : k ∈ S) :
        2 * Real.exp (-(t ^ 2) /
          (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) ≤
        2 * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
      have hkL : L ≤ k.val + 1 := (Finset.mem_filter.mp hk).2.1
      have hkreal : (0 : ℝ) < (k.val + 1 : ℝ) := by positivity
      have hfrac : (m : ℝ) / (k.val + 1 : ℝ) ≤ (m : ℝ) / (L : ℝ) := by
        apply (div_le_div_iff₀ hkreal hLreal).2
        have hcast : (L : ℝ) ≤ (k.val + 1 : ℝ) := by exact_mod_cast hkL
        nlinarith
      have hq := Real.rpow_le_rpow (by positivity : 0 ≤ (m : ℝ) / (k.val + 1 : ℝ))
        hfrac hα.le
      have hd1 : 0 < 2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α := by
        positivity
      have hd2 : 0 < 2 * a ^ 2 := by positivity
      have hden : 2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α ≤
          2 * a ^ 2 := by rw [ha2]; nlinarith [sq_nonneg σ]
      have hexp : -(t ^ 2) /
          (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α) ≤
          -(t ^ 2) / (2 * a ^ 2) := by
        apply (div_le_div_iff₀ hd1 hd2).2
        nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hden)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    have hsumBound :
        (∑ k ∈ S, 2 * Real.exp (-(t ^ 2) /
          (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α))) ≤
        2 * (L : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
      calc
        _ ≤ ∑ _k ∈ S, 2 * Real.exp (-(t ^ 2) / (2 * a ^ 2)) :=
          Finset.sum_le_sum (fun k hk => hbound k hk)
        _ = (S.card : ℝ) * (2 * Real.exp (-(t ^ 2) / (2 * a ^ 2))) := by simp
        _ ≤ 2 * (L : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
          have hc : (S.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcard
          nlinarith [Real.exp_pos (-(t ^ 2) / (2 * a ^ 2))]
    exact min_le_min_left _ hsumBound
  obtain ⟨hclipi, hclipbound⟩ := hclip L a (lt_of_lt_of_le Nat.zero_lt_one hL) ha
  refine ⟨hgi, ?_⟩
  calc
    (∫ t in Set.Ioi (0 : ℝ),
      min 1 (∑ k : Fin N,
        if L ≤ k.val + 1 ∧ k.val + 1 < 2 * L then
          2 * Real.exp (-(t ^ 2) /
            (2 * σ ^ 2 * ((m : ℝ) / (k.val + 1 : ℝ)) ^ α)) else 0)) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          min 1 (2 * (L : ℝ) * Real.exp (-(t ^ 2) / (2 * a ^ 2))) :=
      setIntegral_mono_ae hgi hclipi (Filter.Eventually.of_forall hpoint)
    _ ≤ C * a * Real.sqrt (1 + Real.log (L : ℝ)) := hclipbound
    _ = C * σ * ((m : ℝ) / (L : ℝ)) ^ (α / 2) *
        Real.sqrt (1 + Real.log (L : ℝ)) := by dsimp [a]; ring

end Causalean.Mathlib.Probability.SubGaussian
