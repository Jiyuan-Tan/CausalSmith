module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.Parameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Alternating zeros of reciprocal residual square factors

For each geometric parameter `0 < ρ < 1`, the sine and cosine factors in
the reciprocal residual square identities have interlacing zeros from zero
to pi. This statement isolates the analytic node construction from the
polynomial identities and interval change of variables.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

private noncomputable def angleGrid (m j : ℕ) : ℝ :=
  (j : ℝ) * Real.pi / ((m : ℝ) + 1)

private theorem angleGrid_phase (m j : ℕ) :
    ((m : ℝ) + 1) * angleGrid m j / 2 = (j : ℝ) * Real.pi / 2 := by
  unfold angleGrid
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem angleGrid_phase_sub (m j : ℕ) :
    ((m : ℝ) - 1) * angleGrid m j / 2 =
      (j : ℝ) * Real.pi / 2 - angleGrid m j := by
  unfold angleGrid
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem angleGrid_strictMono (m : ℕ) : StrictMono (angleGrid m) := by
  intro i j hij
  unfold angleGrid
  have hp : 0 < Real.pi := Real.pi_pos
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hic : (i : ℝ) < j := by exact_mod_cast hij
  apply div_lt_div_of_pos_right ?_ hm
  exact mul_lt_mul_of_pos_right hic hp

private theorem angleGrid_mem (m j : ℕ) (hj : j ≤ m + 1) :
    angleGrid m j ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · unfold angleGrid
    positivity
  · unfold angleGrid
    have hm : 0 < (m : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hm).2
    have hcast : (j : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hj
    nlinarith [mul_le_mul_of_nonneg_right hcast Real.pi_pos.le]

private theorem angleGrid_cos_even (m k : ℕ) (ρ : ℝ) :
    Real.cos (((m : ℝ) + 1) * angleGrid m (2 * k) / 2) -
      ρ * Real.cos (((m : ℝ) - 1) * angleGrid m (2 * k) / 2) =
      (-1 : ℝ) ^ k * (1 - ρ * Real.cos (angleGrid m (2 * k))) := by
  rw [angleGrid_phase, angleGrid_phase_sub]
  have h : (((2 * k : ℕ) : ℝ) * Real.pi / 2) = (k : ℝ) * Real.pi := by
    push_cast
    ring
  rw [h, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  ring

private theorem angleGrid_sin_even (m k : ℕ) (ρ : ℝ) :
    Real.sin (((m : ℝ) + 1) * angleGrid m (2 * k) / 2) -
      ρ * Real.sin (((m : ℝ) - 1) * angleGrid m (2 * k) / 2) =
      ρ * (-1 : ℝ) ^ k * Real.sin (angleGrid m (2 * k)) := by
  rw [angleGrid_phase, angleGrid_phase_sub]
  have h : (((2 * k : ℕ) : ℝ) * Real.pi / 2) = (k : ℝ) * Real.pi := by
    push_cast
    ring
  rw [h, Real.sin_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  ring

private theorem angleGrid_cos_odd (m k : ℕ) (ρ : ℝ) :
    Real.cos (((m : ℝ) + 1) * angleGrid m (2 * k + 1) / 2) -
      ρ * Real.cos (((m : ℝ) - 1) * angleGrid m (2 * k + 1) / 2) =
      -(ρ * (-1 : ℝ) ^ k * Real.sin (angleGrid m (2 * k + 1))) := by
  rw [angleGrid_phase, angleGrid_phase_sub]
  have h : (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast
    ring
  rw [h, Real.cos_sub, Real.cos_add, Real.sin_add]
  simp [Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  ring

private theorem angleGrid_sin_odd (m k : ℕ) (ρ : ℝ) :
    Real.sin (((m : ℝ) + 1) * angleGrid m (2 * k + 1) / 2) -
      ρ * Real.sin (((m : ℝ) - 1) * angleGrid m (2 * k + 1) / 2) =
      (-1 : ℝ) ^ k * (1 - ρ * Real.cos (angleGrid m (2 * k + 1))) := by
  rw [angleGrid_phase, angleGrid_phase_sub]
  have h : (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (k : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast
    ring
  rw [h, Real.sin_sub, Real.cos_add, Real.sin_add]
  simp [Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  ring

private theorem exists_zero_in_angleCell {f : ℝ → ℝ} {a b A B s : ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hA : 0 < A) (hB : 0 ≤ B)
    (ha : f a = s * A) (hb : f b = -(s * B))
    (hs : s = 1 ∨ s = -1) :
    ∃ x, a < x ∧ x ≤ b ∧ f x = 0 := by
  rcases hs with hs | hs
  · have hfa : 0 < f a := by rw [ha, hs]; nlinarith
    have hfb : f b ≤ 0 := by rw [hb, hs]; nlinarith
    obtain ⟨x, hx, hfx⟩ :=
      (intermediate_value_Icc' hab hf.continuousOn) ⟨hfb, hfa.le⟩
    refine ⟨x, ?_, hx.2, hfx⟩
    exact lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
  · have hfa : f a < 0 := by rw [ha, hs]; nlinarith
    have hfb : 0 ≤ f b := by rw [hb, hs]; nlinarith
    obtain ⟨x, hx, hfx⟩ :=
      (intermediate_value_Icc hab hf.continuousOn) ⟨hfa.le, hfb⟩
    refine ⟨x, ?_, hx.2, hfx⟩
    exact lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)

private noncomputable def reciprocalSinFactor (m : ℕ) (ρ θ : ℝ) : ℝ :=
  Real.sin (((m : ℝ) + 1) * θ / 2) -
    ρ * Real.sin (((m : ℝ) - 1) * θ / 2)

private noncomputable def reciprocalCosFactor (m : ℕ) (ρ θ : ℝ) : ℝ :=
  Real.cos (((m : ℝ) + 1) * θ / 2) -
    ρ * Real.cos (((m : ℝ) - 1) * θ / 2)

private theorem reciprocalFactor_left_pos {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (θ : ℝ) : 0 < 1 - ρ * Real.cos θ := by
  have hc := Real.cos_le_one θ
  have hm := mul_le_mul_of_nonneg_left hc hρ.1.le
  nlinarith only [hm, hρ.2]

private theorem exists_reciprocalCos_zero_in_cell {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (m k : ℕ)
    (hk : 2 * k + 1 ≤ m + 1) :
    ∃ θ, angleGrid m (2 * k) < θ ∧
      θ ≤ angleGrid m (2 * k + 1) ∧
      reciprocalCosFactor m ρ θ = 0 := by
  have hab : angleGrid m (2 * k) ≤ angleGrid m (2 * k + 1) :=
    (angleGrid_strictMono m (by omega : 2 * k < 2 * k + 1)).le
  have hA : 0 < 1 - ρ * Real.cos (angleGrid m (2 * k)) :=
    reciprocalFactor_left_pos hρ _
  have hB : 0 ≤ ρ * Real.sin (angleGrid m (2 * k + 1)) :=
    mul_nonneg hρ.1.le (Real.sin_nonneg_of_mem_Icc (angleGrid_mem m _ hk))
  have hf : Continuous (reciprocalCosFactor m ρ) := by
    unfold reciprocalCosFactor
    fun_prop
  exact exists_zero_in_angleCell hab hf hA hB
    (by exact angleGrid_cos_even m k ρ)
    (by
      change Real.cos (((m : ℝ) + 1) * angleGrid m (2 * k + 1) / 2) -
        ρ * Real.cos (((m : ℝ) - 1) * angleGrid m (2 * k + 1) / 2) =
          -((-1 : ℝ) ^ k * (ρ * Real.sin (angleGrid m (2 * k + 1))))
      rw [angleGrid_cos_odd]
      ring)
    (neg_one_pow_eq_or ℝ k)

private theorem exists_reciprocalSin_zero_in_cell {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (m k : ℕ)
    (hk : 2 * (k + 1) ≤ m + 1) :
    ∃ θ, angleGrid m (2 * k + 1) < θ ∧
      θ ≤ angleGrid m (2 * (k + 1)) ∧
      reciprocalSinFactor m ρ θ = 0 := by
  have hab : angleGrid m (2 * k + 1) ≤ angleGrid m (2 * (k + 1)) :=
    (angleGrid_strictMono m (by omega : 2 * k + 1 < 2 * (k + 1))).le
  have hA : 0 < 1 - ρ * Real.cos (angleGrid m (2 * k + 1)) :=
    reciprocalFactor_left_pos hρ _
  have hB : 0 ≤ ρ * Real.sin (angleGrid m (2 * (k + 1))) :=
    mul_nonneg hρ.1.le (Real.sin_nonneg_of_mem_Icc (angleGrid_mem m _ hk))
  have hf : Continuous (reciprocalSinFactor m ρ) := by
    unfold reciprocalSinFactor
    fun_prop
  exact exists_zero_in_angleCell hab hf hA hB
    (by exact angleGrid_sin_odd m k ρ)
    (by
      change Real.sin (((m : ℝ) + 1) * angleGrid m (2 * (k + 1)) / 2) -
        ρ * Real.sin (((m : ℝ) - 1) * angleGrid m (2 * (k + 1)) / 2) =
          -((-1 : ℝ) ^ k * (ρ * Real.sin (angleGrid m (2 * (k + 1)))))
      rw [angleGrid_sin_even, pow_succ]
      ring)
    (neg_one_pow_eq_or ℝ k)

private theorem exists_reciprocal_zero_in_cell {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (m i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ m + 1) :
    ∃ θ, angleGrid m (i - 1) < θ ∧ θ ≤ angleGrid m i ∧
      (if Even i then reciprocalSinFactor m ρ θ
       else reciprocalCosFactor m ρ θ) = 0 := by
  by_cases he : Even i
  · have he0 := he
    obtain ⟨k, hk⟩ := he
    have hk0 : 0 < k := by omega
    cases k with
    | zero => omega
    | succ k =>
      have hr : i = 2 * (k + 1) := by omega
      have hl : i - 1 = 2 * k + 1 := by omega
      obtain ⟨θ, hleft, hright, hz⟩ :=
        exists_reciprocalSin_zero_in_cell hρ m k (by omega)
      exact ⟨θ, by simpa [hl] using hleft,
        by simpa [hr] using hright, by simpa [he0] using hz⟩
  · have ho : Odd i := Nat.not_even_iff_odd.mp he
    obtain ⟨k, hk⟩ := ho
    have hr : i = 2 * k + 1 := by omega
    have hl : i - 1 = 2 * k := by omega
    obtain ⟨θ, hleft, hright, hz⟩ :=
      exists_reciprocalCos_zero_in_cell hρ m k (by omega)
    exact ⟨θ, by simpa [hl] using hleft,
      by simpa [hr] using hright, by simpa [he] using hz⟩

/-- A [decay parameter strictly between zero and one](hyp:ρ,hρ) and a
[degree bound](hyp:m) imply [the existence of ordered angles where the sine
and cosine factors vanish in alternating parity](goal). -/
theorem exists_reciprocalAlternatingAngles
    {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ angles : Fin (m + 2) → ℝ,
      StrictMono angles ∧
      (∀ i, angles i ∈ Set.Icc (0 : ℝ) Real.pi) ∧
      (∀ i : Fin (m + 2), if Even (i : ℕ) then
        Real.sin (((m : ℝ) + 1) * angles i / 2) -
          ρ * Real.sin (((m : ℝ) - 1) * angles i / 2) = 0
      else
        Real.cos (((m : ℝ) + 1) * angles i / 2) -
          ρ * Real.cos (((m : ℝ) - 1) * angles i / 2) = 0) := by
  classical
  have hchoice (i : Fin (m + 2)) :
      ∃ θ : ℝ,
        (if (i : ℕ) = 0 then θ = 0
         else angleGrid m ((i : ℕ) - 1) < θ ∧ θ ≤ angleGrid m i) ∧
        (if Even (i : ℕ) then reciprocalSinFactor m ρ θ
         else reciprocalCosFactor m ρ θ) = 0 := by
    by_cases hi : (i : ℕ) = 0
    · refine ⟨0, ?_, ?_⟩
      · simp [hi]
      · simp [hi, reciprocalSinFactor]
    · obtain ⟨θ, hl, hr, hz⟩ :=
        exists_reciprocal_zero_in_cell hρ m i (Nat.pos_of_ne_zero hi) (by
          have := i.isLt
          omega)
      exact ⟨θ, by simp [hi, hl, hr], hz⟩
  choose angles ha using hchoice
  refine ⟨angles, ?_, ?_, ?_⟩
  · intro i j hij
    have hijv : (i : ℕ) < (j : ℕ) := hij
    by_cases hi : (i : ℕ) = 0
    · have hj : (j : ℕ) ≠ 0 := by omega
      have hai : angles i = 0 := by simpa [hi] using (ha i).1
      have haj : angleGrid m ((j : ℕ) - 1) < angles j := by
        have h := (ha j).1
        simp only [if_neg hj] at h
        exact h.1
      have hg : 0 ≤ angleGrid m ((j : ℕ) - 1) :=
        (angleGrid_mem m _ (by have := j.isLt; omega)).1
      linarith
    · have hj : (j : ℕ) ≠ 0 := by omega
      have hai : angles i ≤ angleGrid m i := by
        have h := (ha i).1
        simp only [if_neg hi] at h
        exact h.2
      have haj : angleGrid m ((j : ℕ) - 1) < angles j := by
        have h := (ha j).1
        simp only [if_neg hj] at h
        exact h.1
      have hg : angleGrid m i ≤ angleGrid m ((j : ℕ) - 1) :=
        (angleGrid_strictMono m).monotone (by omega)
      linarith
  · intro i
    by_cases hi : (i : ℕ) = 0
    · have hai : angles i = 0 := by simpa [hi] using (ha i).1
      rw [hai]
      exact ⟨le_refl _, Real.pi_pos.le⟩
    · have hl : angleGrid m ((i : ℕ) - 1) < angles i := by
        have h := (ha i).1
        simp only [if_neg hi] at h
        exact h.1
      have hr : angles i ≤ angleGrid m i := by
        have h := (ha i).1
        simp only [if_neg hi] at h
        exact h.2
      have hgl : 0 ≤ angleGrid m ((i : ℕ) - 1) :=
        (angleGrid_mem m _ (by have := i.isLt; omega)).1
      have hgr : angleGrid m i ≤ Real.pi :=
        (angleGrid_mem m _ (by have := i.isLt; omega)).2
      exact ⟨by linarith, by linarith⟩
  · intro i
    by_cases he : Even (i : ℕ)
    · simpa [he, reciprocalSinFactor] using (ha i).2
    · simpa [he, reciprocalCosFactor] using (ha i).2

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
