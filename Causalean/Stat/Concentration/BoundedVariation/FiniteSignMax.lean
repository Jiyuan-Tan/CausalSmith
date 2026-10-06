module
public import Causalean.Stat.Concentration.BoundedVariation.SignTail
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Maximum of finitely many signed sums

A logarithmic finite-class bound follows from the sign exponential moment.
This is an intermediate estimate for dyadic chaining, where class size grows
geometrically and increment variance decays geometrically.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation

open MeasureTheory

/-- Let c be [positive](hyp:hc) and B [nonnegative](hyp:_hB), and let a
[nonnegative](hyp:hY) function Y on a finite set satisfy [for every positive
t, the number of points where Y is at least t is at most B·exp(−c t)](hyp:htail).
Then [the sum of Y over the set is at most B/c](goal).
-/
private theorem finite_tail_integral {Ω : Type} [Fintype Ω]
    (Y : Ω → ℝ) (c B : ℝ) (hc : 0 < c) (_hB : 0 ≤ B)
    (hY : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t, 0 < t →
      (∑ ω, if t ≤ Y ω then (1 : ℝ) else 0) ≤ B * Real.exp (-c * t)) :
    (∑ ω, Y ω) ≤ B / c := by
  classical
  letI : MeasurableSpace Ω := ⊤
  let f : ℝ → ℝ := fun t => (Measure.count : Measure Ω).real {ω | t ≤ Y ω}
  have hf_count (t : ℝ) : f t = ∑ ω, if t ≤ Y ω then (1 : ℝ) else 0 := by
    dsimp [f, Measure.real]
    rw [Measure.count_apply_finite _ (Set.toFinite _)]
    simp
  have hf_meas : Measurable f := by
    apply Antitone.measurable
    intro x y hxy
    dsimp [f]
    exact ENNReal.toReal_mono (by simp) (measure_mono (fun ω hw => le_trans hxy hw))
  have hf_nn (t : ℝ) : 0 ≤ f t := by
    rw [hf_count]
    positivity
  have hf_bdd (t : ℝ) (ht : 0 < t) : f t ≤ B * Real.exp (-c * t) := by
    rw [hf_count]
    exact htail t ht
  have h_exp_int : IntegrableOn (fun t : ℝ => B * Real.exp (-c * t)) (Set.Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show -c < 0 by linarith) 0).const_mul B
  have hf_int : IntegrableOn f (Set.Ioi 0) := by
    apply integrable_of_le_of_le (g₁ := fun _ => (0 : ℝ))
      (g₂ := fun t => B * Real.exp (-c * t))
    · exact hf_meas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => hf_nn t)
    · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hf_bdd t ht)
    · exact integrable_zero _ _ _
    · exact h_exp_int
  calc
    (∑ ω, Y ω) = ∫ ω, Y ω ∂(Measure.count : Measure Ω) := (integral_count Y).symm
    _ = ∫ t in Set.Ioi 0, f t := by
      exact (Integrable.of_finite.integral_eq_integral_meas_le
        (Filter.Eventually.of_forall hY))
    _ ≤ ∫ t in Set.Ioi 0, B * Real.exp (-c * t) :=
      setIntegral_mono_on hf_int h_exp_int measurableSet_Ioi
        (fun t ht => hf_bdd t ht)
    _ = B / c := by
      rw [integral_const_mul, integral_exp_mul_Ioi (show -c < 0 by linarith)]
      simp [div_eq_mul_inv]


/-- Let V be [positive](hyp:_hV) and [equal to the largest squared
Euclidean norm among m + 1 coefficient vectors](hyp:hVdef), and let u be
[a positive threshold](hyp:hu). Then [the number of sign patterns whose
largest squared signed sum is at least u is at most 2^n times
2(m + 1)·exp(−u/(2V))](goal), by a union bound over the individual tails.
-/
private theorem maxSqTail_le {m n : ℕ} (a : Fin (m + 1) → Fin n → ℝ)
    (V : ℝ) (_hV : 0 < V)
    (hVdef : V = Finset.univ.sup' Finset.univ_nonempty
       (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2))
    (u : ℝ) (hu : 0 < u) :
    (∑ σ : Fin n → Bool,
      if u ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) =>
          (∑ j, (if σ j then (1 : ℝ) else -1) * a k j) ^ 2)
      then (1 : ℝ) else 0) ≤
    (2 ^ n : ℝ) * (2 * (m + 1 : ℝ) * Real.exp (-(u / (2 * V)))) := by
  classical
  let X : Fin (m + 1) → (Fin n → Bool) → ℝ :=
    fun k σ => ∑ j, (if σ j then (1 : ℝ) else -1) * a k j
  have htail_k (k : Fin (m + 1)) :
      (∑ σ : Fin n → Bool, if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0) ≤
      (2 ^ n : ℝ) * (2 * Real.exp (-(u / (2 * V)))) := by
    let Vk : ℝ := ∑ j, (a k j) ^ 2
    have hVk_nonneg : 0 ≤ Vk := by
      dsimp [Vk]
      positivity
    have hVk_le : Vk ≤ V := by
      rw [hVdef]
      exact Finset.le_sup' (fun i : Fin (m + 1) => ∑ j, (a i j) ^ 2)
        (by simp : k ∈ Finset.univ)
    by_cases hVk0 : Vk = 0
    · have ha0 (j : Fin n) : a k j = 0 := by
        have hsq : (a k j) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => sq_nonneg (a k j))).mp hVk0 j (by simp)
        nlinarith
      have hX0 (σ : Fin n → Bool) : X k σ = 0 := by
        simp [X, ha0]
      have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
      simp [hX0, not_le.mpr hsqrt]
      positivity
    · have hVkpos : 0 < Vk := lt_of_le_of_ne hVk_nonneg (Ne.symm hVk0)
      have htail := signTailMass_le (a k) (Real.sqrt u)
        (Real.sqrt_nonneg _) hVkpos
      have hfrac : -(u / (2 * Vk)) ≤ -(u / (2 * V)) := by
        apply neg_le_neg
        gcongr
      have h_exp : Real.exp (-(u / (2 * Vk))) ≤
          Real.exp (-(u / (2 * V))) := Real.exp_le_exp.mpr hfrac
      have htail' : signTailMass (a k) (Real.sqrt u) ≤
          2 * Real.exp (-(u / (2 * V))) := by
        calc
          signTailMass (a k) (Real.sqrt u) ≤
              2 * Real.exp (-(u / (2 * Vk))) := by
                simpa [Vk, Real.sq_sqrt hu.le] using htail
          _ ≤ 2 * Real.exp (-(u / (2 * V))) := by gcongr
      have hden : 0 < (2 ^ n : ℝ) := by positivity
      have heq : signTailMass (a k) (Real.sqrt u) =
        (∑ σ : Fin n → Bool, if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0) /
          (2 ^ n : ℝ) := rfl
      rw [heq] at htail'
      simpa only [mul_comm] using (div_le_iff₀ hden).mp htail'
  have hper (σ : Fin n → Bool) :
      (if u ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) => (X k σ) ^ 2) then (1 : ℝ) else 0) ≤
      ∑ k : Fin (m + 1), if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0 := by
    by_cases h : u ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) => (X k σ) ^ 2)
    · obtain ⟨k, hk, hku⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp h
      have hsqrt : Real.sqrt u ≤ |X k σ| := by
        nlinarith [Real.sq_sqrt hu.le, sq_abs (X k σ), Real.sqrt_nonneg u, abs_nonneg (X k σ)]
      simpa [h, hsqrt] using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun k : Fin (m + 1) =>
            if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0)
          (fun k hk => by positivity) (by simp : k ∈ Finset.univ))
    · simp only [if_neg h]
      positivity
  calc
    (∑ σ : Fin n → Bool,
      if u ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) => (X k σ) ^ 2)
      then (1 : ℝ) else 0)
      ≤ ∑ σ : Fin n → Bool,
        ∑ k : Fin (m + 1),
          if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun σ _ => hper σ)
    _ = ∑ k : Fin (m + 1),
        ∑ σ : Fin n → Bool,
          if Real.sqrt u ≤ |X k σ| then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ _k : Fin (m + 1),
        (2 ^ n : ℝ) * (2 * Real.exp (-(u / (2 * V)))) :=
        Finset.sum_le_sum (fun k _ => htail_k k)
    _ = (2 ^ n : ℝ) * (2 * (m + 1 : ℝ) * Real.exp (-(u / (2 * V)))) := by
      simp [Finset.sum_const]
      ring


/-- [The sign-maximum energy](goal) of [a nonempty finite collection of
coefficient vectors in ℝ^n](hyp:a) is [the uniform average, over all 2^n
sign patterns, of the largest squared signed sum among the
vectors](step:1).
-/
noncomputable def signMaxEnergy {m n : ℕ} (a : Fin (m + 1) → Fin n → ℝ) : ℝ :=
  (∑ σ : Fin n → Bool,
    Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin (m + 1) =>
        (∑ j, (if σ j then (1 : ℝ) else -1) * a k j) ^ 2)) /
    (2 ^ n : ℝ)

/-- For m + 1 coefficient vectors in ℝ^n, [the sign-average of the largest
squared Rademacher sum is at most 32 (1 + log(m + 1)) times the largest
squared Euclidean norm of the vectors](goal).

The numerical constant is uniform in both finite sizes.
-/
theorem signMaxEnergy_le {m n : ℕ} (a : Fin (m + 1) → Fin n → ℝ) :
    signMaxEnergy a ≤
      32 * (1 + Real.log (m + 1)) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2) := by
  change (∑ σ : Fin n → Bool,
      Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin (m + 1) =>
          (∑ j, (if σ j then (1 : ℝ) else -1) * a k j) ^ 2)) /
      (2 ^ n : ℝ) ≤
      32 * (1 + Real.log (m + 1)) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2)
  classical
  let V : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2)
  let D : ℝ := (2 ^ n : ℝ)
  let M : ℝ := (m + 1 : ℝ)
  let Y : (Fin n → Bool) → ℝ := fun σ =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin (m + 1) =>
        (∑ j, (if σ j then (1 : ℝ) else -1) * a k j) ^ 2)
  have hV_nonneg : 0 ≤ V := by
    have h := Finset.le_sup'
      (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2)
      (by simp : (0 : Fin (m + 1)) ∈ Finset.univ)
    dsimp [V]
    exact le_trans (by positivity) h
  have hY_nonneg (σ : Fin n → Bool) : 0 ≤ Y σ := by
    have h := Finset.le_sup'
      (fun k : Fin (m + 1) =>
        (∑ j, (if σ j then (1 : ℝ) else -1) * a k j) ^ 2)
      (by simp : (0 : Fin (m + 1)) ∈ Finset.univ)
    exact le_trans (sq_nonneg _) h
  have hD : 0 < D := by dsimp [D]; positivity
  have hM : 1 ≤ M := by dsimp [M]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  by_cases hV0 : V = 0
  · have ha0 (k : Fin (m + 1)) (j : Fin n) : a k j = 0 := by
      have hVk_le : (∑ j, (a k j) ^ 2) ≤ V := by
        dsimp [V]
        exact Finset.le_sup' (fun k : Fin (m + 1) => ∑ j, (a k j) ^ 2)
          (by simp : k ∈ Finset.univ)
      have hVk0 : (∑ j, (a k j) ^ 2) = 0 := by
        have hnonneg : 0 ≤ (∑ j, (a k j) ^ 2) := by positivity
        linarith
      have hsq : (a k j) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (a k j))).mp hVk0 j (by simp)
      nlinarith
    simp [ha0]
  · have hV : 0 < V := lt_of_le_of_ne hV_nonneg (Ne.symm hV0)
    let T : ℝ := 2 * V * Real.log (2 * M)
    let E : (Fin n → Bool) → ℝ := fun σ => max (Y σ - T) 0
    have h2M : 0 < 2 * M := by positivity
    have hlog2M : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by nlinarith)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hE_nonneg (σ : Fin n → Bool) : 0 ≤ E σ := le_max_right _ _
    have hE_tail (t : ℝ) (ht : 0 < t) :
        (∑ σ : Fin n → Bool, if t ≤ E σ then (1 : ℝ) else 0) ≤
          D * Real.exp (-(1 / (2 * V)) * t) := by
      have hiff (σ : Fin n → Bool) : (t ≤ E σ) ↔ (T + t ≤ Y σ) := by
        dsimp [E]
        constructor
        · intro h
          rcases le_max_iff.mp h with h | h
          · linarith
          · linarith
        · intro h
          exact le_trans (by linarith : t ≤ Y σ - T) (le_max_left _ _)
      have hsumEq :
          (∑ σ : Fin n → Bool, if t ≤ E σ then (1 : ℝ) else 0) =
          ∑ σ : Fin n → Bool, if T + t ≤ Y σ then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [hiff]
      have hraw := maxSqTail_le a V hV rfl (T + t) (by linarith)
      change (∑ σ : Fin n → Bool, if T + t ≤ Y σ then (1 : ℝ) else 0) ≤
        D * (2 * M * Real.exp (-((T + t) / (2 * V)))) at hraw
      have harg : -((T + t) / (2 * V)) =
          -Real.log (2 * M) + (-(1 / (2 * V)) * t) := by
        dsimp [T]
        field_simp
        ring
      have hexp : 2 * M * Real.exp (-((T + t) / (2 * V))) =
          Real.exp (-(1 / (2 * V)) * t) := by
        rw [harg, Real.exp_add, Real.exp_neg, Real.exp_log h2M]
        field_simp
      rw [hexp] at hraw
      rw [hsumEq]
      exact hraw
    have hE_sum : (∑ σ : Fin n → Bool, E σ) ≤ D * (2 * V) := by
      have h := finite_tail_integral E (1 / (2 * V)) D
        (by positivity) hD.le hE_nonneg hE_tail
      convert h using 1
      field_simp
    have hYsum : (∑ σ : Fin n → Bool, Y σ) ≤ D * T + ∑ σ, E σ := by
      calc
        (∑ σ : Fin n → Bool, Y σ) ≤
            ∑ σ : Fin n → Bool, (T + E σ) := by
          apply Finset.sum_le_sum
          intro σ _
          have h := le_max_left (Y σ - T) (0 : ℝ)
          dsimp [E]
          linarith
        _ = D * T + ∑ σ, E σ := by
          simp [Finset.sum_add_distrib, D]
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hlog : Real.log (2 * M) = Real.log 2 + Real.log M :=
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM))
    change (∑ σ : Fin n → Bool, Y σ) / D ≤
      32 * (1 + Real.log M) * V
    calc
      (∑ σ, Y σ) / D ≤ (D * T + ∑ σ, E σ) / D :=
        div_le_div_of_nonneg_right hYsum hD.le
      _ ≤ (D * T + D * (2 * V)) / D := by
        apply div_le_div_of_nonneg_right _ hD.le
        linarith
      _ = T + 2 * V := by field_simp
      _ ≤ 32 * (1 + Real.log M) * V := by
        dsimp [T]
        rw [hlog]
        nlinarith [mul_nonneg hV.le hlogM]

end Causalean.Stat.Concentration.BoundedVariation
