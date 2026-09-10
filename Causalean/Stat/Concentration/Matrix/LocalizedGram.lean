/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.TailBounds.Bernstein
import Causalean.Stat.Concentration.Matrix.LocalizedGramBasic

/-!
# Bernstein coercivity for localized empirical Gram matrices

This module combines variance-sensitive coordinate concentration with the
deterministic entrywise perturbation argument.  The result applies to any
finite feature index type and any bounded measurable local weight, independently
of threshold, density, or local-polynomial constructions.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- For [a finite feature index set](hyp:κ), [a real coercivity level](hyp:lambda), and [a real envelope bound](hyp:B), the [localized Gram-matrix exponential rate](goal) is the smaller of $1/20$ and $\lambda^2/[16d(4dB^4+B^2\lambda)]$, where $d$ is the number of feature indices.

The explicit common exponential rate is the smaller of the local-count and Gram-entry Bernstein rates for a feature dimension, coercivity level, and envelope. -/
noncomputable def localizedGramRate (κ : Type*) [Fintype κ] (lambda B : ℝ) : ℝ :=
  min (1 / 20 : ℝ)
    (lambda ^ 2 /
      (16 * (Fintype.card κ : ℝ) *
        (4 * (Fintype.card κ : ℝ) * B ^ 4 + B ^ 2 * lambda)))

/-- Given [measurable local weights and features](hyp:hqmeas,hphimeas), [positive sample size, local mass, and population coercivity](hyp:hN,hp,hlambda), a [nonnegative feature envelope](hyp:hB), a [unit-interval local weight](hyp:hq), [features bounded by that envelope](hyp:hphi), [the stated local mass](hyp:hmass), and [population Gram coercivity](hyp:hcoercive), [failure of positive local count or realised-count-relative empirical Gram coercivity has an explicit Bernstein bound with exponent proportional to sample size times local mass](goal). -/
theorem localized_empiricalGram_coercive_of_pos
    {N : ℕ} {κ X : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (q : X → ℝ) (phi : κ → X → ℝ)
    (hqmeas : Measurable q) (hphimeas : ∀ j, Measurable (phi j))
    {p lambda B : ℝ} (hN : 0 < N) (hp : 0 < p) (hlambda : 0 < lambda) (hB : 0 ≤ B)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1)
    (hphi : ∀ j, ∀ᵐ x ∂P, |phi j x| ≤ B)
    (hmass : ∫ x, q x ∂P = p)
    (hcoercive : ∀ v : κ → ℝ,
      lambda * p * (∑ j, (v j) ^ 2) ≤
        ∑ j, ∑ k, v j * v k * ∫ x, q x * phi j x * phi k x ∂P) :
    (Measure.pi (fun _ : Fin N ↦ P)).real
        {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega} ≤
      2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
        Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
  let M : κ → κ → ℝ := fun j k ↦ ∫ x, q x * phi j x * phi k x ∂P
  let ι := Option (κ × κ)
  let g : ι → X → ℝ := fun a x ↦
    match a with
    | none => q x
    | some jk => q x * phi jk.1 x * phi jk.2 x
  let b : ι → ℝ := fun a ↦
    match a with
    | none => 1
    | some _ => 2 * B ^ 2
  let sigma2 : ι → ℝ := fun a ↦
    match a with
    | none => p
    | some _ => B ^ 4 * p
  let eta : ι → ℝ := fun a ↦
    match a with
    | none => (N : ℝ) * p / 2
    | some _ => lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ))
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) * p := mul_pos hNreal hp
  have hd : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgmeas : ∀ a, Measurable (g a) := by
    intro a
    cases a with
    | none => simpa [g] using hqmeas
    | some jk =>
        change Measurable (fun x ↦ q x * phi jk.1 x * phi jk.2 x)
        exact (hqmeas.mul (hphimeas jk.1)).mul (hphimeas jk.2)
  have hgint : ∀ a, Integrable (g a) P := by
    intro a
    cases a with
    | none => simpa [g] using localWeight_integrable P q hqmeas hq
    | some jk =>
        simpa [g] using
          localGram_integrable P q phi hqmeas hphimeas hq hB hphi jk.1 jk.2
  have hb : ∀ a, 0 ≤ b a := by
    intro a
    cases a <;> simp [b, sq_nonneg]
  have hsigma2 : ∀ a, 0 ≤ sigma2 a := by
    intro a
    cases a
    · simpa [sigma2] using le_of_lt hp
    · dsimp [sigma2]
      positivity
  have heta : ∀ a, 0 < eta a := by
    intro a
    cases a
    · simpa [eta] using div_pos hNp (by norm_num : (0 : ℝ) < 2)
    · dsimp [eta]
      positivity
  have henvelope : ∀ a, ∀ᵐ x ∂P, |g a x - ∫ y, g a y ∂P| ≤ b a := by
    intro a
    cases a with
    | none =>
        simpa [g, b, hmass] using localWeight_centered_envelope P q hq hmass
    | some jk =>
        simpa [g, b] using localGram_centered_envelope P q phi hq hB hphi jk.1 jk.2
  have hvariance : ∀ a,
      ∫ x, (g a x - ∫ y, g a y ∂P) ^ 2 ∂P ≤ sigma2 a := by
    intro a
    cases a with
    | none =>
        simpa [g, sigma2] using
          localWeight_centered_secondMoment_le P q hqmeas hq hmass
    | some jk =>
        simpa [g, sigma2] using
          localGram_centered_secondMoment_le P q phi hqmeas hphimeas hq hB hphi
            hmass jk.1 jk.2
  have hbern := iid_sum_bernstein_union_bound P g hgmeas hgint b sigma2 eta hb
    hsigma2 heta hN henvelope hvariance
  have hsubset :
      {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega} ⊆
        {omega : Fin N → X |
          ∃ a, eta a ≤
            |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|} := by
    intro omega hfail
    have hdev := localizedGram_failure_subset_deviations q phi M hN hp hlambda
      hcoercive hfail
    rcases hdev with hcount | ⟨j, k, hentry⟩
    · refine ⟨none, ?_⟩
      simpa [eta, g, localCount, hmass] using hcount
    · refine ⟨some (j, k), ?_⟩
      simpa [eta, g, M, localGramEntry] using hentry
  calc
    (Measure.pi (fun _ : Fin N ↦ P)).real
        {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega}
        ≤ (Measure.pi (fun _ : Fin N ↦ P)).real
            {omega : Fin N → X |
              ∃ a, eta a ≤
                |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|} :=
          measureReal_mono hsubset
    _ ≤ ∑ a, 2 * Real.exp
          (-(eta a) ^ 2 /
            (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))) := hbern
    _ ≤ 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
          Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
      by_cases hB0 : B = 0
      · have hrate0 : localizedGramRate κ lambda B = 0 := by
          simp [localizedGramRate, hB0]
        calc
          ∑ a, 2 * Real.exp
              (-(eta a) ^ 2 /
                (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a)))
              ≤ ∑ _a : ι, 2 * 1 := by
                apply Finset.sum_le_sum
                intro a ha
                gcongr
                rw [Real.exp_le_one_iff]
                have hden : 0 ≤
                    2 * (2 * (N : ℝ) * sigma2 a + b a * eta a) := by
                  exact mul_nonneg (by norm_num)
                    (add_nonneg
                      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hNreal))
                        (hsigma2 a))
                      (mul_nonneg (hb a) (le_of_lt (heta a))))
                exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden
          _ = 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) := by
                simp [ι, Fintype.card_option, Fintype.card_prod]
                ring
          _ = 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
                Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
                rw [hrate0]
                simp
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
        have hrate_count : localizedGramRate κ lambda B ≤ (1 / 20 : ℝ) :=
          min_le_left _ _
        have hrate_entry : localizedGramRate κ lambda B ≤
            lambda ^ 2 /
              (16 * (Fintype.card κ : ℝ) *
                (4 * (Fintype.card κ : ℝ) * B ^ 4 + B ^ 2 * lambda)) :=
          min_le_right _ _
        have hcoord : ∀ a,
            (N : ℝ) * p * localizedGramRate κ lambda B ≤
              (eta a) ^ 2 /
                (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a)) := by
          intro a
          cases a with
          | none =>
              have hmul := mul_le_mul_of_nonneg_left hrate_count (le_of_lt hNp)
              dsimp [eta, sigma2, b]
              have hid :
                  (((N : ℝ) * p / 2) ^ 2 /
                    (2 * (2 * (N : ℝ) * p + 1 * ((N : ℝ) * p / 2)))) =
                    (N : ℝ) * p * (1 / 20 : ℝ) := by
                field_simp [ne_of_gt hNreal, ne_of_gt hp]
                ring
              rw [hid]
              exact hmul
          | some jk =>
              have hmul := mul_le_mul_of_nonneg_left hrate_entry (le_of_lt hNp)
              dsimp [eta, sigma2, b]
              have hid :
                  ((lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ))) ^ 2 /
                    (2 * (2 * (N : ℝ) * (B ^ 4 * p) +
                      2 * B ^ 2 *
                        (lambda * (N : ℝ) * p / (4 * (Fintype.card κ : ℝ)))))) =
                    (N : ℝ) * p *
                      (lambda ^ 2 /
                        (16 * (Fintype.card κ : ℝ) *
                          (4 * (Fintype.card κ : ℝ) * B ^ 4 + B ^ 2 * lambda))) := by
                field_simp [ne_of_gt hNreal, ne_of_gt hp, ne_of_gt hd, ne_of_gt hBpos,
                  ne_of_gt hlambda]
                ring
              rw [hid]
              exact hmul
        calc
          ∑ a, 2 * Real.exp
              (-(eta a) ^ 2 /
                (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a)))
              ≤ ∑ _a : ι,
                  2 * Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
                apply Finset.sum_le_sum
                intro a ha
                gcongr
                calc
                  -(eta a) ^ 2 /
                      (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))
                      ≤ -((N : ℝ) * p * localizedGramRate κ lambda B) := by
                        simpa only [neg_div] using neg_le_neg (hcoord a)
                  _ = -(N : ℝ) * p * localizedGramRate κ lambda B := by ring
          _ = 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
                Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
                simp [ι, Fintype.card_option, Fintype.card_prod]
                ring

/-- Given [measurable local weights and features](hyp:hqmeas,hphimeas), [positive sample size, nonnegative local mass, and positive population coercivity](hyp:hN,hp,hlambda), a [nonnegative feature envelope](hyp:hB), a [unit-interval local weight](hyp:hq), [features bounded by that envelope](hyp:hphi), [the stated local mass](hyp:hmass), and [population Gram coercivity](hyp:hcoercive), [failure of positive local count or realised-count-relative empirical Gram coercivity has an explicit Bernstein bound with exponent proportional to sample size times local mass](goal). -/
theorem localized_empiricalGram_coercive
    {N : ℕ} {κ X : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (q : X → ℝ) (phi : κ → X → ℝ)
    (hqmeas : Measurable q) (hphimeas : ∀ j, Measurable (phi j))
    {p lambda B : ℝ} (hN : 0 < N) (hp : 0 ≤ p) (hlambda : 0 < lambda) (hB : 0 ≤ B)
    (hq : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ 1)
    (hphi : ∀ j, ∀ᵐ x ∂P, |phi j x| ≤ B)
    (hmass : ∫ x, q x ∂P = p)
    (hcoercive : ∀ v : κ → ℝ,
      lambda * p * (∑ j, (v j) ^ 2) ≤
        ∑ j, ∑ k, v j * v k * ∫ x, q x * phi j x * phi k x ∂P) :
    (Measure.pi (fun _ : Fin N ↦ P)).real
        {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega} ≤
      2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
        Real.exp (-(N : ℝ) * p * localizedGramRate κ lambda B) := by
  rcases hp.eq_or_lt with rfl | hp
  · have hprob :
        (Measure.pi (fun _ : Fin N ↦ P)).real
            {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega} ≤ 1 :=
      measureReal_le_one
    have hcard : (1 : ℝ) ≤ Fintype.card κ := by
      exact_mod_cast Fintype.card_pos
    calc
      (Measure.pi (fun _ : Fin N ↦ P)).real
          {omega : Fin N → X | ¬ LocalizedGramGood lambda q phi omega}
          ≤ 1 := hprob
      _ ≤ 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) := by
        nlinarith
      _ = 2 * (1 + (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) *
          Real.exp (-(N : ℝ) * 0 * localizedGramRate κ lambda B) := by simp
  · exact localized_empiricalGram_coercive_of_pos P q phi hqmeas hphimeas hN hp
      hlambda hB hq hphi hmass hcoercive

end Causalean.Stat.Concentration
