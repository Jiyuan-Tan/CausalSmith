/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ExtremalSignPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Equioscillation of best bounded-degree approximants

This module combines strict sign-matching perturbations with extremal sign
polynomials to prove the necessity direction of Chebyshev's alternation theorem.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Strict extremal perturbations -/


/-- If a polynomial has the strict sign of a positive-norm continuous
residual at every norm-attaining point of a compact interval, then subtracting
a sufficiently small positive multiple of that polynomial strictly decreases
the residual's uniform norm. [The inputs](hyp:g,r,s,hrs,hg,Q,hE,hsign) guarantee
[such an improvement](goal). -/
theorem exists_strict_uniformImprovement
    {g : ℝ → ℝ} {r s : ℝ} (hrs : r ≤ s)
    (hg : ContinuousOn g (Set.Icc r s)) {Q : Polynomial ℝ}
    (hE : 0 < intervalSupNorm g r s)
    (hsign : ∀ x ∈ Set.Icc r s,
      |g x| = intervalSupNorm g r s → 0 < g x * Q.eval x) :
    ∃ t : ℝ, 0 < t ∧
      intervalSupNorm (fun x ↦ g x - t * Q.eval x) r s <
        intervalSupNorm g r s := by
  let E := intervalSupNorm g r s
  let q : ℝ → ℝ := fun x ↦ Q.eval x
  let p : ℝ → ℝ := fun x ↦ g x * q x
  have hIcc_ne : (Set.Icc r s).Nonempty := ⟨r, le_rfl, hrs⟩
  have hq : Continuous q := Q.continuous
  have hp : ContinuousOn p (Set.Icc r s) := hg.mul hq.continuousOn
  have habs_le : ∀ x ∈ Set.Icc r s, |g x| ≤ E := by
    simpa [E] using
      (intervalSupNorm_le_iff hg hrs).mp
        (le_refl (intervalSupNorm g r s))
  obtain ⟨xE, hxE, hEmax, -⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge hIcc_ne hg.abs
  have hxE_eq : |g xE| = E := by
    simpa [E, intervalSupNorm] using hEmax.symm
  have hp_xE : 0 < p xE := by
    exact hsign xE hxE (by simpa [E] using hxE_eq)
  let B : Set ℝ := {x | x ∈ Set.Icc r s ∧ p x ≤ 0}
  have hBcompact : IsCompact B := by
    apply IsCompact.of_isClosed_subset isCompact_Icc
        (isClosed_Icc.isClosed_le hp continuousOn_const)
    exact fun _ hx ↦ hx.1
  have hc : ∃ c : ℝ, c < E ∧
      ∀ x ∈ Set.Icc r s, c ≤ |g x| → 0 < p x := by
    by_cases hBne : B.Nonempty
    · obtain ⟨xb, hxb, hxb_max⟩ :=
        hBcompact.exists_isMaxOn hBne (hg.abs.mono (fun _ hx ↦ hx.1))
      have hxb_lt : |g xb| < E := by
        apply lt_of_le_of_ne (habs_le xb hxb.1)
        intro heq
        have : 0 < p xb := hsign xb hxb.1 (by simpa [E] using heq)
        linarith [hxb.2]
      refine ⟨(|g xb| + E) / 2, by linarith, ?_⟩
      intro x hx hcx
      by_contra hnot
      have hxB : x ∈ B := ⟨hx, le_of_not_gt hnot⟩
      have hmax_le : |g x| ≤ |g xb| := hxb_max hxB
      linarith
    · refine ⟨E / 2, by linarith [hE], ?_⟩
      intro x hx _
      by_contra hnot
      exact hBne ⟨x, hx, le_of_not_gt hnot⟩
  obtain ⟨c, hcE, hc⟩ := hc
  let A : Set ℝ := {x | x ∈ Set.Icc r s ∧ c ≤ |g x|}
  have hAcompact : IsCompact A := by
    apply IsCompact.of_isClosed_subset isCompact_Icc
        (isClosed_Icc.isClosed_le continuousOn_const hg.abs)
    exact fun _ hx ↦ hx.1
  have hxEA : xE ∈ A := ⟨hxE, by linarith [hxE_eq]⟩
  obtain ⟨xm, hxm, hxm_min⟩ :=
    hAcompact.exists_isMinOn ⟨xE, hxEA⟩ (hp.mono (fun _ hx ↦ hx.1))
  let m := p xm
  have hm : 0 < m := by
    exact hc xm hxm.1 hxm.2
  obtain ⟨xM, hxM, hxM_max⟩ :=
    isCompact_Icc.exists_isMaxOn hIcc_ne hq.abs.continuousOn
  let M := |q xM|
  have hq_le : ∀ x ∈ Set.Icc r s, |q x| ≤ M := by
    intro x hx
    exact hxM_max hx
  have hM : 0 < M := by
    have hqE_ne : q xE ≠ 0 := by
      intro hzero
      simp [p, hzero] at hp_xE
    have hqE_pos : 0 < |q xE| := abs_pos.mpr hqE_ne
    exact lt_of_lt_of_le hqE_pos (hq_le xE hxE)
  let t := min (m / M ^ 2) ((E - c) / (2 * M))
  have ht₁ : 0 < m / M ^ 2 := div_pos hm (sq_pos_of_pos hM)
  have ht₂ : 0 < (E - c) / (2 * M) :=
    div_pos (sub_pos.mpr hcE) (mul_pos (by norm_num) hM)
  have ht : 0 < t := lt_min ht₁ ht₂
  refine ⟨t, ht, ?_⟩
  unfold intervalSupNorm
  apply (isCompact_Icc.sSup_lt_iff_of_continuous hIcc_ne
    ((hg.sub (hq.const_mul t).continuousOn).abs) E).2
  intro x hx
  have hgx := habs_le x hx
  have hqx := hq_le x hx
  by_cases hhigh : c ≤ |g x|
  · have hxA : x ∈ A := ⟨hx, hhigh⟩
    have hmp : m ≤ p x := hxm_min hxA
    have htM : t ≤ m / M ^ 2 := min_le_left _ _
    have hq_sq : q x ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (q x)) (abs_nonneg M)).2
          (by simpa [abs_of_pos hM] using hqx)
    have hmove : t * q x ^ 2 < 2 * p x := by
      have hM_sq : 0 < M ^ 2 := sq_pos_of_pos hM
      have ht_bound : t * M ^ 2 ≤ m := by
        apply (le_div_iff₀ hM_sq).mp
        simpa [mul_comm] using htM
      nlinarith [mul_le_mul_of_nonneg_left hq_sq (le_of_lt ht)]
    have hsquares : (g x - t * q x) ^ 2 < E ^ 2 := by
      calc
        (g x - t * q x) ^ 2 = g x ^ 2 - 2 * t * p x + t ^ 2 * q x ^ 2 := by
          simp only [p]
          ring
        _ < g x ^ 2 := by nlinarith
        _ ≤ E ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (g x)) (le_of_lt hE)).2 hgx
    rw [← sq_abs] at hsquares
    exact (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hE)).mp hsquares
  · have htM : t ≤ (E - c) / (2 * M) := min_le_right _ _
    have ht_bound : t * M ≤ (E - c) / 2 := by
      have htwoM : 0 < 2 * M := mul_pos (by norm_num) hM
      have := (le_div_iff₀ htwoM).mp htM
      nlinarith
    calc
      |g x - t * q x| ≤ |g x| + |t * q x| := abs_sub _ _
      _ = |g x| + t * |q x| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ |g x| + t * M := by gcongr
      _ < E := by
        have : |g x| < c := lt_of_not_ge hhigh
        nlinarith [sub_pos.mpr hcE]

/-! ## Equioscillation witnesses -/


/-- An equioscillation witness for [a target on an interval at a chosen
degree](hyp:f,r,s,L) records
[a best polynomial](hyp:approximant,approximant_degree,approximant_best),
[strictly ordered interval nodes](hyp:nodes,nodes_strictMono,nodes_mem), and [an orientation under
which the residual has
the optimal magnitude with alternating signs](hyp:orientation,orientation_eq,equioscillation). -/
structure EquioscillationWitness
    (f : ℝ → ℝ) (r s : ℝ) (L : ℕ) where
  approximant : Polynomial ℝ
  approximant_degree : approximant.natDegree ≤ L
  approximant_best :
    uniformApproxError f r s approximant = bestUniformApproxError f r s L
  nodes : Fin (L + 2) → ℝ
  nodes_strictMono : StrictMono nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc r s
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  equioscillation : ∀ i,
    f (nodes i) - approximant.eval (nodes i) =
      orientation * (-1 : ℝ) ^ (i : ℕ) * bestUniformApproxError f r s L

/-- Every continuous real target on a nondegenerate compact interval has a
best degree-`L` polynomial whose residual equioscillates at `L+2` strictly
ordered interval points. [The inputs](hyp:f,r,s,hrs,hf,L) guarantee [such a witness](goal). -/
theorem exists_equioscillationWitness
    {f : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hf : ContinuousOn f (Set.Icc r s)) (L : ℕ) :
    Nonempty (EquioscillationWitness f r s L) := by
  classical
  obtain ⟨Q, hQdegree, hQbest⟩ := exists_bestPolynomial hrs hf L
  let g : ℝ → ℝ := fun x ↦ f x - Q.eval x
  have hg : ContinuousOn g (Set.Icc r s) :=
    hf.sub Q.continuous.continuousOn
  have hgError : intervalSupNorm g r s = bestUniformApproxError f r s L := by
    simpa [g, uniformApproxError] using hQbest
  have hErrorNonneg : 0 ≤ bestUniformApproxError f r s L :=
    bestUniformApproxError_nonneg hrs hf L
  by_cases hErrorZero : bestUniformApproxError f r s L = 0
  · let nodes : Fin (L + 2) → ℝ := fun i ↦
      r + (i : ℝ) * (s - r) / (L + 1 : ℝ)
    have hdenom : 0 < (L + 1 : ℝ) := by positivity
    have hnodesMono : StrictMono nodes := by
      intro i j hij
      have hijReal : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      dsimp [nodes]
      have hlength : 0 < s - r := sub_pos.mpr hrs
      simpa [add_comm] using add_lt_add_left
        (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hijReal hlength) hdenom) r
    have hnodesMem : ∀ i, nodes i ∈ Set.Icc r s := by
      intro i
      have hi : (i : ℕ) ≤ L + 1 := by omega
      have hiReal : (i : ℝ) ≤ (L + 1 : ℝ) := by exact_mod_cast hi
      have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := by positivity
      have hlength : 0 < s - r := sub_pos.mpr hrs
      dsimp [nodes]
      constructor
      · have : 0 ≤ (i : ℝ) * (s - r) / (L + 1 : ℝ) := by positivity
        linarith
      · have hfrac : (i : ℝ) / (L + 1 : ℝ) ≤ 1 := by
          exact (div_le_one hdenom).2 hiReal
        calc
          r + (i : ℝ) * (s - r) / (L + 1 : ℝ) =
              r + ((i : ℝ) / (L + 1 : ℝ)) * (s - r) := by ring
          _ ≤ r + 1 * (s - r) := by gcongr
          _ = s := by ring
    have hgZero : ∀ x ∈ Set.Icc r s, g x = 0 := by
      intro x hx
      have hsup : intervalSupNorm g r s ≤ 0 := by rw [hgError, hErrorZero]
      have habs := (intervalSupNorm_le_iff hg hrs.le).mp hsup x hx
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    exact ⟨
      { approximant := Q
        approximant_degree := hQdegree
        approximant_best := hQbest
        nodes := nodes
        nodes_strictMono := hnodesMono
        nodes_mem := hnodesMem
        orientation := 1
        orientation_eq := Or.inl rfl
        equioscillation := by
          intro i
          rw [hErrorZero]
          simp only [mul_zero]
          exact hgZero (nodes i) (hnodesMem i) }⟩
  · have hErrorPos : 0 < bestUniformApproxError f r s L :=
      lt_of_le_of_ne hErrorNonneg (Ne.symm hErrorZero)
    have hAlternates : ∃ nodes orientation,
        IsAlternatingExtrema g r s L nodes orientation := by
      by_contra hno
      obtain ⟨P, hPdegree, hPsign⟩ :=
        exists_signPolynomial_of_no_alternatingExtrema hrs hg L
          (by simpa [hgError] using hErrorPos) hno
      obtain ⟨t, ht, himprove⟩ :=
        exists_strict_uniformImprovement hrs.le hg
          (by simpa [hgError] using hErrorPos) hPsign
      let R : Polynomial ℝ := Q + C t * P
      have hRdegree : R.natDegree ≤ L := by
        calc
          R.natDegree ≤ max Q.natDegree (C t * P).natDegree := by
            dsimp [R]
            exact natDegree_add_le _ _
          _ ≤ L := by
            apply max_le hQdegree
            calc
              (C t * P).natDegree ≤ (C t).natDegree + P.natDegree :=
                natDegree_mul_le
              _ ≤ L := by simpa using hPdegree
      have hResidual :
          uniformApproxError f r s R =
            intervalSupNorm (fun x ↦ g x - t * P.eval x) r s := by
        unfold uniformApproxError
        congr 2
        funext x
        simp [R, g]
        ring
      have hRlower := bestUniformApproxError_le hrs hf hRdegree
      have hRstrict : uniformApproxError f r s R <
          bestUniformApproxError f r s L := by
        rw [hResidual, ← hgError]
        exact himprove
      exact (not_lt_of_ge hRlower) hRstrict
    obtain ⟨nodes, orientation, hmono, hmem, horientation, halternates⟩ := hAlternates
    exact ⟨
      { approximant := Q
        approximant_degree := hQdegree
        approximant_best := hQbest
        nodes := nodes
        nodes_strictMono := hmono
        nodes_mem := hmem
        orientation := orientation
        orientation_eq := horientation
        equioscillation := by
          intro i
          change g (nodes i) = _
          rw [halternates i, hgError] }⟩

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
