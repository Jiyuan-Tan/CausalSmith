/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Interpolation

/-!
# Monomial approximation of multivariate Hölder functions

This module converts the diagonal Fréchet Taylor polynomial supplied by a
multivariate Hölder condition into an explicitly indexed monomial polynomial.
The resulting remainder constant is uniform over the Hölder ball.
-/

@[expose] public section

namespace Causalean.Stat.Nonparametric

open scoped BigOperators Pointwise Manifold ContDiff
open Causalean.Stat.Nonparametric

private def indexCount {d j : ℕ} (ι : Fin j → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun l => ι l = i)).card

private lemma sum_indexCount {d j : ℕ} (ι : Fin j → Fin d) :
    ∑ i, indexCount ι i = j := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin j)))
    (t := (Finset.univ : Finset (Fin d))) (f := ι) (fun l _ => Finset.mem_univ (ι l))
  simpa [indexCount] using h.symm

private lemma prod_eq_monomial {d j : ℕ} (ι : Fin j → Fin d) (u : Fin d → ℝ) :
    ∏ l, u (ι l) = ∏ i, u i ^ indexCount ι i := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (fun l _ => Finset.mem_univ (ι l))
    (fun l => u (ι l))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
    Finset.prod_const]
  rfl

private lemma smul_eq_sum_single' {d : ℕ} (h : ℝ) (u : Fin d → ℝ) :
    (h • u : Fin d → ℝ) = ∑ i, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ a]
  simp

private lemma diagonal_expansion {d j : ℕ} (f : (Fin d → ℝ) → ℝ)
    (x0 u : Fin d → ℝ) (h : ℝ) :
    iteratedFDeriv ℝ j f x0 (fun _ => h • u) =
      ∑ ι : Fin j → Fin d, h ^ j * iteratedFDeriv ℝ j f x0
        (fun l => Pi.single (ι l) 1) * ∏ i, u i ^ indexCount ι i := by
  classical
  have he : (fun _ : Fin j => h • u) =
      fun _ => ∑ i, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
    funext l
    exact smul_eq_sum_single' h u
  rw [he, ContinuousMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro ι hι
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, prod_eq_monomial]
  ring

/-- **Local monomial approximation in a Hölder ball.** Fix a centre `x0` in `d`-dimensional
Euclidean space and a finite family `expo` of exponent multi-indices. If [the smoothness
index `β` is positive](hyp:hβ), [the Hölder constant `L` is positive](hyp:hL), [the
neighbourhood radius `r` is positive](hyp:_hr), [the closed sup-norm cube of radius `r`
around `x0` is contained in the domain `S`](hyp:hS), and [`expo` lists every exponent
multi-index of total degree up to the Taylor order](hyp:hcover), then [there is a constant
`C_b ≥ 0`, depending only on `β` and `d`, such that every function `f` in the standard
Hölder ball of exponent `β`, constant `L`, and domain `S` is approximated near `x0`, at any
bandwidth `h ∈ (0, r)`, by a monomial combination in the `expo` basis with error at most
`C_b · L · h^β`, uniformly over the unit cube of rescaled directions](goal). -/
theorem holder_taylor_monomial_approx {d p : ℕ} {β L r : ℝ} {x0 : Fin d → ℝ}
    {S : Set (Fin d → ℝ)}
    (hβ : 0 < β) (hL : 0 < L) (_hr : 0 < r)
    (hS : {x : Fin d → ℝ | ∀ i, |x i - x0 i| ≤ r} ⊆ S)
    (expo : Fin p → (Fin d → ℕ))
    (hcover : ∀ e : Fin d → ℕ, (∑ j, e j) ≤ ⌈β⌉₊ - 1 → ∃ k, expo k = e) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ f : (Fin d → ℝ) → ℝ, HolderBallStd f β L S →
        ∀ h : ℝ, 0 < h → h < r →
          ∃ θ : Fin p → ℝ,
            ∀ u : Fin d → ℝ, (∀ j, |u j| ≤ 1) →
              |f (x0 + h • u) - ∑ k, θ k * ∏ j, (u j) ^ (expo k j)| ≤
                Cb * L * h ^ β := by
  classical
  let m := ⌈β⌉₊ - 1
  refine ⟨1 / (Nat.factorial m : ℝ), by positivity, ?_⟩
  intro f hf h hh hhr
  let pick : ∀ (j : Fin (m + 1)) (ι : Fin j → Fin d), Fin p := fun j ι =>
    Classical.choose (hcover (indexCount ι) (by rw [sum_indexCount]; omega))
  have hpick : ∀ (j : Fin (m + 1)) (ι : Fin j → Fin d),
      expo (pick j ι) = indexCount ι := fun j ι =>
    Classical.choose_spec (hcover (indexCount ι) (by rw [sum_indexCount]; omega))
  let θ : Fin p → ℝ := fun k => ∑ j : Fin (m + 1), ∑ ι : Fin j → Fin d,
    if pick j ι = k then
      (1 / (Nat.factorial j : ℝ)) * h ^ (j : ℕ) *
        iteratedFDeriv ℝ (j : ℕ) f x0 (fun l => Pi.single (ι l) 1)
    else 0
  refine ⟨θ, ?_⟩
  intro u hu
  have hpoly : (∑ k, θ k * ∏ i, u i ^ expo k i) =
      ∑ j : Fin (m + 1), (1 / (Nat.factorial (j : ℕ) : ℝ)) *
        iteratedFDeriv ℝ (j : ℕ) f x0 (fun _ => h • u) := by
    simp only [θ, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm, diagonal_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ι hι
    rw [Finset.sum_eq_single (pick j ι)]
    · simp [hpick]
      ring
    · intro k hk hne
      simp [hne.symm]
    · simp
  have hpoly' : (∑ j ∈ Finset.range (m + 1),
      (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j f x0 (fun _ => h • u)) =
      ∑ k, θ k * ∏ i, u i ^ expo k i := by
    rw [hpoly]
    exact (Fin.sum_univ_eq_sum_range _ (m + 1)).symm
  set U : Set (Fin d → ℝ) := {x | ∀ i, |x i - x0 i| < r}
  have hU : IsOpen U := by
    rw [show U = ⋂ i, {x : Fin d → ℝ | |x i - x0 i| < r} by ext x; simp [U]]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
  have hUS : U ⊆ S := fun x hx => hS (fun i => le_of_lt (hx i))
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (h • u) ∈ U := by
    intro t ht i
    have he : (x0 + t • (h • u)) i - x0 i = t * (h * u i) := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hh]
    calc
      t * (h * |u i|) ≤ 1 * (h * |u i|) :=
        mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hh.le (abs_nonneg _))
      _ ≤ h := by simpa using mul_le_mul_of_nonneg_left (hu i) hh.le
      _ < r := hhr
  have hb := holder_line_taylor hβ hf hU hUS x0 (h • u) hseg
  rw [show ⌈β⌉₊ - 1 = m from rfl, hpoly'] at hb
  have hunorm : ‖u‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simpa using hu i
  have hy : ‖h • u‖ ≤ h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    calc
      h * ‖u‖ ≤ h * 1 := mul_le_mul_of_nonneg_left hunorm hh.le
      _ = h := mul_one h
  calc
    _ ≤ (L / (Nat.factorial m : ℝ)) * ‖h • u‖ ^ β := hb
    _ ≤ (L / (Nat.factorial m : ℝ)) * h ^ β := by
      gcongr
    _ = (1 / (Nat.factorial m : ℝ)) * L * h ^ β := by ring

end Causalean.Stat.Nonparametric
