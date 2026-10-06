module
public import Mathlib

/-!
# Adjacent-parameter perfect pairings

Finite points on the unit interval can be sorted and paired in adjacent
order. The chosen gaps total at most one, and concavity bounds the sum of
their fractional powers.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- A perfect pairing of the `N` labeled positions is a list of `N/2`
disjoint two-element edges covering each position exactly once. -/
structure PerfectPairing (N : ℕ) where
  edge : Fin (N / 2) → Fin N × Fin N
  distinct : ∀ j, (edge j).1 ≠ (edge j).2
  covers : ∀ i : Fin N, ∃! j : Fin (N / 2),
    i = (edge j).1 ∨ i = (edge j).2

/-- Given [a family size](hyp:N) that is [even and at least two](hyp:hN,hN2), and [unit-interval parameters](hyp:t,ht),
[a perfect pairing has total absolute parameter gap at most one](goal). -/
theorem exists_pairing_gap_le_one (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ M : PerfectPairing N,
      (∑ j : Fin (N / 2), |t (M.edge j).1 - t (M.edge j).2|) ≤ 1 := by
  have htwo : N / 2 * 2 = N := by
    have hd : 2 ∣ N := hN.two_dvd
    omega
  let e : Fin (N / 2) × Fin 2 ≃ Fin N :=
    finProdFinEquiv.trans (finCongr htwo)
  let σ := Tuple.sort t
  let u : Fin N → ℝ := t ∘ σ
  have hu : Monotone u := Tuple.monotone_sort t
  let M : PerfectPairing N := {
    edge := fun j => (σ (e (j, 0)), σ (e (j, 1)))
    distinct := by
      intro j h
      have he := σ.injective h
      have he' := e.injective he
      exact (Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (congrArg Prod.snd he')
    covers := by
      intro i
      obtain ⟨⟨j, k⟩, hjk⟩ := e.surjective (σ.symm i)
      refine ⟨j, ?_, ?_⟩
      · fin_cases k
        · left; exact (σ.apply_symm_apply i).symm.trans (congrArg σ hjk.symm)
        · right; exact (σ.apply_symm_apply i).symm.trans (congrArg σ hjk.symm)
      · intro j' hj'
        rcases hj' with hj' | hj'
        · have h : e (j, k) = e (j', 0) := by
            calc
              _ = σ.symm i := hjk
              _ = σ.symm (σ (e (j', 0))) := congrArg σ.symm hj'
              _ = _ := σ.symm_apply_apply _
          exact (congrArg Prod.fst (e.injective h)).symm
        · have h : e (j, k) = e (j', 1) := by
            calc
              _ = σ.symm i := hjk
              _ = σ.symm (σ (e (j', 1))) := congrArg σ.symm hj'
              _ = _ := σ.symm_apply_apply _
          exact (congrArg Prod.fst (e.injective h)).symm
  }
  refine ⟨M, ?_⟩
  have heval (j : Fin (N / 2)) (k : Fin 2) :
      (e (j, k)).val = 2 * j.val + k.val := by
    simp [e, finCongr_apply, finProdFinEquiv_apply_val]
    omega
  let v : ℕ → ℝ := fun i => if hi : i < N then u ⟨i, hi⟩ else 1
  have hv (i : Fin N) : v i.val = u i := by simp [v]
  have hgap (j : Fin (N / 2)) :
      |t (M.edge j).1 - t (M.edge j).2| =
        v (2 * j.val + 1) - v (2 * j.val) := by
    have hle : e (j, 0) ≤ e (j, 1) := by
      apply Fin.le_iff_val_le_val.mpr
      simp [heval]
    have hmono := hu hle
    change u (e (j, 0)) ≤ u (e (j, 1)) at hmono
    have hval0 : (e (j, 0)).val = 2 * j.val := by simpa using heval j 0
    have hval1 : (e (j, 1)).val = 2 * j.val + 1 := by simpa using heval j 1
    change |u (e (j, 0)) - u (e (j, 1))| = _
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmono)]
    rw [← hv, ← hv, hval0, hval1]
  let g : ℕ → ℝ := fun i => v (i + 1) - v i
  let s : Finset ℕ := Finset.univ.image (fun j : Fin (N / 2) => 2 * j.val)
  have hinj : Function.Injective (fun j : Fin (N / 2) => 2 * j.val) := by
    intro j k h
    apply Fin.ext
    change 2 * j.val = 2 * k.val at h
    omega
  have hsubset : s ⊆ Finset.range (N - 1) := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_range]
    have := j.isLt
    omega
  have hgnonneg (i : ℕ) (hi : i ∈ Finset.range (N - 1)) : 0 ≤ g i := by
    have hi' : i < N - 1 := Finset.mem_range.mp hi
    have hi0 : i < N := by omega
    have hi1 : i + 1 < N := by omega
    change 0 ≤ v (i + 1) - v i
    simp only [v, dif_pos hi0, dif_pos hi1]
    have hidx : (⟨i, hi0⟩ : Fin N) ≤ ⟨i + 1, hi1⟩ := by
      apply Fin.le_iff_val_le_val.mpr
      change i ≤ i + 1
      omega
    exact sub_nonneg.mpr (hu hidx)
  have hsumgap : (∑ j : Fin (N / 2), |t (M.edge j).1 - t (M.edge j).2|) =
      ∑ i ∈ s, g i := by
    rw [Finset.sum_image (by intro j _ k _ h; exact hinj h)]
    apply Finset.sum_congr rfl
    intro j hj
    simpa [g] using hgap j
  have hsumle : (∑ i ∈ s, g i) ≤ ∑ i ∈ Finset.range (N - 1), g i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro i hi _
      exact hgnonneg i hi)
  have htel : (∑ i ∈ Finset.range (N - 1), g i) = v (N - 1) - v 0 :=
    Finset.sum_range_sub v (N - 1)
  have hlast : v (N - 1) ≤ 1 := by
    have hi : N - 1 < N := by omega
    simpa [v, hi, u] using (ht (σ ⟨N - 1, hi⟩)).2
  have hfirst : 0 ≤ v 0 := by
    have hi : 0 < N := by omega
    simpa [v, hi, u] using (ht (σ ⟨0, hi⟩)).1
  rw [hsumgap]
  linarith [hsumle, htel]

/-- For nonnegative gaps totaling at most one, the sum of their `p`th
powers is at most the number of gaps to the power `1-p`, for `0<p≤1`.
This is finite Jensen concavity for the power function. -/
theorem sum_rpow_le_card_rpow {m : ℕ} (hm : 0 < m) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (a : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : (∑ i, a i) ≤ 1) :
    (∑ i, a i ^ p) ≤ (m : ℝ) ^ (1 - p) := by
  let c : ℝ := (m : ℝ)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast hm
  have hw : (∑ _i : Fin m, c⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc.ne'
  have hj := (Real.concaveOn_rpow hp0.le hp1).le_map_sum
    (t := Finset.univ) (w := fun _ : Fin m => c⁻¹) (p := a)
    (by intro i hi; exact inv_nonneg.mpr hc.le) hw
    (by intro i hi; exact ha i)
  simp only [smul_eq_mul] at hj
  have hca : c⁻¹ * (∑ i, a i) ≤ c⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hc.le)]
  have hr := Real.rpow_le_rpow
    (mul_nonneg (inv_nonneg.mpr hc.le) (Finset.sum_nonneg (fun i hi => ha i))) hca hp0.le
  have hmain : c⁻¹ * (∑ i, a i ^ p) ≤ (c⁻¹) ^ p := by
    calc
      _ ≤ (c⁻¹ * ∑ i, a i) ^ p := by simpa [Finset.mul_sum] using hj
      _ ≤ _ := hr
  have hmult := mul_le_mul_of_nonneg_left hmain hc.le
  have hpow : c * (c⁻¹) ^ p = c ^ (1 - p) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    calc
      c * c ^ (-p) = c ^ (1 : ℝ) * c ^ (-p) := by simp
      _ = c ^ (1 + -p) := (Real.rpow_add hc 1 (-p)).symm
      _ = c ^ (1 - p) := by ring
  calc
    (∑ i, a i ^ p) = c * (c⁻¹ * ∑ i, a i ^ p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ c * (c⁻¹) ^ p := hmult
    _ = (m : ℝ) ^ (1 - p) := by simpa [c] using hpow

end Causalean.Mathlib.Topology.SpaceFillingCurve
