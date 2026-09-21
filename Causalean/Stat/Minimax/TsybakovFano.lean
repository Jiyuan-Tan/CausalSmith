module
public import Causalean.Stat.Minimax.Fano

/-!
# Tsybakov's reference-law form of Fano's method

This file proves the sharp likelihood-ratio truncation form of Fano's method
used in minimax lower bounds. It treats one reference law and `M` alternatives,
retaining the square-root prefactor and correction in Tsybakov's theorem.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

private lemma average_sqrt_half_le_sqrt_average_half
    {M : ℕ} (hM : 0 < M) (K : Fin M → ℝ) (hK : ∀ j, 0 ≤ K j) :
    (M : ℝ)⁻¹ * ∑ j, Real.sqrt (K j / 2) ≤
      Real.sqrt (((M : ℝ)⁻¹ * ∑ j, K j) / 2) := by
  let m : ℝ := M
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hM
  change m⁻¹ * ∑ j, Real.sqrt (K j / 2) ≤
    Real.sqrt ((m⁻¹ * ∑ j, K j) / 2)
  have hcs := Real.sum_sqrt_mul_sqrt_le
    (f := fun j => K j / 2) (g := fun _j => (1 : ℝ))
    (Finset.univ : Finset (Fin M))
    (fun j => div_nonneg (hK j) (by norm_num)) (fun _j => zero_le_one)
  simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  rw [← Finset.sum_div] at hcs
  change (∑ j, Real.sqrt (K j / 2)) ≤
    Real.sqrt ((∑ j, K j) / 2) * Real.sqrt m at hcs
  have hsum0 : 0 ≤ ∑ j, K j := Finset.sum_nonneg fun j _ => hK j
  have hsqrt_scale :
      Real.sqrt ((∑ j, K j) / 2) * Real.sqrt m =
        m * Real.sqrt ((m⁻¹ * ∑ j, K j) / 2) := by
    have hm0 : 0 ≤ m := hm.le
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hsum0 (by norm_num)),
      Real.sq_sqrt hm0,
      Real.sq_sqrt (div_nonneg (mul_nonneg (inv_nonneg.mpr hm0) hsum0) (by norm_num))]
    field_simp [hm.ne']
  rw [hsqrt_scale] at hcs
  calc
    m⁻¹ * ∑ j, Real.sqrt (K j / 2) ≤ m⁻¹ *
        (m * Real.sqrt ((m⁻¹ * ∑ j, K j) / 2)) :=
      mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hm.le)
    _ = Real.sqrt ((m⁻¹ * ∑ j, K j) / 2) := by field_simp [hm.ne']

private lemma average_kl_tail_numeric
    {M : ℕ} (hM : 2 ≤ M) {α : ℝ} (hα : 0 ≤ α)
    (K : Fin M → ℝ) (hK : ∀ j, 0 ≤ K j)
    (havg : (M : ℝ)⁻¹ * ∑ j, K j ≤ α * Real.log M) :
    (M : ℝ)⁻¹ * ∑ j,
        (K j + Real.sqrt (K j / 2)) / (Real.log M / 2) ≤
      2 * α + Real.sqrt (2 * α / Real.log M) := by
  let m : ℝ := M
  let L : ℝ := Real.log M
  let A : ℝ := m⁻¹ * ∑ j, K j
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hM)
  have hM1 : 1 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hM)
  have hL : 0 < L := by simpa [L] using Real.log_pos hM1
  have hA0 : 0 ≤ A := mul_nonneg (inv_nonneg.mpr hm.le)
    (Finset.sum_nonneg fun j _ => hK j)
  have havg' : A ≤ α * L := havg
  have hsqrtavg := average_sqrt_half_le_sqrt_average_half
    (lt_of_lt_of_le (by omega : 0 < 2) hM) K hK
  change m⁻¹ * ∑ j, (K j + Real.sqrt (K j / 2)) / (L / 2) ≤ _
  have hcombine :
      m⁻¹ * ∑ j, (K j + Real.sqrt (K j / 2)) / (L / 2) =
        (A + m⁻¹ * ∑ j, Real.sqrt (K j / 2)) / (L / 2) := by
    dsimp [A]
    rw [← Finset.sum_div]
    rw [Finset.sum_add_distrib]
    ring
  rw [hcombine]
  have hsqrtmono : Real.sqrt (A / 2) ≤ Real.sqrt (α * L / 2) := by
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right havg' (by norm_num))
  have hnum :
      A + m⁻¹ * ∑ j, Real.sqrt (K j / 2) ≤
        α * L + Real.sqrt (α * L / 2) :=
    add_le_add havg' (hsqrtavg.trans hsqrtmono)
  have hid :
      (α * L + Real.sqrt (α * L / 2)) / (L / 2) =
        2 * α + Real.sqrt (2 * α / L) := by
    have hsqrt_id : Real.sqrt (α * L / 2) / (L / 2) =
        Real.sqrt (2 * α / L) := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [div_pow, div_pow,
        Real.sq_sqrt (div_nonneg (mul_nonneg hα hL.le) (by norm_num)),
        Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hα) hL.le)]
      field_simp [hL.ne']
    rw [add_div]
    rw [show α * L / (L / 2) = 2 * α by field_simp [hL.ne']]
    rw [hsqrt_id]
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq hid

/-- For a [measurable observation space and parameter space](hyp:Ω,Θ), a
[number `M` of alternatives with `M ≥ 2`](hyp:M,hM), [probability laws](hyp:P),
[parameter values](hyp:θ), a [radius and KL fraction](hyp:s,α) with
[`0 < α < 1/8`](hyp:hα,hα8), [pairwise `2s` separation](hyp:hsep),
[finite KL divergence to the reference law](hyp:hfin), an
[average KL budget `α log M`](hyp:havg), and a
[measurable estimator](hyp:est,hest), [some law has radius-`s` error at least
`sqrt(M)/(1+sqrt(M)) * (1-2α-sqrt(2α/log M))`](goal).

This is Tsybakov (2009), Theorem 2.5 and Corollary 2.6. Index `0` is the
reference law and `Fin.succ j` indexes the `M` alternatives. -/
theorem tsybakov_fano_exists_error
    {Ω Θ : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (M : ℕ) (hM : 2 ≤ M) (P : Fin (M + 1) → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (θ : Fin (M + 1) → Θ)
    {s α : ℝ} (hα : 0 < α) (hα8 : α < 1 / 8)
    (hsep : ∀ i k, i ≠ k → 2 * s ≤ dist (θ i) (θ k))
    (hfin : ∀ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≠ ⊤)
    (havg : (M : ℝ)⁻¹ * ∑ j : Fin M,
      (InformationTheory.klDiv (P j.succ) (P 0)).toReal ≤ α * Real.log M)
    {est : Ω → Θ} (hest : Measurable est) :
    ∃ i, Real.sqrt M / (1 + Real.sqrt M) *
          (1 - 2 * α - Real.sqrt (2 * α / Real.log M)) ≤
        (P i).real {ω | s ≤ dist (est ω) (θ i)} := by
  let m : ℝ := M
  let L : ℝ := Real.log M
  let q : ℝ := Real.sqrt m
  let δ : ℝ := 2 * α + Real.sqrt (2 * α / L)
  let B : ℝ := q / (1 + q) * (1 - δ)
  let A : Fin (M + 1) → Set Ω := fun i => acceptanceRegion est (θ i) s
  let K : Fin M → ℝ := fun j =>
    (InformationTheory.klDiv (P j.succ) (P 0)).toReal
  let T : Fin M → Set Ω := fun j =>
    {ω | L / 2 < llr (P j.succ) (P 0) ω}
  have hac : ∀ j : Fin M, P j.succ ≪ P 0 := fun j =>
    (InformationTheory.klDiv_ne_top_iff.mp (hfin j)).1
  have hint : ∀ j : Fin M, Integrable (llr (P j.succ) (P 0)) (P j.succ) := fun j =>
    (InformationTheory.klDiv_ne_top_iff.mp (hfin j)).2
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hM)
  have hM1 : 1 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hM)
  have hL : 0 < L := by simpa [L] using Real.log_pos hM1
  have hq : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 hm
  have hq2 : q ^ 2 = m := by
    dsimp [q]
    exact Real.sq_sqrt hm.le
  have hexp : Real.exp (L / 2) = q := by
    calc
      Real.exp (L / 2) = Real.exp (Real.log m * (1 / 2)) := by
        congr 1
        dsimp [L, m]
        ring
      _ = m ^ (1 / 2 : ℝ) := (Real.rpow_def_of_pos hm _).symm
      _ = q := by simpa [q] using (Real.sqrt_eq_rpow m).symm
  have hK0 : ∀ j, 0 ≤ K j := fun _j => ENNReal.toReal_nonneg
  have havg' : m⁻¹ * ∑ j, K j ≤ α * L := havg
  have htail : ∀ j, (P j.succ).real (T j) ≤
      (K j + Real.sqrt (K j / 2)) / (L / 2) := by
    intro j
    exact llr_tail_le_kl_add_sqrt (P j.succ) (P 0) (hac j) (hint j)
      (by linarith)
  have htailAvg : m⁻¹ * ∑ j, (P j.succ).real (T j) ≤ δ := by
    calc
      m⁻¹ * ∑ j, (P j.succ).real (T j) ≤
          m⁻¹ * ∑ j, (K j + Real.sqrt (K j / 2)) / (L / 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun j _ => htail j
        · exact inv_nonneg.mpr hm.le
      _ ≤ δ := average_kl_tail_numeric hM hα.le K hK0 havg'
  have htailSum : ∑ j, (P j.succ).real (T j) ≤ m * δ := by
    have hmul := mul_le_mul_of_nonneg_left htailAvg hm.le
    have hm0 : m ≠ 0 := hm.ne'
    simpa [hm0] using hmul
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i => by
    exact measurableSet_acceptanceRegion hest (θ i) s
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    exact acceptanceRegion_pairwiseDisjoint (est := est) (θ := θ) (s := s) hsep
  have hAltDisj : Pairwise (Function.onFun Disjoint (fun j : Fin M => A j.succ)) := by
    intro j k hjk
    exact hAdisj ((Fin.succ_injective M).ne hjk)
  have hAltMeas : ∀ j : Fin M, MeasurableSet (A j.succ) := fun j => hAmeas j.succ
  have hsumRef :
      ∑ j : Fin M, (P 0).real (A j.succ) =
        (P 0).real (⋃ j : Fin M, A j.succ) := by
    exact (measureReal_iUnion_fintype hAltDisj hAltMeas).symm
  have hUnionSubset : (⋃ j : Fin M, A j.succ) ⊆ (A 0)ᶜ := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    obtain ⟨j, hj⟩ := hω
    intro h0
    exact Set.disjoint_left.mp (hAdisj (Fin.succ_ne_zero j)) hj h0
  have hchange : ∀ j : Fin M,
      (P j.succ).real (A j.succ) ≤
        q * (P 0).real (A j.succ) + (P j.succ).real (T j) := by
    intro j
    have hc := measureReal_le_exp_mul_add_llr_tail
      (P j.succ) (P 0) (hac j) (hAmeas j.succ) (L / 2)
    simpa [T, K, hexp] using hc
  have hsumChange :
      ∑ j : Fin M, (P j.succ).real (A j.succ) ≤
        q * ∑ j : Fin M, (P 0).real (A j.succ) +
          ∑ j : Fin M, (P j.succ).real (T j) := by
    calc
      ∑ j : Fin M, (P j.succ).real (A j.succ) ≤
          ∑ j : Fin M,
            (q * (P 0).real (A j.succ) + (P j.succ).real (T j)) :=
        Finset.sum_le_sum fun j _ => hchange j
      _ = q * ∑ j : Fin M, (P 0).real (A j.succ) +
          ∑ j : Fin M, (P j.succ).real (T j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hBform :
      B = Real.sqrt M / (1 + Real.sqrt M) *
        (1 - 2 * α - Real.sqrt (2 * α / Real.log M)) := by
    dsimp [B, q, m, δ, L]
    ring
  by_contra hcon
  push Not at hcon
  rw [← hBform] at hcon
  have herr : ∀ i, (P i).real (A i)ᶜ < B := by
    intro i
    have hi := hcon i
    have hevent : {ω | s ≤ dist (est ω) (θ i)} = (A i)ᶜ := by
      ext ω
      simp [A, acceptanceRegion, not_lt]
    simpa [hevent] using hi
  have hRefLt : ∑ j : Fin M, (P 0).real (A j.succ) < B := by
    rw [hsumRef]
    exact lt_of_le_of_lt
      (measureReal_mono hUnionSubset (measure_ne_top _ _)) (herr 0)
  have hcorrect : ∀ j : Fin M, 1 - B < (P j.succ).real (A j.succ) := by
    intro j
    have herrj := herr j.succ
    rw [measureReal_compl (hAmeas j.succ), probReal_univ] at herrj
    linarith
  have : Nonempty (Fin M) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le (by omega : 0 < 2) hM)
  have hcorrectSum : m * (1 - B) <
      ∑ j : Fin M, (P j.succ).real (A j.succ) := by
    calc
      m * (1 - B) = ∑ _j : Fin M, (1 - B) := by
        simp [m, nsmul_eq_mul]
        ring
      _ < ∑ j : Fin M, (P j.succ).real (A j.succ) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun j _ => hcorrect j)
  have hUpper :
      ∑ j : Fin M, (P j.succ).real (A j.succ) < q * B + m * δ := by
    refine lt_of_le_of_lt hsumChange ?_
    nlinarith [htailSum, mul_lt_mul_of_pos_left hRefLt hq]
  have hstrict : m * (1 - B) < q * B + m * δ :=
    hcorrectSum.trans hUpper
  have hidentity : m * (1 - B) = q * B + m * δ := by
    dsimp [B]
    rw [← hq2]
    field_simp [show 1 + q ≠ 0 by positivity]
    ring
  rw [hidentity] at hstrict
  exact (lt_irrefl _ hstrict)

end Causalean.Stat
