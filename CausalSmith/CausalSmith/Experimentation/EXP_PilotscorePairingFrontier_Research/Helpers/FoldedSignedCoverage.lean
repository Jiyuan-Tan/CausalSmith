module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedCoverage

/-! # Coverage bounds uniform over arbitrary cellwise signs -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

noncomputable def shiftedGridIndices (h L U D : ℝ)
    (dl du : ℤ → ℝ) (y : ℝ) : Finset ℤ :=
  (gridIntervalIndices h (L - D) (U + D) y).filter fun k =>
    y ∈ Set.Icc ((k : ℝ) * h + L + dl k) ((k : ℝ) * h + U + du k)

lemma shiftedGridIndices_def (h L U D : ℝ) (dl du : ℤ → ℝ) (y : ℝ) :
    shiftedGridIndices h L U D dl du y =
      (gridIntervalIndices h (L - D) (U + D) y).filter fun k : ℤ =>
        y ∈ Set.Icc ((k : ℝ) * h + L + dl k) ((k : ℝ) * h + U + du k) := by
  simp only [shiftedGridIndices]

lemma shiftedGridIndices_card_sandwich {h L U D y : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (dl du : ℤ → ℝ)
    (hdl : ∀ k, |dl k| ≤ D) (hdu : ∀ k, |du k| ≤ D) :
    (gridIntervalIndices h (L + D) (U - D) y).card ≤
      (shiftedGridIndices h L U D dl du y).card ∧
    (shiftedGridIndices h L U D dl du y).card ≤
      (gridIntervalIndices h (L - D) (U + D) y).card := by
  classical
  constructor
  · apply Finset.card_le_card
    intro k hk
    have hk' := (mem_gridIntervalIndices_iff hh k).mp hk
    have hdlk := (abs_le.mp (hdl k))
    have hduk := (abs_le.mp (hdu k))
    have hactual : y ∈ Set.Icc
        ((k : ℝ) * h + L + dl k) ((k : ℝ) * h + U + du k) := by
      constructor <;> linarith [hk'.1, hk'.2]
    have hexpand : k ∈ gridIntervalIndices h (L - D) (U + D) y := by
      apply (mem_gridIntervalIndices_iff hh k).2
      constructor <;> linarith [hk'.1, hk'.2]
    exact Finset.mem_filter.mpr ⟨hexpand, hactual⟩
  · exact Finset.card_le_card (Finset.filter_subset _ _)

lemma shiftedGridIndices_card_error {h L U D y : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (hwidth : 2 * D ≤ U - L)
    (dl du : ℤ → ℝ) (hdl : ∀ k, |dl k| ≤ D) (hdu : ∀ k, |du k| ≤ D) :
    |((shiftedGridIndices h L U D dl du y).card : ℝ) - (U - L) / h| ≤
      1 + 2 * D / h := by
  have hsand := shiftedGridIndices_card_sandwich
    (h := h) (L := L) (U := U) (D := D) (y := y) hh hD dl du hdl hdu
  have hcontract : L + D ≤ U - D := by linarith
  have hexpand : L - D ≤ U + D := by linarith
  have hlo := gridIntervalIndices_card_error (y := y) hh hcontract
  have hhi := gridIntervalIndices_card_error (y := y) hh hexpand
  rw [abs_le] at hlo hhi ⊢
  have hsandR₁ :
      ((gridIntervalIndices h (L + D) (U - D) y).card : ℝ) ≤
        (shiftedGridIndices h L U D dl du y).card := by exact_mod_cast hsand.1
  have hsandR₂ :
      ((shiftedGridIndices h L U D dl du y).card : ℝ) ≤
        (gridIntervalIndices h (L - D) (U + D) y).card := by exact_mod_cast hsand.2
  constructor
  · have hlower := hlo.1
    have heq : (U - D - (L + D)) / h = (U - L) / h - 2 * D / h := by
        field_simp [hh.ne']
        ring
    rw [heq] at hlower
    linarith
  · have hupper := hhi.2
    have heq : (U + D - (L - D)) / h = (U - L) / h + 2 * D / h := by
        field_simp [hh.ne']
        ring
    rw [heq] at hupper
    linarith

/-- A branchwise density estimate that is uniform over completely unrelated
endpoint displacements in the different mesh cells.  This is the form needed
for the hypercube signs: no periodicity of the signs is assumed. -/
lemma weighted_shiftedGridIndices_error {h L U D s r y : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (hs : 0 < s) (_hr : 0 ≤ r)
    (hwidth : 2 * D ≤ U - L) (hlen : U - L = s * r)
    (dl du : ℤ → ℝ) (hdl : ∀ k, |dl k| ≤ D) (hdu : ∀ k, |du k| ≤ D) :
    |h / s * ((shiftedGridIndices h L U D dl du y).card : ℝ) - r| ≤
      h / s * (1 + 2 * D / h) := by
  have hcount := shiftedGridIndices_card_error
    (h := h) (L := L) (U := U) (D := D) (y := y)
    hh hD hwidth dl du hdl hdu
  have hid :
      h / s * ((shiftedGridIndices h L U D dl du y).card : ℝ) - r =
        (h / s) *
          (((shiftedGridIndices h L U D dl du y).card : ℝ) - (U - L) / h) := by
    rw [hlen]
    field_simp [hh.ne', hs.ne']
  rw [hid, abs_mul, abs_of_pos (div_pos hh hs)]
  exact mul_le_mul_of_nonneg_left hcount (div_nonneg hh.le hs.le)

lemma shiftedGridIndices_card_upper {h L U D y : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (hwidth : 2 * D ≤ U - L)
    (dl du : ℤ → ℝ) (hdl : ∀ k, |dl k| ≤ D) (hdu : ∀ k, |du k| ≤ D) :
    ((shiftedGridIndices h L U D dl du y).card : ℝ) ≤
      (U - L) / h + 2 * D / h + 1 := by
  have hcount := shiftedGridIndices_card_error
    (h := h) (L := L) (U := U) (D := D) (y := y)
    hh hD hwidth dl du hdl hdu
  rw [abs_le] at hcount
  linarith

/-- The weighted form needed when a sign changes both branch endpoints and
the reciprocal Jacobian.  The reference Jacobian is `h / s`; each cell may
use an unrelated weight within `E` of that value. -/
lemma weighted_shiftedGridIndices_variable_error {h L U D s r E y : ℝ}
    (hh : 0 < h) (hD : 0 ≤ D) (hs : 0 < s) (hr : 0 ≤ r) (hE : 0 ≤ E)
    (hwidth : 2 * D ≤ U - L) (hlen : U - L = s * r)
    (dl du w : ℤ → ℝ) (hdl : ∀ k, |dl k| ≤ D) (hdu : ∀ k, |du k| ≤ D)
    (hw : ∀ k, |w k - h / s| ≤ E) :
    |(∑ k ∈ shiftedGridIndices h L U D dl du y, w k) - r| ≤
      h / s * (1 + 2 * D / h) +
        E * ((U - L) / h + 2 * D / h + 1) := by
  let I := shiftedGridIndices h L U D dl du y
  have href := weighted_shiftedGridIndices_error
    (h := h) (L := L) (U := U) (D := D) (s := s) (r := r) (y := y)
    hh hD hs hr hwidth hlen dl du hdl hdu
  have hcard := shiftedGridIndices_card_upper
    (h := h) (L := L) (U := U) (D := D) (y := y)
    hh hD hwidth dl du hdl hdu
  have hpert :
      |∑ k ∈ I, (w k - h / s)| ≤
        E * ((I.card : ℝ)) := by
    calc
      |∑ k ∈ I, (w k - h / s)| ≤ ∑ k ∈ I, |w k - h / s| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ I, E := Finset.sum_le_sum fun k _ => hw k
      _ = E * (I.card : ℝ) := by simp [mul_comm]
  have hpert' :
      |∑ k ∈ I, (w k - h / s)| ≤
        E * ((U - L) / h + 2 * D / h + 1) := by
    exact hpert.trans (mul_le_mul_of_nonneg_left hcard hE)
  have hid :
      (∑ k ∈ I, w k) - r =
        (∑ k ∈ I, (w k - h / s)) +
          (h / s * (I.card : ℝ) - r) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hid]
  have hsum := add_le_add hpert' (by simpa [I] using href)
  simpa [add_comm] using (abs_add_le _ _).trans hsum

/-- Sum of finitely many arbitrarily signed/shifted branches.  The only input
from each sign pattern is its uniform endpoint displacement bound. -/
-- keep: reusable signed-branch coverage estimate for folded constructions
lemma signedGridBranchDensity_error {n : ℕ} {h : ℝ} (hh : 0 < h)
    (b : Fin n → GridBranch) (D : Fin n → ℝ)
    (dl du : Fin n → ℤ → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hs : ∀ i, 0 < (b i).slope)
    (hr : ∀ i, 0 ≤ (b i).domainLength)
    (hwidth : ∀ i, 2 * D i ≤ (b i).upper - (b i).lower)
    (hlen : ∀ i, (b i).upper - (b i).lower =
      (b i).slope * (b i).domainLength)
    (hdl : ∀ i k, |dl i k| ≤ D i) (hdu : ∀ i k, |du i k| ≤ D i)
    (y : ℝ) :
    |(∑ i, h / (b i).slope *
          ((shiftedGridIndices h (b i).lower (b i).upper (D i)
            (dl i) (du i) y).card : ℝ)) -
        ∑ i, (b i).domainLength| ≤
      ∑ i, h / (b i).slope * (1 + 2 * D i / h) := by
  have hi (i : Fin n) :
      |h / (b i).slope *
          ((shiftedGridIndices h (b i).lower (b i).upper (D i)
            (dl i) (du i) y).card : ℝ) - (b i).domainLength| ≤
        h / (b i).slope * (1 + 2 * D i / h) :=
    weighted_shiftedGridIndices_error hh (hD i) (hs i) (hr i)
      (hwidth i) (hlen i) (dl i) (du i) (hdl i) (hdu i)
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hi i)

end CausalSmith.Experimentation.PilotscorePairingFrontier
