module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFubini
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPushforward

/-! # Finite interval partitions for folded-score branches -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

/-- A nonnegative mesh partitions its first `q` cells, modulo null shared
endpoints. -/
lemma volume_restrict_mesh_partition (q : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (volume : Measure ℝ).restrict (Set.Icc 0 ((q : ℝ) * h)) =
      ∑ k ∈ Finset.range q,
        volume.restrict (Set.Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq : (0 : ℝ) ≤ (q : ℝ) * h := mul_nonneg (by positivity) hh
      have hstep : (q : ℝ) * h ≤ ((q : ℝ) + 1) * h := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hh
      rw [show ((q + 1 : ℕ) : ℝ) * h = ((q : ℝ) + 1) * h by norm_num]
      rw [volume_restrict_Icc_split hq hstep, ih, Finset.sum_range_succ]

lemma volume_restrict_reciprocal_mesh_partition (q : ℕ) (hq : 0 < q) :
    (volume : Measure ℝ).restrict (Set.Icc 0 1) =
      ∑ k ∈ Finset.range q,
        volume.restrict
          (Set.Icc ((k : ℝ) * (q : ℝ)⁻¹)
            (((k : ℝ) + 1) * (q : ℝ)⁻¹)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpart := volume_restrict_mesh_partition q (inv_nonneg.mpr hqR.le)
  rw [mul_inv_cancel₀ hqR.ne'] at hpart
  exact hpart

lemma map_volume_reciprocal_mesh_partition (q : ℕ) (hq : 0 < q)
    {γ : Type*} [MeasurableSpace γ] (f : ℝ → γ) (hf : Measurable f) :
    Measure.map f ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      ∑ k ∈ Finset.range q,
        Measure.map f
          (volume.restrict
            (Set.Icc ((k : ℝ) * (q : ℝ)⁻¹)
              (((k : ℝ) + 1) * (q : ℝ)⁻¹))) := by
  rw [volume_restrict_reciprocal_mesh_partition q hq]
  ext s hs
  simp [Measure.map_apply hf hs]

/-- The seven affine pieces used by the perturbed triangular cell partition
the unit cell in restriction measure. -/
lemma volume_restrict_unit_seven_partition :
    (volume : Measure ℝ).restrict (Set.Icc 0 1) =
      volume.restrict (Set.Icc 0 (1 / 4 : ℝ)) +
      volume.restrict (Set.Icc (1 / 4 : ℝ) (13 / 32)) +
      volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16)) +
      volume.restrict (Set.Icc (7 / 16 : ℝ) (9 / 16)) +
      volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32)) +
      volume.restrict (Set.Icc (19 / 32 : ℝ) (3 / 4)) +
      volume.restrict (Set.Icc (3 / 4 : ℝ) 1) := by
  have h1 := volume_restrict_Icc_split
    (l := (0 : ℝ)) (m := 1 / 4) (u := 1) (by norm_num) (by norm_num)
  have h2 := volume_restrict_Icc_split
    (l := (1 / 4 : ℝ)) (m := 13 / 32) (u := 1) (by norm_num) (by norm_num)
  have h3 := volume_restrict_Icc_split
    (l := (13 / 32 : ℝ)) (m := 7 / 16) (u := 1) (by norm_num) (by norm_num)
  have h4 := volume_restrict_Icc_split
    (l := (7 / 16 : ℝ)) (m := 9 / 16) (u := 1) (by norm_num) (by norm_num)
  have h5 := volume_restrict_Icc_split
    (l := (9 / 16 : ℝ)) (m := 19 / 32) (u := 1) (by norm_num) (by norm_num)
  have h6 := volume_restrict_Icc_split
    (l := (19 / 32 : ℝ)) (m := 3 / 4) (u := 1) (by norm_num) (by norm_num)
  rw [h1, h2, h3, h4, h5, h6]
  ac_rfl

lemma map_volume_unit_seven_partition
    {γ : Type*} [MeasurableSpace γ] (f : ℝ → γ) (hf : Measurable f) :
    Measure.map f ((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      Measure.map f (volume.restrict (Set.Icc 0 (1 / 4 : ℝ))) +
      Measure.map f (volume.restrict (Set.Icc (1 / 4 : ℝ) (13 / 32))) +
      Measure.map f (volume.restrict (Set.Icc (13 / 32 : ℝ) (7 / 16))) +
      Measure.map f (volume.restrict (Set.Icc (7 / 16 : ℝ) (9 / 16))) +
      Measure.map f (volume.restrict (Set.Icc (9 / 16 : ℝ) (19 / 32))) +
      Measure.map f (volume.restrict (Set.Icc (19 / 32 : ℝ) (3 / 4))) +
      Measure.map f (volume.restrict (Set.Icc (3 / 4 : ℝ) 1)) := by
  rw [volume_restrict_unit_seven_partition]
  ext s hs
  simp [Measure.map_apply hf hs]

/-- Rescale an `x`-interval in mesh cell `k` to its unit-cell coordinate.
The factor `h` is the one-dimensional Jacobian that later multiplies every
branch density. -/
lemma map_rescaled_mesh_interval (k : ℕ) {h l u : ℝ} (hh : 0 < h)
    {γ : Type*} [MeasurableSpace γ] (f : ℝ → γ) (hf : Measurable f) :
    Measure.map (fun x : ℝ => f (x / h - k))
        (volume.restrict
          (Set.Icc (((k : ℝ) + l) * h) (((k : ℝ) + u) * h))) =
      ENNReal.ofReal h • Measure.map f (volume.restrict (Set.Icc l u)) := by
  let invCell : ℝ → ℝ := fun x => -(k : ℝ) + h⁻¹ * x
  have hinv : Measurable invCell := by fun_prop
  have hmap :
      Measure.map invCell
          (volume.restrict
            (Set.Icc (((k : ℝ) + l) * h) (((k : ℝ) + u) * h))) =
        ENNReal.ofReal h • volume.restrict (Set.Icc l u) := by
    have hm := map_affine_restrict_Icc_of_pos (-(k : ℝ)) h⁻¹
      (((k : ℝ) + l) * h) (((k : ℝ) + u) * h) (inv_pos.mpr hh)
    convert hm using 1 <;> field_simp [hh.ne'] <;> ring_nf
  have hcomp : (fun x : ℝ => f (x / h - k)) = f ∘ invCell := by
    funext x
    congr 1
    dsimp [invCell]
    rw [div_eq_inv_mul]
    ring
  rw [hcomp, ← Measure.map_map hf hinv, hmap, Measure.map_smul]

end CausalSmith.Experimentation.PilotscorePairingFrontier
