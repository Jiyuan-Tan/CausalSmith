module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Membership
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Certificate

/-!
Signed reciprocal-certificate separation before reservoir normalization.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:L,hL,hB,heps,heps',sigma,B,eps), [The signed one-cell raw target gap is at least one twelfth of b0](goal).
-/
-- @node: affine_signed_target_gap
lemma affine_signed_target_gap (L : Nat) (B eps : Real) (hL : 2 ≤ L)
    (hB : 0 < B) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) (sigma : ConeDual L B eps) :
    let alpha := B / (100 * (L : Real) ^ 2)
    let b0 := alpha / eps
    b0 / 12 ≤ ∑ i, sigma.weights i *
      ((b0 + sigma.nodes i) * alpha / (alpha + (1 - eps) * sigma.nodes i))  := by
  let alpha := B / (100 * (L : Real) ^ 2)
  let b0 := alpha / eps
  have hLR : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have ha : 0 < alpha := div_pos hB (by positivity)
  have hb : 0 < b0 := div_pos ha heps
  have he : 0 < 1 - eps := by linarith
  have hab : alpha = eps * b0 := by dsimp [b0]; field_simp
  have hzero : ∑ i, sigma.weights i = 0 := by
    simpa using sigma.moments 0 (by omega)
  have hid (i : Fin (L + 2)) :
      (b0 + sigma.nodes i) * alpha / (alpha + (1 - eps) * sigma.nodes i) =
      alpha / (1 - eps) + (b0 * (1 - 2 * eps) / (1 - eps)) *
        (alpha / (alpha + (1 - eps) * sigma.nodes i)) := by
    have hden : 0 < alpha + (1 - eps) * sigma.nodes i :=
      add_pos_of_pos_of_nonneg ha (mul_nonneg he.le (sigma.mem i).1)
    have hden' : alpha + sigma.nodes i * (1 - eps) ≠ 0 := by
      simpa only [mul_comm] using hden.ne'
    field_simp [ha.ne', he.ne', hden.ne', hden']
    nlinarith [hab]
  have hsum : (∑ i, sigma.weights i *
      ((b0 + sigma.nodes i) * alpha / (alpha + (1 - eps) * sigma.nodes i))) =
      (b0 * (1 - 2 * eps) / (1 - eps)) *
        ∑ i, sigma.weights i * (alpha / (alpha + (1 - eps) * sigma.nodes i)) := by
    simp_rw [hid, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hzero, zero_mul, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcoef : b0 * (2 / 3) ≤ b0 * (1 - 2 * eps) / (1 - eps) := by
    apply (le_div_iff₀ he).2
    nlinarith
  have hcpos : 0 ≤ b0 * (1 - 2 * eps) / (1 - eps) :=
    div_nonneg (mul_nonneg hb.le (by linarith)) he.le
  have hgap := mul_le_mul_of_nonneg_left sigma.gap hcpos
  change b0 / 12 ≤ _
  rw [hsum]
  change (b0 * (1 - 2 * eps) / (1 - eps)) * (1 / 8) ≤ _ at hgap
  linarith

/-- A single rare cell's raw contribution to the target, including the zero filler. -/
-- @node: affineCellTarget
noncomputable def affineCellTarget {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (hyp : Bool) (z : Latent L) : Real :=
  (B / (100 * (L : Real) ^ 2) / eps + latentNode sigma z) *
    (match z with
    | none => 0
    | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2)

/-- [Under the stated inputs and conditions](hyp:L,sigma,i,B,eps), Multiplying the polar sign by the absolute weight restores the signed weight.  This gives [the stated result](goal).-/
-- @node: affine_latent_polar_weight
lemma affine_latent_polar_weight {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (i : Fin (L + 2)) :
    |sigma.weights i| * latentPolar sigma (some i) = sigma.weights i := by
  dsimp only [latentPolar]
  split_ifs with h
  · rw [abs_of_nonneg h, mul_one]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,B,eps), The expected target difference is exactly the reciprocal signed functional.  This gives [the stated result](goal).-/
-- @node: affine_cell_target_mean_difference
lemma affine_cell_target_mean_difference {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (ha : 0 < B / (100 * (L : Real) ^ 2))
    (he : eps < 1) :
    (∑ z : Latent L, (latentPMF sigma z).toReal * affineCellTarget sigma true z) -
      (∑ z : Latent L, (latentPMF sigma z).toReal * affineCellTarget sigma false z) =
    ∑ i, sigma.weights i *
      ((B / (100 * (L : Real) ^ 2) / eps + sigma.nodes i) *
        (B / (100 * (L : Real) ^ 2)) /
          (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [affine_latent_mass_readback sigma ha he]
  simp only [Fintype.sum_option, affineCellTarget, latentNode,
    Bool.false_eq_true, if_false, if_true, mul_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = |sigma.weights i| * latentPolar sigma (some i) *
        ((B / (100 * (L : Real) ^ 2) / eps + sigma.nodes i) *
          (B / (100 * (L : Real) ^ 2)) /
            (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)) := by
      dsimp only [latentCoreMass]
      ring
    _ = _ := by rw [affine_latent_polar_weight]

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,heps,heps',sigma,B,eps), The two hypotheses separate the expected one-cell raw targets by b0/12.  This gives [the stated result](goal).-/
-- @node: affine_cell_target_mean_gap
lemma affine_cell_target_mean_gap (L : Nat) (B eps : Real) (hL : 2 ≤ L)
    (hB : 0 < B) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual L B eps) :
    (B / (100 * (L : Real) ^ 2) / eps) / 12 ≤
      (∑ z : Latent L, (latentPMF sigma z).toReal * affineCellTarget sigma true z) -
        (∑ z : Latent L, (latentPMF sigma z).toReal * affineCellTarget sigma false z) := by
  have hLR : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  rw [affine_cell_target_mean_difference sigma (by positivity) (by linarith)]
  exact affine_signed_target_gap L B eps hL hB heps heps' sigma

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,heps,hyp,z,B,eps), Each raw cell target is between zero and the cell's total raw mass.  This gives [the stated result](goal).-/
-- @node: affine_cell_target_bounds
lemma affine_cell_target_bounds {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (heps : 0 < eps)
    (hyp : Bool) (z : Latent L) :
    0 ≤ affineCellTarget sigma hyp z ∧
      affineCellTarget sigma hyp z ≤
        B / (100 * (L : Real) ^ 2) / eps + latentNode sigma z := by
  have hb : 0 ≤ B / (100 * (L : Real) ^ 2) / eps := (div_pos ha heps).le
  cases z with
  | none => simpa [affineCellTarget, latentNode] using hb
  | some i =>
    have hw : 0 ≤ B / (100 * (L : Real) ^ 2) / eps + sigma.nodes i :=
      add_nonneg hb (sigma.mem i).1
    cases hyp <;>
      simp only [affineCellTarget, latentNode, latentPolar,
        Bool.false_eq_true, if_false, if_true] <;>
      split_ifs <;> constructor <;> nlinarith

/-- [Under the stated inputs and conditions](hyp:L,sigma,hB,ha,heps,he,hyp,B,eps), The cell target second moment has the bound used in the prior concentration step.  This gives [the stated result](goal).-/
-- @node: affine_cell_target_second_moment_bound
lemma affine_cell_target_second_moment_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (hB : 0 ≤ B)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (heps : 0 < eps) (he : eps < 1)
    (hyp : Bool) :
    (∑ z : Latent L, (latentPMF sigma z).toReal * affineCellTarget sigma hyp z ^ 2) ≤
      2 * (B / (100 * (L : Real) ^ 2) / eps) ^ 2 +
        2 * B * ((B / (100 * (L : Real) ^ 2)) / (1 - eps)) := by
  let b := B / (100 * (L : Real) ^ 2) / eps
  have hp : ∑ z : Latent L, (latentPMF sigma z).toReal = 1 := by
    simp_rw [affine_latent_mass_readback sigma ha he]
    simp only [Fintype.sum_option]
    ring
  calc
    _ ≤ ∑ z : Latent L, (latentPMF sigma z).toReal *
        (2 * b ^ 2 + 2 * latentNode sigma z ^ 2) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      obtain ⟨h0, h1⟩ := affine_cell_target_bounds sigma ha heps hyp z
      have hw : 0 ≤ b + latentNode sigma z := h0.trans h1
      have hs := sq_le_sq₀ h0 hw |>.mpr h1
      nlinarith [sq_nonneg (b - latentNode sigma z)]
    _ = 2 * b ^ 2 + 2 * ∑ z : Latent L,
        (latentPMF sigma z).toReal * latentNode sigma z ^ 2 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := by
      have hs := affine_latent_node_second_moment_bound sigma hB ha he
      change 2 * b ^ 2 + _ ≤ 2 * b ^ 2 + _
      linarith

end CausalSmith.Stat.AnnotationRarearmFrontier
