module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Tuning

/-!
Nonnegative affine raw tables and their exact total mass before normalization.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,B,eps), Reciprocal tilting gives nonnegative core probabilities whose sum is at most one.  This gives [the stated result](goal).-/
-- @node: affine_latent_core_bounds
lemma affine_latent_core_bounds {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : eps < 1) :
    (∀ i, 0 ≤ latentCoreMass sigma i) ∧ (∑ i, latentCoreMass sigma i) ≤ 1 := by
  have hden i : 0 < B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg (by linarith) (sigma.mem i).1)
  constructor
  · intro i
    exact mul_nonneg (div_nonneg ha.le (hden i).le) (abs_nonneg _)
  · calc
      (∑ i, latentCoreMass sigma i) ≤ ∑ i, |sigma.weights i| := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_of_le_one_left (abs_nonneg _)
        exact (div_le_one (hden i)).mpr
          (le_add_of_nonneg_right (mul_nonneg (by linarith) (sigma.mem i).1))
      _ = 1 := sigma.abs_sum

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,z,B,eps), The latent PMF has exactly the specified core and filler masses.  This gives [the stated result](goal).-/
-- @node: affine_latent_mass_readback
lemma affine_latent_mass_readback {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : eps < 1) (z : Latent L) :
    (latentPMF sigma z).toReal =
      (match z with | none => 1 - ∑ i, latentCoreMass sigma i | some i => latentCoreMass sigma i) := by
  obtain ⟨hn, hs⟩ := affine_latent_core_bounds sigma ha he
  apply normalizedPMF_toReal
  · intro z
    cases z with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hn i
  · simp only [Fintype.sum_option]
    ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,B,eps), The expected latent node is at most alpha divided by one minus the overlap floor.  This gives [the stated result](goal).-/
-- @node: affine_latent_node_mean_bound
lemma affine_latent_node_mean_bound {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : eps < 1) :
    (∑ z : Latent L, (latentPMF sigma z).toReal * latentNode sigma z) ≤
      (B / (100 * (L : Real) ^ 2)) / (1 - eps) := by
  simp_rw [affine_latent_mass_readback sigma ha he]
  simp only [Fintype.sum_option, latentNode, mul_zero, zero_add]
  calc
    (∑ i, latentCoreMass sigma i * sigma.nodes i) ≤
        ∑ i, (B / (100 * (L : Real) ^ 2) / (1 - eps)) * |sigma.weights i| := by
      apply Finset.sum_le_sum
      intro i _
      have hepos : 0 < 1 - eps := by linarith
      have hd : 0 < B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i :=
        add_pos_of_pos_of_nonneg ha (mul_nonneg hepos.le (sigma.mem i).1)
      have hb : (B / (100 * (L : Real) ^ 2)) /
          (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i) * sigma.nodes i ≤
          (B / (100 * (L : Real) ^ 2)) / (1 - eps) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hd hepos]
        nlinarith [sq_nonneg (B / (100 * (L : Real) ^ 2))]
      simpa only [latentCoreMass, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hb (abs_nonneg (sigma.weights i))
    _ = _ := by rw [← Finset.mul_sum, sigma.abs_sum, mul_one]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hB,ha,he,B,eps), The latent second moment is bounded by the bandwidth times its first moment.  This gives [the stated result](goal).-/
-- @node: affine_latent_node_second_moment_bound
lemma affine_latent_node_second_moment_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (hB : 0 ≤ B)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : eps < 1) :
    (∑ z : Latent L, (latentPMF sigma z).toReal * latentNode sigma z ^ 2) ≤
      B * ((B / (100 * (L : Real) ^ 2)) / (1 - eps)) := by
  calc
    _ ≤ ∑ z : Latent L, (latentPMF sigma z).toReal *
        (B * latentNode sigma z) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have hv : latentNode sigma z ∈ Set.Icc 0 B := by
        cases z with
        | none => exact ⟨le_rfl, hB⟩
        | some i => exact sigma.mem i
      nlinarith [hv.1, hv.2]
    _ = B * ∑ z : Latent L, (latentPMF sigma z).toReal * latentNode sigma z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (affine_latent_node_mean_bound sigma ha he) hB

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The reservoir has mass greater than one half uniformly in all legal public indices.  This gives [the stated result](goal).-/
-- @node: affine_reservoir_pos
lemma affine_reservoir_pos (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    1 / 2 < 1 - ((affineTuning n m d eps).Kstar : Real) * latentMeanMass sigma := by
  obtain ⟨_, _, _, _, _, ha, hb, hK⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have he : eps < 1 := by linarith
  have hm := affine_latent_node_mean_bound sigma ha he
  change (∑ z, (latentPMF sigma z).toReal * latentNode sigma z) ≤
    (affineTuning n m d eps).alpha / (1 - eps) at hm
  have hprob : ∑ z : Latent (affineTuning n m d eps).L, (latentPMF sigma z).toReal = 1 :=
    by
      simp_rw [affine_latent_mass_readback sigma ha he]
      simp only [Fintype.sum_option]
      ring
  have hmean : latentMeanMass sigma ≤ (4 / 3) * (affineTuning n m d eps).b0 := by
    dsimp only [latentMeanMass]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hprob, one_mul]
    have hfrac : (affineTuning n m d eps).alpha / (1 - eps) ≤
        (1 / 3) * (affineTuning n m d eps).b0 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - eps)).mpr
      have hid : (affineTuning n m d eps).alpha = eps * (affineTuning n m d eps).b0 := by
        dsimp only [affineTuning]; field_simp
      nlinarith
    change (affineTuning n m d eps).b0 + _ ≤ _
    linarith
  have hprod := mul_le_mul_of_nonneg_left hmean
    (Nat.cast_nonneg (affineTuning n m d eps).Kstar)
  nlinarith

/-- [Under the stated inputs and conditions](hyp:hK,f,d,K), Extending a finite cell table by zero preserves its total mass.  This gives [the stated result](goal).-/
-- @node: affine_sum_prefix
lemma affine_sum_prefix (d K : Nat) (hK : K ≤ d) (f : Fin K → Real) :
    (∑ j : Fin d, if h : j.val < K then f ⟨j.val, h⟩ else 0) = ∑ j, f j := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Fin.sum_trunc _ (by intro j; simp [Fin.val_natAdd])]
  simp

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,z,n,m,d), Every raw affine atom is nonnegative, including the reservoir and null cells.  This gives [the stated result](goal).-/
-- @node: affine_rawTable_nonneg
lemma affine_rawTable_nonneg (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (z : Obs d) : 0 ≤ rawTable hyp n m d eps sigma lat z := by
  obtain ⟨_, _, _, _, _, ha, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hp := affine_reservoir_pos n m d eps hn hd heps heps' sigma
  have hv (j) : 0 ≤ latentNode sigma (lat j) := by
    cases lat j with
    | none => exact le_refl 0
    | some i => exact (sigma.mem i).1
  dsimp only [rawTable]
  by_cases hj : z.1.val < (affineTuning n m d eps).Kstar
  · rw [dif_pos hj]
    apply mul_nonneg
    · cases ha' : z.2.1 <;> simp only [ha', Bool.false_eq_true, if_false, if_true]
      · nlinarith [hv ⟨z.1.val, hj⟩]
      · nlinarith [hv ⟨z.1.val, hj⟩]
    · cases ha' : z.2.1
      · cases z.2.2 <;> simp [ha', bernoulliMass]
      · cases hl : lat ⟨z.1.val, hj⟩ with
        | none => cases z.2.2 <;> simp [ha', hl, bernoulliMass]
        | some i =>
          cases hyp <;> cases z.2.2 <;>
            simp [ha', hl, latentPolar, bernoulliMass] <;> split_ifs <;> norm_num
  · rw [dif_neg hj]
    by_cases hr : z.1.val = (affineTuning n m d eps).Kstar
    · rw [if_pos hr]
      cases z.2.2 <;> simp [bernoulliMass] <;> linarith
    · rw [if_neg hr]

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,sigma,hyp,lat,n,m,d), Summing the raw table gives the shared reservoir-plus-cells normalizer.  This gives [the stated result](goal).-/
-- @node: affine_rawTable_sum
lemma affine_rawTable_sum (n m d : Nat) (eps : Real) (hd : 2 ≤ d) (heps : 0 < eps)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    (∑ z : Obs d, rawTable hyp n m d eps sigma lat z) = rawNormalizer n m d eps sigma lat := by
  let K := (affineTuning n m d eps).Kstar
  have hKd : K < d := by
    have h := Nat.min_le_left (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)))
    change K ≤ d - 1 at h
    omega
  have hab : (affineTuning n m d eps).alpha = eps * (affineTuning n m d eps).b0 := by
    dsimp only [affineTuning]
    field_simp
  simp only [Fintype.sum_prod_type]
  have hcell (j : Fin d) :
      (∑ a : Bool, ∑ y : Bool, rawTable hyp n m d eps sigma lat (j, a, y)) =
      (if h : j.val < K then (affineTuning n m d eps).b0 + latentNode sigma (lat ⟨j.val, h⟩)
       else 0) + (if j.val = K then 1 - (K : Real) * latentMeanMass sigma else 0) := by
    by_cases hj : j.val < K
    · have hr : j.val ≠ K := by omega
      simp [rawTable, K, hj, hr, Fintype.sum_bool, bernoulliMass]
      nlinarith [hab]
    · by_cases hr : j.val = K <;>
        simp [rawTable, K, hj, hr, Fintype.sum_bool, bernoulliMass] <;> ring
  simp_rw [hcell]
  rw [Finset.sum_add_distrib, affine_sum_prefix d K hKd.le
    (fun j => (affineTuning n m d eps).b0 + latentNode sigma (lat j))]
  have hres : (∑ j : Fin d, if j.val = K then 1 - (K : Real) * latentMeanMass sigma else 0) =
      1 - (K : Real) * latentMeanMass sigma := by
    have heq (j : Fin d) : j.val = K ↔ j = ⟨K, hKd⟩ := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; subst j; rfl
    simp_rw [heq]
    simp
  rw [hres]
  exact add_comm _ _

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,lat,n,m,d), Positive rare-cell masses preserve the reservoir lower bound on the normalizer.  This gives [the stated result](goal).-/
-- @node: affine_rawNormalizer_pos
lemma affine_rawNormalizer_pos (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    1 / 2 < rawNormalizer n m d eps sigma lat := by
  have hp := affine_reservoir_pos n m d eps hn hd heps heps' sigma
  obtain ⟨_, _, _, _, _, _, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hs : 0 ≤ ∑ j, ((affineTuning n m d eps).b0 + latentNode sigma (lat j)) := by
    apply Finset.sum_nonneg
    intro j _
    apply add_nonneg hb.le
    cases lat j with
    | none => exact le_refl 0
    | some i => exact (sigma.mem i).1
  dsimp only [rawNormalizer]
  linarith

/-- [Under the stated inputs and conditions](hyp:alpha,mass,fallback,hn,hs,z), Normalizing any finite nonnegative table divides each atom by its positive total.  This gives [the stated result](goal).-/
-- @node: affine_normalizedPMF_toReal
lemma affine_normalizedPMF_toReal {alpha : Type} [Fintype alpha]
    (mass : alpha → Real) (fallback : PMF alpha) (hn : ∀ z, 0 ≤ mass z)
    (hs : 0 < ∑ z, mass z) (z : alpha) :
    (normalizedPMF mass fallback z).toReal = mass z / (∑ z, mass z) := by
  have ht : (∑' z, ENNReal.ofReal (mass z)) = ENNReal.ofReal (∑ z, mass z) := by
    rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun z _ => hn z)]
  have hne : ENNReal.ofReal (∑ z, mass z) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hs)
  have hok : (∑' z, ENNReal.ofReal (mass z)) ≠ 0 ∧
      (∑' z, ENNReal.ofReal (mass z)) ≠ ⊤ := by
    rw [ht]
    exact ⟨hne, ENNReal.ofReal_ne_top⟩
  dsimp only [normalizedPMF]
  rw [dif_pos hok]
  simp only [PMF.normalize_apply, ht,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hn z), ENNReal.toReal_ofReal hs.le, div_eq_mul_inv]

end CausalSmith.Stat.AnnotationRarearmFrontier
