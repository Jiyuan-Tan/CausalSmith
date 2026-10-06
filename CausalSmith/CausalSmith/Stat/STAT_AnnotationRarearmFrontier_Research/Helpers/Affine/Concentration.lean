module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Separation
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Tuning

/-!
Exact normalized target readback and the deterministic error decomposition used for affine
prior concentration. The filler, reservoir, and null cells contribute zero target.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- The raw target is the sum of the treated rare-cell contributions. -/
-- @node: affineRawTarget
noncomputable def affineRawTarget (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    Real := ∑ j, affineCellTarget sigma hyp (lat j)

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,j,n,m,d), Every control mean is zero, including the reservoir and null cells.  This gives [the stated result](goal).-/
-- @node: affine_control_mean_zero
lemma affine_control_mean_zero (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) : outcomeMean (normalizedLaw hyp n m d eps hd sigma lat) false j = 0 := by
  unfold outcomeMean markedMass
  rw [affine_jointMass_readback n m d eps hn hd heps heps' sigma hyp lat]
  have hz : rawTable hyp n m d eps sigma lat (j, false, true) = 0 := by
    simp [rawTable, bernoulliMass]
  rw [hz, zero_div, zero_div]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,j,n,m,d), Rare treated means are exactly their assigned binary marks; other means vanish.  This gives [the stated result](goal).-/
-- @node: affine_treated_mean_readback
lemma affine_treated_mean_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) : outcomeMean (normalizedLaw hyp n m d eps hd sigma lat) true j =
      if hj : j.val < (affineTuning n m d eps).Kstar then
        match lat ⟨j.val, hj⟩ with
        | none => 0
        | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
      else 0 := by
  have hQ : rawNormalizer n m d eps sigma lat ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num)
      (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat))
  obtain ⟨_, _, _, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  unfold outcomeMean markedMass
  rw [affine_jointMass_readback n m d eps hn hd heps heps' sigma hyp lat,
    affine_armMass_readback n m d eps hn hd heps heps' sigma hyp lat]
  by_cases hj : j.val < (affineTuning n m d eps).Kstar
  · have hv : 0 ≤ latentNode sigma (lat ⟨j.val, hj⟩) := by
      cases lat ⟨j.val, hj⟩ with
      | none => exact le_refl 0
      | some i => exact (sigma.mem i).1
    have hs : (affineTuning n m d eps).alpha +
        (1 - eps) * latentNode sigma (lat ⟨j.val, hj⟩) ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg ha (mul_nonneg (by linarith) hv))
    simp only [rawTable, dif_pos hj, if_true, bernoulliMass]
    field_simp
    rfl
  · simp [rawTable, hj, bernoulliMass]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), The normalized ATE is precisely the raw target divided by the common total mass.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_readback
lemma affine_normalized_target_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) =
      affineRawTarget n m d eps sigma hyp lat / rawNormalizer n m d eps sigma lat := by
  let K := (affineTuning n m d eps).Kstar
  have hKd : K ≤ d := by
    have h := Nat.min_le_left (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)))
    change K ≤ d - 1 at h
    omega
  unfold ateFunctional
  simp_rw [affine_control_mean_zero n m d eps hn hd heps heps' sigma hyp lat,
    affine_treated_mean_readback n m d eps hn hd heps heps' sigma hyp lat,
    affine_cellMass_readback n m d eps hn hd heps heps' sigma hyp lat, sub_zero]
  have hcell (j : Fin d) :
      (if hj : j.val < K then (affineTuning n m d eps).b0 + latentNode sigma (lat ⟨j.val, hj⟩)
       else if j.val = K then 1 - (K : Real) * latentMeanMass sigma else 0) /
        rawNormalizer n m d eps sigma lat *
      (if hj : j.val < K then
        match lat ⟨j.val, hj⟩ with
        | none => 0
        | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
       else 0) =
      if hj : j.val < K then
        affineCellTarget sigma hyp (lat ⟨j.val, hj⟩) / rawNormalizer n m d eps sigma lat
      else 0 := by
    by_cases hj : j.val < K
    · simp only [dif_pos hj, affineCellTarget]
      rw [div_mul_eq_mul_div]
      cases lat ⟨j.val, hj⟩
      · simp
      · dsimp only [affineTuning]
    · simp [hj]
  dsimp only [K] at hcell
  simp_rw [hcell]
  rw [affine_sum_prefix d (affineTuning n m d eps).Kstar hKd
    (fun j => affineCellTarget sigma hyp (lat j) / rawNormalizer n m d eps sigma lat)]
  exact (Finset.sum_div _ _ _).symm

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), The raw target lies between zero and the shared normalizer.  This gives [the stated result](goal).-/
-- @node: affine_raw_target_bounds
lemma affine_raw_target_bounds (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    0 ≤ affineRawTarget n m d eps sigma hyp lat ∧
      affineRawTarget n m d eps sigma hyp lat ≤ rawNormalizer n m d eps sigma lat := by
  obtain ⟨_, _, _, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have ha' : 0 < (affineTuning n m d eps).B /
      (100 * ((affineTuning n m d eps).L : Real) ^ 2) := ha
  have hb (j : Fin (affineTuning n m d eps).Kstar) :=
    affine_cell_target_bounds sigma ha' heps hyp (lat j)
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hb j).1)
  · have hs : affineRawTarget n m d eps sigma hyp lat ≤
        ∑ j, ((affineTuning n m d eps).b0 + latentNode sigma (lat j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (hb j).2
    have hr := affine_reservoir_pos n m d eps hn hd heps heps' sigma
    unfold rawNormalizer
    linarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), Both normalized affine targets lie in the unit interval.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_bounds
lemma affine_normalized_target_bounds (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    0 ≤ ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) ∧
      ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) ≤ 1 := by
  rw [affine_normalized_target_readback n m d eps hn hd heps heps' sigma hyp lat]
  have hQ : 0 < rawNormalizer n m d eps sigma lat :=
    lt_trans (by norm_num) (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat)
  obtain ⟨h0, h1⟩ := affine_raw_target_bounds n m d eps hn hd heps heps' sigma hyp lat
  exact ⟨div_nonneg h0 hQ.le, (div_le_one hQ).mpr h1⟩

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,t,n,m,d), Normalization separates the raw target error from the total-mass error exactly.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_error_identity
lemma affine_normalized_target_error_identity (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (t : Real) :
    ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t =
      (affineRawTarget n m d eps sigma hyp lat - t) +
        ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) *
          (1 - rawNormalizer n m d eps sigma lat) := by
  rw [affine_normalized_target_readback n m d eps hn hd heps heps' sigma hyp lat]
  have hQ : rawNormalizer n m d eps sigma lat ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num)
      (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat))
  field_simp
  ring

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,t,n,m,d), The squared normalized error is controlled by the raw target and normalizer errors.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_sq_error_bound
lemma affine_normalized_target_sq_error_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (t : Real) :
    (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t) ^ 2 ≤
      2 * (affineRawTarget n m d eps sigma hyp lat - t) ^ 2 +
        2 * (1 - rawNormalizer n m d eps sigma lat) ^ 2 := by
  obtain ⟨h0, h1⟩ := affine_normalized_target_bounds n m d eps hn hd heps heps' sigma hyp lat
  have ht : ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) ^ 2 ≤ 1 := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_right ht
    (sq_nonneg (1 - rawNormalizer n m d eps sigma lat))
  rw [affine_normalized_target_error_identity n m d eps hn hd heps heps' sigma hyp lat t]
  have hs := add_sq_le (a := affineRawTarget n m d eps sigma hyp lat - t)
    (b := ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) *
      (1 - rawNormalizer n m d eps sigma lat))
  rw [mul_pow] at hs
  nlinarith

/-- Under the stated inputs and conditions, Finite latent product expectations of additive statistics equal K times their cell mean.  This gives [the stated result](goal). -/
-- @node: affine_latent_integral_sum
lemma affine_latent_integral_sum {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (K : Nat) (f : Latent L → Real) :
    (∫ lat : Fin K → Latent L, ∑ j, f (lat j)
      ∂Measure.pi (fun _ : Fin K => (latentPMF sigma).toMeasure)) =
        (K : Real) * ∑ z, (latentPMF sigma z).toReal * f z := by
  have hf : Integrable f (latentPMF sigma).toMeasure := Integrable.of_finite
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin K => (latentPMF sigma).toMeasure)
      hf.aestronglyMeasurable, PMF.integral_eq_sum, smul_eq_mul]
    simp
    ring
  · intro j _
    exact integrable_comp_eval hf

/-- [Under the stated hypotheses](hyp:hyp), Expected raw targets are K times their one-cell expectations.  This gives [the stated result](goal). -/
-- @node: affine_raw_target_mean
lemma affine_raw_target_mean (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) (hyp : Bool) :
    (∫ lat, affineRawTarget n m d eps sigma hyp lat
      ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) =
        ((affineTuning n m d eps).Kstar : Real) *
          ∑ z, (latentPMF sigma z).toReal * affineCellTarget sigma hyp z :=
  affine_latent_integral_sum sigma _ _

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps'), Independence lifts the signed one-cell gap to the expected raw targets.  This gives [the stated result](goal). -/
-- @node: affine_raw_target_mean_gap
lemma affine_raw_target_mean_gap (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 / 12 ≤
      (∫ lat, affineRawTarget n m d eps sigma true lat
        ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) -
      (∫ lat, affineRawTarget n m d eps sigma false lat
        ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar =>
          (latentPMF sigma).toMeasure)) := by
  obtain ⟨_, _, hL, _, hB, _, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hell : 1 ≤ logScale n eps := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + labelScale n eps by
        apply le_add_of_nonneg_right; unfold labelScale; positivity)
    simpa only [logScale, Real.log_exp] using h
  have hLn : 2 ≤ (affineTuning n m d eps).L := by
    have : (2 : Real) ≤ (affineTuning n m d eps).L := by linarith
    exact_mod_cast this
  have hg := affine_cell_target_mean_gap _ _ eps hLn hB heps heps' sigma
  rw [affine_raw_target_mean, affine_raw_target_mean, ← mul_sub]
  have hgK := mul_le_mul_of_nonneg_left hg
    (Nat.cast_nonneg (affineTuning n m d eps).Kstar : (0 : Real) ≤ _)
  convert hgK using 1
  · rfl
  · dsimp only [affineTuning]
    ring

/-- Under the stated inputs and conditions, Independence makes the variance of any additive finite latent mark exactly K-fold.  This gives [the stated result](goal). -/
-- @node: affine_latent_variance_sum
lemma affine_latent_variance_sum {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (K : Nat) (f : Latent L → Real) :
    variance (fun lat : Fin K → Latent L => ∑ j, f (lat j))
      (Measure.pi (fun _ : Fin K => (latentPMF sigma).toMeasure)) =
        (K : Real) * variance f (latentPMF sigma).toMeasure := by
  have hf : ∀ _ : Fin K, MemLp f 2 (latentPMF sigma).toMeasure :=
    fun _ => MemLp.of_discrete
  have h := variance_sum_pi hf
  convert h using 1
  · congr 1
    ext lat
    simp
  · simp

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hyp), The raw target variance is bounded using its one-cell second moment.  This gives [the stated result](goal). -/
-- @node: affine_raw_target_variance_bound
lemma affine_raw_target_variance_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) (hyp : Bool) :
    variance (affineRawTarget n m d eps sigma hyp)
      (Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) ≤
        ((affineTuning n m d eps).Kstar : Real) *
          (2 * (affineTuning n m d eps).b0 ^ 2 +
            (8 / 3) * (affineTuning n m d eps).B * (affineTuning n m d eps).alpha) := by
  obtain ⟨_, _, _, _, hB, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have ha' : 0 < (affineTuning n m d eps).B /
      (100 * ((affineTuning n m d eps).L : Real) ^ 2) := ha
  have hs := affine_cell_target_second_moment_bound sigma hB.le ha' heps (by linarith) hyp
  have hv := variance_le_expectation_sq (μ := (latentPMF sigma).toMeasure)
    (X := affineCellTarget sigma hyp) (by fun_prop)
  rw [PMF.integral_eq_sum] at hv
  simp only [Pi.pow_apply, smul_eq_mul] at hv
  have he : 0 < 1 - eps := by linarith
  have hr : (affineTuning n m d eps).alpha / (1 - eps) ≤
      (4 / 3) * (affineTuning n m d eps).alpha := by
    apply (div_le_iff₀ he).mpr
    nlinarith
  have hc : variance (affineCellTarget sigma hyp) (latentPMF sigma).toMeasure ≤
      2 * (affineTuning n m d eps).b0 ^ 2 +
        (8 / 3) * (affineTuning n m d eps).B * (affineTuning n m d eps).alpha := by
    have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * (affineTuning n m d eps).B by positivity)
    have hs' : (∑ z, (latentPMF sigma z).toReal * affineCellTarget sigma hyp z ^ 2) ≤
        2 * (affineTuning n m d eps).b0 ^ 2 +
          2 * (affineTuning n m d eps).B * ((affineTuning n m d eps).alpha / (1 - eps)) := hs
    linarith
  rw [show affineRawTarget n m d eps sigma hyp =
    (fun lat => ∑ j, affineCellTarget sigma hyp (lat j)) from rfl,
    affine_latent_variance_sum]
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

/-- Under the stated inputs and conditions, The common normalizer has expectation exactly one under the latent product prior.  This gives [the stated result](goal). -/
-- @node: affine_raw_normalizer_mean
lemma affine_raw_normalizer_mean (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    (∫ lat, rawNormalizer n m d eps sigma lat
      ∂Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar =>
        (latentPMF sigma).toMeasure)) = 1 := by
  unfold rawNormalizer
  rw [integral_add (integrable_const _) Integrable.of_finite, integral_const,
    affine_latent_integral_sum sigma _ (fun z => (affineTuning n m d eps).b0 + latentNode sigma z)]
  simp only [probReal_univ, one_smul]
  have hb : (affineTuning n m d eps).b0 =
      (affineTuning n m d eps).B / (100 * ((affineTuning n m d eps).L : Real) ^ 2) / eps := by
    dsimp only [affineTuning]
  rw [hb]
  change 1 - _ * latentMeanMass sigma + _ * latentMeanMass sigma = 1
  ring

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps'), The normalizer variance is at most four thirds K B alpha.  This gives [the stated result](goal). -/
-- @node: affine_raw_normalizer_variance_bound
lemma affine_raw_normalizer_variance_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    variance (rawNormalizer n m d eps sigma)
      (Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)) ≤
        (4 / 3) * ((affineTuning n m d eps).Kstar : Real) *
          (affineTuning n m d eps).B * (affineTuning n m d eps).alpha := by
  obtain ⟨_, _, _, _, hB, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have ha' : 0 < (affineTuning n m d eps).B /
      (100 * ((affineTuning n m d eps).L : Real) ^ 2) := ha
  have hs := affine_latent_node_second_moment_bound sigma hB.le ha' (by linarith)
  have hv := variance_le_expectation_sq (μ := (latentPMF sigma).toMeasure)
    (X := latentNode sigma) (by fun_prop)
  rw [PMF.integral_eq_sum] at hv
  simp only [Pi.pow_apply, smul_eq_mul] at hv
  have he : 0 < 1 - eps := by linarith
  have hr : (affineTuning n m d eps).alpha / (1 - eps) ≤
      (4 / 3) * (affineTuning n m d eps).alpha := by
    apply (div_le_iff₀ he).mpr
    nlinarith
  have hc : variance (latentNode sigma) (latentPMF sigma).toMeasure ≤
      (4 / 3) * (affineTuning n m d eps).B * (affineTuning n m d eps).alpha := by
    have hm := mul_le_mul_of_nonneg_left hr hB.le
    have hs' : (∑ z, (latentPMF sigma z).toReal * latentNode sigma z ^ 2) ≤
      (affineTuning n m d eps).B * ((affineTuning n m d eps).alpha / (1 - eps)) := hs
    linarith
  unfold rawNormalizer
  rw [variance_const_add AEStronglyMeasurable.of_discrete,
    affine_latent_variance_sum sigma _ (fun z => (affineTuning n m d eps).b0 + latentNode sigma z),
    variance_const_add (by fun_prop)]
  have hk := mul_le_mul_of_nonneg_left hc
    (Nat.cast_nonneg (affineTuning n m d eps).Kstar : (0 : Real) ≤ _)
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,n,m,d), The normalized target's mean squared error about its raw mean has the roadmap bound.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_mean_sq_bound
lemma affine_normalized_target_mean_sq_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) (hyp : Bool) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := ∫ lat, affineRawTarget n m d eps sigma hyp lat ∂nu
    (∫ lat, (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t) ^ 2 ∂nu) ≤
      4 * ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 ^ 2 +
        8 * ((affineTuning n m d eps).Kstar : Real) *
          (affineTuning n m d eps).B * (affineTuning n m d eps).alpha := by
  intro nu t
  have hi : (∫ lat, (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t) ^ 2 ∂nu) ≤
      ∫ lat, 2 * (affineRawTarget n m d eps sigma hyp lat - t) ^ 2 +
        2 * (1 - rawNormalizer n m d eps sigma lat) ^ 2 ∂nu := by
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro lat
    exact affine_normalized_target_sq_error_bound n m d eps hn hd heps heps' sigma hyp lat t
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul] at hi
  have ht : (∫ lat, (affineRawTarget n m d eps sigma hyp lat - t) ^ 2 ∂nu) =
      variance (affineRawTarget n m d eps sigma hyp) nu := by
    rw [variance_eq_integral (by fun_prop)]
  have hQ : (∫ lat, (1 - rawNormalizer n m d eps sigma lat) ^ 2 ∂nu) =
      variance (rawNormalizer n m d eps sigma) nu := by
    rw [variance_eq_integral (by fun_prop), affine_raw_normalizer_mean]
    apply integral_congr_ae
    exact ae_of_all _ (fun lat => by ring)
  rw [ht, hQ] at hi
  have hv := affine_raw_target_variance_bound n m d eps hn hd heps heps' sigma hyp
  have hw := affine_raw_normalizer_variance_bound n m d eps hn hd heps heps' sigma
  change variance _ nu ≤ _ at hv hw
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,a,ha,n,m,d), Markov's inequality turns the normalized target MSE into a two-sided tail bound.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_tail_bound
lemma affine_normalized_target_tail_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (a : Real) (ha : 0 < a) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := ∫ lat, affineRawTarget n m d eps sigma hyp lat ∂nu
    nu.real {lat | a ≤ |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t|} ≤
      (4 * ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 ^ 2 +
        8 * ((affineTuning n m d eps).Kstar : Real) *
          (affineTuning n m d eps).B * (affineTuning n m d eps).alpha) / a ^ 2 := by
  intro nu t
  have h := mul_meas_ge_le_integral_of_nonneg (μ := nu)
    (f := fun lat => (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t) ^ 2)
    (ae_of_all _ (fun lat => sq_nonneg _)) Integrable.of_finite (a ^ 2)
  have hset : {lat | a ^ 2 ≤ (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t) ^ 2} =
      {lat | a ≤ |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t|} := by
    ext lat
    dsimp
    rw [← sq_abs (ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t)]
    exact sq_le_sq₀ ha.le (abs_nonneg _)
  rw [hset] at h
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  rw [mul_comm]
  exact h.trans (affine_normalized_target_mean_sq_bound n m d eps hn hd heps heps' sigma hyp)

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,sigma,hyp,m,d), The two affine target priors have the roadmap's gap-relative concentration bound.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_gap_tail
lemma affine_normalized_target_gap_tail (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) (hyp : Bool) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let gap := t true - t false
    nu.real {lat | gap / 8 ≤ |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t hyp|} ≤
      2 ^ 23 * (1 + eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2) /
        ((affineTuning n m d eps).Kstar : Real) := by
  intro nu t gap
  have hK : (0 : Real) < (affineTuning n m d eps).Kstar := by
    exact_mod_cast affine_tuning_Kstar_pos n m d eps hn hd heps heps' hS
  obtain ⟨_, _, _, _, _, _, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hg : ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 / 12 ≤ gap :=
    affine_raw_target_mean_gap n m d eps hn hd heps heps' sigma
  have hgp : 0 < gap := lt_of_lt_of_le (by positivity) hg
  have ht := affine_normalized_target_tail_bound n m d eps hn hd heps heps' sigma hyp
    (gap / 8) (by positivity)
  change nu.real _ ≤ _ at ht
  refine ht.trans ?_
  rw [show 8 * ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).B *
      (affineTuning n m d eps).alpha = 8 * ((affineTuning n m d eps).Kstar : Real) *
        ((affineTuning n m d eps).B * (affineTuning n m d eps).alpha) by ring,
    affine_tuning_B_alpha_identity n m d eps heps]
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < gap / 8))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hK).mpr
  have hs : (((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).b0 / 12) ^ 2 ≤
      gap ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
  have hz : 0 ≤ eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 ^ 23 * (1 + eps ^ 2 *
    ((affineTuning n m d eps).L : Real) ^ 2) by positivity)
  have hp : 0 ≤ (((affineTuning n m d eps).Kstar : Real) *
      (affineTuning n m d eps).b0) ^ 2 *
      (eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2) := by positivity
  nlinarith [sq_nonneg (((affineTuning n m d eps).Kstar : Real) *
    (affineTuning n m d eps).b0)]

end CausalSmith.Stat.AnnotationRarearmFrontier
