module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawMass
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawPoissonTV
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Main

/-!
Raw-to-normalized likelihood and intensity readback for both channels, and the
Poisson prefix-failure budgets for the random-scale two-channel transfer.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,z,n,m,d), [Normalized complete-record atom masses read back to raw masses divided by the shared Q](goal).
-/
-- @node: affine_normalized_mass_readback
lemma affine_normalized_mass_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (z : Obs d) :
    ((normalizedLaw hyp n m d eps hd sigma lat).pmf z).toReal =
      rawTable hyp n m d eps sigma lat z / rawNormalizer n m d eps sigma lat  := by
  have hsum := affine_rawTable_sum n m d eps hd heps sigma hyp lat
  have hpos : 0 < ∑ z : Obs d, rawTable hyp n m d eps sigma lat z := by
    rw [hsum]
    exact lt_trans (by norm_num) (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat)
  change (normalizedPMF (rawTable hyp n m d eps sigma lat) _ z).toReal = _
  rw [affine_normalizedPMF_toReal _ _
    (affine_rawTable_nonneg n m d eps hn hd heps heps' sigma hyp lat) hpos, hsum]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,z,n,m,d), The auxiliary channel retains the full arm marginal of the raw table, divided by Q.  This gives [the stated result](goal).-/
-- @node: affine_normalized_aux_mass_readback
lemma affine_normalized_aux_mass_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (z : AuxObs d) :
    (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat) z).toReal =
      (∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y)) /
        rawNormalizer n m d eps sigma lat := by
  rw [auxMarginal_toReal_armMass]
  unfold armMass jointMass
  simp_rw [affine_normalized_mass_readback n m d eps hn hd heps heps' sigma hyp lat]
  rw [Finset.sum_div]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,z,n,m,d), Multiplying the normalized complete-channel probabilities by the raw total
recovers every complete Poisson intensity exactly.  This gives [the stated result](goal).-/
-- @node: affine_complete_intensity_readback
lemma affine_complete_intensity_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (z : Obs d) :
    (affineTuning n m d eps).u * rawNormalizer n m d eps sigma lat *
      ((normalizedLaw hyp n m d eps hd sigma lat).pmf z).toReal =
        (affineTuning n m d eps).u * rawTable hyp n m d eps sigma lat z := by
  rw [affine_normalized_mass_readback n m d eps hn hd heps heps' sigma hyp lat]
  have hQ : rawNormalizer n m d eps sigma lat ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat))
  field_simp

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,z,n,m,d), The random-scale auxiliary pool has exactly the raw arm intensities, including all controls.  This gives [the stated result](goal).-/
-- @node: affine_auxiliary_intensity_readback
lemma affine_auxiliary_intensity_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (z : AuxObs d) :
    (affineTuning n m d eps).w * rawNormalizer n m d eps sigma lat *
      (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat) z).toReal =
        (affineTuning n m d eps).w * ∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y) := by
  rw [affine_normalized_aux_mass_readback n m d eps hn hd heps heps' sigma hyp lat]
  have hQ : rawNormalizer n m d eps sigma lat ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) (affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat))
  field_simp

/-- [Under the stated inputs and conditions](hyp:k,rate,hrate), A Poisson pool with mean at least 64 times the requested size has the
exponential prefix-failure bound in equation (12).  This gives [the stated result](goal).-/
-- @node: affine_poisson_prefix_tail
lemma affine_poisson_prefix_tail (k : Nat) (rate : NNReal)
    (hrate : 64 * (k : Real) ≤ (rate : Real)) :
    poissonMeasure rate (Set.Iio k) ≤ ENNReal.ofReal (Real.exp (-31 * (k : Real))) := by
  have hsub : Set.Iio k ⊆ {j : Nat | (j : Real) ≤ (4 * (k : Real)) / 4} := by
    intro j hj
    have hjk : (j : Real) ≤ k := by exact_mod_cast (show j ≤ k from hj.le)
    change (j : Real) ≤ (4 * (k : Real)) / 4
    linarith
  have htail := Causalean.Stat.Concentration.Poisson.poisson_pilot_lower_tail
    rate (4 * (k : Real))
  have hlog : Real.log (4 : Real) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 4)
    norm_num at h
    exact h
  have hexp : 4 * (k : Real) * Real.log 4 / 4 - 3 * (rate : Real) / 4 ≤
      -31 * (k : Real) := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : Real) ≤ k)
    nlinarith
  have hreal : (poissonMeasure rate).real (Set.Iio k) ≤ Real.exp (-31 * (k : Real)) :=
    (measureReal_mono hsub).trans (htail.trans (Real.exp_le_exp.mpr hexp))
  rw [← ENNReal.ofReal_toReal (measure_ne_top (poissonMeasure rate) (Set.Iio k))]
  exact ENNReal.ofReal_le_ofReal hreal

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,lat,n,m,d), The complete raw pool has the uniform exponential prefix budget, since Q exceeds one half.  This gives [the stated result](goal).-/
-- @node: affine_complete_prefix_tail
lemma affine_complete_prefix_tail (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    poissonMeasure (Real.toNNReal ((affineTuning n m d eps).u *
      rawNormalizer n m d eps sigma lat)) (Set.Iio n) ≤
        ENNReal.ofReal (Real.exp (-31 * (n : Real))) := by
  have hQ := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hu : (affineTuning n m d eps).u = 128 * (n : Real) := rfl
  apply affine_poisson_prefix_tail
  rw [Real.coe_toNNReal _ (by rw [hu]; positivity), hu]
  nlinarith [Nat.cast_nonneg n (α := Real)]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,lat,n,m,d), Retaining m auxiliary records costs at most the exponential budget calibrated to n+m.
When m is zero, monotonicity still applies to the empty failure event.  This gives [the stated result](goal).-/
-- @node: affine_auxiliary_prefix_tail
lemma affine_auxiliary_prefix_tail (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    poissonMeasure (Real.toNNReal ((affineTuning n m d eps).w *
      rawNormalizer n m d eps sigma lat)) (Set.Iio m) ≤
        ENNReal.ofReal (Real.exp (-31 * ((n : Real) + m))) := by
  have hQ := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hw : (affineTuning n m d eps).w = 128 * ((n : Real) + m) := rfl
  have hrate : 64 * ((n + m : Nat) : Real) ≤
      (Real.toNNReal ((affineTuning n m d eps).w *
        rawNormalizer n m d eps sigma lat) : Real) := by
    rw [Real.coe_toNNReal _ (by rw [hw]; positivity), hw, Nat.cast_add]
    nlinarith [Nat.cast_nonneg n (α := Real), Nat.cast_nonneg m (α := Real)]
  exact (measure_mono (show Set.Iio m ⊆ Set.Iio (n + m) by intro j hj; exact lt_of_lt_of_le hj (Nat.le_add_left m n))).trans
    (by simpa only [Nat.cast_add] using affine_poisson_prefix_tail (n + m) _ hrate)

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,lat,m), The sum of the two actual Poisson failure probabilities fits the gap budget
required by the fixed-size transfer.  This gives [the stated result](goal).-/
-- @node: affine_prefix_failure_sum_gap
lemma affine_prefix_failure_sum_gap (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    poissonMeasure (Real.toNNReal ((affineTuning n m d eps).u *
        rawNormalizer n m d eps sigma lat)) (Set.Iio n) +
      poissonMeasure (Real.toNNReal ((affineTuning n m d eps).w *
        rawNormalizer n m d eps sigma lat)) (Set.Iio m) ≤
      ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap
  have hxTail := affine_complete_prefix_tail n m d eps hn hd heps heps' sigma lat
  have hyTail := affine_auxiliary_prefix_tail n m d eps hn hd heps heps' sigma lat
  have hmono : Real.exp (-31 * ((n : Real) + m)) ≤ Real.exp (-31 * (n : Real)) := by
    apply Real.exp_le_exp.mpr
    linarith [Nat.cast_nonneg m (α := Real)]
  have hgap := affine_fixed_size_failure_gap n m d eps hn hd heps heps' hS hx sigma
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-31 * (n : Real))) +
        ENNReal.ofReal (Real.exp (-31 * (n : Real))) :=
      add_le_add hxTail (hyTail.trans (ENNReal.ofReal_le_ofReal hmono))
    _ = ENNReal.ofReal (2 * Real.exp (-31 * (n : Real))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hgap

end CausalSmith.Stat.AnnotationRarearmFrontier
