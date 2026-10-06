module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawMass

/-!
Positivity and support of every normalized affine table under the common latent coupling.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,j,n,m,d,a,y), Every normalized affine atom is its raw mass divided by the common normalizer.  This gives [the stated result](goal).-/
-- @node: affine_jointMass_readback
lemma affine_jointMass_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (a y : Bool) :
    jointMass (normalizedLaw hyp n m d eps hd sigma lat) j a y =
      rawTable hyp n m d eps sigma lat (j, a, y) / rawNormalizer n m d eps sigma lat := by
  have hp := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hs := affine_rawTable_sum n m d eps hd heps sigma hyp lat
  dsimp only [jointMass, normalizedLaw]
  rw [affine_normalizedPMF_toReal _ _
    (affine_rawTable_nonneg n m d eps hn hd heps heps' sigma hyp lat)
    (by rw [hs]; linarith), hs]

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hyp), Summing the outcome marks leaves arm masses independent of the hypothesis.  This gives [the stated result](goal). -/
-- @node: affine_armMass_readback
lemma affine_armMass_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (a : Bool) :
    armMass (normalizedLaw hyp n m d eps hd sigma lat) j a =
      (if hj : j.val < (affineTuning n m d eps).Kstar then
        (if a then (affineTuning n m d eps).alpha + (1 - eps) * latentNode sigma (lat ⟨j.val, hj⟩)
         else (1 - eps) * (affineTuning n m d eps).b0 + eps * latentNode sigma (lat ⟨j.val, hj⟩))
       else if j.val = (affineTuning n m d eps).Kstar then
         (1 - ((affineTuning n m d eps).Kstar : Real) * latentMeanMass sigma) / 2
       else 0) / rawNormalizer n m d eps sigma lat := by
  dsimp only [armMass]
  simp_rw [affine_jointMass_readback n m d eps hn hd heps heps' sigma hyp lat]
  rw [← Finset.sum_div]
  congr 1
  by_cases hj : j.val < (affineTuning n m d eps).Kstar
  · cases a <;> simp [rawTable, hj, Fintype.sum_bool, bernoulliMass] <;> ring
  · by_cases hr : j.val = (affineTuning n m d eps).Kstar <;>
      simp [rawTable, hj, hr, Fintype.sum_bool, bernoulliMass]

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hyp), The normalized cell mass is the sum of its two normalized arm masses.  This gives [the stated result](goal). -/
-- @node: affine_cellMass_readback
lemma affine_cellMass_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) :
    cellMass (normalizedLaw hyp n m d eps hd sigma lat) j =
      (if hj : j.val < (affineTuning n m d eps).Kstar then
        (affineTuning n m d eps).b0 + latentNode sigma (lat ⟨j.val, hj⟩)
       else if j.val = (affineTuning n m d eps).Kstar then
         1 - ((affineTuning n m d eps).Kstar : Real) * latentMeanMass sigma
       else 0) / rawNormalizer n m d eps sigma lat := by
  have hab : (affineTuning n m d eps).alpha = eps * (affineTuning n m d eps).b0 := by
    dsimp only [affineTuning]; field_simp
  change (∑ a : Bool, armMass _ j a) = _
  simp_rw [affine_armMass_readback n m d eps hn hd heps heps' sigma hyp lat]
  rw [← Finset.sum_div]
  congr 1
  by_cases hj : j.val < (affineTuning n m d eps).Kstar
  · simp [hj, Fintype.sum_bool, hab]; ring
  · by_cases hr : j.val = (affineTuning n m d eps).Kstar <;>
      simp [hj, hr, Fintype.sum_bool] <;> ring

/--
[Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), [Reservoir and normalizer positivity, legal support, and pointwise common marginal are
derived](goal).
-/
-- @node: affine_support_and_normalizer
lemma affine_support_and_normalizer (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    1 / 2 < 1 - ((affineTuning n m d eps).Kstar : Real) * latentMeanMass sigma ∧
    ∀ lat, 1 / 2 < rawNormalizer n m d eps sigma lat ∧
      (∀ hyp, ModelClass d eps (normalizedLaw hyp n m d eps hd sigma lat)) ∧
      auxMarginal (normalizedLaw true n m d eps hd sigma lat) =
        auxMarginal (normalizedLaw false n m d eps hd sigma lat)  := by
  refine ⟨affine_reservoir_pos n m d eps hn hd heps heps' sigma, ?_⟩
  intro lat
  have hQ := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hQpos : 0 < rawNormalizer n m d eps sigma lat := by linarith
  obtain ⟨_, _, _, _, _, _, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  refine ⟨hQ, ?_, ?_⟩
  · intro hyp
    constructor
    intro j hjpos
    have hjne := ne_of_gt hjpos
    rw [propensity, if_neg hjne]
    rw [le_div_iff₀ hjpos, div_le_iff₀ hjpos]
    rw [affine_armMass_readback n m d eps hn hd heps heps' sigma hyp lat j true,
      affine_cellMass_readback n m d eps hn hd heps heps' sigma hyp lat j]
    have hab : (affineTuning n m d eps).alpha = eps * (affineTuning n m d eps).b0 := by
      dsimp only [affineTuning]; field_simp
    by_cases hj : j.val < (affineTuning n m d eps).Kstar
    · simp only [dif_pos hj, if_true, hab]
      have hv : 0 ≤ latentNode sigma (lat ⟨j.val, hj⟩) := by
        cases lat ⟨j.val, hj⟩ with
        | none => exact le_refl 0
        | some i => exact (sigma.mem i).1
      simp only [← mul_div_assoc]
      constructor <;> apply (div_le_div_iff_of_pos_right hQpos).mpr
      · nlinarith
      · nlinarith
    · simp only [dif_neg hj]
      by_cases hr : j.val = (affineTuning n m d eps).Kstar
      · simp only [if_pos hr]
        have hp := affine_reservoir_pos n m d eps hn hd heps heps' sigma
        simp only [← mul_div_assoc]
        constructor <;> apply (div_le_div_iff_of_pos_right hQpos).mpr <;> nlinarith
      · simp [hr]
  · apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff'
      ((auxMarginal _).apply_ne_top z) ((auxMarginal _).apply_ne_top z)).mp
    rcases z with ⟨j, a⟩
    rw [auxMarginal_toReal_armMass, auxMarginal_toReal_armMass,
      affine_armMass_readback n m d eps hn hd heps heps' sigma true lat,
      affine_armMass_readback n m d eps hn hd heps heps' sigma false lat]


end CausalSmith.Stat.AnnotationRarearmFrontier
