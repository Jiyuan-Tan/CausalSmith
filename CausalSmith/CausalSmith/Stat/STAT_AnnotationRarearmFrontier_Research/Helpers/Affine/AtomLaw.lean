module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Histogram
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Transfer

/-!
Exact raw atom intensities for the rare-cell and reservoir factors, and
identification of the normalized random-scale independent atom count laws.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,j,hj,n,m,d), The five independent coordinates of a rare cell have exactly the raw
complete and auxiliary atom intensities at its original label.  This gives [the stated result](goal).-/
-- @node: affineCellFullPoissonLaw_raw_atoms
lemma affineCellFullPoissonLaw_raw_atoms (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (hj : j.val < (affineTuning n m d eps).Kstar) :
    let t := affineTuning n m d eps
    let raw := rawTable hyp n m d eps sigma lat
    affineCellFullPoissonLaw sigma t.u t.w hyp (lat ⟨j.val, hj⟩) =
      ((poissonMeasure (Real.toNNReal (t.u * raw (j, true, true)))).prod
        (poissonMeasure (Real.toNNReal (t.u * raw (j, true, false))))).prod
      ((poissonMeasure (Real.toNNReal (t.w * ∑ y : Bool, raw (j, true, y)))).prod
        ((poissonMeasure (Real.toNNReal (t.u * raw (j, false, false)))).prod
          (poissonMeasure (Real.toNNReal (t.w * ∑ y : Bool, raw (j, false, y)))))) := by
  dsimp only
  have halpha : (affineTuning n m d eps).alpha =
      (affineTuning n m d eps).B / (100 * ((affineTuning n m d eps).L : Real) ^ 2) := rfl
  have hb0 : (affineTuning n m d eps).b0 =
      (affineTuning n m d eps).alpha / eps := rfl
  cases hlat : lat ⟨j.val, hj⟩ <;>
    simp [affineCellFullPoissonLaw, rawTable, hj, bernoulliMass,
      ← halpha, ← hb0, hlat, mul_assoc]
  congr 2
  congr 1
  congr 1
  ring

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,lat,j,hj,n,m,d), The independent reservoir coordinates have the same raw atom intensities
in both hypotheses, including the full auxiliary arm marginal.  This gives [the stated result](goal).-/
-- @node: affineReservoirCountLaw_raw_atoms
lemma affineReservoirCountLaw_raw_atoms (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
    (j : Fin d) (hj : j.val = (affineTuning n m d eps).Kstar) :
    let t := affineTuning n m d eps
    let raw := rawTable hyp n m d eps sigma lat
    affineReservoirCountLaw n m d eps sigma =
      ((poissonMeasure (Real.toNNReal (t.u * raw (j, true, false)))).prod
        (poissonMeasure (Real.toNNReal (t.u * raw (j, false, false))))).prod
      ((poissonMeasure (Real.toNNReal (t.w * ∑ y : Bool, raw (j, true, y)))).prod
        (poissonMeasure (Real.toNNReal (t.w * ∑ y : Bool, raw (j, false, y))))) := by
  dsimp only
  simp [affineReservoirCountLaw, rawTable, hj, bernoulliMass]

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hyp), Scaling the normalized complete atom law by its random total gives the
independent Poisson product at the original raw complete intensities.  This gives [the stated result](goal). -/
-- @node: affine_complete_countLaw_readback
lemma affine_complete_countLaw_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    independentPoissonCountLaw (normalizedLaw hyp n m d eps hd sigma lat).pmf.toMeasure
      (Real.toNNReal ((affineTuning n m d eps).u * rawNormalizer n m d eps sigma lat)) =
    Measure.pi (fun z : Obs d => poissonMeasure
      (Real.toNNReal ((affineTuning n m d eps).u * rawTable hyp n m d eps sigma lat z))) := by
  unfold independentPoissonCountLaw
  congr 1
  funext z
  congr 1
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply NNReal.eq
  rw [NNReal.coe_mul]
  have hQ := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hu : (affineTuning n m d eps).u = 128 * (n : Real) := rfl
  rw [Real.coe_toNNReal _ (by rw [hu]; positivity),
    Real.coe_toNNReal _ (mul_nonneg (by rw [hu]; positivity)
      (affine_rawTable_nonneg n m d eps hn hd heps heps' sigma hyp lat z))]
  exact affine_complete_intensity_readback n m d eps hn hd heps heps' sigma hyp lat z

/-- [Under the stated hypotheses](hyp:hn,hd,heps,heps',hyp), Scaling the normalized auxiliary law by the same total retains both arm
marginals and gives the independent Poisson product at their raw intensities.  This gives [the stated result](goal). -/
-- @node: affine_auxiliary_countLaw_readback
lemma affine_auxiliary_countLaw_readback (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    independentPoissonCountLaw (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat)).toMeasure
      (Real.toNNReal ((affineTuning n m d eps).w * rawNormalizer n m d eps sigma lat)) =
    Measure.pi (fun z : AuxObs d => poissonMeasure
      (Real.toNNReal ((affineTuning n m d eps).w *
        ∑ y : Bool, rawTable hyp n m d eps sigma lat (z.1, z.2, y)))) := by
  unfold independentPoissonCountLaw
  congr 1
  funext z
  congr 1
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply NNReal.eq
  rw [NNReal.coe_mul]
  have hQ := affine_rawNormalizer_pos n m d eps hn hd heps heps' sigma lat
  have hw : (affineTuning n m d eps).w = 128 * ((n : Real) + m) := rfl
  rw [Real.coe_toNNReal _ (by rw [hw]; positivity),
    Real.coe_toNNReal _ (mul_nonneg (by rw [hw]; positivity)
      (Finset.sum_nonneg fun y _ =>
        affine_rawTable_nonneg n m d eps hn hd heps heps' sigma hyp lat (z.1, z.2, y)))]
  exact affine_auxiliary_intensity_readback n m d eps hn hd heps heps' sigma hyp lat z

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,lat,n,m,d), Uniformly ordering the independent raw atom counts recovers the two
independent normalized iid Poisson channels at their actual random totals.  This gives [the stated result](goal).-/
-- @node: affine_raw_atom_counts_reconstruction
lemma affine_raw_atom_counts_reconstruction (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) :
    let t := affineTuning n m d eps
    let P := normalizedLaw hyp n m d eps hd sigma lat
    let Q := rawNormalizer n m d eps sigma lat
    let raw := rawTable hyp n m d eps sigma lat
    pairedHistogramReconstructionKernel (Obs d) (AuxObs d) ∘ₘ
      ((Measure.pi fun z : Obs d => poissonMeasure (Real.toNNReal (t.u * raw z))).prod
        (Measure.pi fun z : AuxObs d => poissonMeasure
          (Real.toNNReal (t.w * ∑ y : Bool, raw (z.1, z.2, y))))) =
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        P.pmf.toMeasure (Real.toNNReal (t.u * Q))).prod
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (auxMarginal P).toMeasure (Real.toNNReal (t.w * Q))) := by
  dsimp only
  rw [← affine_complete_countLaw_readback n m d eps hn hd heps heps' sigma hyp lat,
    ← affine_auxiliary_countLaw_readback n m d eps hn hd heps heps' sigma hyp lat]
  exact pairedIndependentPoissonCountLaw_comp_reconstruction _ _ _ _

end CausalSmith.Stat.AnnotationRarearmFrontier
