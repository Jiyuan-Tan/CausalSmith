import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic

/-!
Measurability and finite-partition adapters for transporting the full-data law to the observed
law and decomposing treatment arms into latent cells.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- The full-data treatment coordinate is measurable. -/
-- @node: measurable_fullData_T
lemma measurable_fullData_T {k dx dz : ℕ} :
    Measurable (fun w : FullData k dx dz => w.T) := by
  change Measurable (fun w : FullData k dx dz => (FullData.toCoordinates w).2.1)
  exact continuous_induced_dom.measurable.snd.fst

/-- The full-data latent coordinate is measurable. -/
-- @node: measurable_fullData_U
lemma measurable_fullData_U {k dx dz : ℕ} :
    Measurable (fun w : FullData k dx dz => w.U) := by
  change Measurable (fun w : FullData k dx dz => (FullData.toCoordinates w).1)
  exact continuous_induced_dom.measurable.fst

/-- The observed treatment coordinate is measurable. -/
-- @node: measurable_obs_T
lemma measurable_obs_T {dx dz : ℕ} : Measurable (fun o : Obs dx dz => o.T) := by
  change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).1)
  exact continuous_induced_dom.measurable.fst

/-- A latent class is a measurable full-data event. -/
-- @node: measurableSet_latentClass
lemma measurableSet_latentClass {k dx dz : ℕ} (u : Fin k) :
    MeasurableSet (latentClass (dx := dx) (dz := dz) u) := by
  exact measurable_fullData_U (measurableSet_singleton u)

/-- A latent-treatment cell is a measurable full-data event. -/
-- @node: measurableSet_latentCell
lemma measurableSet_latentCell {k dx dz : ℕ} (u : Fin k) (t : Bool) :
    MeasurableSet (latentCell (dx := dx) (dz := dz) u t) := by
  change MeasurableSet ({w : FullData k dx dz | w.U = u} ∩ {w | w.T = t})
  exact (measurable_fullData_U (measurableSet_singleton u)).inter
    (measurable_fullData_T (measurableSet_singleton t))

/-- A treatment arm is a measurable full-data event. -/
-- @node: measurableSet_fullDataArm
lemma measurableSet_fullDataArm {k dx dz : ℕ} (t : Bool) :
    MeasurableSet {w : FullData k dx dz | w.T = t} := by
  exact measurable_fullData_T (measurableSet_singleton t)

/-- A treatment arm is a measurable observed-data event. -/
-- @node: measurableSet_obsArm_generic
lemma measurableSet_obsArm_generic {dx dz : ℕ} (t : Bool) :
    MeasurableSet (obsArm (dx := dx) (dz := dz) t) := by
  exact measurable_obs_T (measurableSet_singleton t)

/-- The observed-law mass of an arm equals its full-data-law mass. -/
-- @node: obsLaw_real_obsArm
lemma obsLaw_real_obsArm {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    [IsProbabilityMeasure P] (t : Bool) :
    (obsLaw P).real (obsArm t) = P.real {w | w.T = t} := by
  rw [Measure.real, obsLaw,
    Measure.map_apply (obsMap_measurable k dx dz) (measurableSet_obsArm_generic t)]
  rfl

/-- Conditional means under the observed pushforward equal the corresponding full-data
conditional means on the pulled-back event. -/
-- @node: conditionalMean_obsLaw_eq_fullData
lemma conditionalMean_obsLaw_eq_fullData {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (A : Set (Obs dx dz)) (hA : MeasurableSet A)
    (f : Obs dx dz → ℝ) (hf : Measurable f) :
    conditionalMean (obsLaw P) A f =
      conditionalMean P (obsMap ⁻¹' A) (f ∘ obsMap) := by
  have hmap : (obsLaw P).restrict A =
      Measure.map obsMap (P.restrict (obsMap ⁻¹' A)) := by
    exact Measure.restrict_map (obsMap_measurable k dx dz) hA
  unfold conditionalMean
  rw [Measure.real, Measure.real, obsLaw,
    Measure.map_apply (obsMap_measurable k dx dz) hA]
  congr 1
  change (∫ x, f x ∂(obsLaw P).restrict A) =
    ∫ x, (f ∘ obsMap) x ∂P.restrict (obsMap ⁻¹' A)
  rw [hmap]
  exact integral_map (obsMap_measurable k dx dz).aemeasurable hf.aestronglyMeasurable

/-- The observed treatment arm pulls back to the matching full-data arm. -/
-- @node: obsMap_preimage_obsArm
lemma obsMap_preimage_obsArm {k dx dz : ℕ} (t : Bool) :
    @obsMap k dx dz ⁻¹' obsArm t = {w | w.T = t} := rfl

/-- An observed-arm conditional mean can be evaluated directly under the full-data law. -/
-- @node: conditionalMean_obsArm_eq_fullDataArm
lemma conditionalMean_obsArm_eq_fullDataArm {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (t : Bool) (f : Obs dx dz → ℝ) (hf : Measurable f) :
    conditionalMean (obsLaw P) (obsArm t) f =
      conditionalMean P {w | w.T = t} (f ∘ obsMap) := by
  simpa only [obsMap_preimage_obsArm] using
    conditionalMean_obsLaw_eq_fullData P (obsArm t) (measurableSet_obsArm_generic t) f hf

/-- A full-data treatment arm is the disjoint union of its finitely many latent cells. -/
-- @node: fullDataArm_eq_iUnion_latentCell
lemma fullDataArm_eq_iUnion_latentCell {k dx dz : ℕ} (t : Bool) :
    {w : FullData k dx dz | w.T = t} = ⋃ u : Fin k, latentCell u t := by
  ext w
  simp [latentCell]

/-- The real mass of an arm is the sum of the real masses of its latent cells. -/
-- @node: fullDataArm_real_eq_sum_latentCell
lemma fullDataArm_real_eq_sum_latentCell {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsFiniteMeasure P] (t : Bool) :
    P.real {w | w.T = t} = ∑ u : Fin k, P.real (latentCell u t) := by
  rw [fullDataArm_eq_iUnion_latentCell]
  apply measureReal_iUnion_fintype (h' := fun i => measure_ne_top P (latentCell i t))
  · intro u v huv
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro w hwu hwv
    exact huv (hwu.1.symm.trans hwv.1)
  · exact fun u => measurableSet_latentCell u t

/-- Joint latent-arm positivity yields the paper's quantitative marginal arm bound. -/
-- @node: arm_mass_lower_of_latentArmPositivity
lemma arm_mass_lower_of_latentArmPositivity {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpos : LatentArmPositivity (pi0 := pi0) P) (t : Bool) :
    k * pi0 ≤ P.real {w | w.T = t} := by
  rw [fullDataArm_real_eq_sum_latentCell]
  calc
    k * pi0 = ∑ _u : Fin k, pi0 := by simp
    _ ≤ ∑ u : Fin k, P.real (latentCell u t) :=
      Finset.sum_le_sum fun u _ => hpos u t

/-- Every latent-treatment cell has strictly positive mass under a positive margin. -/
-- @node: latentCell_pos_of_latentArmPositivity
lemma latentCell_pos_of_latentArmPositivity {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0) (hpos : LatentArmPositivity (pi0 := pi0) P)
    (u : Fin k) (t : Bool) : 0 < P (latentCell u t) := by
  have hr : 0 < P.real (latentCell u t) := lt_of_lt_of_le hpi (hpos u t)
  exact pos_iff_ne_zero.mpr fun hz => by simp [Measure.real, hz] at hr

/-- Every treatment arm has strictly positive mass under joint latent-arm positivity. -/
-- @node: fullDataArm_pos_of_latentArmPositivity
lemma fullDataArm_pos_of_latentArmPositivity {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 0 < k) (hpi : 0 < pi0) (hpos : LatentArmPositivity (pi0 := pi0) P)
    (t : Bool) : 0 < P {w | w.T = t} := by
  have hr : 0 < P.real {w | w.T = t} :=
    lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hk) hpi)
      (arm_mass_lower_of_latentArmPositivity P hpos t)
  exact pos_iff_ne_zero.mpr fun hz => by simp [Measure.real, hz] at hr

/-- Each normalized latent-arm weight retains the original joint-cell positivity margin. -/
-- @node: latentArmWeight_lower
lemma latentArmWeight_lower {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0) (hpos : LatentArmPositivity (pi0 := pi0) P)
    (u : Fin k) (t : Bool) : pi0 ≤ latentArmWeights P t u u := by
  have hcell : pi0 ≤ P.real (latentCell u t) := hpos u t
  have harmpos : 0 < P.real {w | w.T = t} := by
    have hsubset : latentCell u t ⊆ {w : FullData k dx dz | w.T = t} :=
      fun _ hw => hw.2
    exact lt_of_lt_of_le hpi (hcell.trans
      (measureReal_mono hsubset))
  have harmle : P.real {w : FullData k dx dz | w.T = t} ≤ 1 := measureReal_le_one
  rw [latentArmWeights, Matrix.diagonal_apply_eq]
  exact (le_div_iff₀ harmpos).2 (by
    calc
      pi0 * P.real {w : FullData k dx dz | w.T = t} ≤ pi0 * 1 :=
        mul_le_mul_of_nonneg_left harmle hpi.le
      _ = pi0 := mul_one _
      _ ≤ P.real (latentCell u t) := hcell)

/-- The diagonal matrix of normalized latent-arm weights is injective. -/
-- @node: latentArmWeights_injective
lemma latentArmWeights_injective {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0) (hpos : LatentArmPositivity (pi0 := pi0) P)
    (t : Bool) : Function.Injective (Matrix.toEuclideanLin (latentArmWeights P t)) := by
  intro x y hxy
  apply PiLp.ext
  intro u
  have hwu : latentArmWeights P t u u ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hpi (latentArmWeight_lower P hpi hpos u t))
  have hu := congrArg (fun z : Euc k => z u) hxy
  rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply] at hu
  have hu' : latentArmWeights P t u u * x u = latentArmWeights P t u u * y u := by
    simpa [latentArmWeights, Matrix.mulVec_diagonal] using hu
  exact mul_left_cancel₀ hwu hu'

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
