module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageProduct
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Original-record identification of stage products

At each fixed public seed, ancillary reconstruction identifies the paired adaptive
experiment with the original-record experiment. Consequently the structural stage
product represents the transcript law relative to its zero-contrast reference.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Integrating the independent reconstruction bits identifies the full transcript law at every fixed seed, including seeds of public-law measure zero](goal). -/
-- @node: conditionalTranscriptLaw_eq_paired
lemma conditionalTranscriptLaw_eq_paired (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (r : Q.Seed) :
    conditionalTranscriptLaw Q theta r =
      (Measure.pi (fun _ : Fin n => pairedLaw theta)).bind
        (fun a => fixedTranscriptLaw (averagedProtocol Q) a r) := by
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  ext E hE
  rw [conditionalTranscriptLaw, Measure.bind_apply hE
    (show Measurable (fun o => fixedTranscriptLaw Q o r) by fun_prop).aemeasurable,
    Measure.bind_apply hE
    (show Measurable (fun a => fixedTranscriptLaw (averagedProtocol Q) a r)
      by fun_prop).aemeasurable]
  rw [← symmetricLaw_iid_reconstruction theta htheta hd,
    lintegral_map (by fun_prop) (by fun_prop)]
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro a
  have h := averagedProtocol_fixedTranscript_lintegral Q a r
    (E.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hE)
  change (∫⁻ b, ∫⁻ z, E.indicator (fun _ => (1 : ℝ≥0∞)) z
      ∂fixedTranscriptLaw Q (fun i => recoverObs (a i) (b i)) r
      ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
    ∫⁻ z : ProtocolTranscript Q, E.indicator (fun _ => (1 : ℝ≥0∞)) z
      ∂fixedTranscriptLaw (averagedProtocol Q) a r at h
  simpa only [lintegral_indicator hE, lintegral_one, Measure.restrict_apply_univ] using h

/-- Assume [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hsum condition](hyp:hsum), and [the function hrep](hyp:hrep). [The uniform stage chain is the actual zero-contrast reference experiment](goal). -/
-- @node: stageReferenceTranscriptLaw_eq_reference
lemma stageReferenceTranscriptLaw_eq_reference (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hsum : ∀ i eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ))
    (hrep : ∀ (a : Fin n → PairedSymbol d),
      (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∏ i : Fin n,
          f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
        fixedTranscriptLaw (averagedProtocol Q) a r) :
    stageReferenceTranscriptLaw Q r = referenceLaw Q r := by
  rw [referenceLaw, conditionalTranscriptLaw_eq_paired Q _
    (by intro j; constructor <;> norm_num) hd r]
  exact stageReferenceTranscriptLaw_eq_zero_paired Q hd r f hf hf0 hsum hrep

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hsum condition](hyp:hsum), and [the function hrep](hyp:hrep). [The explicit affine stage product represents the original-record transcript law with the exact reference measure used by the derivative certificate](goal). -/
-- @node: originalTranscript_stageProduct_withDensity
lemma originalTranscript_stageProduct_withDensity (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hsum : ∀ i eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ))
    (hrep : ∀ (a : Fin n → PairedSymbol d),
      (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∏ i : Fin n,
          f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
        fixedTranscriptLaw (averagedProtocol Q) a r) :
    (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal
      (∏ i : Fin n, stageMixtureDensity theta
        (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)))) =
      conditionalTranscriptLaw Q theta r := by
  rw [← stageReferenceTranscriptLaw_eq_reference Q hd r f hf hf0 hsum hrep,
    conditionalTranscriptLaw_eq_paired Q theta htheta hd r]
  exact pairedTranscript_stageProduct_withDensity Q theta htheta hd r f hf hf0 hrep

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [Repaired protocol rows give the original experiment an explicit stage-product RN density, while retaining the row normalization and privacy needed by scores](goal). -/
-- @node: originalTranscript_stageProduct_of_gate
lemma originalTranscript_stageProduct_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      (∀ i, Measurable (f i)) ∧
      (∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps) ∧
      (∀ i r eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ)) ∧
      (∀ i a b r eta z,
        f i (((a,r),eta),z) ≤ Real.exp eps * f i (((b,r),eta),z)) ∧
      (∀ i a r eta, (stageReferenceKernel Q i (r,eta)).withDensity
        (fun z => ENNReal.ofReal (f i (((a,r),eta),z))) =
          averagedKernel Q i ((a,r),eta)) ∧
      (∀ r, stageReferenceTranscriptLaw Q r = referenceLaw Q r) ∧
      ∀ theta ∈ parameterCube d, ∀ r,
        (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal
          (∏ i : Fin n, stageMixtureDensity theta
            (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)))) =
          conditionalTranscriptLaw Q theta r := by
  obtain ⟨f, hf, hbound, hsum, hpriv, hrow, hfixed⟩ :=
    fixedPairedTranscript_product_density_of_gate hRN Q hd eps heps hQ
  have hf0 : ∀ i w, 0 ≤ f i w := fun i w =>
    le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1
  refine ⟨f, hf, hbound, hsum, hpriv, hrow, ?_, ?_⟩
  · intro r
    exact stageReferenceTranscriptLaw_eq_reference Q hd r f hf hf0
      (fun i eta z => hsum i r eta z) (fun a => hfixed a r)
  · intro theta htheta r
    exact originalTranscript_stageProduct_withDensity Q theta htheta hd r f hf hf0
      (fun i eta z => hsum i r eta z) (fun a => hfixed a r)

/-- [The affine product of the repaired rows is jointly measurable in the
parameter, public seed, and complete adaptive transcript](goal) when [every repaired row is measurable](hyp:hf). -/
-- @node: measurable_originalTranscript_stageProduct
@[fun_prop] lemma measurable_originalTranscript_stageProduct
    (Q : LocalProtocol n (ObsRecord d))
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun w : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q =>
      ∏ i : Fin n, stageMixtureDensity w.1
        (fun a => f i (((a,w.2.1),take (Nat.le_of_lt i.isLt) w.2.2),w.2.2 i))) := by
  apply Finset.measurable_prod
  intro i hi
  unfold stageMixtureDensity
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.mul
  · unfold stageInputWeight
    fun_prop
  · apply (hf i).comp
    apply Measurable.prodMk
    · apply Measurable.prodMk (by fun_prop)
      exact (measurable_restrictHistory _ _ _).comp (by fun_prop)
    · fun_prop

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [a nonnegative privacy budget](hyp:heps), [the stated hbound condition](hyp:hbound), and [the stated hpriv condition](hyp:hpriv). [Every score of the actual adaptive transcript has the sharp deterministic privacy bound, with a strictly positive denominator at all histories](goal). -/
-- @node: originalTranscript_stageScore_bound
lemma originalTranscript_stageScore_bound (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (eps : ℝ) (heps : 0 ≤ eps)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hbound : ∀ i w, Real.exp (-eps) ≤ f i w)
    (hpriv : ∀ i a b r eta z,
      f i (((a,r),eta),z) ≤ Real.exp eps * f i (((b,r),eta),z))
    (r : Q.Seed) (z : ProtocolTranscript Q) (i : Fin n) (j : Fin d) :
    let row := fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)
    0 < stageMixtureDensity theta row ∧
      |stageCoordinateSlope row j / stageMixtureDensity theta row| ≤
        derivativeScale d eps := by
  exact stageCoordinateScore_bound hd theta htheta _
    (fun a => lt_of_lt_of_le (Real.exp_pos _) (hbound i _))
    eps heps (fun a b => hpriv i a b r _ _) j

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [measurability of p](hyp:hp), [the protocol transcript](hyp:hp0), [the stated hp rep condition](hyp:hpRep), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hsum condition](hyp:hsum), and [the function hrep](hyp:hrep). [Any nonnegative measurable density certificate agrees almost everywhere with the explicit product. This applies to the existing canonical finite-sum version without selecting another whole-transcript Radon–Nikodym witness](goal). -/
-- @node: transcript_density_ae_eq_stageProduct
lemma transcript_density_ae_eq_stageProduct (Q : LocalProtocol n (ObsRecord d))
    (hd : 0 < d) (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (r : Q.Seed)
    (p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ)
    (hp : Measurable p) (hp0 : ∀ z, 0 ≤ p (theta,r,z))
    (hpRep : (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal (p (theta,r,z))) =
      conditionalTranscriptLaw Q theta r)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hsum : ∀ i eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ))
    (hrep : ∀ (a : Fin n → PairedSymbol d),
      (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∏ i : Fin n,
          f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
        fixedTranscriptLaw (averagedProtocol Q) a r) :
    (fun z => p (theta,r,z)) =ᵐ[referenceLaw Q r]
      (fun z => ∏ i : Fin n, stageMixtureDensity theta
        (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i))) := by
  haveI : IsProbabilityMeasure (referenceLaw Q r) := by
    exact conditionalTranscriptLaw_probability Q _
      (by intro j; constructor <;> norm_num) hd r
  have hprod := originalTranscript_stageProduct_withDensity Q theta htheta hd r
    f hf hf0 hsum hrep
  have hm := (measurable_originalTranscript_stageProduct Q f hf).comp
    (show Measurable (fun z : ProtocolTranscript Q => (theta,r,z)) by fun_prop)
  have heq := (withDensity_eq_iff_of_sigmaFinite
    ((hp.comp (by fun_prop)).ennreal_ofReal.aemeasurable)
    (hm.ennreal_ofReal.aemeasurable)).mp (hpRep.trans hprod.symm)
  filter_upwards [heq] with z hz
  have hnonneg : 0 ≤ ∏ i : Fin n, stageMixtureDensity theta
      (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)) := by
    apply Finset.prod_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (stageInputWeight_nonneg theta htheta a) (hf0 i _)
  exact (ENNReal.ofReal_eq_ofReal_iff (hp0 z) hnonneg).mp hz

end CausalSmith.Stat.LdpOptvalueUniformFrontier
