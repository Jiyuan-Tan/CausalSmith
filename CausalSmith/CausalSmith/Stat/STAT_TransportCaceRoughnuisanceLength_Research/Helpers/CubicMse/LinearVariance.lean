module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.LinearCellVariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.VarianceAggregation

/-! # Conditional variance of the exact held-out linear correction

The exact observation statistic is represented by its centered pilot-cell
sum. Bounded training derivatives and the signed iid covariance bound give
roadmap (19), with the stated constant and no added assumptions.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Roadmap (19) for the actual linear correction, conditioned on the two
training blocks.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: linear_conditional_variance_with_memLp
lemma linear_conditional_variance_with_memLp (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    MemLp (fun ξ : TwoSample n n => linearTerm c_f C_f ξ A -
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ζ : TwoSample n n => linearTerm c_f C_f ζ A) ξ) 2
      (dataLaw P n n) ∧
    (∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
          (linearTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ : TwoSample n n => linearTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
        10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
          (n : ℝ) ^ (-1 : ℝ)) := by
  classical
  let K := pilotResolution n
  have hK : 0 < K := by
    dsimp [K, pilotResolution, dyadicResolution]
    split_ifs <;> positivity
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  have hembed : @MeasurableEmbedding
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) :=
    (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurableEmbedding
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let M := fourthDerivativeEnvelope c_f C_f
  let c (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    dPhi1 A (pilot c_f C_f (E z) (midpoint K l)) i
  let X (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    flatCenteredCellScore P i 1 l (finsetCoordProj (flatBlock n 1) z)
  let Y (i : Fin 7) (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ l : Fin K, c i l z * X i l z
  let Z (z : (a : FlatIndex n) → FlatObs n a) := ∑ i : Fin 7, Y i z
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hM : 0 ≤ M := by
    dsimp [M, fourthDerivativeEnvelope]
    have := hP.sourceBounds.1.1
    positivity
  have hcmeas (i : Fin 7) (l : Fin K) : StronglyMeasurable[m] (c i l) :=
    (stronglyMeasurable_dPhi1_pilot_trainingSigma c_f C_f L P n hn hP A
      (midpoint K l) i).comp_measurable (measurable_unflattenSample_flatTraining n)
  have hc (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :
      |c i l z| ≤ M :=
    dPhi1_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A _
      (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i
  have hXlp (i : Fin 7) (l : Fin K) : MemLp (X i l) 2 μ :=
    flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP i 1 l
  have hYlp (i : Fin 7) : MemLp (Y i) 2 μ := by
    have ht (l : Fin K) : MemLp (fun z => c i l z * X i l z) 2 μ := by
      apply (hXlp i l).of_le_mul (c := M)
        (((hcmeas i l).mono hm).aestronglyMeasurable.mul (hXlp i l).aestronglyMeasurable)
      filter_upwards [] with z
      simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul_of_nonneg_right (hc i l z) (abs_nonneg _)
    exact (memLp_finsetSum Finset.univ (fun l _ => ht l)).const_mul (K : ℝ)⁻¹
  have hZlp : MemLp Z 2 μ := memLp_finsetSum Finset.univ (fun i _ => hYlp i)
  have hYbound (i : Fin 7) : ∀ᵐ z ∂μ,
      condExp m μ (fun y => (Y i y) ^ 2) z ≤ 5 * M ^ 2 * (n : ℝ) ^ (-1 : ℝ) :=
    condExp_sq_bounded_linear_cellAverage_le c_f C_f L P n K hn hP hK i 0
      (c i) M hM (hcmeas i) (by filter_upwards [] with z; exact fun l => hc i l z)
  have hagg := @condExp_sq_finsetSum_le
    ((a : FlatIndex n) → FlatObs n a) (Fin 7) MeasurableSpace.pi μ m
    Finset.univ Y (5 * M ^ 2 * (n : ℝ) ^ (-1 : ℝ))
    (fun i _ => hYlp i) (fun i _ => hYbound i)
  have hflat : ∀ᵐ z ∂μ, condExp m μ (fun y => (Z y) ^ 2) z ≤
      10 * (7 : ℝ) ^ 2 * M ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by
    filter_upwards [hagg] with z hz
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
    change condExp m μ (fun y => (Z y) ^ 2) z ≤ _
    norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hz
    apply hz.trans
    have hb : 0 ≤ M ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by positivity
    nlinarith
  have hbridge : Z ∘ flattenSample n =ᵐ[dataLaw P n n]
      (fun ω => linearTerm c_f C_f ω A - linearProjectionMean c_f C_f L P n hP ω A) := by
    have hb := linearTerm_sub_projectionMean_eq_centered_cell_sum
      c_f C_f L P n K hn hP hK (dvd_refl _) A
    filter_upwards [hb] with ω hω
    dsimp [Z, Y, c, X, E, Function.comp_apply]
    simp only [flattenSample, MeasurableEquiv.apply_symm_apply]
    rw [← Finset.mul_sum]
    exact hω.symm
  have hmean := condExp_linearTerm_eq_linearProjectionMean c_f C_f L P n hn hP A
  have hsquare : (fun ξ =>
      (linearTerm c_f C_f ξ A - condExp (trainingSigma n) (dataLaw P n n)
        (fun ζ => linearTerm c_f C_f ζ A) ξ) ^ 2) =ᵐ[dataLaw P n n]
      (fun z => (Z z) ^ 2) ∘ flattenSample n := by
    filter_upwards [hbridge, hmean] with ξ hb hm
    simp only [Function.comp_apply] at hb ⊢
    rw [hm, hb]
  have houter := condExp_comp_flattenSample c_f C_f L P n hP
    (fun z => (Z z) ^ 2) hZlp.integrable_sq
  have hmap : @Measure.map _ _ _ MeasurableSpace.pi
      (flattenSample n) (dataLaw P n n) = μ :=
    map_flattenSample_dataLaw c_f C_f L P n hP
  have hpull : ∀ᵐ ω ∂dataLaw P n n,
      condExp m μ (fun y => (Z y) ^ 2) (flattenSample n ω) ≤
        10 * (7 : ℝ) ^ 2 * M ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by
    have hp : ∀ᵐ z ∂(@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)),
        @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m MeasurableSpace.pi _ _ μ
          (fun y => (Z y) ^ 2) z ≤
          10 * (7 : ℝ) ^ 2 * M ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by
      rw [hmap]
      exact hflat
    exact (@MeasurableEmbedding.ae_map_iff
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) hembed _ (dataLaw P n n)).mp hp
  have hcongr := condExp_congr_ae (m := trainingSigma n) hsquare
  constructor
  · letI : MeasurableSpace ((a : FlatIndex n) → FlatObs n a) := MeasurableSpace.pi
    have hlp : MemLp Z 2 (@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)) := by
      rw [hmap]
      exact hZlp
    have hp := hlp.comp_of_map (mβ := MeasurableSpace.pi) hembed.measurable.aemeasurable
    apply (memLp_congr_ae (show Z ∘ flattenSample n =ᵐ[dataLaw P n n] _ from ?_)).mp hp
    filter_upwards [hbridge, hmean] with ξ hb hm
    simp only [Function.comp_apply] at hb ⊢
    rw [hm]
    exact hb
  · filter_upwards [hcongr, houter, hpull] with ω hc ho hb
    rw [hc, ho]
    exact hb

/-- Roadmap (19) for the exact linear correction.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: linear_conditional_variance
lemma linear_conditional_variance (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
          (linearTerm c_f C_f ξ A -
            condExp (trainingSigma n) (dataLaw P n n)
              (fun ζ : TwoSample n n => linearTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
        10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
          (n : ℝ) ^ (-1 : ℝ) := by
  exact (linear_conditional_variance_with_memLp c_f C_f L P n hn hP A).2

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
