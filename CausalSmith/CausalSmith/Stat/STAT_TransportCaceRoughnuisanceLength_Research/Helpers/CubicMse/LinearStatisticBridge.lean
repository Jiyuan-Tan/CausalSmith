module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.LinearProjectionMean

/-! # Exact cell representation of the held-out linear statistic

The empirical linear correction and its pilot subtraction are represented on
the pilot partition. This connects the actual observation-level statistic to
the centered histogram scores used in the conditional moment arguments.
-/

public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- An arbitrary function of the pilot integrates exactly as a midpoint sum
on any refinement of the pilot partition.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hK,hdiv,g), [the stated conclusion holds](goal). -/
-- @node: integral_pilot_composition_eq_cell_sum
lemma integral_pilot_composition_eq_cell_sum (c_f C_f : ℝ) {n K : ℕ}
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (g : DensityVector → ℝ) :
    (∫ x in covariateSpace, g (pilot c_f C_f ω x)) =
      (K : ℝ)⁻¹ * ∑ l : Fin K, g (pilot c_f C_f ω (midpoint K l)) := by
  classical
  have heq (l : Fin K) : EqOn (fun x => g (pilot c_f C_f ω x))
      (fun _ => g (pilot c_f C_f ω (midpoint K l))) (cell K l) := by
    intro x hx
    dsimp only
    rw [pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hx]
  have hfinite (l : Fin K) : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  have hi (l : Fin K) : IntegrableOn (fun x => g (pilot c_f C_f ω x))
      (cell K l) :=
    (integrableOn_congr_fun (heq l) (measurableSet_cell K l)).2
      (integrableOn_const (hfinite l))
  rw [← iUnion_cell_eq_covariateSpace hK,
    integral_iUnion_fintype (fun l => measurableSet_cell K l)
      (fun l r hlr => cell_disjoint hK hlr) hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [setIntegral_congr_fun (measurableSet_cell K l) (heq l),
    setIntegral_const, Measure.real, volume_cell hK l,
    ENNReal.toReal_ofReal (by positivity)]
  simp [smul_eq_mul, one_div]

open Classical in
/-- A pilot coefficient at an observed covariate equals its unique cell
coefficient. The support condition is supplied by the model's covariate law.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hK,hdiv,g,x,hx), [the stated conclusion holds](goal). -/
-- @node: pilot_coefficient_eq_cell_indicator_sum
lemma pilot_coefficient_eq_cell_indicator_sum (c_f C_f : ℝ) {n K : ℕ}
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (g : DensityVector → ℝ) {x : ℝ} (hx : x ∈ covariateSpace) :
    g (pilot c_f C_f ω x) =
      ∑ l : Fin K, g (pilot c_f C_f ω (midpoint K l)) *
        (if x ∈ cell K l then 1 else 0) := by
  classical
  obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK x hx
  rw [Finset.sum_eq_single l]
  · rw [if_pos hl, mul_one,
      pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hl]
  · intro r _ hrl
    rw [if_neg (fun hr => Set.disjoint_left.mp (cell_disjoint hK hrl) hr hl),
      mul_zero]
  · exact fun h => (h (Finset.mem_univ l)).elim

/-- The observation-level marked average is exactly a weighted histogram
midpoint sum. This uses the actual block normalization, including unequal
block sizes, and holds whenever its observations lie in the covariate region.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hn,hK,hdiv,i,b,g,hsupport), [the stated conclusion holds](goal). -/
-- @node: marked_average_pilot_coefficient_eq_histogram_sum
lemma marked_average_pilot_coefficient_eq_histogram_sum (c_f C_f : ℝ)
    {n K : ℕ} (hn : threshold ≤ n) (hK : 0 < K)
    (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n) (i : Fin 7)
    (b : Fin 4) (g : DensityVector → ℝ)
    (hsupport : ∀ r ∈ blockIdx n b, channelX ω i r ∈ covariateSpace) :
    (1 / (blockSize n b : ℝ)) * ∑ r ∈ blockIdx n b,
      channelMark ω i r * g (pilot c_f C_f ω (channelX ω i r)) =
    (K : ℝ)⁻¹ * ∑ l : Fin K,
      g (pilot c_f C_f ω (midpoint K l)) *
        markedHistogram ω i K b (midpoint K l) := by
  classical
  have hh (l : Fin K) : markedHistogram ω i K b (midpoint K l) =
      (K : ℝ) / blockSize n b * ∑ r ∈ blockIdx n b,
        channelMark ω i r * (if channelX ω i r ∈ cell K l then 1 else 0) := by
    unfold markedHistogram
    simp only [if_neg (Nat.not_lt_of_ge hn)]
    rw [Finset.sum_eq_single l, if_pos (midpoint_mem_cell hK l)]
    · intro r _ hrl
      rw [if_neg (fun h => hrl ((midpoint_mem_cell_iff hK l r).mp h))]
    · exact fun h => (h (Finset.mem_univ l)).elim
  have heq : (∑ r ∈ blockIdx n b,
      channelMark ω i r * g (pilot c_f C_f ω (channelX ω i r))) =
      ∑ l : Fin K, g (pilot c_f C_f ω (midpoint K l)) *
        ∑ r ∈ blockIdx n b,
          channelMark ω i r * (if channelX ω i r ∈ cell K l then 1 else 0) := by
    have hrw : (∑ r ∈ blockIdx n b,
        channelMark ω i r * g (pilot c_f C_f ω (channelX ω i r))) =
        ∑ r ∈ blockIdx n b, channelMark ω i r *
          ∑ l : Fin K, g (pilot c_f C_f ω (midpoint K l)) *
            (if channelX ω i r ∈ cell K l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [pilot_coefficient_eq_cell_indicator_sum c_f C_f hK hdiv ω g (hsupport r hr)]
    rw [hrw]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq]
  simp_rw [hh]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

/-- On samples in the covariate support, the exact linear correction is the
cell sum of pilot coefficients times block-one histogram residuals.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hn,hK,hdiv,A,hsupport), [the stated conclusion holds](goal). -/
-- @node: linearTerm_eq_residual_cell_sum
lemma linearTerm_eq_residual_cell_sum (c_f C_f : ℝ) {n K : ℕ}
    (hn : threshold ≤ n) (hK : 0 < K) (hdiv : pilotResolution n ∣ K)
    (ω : TwoSample n n) (A : Bool)
    (hsupport : ∀ i r, r ∈ blockIdx n 1 → channelX ω i r ∈ covariateSpace) :
    linearTerm c_f C_f ω A =
      (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ l : Fin K,
        dPhi1 A (pilot c_f C_f ω (midpoint K l)) i *
          residual c_f C_f ω i K 1 (midpoint K l) := by
  classical
  unfold linearTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [marked_average_pilot_coefficient_eq_histogram_sum c_f C_f hn hK hdiv
    ω i 1 (fun v => dPhi1 A v i) (hsupport i)]
  have hp := integral_pilot_composition_eq_cell_sum c_f C_f hK hdiv ω
    (fun v => dPhi1 A v i * v i)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, show Icc (0 : ℝ) 1 = covariateSpace from rfl, hp,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  simp only [residual, mul_sub]

/-- Every recorded covariate lies in the covariate region almost surely under
the model's actual two-sample experiment. Both marginal density identities
are used, and no support hypothesis is added to the model.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
-- @node: ae_channelX_mem_covariateSpace
lemma ae_channelX_mem_covariateSpace (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hP : ModelClass c_f C_f L P n) :
    ∀ᵐ ω ∂dataLaw P n n, ∀ i r, channelX ω i r ∈ covariateSpace := by
  have hregion : MeasurableSet covariateSpace := measurableSet_Icc
  have hS : ∀ᵐ x ∂sourceXLaw P, x ∈ covariateSpace := by
    rw [hP.sourceBounds.2.2.2.2.1]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hregion)
  have hT : ∀ᵐ x ∂targetXLaw P, x ∈ covariateSpace := by
    rw [hP.targetBounds.1]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hregion)
  have hobs : ∀ᵐ o ∂sourceObsLaw P, o.1 ∈ covariateSpace :=
    (ae_map_iff (μ := sourceObsLaw P) measurable_fst.aemeasurable hregion).mp hS
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hsource : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => sourceObsLaw P),
      ∀ r, (z r).1 ∈ covariateSpace :=
    ae_all_iff.mpr (fun r =>
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => sourceObsLaw P) r).ae hobs)
  have htarget : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => targetXLaw P),
      ∀ r, z r ∈ covariateSpace :=
    ae_all_iff.mpr (fun r =>
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => targetXLaw P) r).ae hT)
  rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
  have hs := (measurePreserving_fst (μ := Measure.pi (fun _ : Fin n => sourceObsLaw P))
    (ν := Measure.pi (fun _ : Fin n => targetXLaw P))).quasiMeasurePreserving.ae hsource
  have ht := (measurePreserving_snd (μ := Measure.pi (fun _ : Fin n => sourceObsLaw P))
    (ν := Measure.pi (fun _ : Fin n => targetXLaw P))).quasiMeasurePreserving.ae htarget
  filter_upwards [hs, ht] with ω hs ht
  intro i r
  unfold channelX
  split_ifs
  · exact hs r
  · exact ht r

/-- The exact held-out linear statistic is almost surely a centered block-one
cell sum plus its spatial projected mean. This is the genuine statistic
bridge needed for its conditional mean and variance.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,hdiv,A), [the stated conclusion holds](goal). -/
-- @node: linearTerm_sub_projectionMean_eq_centered_cell_sum
lemma linearTerm_sub_projectionMean_eq_centered_cell_sum (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (hdiv : pilotResolution n ∣ K) (A : Bool) :
    (fun ω : TwoSample n n => linearTerm c_f C_f ω A -
      linearProjectionMean c_f C_f L P n hP ω A) =ᵐ[dataLaw P n n]
    (fun ω => (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ l : Fin K,
      dPhi1 A (pilot c_f C_f ω (midpoint K l)) i *
        flatCenteredCellScore P i 1 l
          (Causalean.Mathlib.Probability.Independence.finsetCoordProj
            (flatBlock n 1) (flattenSample n ω))) := by
  classical
  filter_upwards [ae_channelX_mem_covariateSpace c_f C_f L P n hP] with ω hω
  rw [linearTerm_eq_residual_cell_sum c_f C_f hn hK hdiv ω A
    (fun i r _ => hω i r),
    linearProjectionMean_eq_cell_sum c_f C_f L P n K hP hK hdiv ω A,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [residual_eq_flatCenteredCellScore_add_trainingShift c_f C_f L P hn hP hK]
  ring

/-- The first derivative uses the same explicit envelope as the higher
Taylor coefficients.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,hf,hF,A,v,hv,i), [the stated conclusion holds](goal). -/
-- @node: dPhi1_abs_le
lemma dPhi1_abs_le (c_f C_f : ℝ) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (A : Bool) (v : DensityVector)
    (hv : clippingRectangle c_f C_f v) (i : Fin 7) :
    |dPhi1 A v i| ≤ fourthDerivativeEnvelope c_f C_f := by
  have hb : coordinateBasis i = basis i := by
    funext j
    simp [coordinateBasis, basis, eq_comm]
  simpa only [dPhi1, iteratedFDeriv_one_apply, hb, Matrix.cons_val_zero] using
    Phi_first_derivative_abs_le_fourthDerivativeEnvelope c_f C_f hf hF A v hv i

/-- The held-out linear correction has exactly its spatial linear Taylor term
as conditional mean. Training coefficients pull out of the conditional
expectation, and the centered block-one histograms have mean zero.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: condExp_linearTerm_eq_linearProjectionMean
lemma condExp_linearTerm_eq_linearProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    condExp (trainingSigma n) (dataLaw P n n)
      (fun ω : TwoSample n n => linearTerm c_f C_f ω A) =ᵐ[dataLaw P n n]
      (fun ω => linearProjectionMean c_f C_f L P n hP ω A) := by
  classical
  let K := pilotResolution n
  have hK : 0 < K := by
    dsimp [K, pilotResolution, dyadicResolution]
    split_ifs <;> positivity
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  have hEembed : @MeasurableEmbedding
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) :=
    (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurableEmbedding
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let c (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    dPhi1 A (pilot c_f C_f (E z) (midpoint K l)) i
  let X (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    flatCenteredCellScore P i 1 l (finsetCoordProj (flatBlock n 1) z)
  let shift (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
      pilot c_f C_f (E z) (midpoint K l) i
  let Y (i : Fin 7) (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ l : Fin K, c i l z * X i l z
  let Z (z : (a : FlatIndex n) → FlatObs n a) := ∑ i : Fin 7, Y i z
  let G (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ l : Fin K, c i l z * shift i l z
  let F := Z + G
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hcmeas (i : Fin 7) (l : Fin K) : StronglyMeasurable[m] (c i l) :=
    (stronglyMeasurable_dPhi1_pilot_trainingSigma c_f C_f L P n hn hP A
      (midpoint K l) i).comp_measurable (measurable_unflattenSample_flatTraining n)
  have hsmeas (i : Fin 7) (l : Fin K) : StronglyMeasurable[m] (shift i l) :=
    stronglyMeasurable_const.sub
      (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) i)
  have hc (i : Fin 7) (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :
      |c i l z| ≤ fourthDerivativeEnvelope c_f C_f :=
    dPhi1_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A _
      (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i
  have hXlp (i : Fin 7) (l : Fin K) : MemLp (X i l) 2 μ :=
    flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP i 1 l
  have hprod (i : Fin 7) (l : Fin K) :
      Integrable (fun z => c i l z * X i l z) μ := by
    apply (hXlp i l).integrable (by norm_num) |>.bdd_mul
      ((hcmeas i l).mono hm).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs] using hc i l z
  have hYint (i : Fin 7) : Integrable (Y i) μ :=
    (integrable_finsetSum Finset.univ (fun l _ => hprod i l)).const_mul (K : ℝ)⁻¹
  have hYzero (i : Fin 7) : condExp m μ (Y i) =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
    exact @condExp_weighted_cellAverage_zero
      ((a : FlatIndex n) → FlatObs n a) MeasurableSpace.pi μ m K hm _
      (c i) (X i) (hcmeas i)
      (fun l => (hXlp i l).integrable (by norm_num)) (hprod i)
      (fun l => condExp_flatCenteredCellScore_zero c_f C_f L P n K hn hP i 0 l)
  have hZint : Integrable Z μ := integrable_finsetSum Finset.univ (fun i _ => hYint i)
  have hZzero : condExp m μ Z =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
    have hs := condExp_finsetSum (μ := μ) (s := Finset.univ) (f := Y)
      (fun i _ => hYint i) m
    filter_upwards [hs, ae_all_iff.mpr hYzero] with z hs hz
    simp only [Finset.sum_fn, Finset.sum_apply] at hs
    change condExp m μ (fun z => ∑ i : Fin 7, Y i z) z = 0
    rw [hs]
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero]
  have hGmeas : StronglyMeasurable[m] G := by
    simpa only [G, Finset.sum_apply, Pi.mul_apply] using
      ((Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun l _ =>
          (hcmeas i l).mul (hsmeas i l)).const_mul (K : ℝ)⁻¹)
  have hGint : Integrable G μ := by
    have ht (i : Fin 7) (l : Fin K) : Integrable (fun z => c i l z * shift i l z) μ := by
      apply Integrable.of_bound (((hcmeas i l).mul (hsmeas i l)).mono hm).aestronglyMeasurable
        (fourthDerivativeEnvelope c_f C_f * (2 * (1 + C_f)))
      filter_upwards [] with z
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      have hb := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
      exact mul_le_mul (hc i l z) hb (abs_nonneg _)
        (le_trans (abs_nonneg _) (hc i l z))
    exact (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun l _ => ht i l))).const_mul (K : ℝ)⁻¹
  have hFint : Integrable F μ := hZint.add hGint
  have hflat : condExp m μ F =ᵐ[μ] G :=
    @condExp_add_eq_shift_of_centered
      ((a : FlatIndex n) → FlatObs n a) MeasurableSpace.pi μ m hm _
      Z G hZint hGint hGmeas hZzero
  have hcompG : G ∘ flattenSample n =
      fun ω => linearProjectionMean c_f C_f L P n hP ω A := by
    funext ω
    rw [linearProjectionMean_eq_cell_sum c_f C_f L P n K hP hK (dvd_refl _)]
    simp [G, c, shift, E, Function.comp_apply]
  have hcompF : F ∘ flattenSample n =ᵐ[dataLaw P n n]
      (fun ω => linearTerm c_f C_f ω A) := by
    have hb := linearTerm_sub_projectionMean_eq_centered_cell_sum
      c_f C_f L P n K hn hP hK (dvd_refl _) A
    filter_upwards [hb] with ω hω
    have hg := congrFun hcompG ω
    dsimp [F, Function.comp_apply, Pi.add_apply]
    rw [show G (flattenSample n ω) = linearProjectionMean c_f C_f L P n hP ω A from hg]
    dsimp [Z, Y, c, X, E]
    simp only [flattenSample, MeasurableEquiv.apply_symm_apply]
    rw [← Finset.mul_sum]
    linear_combination -hω
  have hpull := condExp_comp_flattenSample c_f C_f L P n hP F hFint
  have hflat_pull : ∀ᵐ ω ∂dataLaw P n n,
      @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m MeasurableSpace.pi _ _ μ F
        (flattenSample n ω) = G (flattenSample n ω) := by
    have hmap : @Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n) = μ :=
      map_flattenSample_dataLaw c_f C_f L P n hP
    have hp : ∀ᵐ z ∂(@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)),
        @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m MeasurableSpace.pi _ _ μ F z = G z := by
      rw [hmap]
      exact hflat
    exact (@MeasurableEmbedding.ae_map_iff
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n)
      hEembed
      (fun z => @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
        MeasurableSpace.pi _ _ μ F z = G z) (dataLaw P n n)).mp hp
  have hcongr := condExp_congr_ae (m := trainingSigma n) hcompF
  filter_upwards [hpull, hflat_pull, hcongr] with ω hp hf hc
  rw [← hc, hp]
  exact hf.trans (congrFun hcompG ω)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
