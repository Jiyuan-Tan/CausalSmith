module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredPairCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicDerivative
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotSampling
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotSecondMoment

/-! # Exact bridges from histogram residuals to centered block scores

This file identifies the abstract block-centering constants with the marked-density
cell averages used by the quadratic and cubic statistics.  It also records that
the clipped pilot and its Taylor coefficients are measurable with respect to the
training block.
-/

@[expose] public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The mean of every flattened held-out block height is the corresponding
marked-density cell average.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,l), [the stated conclusion holds](goal). -/
lemma integral_flatBlockHeight_eq_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 7) (b : Fin 4) (l : Fin K) :
    (∫ x, flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x)
      ∂Measure.pi (flatLaw P n)) =
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hcard : 0 < (blockIdx n b).card := by
    rw [block_card]
    exact blockSize_pos_of_threshold n hn b
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P)
  let μT := Measure.pi (fun _ : Fin n => targetXLaw P)
  by_cases hi : i = 0
  · subst i
    have hfun : (fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight 0 b l (finsetCoordProj (flatBlock n b) x)) =
        (fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (targetCellScore K l) p.2) ∘ E := by
      funext x
      exact flatBlockHeight_proj_target x b l
    rw [hfun]
    have hE := measurePreserving_sumPiEquivProdPi (flatLaw P n)
    have hg : AEStronglyMeasurable
        (fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (targetCellScore K l) p.2)
        ((Measure.pi (flatLaw P n)).map E) := by
      rw [hE.map_eq]
      exact (by unfold iidBlockHeight; fun_prop : Measurable _).aestronglyMeasurable
    have htransfer0 := (integral_map hE.measurable.aemeasurable hg).symm
    rw [hE.map_eq] at htransfer0
    have htransfer :
        (∫ x, ((fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (targetCellScore K l) p.2) ∘ E) x
            ∂Measure.pi (flatLaw P n)) =
        ∫ p, iidBlockHeight K (blockIdx n b) (targetCellScore K l) p.2
          ∂μS.prod μT := by
      simpa [E, μS, μT, flatLaw] using htransfer0
    rw [htransfer]
    have hsnd := measurePreserving_snd (μ := μS) (ν := μT)
    have hs : AEStronglyMeasurable
        (iidBlockHeight K (blockIdx n b) (targetCellScore K l))
        ((μS.prod μT).map Prod.snd) := by
      rw [hsnd.map_eq]
      fun_prop
    have htransfer' := (integral_map hsnd.measurable.aemeasurable hs).symm
    rw [hsnd.map_eq] at htransfer'
    rw [htransfer']
    simpa [μS, μT, markedDensityVector] using
      target_bin_height_mean_eq_cellAverage c_f C_f L P n K hP hK
        (blockIdx n b) hcard l
  · have hfun : (fun x : (a : FlatIndex n) → FlatObs n a =>
        flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x)) =
        (fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) p.1) ∘ E := by
      funext x
      exact flatBlockHeight_proj_source i hi x b l
    rw [hfun]
    have hE := measurePreserving_sumPiEquivProdPi (flatLaw P n)
    have hg : AEStronglyMeasurable
        (fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) p.1)
        ((Measure.pi (flatLaw P n)).map E) := by
      rw [hE.map_eq]
      exact (by unfold iidBlockHeight; fun_prop : Measurable _).aestronglyMeasurable
    have htransfer0 := (integral_map hE.measurable.aemeasurable hg).symm
    rw [hE.map_eq] at htransfer0
    have htransfer :
        (∫ x, ((fun p : (Fin n → SourceObs) × (Fin n → ℝ) =>
          iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) p.1) ∘ E) x
            ∂Measure.pi (flatLaw P n)) =
        ∫ p, iidBlockHeight K (blockIdx n b) (sourceCellScore i K l) p.1
          ∂μS.prod μT := by
      simpa [E, μS, μT, flatLaw] using htransfer0
    rw [htransfer]
    have hfst := measurePreserving_fst (μ := μS) (ν := μT)
    have hs : AEStronglyMeasurable
        (iidBlockHeight K (blockIdx n b) (sourceCellScore i K l))
        ((μS.prod μT).map Prod.fst) := by
      rw [hfst.map_eq]
      fun_prop
    have htransfer' := (integral_map hfst.measurable.aemeasurable hs).symm
    rw [hfst.map_eq] at htransfer'
    rw [htransfer']
    simpa [μS, μT] using
      source_bin_height_mean_eq_cellAverage c_f C_f L P n K hP hK
        (blockIdx n b) hcard l i hi

/-- At a cell midpoint, each exact histogram residual is its block-centered
score plus the training shift from the true cell average to the clipped pilot.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,l), [the stated conclusion holds](goal). -/
lemma residual_eq_flatCenteredCellScore_add_trainingShift
    (c_f C_f L : ℝ) (P : TransportLaw) {n K : ℕ}
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (ω : TwoSample n n) (i : Fin 7) (b : Fin 4) (l : Fin K) :
    residual c_f C_f ω i K b (midpoint K l) =
      flatCenteredCellScore P i b l
          (finsetCoordProj (flatBlock n b) (flattenSample n ω)) +
        (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
          pilot c_f C_f ω (midpoint K l) i) := by
  unfold residual flatCenteredCellScore
  rw [flatBlockHeight_proj hn hK,
    integral_flatBlockHeight_eq_cellAverage c_f C_f L P n K hn hP hK]
  simp only [flattenSample, MeasurableEquiv.apply_symm_apply]
  ring

/-- A training-block channel covariate is unchanged by the training view.  Under [the displayed assumptions and inputs](hyp:n,i,r,hr), [the stated conclusion holds](goal). -/
lemma channelX_trainingView {n : ℕ} (ω : TwoSample n n) (i : Fin 7)
    (r : Fin n) (hr : r ∈ blockIdx n 0) :
    channelX (trainingView ω) i r = channelX ω i r := by
  unfold channelX
  split_ifs <;> simp [trainingView, hr]

/-- A training-block channel mark is unchanged by the training view.  Under [the displayed assumptions and inputs](hyp:n,i,r,hr), [the stated conclusion holds](goal). -/
lemma channelMark_trainingView {n : ℕ} (ω : TwoSample n n) (i : Fin 7)
    (r : Fin n) (hr : r ∈ blockIdx n 0) :
    channelMark (trainingView ω) i r = channelMark ω i r := by
  simp [channelMark, trainingView, hr]

/-- The block-zero histogram only sees the training view.  Under [the displayed assumptions and inputs](hyp:n,i,K,x), [the stated conclusion holds](goal). -/
lemma markedHistogram_trainingView {n : ℕ} (ω : TwoSample n n)
    (i : Fin 7) (K : ℕ) (x : ℝ) :
    markedHistogram (trainingView ω) i K 0 x = markedHistogram ω i K 0 x := by
  unfold markedHistogram
  split_ifs with hn
  · rfl
  · apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [channelMark_trainingView ω i r hr, channelX_trainingView ω i r hr]
    · rfl

/-- The clipped pilot only sees the training view.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,x), [the stated conclusion holds](goal). -/
lemma pilot_trainingView (c_f C_f : ℝ) {n : ℕ} (ω : TwoSample n n)
    (x : ℝ) :
    pilot c_f C_f (trainingView ω) x = pilot c_f C_f ω x := by
  unfold pilot
  split_ifs
  · rfl
  · funext i
    rw [markedHistogram_trainingView]

/-- A fixed pilot coordinate is measurable in the full sample.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,x,i), [the stated conclusion holds](goal). -/
@[fun_prop]
lemma measurable_pilot_eval (c_f C_f : ℝ) {n : ℕ} (x : ℝ) (i : Fin 7) :
    Measurable (fun ω : TwoSample n n => pilot c_f C_f ω x i) := by
  by_cases hn : n < threshold
  · simp only [pilot, if_pos hn]
    fun_prop
  · simp only [pilot, if_neg hn]
    unfold clipChannel clip
    split_ifs <;>
      exact measurable_const.max (measurable_const.min
        (measurable_markedHistogram i (pilotResolution n) 0 x))

/-- A fixed pilot coordinate is strongly measurable with respect to the
training σ-algebra.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,x,i), [the stated conclusion holds](goal). -/
@[fun_prop]
lemma stronglyMeasurable_pilot_eval_trainingSigma
    (c_f C_f : ℝ) {n : ℕ} (x : ℝ) (i : Fin 7) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => pilot c_f C_f ω x i) := by
  have h : StronglyMeasurable[trainingSigma n]
      ((fun ω : TwoSample n n => pilot c_f C_f ω x i) ∘ trainingView) :=
    (measurable_pilot_eval c_f C_f (n := n) x i).stronglyMeasurable.comp_measurable
      (comap_measurable (trainingView (n := n)))
  convert h using 1
  funext ω
  exact (congrFun (pilot_trainingView c_f C_f ω x) i).symm

/-- At the clipped pilot, the second derivative coefficient equals its explicit
rational formula.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j), [the stated conclusion holds](goal). -/
lemma dPhi2_pilot_eq_explicit (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (A : Bool) (x : ℝ) (i j : Fin 7) (ω : TwoSample n n) :
    dPhi2 A (pilot c_f C_f ω x) i j =
      cubicRatioD2Apply 0 (if A then 4 else 6) 2 (basis i) (basis j)
          (pilot c_f C_f ω x) -
        cubicRatioD2Apply 0 (if A then 3 else 5) 1 (basis i) (basis j)
          (pilot c_f C_f ω x) := by
  have hv := pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x
  have hcf : 0 < c_f := hP.sourceBounds.1.1
  have h1 : pilot c_f C_f ω x 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.1.1)
  have h2 : pilot c_f C_f ω x 2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.2.1.1)
  unfold dPhi2
  exact iteratedFDeriv_two_Phi A (pilot c_f C_f ω x)
    (basis i) (basis j) h1 h2

/-- At the clipped pilot, the third derivative coefficient equals its explicit
rational formula.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j,k), [the stated conclusion holds](goal). -/
lemma dPhi3_pilot_eq_explicit (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (A : Bool) (x : ℝ) (i j k : Fin 7) (ω : TwoSample n n) :
    dPhi3 A (pilot c_f C_f ω x) i j k =
      cubicRatioD3Apply 0 (if A then 4 else 6) 2 (basis i) (basis j) (basis k)
          (pilot c_f C_f ω x) -
        cubicRatioD3Apply 0 (if A then 3 else 5) 1 (basis i) (basis j) (basis k)
          (pilot c_f C_f ω x) := by
  have hv := pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x
  have hcf : 0 < c_f := hP.sourceBounds.1.1
  have h1 : pilot c_f C_f ω x 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.1.1)
  have h2 : pilot c_f C_f ω x 2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.2.1.1)
  unfold dPhi3
  exact iteratedFDeriv_three_Phi A (pilot c_f C_f ω x)
    (basis i) (basis j) (basis k) h1 h2

/-- Every quadratic Taylor coefficient evaluated at the clipped pilot is
strongly measurable with respect to the training σ-algebra.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_dPhi2_pilot_trainingSigma
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) (x : ℝ) (i j : Fin 7) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => dPhi2 A (pilot c_f C_f ω x) i j) := by
  have hexplicit : StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n =>
        cubicRatioD2Apply 0 (if A then 4 else 6) 2 (basis i) (basis j)
            (pilot c_f C_f ω x) -
          cubicRatioD2Apply 0 (if A then 3 else 5) 1 (basis i) (basis j)
            (pilot c_f C_f ω x)) := by
    unfold cubicRatioD2Apply basis
    fun_prop
  convert hexplicit using 1
  funext ω
  exact dPhi2_pilot_eq_explicit c_f C_f L P n hn hP A x i j ω

/-- Every cubic Taylor coefficient evaluated at the clipped pilot is strongly
measurable with respect to the training σ-algebra.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j,k), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_dPhi3_pilot_trainingSigma
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) (x : ℝ) (i j k : Fin 7) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => dPhi3 A (pilot c_f C_f ω x) i j k) := by
  have hexplicit : StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n =>
        cubicRatioD3Apply 0 (if A then 4 else 6) 2 (basis i) (basis j) (basis k)
            (pilot c_f C_f ω x) -
          cubicRatioD3Apply 0 (if A then 3 else 5) 1 (basis i) (basis j) (basis k)
            (pilot c_f C_f ω x)) := by
    unfold cubicRatioD3Apply basis
    fun_prop
  convert hexplicit using 1
  funext ω
  exact dPhi3_pilot_eq_explicit c_f C_f L P n hn hP A x i j k ω

/-- The exact quadratic residual product, after removing its training-only
part, is the sum of its three nonempty centered subsets.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,j,l), [the stated conclusion holds](goal). -/
lemma quadratic_residual_three_subset_decomposition
    (c_f C_f L : ℝ) (P : TransportLaw) {n K : ℕ}
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (ω : TwoSample n n) (i j : Fin 7) (l : Fin K) :
    let Xi := flatCenteredCellScore P i 1 l
      (finsetCoordProj (flatBlock n 1) (flattenSample n ω))
    let Xj := flatCenteredCellScore P j 2 l
      (finsetCoordProj (flatBlock n 2) (flattenSample n ω))
    let si := cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
        pilot c_f C_f ω (midpoint K l) i
    let sj := cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
        pilot c_f C_f ω (midpoint K l) j
    residual c_f C_f ω i K 1 (midpoint K l) *
        residual c_f C_f ω j K 2 (midpoint K l) - si * sj =
      Xi * Xj + si * Xj + sj * Xi := by
  dsimp only
  rw [residual_eq_flatCenteredCellScore_add_trainingShift
      c_f C_f L P hn hP hK ω i 1 l,
    residual_eq_flatCenteredCellScore_add_trainingShift
      c_f C_f L P hn hP hK ω j 2 l]
  ring

/-- The exact cubic residual product, after removing its training-only part,
is the sum of its seven nonempty centered subsets.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,j,k,l), [the stated conclusion holds](goal). -/
lemma cubic_residual_seven_subset_decomposition
    (c_f C_f L : ℝ) (P : TransportLaw) {n K : ℕ}
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (ω : TwoSample n n) (i j k : Fin 7) (l : Fin K) :
    let Xi := flatCenteredCellScore P i 1 l
      (finsetCoordProj (flatBlock n 1) (flattenSample n ω))
    let Xj := flatCenteredCellScore P j 2 l
      (finsetCoordProj (flatBlock n 2) (flattenSample n ω))
    let Xk := flatCenteredCellScore P k 3 l
      (finsetCoordProj (flatBlock n 3) (flattenSample n ω))
    let si := cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
        pilot c_f C_f ω (midpoint K l) i
    let sj := cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
        pilot c_f C_f ω (midpoint K l) j
    let sk := cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y k) K l -
        pilot c_f C_f ω (midpoint K l) k
    residual c_f C_f ω i K 1 (midpoint K l) *
          residual c_f C_f ω j K 2 (midpoint K l) *
          residual c_f C_f ω k K 3 (midpoint K l) - si * sj * sk =
      Xi * Xj * Xk + si * Xj * Xk + sj * Xi * Xk + sk * Xi * Xj +
        si * sj * Xk + si * sk * Xj + sj * sk * Xi := by
  dsimp only
  rw [residual_eq_flatCenteredCellScore_add_trainingShift
      c_f C_f L P hn hP hK ω i 1 l,
    residual_eq_flatCenteredCellScore_add_trainingShift
      c_f C_f L P hn hP hK ω j 2 l,
    residual_eq_flatCenteredCellScore_add_trainingShift
      c_f C_f L P hn hP hK ω k 3 l]
  ring

/-- A single centered held-out cell score is square integrable under the
flattened product experiment.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,b,l), [the stated conclusion holds](goal). -/
lemma flatCenteredCellScore_comp_memLp (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 7) (b : Fin 4) (l : Fin K) :
    MemLp (fun x => flatCenteredCellScore P i b l
      (finsetCoordProj (flatBlock n b) x)) 2 (Measure.pi (flatLaw P n)) := by
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  exact (flatBlockHeight_memLp c_f C_f L P n K hn hP i b l).sub (memLp_const _)

/-- A product of centered scores from two distinct evaluation blocks is square
integrable under the flattened product experiment.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,b,hb,l), [the stated conclusion holds](goal). -/
lemma flatCenteredPairCell_memLp (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 2 → Fin 7) (b : Fin 2 → Fin 3) (hb : Function.Injective b)
    (l : Fin K) :
    MemLp (flatCenteredPairCell P i b l) 2 (Measure.pi (flatLaw P n)) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let μ := Measure.pi (flatLaw P n)
  let F (t : Fin 2) := flatCenteredCellScore P (n := n) (i t) (b t).succ l
  have hf (t : Fin 2) : Measurable (F t) :=
    (measurable_flatBlockHeight (i t) (b t).succ l).sub measurable_const
  have hflp (t : Fin 2) :
      MemLp (fun x => F t (finsetCoordProj (flatBlock n (b t).succ) x)) 2 μ :=
    flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP
      (i t) (b t).succ l
  have hdisj : Disjoint (flatBlock n (b 0).succ) (flatBlock n (b 1).succ) :=
    flatBlock_eval_pairwise n (hb.ne (by decide : (0 : Fin 2) ≠ 1))
  have hs := integrable_twoBlockProduct (flatLaw P n)
    (flatBlock n (b 0).succ) (flatBlock n (b 1).succ) hdisj
    (fun z => F 0 z ^ 2) (fun z => F 1 z ^ 2)
    ((hf 0).pow_const 2) ((hf 1).pow_const 2)
    ((hflp 0).integrable_sq) ((hflp 1).integrable_sq)
  apply (memLp_two_iff_integrable_sq ?_).mpr
  · simpa only [flatCenteredPairCell, Fin.prod_univ_two, mul_pow, F, μ] using hs
  · have hm : Measurable (fun x =>
        F 0 (finsetCoordProj (flatBlock n (b 0).succ) x) *
          F 1 (finsetCoordProj (flatBlock n (b 1).succ) x)) :=
      ((hf 0).comp (measurable_finsetCoordProj _)).mul
        ((hf 1).comp (measurable_finsetCoordProj _))
    have hmeas : Measurable
        (flatCenteredPairCell (n := n) P i b l :
          ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
      have heq : (flatCenteredPairCell (n := n) P i b l :
          ((a : FlatIndex n) → FlatObs n a) → ℝ) = fun x =>
          F 0 (finsetCoordProj (flatBlock n (b 0).succ) x) *
            F 1 (finsetCoordProj (flatBlock n (b 1).succ) x) := by
        funext x
        simp only [flatCenteredPairCell, Fin.prod_univ_two, F]
      rw [heq]
      exact hm
    exact hmeas.aestronglyMeasurable

/-- Unflattening the product experiment is measurable from the block-zero
sigma algebra to the paper's training sigma algebra.  Under [the displayed assumptions and inputs](hyp:n), [the stated conclusion holds](goal). -/
lemma measurable_unflattenSample_flatTraining (n : ℕ) :
    @Measurable ((a : FlatIndex n) → FlatObs n a) (TwoSample n n)
      (MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
      (trainingSigma n) (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)) := by
  rw [trainingSigma_eq_comap_flatTrainingProj]
  rw [measurable_iff_comap_le]
  rw [MeasurableSpace.comap_comp]
  have heq : flatTrainingProj n ∘ MeasurableEquiv.sumPiEquivProdPi (FlatObs n) =
      finsetCoordProj (flatBlock n 0) := by
    funext x
    simp only [flatTrainingProj, flattenSample, MeasurableEquiv.symm_apply_apply,
      Function.comp_apply]
  rw [heq]

/-- Pilot coordinates pulled back to the flattened experiment are measurable
with respect to block zero.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,x,i), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_pilot_eval_flatTraining
    (c_f C_f : ℝ) (n : ℕ) (x : ℝ) (i : Fin 7) :
    StronglyMeasurable[
      MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi]
      (fun z => pilot c_f C_f
        (MeasurableEquiv.sumPiEquivProdPi (FlatObs n) z) x i) :=
  (stronglyMeasurable_pilot_eval_trainingSigma c_f C_f x i).comp_measurable
    (measurable_unflattenSample_flatTraining n)

/-- Quadratic derivative coefficients pulled back to the flattened experiment
are measurable with respect to block zero.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_dPhi2_pilot_flatTraining
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) (x : ℝ) (i j : Fin 7) :
    StronglyMeasurable[
      MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi]
      (fun z => dPhi2 A (pilot c_f C_f
        (MeasurableEquiv.sumPiEquivProdPi (FlatObs n) z) x) i j) :=
  (stronglyMeasurable_dPhi2_pilot_trainingSigma c_f C_f L P n hn hP A x i j).comp_measurable
    (measurable_unflattenSample_flatTraining n)

/-- Cubic derivative coefficients pulled back to the flattened experiment are
measurable with respect to block zero.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i,j,k), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_dPhi3_pilot_flatTraining
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) (x : ℝ) (i j k : Fin 7) :
    StronglyMeasurable[
      MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi]
      (fun z => dPhi3 A (pilot c_f C_f
        (MeasurableEquiv.sumPiEquivProdPi (FlatObs n) z) x) i j k) :=
  (stronglyMeasurable_dPhi3_pilot_trainingSigma c_f C_f L P n hn hP A x i j k).comp_measurable
    (measurable_unflattenSample_flatTraining n)

/-- Every marked-density coordinate is nonnegative and bounded by the common
model envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,x,hx,i), [the stated conclusion holds](goal). -/
lemma markedDensityVector_mem_Icc_zero_Cf (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (x : ℝ) (hx : x ∈ covariateSpace) (i : Fin 7) :
    markedDensityVector c_f C_f L P n hP x i ∈ Icc 0 C_f := by
  have hv := markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx
  have hc : 0 < c_f := hP.sourceBounds.1.1
  have hC : 0 < C_f := lt_trans (by norm_num) hP.sourceBounds.2.1
  rcases hv with ⟨h0, h1, h2, hr⟩
  fin_cases i
  · simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨hc.le.trans h0.1, h0.2⟩)
  · simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨by linarith [h1.1], by linarith [h1.2]⟩)
  · simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨by linarith [h2.1], by linarith [h2.2]⟩)
  · have h := hr 3 (by norm_num); simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨h.1, by linarith [h.2]⟩)
  · have h := hr 4 (by norm_num); simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨h.1, by linarith [h.2]⟩)
  · have h := hr 5 (by norm_num); simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨h.1, by linarith [h.2]⟩)
  · have h := hr 6 (by norm_num); simpa using (show _ ∈ Icc (0 : ℝ) C_f from ⟨h.1, by linarith [h.2]⟩)

/-- A marked-density cell average has absolute value at most the common model
envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i), [the stated conclusion holds](goal). -/
lemma abs_cellAverage_markedDensityVector_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i : Fin 7) :
    |cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l| ≤ C_f := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hC : 0 ≤ C_f := (lt_trans (by norm_num) hP.sourceBounds.2.1).le
  have hmeas := measurableSet_cell K l
  have hfinite : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn
      (fun y => markedDensityVector c_f C_f L P n hP y i) (cell K l) :=
    ((markedDensityVector_continuousOn c_f C_f L P n hP i).integrableOn_Icc).mono_set
      (cell_subset_covariateSpace hK l)
  have hlo : 0 ≤ ∫ y in cell K l,
      markedDensityVector c_f C_f L P n hP y i :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem hmeas fun y hy =>
      (markedDensityVector_mem_Icc_zero_Cf c_f C_f L P n hP y
        (cell_subset_covariateSpace hK l hy) i).1)
  have hhi : (∫ y in cell K l,
      markedDensityVector c_f C_f L P n hP y i) ≤
      ∫ _y in cell K l, C_f :=
    integral_mono_ae hint (integrableOn_const hfinite)
      (ae_restrict_of_forall_mem hmeas fun y hy =>
        (markedDensityVector_mem_Icc_zero_Cf c_f C_f L P n hP y
          (cell_subset_covariateSpace hK l hy) i).2)
  have hreal : (volume.restrict (cell K l)).real univ = 1 / (K : ℝ) := by
    rw [Measure.real, Measure.restrict_apply_univ, volume_cell hK l,
      ENNReal.toReal_ofReal (by positivity)]
  rw [integral_const, hreal] at hhi
  simp only [smul_eq_mul] at hhi
  unfold cellAverage
  rw [abs_of_nonneg (mul_nonneg hKr.le hlo)]
  calc
    (K : ℝ) * ∫ y in cell K l,
        markedDensityVector c_f C_f L P n hP y i ≤
        (K : ℝ) * (C_f * (1 / (K : ℝ))) :=
      mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hhi) hKr.le
    _ = C_f := by field_simp

/-- The deterministic training shift in every residual is bounded by the
uniform envelope used by the variance constants.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,l,i), [the stated conclusion holds](goal). -/
lemma abs_trainingShift_le (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (ω : TwoSample n n) (l : Fin K) (i : Fin 7) :
    |cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
        pilot c_f C_f ω (midpoint K l) i| ≤ 2 * (1 + C_f) := by
  have hp := pilot_mem_clippingRectangle c_f C_f L P n hn hP ω (midpoint K l)
  have hc : 0 < c_f := hP.sourceBounds.1.1
  have hC : 0 < C_f := lt_trans (by norm_num) hP.sourceBounds.2.1
  have hpabs : |pilot c_f C_f ω (midpoint K l) i| ≤ C_f := by
    rcases hp with ⟨h0, h1, h2, hr⟩
    fin_cases i
    · change |pilot c_f C_f ω (midpoint K l) 0| ≤ C_f
      rw [abs_of_nonneg (hc.le.trans h0.1)]
      exact h0.2
    · change |pilot c_f C_f ω (midpoint K l) 1| ≤ C_f
      rw [abs_of_nonneg (by linarith [h1.1] : 0 ≤ pilot c_f C_f ω (midpoint K l) 1)]
      linarith [h1.2]
    · change |pilot c_f C_f ω (midpoint K l) 2| ≤ C_f
      rw [abs_of_nonneg (by linarith [h2.1] : 0 ≤ pilot c_f C_f ω (midpoint K l) 2)]
      linarith [h2.2]
    · change |pilot c_f C_f ω (midpoint K l) 3| ≤ C_f
      have h := hr 3 (by norm_num); rw [abs_of_nonneg h.1]; linarith [h.2]
    · change |pilot c_f C_f ω (midpoint K l) 4| ≤ C_f
      have h := hr 4 (by norm_num); rw [abs_of_nonneg h.1]; linarith [h.2]
    · change |pilot c_f C_f ω (midpoint K l) 5| ≤ C_f
      have h := hr 5 (by norm_num); rw [abs_of_nonneg h.1]; linarith [h.2]
    · change |pilot c_f C_f ω (midpoint K l) 6| ≤ C_f
      have h := hr 6 (by norm_num); rw [abs_of_nonneg h.1]; linarith [h.2]
  exact (abs_sub _ _).trans (by
    have ha := abs_cellAverage_markedDensityVector_le c_f C_f L P n K hP hK l i
    linarith)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
