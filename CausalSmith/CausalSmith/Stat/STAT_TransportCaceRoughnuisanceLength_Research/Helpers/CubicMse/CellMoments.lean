module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Blocks
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockProduct
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport.AeRetraction

/-! # Product-law and bounded-mark facts for histogram cells -/

@[expose] public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional.Transport

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The three sampling assumptions identify the full observed-data law with
the product of the source and target iid laws.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
lemma dataLaw_eq_source_target_pi (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) :
    dataLaw P n n =
      (Measure.pi (fun _ : Fin n => sourceObsLaw P)).prod
        (Measure.pi (fun _ : Fin n => targetXLaw P)) := by
  rw [hP.independence, hP.sourceIid, hP.targetIid]

/-- A single dependent product carrier for the source and target arrays.  This
is the carrier expected by the conditional independence lemmas for coordinate
blocks.  For [the displayed assumptions and inputs](hyp:n), [the stated object is defined](goal). -/
abbrev FlatIndex (n : ℕ) := Sum (Fin n) (Fin n)
/-- [The flat obs object](goal) is defined from [the supplied inputs](hyp:n). -/

abbrev FlatObs (n : ℕ) : FlatIndex n → Type
  | .inl _ => SourceObs
  | .inr _ => ℝ
/-- [The flat obs measurable space object](goal) is defined from [the supplied inputs](hyp:n,i). -/

noncomputable instance flatObsMeasurableSpace (n : ℕ) (i : FlatIndex n) :
    MeasurableSpace (FlatObs n i) := by
  cases i <;> simp only [FlatObs] <;> infer_instance
/-- [The flat law object](goal) is defined from [the supplied inputs](hyp:P,n). -/

noncomputable def flatLaw (P : TransportLaw) (n : ℕ) :
    (i : FlatIndex n) → Measure (FlatObs n i)
  | .inl _ => sourceObsLaw P
  | .inr _ => targetXLaw P
/-- [The flatten sample object](goal) is defined from [the supplied inputs](hyp:n). -/

noncomputable abbrev flattenSample (n : ℕ) :
    TwoSample n n → (i : FlatIndex n) → FlatObs n i :=
  (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm

/-- The model assumptions identify the flattened sample with one dependent
`Measure.pi`.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
lemma map_flattenSample_dataLaw (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) :
    (dataLaw P n n).map (flattenSample n) = Measure.pi (flatLaw P n) := by
  letI : IsProbabilityMeasure P.assignedLaw := hP.randomized.1
  letI : IsFiniteMeasure (sourceObsLaw P) := by
    unfold sourceObsLaw
    infer_instance
  letI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  letI : IsFiniteMeasure (targetXLaw P) := by
    unfold targetXLaw populationLaw
    infer_instance
  letI : ∀ i, SigmaFinite (flatLaw P n i) := fun i => by
    cases i <;> simp only [flatLaw] <;> infer_instance
  rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
  exact (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
    (flatLaw P n)).map_eq
/-- [The flat block object](goal) is defined from [the supplied inputs](hyp:n,b). -/

def flatBlock (n : ℕ) (b : Fin 4) : Finset (FlatIndex n) :=
  (blockIdx n b).image Sum.inl ∪ (blockIdx n b).image Sum.inr
/-- Given [the supplied inputs](hyp:n,b,r), [the stated result about inl mem flat block holds](goal). -/

lemma inl_mem_flatBlock {n : ℕ} {b : Fin 4} (r : Fin n) :
    Sum.inl r ∈ flatBlock n b ↔ r ∈ blockIdx n b := by
  simp [flatBlock]
/-- Given [the supplied inputs](hyp:n,b,r), [the stated result about inr mem flat block holds](goal). -/

lemma inr_mem_flatBlock {n : ℕ} {b : Fin 4} (r : Fin n) :
    Sum.inr r ∈ flatBlock n b ↔ r ∈ blockIdx n b := by
  simp [flatBlock]
/-- Given [the supplied inputs](hyp:n,b,c,hbc), [the stated result about block idx disjoint holds](goal). -/

lemma blockIdx_disjoint {n : ℕ} {b c : Fin 4} (hbc : b ≠ c) :
    Disjoint (blockIdx n b) (blockIdx n c) := by
  rw [Finset.disjoint_left]
  intro r hrb hrc
  fin_cases b <;> fin_cases c <;> simp [blockIdx] at hrb hrc ⊢ <;> omega
/-- Given [the supplied inputs](hyp:n,b,c,hbc), [the stated result about flat block disjoint holds](goal). -/

lemma flatBlock_disjoint {n : ℕ} {b c : Fin 4} (hbc : b ≠ c) :
    Disjoint (flatBlock n b) (flatBlock n c) := by
  rw [Finset.disjoint_left]
  intro i hib hic
  cases i with
  | inl r =>
      rw [inl_mem_flatBlock] at hib hic
      exact Finset.disjoint_left.mp (blockIdx_disjoint hbc) hib hic
  | inr r =>
      rw [inr_mem_flatBlock] at hib hic
      exact Finset.disjoint_left.mp (blockIdx_disjoint hbc) hib hic
/-- Given [the supplied inputs](hyp:n,t), [the stated result about flat block training disjoint holds](goal). -/

lemma flatBlock_training_disjoint (n : ℕ) (t : Fin 3) :
    Disjoint (flatBlock n 0) (flatBlock n t.succ) :=
  flatBlock_disjoint (Fin.succ_ne_zero t).symm
/-- Given [the supplied inputs](hyp:n), [the stated result about flat block eval pairwise holds](goal). -/

lemma flatBlock_eval_pairwise (n : ℕ) :
    Pairwise (fun s t : Fin 3 => Disjoint (flatBlock n s.succ) (flatBlock n t.succ)) := by
  intro s t hst
  exact flatBlock_disjoint ((Fin.succ_injective 3).ne hst)
/-- [The flat mask object](goal) is defined from [the supplied inputs](hyp:n,b,x). -/

noncomputable def flatMask (n : ℕ) (b : Fin 4)
    (x : (i : FlatIndex n) → FlatObs n i) : (i : FlatIndex n) → FlatObs n i :=
  fun i => by
    classical
    cases i with
    | inl r => exact if Sum.inl r ∈ flatBlock n b then x (Sum.inl r) else (0, false, false, 0)
    | inr r => exact if Sum.inr r ∈ flatBlock n b then x (Sum.inr r) else 0
/-- Given [the supplied inputs](hyp:n,w), [the stated result about flatten sample training view holds](goal). -/

lemma flattenSample_trainingView {n : ℕ} (w : TwoSample n n) :
    flattenSample n (trainingView w) = flatMask n 0 (flattenSample n w) := by
  funext i
  cases i with
  | inl r =>
      simp [flattenSample, trainingView, flatMask, inl_mem_flatBlock,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  | inr r =>
      simp [flattenSample, trainingView, flatMask, inr_mem_flatBlock,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm]
/-- [The flat reconstruct object](goal) is defined from [the supplied inputs](hyp:n,b,z). -/

noncomputable def flatReconstruct (n : ℕ) (b : Fin 4)
    (z : (i : {i // i ∈ flatBlock n b}) → FlatObs n i.val) :
    (i : FlatIndex n) → FlatObs n i :=
  fun i => by
    classical
    by_cases hi : i ∈ flatBlock n b
    · exact z ⟨i, hi⟩
    · cases i with
      | inl _ => exact (0, false, false, 0)
      | inr _ => exact 0
/-- Given [the supplied inputs](hyp:n,b), [the stated result about measurable flat reconstruct holds](goal). -/

@[fun_prop]
lemma measurable_flatReconstruct (n : ℕ) (b : Fin 4) :
    Measurable (flatReconstruct n b) := by
  rw [measurable_pi_iff]
  intro i
  unfold flatReconstruct
  split_ifs with hi
  · exact measurable_pi_apply (⟨i, hi⟩ : {j // j ∈ flatBlock n b})
  · cases i <;> fun_prop
/-- Given [the supplied inputs](hyp:n,b,x), [the stated result about flat reconstruct proj eq mask holds](goal). -/

lemma flatReconstruct_proj_eq_mask (n : ℕ) (b : Fin 4)
    (x : (i : FlatIndex n) → FlatObs n i) :
    flatReconstruct n b (finsetCoordProj (flatBlock n b) x) = flatMask n b x := by
  funext i
  cases i with
  | inl r =>
      simp only [flatReconstruct, flatMask]
      split_ifs with hi <;> rfl
  | inr r =>
      simp only [flatReconstruct, flatMask]
      split_ifs with hi <;> rfl
/-- Given [the supplied inputs](hyp:n,b,x), [the stated result about proj flat mask eq proj holds](goal). -/

lemma proj_flatMask_eq_proj (n : ℕ) (b : Fin 4)
    (x : (i : FlatIndex n) → FlatObs n i) :
    finsetCoordProj (flatBlock n b) (flatMask n b x) =
      finsetCoordProj (flatBlock n b) x := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i <;> simp [finsetCoordProj, flatMask, hi]
/-- [The flat training proj object](goal) is defined from [the supplied inputs](hyp:n). -/

noncomputable abbrev flatTrainingProj (n : ℕ) :
    TwoSample n n → ((i : {i // i ∈ flatBlock n 0}) → FlatObs n i.val) :=
  fun w => finsetCoordProj (flatBlock n 0) (flattenSample n w)
/-- Given [the supplied inputs](hyp:n,w), [the stated result about flat training proj training view holds](goal). -/

lemma flatTrainingProj_trainingView {n : ℕ} (w : TwoSample n n) :
    flatTrainingProj n (trainingView w) = flatTrainingProj n w := by
  change finsetCoordProj (flatBlock n 0) (flattenSample n (trainingView w)) = _
  rw [flattenSample_trainingView, proj_flatMask_eq_proj]
/-- Given [the supplied inputs](hyp:n,w), [the stated result about training view eq unflatten reconstruct proj holds](goal). -/

lemma trainingView_eq_unflatten_reconstruct_proj {n : ℕ} (w : TwoSample n n) :
    trainingView w = (MeasurableEquiv.sumPiEquivProdPi (FlatObs n))
      (flatReconstruct n 0 (flatTrainingProj n w)) := by
  apply (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.injective
  rw [MeasurableEquiv.symm_apply_apply]
  change flattenSample n (trainingView w) = flatReconstruct n 0 (flatTrainingProj n w)
  rw [flattenSample_trainingView]
  exact (flatReconstruct_proj_eq_mask n 0 (flattenSample n w)).symm

/-- The paper's zero-filled training view generates the same sigma algebra as
the flattened finite-coordinate projection used by the conditional product
library.  Under [the displayed assumptions and inputs](hyp:n), [the stated conclusion holds](goal). -/
lemma trainingSigma_eq_comap_flatTrainingProj (n : ℕ) :
    trainingSigma n = MeasurableSpace.comap (flatTrainingProj n) inferInstance := by
  apply le_antisymm
  · apply Measurable.comap_le
    have hcomp := (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).measurable.comp
      ((measurable_flatReconstruct n 0).comp (comap_measurable (flatTrainingProj n)))
    convert hcomp using 1
    funext w
    exact trainingView_eq_unflatten_reconstruct_proj w
  · apply Measurable.comap_le
    have hcomp := (measurable_finsetCoordProj (flatBlock n 0)).comp
      ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable.comp
        (comap_measurable trainingView))
    convert hcomp using 1
    funext w
    exact (flatTrainingProj_trainingView w).symm

/-- The target marginal is a probability measure.  Positivity of the
conditioning event is forced by the strictly positive density lower envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
lemma targetXLaw_isProbabilityMeasure (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) : IsProbabilityMeasure (targetXLaw P) := by
  letI : IsProbabilityMeasure P.fullLaw := hP.sourceBounds.2.2.1
  have hc : 0 < c_f := hP.sourceBounds.1.1
  have htarget_univ : targetXLaw P Set.univ ≠ 0 := by
    rw [hP.targetBounds.1, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    apply ne_of_gt
    calc
      0 < ENNReal.ofReal c_f * volume covariateSpace := by
        rw [show volume covariateSpace = 1 by simp [covariateSpace]]
        simp [ENNReal.ofReal_pos.2 hc]
      _ = ∫⁻ _x, ENNReal.ofReal c_f ∂(volume.restrict covariateSpace) := by simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (P.fT x) ∂(volume.restrict covariateSpace) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (by simp [covariateSpace] :
          MeasurableSet covariateSpace)] with x hx
        exact ENNReal.ofReal_le_ofReal (hP.targetBounds.2.1 x hx).1
  have hevent : P.fullLaw {o | population o = false} ≠ 0 := by
    intro hevent_zero
    apply htarget_univ
    unfold targetXLaw populationLaw
    rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hevent_zero]
    simp
  letI : IsProbabilityMeasure (populationLaw P false) := by
    unfold populationLaw
    exact ProbabilityTheory.cond_isProbabilityMeasure hevent
  unfold targetXLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  unfold covariate
  fun_prop
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP), [the stated result about source obs law is probability measure holds](goal). -/

lemma sourceObsLaw_isProbabilityMeasure (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) : IsProbabilityMeasure (sourceObsLaw P) := by
  letI : IsProbabilityMeasure P.assignedLaw := hP.randomized.1
  unfold sourceObsLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  unfold observeSource covariate
  fun_prop
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,i), [the stated result about flat law is probability measure holds](goal). -/

lemma flatLaw_isProbabilityMeasure (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (i : FlatIndex n) :
    IsProbabilityMeasure (flatLaw P n i) := by
  cases i with
  | inl r =>
      simp only [flatLaw]
      exact sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  | inr r =>
      simp only [flatLaw]
      exact targetXLaw_isProbabilityMeasure c_f C_f L P n hP
/-- Given [the supplied inputs](hyp:K,l), [the stated result about measurable set cell holds](goal). -/

lemma measurableSet_cell (K : ℕ) (l : Fin K) : MeasurableSet (cell K l) := by
  unfold cell
  split_ifs <;> measurability
/-- Given [the supplied inputs](hyp:K,hK,l), [the stated result about cell subset covariate space holds](goal). -/

lemma cell_subset_covariateSpace {K : ℕ} (hK : 0 < K) (l : Fin K) :
    cell K l ⊆ covariateSpace := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  intro x hx
  unfold cell at hx
  unfold covariateSpace
  split_ifs at hx
  · constructor
    · exact le_trans (div_nonneg (by positivity) hKr.le) hx.1
    · exact hx.2
  · constructor
    · exact le_trans (div_nonneg (by positivity) hKr.le) hx.1
    · have hl : (l.val : ℝ) + 1 ≤ K := by exact_mod_cast l.isLt
      exact le_trans hx.2.le ((div_le_one hKr).2 hl)
/-- Given [the supplied inputs](hyp:K,hK,l), [the stated result about volume cell holds](goal). -/

lemma volume_cell {K : ℕ} (hK : 0 < K) (l : Fin K) :
    volume (cell K l) = ENNReal.ofReal (1 / (K : ℝ)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold cell
  split_ifs with hlast
  · have hlast' : (l.val : ℝ) + 1 = K := by exact_mod_cast hlast
    simp only [Real.volume_Icc]
    congr 1
    field_simp
    linarith
  · simp only [Real.volume_Ico]
    congr 1
    field_simp
    ring
/-- Given [the supplied inputs](hyp:K,hK,l,r,hlr), [the stated result about cell disjoint holds](goal). -/

lemma cell_disjoint {K : ℕ} (hK : 0 < K) {l r : Fin K} (hlr : l ≠ r) :
    Disjoint (cell K l) (cell K r) := by
  rw [Set.disjoint_left]
  intro x hxl hxr
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hlr) with hltr | hrtl
  · have hlnot : l.val + 1 ≠ K := by omega
    unfold cell at hxl hxr
    simp only [hlnot, if_false] at hxl
    split_ifs at hxr
    all_goals
      have hstep : (l.val : ℝ) + 1 ≤ r.val := by exact_mod_cast (show l.val + 1 ≤ r.val by omega)
      have hdiv : ((l.val : ℝ) + 1) / K ≤ (r.val : ℝ) / K :=
        (div_le_div_iff_of_pos_right hKr).2 hstep
      linarith [hxl.2, hxr.1, hdiv]
  · have hrnot : r.val + 1 ≠ K := by omega
    unfold cell at hxl hxr
    simp only [hrnot, if_false] at hxr
    split_ifs at hxl
    all_goals
      have hstep : (r.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (show r.val + 1 ≤ l.val by omega)
      have hdiv : ((r.val : ℝ) + 1) / K ≤ (l.val : ℝ) / K :=
        (div_le_div_iff_of_pos_right hKr).2 hstep
      linarith [hxr.2, hxl.1, hdiv]

/-- Either source or target covariate mass of one regular cell is at most
`C_f / K`.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l), [the stated conclusion holds](goal). -/
lemma target_cell_mass_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (l : Fin K) :
    (targetXLaw P (cell K l)).toReal ≤ C_f / K := by
  have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hmeas := measurableSet_cell K l
  rw [hP.targetBounds.1, withDensity_apply _ hmeas]
  have hmono : ∫⁻ x in cell K l, ENNReal.ofReal (P.fT x) ∂(volume.restrict covariateSpace) ≤
      ∫⁻ _x in cell K l, ENNReal.ofReal C_f ∂(volume.restrict covariateSpace) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact ENNReal.ofReal_le_ofReal
      (hP.targetBounds.2.1 x (cell_subset_covariateSpace hK l hx)).2
  have hsub := cell_subset_covariateSpace hK l
  have hrhs_top :
      ∫⁻ _x in cell K l, ENNReal.ofReal C_f ∂(volume.restrict covariateSpace) ≠ ⊤ := by
    rw [setLIntegral_const, Measure.restrict_apply hmeas,
      inter_eq_left.mpr hsub, volume_cell hK]
    finiteness
  apply le_trans (ENNReal.toReal_mono hrhs_top hmono)
  rw [setLIntegral_const, Measure.restrict_apply hmeas,
    inter_eq_left.mpr hsub, volume_cell hK]
  simp [ENNReal.toReal_mul, hC, div_eq_mul_inv]
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l), [the stated result about source cell mass le holds](goal). -/

lemma source_cell_mass_le (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (l : Fin K) :
    (sourceXLaw P (cell K l)).toReal ≤ C_f / K := by
  have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hmeas := measurableSet_cell K l
  rw [hP.sourceBounds.2.2.2.2.1, withDensity_apply _ hmeas]
  have hmono : ∫⁻ x in cell K l, ENNReal.ofReal (P.fS x) ∂(volume.restrict covariateSpace) ≤
      ∫⁻ _x in cell K l, ENNReal.ofReal C_f ∂(volume.restrict covariateSpace) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact ENNReal.ofReal_le_ofReal
      (hP.sourceBounds.2.2.2.2.2 x (cell_subset_covariateSpace hK l hx)).2
  have hsub := cell_subset_covariateSpace hK l
  have hrhs_top :
      ∫⁻ _x in cell K l, ENNReal.ofReal C_f ∂(volume.restrict covariateSpace) ≠ ⊤ := by
    rw [setLIntegral_const, Measure.restrict_apply hmeas,
      inter_eq_left.mpr hsub, volume_cell hK]
    finiteness
  apply le_trans (ENNReal.toReal_mono hrhs_top hmono)
  rw [setLIntegral_const, Measure.restrict_apply hmeas,
    inter_eq_left.mpr hsub, volume_cell hK]
  simp [ENNReal.toReal_mul, hC, div_eq_mul_inv]

/-- Conditional expectations given the paper's training view are the pullbacks
of conditional expectations given block zero in the flattened product
experiment.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,f,hf), [the stated conclusion holds](goal). -/
lemma condExp_comp_flattenSample (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n)
    (f : ((i : FlatIndex n) → FlatObs n i) → ℝ)
    (hf : Integrable f (Measure.pi (flatLaw P n))) :
    condExp (trainingSigma n) (dataLaw P n n) (f ∘ flattenSample n) =ᵐ[dataLaw P n n]
      (condExp
        (MeasurableSpace.comap
          (finsetCoordProj (flatBlock n 0)) inferInstance)
        (Measure.pi (flatLaw P n)) f) ∘ flattenSample n := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : ∀ i, IsProbabilityMeasure (flatLaw P n i) := fun i =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP i
  letI : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  have h := condExp_comp_of_map_eq (flattenSample n)
    (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable
    (map_flattenSample_dataLaw c_f C_f L P n hP)
    (MeasurableSpace.comap
      (finsetCoordProj (flatBlock n 0)) inferInstance)
    (Measurable.comap_le (measurable_finsetCoordProj (flatBlock n 0))) hf
  rw [trainingSigma_eq_comap_flatTrainingProj]
  change condExp
      (MeasurableSpace.comap
        (finsetCoordProj (flatBlock n 0) ∘ flattenSample n) inferInstance)
      (dataLaw P n n) (f ∘ flattenSample n) =ᵐ[dataLaw P n n] _
  simpa only [MeasurableSpace.comap_comp] using h
/-- Given [the supplied inputs](hyp:n,i,r), [the stated result about measurable channel x holds](goal). -/

@[fun_prop]
lemma measurable_channelX {n : ℕ} (i : Fin 7) (r : Fin n) :
    Measurable (fun ω : TwoSample n n => channelX ω i r) := by
  unfold channelX sourceChannel
  split_ifs <;> fun_prop
/-- Given [the supplied inputs](hyp:n,i,r), [the stated result about measurable channel mark holds](goal). -/

@[fun_prop]
lemma measurable_channelMark {n : ℕ} (i : Fin 7) (r : Fin n) :
    Measurable (fun ω : TwoSample n n => channelMark ω i r) := by
  fin_cases i <;> simp [channelMark] <;> fun_prop

/-- Every empirical channel mark is deterministically between zero and one.
The outcome channels are clipped in the statistic itself.  Under [the displayed assumptions and inputs](hyp:n,i,r), [the stated conclusion holds](goal). -/
lemma channelMark_mem_unit_interval {n : ℕ} (ω : TwoSample n n)
    (i : Fin 7) (r : Fin n) : channelMark ω i r ∈ Icc (0 : ℝ) 1 := by
  have hclip (y : ℝ) : max 0 (min 1 y) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  fin_cases i <;> simp [channelMark, boolReal, Set.mem_Icc] <;>
    split_ifs <;> simp_all [Set.mem_Icc, (hclip _).1, (hclip _).2]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
