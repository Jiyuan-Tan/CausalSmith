module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalBlockCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.HistogramCellRepresentation

/-! # Histogram scores on flattened held-out blocks -/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The flat block height object](goal) is defined from [the supplied inputs](hyp:n,K,i,b,l,z). -/

noncomputable def flatBlockHeight {n K : ℕ} (i : Fin 7) (b : Fin 4) (l : Fin K)
    (z : (a : {a // a ∈ flatBlock n b}) → FlatObs n a.val) : ℝ :=
  if i = 0 then
    iidBlockHeight K (blockIdx n b) (targetCellScore K l)
      (fun r => flatReconstruct n b z (Sum.inr r))
  else
    iidBlockHeight K (blockIdx n b) (sourceCellScore i K l)
      (fun r => flatReconstruct n b z (Sum.inl r))
/-- Given [the supplied inputs](hyp:n,K,i,b,l), [the stated result about measurable flat block height holds](goal). -/

@[fun_prop]
lemma measurable_flatBlockHeight {n K : ℕ} (i : Fin 7) (b : Fin 4) (l : Fin K) :
    Measurable (flatBlockHeight (n := n) i b l) := by
  unfold flatBlockHeight iidBlockHeight
  split_ifs
  · fun_prop
  · fun_prop
/-- Given [the supplied inputs](hyp:n,K,hn,hK,x,i,b,l), [the stated result about flat block height proj holds](goal). -/

lemma flatBlockHeight_proj {n K : ℕ} (hn : threshold ≤ n) (hK : 0 < K)
    (x : (a : FlatIndex n) → FlatObs n a) (i : Fin 7) (b : Fin 4) (l : Fin K) :
    flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x) =
      markedHistogram (MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x)
        i K b (midpoint K l) := by
  by_cases hi : i = 0
  · subst i
    rw [markedHistogram_midpoint_target hn hK]
    simp only [flatBlockHeight, if_true]
    unfold iidBlockHeight
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    simp [flatReconstruct, inr_mem_flatBlock, hr,
      MeasurableEquiv.sumPiEquivProdPi, finsetCoordProj]
  · rw [markedHistogram_midpoint_source hn hK _ i hi]
    simp only [flatBlockHeight, if_neg hi]
    unfold iidBlockHeight
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    simp [flatReconstruct, inl_mem_flatBlock, hr,
      MeasurableEquiv.sumPiEquivProdPi, finsetCoordProj]
/-- Given [the supplied inputs](hyp:n,K,x,b,l), [the stated result about flat block height proj target holds](goal). -/


lemma flatBlockHeight_proj_target {n K : ℕ}
    (x : (a : FlatIndex n) → FlatObs n a) (b : Fin 4) (l : Fin K) :
    flatBlockHeight 0 b l (finsetCoordProj (flatBlock n b) x) =
      iidBlockHeight K (blockIdx n b) (targetCellScore K l)
        ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).2) := by
  simp only [flatBlockHeight, if_true]
  unfold iidBlockHeight
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp [flatReconstruct, inr_mem_flatBlock, hr, finsetCoordProj,
    MeasurableEquiv.sumPiEquivProdPi]
/-- Given [the supplied inputs](hyp:n,K,i,hi,x,b,l), [the stated result about flat block height proj source holds](goal). -/

lemma flatBlockHeight_proj_source {n K : ℕ} (i : Fin 7) (hi : i ≠ 0)
    (x : (a : FlatIndex n) → FlatObs n a) (b : Fin 4) (l : Fin K) :
    flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x) =
      iidBlockHeight K (blockIdx n b) (sourceCellScore i K l)
        ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).1) := by
  simp only [flatBlockHeight, if_neg hi]
  unfold iidBlockHeight
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp [flatReconstruct, inl_mem_flatBlock, hr, finsetCoordProj,
    MeasurableEquiv.sumPiEquivProdPi]
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,f,g,hf,hg), [the stated result about covariance flat law source holds](goal). -/


lemma covariance_flatLaw_source (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (f g : (Fin n → SourceObs) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    ProbabilityTheory.covariance
      (fun x : (a : FlatIndex n) → FlatObs n a =>
        f ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).1))
      (fun x => g ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).1))
      (Measure.pi (flatLaw P n)) =
      ProbabilityTheory.covariance f g
        (Measure.pi (fun _ : Fin n => sourceObsLaw P)) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P)
  let μT := Measure.pi (fun _ : Fin n => targetXLaw P)
  have hprod : ProbabilityTheory.covariance
      (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.1)
      (fun p => g p.1) (μS.prod μT) = ProbabilityTheory.covariance f g μS := by
    have h := covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
      measurable_fst.aemeasurable (μ := μS.prod μT)
    rw [measurePreserving_fst.map_eq] at h
    exact h.symm
  have hE := covariance_map_equiv
    (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.1)
    (fun p => g p.1) E (μ := Measure.pi (flatLaw P n))
  have hmap := (measurePreserving_sumPiEquivProdPi (flatLaw P n)).map_eq
  change ProbabilityTheory.covariance (fun x => f (E x).1) (fun x => g (E x).1)
    (Measure.pi (flatLaw P n)) = _
  rw [← hprod]
  have hE' := hE.symm
  rw [hmap] at hE'
  simpa [E, μS, μT, flatLaw, Function.comp_def] using hE' 
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,f,g,hf,hg), [the stated result about covariance flat law target holds](goal). -/


lemma covariance_flatLaw_target (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (f g : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    ProbabilityTheory.covariance
      (fun x : (a : FlatIndex n) → FlatObs n a =>
        f ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).2))
      (fun x => g ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).2))
      (Measure.pi (flatLaw P n)) =
      ProbabilityTheory.covariance f g
        (Measure.pi (fun _ : Fin n => targetXLaw P)) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P)
  let μT := Measure.pi (fun _ : Fin n => targetXLaw P)
  have hprod : ProbabilityTheory.covariance
      (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.2)
      (fun p => g p.2) (μS.prod μT) = ProbabilityTheory.covariance f g μT := by
    have h := covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
      measurable_snd.aemeasurable (μ := μS.prod μT)
    rw [measurePreserving_snd.map_eq] at h
    exact h.symm
  have hE := covariance_map_equiv
    (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.2)
    (fun p => g p.2) E (μ := Measure.pi (flatLaw P n))
  have hmap := (measurePreserving_sumPiEquivProdPi (flatLaw P n)).map_eq
  change ProbabilityTheory.covariance (fun x => f (E x).2) (fun x => g (E x).2)
    (Measure.pi (flatLaw P n)) = _
  rw [← hprod]
  have hE' := hE.symm
  rw [hmap] at hE'
  simpa [E, μS, μT, flatLaw, Function.comp_def] using hE'
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,f,g,hf,hg), [the stated result about covariance flat law source target zero holds](goal). -/

lemma covariance_flatLaw_source_target_zero (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (f : (Fin n → SourceObs) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin n => sourceObsLaw P)))
    (hg : MemLp g 2 (Measure.pi (fun _ : Fin n => targetXLaw P))) :
    ProbabilityTheory.covariance
      (fun x : (a : FlatIndex n) → FlatObs n a =>
        f ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).1))
      (fun x => g ((MeasurableEquiv.sumPiEquivProdPi (FlatObs n) x).2))
      (Measure.pi (flatLaw P n)) = 0 := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P)
  let μT := Measure.pi (fun _ : Fin n => targetXLaw P)
  have hprod : ProbabilityTheory.covariance
      (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.1)
      (fun p => g p.2) (μS.prod μT) = 0 :=
    covariance_fst_snd_prod hf hg
  have hE := covariance_map_equiv
    (fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.1)
    (fun p => g p.2) E (μ := Measure.pi (flatLaw P n))
  have hmap := (measurePreserving_sumPiEquivProdPi (flatLaw P n)).map_eq
  change ProbabilityTheory.covariance (fun x => f (E x).1) (fun x => g (E x).2)
    (Measure.pi (flatLaw P n)) = 0
  have hE' := hE.symm
  rw [hmap] at hE'
  have hE'' : ProbabilityTheory.covariance
      ((fun p : (Fin n → SourceObs) × (Fin n → ℝ) => f p.1) ∘ E)
      ((fun p => g p.2) ∘ E) (Measure.pi (flatLaw P n)) =
      ProbabilityTheory.covariance (fun p => f p.1) (fun p => g p.2) (μS.prod μT) := by
    simpa [μS, μT, flatLaw] using hE'
  rw [hprod] at hE''
  simpa [E, Function.comp_def] using hE''
/-- Given [the supplied inputs](hyp:n,K,i,b,l,z), [the stated result about flat block height nonneg holds](goal). -/

lemma flatBlockHeight_nonneg {n K : ℕ} (i : Fin 7) (b : Fin 4) (l : Fin K)
    (z : (a : {a // a ∈ flatBlock n b}) → FlatObs n a.val) :
    0 ≤ flatBlockHeight i b l z := by
  unfold flatBlockHeight iidBlockHeight
  split_ifs
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ =>
      (targetCellScore_mem_unit_interval K l _).1)
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ =>
      (sourceCellScore_mem_unit_interval i K l _).1)
/-- Given [the supplied inputs](hyp:n,K,b,hcard,i,l,z), [the stated result about flat block height le holds](goal). -/

lemma flatBlockHeight_le {n K : ℕ} (b : Fin 4) (hcard : 0 < (blockIdx n b).card)
    (i : Fin 7) (l : Fin K)
    (z : (a : {a // a ∈ flatBlock n b}) → FlatObs n a.val) :
    flatBlockHeight i b l z ≤ K := by
  have hsum_target : (∑ r ∈ blockIdx n b,
      targetCellScore K l (flatReconstruct n b z (Sum.inr r))) ≤
      (blockIdx n b).card := by
    simpa using Finset.sum_le_card_nsmul (blockIdx n b)
      (fun r => targetCellScore K l
        (flatReconstruct n b z (Sum.inr r))) 1
      (fun r _ => (targetCellScore_mem_unit_interval K l _).2)
  have hsum_source : (∑ r ∈ blockIdx n b,
      sourceCellScore i K l (flatReconstruct n b z (Sum.inl r))) ≤
      (blockIdx n b).card := by
    simpa using Finset.sum_le_card_nsmul (blockIdx n b)
      (fun r => sourceCellScore i K l
        (flatReconstruct n b z (Sum.inl r))) 1
      (fun r _ => (sourceCellScore_mem_unit_interval i K l _).2)
  unfold flatBlockHeight iidBlockHeight
  split_ifs
  · calc
      (K : ℝ) / (blockIdx n b).card * _ ≤
          (K : ℝ) / (blockIdx n b).card * (blockIdx n b).card :=
        mul_le_mul_of_nonneg_left hsum_target (by positivity)
      _ = K := by
        have hc : ((blockIdx n b).card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
        field_simp
  · calc
      (K : ℝ) / (blockIdx n b).card * _ ≤
          (K : ℝ) / (blockIdx n b).card * (blockIdx n b).card :=
        mul_le_mul_of_nonneg_left hsum_source (by positivity)
      _ = K := by
        have hc : ((blockIdx n b).card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
        field_simp
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,b,l), [the stated result about flat block height mem lp holds](goal). -/

lemma flatBlockHeight_memLp (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 7) (b : Fin 4) (l : Fin K) :
    MemLp (fun x : (a : FlatIndex n) → FlatObs n a =>
      flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x))
      2 (Measure.pi (flatLaw P n)) := by
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hcard : 0 < (blockIdx n b).card := by
    rw [block_card]
    have hlo := block_size_lower n hn b
    have hnpos : (0 : ℝ) < n := by
      norm_num [threshold] at hn
      exact_mod_cast (show 0 < n by omega)
    exact_mod_cast (lt_of_lt_of_le (div_pos hnpos (by norm_num)) hlo)
  apply MemLp.of_bound
    ((measurable_flatBlockHeight (n := n) i b l).comp
      (measurable_finsetCoordProj (flatBlock n b))).aestronglyMeasurable K
  filter_upwards [] with x
  change |flatBlockHeight (n := n) i b l (finsetCoordProj (flatBlock n b) x)| ≤ K
  rw [abs_of_nonneg (flatBlockHeight_nonneg i b l _)]
  exact flatBlockHeight_le b hcard i l _

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
