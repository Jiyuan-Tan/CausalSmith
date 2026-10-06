module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.MarkedCellCovariance

/-! # Covariance of iid block histogram heights -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.Independence

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The iid block height object](goal) is defined from [the supplied inputs](hyp:Ω,n,K,S,f,x). -/

noncomputable def iidBlockHeight {Ω : Type*} {n : ℕ} (K : ℕ)
    (S : Finset (Fin n)) (f : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (K : ℝ) / S.card * ∑ r ∈ S, f (x r)
/-- Given [the supplied inputs](hyp:Ω,n,K,S,hS,f,g,hfmeas,hgmeas,hf,hg), [the stated result about covariance iid block height holds](goal). -/

lemma covariance_iidBlockHeight
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n K : ℕ}
    (S : Finset (Fin n)) (hS : 0 < S.card) (f g : Ω → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    cov[iidBlockHeight K S f, iidBlockHeight K S g;
      Measure.pi (fun _ : Fin n => μ)] =
      (K : ℝ) ^ 2 / S.card * cov[f, g; μ] := by
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let X : Fin n → (Fin n → Ω) → ℝ := fun r x => f (x r)
  let Y : Fin n → (Fin n → Ω) → ℝ := fun r x => g (x r)
  have hX (r : Fin n) : MemLp (X r) 2 ν := by
    exact hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) r)
  have hY (r : Fin n) : MemLp (Y r) 2 ν := by
    exact hg.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) r)
  have hcoord (r s : Fin n) : cov[X r, Y s; ν] =
      if r = s then cov[f, g; μ] else 0 := by
    by_cases hrs : r = s
    · subst s
      simp only [if_pos rfl]
      have hpres := measurePreserving_eval (fun _ : Fin n => μ) r
      have hfmap : AEStronglyMeasurable f (ν.map (Function.eval r)) := by
        rw [hpres.map_eq]
        exact hf.aestronglyMeasurable
      have hgmap : AEStronglyMeasurable g (ν.map (Function.eval r)) := by
        rw [hpres.map_eq]
        exact hg.aestronglyMeasurable
      have hmap := covariance_map hfmap hgmap hpres.measurable.aemeasurable
      rw [hpres.map_eq] at hmap
      exact hmap.symm
    · simp only [if_neg hrs]
      have hind := indepFun_pi_of_disjoint (Ω := fun _ : Fin n => Ω)
        (fun _ : Fin n => μ) (show Disjoint ({r} : Finset (Fin n)) {s} by simpa)
      have hind' : IndepFun (X r) (Y s) ν := by
        have hcomp := hind.comp
          (hfmeas.comp (measurable_pi_apply
            (⟨r, Finset.mem_singleton_self r⟩ : {i // i ∈ ({r} : Finset (Fin n))})))
          (hgmeas.comp (measurable_pi_apply
            (⟨s, Finset.mem_singleton_self s⟩ : {i // i ∈ ({s} : Finset (Fin n))})))
        have hF : (Fintype.ofFinite (Fin n)) = (inferInstance : Fintype (Fin n)) :=
          Subsingleton.elim _ _
        have hpi : @Measure.pi (Fin n) (fun _ => Ω) (Fintype.ofFinite (Fin n))
            (fun _ => inferInstance) (fun _ => μ) = Measure.pi (fun _ : Fin n => μ) :=
          congrArg (fun fi : Fintype (Fin n) =>
            @Measure.pi (Fin n) (fun _ => Ω) fi (fun _ => inferInstance) (fun _ => μ)) hF
        simpa only [hpi, ν, X, Y, finsetCoordProj, Function.comp_def] using hcomp
      exact hind'.covariance_eq_zero (hX r) (hY s)
  have hsum : cov[(fun x => ∑ r ∈ S, X r x), (fun x => ∑ s ∈ S, Y s x); ν] =
      S.card * cov[f, g; μ] := by
    rw [covariance_fun_sum_fun_sum'
      (fun r _ => hX r) (fun s _ => hY s)]
    simp_rw [hcoord]
    calc
      ∑ r ∈ S, ∑ s ∈ S, (if r = s then cov[f, g; μ] else 0) =
          ∑ r ∈ S, cov[f, g; μ] := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [eq_comm, hr]
      _ = (S.card : ℝ) * cov[f, g; μ] := by simp
  change cov[(fun x => ((K : ℝ) / S.card) * (∑ r ∈ S, X r x)),
    (fun x => ((K : ℝ) / S.card) * (∑ s ∈ S, Y s x)); ν] = _
  rw [covariance_const_mul_left, covariance_const_mul_right, hsum]
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,i,j), [the stated result about source iid block height same cell covariance le holds](goal). -/

lemma source_iidBlockHeight_same_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (S : Finset (Fin n)) (hS : 0 < S.card) (l : Fin K) (i j : Fin 7) :
    |cov[iidBlockHeight K S (sourceCellScore i K l),
      iidBlockHeight K S (sourceCellScore j K l);
      Measure.pi (fun _ : Fin n => sourceObsLaw P)]| ≤
      ((K : ℝ) * C_f + C_f ^ 2) / S.card := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hfi := memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore i K l) (sourceCellScore_mem_unit_interval i K l)
  have hfj := memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore j K l) (sourceCellScore_mem_unit_interval j K l)
  rw [covariance_iidBlockHeight S hS _ _
    (measurable_sourceCellScore i K l) (measurable_sourceCellScore j K l) hfi hfj,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg (K : ℝ)) (by positivity))]
  have hsingle := source_same_cell_covariance_le c_f C_f L P n K hP hK l i j
  apply le_trans (mul_le_mul_of_nonneg_left hsingle
    (div_nonneg (sq_nonneg (K : ℝ)) (by positivity)))
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hSr : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  exact le_rfl
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,r,hlr,i,j), [the stated result about source iid block height off cell covariance le holds](goal). -/

lemma source_iidBlockHeight_off_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (S : Finset (Fin n)) (hS : 0 < S.card) {l r : Fin K} (hlr : l ≠ r) (i j : Fin 7) :
    |cov[iidBlockHeight K S (sourceCellScore i K l),
      iidBlockHeight K S (sourceCellScore j K r);
      Measure.pi (fun _ : Fin n => sourceObsLaw P)]| ≤ C_f ^ 2 / S.card := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  have hfi := memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore i K l) (sourceCellScore_mem_unit_interval i K l)
  have hfj := memLp_two_of_mem_unit_interval (μ := sourceObsLaw P)
    (measurable_sourceCellScore j K r) (sourceCellScore_mem_unit_interval j K r)
  rw [covariance_iidBlockHeight S hS _ _
    (measurable_sourceCellScore i K l) (measurable_sourceCellScore j K r) hfi hfj,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg (K : ℝ)) (by positivity))]
  have hsingle := source_off_cell_covariance_le c_f C_f L P n K hP hK hlr i j
  apply le_trans (mul_le_mul_of_nonneg_left hsingle
    (div_nonneg (sq_nonneg (K : ℝ)) (by positivity)))
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hSr : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  exact le_rfl
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l), [the stated result about target iid block height same cell covariance le holds](goal). -/

lemma target_iidBlockHeight_same_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (S : Finset (Fin n)) (hS : 0 < S.card) (l : Fin K) :
    |cov[iidBlockHeight K S (targetCellScore K l),
      iidBlockHeight K S (targetCellScore K l);
      Measure.pi (fun _ : Fin n => targetXLaw P)]| ≤
      ((K : ℝ) * C_f + C_f ^ 2) / S.card := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hf := memLp_two_of_mem_unit_interval (μ := targetXLaw P)
    (measurable_targetCellScore K l) (targetCellScore_mem_unit_interval K l)
  rw [covariance_iidBlockHeight S hS _ _
    (measurable_targetCellScore K l) (measurable_targetCellScore K l) hf hf,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg (K : ℝ)) (by positivity))]
  have hsingle := target_same_cell_covariance_le c_f C_f L P n K hP hK l
  apply le_trans (mul_le_mul_of_nonneg_left hsingle
    (div_nonneg (sq_nonneg (K : ℝ)) (by positivity)))
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hSr : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  exact le_rfl
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,S,hS,l,r,hlr), [the stated result about target iid block height off cell covariance le holds](goal). -/

lemma target_iidBlockHeight_off_cell_covariance_le
    (c_f C_f L : ℝ) (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (S : Finset (Fin n)) (hS : 0 < S.card) {l r : Fin K} (hlr : l ≠ r) :
    |cov[iidBlockHeight K S (targetCellScore K l),
      iidBlockHeight K S (targetCellScore K r);
      Measure.pi (fun _ : Fin n => targetXLaw P)]| ≤ C_f ^ 2 / S.card := by
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hfl := memLp_two_of_mem_unit_interval (μ := targetXLaw P)
    (measurable_targetCellScore K l) (targetCellScore_mem_unit_interval K l)
  have hfr := memLp_two_of_mem_unit_interval (μ := targetXLaw P)
    (measurable_targetCellScore K r) (targetCellScore_mem_unit_interval K r)
  rw [covariance_iidBlockHeight S hS _ _
    (measurable_targetCellScore K l) (measurable_targetCellScore K r) hfl hfr,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg (K : ℝ)) (by positivity))]
  have hsingle := target_off_cell_covariance_le c_f C_f L P n K hP hK hlr
  apply le_trans (mul_le_mul_of_nonneg_left hsingle
    (div_nonneg (sq_nonneg (K : ℝ)) (by positivity)))
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hSr : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  exact le_rfl

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
