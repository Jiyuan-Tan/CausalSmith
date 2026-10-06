module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentOverlap

/-! Full-record likelihood representation for the rare-mark paired-tent table. -/
@[expose] public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A cellwise likelihood identity tilts the entire original-record table, retaining zero marks. This statement assumes [the h' condition](hyp:h'), [the hf condition](hyp:hf), [the hratio condition](hyp:hratio), [the hf0 condition](hyp:hf0). [This is the stated conclusion](goal). -/
-- @node: tableLaw_eq_withDensity_of_atom_ratios
lemma tableLaw_eq_withDensity_of_atom_ratios
    (ξ υ ζ ξ' υ' ζ' : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (h' : TableValid ξ' υ' ζ' ε L)
    (f : Record → ℝ) (hf : Measurable f)
    (hratio : ∀ x cat, markedTable (ξ' x) (υ' x) (ζ' x) ε cat =
      markedTable (ξ x) (υ x) (ζ x) ε cat * f (x,cat.1,markValue L cat.2))
    (hf0 : ∀ o, 0 ≤ f o) :
    tableLaw ξ' υ' ζ' ε L = (tableLaw ξ υ ζ ε L).withDensity (fun o => ENNReal.ofReal (f o)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  simp only [tableLaw]
  rw [Measure.lintegral_bind
      (measurable_table_record_atoms ξ υ ζ ε L h).aemeasurable
      ((hf.ennreal_ofReal).indicator hs).aemeasurable,
    Measure.bind_apply hs
      (measurable_table_record_atoms ξ' υ' ζ' ε L h').aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_finsetSum_measure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, lintegral_smul_measure,
    lintegral_dirac' _ ((hf.ennreal_ofReal).indicator hs)]
  apply Finset.sum_congr rfl
  intro cat _
  rw [hratio x cat, ENNReal.ofReal_mul (h.2.2.2.2.2.2 x cat)]
  by_cases ho : (x,cat.1,markValue L cat.2) ∈ s <;> simp [Set.indicator, ho]

/-- A categorywise likelihood identity tilts the faithful paired-tent record law. This statement assumes [the h condition](hyp:h), [the h' condition](hyp:h'), [the hf condition](hyp:hf), [the hratio condition](hyp:hratio), [the hf0 condition](hyp:hf0). [This is the stated conclusion](goal). -/
lemma pairedTentRecordLaw_eq_withDensity_of_atom_ratios
    (r r' : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) (h' : TableValid (fun _ => 0) r' r' ε L)
    (f : Record → ℝ) (hf : Measurable f)
    (hratio : ∀ x cat, pairedTentTable (r' x) ε cat =
      pairedTentTable (r x) ε cat * f (x,cat.1,markValue L cat.2))
    (hf0 : ∀ o, 0 ≤ f o) :
    pairedTentRecordLaw r' ε L = (pairedTentRecordLaw r ε L).withDensity
      (fun o => ENNReal.ofReal (f o)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  simp only [pairedTentRecordLaw]
  rw [Measure.lintegral_bind
      (measurable_pairedTent_record_atoms r ε L h).aemeasurable
      ((hf.ennreal_ofReal).indicator hs).aemeasurable,
    Measure.bind_apply hs
      (measurable_pairedTent_record_atoms r' ε L h').aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_finsetSum_measure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, lintegral_smul_measure,
    lintegral_dirac' _ ((hf.ennreal_ofReal).indicator hs)]
  apply Finset.sum_congr rfl
  intro cat _
  rw [hratio x cat, ENNReal.ofReal_mul (pairedTentTable_nonneg r ε L h x cat)]
  by_cases ho : (x,cat.1,markValue L cat.2) ∈ s <;> simp [Set.indicator, ho]

/-- The true likelihood keeps both treatment categories and every zero-outcome record. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the σ parameter](hyp:σ), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
-- @node: tentLikelihood
def tentLikelihood (n : ℕ) (v : Params) (σ : Fin (tentRank n v/2) → Bool)
    (o : Record) : ℝ :=
  1 + if o.2.1 then
    if o.2.2 = tentMagnitude n v then kappa0*coarseTent (tentRank n v) σ o.1
    else if o.2.2 = -tentMagnitude n v then -kappa0*coarseTent (tentRank n v) σ o.1
    else 0
  else 0

/-- The complete-record likelihood is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_tentLikelihood
@[fun_prop] lemma measurable_tentLikelihood (n : ℕ) (v : Params)
    (σ : Fin (tentRank n v/2) → Bool) : Measurable (tentLikelihood n v σ) := by
  unfold tentLikelihood
  apply measurable_const.add
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
    · apply Measurable.ite
      · exact measurableSet_eq_fun (by fun_prop) measurable_const
      · fun_prop
      · exact measurable_const
  · exact measurable_const

/-- The complete-record likelihood is positive and uniformly bounded on the whole record space. [This is the stated conclusion](goal). -/
-- @node: tentLikelihood_bounds
lemma tentLikelihood_bounds (n : ℕ) (v : Params)
    (σ : Fin (tentRank n v/2) → Bool) (o : Record) :
    15/16 ≤ tentLikelihood n v σ o ∧ tentLikelihood n v σ o ≤ 17/16 := by
  have hg := abs_le.mp (coarseTent_abs_le_one (tentRank n v) σ o.1)
  unfold tentLikelihood
  split_ifs <;> norm_num [kappa0] <;> constructor <;> linarith [hg.1, hg.2]

/-- Every alternative table atom is the corresponding null atom times its full-record likelihood. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma tent_table_atom_likelihood (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) (cat : Category) :
    pairedTentTable
      (tentEffect n v σ x/(2*tentRarity n v*tentMagnitude n v)) (tentRarity n v) cat =
      pairedTentTable 0 (tentRarity n v) cat *
        tentLikelihood n v σ (x,cat.1,markValue (tentMagnitude n v) cat.2) := by
  have hL := (tent_mark_parameters v hv n hn).2
  have hL0 : tentMagnitude n v ≠ 0 := hL.ne'
  have hLn : tentMagnitude n v ≠ -tentMagnitude n v := by linarith
  rw [tent_table_coordinate v hv n hn σ x]
  rcases cat with ⟨a, mark⟩
  cases mark with
  | none => cases a <;> simp [pairedTentTable, markedTable, markValue, tentLikelihood, hL0, hL0.symm]
  | some b =>
    cases a <;> cases b <;>
      simp [pairedTentTable, markedTable, markValue, tentLikelihood, signVal, hLn, hLn.symm] <;> ring <;> simp

/-- The alternative is the likelihood tilt of the actual normalized null original-record law. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_true_eq_withDensity
lemma tentLaw_true_eq_withDensity (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) :
    (tentLaw true n v σ).P = (tentLaw false n v (fun _ => false)).P.withDensity
      (fun o => ENNReal.ofReal (tentLikelihood n v σ o)) := by
  have h := zero_table_valid _ _ (tent_mark_parameters v hv n hn).1
    (tent_mark_parameters v hv n hn).2
  have h' := tentLaw_true_table_valid v hv n hn σ
  simp only [tentLaw, Bool.false_eq_true, ↓reduceIte, zero_div]
  simp only [pairedTentObservedLaw, dif_pos h, dif_pos h']
  exact pairedTentRecordLaw_eq_withDensity_of_atom_ratios _ _ _ _ h h'
    _ (measurable_tentLikelihood n v σ) (tent_table_atom_likelihood v hv n hn σ)
    (fun o => le_trans (by norm_num) (tentLikelihood_bounds n v σ o).1)

/-- Integrating a nonnegative Borel function over the table keeps all six atom contributions. This statement assumes [the hf condition](hyp:hf), [the hf0 condition](hyp:hf0). [This is the stated conclusion](goal). -/
-- @node: integral_tableLaw_nonneg
lemma integral_tableLaw_nonneg (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (f : Record → ℝ)
    (hf : Measurable f) (hf0 : ∀ o, 0 ≤ f o) :
    (∫ o, f o ∂tableLaw ξ υ ζ ε L) =
      ∫ x : unitInterval, ∑ cat : Category,
        markedTable (ξ x) (υ x) (ζ x) ε cat * f (x,cat.1,markValue L cat.2) ∂design := by
  have hm : Measurable (fun x : unitInterval => ∑ cat : Category,
      markedTable (ξ x) (υ x) (ζ x) ε cat * f (x,cat.1,markValue L cat.2)) := by
    have hξ := h.1.measurable
    have hυ := h.2.1.measurable
    have hζ := h.2.2.1.measurable
    apply Finset.measurable_fun_sum
    intro cat _
    have hfc : Measurable (fun x : unitInterval => f (x,cat.1,markValue L cat.2)) := by
      fun_prop
    rcases cat with ⟨a, mark⟩
    cases mark <;> simp only [markedTable] <;> fun_prop
  have hn (x : unitInterval) : 0 ≤ ∑ cat : Category,
      markedTable (ξ x) (υ x) (ζ x) ε cat * f (x,cat.1,markValue L cat.2) :=
    Finset.sum_nonneg (fun cat _ => mul_nonneg (h.2.2.2.2.2.2 x cat) (hf0 _))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable,
    tableLaw, Measure.lintegral_bind (measurable_table_record_atoms ξ υ ζ ε L h).aemeasurable
      hf.ennreal_ofReal.aemeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf.ennreal_ofReal, smul_eq_mul]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun cat _ => mul_nonneg (h.2.2.2.2.2.2 x cat) (hf0 _))]
  apply Finset.sum_congr rfl
  intro cat _
  exact (ENNReal.ofReal_mul (h.2.2.2.2.2.2 x cat)).symm

/-- Integrate every paired-tent record category, including the deterministic control atom. This statement assumes [the h condition](hyp:h), [the hf condition](hyp:hf), [the hf0 condition](hyp:hf0). [This is the stated conclusion](goal). -/
lemma integral_pairedTentRecordLaw_nonneg (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) (f : Record → ℝ)
    (hf : Measurable f) (hf0 : ∀ o, 0 ≤ f o) :
    (∫ o, f o ∂pairedTentRecordLaw r ε L) =
      ∫ x : unitInterval, ∑ cat : Category,
        pairedTentTable (r x) ε cat * f (x,cat.1,markValue L cat.2) ∂design := by
  have hm : Measurable (fun x : unitInterval => ∑ cat : Category,
      pairedTentTable (r x) ε cat * f (x,cat.1,markValue L cat.2)) := by
    have hr := h.2.1.measurable
    apply Finset.measurable_fun_sum
    intro cat _
    have hfc : Measurable (fun x : unitInterval => f (x,cat.1,markValue L cat.2)) := by
      fun_prop
    rcases cat with ⟨a, mark⟩
    cases a <;> cases mark <;> simp [pairedTentTable, markedTable] <;> fun_prop
  have hn (x : unitInterval) : 0 ≤ ∑ cat : Category,
      pairedTentTable (r x) ε cat * f (x,cat.1,markValue L cat.2) :=
    Finset.sum_nonneg (fun cat _ => mul_nonneg (pairedTentTable_nonneg r ε L h x cat) (hf0 _))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable,
    pairedTentRecordLaw, Measure.lintegral_bind (measurable_pairedTent_record_atoms r ε L h).aemeasurable
      hf.ennreal_ofReal.aemeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf.ennreal_ofReal, smul_eq_mul]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun cat _ => mul_nonneg (pairedTentTable_nonneg r ε L h x cat) (hf0 _))]
  apply Finset.sum_congr rfl
  intro cat _
  exact (ENNReal.ofReal_mul (pairedTentTable_nonneg r ε L h x cat)).symm

/-- Every pair of complete-record likelihoods is integrable under the actual null. [This is the stated conclusion](goal). -/
-- @node: tentLikelihood_pair_integrable
lemma tentLikelihood_pair_integrable (n : ℕ) (v : Params)
    (σ τ : Fin (tentRank n v/2) → Bool) :
    Integrable (fun o => tentLikelihood n v σ o * tentLikelihood n v τ o)
      (tentLaw false n v (fun _ => false)).P := by
  apply Integrable.of_bound
    ((measurable_tentLikelihood n v σ).mul (measurable_tentLikelihood n v τ)).aestronglyMeasurable 4
  filter_upwards [] with o
  have hs := tentLikelihood_bounds n v σ o
  have ht := tentLikelihood_bounds n v τ o
  change |tentLikelihood n v σ o * tentLikelihood n v τ o| ≤ 4
  rw [abs_of_nonneg (mul_nonneg (by linarith [hs.1]) (by linarith [ht.1]))]
  nlinarith [mul_le_mul hs.2 ht.2 (by linarith [ht.1]) (by norm_num : (0:ℝ) ≤ 17/16)]

/-- Summing every record category gives the exact treated-mark overlap and its rarity factor. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma tentLikelihood_pair_atom_sum (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n v/2) → Bool) (x : unitInterval) :
    (∑ cat : Category, pairedTentTable 0 (tentRarity n v) cat *
      (tentLikelihood n v σ (x,cat.1,markValue (tentMagnitude n v) cat.2) *
        tentLikelihood n v τ (x,cat.1,markValue (tentMagnitude n v) cat.2))) =
      1 + (tentRarity n v*kappa0^2/2)*
        (coarseTent (tentRank n v) σ x * coarseTent (tentRank n v) τ x) := by
  have hL := (tent_mark_parameters v hv n hn).2
  have hL0 : tentMagnitude n v ≠ 0 := hL.ne'
  have hLn : tentMagnitude n v ≠ -tentMagnitude n v := by linarith
  simp [Fintype.sum_prod_type, pairedTentTable, markedTable, markValue, tentLikelihood,
    signVal, hL0, hL0.symm, hLn, hLn.symm]
  ring

/-- The true one-observation overlap is the normalized inner-sign product in the roadmap. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLikelihood_pair_overlap
lemma tentLikelihood_pair_overlap (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n v/2) → Bool) :
    (∫ o, tentLikelihood n v σ o * tentLikelihood n v τ o
      ∂(tentLaw false n v (fun _ => false)).P) =
      1+(tentRarity n v*kappa0^2/6)*
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(tentRank n v/2:ℕ) := by
  have h := zero_table_valid _ _ (tent_mark_parameters v hv n hn).1
    (tent_mark_parameters v hv n hn).2
  rw [tentLaw_false_eq_zero_table]
  simp only [pairedTentObservedLaw, dif_pos h]
  rw [integral_pairedTentRecordLaw_nonneg _ _ _ h (fun o => tentLikelihood n v σ o * tentLikelihood n v τ o)
    ((measurable_tentLikelihood n v σ).mul (measurable_tentLikelihood n v τ))
    (fun o => mul_nonneg
      (le_trans (by norm_num) (tentLikelihood_bounds n v σ o).1)
      (le_trans (by norm_num) (tentLikelihood_bounds n v τ o).1))]
  simp_rw [tentLikelihood_pair_atom_sum v hv n hn σ τ]
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  have hg : Integrable (fun x : unitInterval =>
      coarseTent (tentRank n v) σ x * coarseTent (tentRank n v) τ x) design := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (coarseTent_abs_le_one _ σ x) (abs_nonneg _)
      (coarseTent_abs_le_one _ τ x)
  have hN : 0 < tentRank n v := by have := (tentRank_bounds v hv n hn).1; omega
  rw [integral_add (integrable_const 1) (hg.const_mul _), integral_const_mul,
    coarseTent_design_overlap _ hN]
  have heven : 2*(tentRank n v/2) = tentRank n v := by unfold tentRank; omega
  have hc : (tentRank n v:ℝ) = 2*(tentRank n v/2:ℕ) := by exact_mod_cast heven.symm
  have hvol : design Set.univ = 1 := by
    change (volume : Measure unitInterval) Set.univ = 1
    exact measure_univ
  simp only [integral_const, measureReal_def, hvol, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [hc]
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
