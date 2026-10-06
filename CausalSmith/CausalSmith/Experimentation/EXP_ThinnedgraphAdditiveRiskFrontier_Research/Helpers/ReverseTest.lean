module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLaw
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseBaselineMoments
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseSourceRows

/-!
# Observable reverse-test statistic and its actual partition channel

The test uses the entire recorded graph and assignment to compute revealed sign
sums, and reads the distinct responses from the copied outcomes. Its latent
representation keeps the original source labels and independent reveal vector.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The sign test's real-valued statistic, computed from the original record. -/
-- @node: reverseTestStatistic
def reverseTestStatistic (n B d : ℕ) (o : Record (Fin n)) : ℝ :=
  ∑ ℓ, revealedSignSum n B d o.1 o.2.1 ℓ * distinctResponses n B d o ℓ

/-- [The original-record statistic is Borel measurable](goal). -/
-- @node: reverseTestStatistic_measurable
@[fun_prop]
lemma reverseTestStatistic_measurable (n B d : ℕ) :
    Measurable (reverseTestStatistic n B d) := by
  unfold reverseTestStatistic
  apply Finset.measurable_sum
  intro ℓ _
  apply Measurable.mul
  · exact (measurable_of_finite (fun hz :
        (OffDiag (Fin n) → Bool) × Assign (Fin n) =>
        revealedSignSum n B d hz.1 hz.2 ℓ)).comp
      (measurable_fst.prodMk measurable_snd.fst)
  · exact (measurable_pi_apply ℓ).comp (distinctResponses_measurable n B d)

/-- Retained graphs of the block channel do not depend on baselines or the prior sign.  [For the stated data and conditions](hyp:n,B,d,σ,h,s,U,ω), [the stated conclusion holds](goal). -/
-- @node: reverse_record_graph
lemma reverse_record_graph (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (U : Fin B → ℝ)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    (recordOf (blockSchedule n B d σ h (s, U)) ω).1 =
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 := by
  rfl

/-- For a compatible detailed graph, a row's revealed set is its source set
filtered by whether an arrow from the original label was retained anywhere.  [For the stated data and conditions](hyp:n,B,d,s,H,hs,ℓ), [the stated conclusion holds](goal). -/
-- @node: reverse_revealedSources_filter
lemma reverse_revealedSources_filter (n B d : ℕ) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2) (ℓ : Fin B) :
    revealedSources n B d H ℓ = (partitionSourceLabels n B d s ℓ).filter
      (fun j => ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true) := by
  ext j
  simp only [Finset.mem_filter]
  constructor
  · intro hj
    refine ⟨revealedSources_subset_partitionSourceLabels n B d s H hs ℓ hj, ?_⟩
    obtain ⟨_, i, _, hji, he⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨i, hji, he⟩
  · rintro ⟨hj, i, hji, he⟩
    obtain ⟨hjlt, hrow⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨⟨hjlt', k, hsk, hik⟩, _⟩ := hs ⟨(j,i),hji⟩ he
    have hk : k = ℓ := hsk.symm.trans hrow
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt, i,
      by simpa only [hk] using hik, hji, he⟩

/-- Each recorded response has the true row's total sign shift.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,U,ω,ℓ), [the stated conclusion holds](goal). -/
-- @node: reverse_distinctResponses_source_sum
lemma reverse_distinctResponses_source_sum (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (U : Fin B → ℝ) (ω : Assign (Fin n) × Audit (Fin n)) (ℓ : Fin B) :
    distinctResponses n B d (recordOf (blockSchedule n B d σ h (s,U)) ω) ℓ =
      U ℓ + signOf σ * h / (2 * d) *
        ∑ j ∈ partitionSourceLabels n B d s ℓ, signOf (ω.1 j) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (recipientBlock n B d ℓ).card by
    rw [recipientBlock_card n B d hfit]; omega)
  rw [distinctResponses_record_translation n B d hd hfit σ h s ω U]
  dsimp only
  rw [partitionResponseShift_eq_source_sum n B d hd hfit σ h s ω ℓ i hi,
    ← partitionSourceLabels_eq_inNbhd n B d s ℓ i hi]

/-- The true row's original labels are the image of its finite source fiber.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: reverse_sourceLabels_image
lemma reverse_sourceLabels_image (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) :
    partitionSourceLabels n B d s ℓ =
      (Finset.univ.filter (fun j => s.1 j = ℓ)).image
        (fun j : Fin (B * d) => (⟨j.val, by omega⟩ : Fin n)) := by
  ext j
  simp only [partitionSourceLabels, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨hj, hs⟩
    exact ⟨⟨j.val,hj⟩, hs, Fin.ext rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.isLt,hk⟩

/-- Reindexing a row sum preserves each original source label.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ,f), [the stated conclusion holds](goal). -/
-- @node: reverse_sourceLabels_sum
lemma reverse_sourceLabels_sum (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) (f : Fin n → ℝ) :
    (∑ j ∈ partitionSourceLabels n B d s ℓ, f j) =
      ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        f ⟨j.val, by omega⟩ := by
  rw [reverse_sourceLabels_image n B d hfit, Finset.sum_image]
  intro a _ b _ hab
  exact Fin.ext (congrArg (fun j : Fin n => j.val) hab)

/-- A compatible row's revealed sum is the source-fiber sum with its Bernoulli
reveal indicators, keeping assignments at their original population labels.  [For the stated data and conditions](hyp:n,B,d,hfit,s,H,hs,z,ℓ), [the stated conclusion holds](goal). -/
-- @node: reverse_revealedSignSum_source_fiber
lemma reverse_revealedSignSum_source_fiber (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (z : Assign (Fin n)) (ℓ : Fin B) :
    revealedSignSum n B d H z ℓ =
      ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        if sourceReveals n B d H j then signOf (z ⟨j.val,by omega⟩) else 0 := by
  rw [revealedSignSum, reverse_revealedSources_filter n B d s H hs,
    Finset.sum_filter, reverse_sourceLabels_sum n B d hfit]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∃ i : Fin n, ∃ hji : (⟨j.val,by omega⟩ : Fin n) ≠ i,
      H ⟨((⟨j.val,by omega⟩ : Fin n),i),hji⟩ = true) ↔
      sourceReveals n B d H j = true := by
    simp only [sourceReveals, decide_eq_true_eq]
    constructor
    · rintro ⟨i,hji,hi⟩
      exact ⟨⟨j.val,by omega⟩,rfl,i,hji,hi⟩
    · rintro ⟨v,hv,i,hvi,hi⟩
      have hv' : v = (⟨j.val,by omega⟩ : Fin n) := Fin.ext hv
      exact ⟨i, hv' ▸ hvi, by simpa only [hv'] using hi⟩
  simp only [he]

/-- The reverse statistic as a function of baselines, assignments and source reveals,
conditional on the true source partition. -/
-- @node: reverseLatentStatistic
def reverseLatentStatistic (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (s : SourcePartition B d) (U : Fin B → ℝ)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool)) : ℝ :=
  ∑ ℓ, (∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
      if zr.2 j then signOf (zr.1 ⟨j.val,by omega⟩) else 0) *
    (U ℓ + signOf σ * h / (2 * d) *
      ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        signOf (zr.1 ⟨j.val,by omega⟩))

/-- The original-record test is exactly the independent-input statistic; the
partition is used for the proof but is never supplied to the test.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,U,ω), [the stated conclusion holds](goal). -/
-- @node: reverseTestStatistic_eq_latent
lemma reverseTestStatistic_eq_latent (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (U : Fin B → ℝ) (ω : Assign (Fin n) × Audit (Fin n)) :
    reverseTestStatistic n B d (recordOf (blockSchedule n B d σ h (s,U)) ω) =
      reverseLatentStatistic n B d hfit σ h s U (ω.1, sourceReveals n B d
        (recordOf (blockSchedule n B d true 0 (s,fun _ => 0)) ω).1) := by
  unfold reverseTestStatistic reverseLatentStatistic
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [reverse_distinctResponses_source_sum n B d hd hfit,
    reverse_sourceLabels_sum n B d hfit]
  congr 1
  change revealedSignSum n B d _ ω.1 ℓ = _
  rw [reverse_record_graph, reverse_revealedSignSum_source_fiber n B d hfit]
  intro e he
  have he' : blockEdge n B d s e.val.1 e.val.2 ∧ ω.2 e = true := by
    simpa only [recordOf, blockSchedule, Bool.and_eq_true, decide_eq_true_eq] using he
  exact he'.1

/-- Actual assignments and source reveals have a product law conditional on every
true partition; the complete assignment vector remains available.  [For the stated data and conditions](hyp:n,B,d,q,hfit,hq,s), [the stated conclusion holds](goal). -/
-- @node: reverse_assignment_reveals_law
lemma reverse_assignment_reveals_law (n B d : ℕ) (q : ℝ)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d) :
    (thinnedDesign (Fin n) q).map (fun ω => (ω.1, sourceReveals n B d
      (recordOf (blockSchedule n B d true 0 (s,fun _ => 0)) ω).1)) =
      (halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q))) := by
  let := bernoulliLaw_probability q hq
  let := bernoulliLaw_probability (1 / 2) (by constructor <;> norm_num)
  let g : Audit (Fin n) → (Fin (B * d) → Bool) := fun w => sourceReveals n B d
    (recordOf (blockSchedule n B d true 0 (s,fun _ => 0)) (fun _ => false,w)).1
  have hg : Measurable g := measurable_of_finite _
  have hgm : (auditLaw (Fin n) q).map g =
      Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)) := by
    have hm := block_reveal_fixed_partition n B d q hfit hq s
    have hsnd := (thinnedDesign_audit (V := Fin n) q hq).2.2
    have ht := congrArg (fun μ : Measure (Audit (Fin n)) => μ.map g) hsnd
    rw [Measure.map_map hg measurable_snd] at ht
    exact ht.symm.trans hm
  have ht := Measure.map_prod_map (halfBernoulli (Fin n)) (auditLaw (Fin n) q)
    measurable_id hg
  rw [Measure.map_id, hgm] at ht
  exact ht.symm

/-- For each fixed partition and baseline draw, the actual statistic's law is
obtained from independent assignments and independent source reveals.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hq,s,U), [the stated conclusion holds](goal). -/
-- @node: reverseTestStatistic_fixed_partition_law
lemma reverseTestStatistic_fixed_partition_law (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (s : SourcePartition B d) (U : Fin B → ℝ) :
    (thinnedDesign (Fin n) q).map (fun ω =>
      reverseTestStatistic n B d (recordOf (blockSchedule n B d σ h (s,U)) ω)) =
    ((halfBernoulli (Fin n)).prod
      (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))).map
        (reverseLatentStatistic n B d hfit σ h s U) := by
  rw [← reverse_assignment_reveals_law n B d q hfit hq s,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  congr 1
  funext ω
  exact reverseTestStatistic_eq_latent n B d hd hfit σ h s U ω

/-- Mixing the independent-input reverse statistic over the genuine prior parameters. -/
-- @node: reverseLatentLaw
def reverseLatentLaw (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) :
    Measure ℝ :=
  (blockParamLaw B d).bind (fun ξ =>
    ((halfBernoulli (Fin n)).prod
      (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))).map
        (reverseLatentStatistic n B d hfit σ h ξ.1 ξ.2))

/-- The actual full-record statistic has exactly the independent-input mixture law.
Every conditional law retains the true source-label fiber and all assignment coordinates.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hq), [the stated conclusion holds](goal). -/
-- @node: reverseTestStatistic_mixture_law
lemma reverseTestStatistic_mixture_law (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (blockMixtureLawOf n B d (thinnedDesign (Fin n) q) σ h).map
      (reverseTestStatistic n B d) = reverseLatentLaw n B d hfit σ h q := by
  rw [blockMixtureLawOf, mixtureLaw, block_map_bind _ _ _
    (block_measurable_map_parameter _ _ (block_record_measurable n B d σ h))
    (reverseTestStatistic_measurable n B d)]
  unfold reverseLatentLaw
  congr 1
  funext ξ
  rw [Measure.map_map (reverseTestStatistic_measurable n B d)
    (measurable_of_finite _)]
  exact reverseTestStatistic_fixed_partition_law n B d hd hfit σ h q hq ξ.1 ξ.2

/-- Chebyshev bounds the plus-sign error, including the strict tie convention.  [For the stated data and conditions](hyp:μ,a,v,ha,hi,hv), [the stated conclusion holds](goal). -/
-- @node: reverse_plus_sign_error_le
lemma reverse_plus_sign_error_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a v : ℝ) (ha : 0 < a)
    (hi : Integrable (fun x => (x - a) ^ 2) μ)
    (hv : (∫ x, (x - a) ^ 2 ∂μ) ≤ v) :
    μ.real (Set.Iio 0) ≤ v / a ^ 2 := by
  have hs : Set.Iio (0 : ℝ) ⊆ {x : ℝ | a ^ 2 ≤ (x - a) ^ 2} := by
    intro x hx
    have hx' : x < 0 := hx
    dsimp
    nlinarith [sq_nonneg x]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => sq_nonneg (x - a))) hi (a ^ 2)
  have he := measureReal_mono (μ := μ) hs (measure_ne_top μ _)
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  calc
    μ.real (Set.Iio 0) * a ^ 2 ≤
        μ.real {x : ℝ | a ^ 2 ≤ (x - a) ^ 2} * a ^ 2 :=
      mul_le_mul_of_nonneg_right he (sq_nonneg a)
    _ ≤ v := by linarith

/-- Chebyshev bounds the minus-sign error, with zero assigned to plus.  [For the stated data and conditions](hyp:μ,a,v,ha,hi,hv), [the stated conclusion holds](goal). -/
-- @node: reverse_minus_sign_error_le
lemma reverse_minus_sign_error_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a v : ℝ) (ha : 0 < a)
    (hi : Integrable (fun x => (x + a) ^ 2) μ)
    (hv : (∫ x, (x + a) ^ 2 ∂μ) ≤ v) :
    μ.real (Set.Ici 0) ≤ v / a ^ 2 := by
  have hs : Set.Ici (0 : ℝ) ⊆ {x : ℝ | a ^ 2 ≤ (x + a) ^ 2} := by
    intro x hx
    have hx' : 0 ≤ x := hx
    dsimp
    nlinarith [sq_nonneg x]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => sq_nonneg (x + a))) hi (a ^ 2)
  have he := measureReal_mono (μ := μ) hs (measure_ne_top μ _)
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  calc
    μ.real (Set.Ici 0) * a ^ 2 ≤
        μ.real {x : ℝ | a ^ 2 ≤ (x + a) ^ 2} * a ^ 2 :=
      mul_le_mul_of_nonneg_right he (sq_nonneg a)
    _ ≤ v := by linarith

/-- The observable sign test separates scalar laws with opposite centers and
controlled squared deviations; no assertion about those moments is assumed
in the paper theorem.  [For the stated data and conditions](hyp:μ,ν,a,v,ha,hiμ,hiν,hvμ,hvν), [the stated conclusion holds](goal). -/
-- @node: reverse_scalar_sign_test_tv_le
lemma reverse_scalar_sign_test_tv_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a v : ℝ) (ha : 0 < a)
    (hiμ : Integrable (fun x => (x - a) ^ 2) μ)
    (hiν : Integrable (fun x => (x + a) ^ 2) ν)
    (hvμ : (∫ x, (x - a) ^ 2 ∂μ) ≤ v)
    (hvν : (∫ x, (x + a) ^ 2 ∂ν) ≤ v) :
    1 - 2 * v / a ^ 2 ≤ Causalean.Stat.tvDist μ ν := by
  have htest := Causalean.Stat.one_sub_tvDist_le_test
    (μ := μ) (ν := ν) (A := Set.Iio (0 : ℝ)) measurableSet_Iio
  rw [Set.compl_Iio] at htest
  have hplus := reverse_plus_sign_error_le μ a v ha hiμ hvμ
  have hminus := reverse_minus_sign_error_le ν a v ha hiν hvν
  rw [mul_div_assoc]
  linarith

/-- The scalar law is the pushforward of the actual probability experiment.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hq), [the stated conclusion holds](goal). -/
-- @node: reverseLatentLaw_probability
lemma reverseLatentLaw_probability (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (reverseLatentLaw n B d hfit σ h q) := by
  let : IsProbabilityMeasure (thinnedDesign (Fin n) q) :=
    thinnedDesign_probabilityDesign (V := Fin n) q hq
  let := blockMixtureLawOf_probability n B d (thinnedDesign (Fin n) q) σ h
  rw [← reverseTestStatistic_mixture_law n B d hd hfit σ h q hq]
  exact Measure.isProbabilityMeasure_map (reverseTestStatistic_measurable n B d).aemeasurable

/-- A bounded sign sum over the true source fiber is bounded by its row size.  [For the stated data and conditions](hyp:B,d,s,ℓ,f,hf), [the stated conclusion holds](goal). -/
-- @node: reverse_source_fiber_sum_abs_le
lemma reverse_source_fiber_sum_abs_le (B d : ℕ) (s : SourcePartition B d)
    (ℓ : Fin B) (f : Fin (B * d) → ℝ) (hf : ∀ j, |f j| ≤ 1) :
    |∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ), f j| ≤ d := by
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ), |f j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j => s.1 j = ℓ), (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => hf j)
    _ = d := by simp [s.2 ℓ]

/-- Every fixed-input scalar statistic is bounded on the genuine baseline support.  [For the stated data and conditions](hyp:n,B,d,hfit,σ,h,s,U,zr,hU), [the stated conclusion holds](goal). -/
-- @node: reverseLatentStatistic_abs_le
lemma reverseLatentStatistic_abs_le (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (s : SourcePartition B d) (U : Fin B → ℝ)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool))
    (hU : ∀ ℓ, |U ℓ| ≤ (1 / 4 : ℝ)) :
    |reverseLatentStatistic n B d hfit σ h s U zr| ≤
      B * ((d : ℝ) * (1 / 4 + |signOf σ * h / (2 * d)| * d)) := by
  have hsign (b : Bool) : |signOf b| ≤ 1 := by cases b <;> norm_num [signOf]
  have hA (ℓ : Fin B) := reverse_source_fiber_sum_abs_le B d s ℓ
    (fun j => if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0)
    (fun j => by split_ifs <;> simp_all only [abs_zero, zero_le_one])
  have hT (ℓ : Fin B) := reverse_source_fiber_sum_abs_le B d s ℓ
    (fun j => signOf (zr.1 ⟨j.val, by omega⟩)) (fun j => hsign _)
  unfold reverseLatentStatistic
  calc
    _ ≤ ∑ ℓ, |(∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0) *
      (U ℓ + signOf σ * h / (2 * d) *
        ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
          signOf (zr.1 ⟨j.val, by omega⟩))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ℓ : Fin B, (d : ℝ) * (1 / 4 + |signOf σ * h / (2 * d)| * d) := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [abs_mul]
      apply mul_le_mul (hA ℓ) _ (abs_nonneg _) (Nat.cast_nonneg d)
      calc
        _ ≤ |U ℓ| + |signOf σ * h / (2 * d) *
          ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
            signOf (zr.1 ⟨j.val, by omega⟩)| := abs_add_le _ _
        _ ≤ 1 / 4 + |signOf σ * h / (2 * d)| * d := by
          rw [abs_mul]
          exact add_le_add (hU ℓ) (mul_le_mul_of_nonneg_left (hT ℓ) (abs_nonneg _))
    _ = _ := by simp

/-- The bound on every fixed-input statistic survives the actual parameter mixture.  [For the stated data and conditions](hyp:n,B,d,hfit,σ,h,q,_hq), [the stated conclusion holds](goal). -/
-- @node: reverseLatentLaw_ae_abs_le
lemma reverseLatentLaw_ae_abs_le (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h q : ℝ) (_hq : q ∈ Set.Icc 0 1) :
    ∀ᵐ x ∂reverseLatentLaw n B d hfit σ h q,
      |x| ≤ B * ((d : ℝ) * (1 / 4 + |signOf σ * h / (2 * d)| * d)) := by
  let C : ℝ := B * ((d : ℝ) * (1 / 4 + |signOf σ * h / (2 * d)| * d))
  let := blockBaselineLaw_probability B
  have hparam : ∀ᵐ ξ ∂blockParamLaw B d, ∀ ℓ, |ξ.2 ℓ| ≤ (1 / 4 : ℝ) := by
    unfold blockParamLaw
    apply (Measure.ae_prod_iff_ae_ae (by
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro ℓ
      exact measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun _ => blockBaselineLaw_ae_support B)
  have hfibre : ∀ᵐ ξ ∂blockParamLaw B d,
      ∀ᵐ x ∂(((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))).map
          (reverseLatentStatistic n B d hfit σ h ξ.1 ξ.2)), |x| ≤ C := by
    filter_upwards [hparam] with ξ hξ
    apply (ae_map_iff (measurable_of_finite _).aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun zr =>
      reverseLatentStatistic_abs_le n B d hfit σ h ξ.1 ξ.2 zr hξ)
  have hz := hfibre.mono (fun ξ hξ => ae_iff.mp hξ)
  change ∀ᵐ x ∂(blockParamLaw B d).bind _, |x| ≤ C
  rw [ae_iff]
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∫⁻ ξ, (((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))).map
          (reverseLatentStatistic n B d hfit σ h ξ.1 ξ.2)) {x | ¬ |x| ≤ C}
        ∂blockParamLaw B d := Measure.bind_apply_le _
          (measurableSet_le (by fun_prop : Measurable (fun x : ℝ => |x|))
            (measurable_const : Measurable (fun _ : ℝ => C))).compl
    _ = 0 := by rw [lintegral_congr_ae hz, lintegral_zero]

/-- Every squared deviation under the actual scalar law is integrable by bounded
support, without a new regularity hypothesis.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,a,hq), [the stated conclusion holds](goal). -/
-- @node: reverseLatentLaw_squared_deviation_integrable
lemma reverseLatentLaw_squared_deviation_integrable (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q a : ℝ) (hq : q ∈ Set.Icc 0 1) :
    Integrable (fun x => (x - a) ^ 2) (reverseLatentLaw n B d hfit σ h q) := by
  let := reverseLatentLaw_probability n B d hd hfit σ h q hq
  let C : ℝ := B * ((d : ℝ) * (1 / 4 + |signOf σ * h / (2 * d)| * d))
  apply (integrable_const ((C + |a|) ^ 2)).mono' (by fun_prop)
  filter_upwards [reverseLatentLaw_ae_abs_le n B d hfit σ h q hq] with x hx
  have hb : |x - a| ≤ C + |a| := (abs_sub x a).trans (add_le_add hx (le_refl |a|))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (x - a), abs_nonneg (x - a), abs_nonneg a]

/-- The baseline-free squared signal plus the diagonal baseline budget, retaining
all original assignment coordinates and source-label fibers. -/
-- @node: reverseSignalEnergy
def reverseSignalEnergy (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h a : ℝ) (s : SourcePartition B d)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool)) : ℝ :=
  (∑ ℓ, (∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
    if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0) ^ 2) / 16 +
    (reverseLatentStatistic n B d hfit σ h s (fun _ => 0) zr - a) ^ 2

/-- Integrating the actual statistic's baselines leaves the finite signal energy.  [For the stated data and conditions](hyp:n,B,d,hfit,σ,h,a,s,zr), [the stated conclusion holds](goal). -/
-- @node: reverseLatentStatistic_baseline_energy_le
lemma reverseLatentStatistic_baseline_energy_le (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h a : ℝ) (s : SourcePartition B d)
    (zr : Assign (Fin n) × (Fin (B * d) → Bool)) :
    (∫ U, (reverseLatentStatistic n B d hfit σ h s U zr - a) ^ 2
      ∂blockBaselineLaw B) ≤ reverseSignalEnergy n B d hfit σ h a s zr := by
  have he (U : Fin B → ℝ) : reverseLatentStatistic n B d hfit σ h s U zr - a =
      (∑ ℓ, (∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0) * U ℓ) +
      (reverseLatentStatistic n B d hfit σ h s (fun _ => 0) zr - a) := by
    simp only [reverseLatentStatistic, mul_add, Finset.sum_add_distrib, zero_add]
    ring
  calc
    _ = ∫ U, ((∑ ℓ, (∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0) * U ℓ) +
        (reverseLatentStatistic n B d hfit σ h s (fun _ => 0) zr - a)) ^ 2
        ∂blockBaselineLaw B := integral_congr_ae
          (Filter.Eventually.of_forall (fun U => congrArg (fun x : ℝ => x ^ 2) (he U)))
    _ ≤ _ := by
      simpa only [reverseSignalEnergy] using reverse_baseline_shifted_second_le B
        (fun ℓ => ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
          if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0)
        (reverseLatentStatistic n B d hfit σ h s (fun _ => 0) zr - a)

/-- [Under the stated population-size condition](hyp:hfit), [the actual independent-input statistic is jointly Borel measurable](goal). -/
-- @node: reverseLatentStatistic_joint_measurable
@[fun_prop]
lemma reverseLatentStatistic_joint_measurable (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) :
    Measurable (fun x : (SourcePartition B d × (Fin B → ℝ)) ×
      (Assign (Fin n) × (Fin (B * d) → Bool)) =>
      reverseLatentStatistic n B d hfit σ h x.1.1 x.1.2 x.2) := by
  apply measurable_from_prod_countable_left
  intro zr
  apply measurable_from_prod_countable_right
  intro s
  dsimp only [reverseLatentStatistic]
  apply Finset.measurable_sum
  intro ℓ _
  apply Measurable.mul
  · exact (measurable_const : Measurable (fun _ : Fin B → ℝ =>
      ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
        if zr.2 j then signOf (zr.1 ⟨j.val, by omega⟩) else 0))
  · apply Measurable.add
    · exact measurable_pi_apply ℓ
    · exact (measurable_const : Measurable (fun _ : Fin B → ℝ =>
        signOf σ * h / (2 * d) * ∑ j ∈ Finset.univ.filter (fun j => s.1 j = ℓ),
          signOf (zr.1 ⟨j.val, by omega⟩)))

/-- The scalar mixture is the pushforward of its actual independent joint inputs.  [For the stated data and conditions](hyp:n,B,d,hfit,σ,h,q), [the stated conclusion holds](goal). -/
-- @node: reverseLatentLaw_joint_map
lemma reverseLatentLaw_joint_map (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h q : ℝ) :
    reverseLatentLaw n B d hfit σ h q =
      ((blockParamLaw B d).prod ((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q))))).map
          (fun x => reverseLatentStatistic n B d hfit σ h x.1.1 x.1.2 x.2) := by
  have hf := reverseLatentStatistic_joint_measurable n B d hfit σ h
  rw [Measure.prod, block_map_bind _ _ _ Measurable.map_prodMk_left hf]
  unfold reverseLatentLaw
  congr 1
  funext ξ
  rw [Measure.map_map hf measurable_prodMk_left]
  rfl

/-- The remaining scalar moment is bounded by a finite partition, assignment and
reveal average; the continuous baseline variables have been integrated out.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,a,hq), [the stated conclusion holds](goal). -/
-- @node: reverseLatentLaw_baseline_energy_le
lemma reverseLatentLaw_baseline_energy_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q a : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (∫ x, (x - a) ^ 2 ∂reverseLatentLaw n B d hfit σ h q) ≤
      ∫ zr, ∫ s, reverseSignalEnergy n B d hfit σ h a s zr ∂partitionLaw B d
        ∂((halfBernoulli (Fin n)).prod
          (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))) := by
  let := blockBaselineLaw_probability B
  let := partitionLaw_probability B d
  let : IsFiniteMeasure (blockParamLaw B d) := by
    unfold blockParamLaw
    infer_instance
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability (retentionP d q) (retentionP_mem_Icc d q hq)
  let ν := (halfBernoulli (Fin n)).prod
    (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)))
  let f := fun x : (SourcePartition B d × (Fin B → ℝ)) ×
      (Assign (Fin n) × (Fin (B * d) → Bool)) =>
      reverseLatentStatistic n B d hfit σ h x.1.1 x.1.2 x.2
  have hf : Measurable f := reverseLatentStatistic_joint_measurable n B d hfit σ h
  have hi := reverseLatentLaw_squared_deviation_integrable n B d hd hfit σ h q a hq
  rw [reverseLatentLaw_joint_map] at hi ⊢
  have hfi : Integrable (fun x => (f x - a) ^ 2) ((blockParamLaw B d).prod ν) :=
    (integrable_map_measure (by fun_prop) hf.aemeasurable).mp hi
  rw [integral_map hf.aemeasurable (by fun_prop), integral_prod_symm _ hfi]
  apply integral_mono_ae hfi.integral_prod_right Integrable.of_finite
  filter_upwards [hfi.prod_left_ae] with zr hz
  change Integrable (fun ξ => (f (ξ, zr) - a) ^ 2)
    ((partitionLaw B d).prod (blockBaselineLaw B)) at hz
  unfold blockParamLaw
  rw [integral_prod _ hz]
  apply integral_mono_ae hz.integral_prod_left Integrable.of_finite
  exact Filter.Eventually.of_forall (fun s =>
    reverseLatentStatistic_baseline_energy_le n B d hfit σ h a s zr)

/-- Summing the exact actual-row energies gives the finite baseline contribution.  [For the stated data and conditions](hyp:n,B,d,hfit,s,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_source_baseline_energy
lemma reverse_source_baseline_energy (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, (∑ ℓ, (reverseRowA n B d hfit s ℓ zr) ^ 2) / 16
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) =
      (B : ℝ) * d * p / 16 := by
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability p hp
  rw [integral_div, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [reverse_source_row_second n B d hfit s _ p hp]
  simp
  ring

/-- The finite signal energy of every genuine partition satisfies the roadmap bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,s,σ,h,p,hh,hhu,hp), [the stated conclusion holds](goal). -/
-- @node: reverseSignalEnergy_fixed_partition_le
lemma reverseSignalEnergy_fixed_partition_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (s : SourcePartition B d)
    (σ : Bool) (h p : ℝ) (hh : 0 < h) (hhu : h ≤ 1 / 4)
    (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, reverseSignalEnergy n B d hfit σ h
      (signOf σ * (h * (B * d : ℕ) * p / (2 * d))) s zr
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p)))) ≤
      7 * (B * d : ℕ) * p / 64 := by
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability p hp
  let ν := (halfBernoulli (Fin n)).prod
    (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p))
  let c : ℝ := signOf σ * h / (2 * d)
  have he (zr : Assign (Fin n) × (Fin (B * d) → Bool)) :
      reverseLatentStatistic n B d hfit σ h s (fun _ => 0) zr -
        signOf σ * (h * (B * d : ℕ) * p / (2 * d)) =
      c * ((∑ ℓ, reverseRowA n B d hfit s ℓ zr * reverseRowT n B d hfit s ℓ zr) -
        (B : ℝ) * d * p) := by
    simp only [reverseLatentStatistic, zero_add, reverseRowA, reverseRowT, Nat.cast_mul]
    simp_rw [mul_left_comm _ (signOf σ * h / (2 * d)), ← Finset.mul_sum]
    dsimp [c]
    ring
  have hs : c ^ 2 = h ^ 2 / (4 * (d : ℝ) ^ 2) := by
    cases σ <;> simp [c, signOf, div_pow] <;> ring
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hv := reverse_source_signal_variance_le n B d hfit s p hp
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg c)
  have henergy : (∫ zr, reverseSignalEnergy n B d hfit σ h
      (signOf σ * (h * (B * d : ℕ) * p / (2 * d))) s zr ∂ν) ≤
      (B : ℝ) * d * p / 16 + c ^ 2 * ((B : ℝ) * (3 * (d : ℝ) ^ 2 * p)) := by
    unfold reverseSignalEnergy
    simp_rw [he, mul_pow]
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
    change (∫ zr, (∑ ℓ, (reverseRowA n B d hfit s ℓ zr) ^ 2) / 16 ∂ν) + _ ≤ _
    rw [reverse_source_baseline_energy n B d hfit s p hp]
    exact add_le_add le_rfl hv'
  apply henergy.trans
  rw [hs, Nat.cast_mul]
  have hc : h ^ 2 / (4 * (d : ℝ) ^ 2) * ((B : ℝ) * (3 * (d : ℝ) ^ 2 * p)) =
      3 * h ^ 2 * B * p / 4 := by
    field_simp
  rw [hc]
  have hh2 : h ^ 2 ≤ 1 / 16 := by nlinarith
  have hm : 0 ≤ (B : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp.1
  have hb := mul_le_mul_of_nonneg_right hh2 hm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_right hd1 hm]

/-- Averaging the uniform fixed-partition bound retains its exact constant.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hh,hhu,hq), [the stated conclusion holds](goal). -/
-- @node: reverseSignalEnergy_average_le
lemma reverseSignalEnergy_average_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ)
    (hh : 0 < h) (hhu : h ≤ 1 / 4) (hq : q ∈ Set.Icc 0 1) :
    (∫ zr, ∫ s, reverseSignalEnergy n B d hfit σ h
      (signOf σ * (h * (B * d : ℕ) * retentionP d q / (2 * d))) s zr
      ∂partitionLaw B d ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q))))) ≤
      7 * (B * d : ℕ) * retentionP d q / 64 := by
  let := halfBernoulli_probability (V := Fin n)
  let := bernoulliLaw_probability (retentionP d q) (retentionP_mem_Icc d q hq)
  let := partitionLaw_probability B d
  rw [integral_integral_swap Integrable.of_finite]
  calc
    _ ≤ ∫ _s, (7 * (B * d : ℕ) * retentionP d q / 64 : ℝ) ∂partitionLaw B d := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro s
      exact reverseSignalEnergy_fixed_partition_le n B d hd hfit s σ h
        (retentionP d q) hh hhu (retentionP_mem_Icc d q hq)
    _ = _ := by simp

/-- Substituting the exact center and row-variance bound gives the paper constant.  [For the stated data and conditions](hyp:d,m,h,p,hm,hh,hp,hd), [the stated conclusion holds](goal). -/
-- @node: reverse_sign_test_constant
lemma reverse_sign_test_constant (d : ℕ) (m h p : ℝ)
    (hm : 0 < m) (hh : 0 < h) (hp : 0 < p) (hd : 1 ≤ d) :
    2 * (7 * m * p / 64) / (h * m * p / (2 * d)) ^ 2 =
      7 * (d : ℝ) ^ 2 / (8 * h ^ 2 * m * p) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp
  ring

/-- The revealed-sign outcome test supplies the reverse total-variation bound.  [For the stated data and conditions](hyp:n,B,d,h,q,D,hB,hd,hfit,hh,hhu,hq,hp,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: reverse_test_tv_bound
lemma reverse_test_tv_bound (n B d : ℕ) (h q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (hh : 0 < h) (hhu : h ≤ 1 / 4) (hq : q ∈ Set.Icc 0 1)
    (hp : 0 < retentionP d q) (ha : AssignmentLaw D) (hw : AuditLaw D q)
    (hi : DesignIndependent D) :
    1 - 7 * (d : ℝ) ^ 2 / (8 * h ^ 2 * (B * d : ℕ) * retentionP d q) ≤
      Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
        (blockMixtureLawOf n B d D false h) := by
  let := design_isProbabilityMeasure D q ha hw hi
  let := blockMixtureLawOf_probability n B d D true h
  let := blockMixtureLawOf_probability n B d D false h
  have hprojection := block_tvDist_map_le
    (blockMixtureLawOf n B d D true h) (blockMixtureLawOf n B d D false h)
    (reverseTestStatistic n B d) (reverseTestStatistic_measurable n B d)
  rw [design_eq_thinnedDesign D q ha hw hi,
    reverseTestStatistic_mixture_law n B d hd hfit true h q hq,
    reverseTestStatistic_mixture_law n B d hd hfit false h q hq] at hprojection
  rw [design_eq_thinnedDesign D q ha hw hi]
  apply le_trans _ hprojection
  let μ := reverseLatentLaw n B d hfit true h q
  let ν := reverseLatentLaw n B d hfit false h q
  let a : ℝ := h * (B * d : ℕ) * retentionP d q / (2 * d)
  let v : ℝ := 7 * (B * d : ℕ) * retentionP d q / 64
  let := reverseLatentLaw_probability n B d hd hfit true h q hq
  let := reverseLatentLaw_probability n B d hd hfit false h q hq
  have hm : (0 : ℝ) < (B * d : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < B) (by omega : 0 < d))
  have ha' : 0 < a := by
    dsimp [a]
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  -- The baseline bridge below reduces (4) in the roadmap to finite sign/reveal
  -- moments and independent row variances. The sign test is fully proved.
  have hmoment : ∀ σ : Bool,
      Integrable (fun x => (x - signOf σ * a) ^ 2)
        (reverseLatentLaw n B d hfit σ h q) ∧
      (∫ x, (x - signOf σ * a) ^ 2
        ∂reverseLatentLaw n B d hfit σ h q) ≤ v := by
    intro σ
    refine ⟨reverseLatentLaw_squared_deviation_integrable n B d hd hfit σ h q
      (signOf σ * a) hq, ?_⟩
    apply (reverseLatentLaw_baseline_energy_le n B d hd hfit σ h q
      (signOf σ * a) hq).trans
    exact reverseSignalEnergy_average_le n B d hd hfit σ h q hh hhu hq
  have hplus := hmoment true
  have hminus := hmoment false
  simp only [signOf, ↓reduceIte, one_mul] at hplus
  simp only [signOf, Bool.false_eq_true, ↓reduceIte, neg_one_mul, sub_neg_eq_add] at hminus
  have ht := reverse_scalar_sign_test_tv_le μ ν a v ha'
    hplus.1 hminus.1 hplus.2 hminus.2
  have hc := reverse_sign_test_constant d (B * d : ℕ) h (retentionP d q)
    hm hh hp hd
  simpa only [μ, ν, a, v, hc] using ht

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
