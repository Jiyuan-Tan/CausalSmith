module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ChiSqDecomposition
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.GeniePartition

/-!
# Finite retained-graph conditioning and conditional testing bounds

The normalized graph fibers have unit mass on every positive-probability graph.
Common finite mixtures average conditional total-variation bounds, and a common
reference converts two conditional chi-squared budgets into a testing bound.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory Function
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- The distinct-response record has exactly the actual complete retained-graph marginal.  [For the stated data and conditions](hyp:n,B,d,D,σ,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_graph_marginal
lemma reducedBlockLaw_graph_marginal (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [SFinite D] (σ : Bool) (h : ℝ) :
    (reducedBlockLaw n B d D σ h).map Prod.fst = retainedGraphMarginal n B d D := by
  rw [reducedBlockLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have he := block_mixture_graphAssignMarginal n B d σ h D
  rw [retainedGraphMarginal, ← he, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The unnormalized graph fiber has mass equal to the actual graph-atom probability.  [For the stated data and conditions](hyp:n,B,d,D,σ,h,H), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_graph_fiber_mass
lemma reducedBlockLaw_graph_fiber_mass (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [SFinite D] (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) :
    ((reducedBlockLaw n B d D σ h).restrict {x | x.1 = H}).map Prod.snd Set.univ =
      retainedGraphMarginal n B d D {H} := by
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, ← reducedBlockLaw_graph_marginal n B d D σ h,
    Measure.map_apply (by fun_prop) (measurableSet_singleton H)]
  rfl

/-- On every graph atom of positive probability, the actual conditional law is a probability law.  [For the stated data and conditions](hyp:n,B,d,D,σ,h,H,hH), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_probability
lemma conditionalBlockLaw_probability (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (σ : Bool) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d D {H} ≠ 0) :
    IsProbabilityMeasure (conditionalBlockLaw n B d D σ h H) := by
  let := blockMixtureLawOf_probability n B d D σ h
  have hm : Measurable (fun o : Record (Fin n) =>
      (o.1, o.2.1, distinctResponses n B d o)) := by fun_prop
  let : IsProbabilityMeasure (reducedBlockLaw n B d D σ h) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure (retainedGraphMarginal n B d D) := by
    rw [← reducedBlockLaw_graph_marginal n B d D σ h]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  rw [conditionalBlockLaw, Measure.smul_apply, smul_eq_mul,
    reducedBlockLaw_graph_fiber_mass, ENNReal.inv_mul_cancel hH (measure_ne_top _ _)]

/-- A null retained graph has zero conditional law under the chosen null-atom convention.  [For the stated data and conditions](hyp:n,B,d,D,σ,h,H,hH), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_null
lemma conditionalBlockLaw_null (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [SFinite D]
    (σ : Bool) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d D {H} = 0) :
    conditionalBlockLaw n B d D σ h H = 0 := by
  have hz : ((reducedBlockLaw n B d D σ h).restrict {x | x.1 = H}).map Prod.snd = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    rw [reducedBlockLaw_graph_fiber_mass, hH]
  rw [conditionalBlockLaw, hz, smul_zero]

/-- Multiplying a conditional law by its graph probability recovers the unnormalized fiber.  [For the stated data and conditions](hyp:n,B,d,D,σ,h,H), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_weighted
lemma conditionalBlockLaw_weighted (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (σ : Bool) (h : ℝ) (H : OffDiag (Fin n) → Bool) :
    retainedGraphMarginal n B d D {H} • conditionalBlockLaw n B d D σ h H =
      ((reducedBlockLaw n B d D σ h).restrict {x | x.1 = H}).map Prod.snd := by
  by_cases hH : retainedGraphMarginal n B d D {H} = 0
  · rw [hH, zero_smul]
    apply Eq.symm
    apply Measure.measure_univ_eq_zero.mp
    rw [reducedBlockLaw_graph_fiber_mass, hH]
  · let := blockMixtureLawOf_probability n B d D σ h
    let : IsProbabilityMeasure (reducedBlockLaw n B d D σ h) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    let : IsProbabilityMeasure (retainedGraphMarginal n B d D) := by
      rw [← reducedBlockLaw_graph_marginal n B d D σ h]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    rw [conditionalBlockLaw, smul_smul,
      ENNReal.mul_inv_cancel hH (measure_ne_top _ _), one_smul]

/-- Restoring the fixed graph coordinate after projecting a graph fiber is exact.  [For the stated data and conditions](hyp:α,β,μ,a), [the stated conclusion holds](goal). -/
-- @node: block_graph_fiber_map_copy
lemma block_graph_fiber_map_copy {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] (μ : Measure (α × β)) (a : α) :
    ((μ.restrict {x | x.1 = a}).map Prod.snd).map (Prod.mk a) =
      μ.restrict {x | x.1 = a} := by
  rw [Measure.map_map measurable_prodMk_left measurable_snd]
  have hs : MeasurableSet {x : α × β | x.1 = a} := by
    exact measurable_fst (measurableSet_singleton a)
  have he : (Prod.mk a ∘ Prod.snd) =ᵐ[μ.restrict {x | x.1 = a}] id := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact Prod.ext hx.symm rfl
  rw [Measure.map_congr he, Measure.map_id]

/-- The actual distinct-response record is the mixture of its normalized complete-graph fibers.
Null graph atoms contribute zero, so no conditional law on a null event is assumed.  [For the stated data and conditions](hyp:n,B,d,D,σ,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_bind_conditional
lemma reducedBlockLaw_bind_conditional (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (σ : Bool) (h : ℝ) :
    reducedBlockLaw n B d D σ h =
      (retainedGraphMarginal n B d D).bind (fun H =>
        (conditionalBlockLaw n B d D σ h H).map (Prod.mk H)) := by
  let μ := reducedBlockLaw n B d D σ h
  let K := fun H => (conditionalBlockLaw n B d D σ h H).map (Prod.mk H)
  have hK : Measurable K := measurable_of_finite _
  have hcopy (H : OffDiag (Fin n) → Bool) :
      retainedGraphMarginal n B d D {H} • K H = μ.restrict {x | x.1 = H} := by
    dsimp only [K]
    rw [← Measure.map_smul, conditionalBlockLaw_weighted,
      block_graph_fiber_map_copy]
  have hd : Pairwise (Disjoint on (fun H : OffDiag (Fin n) → Bool =>
      {x : (OffDiag (Fin n) → Bool) × (Assign (Fin n) × (Fin B → ℝ)) | x.1 = H})) := by
    intro H G hHG
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hHG (hx.symm.trans hy)
  have hs (H : OffDiag (Fin n) → Bool) :
      MeasurableSet {x : (OffDiag (Fin n) → Bool) ×
        (Assign (Fin n) × (Fin B → ℝ)) | x.1 = H} :=
    measurable_fst (measurableSet_singleton H)
  have hu : (⋃ H : OffDiag (Fin n) → Bool,
      {x : (OffDiag (Fin n) → Bool) × (Assign (Fin n) × (Fin B → ℝ)) | x.1 = H}) =
      Set.univ := by
    ext x
    simp
  have hsum := Measure.restrict_iUnion (μ := μ) hd hs
  rw [hu, Measure.restrict_univ] at hsum
  ext E hE
  rw [Measure.bind_apply hE hK.aemeasurable, lintegral_fintype]
  change μ E = _
  rw [hsum, Measure.sum_apply _ hE, tsum_fintype]
  apply Finset.sum_congr rfl
  intro H _
  have he := congrArg (fun ν => ν E) (hcopy H)
  simpa only [Measure.smul_apply, smul_eq_mul, mul_comm] using he.symm

/-- A common finite mixing marginal averages conditional total-variation distances.  [For the stated data and conditions](hyp:α,β,μ,P,Q,hP,hQ,hPm,hQm), [the stated conclusion holds](goal). -/
-- @node: block_tvDist_bind_integral_le
lemma block_tvDist_bind_integral_le {α β : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (P Q : α → Measure β)
    (hP : ∀ᵐ a ∂μ, IsProbabilityMeasure (P a))
    (hQ : ∀ᵐ a ∂μ, IsProbabilityMeasure (Q a))
    (hPm : Measurable P) (hQm : Measurable Q) :
    Causalean.Stat.tvDist (μ.bind P) (μ.bind Q) ≤
      ∫ a, Causalean.Stat.tvDist (P a) (Q a) ∂μ := by
  unfold Causalean.Stat.tvDist at ⊢
  apply ciSup_le
  rintro ⟨E, hE⟩
  have hreal (K : α → Measure β) (hK : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
      (hKm : Measurable K) : (μ.bind K).real E = ∫ a, (K a).real E ∂μ := by
    rw [measureReal_def, Measure.bind_apply hE hKm.aemeasurable]
    exact (integral_toReal ((Measure.measurable_coe hE).comp hKm).aemeasurable
      (hK.mono (fun a ha => by
        let _ := ha
        exact measure_lt_top (K a) E))).symm
  rw [hreal P hP hPm, hreal Q hQ hQm,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  exact abs_integral_le_integral_abs.trans
    (integral_mono_ae Integrable.of_finite Integrable.of_finite (by
      filter_upwards [hP, hQ] with a ha hb
      let _ := ha
      let _ := hb
      exact Causalean.Stat.abs_measureReal_sub_le_tvDist hE))

/-- The full original-record distance is bounded by the mean conditional distance over
its actual complete retained-graph marginal, with all assignment coordinates retained.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h), [the stated conclusion holds](goal). -/
-- @node: blockMixture_tvDist_le_mean_conditional
lemma blockMixture_tvDist_le_mean_conditional (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] (h : ℝ) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤
      ∫ H, Causalean.Stat.tvDist (conditionalBlockLaw n B d D true h H)
        (conditionalBlockLaw n B d D false h H) ∂(retainedGraphMarginal n B d D) := by
  let μ := retainedGraphMarginal n B d D
  let := blockMixtureLawOf_probability n B d D true h
  let : IsProbabilityMeasure (reducedBlockLaw n B d D true h) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure μ := by
    dsimp only [μ]
    rw [← reducedBlockLaw_graph_marginal n B d D true h]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpos : ∀ᵐ H ∂μ, μ {H} ≠ 0 := ae_iff_of_countable.mpr (fun _ => id)
  have hprob (σ : Bool) : ∀ᵐ H ∂μ,
      IsProbabilityMeasure ((conditionalBlockLaw n B d D σ h H).map (Prod.mk H)) := by
    filter_upwards [hpos] with H hH
    let := conditionalBlockLaw_probability n B d D σ h H hH
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← reducedBlockLaw_tvDist_eq n B d hd hfit D h,
    reducedBlockLaw_bind_conditional, reducedBlockLaw_bind_conditional]
  apply (block_tvDist_bind_integral_le μ _ _ (hprob true) (hprob false)
    (measurable_of_finite _) (measurable_of_finite _)).trans
  apply integral_mono_ae Integrable.of_finite Integrable.of_finite
  filter_upwards [hpos] with H hH
  let := conditionalBlockLaw_probability n B d D true h H hH
  let := conditionalBlockLaw_probability n B d D false h H hH
  exact block_tvDist_map_le _ _ (Prod.mk H) (by fun_prop)

/-- Two conditional laws with the same chi-squared budget against a common reference
have distance at most the square root of that budget.  [For the stated data and conditions](hyp:α,P,Q,R,hP,hQ,hiP,hiQ,heq), [the stated conclusion holds](goal). -/
-- @node: block_tvDist_le_sqrt_common_chiSq
lemma block_tvDist_le_sqrt_common_chiSq {α : Type*} [MeasurableSpace α]
    (P Q R : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] (hP : P ≪ R) (hQ : Q ≪ R)
    (hiP : Integrable (fun x => ((P.rnDeriv R x).toReal - 1) ^ 2) R)
    (hiQ : Integrable (fun x => ((Q.rnDeriv R x).toReal - 1) ^ 2) R)
    (heq : Causalean.Stat.chiSqDiv Q R = Causalean.Stat.chiSqDiv P R) :
    Causalean.Stat.tvDist P Q ≤ Real.sqrt (Causalean.Stat.chiSqDiv P R) := by
  have hp := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv P R hP hiP
  have hq := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv Q R hQ hiQ
  rw [heq] at hq
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨E, hE⟩
  calc
    |P.real E - Q.real E| ≤ |P.real E - R.real E| + |Q.real E - R.real E| := by
      have ht := abs_add_le (P.real E - R.real E) (R.real E - Q.real E)
      rw [abs_sub_comm (R.real E) (Q.real E)] at ht
      simpa only [sub_add_sub_cancel] using ht
    _ ≤ (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv P R) +
        (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv P R) :=
      add_le_add ((Causalean.Stat.abs_measureReal_sub_le_tvDist hE).trans hp)
        ((Causalean.Stat.abs_measureReal_sub_le_tvDist hE).trans hq)
    _ = _ := by ring

/-- The actual complete retained-graph marginal is a probability law.  [For the stated data and conditions](hyp:n,B,d,D), [the stated conclusion holds](goal). -/
-- @node: retainedGraphMarginal_probability
lemma retainedGraphMarginal_probability (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (retainedGraphMarginal n B d D) := by
  let := blockMixtureLawOf_probability n B d D true 0
  let : IsProbabilityMeasure (reducedBlockLaw n B d D true 0) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← reducedBlockLaw_graph_marginal n B d D true 0]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- On a finite probability space, averaging square roots costs at most the square root
of the mean. This is Cauchy--Schwarz with the constant function one.  [For the stated data and conditions](hyp:α,μ,g,hg), [the stated conclusion holds](goal). -/
-- @node: block_integral_sqrt_le
lemma block_integral_sqrt_le {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∫ a, Real.sqrt (g a) ∂μ) ≤ Real.sqrt (∫ a, g a ∂μ) := by
  let c := ∫ a, Real.sqrt (g a) ∂μ
  have hvar : 0 ≤ ∫ a, (Real.sqrt (g a) - c) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun a => (Real.sqrt (g a) - c) ^ 2) =
      fun a => g a - 2 * c * Real.sqrt (g a) + c ^ 2 := by
    funext a
    nlinarith [Real.sq_sqrt (hg a)]
  rw [he, integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul] at hvar
  have hsq : c ^ 2 ≤ ∫ a, g a ∂μ := by
    simp [integral_const] at hvar
    change 0 ≤ (∫ a, g a ∂μ) - 2 * c * c + c ^ 2 at hvar
    nlinarith
  have hroot := Real.sq_sqrt (integral_nonneg hg : 0 ≤ ∫ a, g a ∂μ)
  have hc : 0 ≤ c := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have hr : 0 ≤ Real.sqrt (∫ a, g a ∂μ) := Real.sqrt_nonneg _
  change c ≤ _
  nlinarith

/-- A finite probability mixture splits into a bad-event mass and the square root
of its good-event second-moment budget.  [For the stated data and conditions](hyp:α,μ,E,t,g,hg,ht,hgood), [the stated conclusion holds](goal). -/
-- @node: block_integral_good_event_le
lemma block_integral_good_event_le {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (t g : α → ℝ) (hg : ∀ a, 0 ≤ g a)
    (ht : ∀ᵐ a ∂μ, t a ≤ 1)
    (hgood : ∀ᵐ a ∂μ, a ∈ E → t a ≤ Real.sqrt (g a)) :
    (∫ a, t a ∂μ) ≤ μ.real Eᶜ + Real.sqrt (∫ a, E.indicator g a ∂μ) := by
  classical
  have hs : MeasurableSet E := Set.to_countable E |>.measurableSet
  have hpoint : ∀ᵐ a ∂μ, t a ≤ Eᶜ.indicator (fun _ => (1 : ℝ)) a +
      Real.sqrt (E.indicator g a) := by
    filter_upwards [ht, hgood] with a ha hb
    by_cases he : a ∈ E
    · simpa [he] using hb he
    · simpa [he] using ha
  have havg := integral_mono_ae (μ := μ) Integrable.of_finite
    Integrable.of_finite hpoint
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_indicator hs.compl] at havg
  have hb := block_integral_sqrt_le μ (E.indicator g)
    (fun a => Set.indicator_nonneg (fun a _ => hg a) a)
  have hmass : (∫ a in Eᶜ, (1 : ℝ) ∂μ) = μ.real Eᶜ := by simp
  rw [hmass] at havg
  exact havg.trans (add_le_add_right hb _)

/-- Conditional square-root bounds give the roadmap's good-event bound for the
complete original record, retaining the full graph and assignment marginal.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h,E,hcond), [the stated conclusion holds](goal). -/
-- @node: blockMixture_tvDist_good_event_le
lemma blockMixture_tvDist_good_event_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) (E : Set (OffDiag (Fin n) → Bool))
    (hcond : ∀ᵐ H ∂(retainedGraphMarginal n B d D), H ∈ E →
      Causalean.Stat.tvDist (conditionalBlockLaw n B d D true h H)
        (conditionalBlockLaw n B d D false h H) ≤ Real.sqrt (hiddenChiSq n B d D h H)) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤
      (retainedGraphMarginal n B d D).real Eᶜ +
        Real.sqrt (∫ H, E.indicator (hiddenChiSq n B d D h) H
          ∂(retainedGraphMarginal n B d D)) := by
  let := retainedGraphMarginal_probability n B d D
  apply (blockMixture_tvDist_le_mean_conditional n B d hd hfit D h).trans
  apply block_integral_good_event_le _ E _ _ (hiddenChiSq_nonneg n B d D h) _ hcond
  have hpos : ∀ᵐ H ∂(retainedGraphMarginal n B d D),
      retainedGraphMarginal n B d D {H} ≠ 0 := ae_iff_of_countable.mpr (fun _ => id)
  filter_upwards [hpos] with H hH
  let := conditionalBlockLaw_probability n B d D true h H hH
  let := conditionalBlockLaw_probability n B d D false h H hH
  exact Causalean.Stat.tvDist_le_one

/-- The cosine baseline density is even.  [For the stated data and conditions](hyp:w), [the stated conclusion holds](goal). -/
-- @node: cosSqDensity_neg
lemma cosSqDensity_neg (w : ℝ) : cosSqDensity (-w) = cosSqDensity w := by
  simp [cosSqDensity, abs_neg, mul_neg, Real.cos_neg]

/-- Reflecting a baseline draw preserves its probability law.  [the stated conclusion holds](goal). -/
-- @node: block_baseline_map_neg
lemma block_baseline_map_neg :
    (volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))).map
      (fun w : ℝ => -w) = volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w)) := by
  have ht := Causalean.Mathlib.MeasureTheory.map_withDensity_comp_measurableEquiv
    (MeasurableEquiv.neg ℝ) (Measure.measurePreserving_neg volume)
    (fun w => ENNReal.ofReal (cosSqDensity w))
  simpa [Function.comp_def, cosSqDensity_neg] using ht

/-- Reflecting independent block baselines preserves their joint law.  [For the stated data and conditions](hyp:B), [the stated conclusion holds](goal). -/
-- @node: blockBaselineLaw_map_neg
lemma blockBaselineLaw_map_neg (B : ℕ) :
    (blockBaselineLaw B).map (fun U ℓ => -U ℓ) = blockBaselineLaw B := by
  let : IsProbabilityMeasure (volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal cosSqDensity_integrable_normalized.1
        (Filter.Eventually.of_forall cosSqDensity_nonneg), cosSqDensity_integrable_normalized.2]
    simp
  let : IsProbabilityMeasure ((volume.withDensity
      (fun w => ENNReal.ofReal (cosSqDensity w))).map (fun w : ℝ => -w)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [blockBaselineLaw, Measure.pi_map_pi (f := fun _ w => -w) (fun _ => by fun_prop)]
  simp_rw [block_baseline_map_neg]

/-- The prior is invariant when all baselines are reflected, with the labeled partition fixed.  [For the stated data and conditions](hyp:B,d), [the stated conclusion holds](goal). -/
-- @node: blockParamLaw_map_neg
lemma blockParamLaw_map_neg (B d : ℕ) :
    (blockParamLaw B d).map (fun ξ => (ξ.1, fun ℓ => -ξ.2 ℓ)) = blockParamLaw B d := by
  let := partitionLaw_probability B d
  let := blockBaselineLaw_probability B
  change (blockParamLaw B d).map (Prod.map id (fun U ℓ => -U ℓ)) = _
  rw [blockParamLaw, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
    Measure.map_id, blockBaselineLaw_map_neg]

/-- Reversing the sign and the baselines negates every response, while preserving the
complete retained graph and all observed treatment coordinates.  [For the stated data and conditions](hyp:n,B,d,h,ξ,ω), [the stated conclusion holds](goal). -/
-- @node: block_record_sign_reflection
lemma block_record_sign_reflection (n B d : ℕ) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) (ω : Assign (Fin n) × Audit (Fin n)) :
    recordOf (blockSchedule n B d false h (ξ.1, fun ℓ => -ξ.2 ℓ)) ω =
      let o := recordOf (blockSchedule n B d true h ξ) ω
      (o.1, o.2.1, fun i => -o.2.2 i) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext i
  simp only [recordOf, potentialOutcome, blockSchedule, signOf, Bool.false_eq_true,
    if_false, if_true, zero_mul, add_zero, inNbhd]
  rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro ℓ _
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- The entire negative-sign record law is the response reflection of the positive-sign law.  [For the stated data and conditions](hyp:n,B,d,h,D), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_sign_reflection
lemma blockMixtureLawOf_sign_reflection (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    (blockMixtureLawOf n B d D true h).map
      (fun o => (o.1, o.2.1, fun i => -o.2.2 i)) = blockMixtureLawOf n B d D false h := by
  let π := blockParamLaw B d
  let := partitionLaw_probability B d
  let := blockBaselineLaw_probability B
  let : IsProbabilityMeasure π := by dsimp [π, blockParamLaw]; infer_instance
  let f := fun ξ : SourcePartition B d × (Fin B → ℝ) => (ξ.1, fun ℓ => -ξ.2 ℓ)
  have hf : Measurable f := by fun_prop
  have hpi : π.map f = π := blockParamLaw_map_neg B d
  have hprod : (π.prod D).map (Prod.map f id) = π.prod D := by
    rw [← Measure.map_prod_map _ _ hf measurable_id, hpi, Measure.map_id]
  rw [blockMixtureLawOf, mixtureLaw_eq_product_map D _ _
    (block_record_measurable n B d true h),
    Measure.map_map (by fun_prop) (block_record_measurable n B d true h)]
  rw [blockMixtureLawOf, mixtureLaw_eq_product_map D _ _
    (block_record_measurable n B d false h), ← hprod,
    Measure.map_map (block_record_measurable n B d false h) (hf.prodMap measurable_id)]
  congr 1
  funext x
  exact (block_record_sign_reflection n B d h x.1 x.2).symm

/-- Averaging identical recipients commutes with reflection of every outcome.  [For the stated data and conditions](hyp:n,B,d,o), [the stated conclusion holds](goal). -/
-- @node: distinctResponses_neg
lemma distinctResponses_neg (n B d : ℕ) (o : Record (Fin n)) :
    distinctResponses n B d (o.1, o.2.1, fun i => -o.2.2 i) =
      fun ℓ => -distinctResponses n B d o ℓ := by
  funext ℓ
  simp [distinctResponses, Finset.sum_neg_distrib]

/-- Response reflection preserves the full detailed retained-graph coordinate and assignments
in the reduced experiment.  [For the stated data and conditions](hyp:n,B,d,h,D), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_sign_reflection
lemma reducedBlockLaw_sign_reflection (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    (reducedBlockLaw n B d D true h).map
      (fun x => (x.1, x.2.1, fun ℓ => -x.2.2 ℓ)) = reducedBlockLaw n B d D false h := by
  rw [reducedBlockLaw, reducedBlockLaw, ← blockMixtureLawOf_sign_reflection n B d h D,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext o
  simp only [Function.comp_apply, distinctResponses_neg]

/-- Conditioning on any complete retained graph commutes with response reflection.  [For the stated data and conditions](hyp:n,B,d,h,D,H), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_sign_reflection
lemma conditionalBlockLaw_sign_reflection (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (H : OffDiag (Fin n) → Bool) :
    (conditionalBlockLaw n B d D true h H).map
      (fun x => (x.1, fun ℓ => -x.2 ℓ)) = conditionalBlockLaw n B d D false h H := by
  rw [conditionalBlockLaw, conditionalBlockLaw, Measure.map_smul,
    ← reducedBlockLaw_sign_reflection n B d h D,
    Measure.restrict_map (by fun_prop) (by measurability),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Reflecting every response preserves the uniform-sign reference density.  [For the stated data and conditions](hyp:d,h,w), [the stated conclusion holds](goal). -/
-- @node: refDensity_neg
lemma refDensity_neg (d : ℕ) (h w : ℝ) : refDensity d h (-w) = refDensity d h w := by
  classical
  let e : (Fin d → Bool) ≃ (Fin d → Bool) :=
    { toFun := fun ε j => !(ε j)
      invFun := fun ε j => !(ε j)
      left_inv := fun ε => by funext j; simp
      right_inv := fun ε => by funext j; simp }
  have hsign (b : Bool) : signOf (!b) = -signOf b := by cases b <;> norm_num [signOf]
  have hrow (ε : Fin d → Bool) : rowDensity d h ε (-w) = rowDensity d h (e ε) w := by
    have hsum : (∑ j, signOf ((e ε) j)) = -(∑ j, signOf (ε j)) := by
      simp only [e, Equiv.coe_fn_mk, hsign, Finset.sum_neg_distrib]
    rw [rowDensity, rowDensity, hsum]
    have he : -w - h / (2 * d) * (∑ j, signOf (ε j)) =
        -(w - h / (2 * d) * -(∑ j, signOf (ε j))) := by ring
    rw [he, cosSqDensity_neg]
  unfold refDensity
  congr 1
  exact Fintype.sum_equiv e _ _ hrow

/-- Reflecting a reference response preserves its law.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: block_referenceRow_map_neg
lemma block_referenceRow_map_neg (d : ℕ) (h : ℝ) :
    (volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))).map
      (fun w : ℝ => -w) = volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w)) := by
  have ht := Causalean.Mathlib.MeasureTheory.map_withDensity_comp_measurableEquiv
    (MeasurableEquiv.neg ℝ) (Measure.measurePreserving_neg volume)
    (fun w => ENNReal.ofReal (refDensity d h w))
  simpa [Function.comp_def, refDensity_neg] using ht

/-- The independent reference responses are jointly invariant under reflection.  [For the stated data and conditions](hyp:B,d,h), [the stated conclusion holds](goal). -/
-- @node: block_referencePi_map_neg
lemma block_referencePi_map_neg (B d : ℕ) (h : ℝ) :
    (Measure.pi (fun _ : Fin B => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w)))).map (fun y ℓ => -y ℓ) =
    Measure.pi (fun _ : Fin B => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))) := by
  let := referenceRowLaw_probability d h
  let : IsProbabilityMeasure ((volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))).map (fun w : ℝ => -w)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_map_pi (f := fun _ w => -w) (fun _ => by fun_prop)]
  simp_rw [block_referenceRow_map_neg]

/-- The full reference retains all treatment coordinates when reflecting the responses.  [For the stated data and conditions](hyp:n,B,d,h,D), [the stated conclusion holds](goal). -/
-- @node: hiddenReferenceLaw_map_neg
lemma hiddenReferenceLaw_map_neg (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    (hiddenReferenceLaw n B d D h).map (fun x => (x.1, fun ℓ => -x.2 ℓ)) =
      hiddenReferenceLaw n B d D h := by
  let := referenceRowLaw_probability d h
  change (hiddenReferenceLaw n B d D h).map (Prod.map id (fun y ℓ => -y ℓ)) = _
  rw [hiddenReferenceLaw, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
    Measure.map_id, block_referencePi_map_neg]

/-- The reference consists of independent probability responses and the actual assignment law.  [For the stated data and conditions](hyp:n,B,d,h,D), [the stated conclusion holds](goal). -/
-- @node: hiddenReferenceLaw_probability
lemma hiddenReferenceLaw_probability (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (hiddenReferenceLaw n B d D h) := by
  let := referenceRowLaw_probability d h
  let : IsProbabilityMeasure (D.map Prod.fst) := Measure.isProbabilityMeasure_map (by fun_prop)
  unfold hiddenReferenceLaw
  infer_instance

/-- The two conditional sign laws have equal chi-squared divergence against the actual
assignment-reference product, by measurable response reflection.  [For the stated data and conditions](hyp:n,B,d,h,D,H,hH), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_chiSq_sign_eq
lemma conditionalBlockLaw_chiSq_sign_eq (n B d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (H : OffDiag (Fin n) → Bool) (hH : retainedGraphMarginal n B d D {H} ≠ 0) :
    Causalean.Stat.chiSqDiv (conditionalBlockLaw n B d D false h H)
      (hiddenReferenceLaw n B d D h) = hiddenChiSq n B d D h H := by
  let := conditionalBlockLaw_probability n B d D true h H hH
  let := hiddenReferenceLaw_probability n B d h D
  let e := (MeasurableEquiv.refl (Assign (Fin n))).prodCongr
    (MeasurableEquiv.piCongrRight (fun _ : Fin B => MeasurableEquiv.neg ℝ))
  have he := Causalean.Stat.chiSqDiv_map_measurableEquiv e
    (conditionalBlockLaw n B d D true h H) (hiddenReferenceLaw n B d D h)
  change Causalean.Stat.chiSqDiv
    ((conditionalBlockLaw n B d D true h H).map (fun x => (x.1, fun ℓ => -x.2 ℓ)))
    ((hiddenReferenceLaw n B d D h).map (fun x => (x.1, fun ℓ => -x.2 ℓ))) = _ at he
  rwa [conditionalBlockLaw_sign_reflection, hiddenReferenceLaw_map_neg] at he

/-- The negative-sign conditional law is also dominated by the reference, since reflection
preserves that reference and transports the actual positive-sign law.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,D,H), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_false_absolutelyContinuous
lemma conditionalBlockLaw_false_absolutelyContinuous (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d D false h H ≪ hiddenReferenceLaw n B d D h := by
  have hac := (conditionalBlockLaw_absolutelyContinuous_of_probability n B d hd hfit D h H).map
    (f := fun x => (x.1, fun ℓ => -x.2 ℓ)) (by fun_prop)
  rwa [conditionalBlockLaw_sign_reflection, hiddenReferenceLaw_map_neg] at hac

/-- On any positive-probability detailed graph, square-integrable conditional likelihoods
convert the common chi-squared divergence into the conditional testing bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,D,H,hH,hi), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_tvDist_le_sqrt_chiSq
lemma conditionalBlockLaw_tvDist_le_sqrt_chiSq (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (H : OffDiag (Fin n) → Bool) (hH : retainedGraphMarginal n B d D {H} ≠ 0)
    (hi : ∀ σ : Bool, Integrable (fun x =>
      (((conditionalBlockLaw n B d D σ h H).rnDeriv (hiddenReferenceLaw n B d D h) x).toReal
        - 1) ^ 2) (hiddenReferenceLaw n B d D h)) :
    Causalean.Stat.tvDist (conditionalBlockLaw n B d D true h H)
      (conditionalBlockLaw n B d D false h H) ≤ Real.sqrt (hiddenChiSq n B d D h H) := by
  let := conditionalBlockLaw_probability n B d D true h H hH
  let := conditionalBlockLaw_probability n B d D false h H hH
  let := hiddenReferenceLaw_probability n B d h D
  exact block_tvDist_le_sqrt_common_chiSq _ _ _
    (conditionalBlockLaw_absolutelyContinuous_of_probability n B d hd hfit D h H)
    (conditionalBlockLaw_false_absolutelyContinuous n B d hd hfit h D H)
    (hi true) (hi false) (conditionalBlockLaw_chiSq_sign_eq n B d h D H hH)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
