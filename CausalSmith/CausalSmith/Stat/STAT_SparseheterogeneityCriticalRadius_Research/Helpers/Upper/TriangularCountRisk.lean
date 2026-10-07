module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.TriangularTsum
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Representation

/-! A bounded nonnegative loss over two Poisson samples dominates every
finite triangular collection of its fixed-count fibres. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- keep: reusable triangular fixed-count to Poisson risk transfer theorem
lemma triangular_fixedCount_risk_le_poisson
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (pi : Measure T) [IsProbabilityMeasure pi]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) (r : ℕ)
    (L : T × (FiniteSample X × FiniteSample X) → ℝ)
    (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hL0 : ∀ z, 0 ≤ L z) (hLC : ∀ z, L z ≤ C) :
    (∑ u ∈ Finset.range (r + 1),
      ∑ v ∈ Finset.range (r - u + 1),
        (poissonMeasure lam).real ({u} : Set ℕ) *
          (poissonMeasure lam).real ({v} : Set ℕ) *
          (∫ p : T × ((Fin u → X) × (Fin v → X)),
            L (p.1, (⟨u, p.2.1⟩, ⟨v, p.2.2⟩))
            ∂pi.prod ((Measure.pi fun _ : Fin u => Q).prod
              (Measure.pi fun _ : Fin v => Q)))) ≤
      ∫ z, L z ∂pi.prod
        ((finitePoissonSampleLaw Q lam).prod
          (finitePoissonSampleLaw Q lam)) := by
  let raw := (finitePoissonSampleLaw Q lam).prod
    (finitePoissonSampleLaw Q lam)
  let w : ℕ → ℝ := fun u => (poissonMeasure lam).real ({u} : Set ℕ)
  let B : ℕ → ℕ → ℝ := fun u v =>
    ∫ p : T × ((Fin u → X) × (Fin v → X)),
      L (p.1, (⟨u, p.2.1⟩, ⟨v, p.2.2⟩))
      ∂pi.prod ((Measure.pi fun _ : Fin u => Q).prod
        (Measure.pi fun _ : Fin v => Q))
  let a : ℕ → ℕ → ℝ := fun u v => w u * w v * B u v
  have hLint : Integrable L (pi.prod raw) := by
    apply Integrable.of_bound hL.aestronglyMeasurable C
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hL0 z)]
    exact hLC z
  have hBint (u v : ℕ) : Integrable
      (fun p : T × ((Fin u → X) × (Fin v → X)) =>
        L (p.1, (⟨u, p.2.1⟩, ⟨v, p.2.2⟩)))
      (pi.prod ((Measure.pi fun _ : Fin u => Q).prod
        (Measure.pi fun _ : Fin v => Q))) := by
    apply Integrable.of_bound
    · exact hL.aestronglyMeasurable.comp_measurable
        (measurable_fst.prodMk
          (((measurable_fixedSizeEmbed u).comp measurable_snd.fst).prodMk
            ((measurable_fixedSizeEmbed v).comp measurable_snd.snd)))
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0 _)]
      exact hLC _
  have hB0 (u v : ℕ) : 0 ≤ B u v := integral_nonneg fun p => hL0 _
  have hBle (u v : ℕ) : B u v ≤ C := by
    calc
      _ ≤ ∫ _ : T × ((Fin u → X) × (Fin v → X)), C
          ∂pi.prod ((Measure.pi fun _ : Fin u => Q).prod
            (Measure.pi fun _ : Fin v => Q)) := by
        apply integral_mono_ae (hBint u v) (integrable_const _)
        filter_upwards with p
        exact hLC _
      _ = C := by simp
  have hw0 (u : ℕ) : 0 ≤ w u := ENNReal.toReal_nonneg
  have ha0 (u v : ℕ) : 0 ≤ a u v := by
    unfold a
    exact mul_nonneg (mul_nonneg (hw0 u) (hw0 v)) (hB0 u v)
  have hwSum : Summable w := by
    unfold w
    apply summable_measure_toReal
    · intro u
      exact measurableSet_singleton u
    · intro u v huv
      exact Set.disjoint_singleton.mpr huv
  let W := ∑' u, w u
  have hW0 : 0 ≤ W := tsum_nonneg hw0
  have hinner (u : ℕ) : Summable (a u) := by
    let major : ℕ → ℝ := fun v => (w u * C) * w v
    have hmajor : Summable major := hwSum.mul_left (w u * C)
    refine Summable.of_nonneg_of_le (ha0 u) ?_ hmajor
    intro v
    change a u v ≤ major v
    · unfold a major
      calc
        w u * w v * B u v ≤ w u * w v * C :=
          mul_le_mul_of_nonneg_left (hBle u v) (mul_nonneg (hw0 u) (hw0 v))
        _ = w u * C * w v := by ring
  have hinnerLe (u : ℕ) : (∑' v, a u v) ≤ (w u * C) * W := by
    have hmajor : Summable (fun v => (w u * C) * w v) :=
      hwSum.mul_left (w u * C)
    calc
      _ ≤ ∑' v, (w u * C) * w v := by
        apply Summable.tsum_le_tsum
        · intro v
          unfold a
          calc
            w u * w v * B u v ≤ w u * w v * C :=
              mul_le_mul_of_nonneg_left (hBle u v)
                (mul_nonneg (hw0 u) (hw0 v))
            _ = w u * C * w v := by ring
        · exact hinner u
        · exact hmajor
      _ = (w u * C) * W := by rw [tsum_mul_left]
  have houter : Summable (fun u => ∑' v, a u v) := by
    let major : ℕ → ℝ := fun u => (C * W) * w u
    have hmajor : Summable major := hwSum.mul_left (C * W)
    apply Summable.of_nonneg_of_le
    · intro u
      exact tsum_nonneg (ha0 u)
    · intro u
      calc
        _ ≤ (w u * C) * W := hinnerLe u
        _ = major u := by unfold major; ring
    · exact hmajor
  have htri := triangular_sum_le_iterated_tsum r a ha0 hinner houter
  have hfInt : Integrable (fun p : FiniteSample X × FiniteSample X =>
      ∫ t, L (t, p) ∂pi) raw := hLint.integral_prod_right
  have hmix := Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_pair_count_mixture
    Q Q lam lam (fun p : FiniteSample X × FiniteSample X =>
      ∫ t, L (t, p) ∂pi) hfInt
  have hseries : (∑' u, ∑' v, a u v) = ∫ z, L z ∂pi.prod raw := by
    rw [integral_prod_symm L hLint]
    rw [hmix]
    congr 1
    funext u
    congr 1
    funext v
    unfold a B w
    congr 1
    rw [integral_prod_symm _ (hBint u v)]
  change (∑ u ∈ Finset.range (r + 1),
      ∑ v ∈ Finset.range (r - u + 1), a u v) ≤ _
  rw [← hseries]
  exact htri

/-- The finite legal count triangle is dominated by the unrestricted
product of finite-sample laws. -/
lemma triangular_finiteSample_countFibre_integral_le {n : ℕ}
    (pi : Measure ℝ) (nu : Measure (FiniteSample (SampleObs n)))
    [SFinite pi] [SFinite nu]
    (f : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) → ℝ)
    (hf : Integrable f (pi.prod (nu.prod nu)))
    (hf0 : ∀ z, 0 ≤ f z) :
    (∑ u ∈ Finset.range (postPilotSize n + 1),
      ∑ v ∈ Finset.range (postPilotSize n - u + 1),
        ∫ z, f z ∂pi.prod
          ((nu.restrict (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
           (nu.restrict (FiniteSample.count ⁻¹' ({v} : Set ℕ))))) ≤
      ∫ z, f z ∂pi.prod (nu.prod nu) := by
  classical
  let mu := pi.prod (nu.prod nu)
  let E (u v : ℕ) : Set
      (ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n))) :=
    Set.univ ×ˢ ((FiniteSample.count ⁻¹' ({u} : Set ℕ)) ×ˢ
      (FiniteSample.count ⁻¹' ({v} : Set ℕ)))
  have hE (u v : ℕ) : MeasurableSet (E u v) := by
    exact MeasurableSet.univ.prod
      ((measurable_finiteSample_count (measurableSet_singleton u)).prod
        (measurable_finiteSample_count (measurableSet_singleton v)))
  have hmeasure (u v : ℕ) :
      pi.prod
          ((nu.restrict (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
           (nu.restrict (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) =
        mu.restrict (E u v) := by
    unfold mu E
    rw [Measure.prod_restrict]
    calc
      pi.prod ((nu.prod nu).restrict
          ((FiniteSample.count ⁻¹' ({u} : Set ℕ)) ×ˢ
            (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) =
        (pi.restrict Set.univ).prod ((nu.prod nu).restrict
          ((FiniteSample.count ⁻¹' ({u} : Set ℕ)) ×ˢ
            (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) := by
          rw [Measure.restrict_univ]
      _ = _ := Measure.prod_restrict _ _
  simp_rw [hmeasure]
  have hInt (u v : ℕ) : Integrable ((E u v).indicator f) mu :=
    hf.indicator (hE u v)
  rw [show (∑ u ∈ Finset.range (postPilotSize n + 1),
      ∑ v ∈ Finset.range (postPilotSize n - u + 1),
        ∫ z, f z ∂mu.restrict (E u v)) =
      ∫ z, ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          (E u v).indicator f z ∂mu by
    simp_rw [← integral_indicator (hE _ _)]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [integral_finsetSum]
      intro v hv
      exact hInt u v
    · intro u hu
      exact integrable_finset_sum _ fun v hv => hInt u v]
  apply integral_mono_ae
  · exact integrable_finset_sum _ fun u hu =>
      integrable_finset_sum _ fun v hv => hInt u v
  · exact hf
  · filter_upwards with z
    rcases z with ⟨t, p⟩
    by_cases hlegal : p.1.count + p.2.count ≤ postPilotSize n
    · have hu : p.1.count ∈ Finset.range (postPilotSize n + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact le_trans (Nat.le_add_right _ _) hlegal
      have hv : p.2.count ∈
          Finset.range (postPilotSize n - p.1.count + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hlegal)
      rw [Finset.sum_eq_single p.1.count]
      · rw [Finset.sum_eq_single p.2.count]
        · simp [E]
        · intro v hv' hvne
          unfold E
          rw [Set.indicator_apply]
          split_ifs with hz
          · simp only [Set.mem_prod, Set.mem_univ, Set.mem_preimage,
              Set.mem_singleton_iff, true_and] at hz
            exact (hvne hz.symm).elim
          · rfl
        · exact fun hnot => (hnot hv).elim
      · intro u hu' hune
        apply Finset.sum_eq_zero
        intro v hv'
        unfold E
        rw [Set.indicator_apply]
        split_ifs with hz
        · simp only [Set.mem_prod, Set.mem_univ, Set.mem_preimage,
            Set.mem_singleton_iff, true_and] at hz
          exact (hune hz.1.symm).elim
        · rfl
      · exact fun hnot => (hnot hu).elim
    · have hzero : ∀ u ∈ Finset.range (postPilotSize n + 1),
          ∀ v ∈ Finset.range (postPilotSize n - u + 1),
            (E u v).indicator f (t, p) = 0 := by
        intro u hu v hv
        have huv : u + v ≤ postPilotSize n := by
          have hu' : u ≤ postPilotSize n := by
            rw [Finset.mem_range, Nat.lt_succ_iff] at hu
            exact hu
          have hv' : v ≤ postPilotSize n - u := by
            rw [Finset.mem_range, Nat.lt_succ_iff] at hv
            exact hv
          omega
        unfold E
        rw [Set.indicator_apply]
        split_ifs with hz
        · simp only [Set.mem_prod, Set.mem_univ, Set.mem_preimage,
            Set.mem_singleton_iff, true_and] at hz
          rcases hz with ⟨huEq, hvEq⟩
          exact (hlegal (by simpa [huEq, hvEq] using huv)).elim
        · rfl
      calc
        (∑ u ∈ Finset.range (postPilotSize n + 1),
          ∑ v ∈ Finset.range (postPilotSize n - u + 1),
            (E u v).indicator f (t, p)) = 0 := by
              apply Finset.sum_eq_zero
              intro u hu
              apply Finset.sum_eq_zero
              intro v hv
              exact hzero u hu v hv
        _ ≤ f (t, p) := hf0 (t, p)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
