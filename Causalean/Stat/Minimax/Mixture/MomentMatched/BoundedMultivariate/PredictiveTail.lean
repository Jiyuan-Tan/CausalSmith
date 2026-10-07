module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PredictiveEnvelope

/-!
# Integrated marked-Poisson Taylor tails

This module moves the nonnegative four-rate Taylor envelope through finite-support priors and reindexes it by observed count triples.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- Use the finite atomic support to commute the four-index sum with the
  prior integral. On supported points, the preceding pointwise lemma gives
  summability and the common upper bound. Summing finitely many supported
  atoms preserves summability. Integrate the pointwise inequality and use
  `integral_const` together with the probability normalization. -/

/-- For a bounded finite prior, the integrated four-index unmatched
coefficients form a summable series bounded by the factorial tail. -/
private lemma finiteSupport_integral_eq_sum
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] (s : Finset α)
    (hs : ν (s : Set α) = 1) (f : α → ℝ) :
    (∫ x, f x ∂ν) = ∑ x ∈ s, (ν {x}).toReal * f x := by
  have hae : ∀ᵐ x ∂ν, x ∈ s :=
    (mem_ae_iff_prob_eq_one s.measurableSet).2 hs
  have hν : ν = ∑ x ∈ s, ν {x} • Measure.dirac x :=
    Measure.ae_mem_finset_iff.mp hae
  calc
    (∫ x, f x ∂ν) = ∫ x, f x ∂(∑ x ∈ s, ν {x} • Measure.dirac x) :=
      congrArg (fun μ : Measure α => ∫ x, f x ∂μ) hν
    _ = ∑ x ∈ s, ∫ y, f y ∂(ν {x} • Measure.dirac x) := by
      rw [integral_finsetSum_measure]
      intro x hx
      exact (integrable_dirac (by simp)).smul_measure (measure_ne_top ν {x})
    _ = ∑ x ∈ s, (ν {x}).toReal * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_smul_measure, integral_dirac]
      simp [smul_eq_mul]

private lemma finiteSupport_integral_tsum
    {α ι : Type*} [Countable ι] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset α, ν (s : Set α) = 1)
    (f : ι → α → ℝ) (hf : ∀ x, Summable fun r => f r x) :
    (∫ x, ∑' r, f r x ∂ν) = ∑' r, ∫ x, f r x ∂ν := by
  obtain ⟨s, hs⟩ := hfinite
  rw [finiteSupport_integral_eq_sum ν s hs]
  simp_rw [finiteSupport_integral_eq_sum ν s hs]
  rw [Summable.tsum_finsetSum (fun x hx => (hf x).mul_left _)]
  apply Finset.sum_congr rfl
  intro x hx
  exact tsum_mul_left.symm

private lemma finiteSupport_summable_integral
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset α, ν (s : Set α) = 1)
    (f : ι → α → ℝ) (hf : ∀ x, Summable fun r => f r x) :
    Summable fun r => ∫ x, f r x ∂ν := by
  classical
  obtain ⟨s, hs⟩ := hfinite
  simp_rw [finiteSupport_integral_eq_sum ν s hs]
  have hsum : ∀ t : Finset α,
      Summable fun r => ∑ x ∈ t, (ν {x}).toReal * f r x := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert x t hx ih =>
        simp only [Finset.sum_insert hx]
        exact ((hf x).mul_left _).add ih
  exact hsum s

private lemma finiteSupport_integrable
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset α, ν (s : Set α) = 1) (f : α → ℝ) :
    Integrable f ν := by
  obtain ⟨s, hs⟩ := hfinite
  have hae : ∀ᵐ x ∂ν, x ∈ s :=
    (mem_ae_iff_prob_eq_one s.measurableSet).2 hs
  rw [Measure.ae_mem_finset_iff.mp hae, integrable_finsetSum_measure]
  intro x hx
  exact (integrable_dirac (by simp)).smul_measure (measure_ne_top ν {x})

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), and a [finitely supported probability prior with the stated bounded support](hyp:ν,hfinite,hsupport) give [a summable integrated four-index envelope bounded by the factorial tail](goal). -/
theorem tsum_integral_unmatchedEnvelopeCoeff_le_tail
    {K : ℕ} (hK : 1 ≤ K) {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b)
    (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset MarkedParam, ν (s : Set MarkedParam) = 1)
    (hsupport : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
      0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1) :
    Summable (fun q : Fin 4 → ℕ =>
      ∫ θ, if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3)
      else 0 ∂ν) ∧
    (∑' q : Fin 4 → ℕ,
      ∫ θ, if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3)
      else 0 ∂ν) ≤ unmatchedTail K n b := by
  classical
  let G : Set MarkedParam := {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
    0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1}
  let F (q : Fin 4 → ℕ) (θ : MarkedParam) : ℝ :=
    if θ ∈ G then
      if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3)
      else 0
    else 0
  have hGae : ∀ᵐ θ ∂ν, θ ∈ G :=
    (mem_ae_iff_prob_eq_one (by measurability : MeasurableSet G)).2 hsupport
  have hFsum (θ : MarkedParam) : Summable (fun q => F q θ) := by
    by_cases hθ : θ ∈ G
    · exact (unmatchedEnvelopeCoeff_pointwise_le_tail hK hn θ
        hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2.1 hθ.2.2.2.2.1 hθ.2.2.2.2.2).1.congr
          (fun q => by simp [F, hθ])
    · simp [F, hθ]
  have hint (q : Fin 4 → ℕ) :
      (∫ θ, if 3 * K < q 0 + q 1 + q 2 + q 3 then
          markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3) else 0 ∂ν) =
        ∫ θ, F q θ ∂ν := by
    apply integral_congr_ae
    filter_upwards [hGae] with θ hθ
    simp [F, hθ]
  have hsum : Summable (fun q : Fin 4 → ℕ => ∫ θ, F q θ ∂ν) :=
    finiteSupport_summable_integral ν hfinite F hFsum
  constructor
  · exact hsum.congr (fun q => (hint q).symm)
  · simp_rw [hint]
    rw [← finiteSupport_integral_tsum ν hfinite F hFsum]
    calc
      (∫ θ, ∑' q, F q θ ∂ν) ≤ ∫ _θ, unmatchedTail K n b ∂ν := by
        apply integral_mono_ae
        · exact finiteSupport_integrable ν hfinite _
        · exact finiteSupport_integrable ν hfinite _
        · filter_upwards with θ
          by_cases hθ : θ ∈ G
          · simpa [F, hθ] using
              (unmatchedEnvelopeCoeff_pointwise_le_tail hK hn θ
                hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2.1
                hθ.2.2.2.2.1 hθ.2.2.2.2.2).2
          · simp [F, hθ]
            unfold unmatchedTail
            exact tsum_nonneg fun m => by split_ifs <;> positivity
      _ = unmatchedTail K n b := by simp

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), and a [finitely supported probability prior with arrival mass between 0 and b and propensity and success probability between 0 and 1](hyp:ν,hfinite,hsupport) give [that the prior-integrated envelope coefficients of total degree above 3K are summable in the Taylor index for each count triple, that their sums are summable over count triples, and that the total is at most the unmatched Taylor tail Σ over m > 3K of (2nb)ᵐ/m!](goal). -/
theorem tsum_unmatchedEnvelope_integral_le_tail
    {K : ℕ} (hK : 1 ≤ K) {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b)
    (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset MarkedParam, ν (s : Set MarkedParam) = 1)
    (hsupport : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
      0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1) :
    (∀ z : (ℕ × ℕ) × ℕ, Summable (fun t : ℕ =>
      if 3 * K < t + z.1.1 + z.1.2 + z.2 then
        ∫ θ, markedEnvelopeCoeff n θ t z.1.1 z.1.2 z.2 ∂ν
      else 0)) ∧
    Summable (fun z : (ℕ × ℕ) × ℕ => ∑' t : ℕ,
      if 3 * K < t + z.1.1 + z.1.2 + z.2 then
        ∫ θ, markedEnvelopeCoeff n θ t z.1.1 z.1.2 z.2 ∂ν
      else 0) ∧
    (∑' z : (ℕ × ℕ) × ℕ, ∑' t : ℕ,
      if 3 * K < t + z.1.1 + z.1.2 + z.2 then
        ∫ θ, markedEnvelopeCoeff n θ t z.1.1 z.1.2 z.2 ∂ν
      else 0) ≤ unmatchedTail K n b := by
  classical
  let A (q : Fin 4 → ℕ) : ℝ :=
    ∫ θ, if 3 * K < q 0 + q 1 + q 2 + q 3 then
      markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3) else 0 ∂ν
  let Z := (ℕ × ℕ) × ℕ
  let e : Z × ℕ ≃ (Fin 4 → ℕ) :=
    { toFun := fun zt => ![zt.2, zt.1.1.1, zt.1.1.2, zt.1.2]
      invFun := fun q => (((q 1, q 2), q 3), q 0)
      left_inv := by
        rintro ⟨⟨⟨u, v⟩, w⟩, t⟩
        rfl
      right_inv := by
        intro q
        funext i
        fin_cases i <;> rfl }
  let C : Z × ℕ → ℝ := fun zt =>
    if 3 * K < zt.2 + zt.1.1.1 + zt.1.1.2 + zt.1.2 then
      ∫ θ, markedEnvelopeCoeff n θ zt.2 zt.1.1.1 zt.1.1.2 zt.1.2 ∂ν
    else 0
  obtain ⟨hA, hAtail⟩ :=
    tsum_integral_unmatchedEnvelopeCoeff_le_tail hK hn hb ν hfinite hsupport
  have hcomp : A ∘ e = C := by
    funext zt
    rcases zt with ⟨⟨⟨u, v⟩, w⟩, t⟩
    by_cases hdeg : 3 * K < t + u + v + w
    · simp [A, C, e, hdeg]
    · simp [A, C, e, hdeg]
  have hC : Summable C := by
    rw [← hcomp]
    exact (e.summable_iff).2 hA
  have hinner : ∀ z : Z, Summable (fun t : ℕ => C (z, t)) := by
    intro z
    exact hC.comp_injective (fun _ _ h => congrArg Prod.snd h)
  have houter : Summable (fun z : Z => ∑' t : ℕ, C (z, t)) := hC.prod
  have hCform (z : Z) (t : ℕ) :
      C (z, t) = if 3 * K < t + z.1.1 + z.1.2 + z.2 then
        ∫ θ, markedEnvelopeCoeff n θ t z.1.1 z.1.2 z.2 ∂ν else 0 := by
    rfl
  constructor
  · intro z
    exact (hinner z).congr (fun t => hCform z t)
  · constructor
    · exact houter.congr (fun z => tsum_congr (hCform z))
    · have hreindex : (∑' z : Z, ∑' t : ℕ, C (z, t)) = ∑' q, A q := by
        rw [← hC.tsum_prod, ← hcomp]
        exact e.tsum_eq A
      simpa only [hCform] using hreindex.trans_le hAtail

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
