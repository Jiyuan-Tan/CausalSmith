module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.FuzzyPrior

/-! The event on which every treated baseline category occurs at most once. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:n,d,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def noRepeatedTreatedCell {n d : ℕ} (s : Fin n → ObsRecord d) : Prop :=
  ∀ i j : Fin n, i ≠ j → (s i).A = true → (s j).A = true → (s i).X ≠ (s j).X

/-- Given [the specified inputs and assumptions](hyp:n,d,Q,b,hpair), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_collision_union_bound
lemma largeAlphabet_collision_union_bound {n d : ℕ}
    (Q : Measure (Fin n → ObsRecord d)) [IsProbabilityMeasure Q]
    (b : ℝ)
    (hpair : ∀ i j : Fin n, i < j →
      Q.real {s | (s i).A = true ∧ (s j).A = true ∧ (s i).X = (s j).X} ≤ b) :
    Q.real {s | ¬ noRepeatedTreatedCell s} ≤ (n.choose 2 : ℝ) * b := by
  classical
  let pairs := (Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
    (fun ij => ij.1 < ij.2)
  let events (ij : Fin n × Fin n) : Set (Fin n → ObsRecord d) :=
    {s | (s ij.1).A = true ∧ (s ij.2).A = true ∧ (s ij.1).X = (s ij.2).X}
  have hcover : {s | ¬ noRepeatedTreatedCell s} ⊆ ⋃ ij ∈ pairs, events ij := by
    intro s hs
    simp only [Set.mem_ofPred_eq, noRepeatedTreatedCell, not_forall,
      not_not] at hs
    obtain ⟨i, j, hij, hi, hj, hx⟩ := hs
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Set.mem_iUnion.mpr ⟨(i, j), Set.mem_iUnion.mpr
        ⟨by simp [pairs, hlt], ⟨hi, hj, hx⟩⟩⟩
    · exact Set.mem_iUnion.mpr ⟨(j, i), Set.mem_iUnion.mpr
        ⟨by simp [pairs, hgt], ⟨hj, hi, hx.symm⟩⟩⟩
  calc
    Q.real {s | ¬ noRepeatedTreatedCell s} ≤ Q.real (⋃ ij ∈ pairs, events ij) :=
      measureReal_mono hcover (measure_ne_top Q _)
    _ ≤ ∑ ij ∈ pairs, Q.real (events ij) := measureReal_biUnion_finset_le pairs events
    _ ≤ ∑ _ij ∈ pairs, b := by
      apply Finset.sum_le_sum
      intro ij hij
      exact hpair ij.1 ij.2 (by simpa [pairs] using hij)
    _ = (n.choose 2 : ℝ) * b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      simpa [pairs] using congrArg (fun k : ℕ => (k : ℝ))
        (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

/-- Given [the specified inputs and assumptions](hyp:Z,Q₀,Q₁,E,hmatch), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_tv_le_collision_mass
lemma largeAlphabet_tv_le_collision_mass
    {Z : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q₀ Q₁ : Measure Z) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (E : Set Z) (hmatch : ∀ z ∈ E, Q₀.real {z} = Q₁.real {z}) :
    Causalean.Stat.tvDist Q₀ Q₁ ≤ (Q₀.real Eᶜ + Q₁.real Eᶜ) / 2 := by
  classical
  let _ := Fintype.ofFinite Z
  have hmass (Q : Measure Z) [IsProbabilityMeasure Q] :
      Q.real Eᶜ = ∑ z : Z, Eᶜ.indicator (fun z => Q.real {z}) z := by
    simpa only [tsum_fintype] using
      Causalean.Stat.probability_measureReal_eq_tsum_singletons Q Eᶜ (by measurability)
  have hsum : (∑ z : Z, |Q₀.real {z} - Q₁.real {z}|) ≤
      Q₀.real Eᶜ + Q₁.real Eᶜ := by
    rw [hmass Q₀, hmass Q₁, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : z ∈ E
    · simp [hmatch z hz, Set.indicator, hz]
    · simp only [Set.mem_compl_iff, hz, not_false_eq_true, Set.indicator_of_mem]
      apply abs_le.mpr
      constructor <;> linarith [measureReal_nonneg (μ := Q₀) (s := {z}),
        measureReal_nonneg (μ := Q₁) (s := {z})]
  have htv := Causalean.Stat.tvDist_le_half_tsum_singleton_abs Q₀ Q₁
  rw [tsum_fintype] at htv
  exact htv.trans (by linarith)

/-- Given [the specified inputs and assumptions](hyp:n,d,Q₀,Q₁,hmatch,hcollision₀,hcollision₁,κ,T,hT), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_collision_testing
lemma largeAlphabet_collision_testing
    {n d : ℕ} (Q₀ Q₁ : Measure (Fin n → ObsRecord d))
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (hmatch : ∀ s, noRepeatedTreatedCell s → Q₀.real {s} = Q₁.real {s})
    (hcollision₀ : Q₀.real {s | ¬ noRepeatedTreatedCell s} ≤ 1 / 8192)
    (hcollision₁ : Q₁.real {s | ¬ noRepeatedTreatedCell s} ≤ 1 / 8192)
    (κ : BoundedKernel (Fin n → ObsRecord d))
    (T : Set ((Fin n → ObsRecord d) × ℝ)) (hT : MeasurableSet T) :
    1 - (1 / 8192 : ℝ) ≤ (Q₀ ⊗ₘ κ.1).real T + (Q₁ ⊗ₘ κ.1).real Tᶜ := by
  let : IsMarkovKernel κ.1 := κ.2.1
  have htv := largeAlphabet_tv_le_collision_mass Q₀ Q₁
    {s | noRepeatedTreatedCell s} hmatch
  have hbudget : Causalean.Stat.tvDist Q₀ Q₁ ≤ 1 / 8192 := by
    change Causalean.Stat.tvDist Q₀ Q₁ ≤
      (Q₀.real {s | ¬ noRepeatedTreatedCell s} +
        Q₁.real {s | ¬ noRepeatedTreatedCell s}) / 2 at htv
    linarith
  exact (sub_le_sub_left hbudget 1).trans
    ((randomized_kernel_tv_comparison Q₀ Q₁ κ.1).2.2.1 T hT)

end CausalSmith.Stat.MarRareqLogfrontier
