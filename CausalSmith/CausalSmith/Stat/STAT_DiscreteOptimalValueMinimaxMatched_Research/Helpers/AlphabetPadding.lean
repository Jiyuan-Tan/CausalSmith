import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.L1Depoissonization
import Mathlib.MeasureTheory.Measure.Prod

/-! Zero-mass alphabet padding for the paired fixed-sample L1 experiment. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- [extending a function by zero along an injection preserves its finite sum](goal). -/
lemma sum_function_extend_embedding_zero {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (f : α → ℝ) :
    ∑ y, Function.extend e f 0 y = ∑ x, f x := by
  classical
  calc
    ∑ y, Function.extend e f 0 y =
        ∑ y ∈ Finset.univ.image e, Function.extend e f 0 y := by
      symm
      apply Finset.sum_subset
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
      intro y _ hy
      have hnot : ¬∃ x, e x = y := by
        intro hex
        obtain ⟨x, hx⟩ := hex
        apply hy
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
      rw [Function.extend_apply' _ _ _ hnot]
      rfl
    _ = ∑ x, Function.extend e f 0 (e x) :=
      Finset.sum_image e.injective.injOn
    _ = ∑ x, f x := by
      apply Fintype.sum_congr
      intro x
      exact Function.Injective.extend_apply e.injective f 0 x

/-- For [the specified alphabet embedding certificate, discrete law](hyp:hsd,P), the [padded simplex point extends a smaller probability vector by zero on the added alphabet cells](goal). -/
noncomputable def padSimplex {s d : ℕ} (hsd : s ≤ d)
    (P : ProbabilitySimplex s) : ProbabilitySimplex d := by
  let e : Fin s ↪ Fin d := ⟨Fin.castLE hsd, Fin.castLE_injective hsd⟩
  let f : Fin d → ℝ := Function.extend e P.1 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    dsimp [f]
    unfold Function.extend
    split
    · exact P.2.1 _
    · exact le_rfl
  · dsimp [f]
    rw [sum_function_extend_embedding_zero, P.2.2]

/-- If [the stated sd condition holds](hyp:hsd), then [the stated pad simplex l1 distance relation holds](goal). -/
lemma padSimplex_l1Distance {s d : ℕ} (hsd : s ≤ d)
    (P Q : ProbabilitySimplex s) :
    l1Distance (padSimplex hsd P) (padSimplex hsd Q) = l1Distance P Q := by
  unfold l1Distance padSimplex
  dsimp
  let e : Fin s ↪ Fin d := ⟨Fin.castLE hsd, Fin.castLE_injective hsd⟩
  change (∑ x, |Function.extend e P.1 0 x - Function.extend e Q.1 0 x|) = _
  rw [← sum_function_extend_embedding_zero e (fun i => |P.1 i - Q.1 i|)]
  apply Fintype.sum_congr
  intro x
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [Function.Injective.extend_apply e.injective,
      Function.Injective.extend_apply e.injective,
      Function.Injective.extend_apply e.injective]
  · rw [Function.extend_apply' _ _ _ hx,
      Function.extend_apply' _ _ _ hx, Function.extend_apply' _ _ _ hx]
    simp

/-- If [the stated sd condition holds](hyp:hsd), then [the stated simplex probability mass pad simplex relation holds](goal). -/
lemma simplexPMF_padSimplex {s d : ℕ} (hsd : s ≤ d) (P : ProbabilitySimplex s) :
    simplexPMF (padSimplex hsd P) =
      PMF.map (Fin.castLE hsd) (simplexPMF P) := by
  classical
  apply PMF.ext
  intro x
  simp only [simplexPMF, PMF.ofFintype_apply, PMF.map_apply]
  unfold padSimplex
  dsimp
  by_cases hx : ∃ i : Fin s, x = Fin.castLE hsd i
  · obtain ⟨i, rfl⟩ := hx
    rw [Function.Injective.extend_apply (Fin.castLE_injective hsd)]
    simp
  · rw [Function.extend_apply']
    · rw [Pi.zero_apply, ENNReal.ofReal_zero]
      symm
      rw [ENNReal.tsum_eq_zero]
      intro a
      rw [if_neg (fun ha => hx ⟨a, ha⟩)]
    · simpa [eq_comm] using hx

/-- If [the stated sd condition holds](hyp:hsd), then [the stated map fixed pair single pad simplex relation holds](goal). -/
lemma map_fixedPairSingle_padSimplex {s d : ℕ} (hsd : s ≤ d)
    (P Q : ProbabilitySimplex s) :
    Measure.map (Prod.map (Fin.castLE hsd) (Fin.castLE hsd))
        ((simplexPMF P).toMeasure.prod (simplexPMF Q).toMeasure) =
      (simplexPMF (padSimplex hsd P)).toMeasure.prod
        (simplexPMF (padSimplex hsd Q)).toMeasure := by
  rw [simplexPMF_padSimplex, simplexPMF_padSimplex]
  rw [← PMF.toMeasure_map (Fin.castLE hsd) (simplexPMF P) (measurable_of_finite _),
    ← PMF.toMeasure_map (Fin.castLE hsd) (simplexPMF Q) (measurable_of_finite _)]
  exact (Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _)).symm

/-- For [the specified alphabet embedding certificate, data point or sample](hyp:hsd,z), the [padded paired sample embeds both coordinates of every smaller-alphabet observation into the larger alphabet](goal). -/
noncomputable def padPairSample {n s d : ℕ} (hsd : s ≤ d)
    (z : Fin n → Fin s × Fin s) : Fin n → Fin d × Fin d :=
  fun i => (Fin.castLE hsd (z i).1, Fin.castLE hsd (z i).2)

/-- If [the stated sd condition holds](hyp:hsd), then [zero-padding both distributions and the paired sample preserves fixed-sample L1 risk](goal). -/
lemma fixedL1Risk_padSimplex {n s d : ℕ} (hsd : s ≤ d)
    (est : FixedL1Estimator n d) (P Q : ProbabilitySimplex s) :
    fixedL1Risk n
        ⟨fun z => est.1 (padPairSample hsd z), measurable_of_finite _⟩ (P, Q) =
      fixedL1Risk n est (padSimplex hsd P, padSimplex hsd Q) := by
  unfold fixedL1Risk Causalean.Stat.sqRisk fixedPairLaw
  rw [padSimplex_l1Distance]
  let mu := (simplexPMF P).toMeasure.prod (simplexPMF Q).toMeasure
  have hi := Causalean.Stat.integral_comp_finCoordinatewise n mu
    (phi := Prod.map (Fin.castLE hsd) (Fin.castLE hsd)) (measurable_of_finite _)
    (fun z => (est.1 z - l1Distance P Q) ^ 2) (measurable_of_finite _)
  rw [map_fixedPairSingle_padSimplex hsd P Q] at hi
  have hfun : (fun z : Fin n → Fin s × Fin s =>
      fun i => Prod.map (Fin.castLE hsd) (Fin.castLE hsd) (z i)) =
      padPairSample hsd := by
    funext z i
    rfl
  convert hi using 1 <;> simp only [mu]
  congr 1

/-- For [the specified smaller alphabet size, nonempty-alphabet certificate](hyp:s,hs), the [simplex point mass places all probability on the first cell of a nonempty alphabet](goal). -/
noncomputable def simplexPointMass (s : ℕ) (hs : 1 ≤ s) : ProbabilitySimplex s := by
  let z : Fin s := ⟨0, hs⟩
  refine ⟨fun x => if x = z then 1 else 0, ?_, ?_⟩
  · intro x
    dsimp
    split <;> positivity
  · simp [z]

/-- If [the stated support condition holds](hyp:hs), and [the stated sd condition holds](hyp:hsd), then [fixed-sample L1 minimax risk cannot decrease when the alphabet is enlarged](goal). -/
lemma fixedL1MinimaxRisk_mono_alphabet {n s d : ℕ} (hs : 1 ≤ s) (hsd : s ≤ d) :
    fixedL1MinimaxRisk n s ≤ fixedL1MinimaxRisk n d := by
  classical
  let P0 := simplexPointMass s hs
  letI : Nonempty (ProbabilitySimplex s × ProbabilitySimplex s) := ⟨(P0, P0)⟩
  letI : Nonempty (FixedL1Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold fixedL1MinimaxRisk
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk fun _ _ => by
      unfold fixedL1Risk Causalean.Stat.sqRisk
      positivity)
  intro est
  let estSmall : FixedL1Estimator n s :=
    ⟨fun z => est.1 (padPairSample hsd z), measurable_of_finite _⟩
  refine ⟨estSmall, ?_⟩
  apply Causalean.Stat.worstCaseRisk_le
  intro PQ
  calc
    fixedL1Risk n estSmall PQ =
        fixedL1Risk n est (padSimplex hsd PQ.1, padSimplex hsd PQ.2) :=
      fixedL1Risk_padSimplex hsd est PQ.1 PQ.2
    _ ≤ Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) est :=
      Causalean.Stat.le_worstCaseRisk (fixedL1Risk_bddAbove est) _

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
