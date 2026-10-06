module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.PatternFirstMoment
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.ZeroCases
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Nested-event ratio means for fixed-size iid samples

The unnormalised count-fibre first moment avoids division by event mass or fibre
mass. Its ratio form expresses the conditional mean on every positive count
fibre. Summing those fibres gives the fixed-size success-fraction mean.
-/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

variable {X : Type*} [MeasurableSpace X]

open Classical in
omit [MeasurableSpace X] in
private theorem count_eq_card (B : Set X) {n : ℕ} (x : Fin n → X) :
    iidEventCount B x = ((Finset.univ.filter (fun i => x i ∈ B)).card : ℝ) := by
  classical
  exact Finset.sum_boole _ _

open Classical in
omit [MeasurableSpace X] in
private theorem mem_pattern_iff (B : Set X) {n : ℕ} (U : Finset (Fin n))
    (x : Fin n → X) :
    x ∈ Set.univ.pi (fun i => if i ∈ U then B else Bᶜ) ↔
      Finset.univ.filter (fun i => x i ∈ B) = U := by
  classical
  simp only [Set.mem_univ_pi]
  constructor
  · intro hx
    ext i
    by_cases hi : i ∈ U
    · have h := hx i
      simpa [hi] using h
    · have h := hx i
      simp only [hi, if_false, Set.mem_compl_iff] at h
      simp [hi, h]
  · intro hx i
    have hi : x i ∈ B ↔ i ∈ U := by
      have := Finset.ext_iff.mp hx i
      simpa using this
    by_cases h : i ∈ U <;> simp [h, hi]

private theorem measurable_pattern {B : Set X} (hB : MeasurableSet B)
    {n : ℕ} (U : Finset (Fin n)) :
    MeasurableSet (Set.univ.pi (fun i => if i ∈ U then B else Bᶜ)) := by
  classical
  apply (measurableSet_pi Set.countable_univ).mpr
  left
  intro i _
  split_ifs
  · exact hB
  · exact hB.compl

omit [MeasurableSpace X] in
private theorem disjoint_patterns (B : Set X) {n : ℕ} (U V : Finset (Fin n))
    (hUV : U ≠ V) :
    Disjoint (Set.univ.pi (fun i => if i ∈ U then B else Bᶜ))
      (Set.univ.pi (fun i => if i ∈ V then B else Bᶜ)) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hUV ((mem_pattern_iff B U x).mp hx |>.symm.trans
    ((mem_pattern_iff B V x).mp hy))

private theorem integrable_count (P : Measure X) [IsProbabilityMeasure P]
    {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    Integrable (iidEventCount A) (Measure.pi (fun _ : Fin n => P)) := by
  apply Integrable.of_mem_Icc 0 (n : ℝ)
  · exact (measurable_iidEventCount hA n).aemeasurable
  · exact Filter.Eventually.of_forall fun x => eventCount_bounds A (fixedSizeEmbed n x)

/-- Under [an observation probability law](hyp:P), [a tuple size and count-fibre index](hyp:n,k),
two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), and [containment of the
first in the second](hyp:hAB), [the iid smaller-event count moment on that fibre satisfies
the division-free ratio identity](goal). -/
theorem iid_nested_count_fibre_first_moment
    (P : Measure X) [IsProbabilityMeasure P] (n k : ℕ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    P.real B *
        (∫ x : Fin n → X, iidEventCount A x
          ∂(Measure.pi (fun _ : Fin n => P)).restrict
            {x | iidEventCount B x = (k : ℝ)}) =
      P.real A * (k : ℝ) *
        (Measure.pi (fun _ : Fin n => P)).real {x | iidEventCount B x = (k : ℝ)} := by
  /- Use iid_nested_pattern_first_moment from PatternFirstMoment.lean.
  For U : Finset (Fin n), the corresponding rectangle prescribes exactly those
  coordinates in B. These rectangles are pairwise disjoint and measurable;
  iidEventCount B is U.card on each. The k-fibre is their finite union over
  U.card = k. Sum restricted integrals with integral_biUnion_finset and sum
  probabilities with measureReal_biUnion_finset. This handles k=0 and k>n
  without dividing by P(B) or by k. Keep the finite set manipulations in private
  helpers if they would make this proof bulky; do not duplicate the rectangle
  integral argument.

  `integral_biUnion_finset` takes measurability, pairwise disjointness, and
  IntegrableOn on every piece; measureReal_biUnion_finset takes the same
  disjointness/measurability and finite masses (automatic here).
  A convenient index is Finset.univ.filter (fun U : Finset (Fin n) => U.card = k).
  For a tuple x, use Ux := Finset.univ.filter (fun i => x i ∈ B).
  Expanding iidEventCount gives iidEventCount B x = (Ux.card : ℝ).
  This proves the union equality and the constant count on each rectangle.
  Distinct patterns differ at a coordinate, so their rectangles are disjoint.
  Each restricted count is integrable by its measurable bound [0,n], using
  eventCount_bounds on fixedSizeEmbed. All arguments also cover n=0 and k>n. -/
  classical
  let T := Finset.univ.filter (fun U : Finset (Fin n) => U.card = k)
  let R := fun U : Finset (Fin n) => Set.univ.pi (fun i => if i ∈ U then B else Bᶜ)
  have hset : {x : Fin n → X | iidEventCount B x = (k : ℝ)} = ⋃ U ∈ T, R U := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨Finset.univ.filter (fun i => x i ∈ B), ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact_mod_cast (count_eq_card B x).symm.trans hx
      · exact (mem_pattern_iff B _ x).mpr rfl
    · rintro ⟨U, hU, hx⟩
      have hcard : U.card = k := (Finset.mem_filter.mp hU).2
      rw [count_eq_card B x, (mem_pattern_iff B U x).mp hx, hcard]
  have hm : ∀ U ∈ T, MeasurableSet (R U) := fun U _ => measurable_pattern hB U
  have hd : Set.PairwiseDisjoint (↑T) R := fun U _ V _ hUV => disjoint_patterns B U V hUV
  rw [hset, integral_biUnion_finset T hm hd
    (fun _ _ => (integrable_count P hA n).integrableOn),
    measureReal_biUnion_finset hd hm, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hcard : U.card = k := (Finset.mem_filter.mp hU).2
  simpa [R, hcard] using iid_nested_pattern_first_moment P n U hA hB hAB

/-- Under [an observation probability law](hyp:P), [a tuple size](hyp:n), [a positive
containing-event count](hyp:k,hk), two [events](hyp:A,B) with [measurable membership](hyp:hA,hB),
[containment of the first in the second](hyp:hAB), and [positive containing-event
probability](hyp:hPB), [the total success-fraction integral on that count fibre equals
the event-probability ratio times its probability](goal). -/
theorem iid_successFraction_count_fibre
    (P : Measure X) [IsProbabilityMeasure P] (n k : ℕ) (hk : 0 < k)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (hPB : 0 < P.real B) :
    (∫ x : Fin n → X, successFraction A B (fixedSizeEmbed n x)
      ∂(Measure.pi (fun _ : Fin n => P)).restrict
        {x | iidEventCount B x = (k : ℝ)}) =
      (P.real A / P.real B) *
        (Measure.pi (fun _ : Fin n => P)).real {x | iidEventCount B x = (k : ℝ)} := by
  /- The fibre is measurable by measurable_iidEventCount. Use ae_restrict_mem
  and integral_congr_ae to replace the success fraction by iidEventCount A / k
  on that fibre; the cast of hk makes its zero branch false. integral_div
  then reduces the claim to iid_nested_count_fibre_first_moment. Cancel only
  the positive real numbers k and P.real B, never the fibre probability:
  that probability may vanish even with positive event mass. -/
  classical
  have hf : MeasurableSet {x : Fin n → X | iidEventCount B x = (k : ℝ)} :=
    (measurable_iidEventCount hB n) (measurableSet_singleton _)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have heq : (fun x : Fin n → X => successFraction A B (fixedSizeEmbed n x)) =ᵐ[
      (Measure.pi (fun _ : Fin n => P)).restrict {x | iidEventCount B x = (k : ℝ)}]
      (fun x => iidEventCount A x / (k : ℝ)) := by
    filter_upwards [ae_restrict_mem hf] with x hx
    simp [successFraction, hx, hk0]
  rw [integral_congr_ae heq, integral_div]
  have hm := iid_nested_count_fibre_first_moment P n k hA hB hAB
  apply (div_eq_iff hk0).mpr
  apply (mul_left_cancel₀ hPB.ne')
  rw [← mul_assoc, hm]
  field_simp

/-- Under [an observation probability law](hyp:P), [a fixed sample size](hyp:n), two
[events](hyp:A,B) with [measurable membership](hyp:hA,hB), and [containment of the first
in the second](hyp:hAB), [containing-event probability times the iid total
success-fraction mean equals smaller-event probability times the nonempty-count
probability](goal). -/
theorem iid_successFraction_mean_mul
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    P.real B *
        (∫ x : Fin n → X, successFraction A B (fixedSizeEmbed n x)
          ∂Measure.pi (fun _ : Fin n => P)) =
      P.real A * (1 - (1 - P.real B) ^ n) := by
  /- Sum the finite count fibres k=0,...,n, using the first-moment identity
  before cancelling k>0. The k=0 branch is identically zero. One can also split
  P.real B=0 first (then P.real A=0 by measureReal_mono and nonnegativity),
  and use the ratio fibre lemma in the positive-mass branch. Integrability of
  the embedded success fraction follows from successFraction_bounds and
  measurable_successFraction.comp (measurable_fixedSizeEmbed n).
  The fibres indexed by Finset.range (n+1) partition Set.univ: again express
  the count as the real cast of the membership-filter cardinality, bounded
  by n. integral_biUnion_finset then gives the expectation sum. Summing
  the positive-fibre probabilities yields 1 minus the zero-fibre probability;
  use iid_eventCount_zero_probability for the latter. No binomial coefficient
  calculation or positivity of individual fibre probabilities is required. -/
  classical
  by_cases hPB : P.real B = 0
  · have hPA : P.real A = 0 := le_antisymm
      (by simpa [hPB] using measureReal_mono (μ := P) hAB) measureReal_nonneg
    simp [hPB, hPA]
  have hPBpos : 0 < P.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hPB)
  let μ : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
  let F : ℕ → Set (Fin n → X) := fun k => {x | iidEventCount B x = (k : ℝ)}
  let T := Finset.range (n + 1)
  let f : (Fin n → X) → ℝ := fun x => successFraction A B (fixedSizeEmbed n x)
  have hm : ∀ k ∈ T, MeasurableSet (F k) := fun k _ =>
    (measurable_iidEventCount hB n) (measurableSet_singleton _)
  have hd : Set.PairwiseDisjoint (↑T) F := by
    intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hkl
    exact_mod_cast (hx.symm.trans hy : (k : ℝ) = (l : ℝ))
  have hcover : (⋃ k ∈ T, F k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let U := Finset.univ.filter (fun i : Fin n => x i ∈ B)
    have hU : U.card ≤ n := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    exact Set.mem_iUnion.mpr ⟨U.card, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (by omega), count_eq_card B x⟩⟩
  have hi : Integrable f μ := by
    apply Integrable.of_mem_Icc 0 1
    · exact ((measurable_successFraction hA hB).comp
        (measurable_fixedSizeEmbed n)).aemeasurable
    · exact Filter.Eventually.of_forall fun x => successFraction_bounds hAB _
  have hsum : (∫ x, f x ∂μ) = ∑ k ∈ T, ∫ x in F k, f x ∂μ := by
    rw [← integral_biUnion_finset T hm hd (fun _ _ => hi.integrableOn), hcover,
      Measure.restrict_univ]
  have hprob : (∑ k ∈ T, μ.real (F k)) = 1 := by
    rw [← measureReal_biUnion_finset hd hm, hcover]
    exact probReal_univ
  have h0 : 0 ∈ T := Finset.mem_range.mpr (by omega)
  have hz : (∫ x in F 0, f x ∂μ) = 0 := by
    have heq : f =ᵐ[μ.restrict (F 0)] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem (hm 0 h0)] with x hx
      have hx0 : iidEventCount B x = 0 := by simpa [F] using hx
      simp [f, successFraction, hx0]
    rw [integral_congr_ae heq, integral_zero]
  have hpos : ∀ k ∈ T.erase 0,
      (∫ x in F k, f x ∂μ) = (P.real A / P.real B) * μ.real (F k) := by
    intro k hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero (Finset.mem_erase.mp hk).1
    exact iid_successFraction_count_fibre P n k hkpos hA hB hAB hPBpos
  have hp : (∑ k ∈ T.erase 0, μ.real (F k)) = 1 - μ.real (F 0) := by
    have he := Finset.sum_erase_add T (fun k => μ.real (F k)) h0
    rw [hprob] at he
    linarith
  have he := Finset.sum_erase_add T (fun k => ∫ x in F k, f x ∂μ) h0
  rw [hz, add_zero] at he
  change P.real B * (∫ x, f x ∂μ) = _
  rw [hsum, ← he, Finset.sum_congr rfl hpos, ← Finset.mul_sum, hp]
  have hzero : μ.real (F 0) = (1 - P.real B) ^ n := by
    simpa [μ, F] using iid_eventCount_zero_probability P n hB
  rw [hzero]
  field_simp

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean
