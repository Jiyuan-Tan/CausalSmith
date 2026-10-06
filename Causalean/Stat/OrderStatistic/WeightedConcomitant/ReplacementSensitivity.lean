module
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ConcomitantExpectation
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ReplacementLaw

/-!
# Replacement sensitivity and variance of rank concomitants

Exact removal and insertion positions for a replaced observation, followed by
tensorized variance under an iid marked sample law.

Proof route: remove the tagged point, compare the two ordered lists of the
remaining points, then insert the old and new marks at their exact ranks.
Antitonicity makes all intermediate weight increments one-signed and
telescoping. Under continuous CDF transport, all coordinates and independent
replacements avoid ties almost surely. Apply the existing tensor variance
theorem and use rank exchangeability to sum the squared weights.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open scoped BigOperators

noncomputable section

/-- For a [marked sample](hyp:x) and [observation index](hyp:i), the
 [zero-based rank position](goal) is the inverse sorting permutation evaluated at that index. -/
def rankPosition {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) : Fin N :=
  (Tuple.sort (fun j => (x j).1)).symm i

/-- For [distinct sorting coordinates](hyp:hinj), [the zero-based rank of a tagged
 observation](goal) is the number of observations with a smaller coordinate. -/
theorem rankPosition_val_eq_card_lt {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N)
    (hinj : Function.Injective (fun j => (x j).1)) :
    (rankPosition x i).val =
      ((Finset.univ : Finset (Fin N)).filter (fun j => (x j).1 < (x i).1)).card := by
  classical
  let f : Fin N → ℝ := fun j => (x j).1
  let σ := Tuple.sort f
  have hs : StrictMono (f ∘ σ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hinj.comp σ.injective)
  have hcard :
      ((Finset.univ : Finset (Fin N)).filter (fun j => f j < f i)).card =
        ((Finset.univ : Finset (Fin N)).filter (fun j => j < σ.symm i)).card := by
    apply Finset.card_equiv σ.symm
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (hs.lt_iff_lt (a := σ.symm j) (b := σ.symm i))
  rw [hcard]
  change (σ.symm i).val = ((Finset.univ : Finset (Fin N)).filter
    (fun j : Fin N => j.val < (σ.symm i).val)).card
  rw [Fin.card_filter_val_lt]
  exact (Nat.min_eq_right (Nat.le_of_lt (σ.symm i).isLt)).symm

private theorem rankConcomitant_eq_sum_rankPosition {N : ℕ}
    (a : Fin N → ℝ) (x : Fin N → ℝ × ℝ) :
    rankConcomitant a x = ∑ j : Fin N, a (rankPosition x j) * (x j).2 := by
  let σ := Tuple.sort (fun j : Fin N => (x j).1)
  have h := Equiv.sum_comp σ (fun j : Fin N =>
    a (rankPosition x j) * (x j).2)
  simpa only [rankConcomitant, rankPosition, σ, Equiv.symm_apply_apply] using h

private theorem sum_rankPosition_weights {N : ℕ}
    (a : Fin N → ℝ) (x : Fin N → ℝ × ℝ) :
    (∑ j : Fin N, a (rankPosition x j)) = ∑ j : Fin N, a j := by
  let σ := Tuple.sort (fun j : Fin N => (x j).1)
  have h := Equiv.sum_comp σ (fun j : Fin N => a (rankPosition x j))
  simpa only [rankPosition, σ, Equiv.symm_apply_apply] using h.symm

private theorem rankPosition_replace_le {N : ℕ}
    (x : Fin N → ℝ × ℝ) (i j : Fin N) (y : ℝ × ℝ)
    (hij : j ≠ i) (hxy : (x i).1 ≤ y.1)
    (hinj : Function.Injective (fun k => (x k).1))
    (hinj' : Function.Injective
      (fun k => ((coordinateReplace i x y) k).1)) :
    rankPosition (coordinateReplace i x y) j ≤ rankPosition x j := by
  apply Fin.le_iff_val_le_val.mpr
  rw [rankPosition_val_eq_card_lt _ _ hinj', rankPosition_val_eq_card_lt _ _ hinj]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hki : k = i
  · subst k
    have hk' : y.1 < (x j).1 := by simpa [coordinateReplace, hij] using hk
    simpa using lt_of_le_of_lt hxy hk'
  · simpa [coordinateReplace, hki, hij] using hk

private theorem weighted_replacement_bound {N : ℕ}
    (c d m : Fin N → ℝ) (i : Fin N) (z : ℝ)
    (hc : ∀ j, 0 ≤ c j) (hd : ∀ j, 0 ≤ d j)
    (hm : ∀ j, m j ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hcd : ∀ j, j ≠ i → c j ≤ d j)
    (hsum : (∑ j : Fin N, c j) = ∑ j : Fin N, d j) :
    |(∑ j : Fin N, c j * m j) -
      ((∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, d j * m j) + d i * z)| ≤
      c i + d i := by
  classical
  let s : Finset (Fin N) := Finset.univ.erase i
  have htot : (∑ j ∈ s, (d j - c j)) = c i - d i := by
    rw [Finset.sum_sub_distrib]
    have hc' := Finset.sum_erase_add Finset.univ c (Finset.mem_univ i)
    have hd' := Finset.sum_erase_add Finset.univ d (Finset.mem_univ i)
    dsimp [s] at *
    linarith
  have hVlo : 0 ≤ (∑ j ∈ s, d j * m j) - (∑ j ∈ s, c j * m j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro j hj
    have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
    nlinarith [hcd j hj', (hm j).1]
  have hVhi : (∑ j ∈ s, d j * m j) - (∑ j ∈ s, c j * m j) ≤
      c i - d i := by
    rw [← Finset.sum_sub_distrib, ← htot]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
    nlinarith [hcd j hj', (hm j).1, (hm j).2]
  have hsplit := Finset.sum_erase_add Finset.univ (fun j => c j * m j)
    (Finset.mem_univ i)
  have hc0 : 0 ≤ c i * m i := mul_nonneg (hc i) (hm i).1
  have hc1 : c i * m i ≤ c i := mul_le_of_le_one_right (hc i) (hm i).2
  have hd0 : 0 ≤ d i * z := mul_nonneg (hd i) hz.1
  have hd1 : d i * z ≤ d i := mul_le_of_le_one_right (hd i) hz.2
  rw [abs_le]
  constructor
  · dsimp [s] at *
    linarith only [hVhi, hsplit, hc0, hd1, hd i]
  · dsimp [s] at *
    linarith only [hVlo, hsplit, hc1, hd0, hd i]

/-- For [rank weights](hyp:a) that are [nonnegative](hyp:ha) and [decrease with rank](hyp:hmono),
 [an original sample, selected coordinate, and replacement](hyp:x,i,y) with [unit-bounded marks](hyp:hx,hy), [distinct original coordinates](hyp:hinj), and
 [distinct coordinates after replacement](hyp:hinj'),
 [the statistic changes by at most the removal and insertion weights](goal). -/
theorem rankConcomitant_replacement_sensitivity {N : ℕ}
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (x : Fin N → ℝ × ℝ) (i : Fin N) (y : ℝ × ℝ)
    (hx : ∀ j, (x j).2 ∈ Set.Icc (0 : ℝ) 1)
    (hy : y.2 ∈ Set.Icc (0 : ℝ) 1)
    (hinj : Function.Injective (fun j => (x j).1))
    (hinj' : Function.Injective
      (fun j => ((coordinateReplace i x y) j).1)) :
    |rankConcomitant a x - rankConcomitant a (coordinateReplace i x y)| ≤
      a (rankPosition x i) + a (rankPosition (coordinateReplace i x y) i) := by
  classical
  let x' := coordinateReplace i x y
  have hback : coordinateReplace i x' (x i) = x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [x', coordinateReplace]
    · simp [x', coordinateReplace, hji]
  have hsum : (∑ j : Fin N, a (rankPosition x j)) =
      ∑ j : Fin N, a (rankPosition x' j) := by
    rw [sum_rankPosition_weights, sum_rankPosition_weights]
  have hnew : rankConcomitant a x' =
      (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        a (rankPosition x' j) * (x j).2) +
        a (rankPosition x' i) * y.2 := by
    rw [rankConcomitant_eq_sum_rankPosition,
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [x', coordinateReplace, hji]
    · simp [x', coordinateReplace]
  rcases le_total (x i).1 y.1 with hxy | hyx
  · have hcd : ∀ j, j ≠ i → a (rankPosition x j) ≤ a (rankPosition x' j) := by
      intro j hji
      exact hmono (rankPosition_replace_le x i j y hji hxy hinj hinj')
    have hb := weighted_replacement_bound
      (fun j => a (rankPosition x j)) (fun j => a (rankPosition x' j))
      (fun j => (x j).2) i y.2 (fun j => ha _) (fun j => ha _) hx hy hcd hsum
    rw [rankConcomitant_eq_sum_rankPosition, hnew]
    exact hb
  · have hcd : ∀ j, j ≠ i → a (rankPosition x' j) ≤ a (rankPosition x j) := by
      intro j hji
      apply hmono
      simpa only [hback] using
        (rankPosition_replace_le x' i j (x i) hji
          (by simpa [x', coordinateReplace] using hyx) hinj' (by simpa [hback] using hinj))
    have hmark : ∀ j, (x' j).2 ∈ Set.Icc (0 : ℝ) 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [x', coordinateReplace] using hy
      · simpa [x', coordinateReplace, hji] using hx j
    have hold : rankConcomitant a x =
        (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
          a (rankPosition x j) * (x' j).2) +
          a (rankPosition x i) * (x i).2 := by
      rw [rankConcomitant_eq_sum_rankPosition,
        ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [x', coordinateReplace, hji]
    have hb := weighted_replacement_bound
      (fun j => a (rankPosition x' j)) (fun j => a (rankPosition x j))
      (fun j => (x' j).2) i (x i).2 (fun j => ha _) (fun j => ha _)
      hmark (hx i) hcd hsum.symm
    change |rankConcomitant a x - rankConcomitant a x'| ≤
      a (rankPosition x i) + a (rankPosition x' i)
    calc
      |rankConcomitant a x - rankConcomitant a x'| =
          |rankConcomitant a x' - rankConcomitant a x| := abs_sub_comm _ _
      _ = |(∑ j : Fin N, a (rankPosition x' j) * (x' j).2) -
          ((∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
            a (rankPosition x j) * (x' j).2) +
            a (rankPosition x i) * (x i).2)| := by
            rw [rankConcomitant_eq_sum_rankPosition, hold]
      _ ≤ _ := by simpa only [add_comm] using hb

/-- For an [iid marked observation law](hyp:μ) with [unit-bounded marks](hyp:hmark),
 [a rank-weighted concomitant has a square-integrable law](goal). -/
theorem rankConcomitant_memLp_two {N : ℕ} (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) :
    MemLp (rankConcomitant a) 2 (Measure.pi (fun _ : Fin N => μ)) := by
  classical
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  letI : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
  have hsort : Measurable (fun x : Fin N → ℝ × ℝ =>
      Tuple.sort (fun i => (x i).1)) := by
    apply measurable_to_countable'
    intro σ
    have hEq : {x : Fin N → ℝ × ℝ |
        Tuple.sort (fun i => (x i).1) = σ} =
        {x | Monotone ((fun i => (x i).1) ∘ σ) ∧
          ∀ i j : Fin N, i < j → (x (σ i)).1 = (x (σ j)).1 → σ i < σ j} := by
      ext x
      simpa only [Set.mem_setOf_eq, eq_comm] using
        (Tuple.eq_sort_iff (f := fun i => (x i).1) (σ := σ))
    rw [show (fun x : Fin N → ℝ × ℝ =>
        Tuple.sort (fun i => (x i).1)) ⁻¹' {σ} =
        {x | Tuple.sort (fun i => (x i).1) = σ} by rfl, hEq]
    apply MeasurableSet.inter
    · change MeasurableSet {x : Fin N → ℝ × ℝ |
        ∀ i j : Fin N, i ≤ j → (x (σ i)).1 ≤ (x (σ j)).1}
      have hh : MeasurableSet (⋂ i : Fin N, ⋂ j : Fin N,
          {x : Fin N → ℝ × ℝ | i ≤ j → (x (σ i)).1 ≤ (x (σ j)).1}) := by
        apply MeasurableSet.iInter
        intro i
        apply MeasurableSet.iInter
        intro j
        by_cases hij : i ≤ j
        · simpa only [hij, true_implies, Function.comp_apply] using measurableSet_le
            (measurable_fst.comp (measurable_pi_apply (σ i)))
            (measurable_fst.comp (measurable_pi_apply (σ j)))
        · simp [hij]
      simpa only [Set.iInter_setOf] using hh
    · change MeasurableSet {x : Fin N → ℝ × ℝ |
        ∀ i j : Fin N, i < j → (x (σ i)).1 = (x (σ j)).1 → σ i < σ j}
      have hh : MeasurableSet (⋂ i : Fin N, ⋂ j : Fin N,
          {x : Fin N → ℝ × ℝ |
            i < j → (x (σ i)).1 = (x (σ j)).1 → σ i < σ j}) := by
        apply MeasurableSet.iInter
        intro i
        apply MeasurableSet.iInter
        intro j
        by_cases hij : i < j
        · by_cases hσ : σ i < σ j
          · simp [hσ]
          · have heq : MeasurableSet {x : Fin N → ℝ × ℝ |
                (x (σ i)).1 = (x (σ j)).1} := by
              simpa only [Function.comp_apply] using
                (measurableSet_eq_fun
                (measurable_fst.comp (measurable_pi_apply (σ i)))
                (measurable_fst.comp (measurable_pi_apply (σ j))))
            convert heq.compl using 1 <;> ext x <;> simp [hij, hσ]
        · simp [hij]
      simpa only [Set.iInter_setOf] using hh
  have hstat : Measurable (rankConcomitant a : (Fin N → ℝ × ℝ) → ℝ) := by
    unfold rankConcomitant
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.mul
    have hsel : Measurable (fun x : Fin N → ℝ × ℝ =>
        ∑ i : Fin N, if Tuple.sort (fun k => (x k).1) j = i then (x i).2 else 0) := by
      apply Finset.measurable_sum
      intro i _
      apply Measurable.ite
      · exact measurableSet_eq_fun
          ((measurable_of_finite (fun σ : Equiv.Perm (Fin N) => σ j)).comp hsort)
          measurable_const
      · exact measurable_snd.comp (measurable_pi_apply i)
      · exact measurable_const
    convert hsel using 1
    funext x
    simp
  have hcoord (i : Fin N) : ∀ᵐ x ∂P, (x i).2 ∈ Set.Icc (0 : ℝ) 1 := by
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => μ)
      (i := i)).eventually hmark
  have hbound : ∀ᵐ x ∂P, ‖rankConcomitant a x‖ ≤ ∑ j : Fin N, |a j| := by
    have hall : ∀ᵐ x ∂P, ∀ i : Fin N, (x i).2 ∈ Set.Icc (0 : ℝ) 1 := by
      exact Filter.eventually_all.mpr hcoord
    filter_upwards [hall] with x hx
    rw [Real.norm_eq_abs]
    calc
      |rankConcomitant a x| ≤ ∑ j : Fin N,
          |a j * (x (Tuple.sort (fun i => (x i).1) j)).2| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin N, |a j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have hm := hx (Tuple.sort (fun i => (x i).1) j)
        have habs : |(x (Tuple.sort (fun i => (x i).1) j)).2| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hm.1, hm.2]
        nlinarith [abs_nonneg (a j)]
  exact MemLp.of_bound hstat.aestronglyMeasurable _ hbound

/-- For a [positive iid sample size](hyp:hN) and [continuous sorting-coordinate
 CDF](hyp:hcont), [each tagged observation has uniform rank, so its squared
 rank weight averages to the mean squared cell weight](goal). -/
theorem integral_rankPosition_weight_sq {N : ℕ} (hN : 0 < N)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (a : Fin N → ℝ) (i : Fin N) :
    (∫ x, (a (rankPosition x i)) ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) =
      (∑ j : Fin N, (a j) ^ 2) / N := by
  -- Transport to iid uniforms and integrate over the finite rank partition.
  classical
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  let Q : Measure (Fin N → ℝ) :=
    Causalean.Stat.OrderStatistic.iidSample Causalean.Stat.OrderStatistic.uniform01 N
  let F : (Fin N → ℝ × ℝ) → (Fin N → ℝ) :=
    fun x k => ProbabilityTheory.cdf (μ.map Prod.fst) (x k).1
  let r : (Fin N → ℝ) → Fin N := fun u => (Tuple.sort u).symm i
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro k
    exact hcont.measurable.comp (measurable_fst.comp (measurable_pi_apply k))
  have hrank (j : Fin N) : NullMeasurableSet {u | r u = j} Q := by
    let E : Set (Fin N → ℝ) :=
      {u | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => u k < u i)).card = j.val}
    have hE : MeasurableSet E := by
      dsimp [E]
      apply measurableSet_eq_fun
      · simp_rw [Finset.card_filter]
        apply Finset.measurable_sum
        intro k _
        apply Measurable.ite
        · exact measurableSet_lt (measurable_pi_apply k) (measurable_pi_apply i)
        · exact measurable_const
        · exact measurable_const
      · exact measurable_const
    apply hE.nullMeasurableSet.congr
    filter_upwards [iid_uniform_coordinates_injective_ae (N := N)] with u hu
    apply propext
    change (((Finset.univ : Finset (Fin N)).erase i).filter
      (fun k => u k < u i)).card = j.val ↔ r u = j
    rw [← uniform_tagged_rank_eq_count u i hu]
    exact Fin.ext_iff.symm
  have hr : AEMeasurable r Q := by
    apply NullMeasurable.aemeasurable
    change @Measurable (NullMeasurableSpace (Fin N → ℝ) Q) (Fin N) _ _ r
    apply measurable_to_countable'
    intro j
    exact hrank j
  have htransport : P.map F = Q := cdf_transport_iid μ hcont
  have hmass (j : Fin N) : (Q.map r) {j} = ENNReal.ofReal (1 / (N : ℝ)) := by
    rw [Measure.map_apply₀ hr (measurableSet_singleton j).nullMeasurableSet]
    exact uniform_tagged_rank_mass hN i j
  haveI : IsProbabilityMeasure Q := by
    haveI : IsProbabilityMeasure Causalean.Stat.OrderStatistic.uniform01 :=
      ⟨by simp [Causalean.Stat.OrderStatistic.uniform01]⟩
    dsimp [Q, Causalean.Stat.OrderStatistic.iidSample]
    infer_instance
  haveI : IsProbabilityMeasure (Q.map r) :=
    Measure.isProbabilityMeasure_map hr
  have hfin : Integrable (fun j : Fin N => (a j) ^ 2) (Q.map r) :=
    Integrable.of_finite
  calc
    (∫ x, (a (rankPosition x i)) ^ 2 ∂P) =
        ∫ x, (a (r (F x))) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [sort_cdf_eq_ae μ hcont] with x hx
          simp only [rankPosition, r, F, hx]
    _ = ∫ u, (a (r u)) ^ 2 ∂Q := by
      have hstrong : AEStronglyMeasurable (fun u => (a (r u)) ^ 2) Q :=
        ((measurable_of_countable (fun j : Fin N => (a j) ^ 2)).comp_aemeasurable
          hr).aestronglyMeasurable
      rw [← htransport]
      rw [← htransport] at hstrong
      exact (integral_map hF.aemeasurable hstrong).symm
    _ = ∫ j, (a j) ^ 2 ∂Q.map r := by
      exact (integral_map hr
        ((measurable_of_countable (fun j : Fin N => (a j) ^ 2)).aestronglyMeasurable)).symm
    _ = (∑ j : Fin N, (a j) ^ 2) / N := by
      rw [integral_fintype hfin]
      have hnonneg : 0 ≤ (1 / (N : ℝ)) := by positivity
      simp only [Measure.real, hmass, ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
