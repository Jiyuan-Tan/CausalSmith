module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Markov
public import Causalean.Mathlib.InformationTheory.FiniteKL
public import Causalean.Stat.Minimax.Pinsker
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
Finite Pinsker, Markov, and finite polynomial duality proved from Causalean primitives.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- Natural-log KL on a finite alphabet, with infinite divergence when a positive mass
has zero reference mass. On probability vectors its finite branch is the usual KL sum. -/
noncomputable def extendedFiniteKL {alpha : Type} [Fintype alpha]
    (p q : alpha → Real) : ENNReal :=
  if ∀ z, q z = 0 → p z = 0 then
    ENNReal.ofReal (∑ z, p z * Real.log (p z / q z))
  else ⊤

-- @node: lem:pinsker-finite
/--
[Wu and Yang (2016), Remark 4, displayed Pinsker inequality, arXiv:1407.0381v3. Natural-log
finite divergence, including infinite KL for singular probability pairs](goal).
-/
lemma PinskerFinite :
  ∀ (alpha : Type) [Fintype alpha] (p q : alpha → Real),
    (∀ z, 0 ≤ p z) → (∀ z, 0 ≤ q z) → (∑ z, p z = 1) → (∑ z, q z = 1) →
    ENNReal.ofReal ((1 / 2) * (∑ z, |p z - q z|)) ≤
      (extendedFiniteKL p q / 2) ^ (1 / 2 : Real)
 := by
  intro alpha _ p q hp hq hpsum hqsum
  classical
  by_cases hac : ∀ z, q z = 0 → p z = 0
  swap
  · simp [extendedFiniteKL, hac, ENNReal.top_div_of_ne_top]
  let : MeasurableSpace alpha := ⊤
  let : MeasurableSingletonClass alpha := ⟨fun _ => trivial⟩
  let pp : PMF alpha := PMF.ofFintype (fun z => ENNReal.ofReal (p z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hp z), hpsum]
    simp)
  let qq : PMF alpha := PMF.ofFintype (fun z => ENNReal.ofReal (q z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hq z), hqsum]
    simp)
  have hpread (z : alpha) : pp.toMeasure.real {z} = p z := by
    simp [Measure.real_def, pp, ENNReal.toReal_ofReal (hp z)]
  have hqread (z : alpha) : qq.toMeasure.real {z} = q z := by
    simp [Measure.real_def, qq, ENNReal.toReal_ofReal (hq z)]
  have hpmf : pp.toMeasure ≪ qq.toMeasure := by
    intro s hs
    rw [pp.toMeasure_apply_eq_toOuterMeasure_apply (by trivial), PMF.toOuterMeasure_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro z
    by_cases hz : z ∈ s
    · have hqz : qq.toMeasure {z} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hz) hs
      have hqzero : q z = 0 := by
        have := congrArg ENNReal.toReal hqz
        simpa [Measure.real_def, ← hqread z] using this
      simp [Set.indicator_of_mem hz, pp, hac z hqzero]
    · simp [Set.indicator_of_notMem hz]
  have hfin : InformationTheory.klDiv pp.toMeasure qq.toMeasure ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hpmf (by exact Integrable.of_finite)
  have hKL := Causalean.Mathlib.InformationTheory.klDiv_toReal_eq_sum_measureReal
    pp.toMeasure qq.toMeasure hpmf
  simp only [hpread, hqread] at hKL
  have hTV : (1 / 2 : Real) * ∑ z, |p z - q z| ≤
      Causalean.Stat.tvDist pp.toMeasure qq.toMeasure := by
    let A : Finset alpha := Finset.univ.filter (fun z => 0 ≤ p z - q z)
    have hsum : ∑ z, (p z - q z) = 0 := by rw [Finset.sum_sub_distrib, hpsum, hqsum]; ring
    have habs : ∑ z, |p z - q z| = 2 * ∑ z ∈ A, (p z - q z) := by
      have hsplit : ∑ z, (p z - q z) =
          (∑ z ∈ A, (p z - q z)) + ∑ z ∈ Aᶜ, (p z - q z) := by
        rw [Finset.sum_add_sum_compl A]
      have hsplitabs : ∑ z, |p z - q z| =
          (∑ z ∈ A, |p z - q z|) + ∑ z ∈ Aᶜ, |p z - q z| := by
        rw [Finset.sum_add_sum_compl A]
      have hpos : ∑ z ∈ A, |p z - q z| = ∑ z ∈ A, (p z - q z) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact abs_of_nonneg (Finset.mem_filter.mp hz).2
      have hneg : ∑ z ∈ Aᶜ, |p z - q z| =
          -(∑ z ∈ Aᶜ, (p z - q z)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro z hz
        apply abs_of_neg
        exact lt_of_not_ge (fun h => (Finset.mem_compl.mp hz)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩))
      rw [hpos, hneg] at hsplitabs
      linarith
    have hevent (rr : PMF alpha) : rr.toMeasure.real (A : Set alpha) =
        ∑ z ∈ A, rr.toMeasure.real {z} := by
      rw [Causalean.Stat.probability_measureReal_eq_tsum_singletons rr.toMeasure
        (A : Set alpha) (by trivial)]
      simp [Set.indicator]
    have hgap : pp.toMeasure.real (A : Set alpha) - qq.toMeasure.real (A : Set alpha) =
        ∑ z ∈ A, (p z - q z) := by
      rw [hevent pp, hevent qq, ← Finset.sum_sub_distrib]
      simp only [hpread, hqread]
    have hle := Causalean.Stat.abs_measureReal_sub_le_tvDist
      (μ := pp.toMeasure) (ν := qq.toMeasure) (show MeasurableSet (A : Set alpha) from by trivial)
    rw [hgap] at hle
    rw [habs]
    nlinarith [le_abs_self (∑ z ∈ A, (p z - q z))]
  have hPinsker := Causalean.Stat.pinskerBound_of_ac_of_ne_top
    pp.toMeasure qq.toMeasure hpmf hfin
  change Causalean.Stat.tvDist pp.toMeasure qq.toMeasure ≤ _ at hPinsker
  rw [hKL] at hPinsker
  have hnonneg : 0 ≤ ∑ z, p z * Real.log (p z / q z) := by
    rw [← hKL]
    exact ENNReal.toReal_nonneg
  have hbound := ENNReal.ofReal_le_ofReal (hTV.trans hPinsker)
  rw [Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (div_nonneg hnonneg (by norm_num)) (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)] at hbound
  simpa only [extendedFiniteKL, if_pos hac, ENNReal.ofReal_ofNat] using hbound
-- @node: lem:markov-polynomial
/--
[Pierzchała (2016), Theorem 1.1, DOI:10.1007/s00208-015-1294-9. The degree-bounded pointwise
form of Markov's inequality](goal).
-/
lemma MarkovPolynomial :
  ∀ (L : Nat) (Q : Polynomial Real) (Mb : Real), Q.natDegree ≤ L →
    (∀ x, x ∈ Set.Icc (-1 : Real) 1 → |Q.eval x| ≤ Mb) →
    ∀ x, x ∈ Set.Icc (-1 : Real) 1 → |Q.derivative.eval x| ≤ (L : Real) ^ 2 * Mb
 := by
  intro L Q Mb hdeg hMb x hx
  open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality in
    exact ((intervalSupNorm_le_iff Q.derivative.continuous.continuousOn (by norm_num)).mp
      ((markov_derivative_unitInterval Q L hdeg).trans
        (mul_le_mul_of_nonneg_left
          ((intervalSupNorm_le_iff Q.continuous.continuousOn (by norm_num)).mpr hMb)
          (sq_nonneg (L : Real))))) x hx
-- @node: lem:finite-polynomial-duality
/--
[Wu and Yang (2016), Appendix E, identity (34) and alternating finite weights,
arXiv:1407.0381v3. Weights have variation one and positive orientation](goal).
-/
lemma FinitePolynomialDuality :
  ∀ (g : Real → Real) (vlo vhi : Real) (L : Nat), vlo < vhi →
    ContinuousOn g (Set.Icc vlo vhi) →
    ∃ (nodes : Fin (L + 2) → Real) (w : Fin (L + 2) → Real),
      StrictMono nodes ∧ (∀ i, nodes i ∈ Set.Icc vlo vhi) ∧
      (∑ i, |w i| = 1) ∧ (∀ h, h ≤ L → ∑ i, w i * nodes i ^ h = 0) ∧
      ∑ i, w i * g (nodes i) =
        Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.bestUniformApproxError g
          vlo vhi L
 := by
  intro g vlo vhi L hv hg
  obtain ⟨D⟩ :=
    Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.exists_finiteMomentDual hv hg L
  by_cases h : 0 ≤ ∑ i, D.weights i * g (D.nodes i)
  · exact ⟨D.nodes, D.weights, D.nodes_strictMono, D.nodes_mem, D.weights_normalized,
      D.moments_zero, (abs_of_nonneg h).symm.trans D.target_abs_eq⟩
  · refine ⟨D.nodes, fun i => -D.weights i, D.nodes_strictMono, D.nodes_mem, ?_, ?_, ?_⟩
    · simpa only [abs_neg] using D.weights_normalized
    · intro k hk
      simpa only [neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg (D.moments_zero k hk)
    · simpa only [neg_mul, Finset.sum_neg_distrib, abs_of_neg (lt_of_not_ge h)] using
        D.target_abs_eq

end CausalSmith.Stat.AnnotationRarearmFrontier
