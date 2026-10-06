module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions

/-!
# Zero-mass padding of finite multinomial alphabets

An alphabet can be enlarged by assigning zero probability to every new cell.
The L1 target and the fixed ordered two-sample experiment are preserved.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory

private lemma sum_pad {M : Type*} [AddCommMonoid M] {r k : ℕ} (h : r ≤ k)
    (f : Fin r → M) :
    (∑ i : Fin k, if hi : (i : ℕ) < r then f ⟨i, hi⟩ else 0) = ∑ i : Fin r, f i := by
  calc
    _ = ∑ j ∈ Finset.range k, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = ∑ j ∈ Finset.range r, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      exact (Finset.sum_subset (Finset.range_mono h)
        (by intro j hj hnot; simp [Finset.mem_range] at hnot; simp [hnot])).symm
    _ = ∑ i : Fin r, f i := by
      rw [Finset.sum_fin_eq_sum_range]

/-- A probability vector on a smaller alphabet, extended by zero mass to a
larger alphabet. -/
noncomputable def padSimplex {r k : ℕ} (h : r ≤ k)
    (R : ProbabilitySimplex r) : ProbabilitySimplex k :=
  ⟨fun i => if hi : (i : ℕ) < r then R.1 ⟨i, hi⟩ else 0, by
    constructor
    · intro i
      dsimp
      split_ifs with hi
      · exact R.2.1 ⟨i, hi⟩
      · exact le_refl _
    · simpa using (sum_pad h R.1).trans R.2.2⟩

/-- Adding zero-mass labels to both probability vectors preserves their L1
distance exactly. -/
theorem padSimplex_l1 {r k : ℕ} (h : r ≤ k)
    (R S : ProbabilitySimplex r) :
    simplexL1 (padSimplex h R) (padSimplex h S) = simplexL1 R S := by
  change (∑ i : Fin k, |(if hi : (i : ℕ) < r then R.1 ⟨i, hi⟩ else 0) -
    (if hi : (i : ℕ) < r then S.1 ⟨i, hi⟩ else 0)|) =
    ∑ i : Fin r, |R.1 i - S.1 i|
  calc
    _ = ∑ i : Fin k, if hi : (i : ℕ) < r then |R.1 ⟨i, hi⟩ - S.1 ⟨i, hi⟩| else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := sum_pad h (fun i => |R.1 i - S.1 i|)

private lemma simplexPMF_pad {r k : ℕ} (h : r ≤ k) (R : ProbabilitySimplex r) :
    (simplexPMF R).map (Fin.castLE h) = simplexPMF (padSimplex h R) := by
  ext y
  rw [PMF.map_apply]
  by_cases hy : (y : ℕ) < r
  · let x : Fin r := ⟨y, hy⟩
    rw [tsum_eq_single x]
    · simp [simplexPMF, padSimplex, hy, x]
    · intro b hb
      have hne : y ≠ Fin.castLE h b := by
        intro he
        apply hb
        apply Fin.ext
        simpa [x] using congrArg Fin.val he.symm
      simp [hne]
  · have hz : ∀ b : Fin r, y ≠ Fin.castLE h b := by
      intro b he
      apply hy
      have hv : (y : ℕ) = (b : ℕ) := by simpa using congrArg Fin.val he
      simpa only [hv] using b.isLt
    simp [hz, simplexPMF, padSimplex, hy]

private lemma simplexSampleLaw_pad {r k n : ℕ} (h : r ≤ k)
    (R : ProbabilitySimplex r) :
    Measure.map (fun z : Fin n → Fin r => fun i => Fin.castLE h (z i))
      (simplexSampleLaw R n) = simplexSampleLaw (padSimplex h R) n := by
  unfold simplexSampleLaw
  rw [Measure.pi_map_pi (fun _ => (measurable_of_finite _).aemeasurable)]
  congr 1
  funext i
  rw [PMF.toMeasure_map (Fin.castLE h) (simplexPMF R) (measurable_of_finite _),
    simplexPMF_pad]

/-- Given [smaller and larger alphabet sizes and a sample size](hyp:r,k,n), [an embedding of the smaller alphabet](hyp:h), and [a pair of smaller-alphabet probability vectors](hyp:RS), [relabeling both samples gives exactly the law under zero-mass padding](goal). -/
theorem twoSampleLaw_pad {r k n : ℕ} (h : r ≤ k)
    (RS : ProbabilitySimplex r × ProbabilitySimplex r) :
    Measure.map
      (fun z : (Fin n → Fin r) × (Fin n → Fin r) =>
        ((fun i => Fin.castLE h (z.1 i)), (fun i => Fin.castLE h (z.2 i))))
      (twoSampleLaw n RS) =
    twoSampleLaw n (padSimplex h RS.1, padSimplex h RS.2) := by
  let f : (Fin n → Fin r) → (Fin n → Fin k) :=
    fun z i => Fin.castLE h (z i)
  change Measure.map (Prod.map f f) (twoSampleLaw n RS) =
    twoSampleLaw n (padSimplex h RS.1, padSimplex h RS.2)
  unfold twoSampleLaw
  rw [← Measure.map_prod_map (simplexSampleLaw RS.1 n) (simplexSampleLaw RS.2 n)
    (measurable_of_finite f) (measurable_of_finite f)]
  rw [simplexSampleLaw_pad h RS.1, simplexSampleLaw_pad h RS.2]

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
