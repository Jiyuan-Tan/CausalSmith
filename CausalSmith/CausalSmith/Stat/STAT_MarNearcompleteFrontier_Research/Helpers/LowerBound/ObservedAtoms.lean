module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw
/-! # Exact observed-atom masses of the normalized paired construction

The full-data construction marginalizes to the displayed count-experiment
coefficients divided by the shared normalizer.
-/
public section
namespace CausalSmith.Stat.MarNearcompleteFrontier
open MeasureTheory ProbabilityTheory
/-- An oriented pair marginalizes to its displayed observed coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j), [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ). -/
-- @node: pairAtomWeight_observed_sum
lemma pairAtomWeight_observed_sum (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool) (o : Obs d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hσ : σ ∈ Set.Icc (-1) 1) :
    (∑ w : FullAtom d, if observe w = o then pairAtomWeight n d q σ hd θ j side w else 0) =
      if o.X = pairLabel n d hd j side then
        latentP n (θ.1 j) / normalizationJ n d θ *
          pairObservedCoeff q σ (latentZ n (θ.1 j)) (orientation θ j side) o
      else 0 := by
  have hρ : pairRho q σ (latentZ n (θ.1 j)) (orientation θ j side) ≠ 0 := by
    have h := pairRho_mem_unit q σ (latentZ n (θ.1 j)) (orientation θ j side)
      hq (pair_sign_mem_unit n d σ hσ θ j side)
    exact ne_of_gt (lt_of_lt_of_le (by linarith [hq.1]) h.1)
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => if observe w = o then pairAtomWeight n d q σ hd θ j side w else 0)
    (fun t => if observe ((fullAtomTupleEquiv d).symm t) = o then
      pairAtomWeight n d q σ hd θ j side ((fullAtomTupleEquiv d).symm t) else 0)
    (by intro w; simp)]
  rcases o with ⟨x, a, s, r, y⟩
  cases a <;> cases s <;> cases r <;> cases y <;>
    simp [Fintype.sum_prod_type, fullAtomTupleEquiv, pairAtomWeight, observe,
      bernoulliFactor, FullAtom.X, FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1,
      Obs.mk.injEq, pairObservedCoeff]
  all_goals
    by_cases hx : x = pairLabel n d hd j side
    · simp only [hx, ↓reduceIte]
      simp only [pairMu]
      field_simp [hρ]
      try simp only [pairRho]
      ring
    · simp [hx]
/-- The filler marginalizes to its common observed coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). -/
-- @node: fillerAtomWeight_observed_sum
lemma fillerAtomWeight_observed_sum (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (o : Obs d) :
    (∑ w : FullAtom d, if observe w = o then fillerAtomWeight n d q hd θ w else 0) =
      if o.X = fillerLabel d hd then
        fillerMass n d / normalizationJ n d θ * fillerObservedCoeff q o
      else 0 := by
  rw [Fintype.sum_equiv (fullAtomTupleEquiv d)
    (fun w => if observe w = o then fillerAtomWeight n d q hd θ w else 0)
    (fun t => if observe ((fullAtomTupleEquiv d).symm t) = o then
      fillerAtomWeight n d q hd θ ((fullAtomTupleEquiv d).symm t) else 0)
    (by intro w; simp)]
  rcases o with ⟨x, a, s, r, y⟩
  cases a <;> cases s <;> cases r <;> cases y <;>
    simp [Fintype.sum_prod_type, fullAtomTupleEquiv, fillerAtomWeight, observe,
      bernoulliFactor, FullAtom.X, FullAtom.S0, FullAtom.S1, FullAtom.Y0, FullAtom.Y1,
      Obs.mk.injEq, fillerObservedCoeff]
  all_goals
    by_cases hx : x = fillerLabel d hd
    · simp only [hx, ↓reduceIte]
      ring
    · simp [hx]
/-- The normalized observed atom mass is the unnormalized count mass divided by the shared scale. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ). -/
-- @node: pairedFullLaw_observed_atom_mass
lemma pairedFullLaw_observed_atom_mass (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ ∈ Set.Icc (-1) 1) (θ : Theta n d) (o : Obs d) :
    obsMass (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)) o =
      countAtomMass n d q σ hd θ o / normalizationJ n d θ := by
  have hmass : obsMass (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)) o =
      ∑ w : FullAtom d, if observe w = o then
        pairedAtomWeight n d q σ hd θ w else 0 := by
    simp only [obsMass, observedLaw, PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun w _ => by split_ifs <;> simp [pairedFullLaw])]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : observe w = o
    · simp [hw, pairedFullLaw,
        pairedAtomWeight_nonneg n d q σ hn hd hq hσ θ w]
    · have hwo : ¬ o = observe w := Ne.symm hw
      simp [hw, hwo]
  rw [hmass]
  have hsplit (w : FullAtom d) :
      (if observe w = o then pairedAtomWeight n d q σ hd θ w else 0) =
      (if observe w = o then fillerAtomWeight n d q hd θ w else 0) +
        ∑ j : Fin (pairCount n d), ∑ side : Bool,
          if observe w = o then pairAtomWeight n d q σ hd θ j side w else 0 := by
    by_cases hw : observe w = o <;> simp [hw, pairedAtomWeight]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, fillerAtomWeight_observed_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (FullAtom d)))
    (t := (Finset.univ : Finset Bool))]
  simp_rw [pairAtomWeight_observed_sum n d q σ hd θ _ _ o hq hσ]
  unfold countAtomMass
  rw [add_div, Finset.sum_div]
  congr 1
  · split_ifs <;> (try simp) <;> ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro side _
    split_ifs <;> (try simp) <;> ring

/-- The paper's conditional count experiment is the histogram law of the
normalized observed distribution at intensity four n times the shared scale. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ). -/
-- @node: conditionalCountLaw_eq_independentPoissonCountLaw
lemma conditionalCountLaw_eq_independentPoissonCountLaw (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ ∈ Set.Icc (-1) 1) (θ : Theta n d) :
    conditionalCountLaw n d q σ hd θ =
      Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
        (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)).toMeasure
        (Real.toNNReal (4 * (n : ℝ)) * Real.toNNReal (normalizationJ n d θ)) := by
  unfold conditionalCountLaw
    Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
  congr 1
  funext o
  congr 1
  apply NNReal.eq
  have hJ := normalizationJ_pos n d q hn hd hq θ
  have hp : 0 ≤ (4 : ℝ) * n := by positivity
  have hm := pairedFullLaw_observed_atom_mass n d q σ hn hd hq hσ θ o
  have hm0 : 0 ≤ countAtomMass n d q σ hd θ o := by
    have : 0 ≤ obsMass (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)) o :=
      ENNReal.toReal_nonneg
    rw [hm] at this
    have hx := mul_nonneg this hJ.le
    rw [div_mul_cancel₀ _ (ne_of_gt hJ)] at hx
    exact hx
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ hp,
    Real.coe_toNNReal _ hJ.le, ENNReal.coe_toNNReal]
  rw [Real.toNNReal_of_nonneg (mul_nonneg hp hm0)]
  change 4 * (n : ℝ) * countAtomMass n d q σ hd θ o =
    4 * (n : ℝ) * normalizationJ n d θ *
      obsMass (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)) o
  rw [hm]
  field_simp [ne_of_gt hJ]

end CausalSmith.Stat.MarNearcompleteFrontier
