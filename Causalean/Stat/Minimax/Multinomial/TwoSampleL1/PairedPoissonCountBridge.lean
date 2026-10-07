module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedSimplex
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonLikelihood

/-!
# Count-vector bridge for the balanced Poisson experiment

Counting each cell of a finite Poisson sample from a balanced multinomial
vector gives independent Poisson counts, paired by alphabet cell.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

/-- The two counts in each balanced alphabet pair of a finite sample. -/
noncomputable def pairedCountVector (b : ℕ)
    (s : FiniteSample (Fin (b * 2))) : Fin b → ℕ × ℕ :=
  fun j =>
    ((Finset.univ.filter fun i : Fin s.count =>
        s.points i = finProdFinEquiv (j, 0)).card,
      (Finset.univ.filter fun i : Fin s.count =>
        s.points i = finProdFinEquiv (j, 1)).card)

/-- Given [a positive balanced pair count and a sample size](hyp:b,n,hb), [a bounded nonnegative tilt](hyp:t,ht,ht1), and [bounded cell directions](hyp:u,hu), [the paired count vector of a finite Poisson sample with mean 2n drawn from the tilted vector consists of independent count pairs, the pair for cell pair j being two independent Poisson counts with rates (n/b)(1 + t·u_j) and (n/b)(1 − t·u_j)](goal). -/
theorem pairedCountVector_map_finitePoissonSampleLaw
    (b n : ℕ) (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (u : Fin b → ℝ) (hu : ∀ j, |u j| ≤ 1) :
    Measure.map (pairedCountVector b)
      (finitePoissonSampleLaw
        (simplexPMF (pairedTiltVector b hb t ht ht1 u hu)).toMeasure
        (Real.toNNReal (2 * (n : ℝ)))) =
    Measure.pi (fun j : Fin b =>
        scalarPoissonPairLaw ((n : ℝ) / (b : ℝ)) t (u j)) := by
  classical
  let P := (simplexPMF (pairedTiltVector b hb t ht ht1 u hu)).toMeasure
  let lam : ℝ≥0 := Real.toNNReal (2 * (n : ℝ))
  let H : FiniteSample (Fin (b * 2)) → (Fin (b * 2) → ℕ) :=
    fun s => Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram s.points
  let R : (Fin (b * 2) → ℕ) → (Fin b → ℕ × ℕ) :=
    fun c j => (c (finProdFinEquiv (j, 0)), c (finProdFinEquiv (j, 1)))
  have hR : Measurable R := measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hH : Measurable H := by
    apply measurable_to_countable'
    intro c
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet ((Sigma.mk m) ⁻¹'
      {s : FiniteSample (Fin (b * 2)) | H s = c})
    exact (Set.to_countable _).measurableSet
  have hfactor : pairedCountVector b = R ∘ H := by
    funext s j
    unfold pairedCountVector R H
    change ((Finset.univ.filter fun i : Fin s.count =>
        s.points i = finProdFinEquiv (j, 0)).card,
      (Finset.univ.filter fun i : Fin s.count =>
        s.points i = finProdFinEquiv (j, 1)).card) =
      (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram
        s.points (finProdFinEquiv (j, 0)),
       Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram
        s.points (finProdFinEquiv (j, 1)))
    simp [Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram,
      Fintype.card_subtype]
  rw [hfactor, ← Measure.map_map hR hH]
  rw [Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finitePoissonSampleLaw_map_histogram
    P lam]
  unfold Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
  apply Measure.ext_of_singleton
  intro z
  let c : Fin (b * 2) → ℕ := fun i =>
    let p := finProdFinEquiv.symm i
    if p.2 = 0 then (z p.1).1 else (z p.1).2
  have hc : R ⁻¹' {z} = {c} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hd
      funext i
      have h := congrFun hd (finProdFinEquiv.symm i).1
      change (d (finProdFinEquiv ((finProdFinEquiv.symm i).1, 0)),
        d (finProdFinEquiv ((finProdFinEquiv.symm i).1, 1))) =
        z (finProdFinEquiv.symm i).1 at h
      unfold c
      have hfin : (finProdFinEquiv.symm i).2 = 0 ∨
          (finProdFinEquiv.symm i).2 = 1 := by omega
      rcases hfin with h0 | h1
      · have hd0 := congrArg Prod.fst h
        rw [← h0, finProdFinEquiv.apply_symm_apply] at hd0
        change i.modNat = 0 at h0
        simpa [h0] using hd0
      · have hd1 := congrArg Prod.snd h
        rw [← h1, finProdFinEquiv.apply_symm_apply] at hd1
        change i.modNat = 1 at h1
        simpa [h1] using hd1
    · intro hd
      subst d
      funext j
      change (c (finProdFinEquiv (j, 0)), c (finProdFinEquiv (j, 1))) = z j
      simp only [c, Equiv.symm_apply_apply, ↓reduceIte, one_ne_zero]
  rw [Measure.map_apply hR (MeasurableSet.singleton z), hc,
    Measure.pi_singleton]
  simp only [scalarPoissonPairLaw, Measure.pi_singleton]
  have hrate0 (j : Fin b) :
      lam * (P {finProdFinEquiv (j, 0)}).toNNReal =
        Real.toNNReal (((n : ℝ) / (b : ℝ)) * (1 + t * u j)) := by
    have hp : (P {finProdFinEquiv (j, 0)}).toNNReal =
        Real.toNNReal ((1 + t * u j) / ((b : ℝ) * 2)) := by
      have he := finProdFinEquiv.symm_apply_apply (j, (0 : Fin 2))
      have hdiv : (finProdFinEquiv (j, 0)).divNat = j := congrArg Prod.fst he
      have hmod : (finProdFinEquiv (j, 0)).modNat = 0 := congrArg Prod.snd he
      simp [P, simplexPMF, pairedTiltVector, ENNReal.ofReal, hdiv, hmod]
    rw [hp]
    change Real.toNNReal (2 * (n : ℝ)) *
      Real.toNNReal ((1 + t * u j) / ((b : ℝ) * 2)) = _
    rw [← Real.toNNReal_mul (by positivity)]
    congr 1
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    field_simp
  have hrate1 (j : Fin b) :
      lam * (P {finProdFinEquiv (j, 1)}).toNNReal =
        Real.toNNReal (((n : ℝ) / (b : ℝ)) * (1 - t * u j)) := by
    have hp : (P {finProdFinEquiv (j, 1)}).toNNReal =
        Real.toNNReal ((1 - t * u j) / ((b : ℝ) * 2)) := by
      have he := finProdFinEquiv.symm_apply_apply (j, (1 : Fin 2))
      have hdiv : (finProdFinEquiv (j, 1)).divNat = j := congrArg Prod.fst he
      have hmod : (finProdFinEquiv (j, 1)).modNat = 1 := congrArg Prod.snd he
      simp [P, simplexPMF, pairedTiltVector, ENNReal.ofReal, hdiv, hmod,
        sub_eq_add_neg]
    rw [hp]
    change Real.toNNReal (2 * (n : ℝ)) *
      Real.toNNReal ((1 - t * u j) / ((b : ℝ) * 2)) = _
    rw [← Real.toNNReal_mul (by positivity)]
    congr 1
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    field_simp
  calc
    (∏ i : Fin (b * 2), poissonMeasure (lam * (P {i}).toNNReal) {c i}) =
        ∏ j : Fin b,
          poissonMeasure (lam * (P {finProdFinEquiv (j, 0)}).toNNReal) {(z j).1} *
          poissonMeasure (lam * (P {finProdFinEquiv (j, 1)}).toNNReal) {(z j).2} := by
      rw [← Equiv.prod_comp finProdFinEquiv]
      simp only [Fintype.prod_prod_type, Fin.prod_univ_two]
      apply Finset.prod_congr rfl
      intro j _
      have hc0 : c (finProdFinEquiv (j, 0)) = (z j).1 := by
        have he := finProdFinEquiv.symm_apply_apply (j, (0 : Fin 2))
        have hdiv : (finProdFinEquiv (j, 0)).divNat = j := congrArg Prod.fst he
        have hmod : (finProdFinEquiv (j, 0)).modNat = 0 := congrArg Prod.snd he
        simp [c, hdiv, hmod]
      have hc1 : c (finProdFinEquiv (j, 1)) = (z j).2 := by
        have he := finProdFinEquiv.symm_apply_apply (j, (1 : Fin 2))
        have hdiv : (finProdFinEquiv (j, 1)).divNat = j := congrArg Prod.fst he
        have hmod : (finProdFinEquiv (j, 1)).modNat = 1 := congrArg Prod.snd he
        simp [c, hdiv, hmod]
      rw [hc0, hc1]
    _ = ∏ j : Fin b,
        (poissonMeasure (Real.toNNReal (((n : ℝ) / (b : ℝ)) * (1 + t * u j)))).prod
          (poissonMeasure (Real.toNNReal (((n : ℝ) / (b : ℝ)) * (1 - t * u j))))
            {z j} := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hrate0 j, hrate1 j, ← Set.singleton_prod_singleton, Measure.prod_prod]

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
