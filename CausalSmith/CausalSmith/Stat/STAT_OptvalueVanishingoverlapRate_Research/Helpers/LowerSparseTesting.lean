module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparse
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedDuality

/-! # Sparse moment-matched likelihood separation

Centering the explicit constrained priors preserves their matched moments and
places their support in the radius-M/2 interval. The full four-coordinate
Poisson Gram identity then gives the unmatched exponential-series bound (34).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture
open scoped BigOperators

/-- Translating a supported prior by its reference midpoint gives support radius M/2. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_centered_prior_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {M : ℝ} (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (hMpaper : 2 ≤ M) :
    (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν) {z | |z| ≤ M / 2} = 1 := by
  have hm : Measurable (fun z => z - sparseReference (_hMpaper := hMpaper) M) := by fun_prop
  rw [Measure.map_apply hm (measurableSet_le (by fun_prop) measurable_const)]
  apply (mem_ae_iff_prob_eq_one
    ((measurableSet_le (by fun_prop) measurable_const).preimage hm)).1
  filter_upwards [show ∀ᵐ z ∂ν, z ∈ Set.Icc 0 M from
    (ae_iff).2 hsupp] with z hz
  change |z - sparseReference (_hMpaper := hMpaper) M| ≤ M / 2
  rw [abs_le]
  dsimp [sparseReference]
  constructor <;> linarith [hz.1, hz.2]

/-- Every centered moment through K agrees for the completed packet priors. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hj,hMpaper), the [stated conclusion](goal) holds. -/
lemma constrainedPriorPair_centered_moments {K : ℕ} {M : ℝ}
    (P : ConstrainedPriorPair K M) (j : ℕ) (hj : j ≤ K) (hMpaper : 2 ≤ M) :
    (∫ z, z ^ j ∂Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) P.ν₀) =
      (∫ z, z ^ j ∂Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) P.ν₁) := by
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  let p : Polynomial ℝ := (Polynomial.X - Polynomial.C (sparseReference (_hMpaper := hMpaper) M)) ^ j
  have hp : p.natDegree ≤ K := by
    calc
      p.natDegree ≤ (Polynomial.X - Polynomial.C (sparseReference (_hMpaper := hMpaper) M)).natDegree * j := by
        simpa only [Nat.mul_comm] using
          (Polynomial.natDegree_pow_le
            (p := Polynomial.X - Polynomial.C (sparseReference (_hMpaper := hMpaper) M)) (n := j))
      _ ≤ 1 * j := by
        gcongr
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ ≤ K := by simpa using hj
  simpa [p] using constrainedPriorPair_polynomial_integrals P p hp

/-- The full sparse likelihood is jointly measurable in its intensity and counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_oneCellLikelihood (B : ℝ) (n d : ℕ) (ε M : ℝ) (hMpaper : 2 ≤ M) :
    Measurable (fun p : ℝ × (Fin 4 → ℕ) => oneCellLikelihood (hMpaper := hMpaper) B n d ε M p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro N
  unfold oneCellLikelihood poissonCellMean
  apply Finset.measurable_prod
  intro j _
  split_ifs <;> fun_prop

/-- Legal sparse intensities give nonnegative likelihoods on every count vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,hε,hεhalf,hM,hz), the [stated conclusion](goal) holds. -/
lemma oneCellLikelihood_nonneg {B ε M : ℝ} {n d : ℕ}
    (hB : 2 < B) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M)
    {z : ℝ} (hz : z ∈ Set.Icc 0 M) (N : Fin 4 → ℕ) :
    0 ≤ oneCellLikelihood (hMpaper := hM) B n d ε M z N := by
  have hbase : 0 ≤ 1 - ε := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hM0 : 0 ≤ sparseReference (_hMpaper := hM) M := by dsimp [sparseReference]; linarith
  have hmean (w : ℝ) (hw : 0 ≤ w) (j : Fin 4) :
      0 ≤ poissonCellMean B n d ε w j := by
    unfold poissonCellMean
    split_ifs <;> positivity
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg
    (div_nonneg (hmean z hz.1 j) (hmean _ hM0 j)) _)


-- @node: sparse_poisson_likelihood_atom
/-- The scalar Poisson likelihood recovers each atom, including zero intensity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hμ,hstar), the [stated conclusion](goal) holds. -/
lemma sparse_poisson_likelihood_atom {μ μstar : ℝ} (hμ : 0 ≤ μ)
    (hstar : 0 < μstar) (k : ℕ) :
    poissonMeasure (Real.toNNReal μ) {k} =
      ENNReal.ofReal (Real.exp (μstar - μ) * (μ / μstar) ^ k) *
        poissonMeasure (Real.toNNReal μstar) {k} := by
  rw [poissonMeasure_singleton, poissonMeasure_singleton,
    Real.coe_toNNReal _ hμ, Real.coe_toNNReal _ hstar.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  have he : Real.exp (μstar - μ) * Real.exp (-μstar) = Real.exp (-μ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  symm
  calc
    _ = (Real.exp (μstar - μ) * Real.exp (-μstar)) * μ ^ k / (k.factorial : ℝ) := by
      field_simp [ne_of_gt hstar]
      <;> ring
    _ = _ := by rw [he]

/-- The full four-coordinate sparse likelihood is the actual Poisson density, so the Gram calculation applies to probability experiments rather than merely formal functions of the counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,hn,hd,hε,hεhalf,hM,hz), the [stated conclusion](goal) holds. -/
lemma poissonCellLaw_eq_withDensity_oneCellLikelihood {B ε M : ℝ} {n d : ℕ}
    (hB : 2 < B) (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε)
    (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M) {z : ℝ} (hz : z ∈ Set.Icc 0 M) :
    poissonCellLaw B n d ε z =
      (poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M)).withDensity
        (fun N => ENNReal.ofReal (oneCellLikelihood (hMpaper := hM) B n d ε M z N)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε1 : 0 < 1 - ε := by linarith
  have hMstar : 0 < sparseReference (_hMpaper := hM) M := by unfold sparseReference; linarith
  have hstar (j : Fin 4) : 0 < poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j := by
    fin_cases j <;> simp [poissonCellMean, cellIdx] <;> positivity
  have hz0 : 0 ≤ z := hz.1
  have hmean (j : Fin 4) : 0 ≤ poissonCellMean B n d ε z j := by
    unfold poissonCellMean
    split_ifs <;> positivity
  apply Measure.ext_of_singleton
  intro N
  rw [withDensity_apply _ (measurableSet_singleton N), lintegral_singleton]
  simp only [poissonCellLaw, Measure.pi_singleton]
  have hatom (j : Fin 4) := sparse_poisson_likelihood_atom (hmean j) (hstar j) (N j)
  simp_rw [hatom]
  rw [Finset.prod_mul_distrib]
  congr 1
  unfold oneCellLikelihood
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ => by
    exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg
      (div_nonneg (hmean j) (hstar j).le) _))).symm

/-- Equation (34): moment matching removes every low-degree term in the full four-coordinate Poisson mixture, with the exact midpoint radius. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hεhalf,hM,hB), the [stated conclusion](goal) holds. -/
lemma sparse_mixture_likelihood_sq_le_tail {K n d : ℕ} {ε M B : ℝ}
    (P : ConstrainedPriorPair K M) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M) (hB : 2 < B) :
    (∫ N : Fin 4 → ℕ,
      ((∫ z, oneCellLikelihood (hMpaper := hM) B n d ε M z N ∂P.ν₀) -
        (∫ z, oneCellLikelihood (hMpaper := hM) B n d ε M z N ∂P.ν₁)) ^ 2
      ∂poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M)) ≤
      4 * exponentialSeriesTail K (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * M ^ 2 / 4) := by
  let := P.prob₀
  let := P.prob₁
  let π₀ := Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀
  let π₁ := Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁
  let Q := poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M)
  let L := fun θ N => oneCellLikelihood (hMpaper := hM) B n d ε M (θ + sparseReference (_hMpaper := hM) M) N
  have hcenter : Measurable (fun z => z - sparseReference (_hMpaper := hM) M) := by fun_prop
  let : IsProbabilityMeasure π₀ := Measure.isProbabilityMeasure_map hcenter.aemeasurable
  let : IsProbabilityMeasure π₁ := Measure.isProbabilityMeasure_map hcenter.aemeasurable
  let : IsProbabilityMeasure Q := by dsimp [Q, poissonCellLaw]; infer_instance
  have hα : 0 ≤ sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM := by
    have hB0 : 0 ≤ B := by linarith
    have hbase : 0 ≤ 1 - ε := by linarith
    have hM0 : 0 ≤ M := by linarith
    unfold sparseGramCoefficient sparseReference
    positivity
  have hlegal (θ : ℝ) (hθ : |θ| ≤ M / 2) :
      θ + sparseReference (_hMpaper := hM) M ∈ Set.Icc 0 M := by
    rw [abs_le] at hθ
    dsimp [sparseReference]
    constructor <;> linarith [hθ.1, hθ.2]
  have hmeas : Measurable (fun p : ℝ × (Fin 4 → ℕ) => L p.1 p.2) := by
    change Measurable (fun p : ℝ × (Fin 4 → ℕ) =>
      oneCellLikelihood (hMpaper := hM) B n d ε M (p.1 + sparseReference (_hMpaper := hM) M) p.2)
    have ht : Measurable (fun p : ℝ × (Fin 4 → ℕ) =>
      (p.1 + sparseReference (_hMpaper := hM) M, p.2)) := by fun_prop
    exact Measurable.comp
      (g := fun p : ℝ × (Fin 4 → ℕ) => oneCellLikelihood (hMpaper := hM) B n d ε M p.1 p.2)
      (f := fun p : ℝ × (Fin 4 → ℕ) => (p.1 + sparseReference (_hMpaper := hM) M, p.2))
      (measurable_oneCellLikelihood (hMpaper := hM) B n d ε M) ht
  have hgram := (sparse_likelihood n d ε M B (fun _ => 0) hn hd hε hεhalf hM hB
    (fun _ => ⟨le_rfl, by linarith⟩)).2.2.2.1
  have hinner : ∀ θ, |θ| ≤ M / 2 → ∀ θ', |θ'| ≤ M / 2 →
      (∫ N, L θ N * L θ' N ∂Q) =
        Real.exp (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * θ * θ') := by
    intro θ hθ θ' hθ'
    simpa [L, Q] using hgram _ _ (hlegal θ hθ) (hlegal θ' hθ')
  have hbound := integral_sq_mixtureLikelihood_sub_le_tail_of_supported
    π₀ π₁ Q L (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM) (M / 2) K hα (by linarith)
    hmeas (fun θ hθ N => oneCellLikelihood_nonneg hB hε hεhalf hM (hlegal θ hθ) N)
    hinner (sparse_centered_prior_support (hMpaper := hM) P.ν₀ P.supp₀)
    (sparse_centered_prior_support (hMpaper := hM) P.ν₁ P.supp₁)
    (constrainedPriorPair_centered_moments (hMpaper := hM) P)
  have hmix (ν : Measure ℝ) (N : Fin 4 → ℕ) :
      mixtureLikelihood (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν) L N =
        ∫ z, oneCellLikelihood (hMpaper := hM) B n d ε M z N ∂ν := by
    unfold mixtureLikelihood
    have hf : Measurable (fun θ => L θ N) :=
      Measurable.comp (g := fun p : ℝ × (Fin 4 → ℕ) => L p.1 p.2)
        (f := fun θ : ℝ => (θ, N)) hmeas measurable_prodMk_right
    rw [integral_map hcenter.aemeasurable hf.aestronglyMeasurable]
    simp [L]
  simpa only [π₀, π₁, Q, hmix, show (M / 2) ^ 2 = M ^ 2 / 4 by ring,
    mul_div_assoc] using hbound

/-- The exact full-likelihood series argument obeys the scalar upper bound in (34), including the two untreated-outcome coordinates. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hεhalf,hM,hB), the [stated conclusion](goal) holds. -/
lemma sparse_mixture_series_argument_le {n d : ℕ} {ε M B : ℝ}
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hM : 2 ≤ M) (hB : 2 < B) :
    sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * M ^ 2 / 4 ≤ B * n * ε * M / (2 * d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hM0 : 0 < M := by linarith
  calc
    _ ≤ (2 * B * n * ε / (d * M)) * M ^ 2 / 4 := by
      gcongr
      exact sparseGramCoefficient_bound B hB n d hn hd ε M hε hεhalf hM
    _ = _ := by field_simp; ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
