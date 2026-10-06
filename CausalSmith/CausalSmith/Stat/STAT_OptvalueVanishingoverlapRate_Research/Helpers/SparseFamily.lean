module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Basic
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedApproximation
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normalized sparse family and its full four-coordinate Poisson likelihood
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- For the displayed parameters, sparseNormalizerFormula is the object specified by this definition. -/
 noncomputable def sparseNormalizerFormula (d : ℕ) (ε M : ℝ) (z : Fin d → ℝ) (_hz : ∀ x, z x ∈ Set.Icc 0 M) : ℝ := 1 - ε + ε / d * ∑ x : Fin d, z x 
/-- Normalizing mass on the public positive-overlap domain. For the displayed parameters, sparseNormalizer is the object specified by this definition. -/
 noncomputable def sparseNormalizer (d : ℕ) (ε M : ℝ) (_hε : 0 < ε ∧ ε ≤ 1 / 2) (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M) : ℝ := sparseNormalizerFormula d ε M z hz -- @realizes \(S(\mathbf z)\)(normalizing mass; 0<ε≤1/2) -- @realizes \(\mathbf z\)(every coordinate in [0, M]) 
/-- For the displayed parameters, sparseUnnormalizedMass is the object specified by this definition. -/
noncomputable def sparseUnnormalizedMass {d : ℕ} (ε : ℝ) (z : Fin d → ℝ)
    (o : Obs d) : ℝ :=
  let x := o.1
  let a := o.2.1
  let y := o.2.2
  if a then
    if y then ε * (1 - ε) * z x / d else ε * (1 - ε) / d
  else
    ((1 - ε) ^ 2 + ε ^ 2 * z x) / (2 * d)
/-- For the displayed parameters, sparseMass is the object specified by this definition. -/
 noncomputable def sparseMass {d : ℕ} (ε M : ℝ) (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M) (o : Obs d) : ℝ := sparseUnnormalizedMass ε z o / sparseNormalizerFormula d ε M z hz -- @node: sparseMass_pmf_sum 
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hz), the [stated conclusion](goal) holds. -/
lemma sparseMass_pmf_sum {d : ℕ} (hd : 0 < d) (ε M : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1 / 2) (z : Fin d → ℝ)
    (hz : ∀ x, z x ∈ Set.Icc 0 M) :
    (∑ o : Obs d, ENNReal.ofReal (sparseMass ε M z hz o)) = 1 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hz0 (x : Fin d) : 0 ≤ z x := (hz x).1
  have hε0 : 0 ≤ ε := le_of_lt hε.1
  have hε1 : 0 ≤ 1 - ε := by linarith [hε.2]
  have hS : 0 < sparseNormalizerFormula d ε M z hz := by
    unfold sparseNormalizerFormula
    have hs : 0 ≤ ∑ x : Fin d, z x := Finset.sum_nonneg (fun x _ => hz0 x)
    have : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, z x :=
      mul_nonneg (div_nonneg hε0 (le_of_lt hdR)) hs
    linarith [hε.2]
  have hm (o : Obs d) : 0 ≤ sparseMass ε M z hz o := by
    unfold sparseMass sparseUnnormalizedMass
    rcases o with ⟨x, a, y⟩
    have hzx : 0 ≤ z x := hz0 x
    cases a <;> cases y <;> dsimp <;> positivity
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => hm o)]
  have hreal : (∑ o : Obs d, sparseMass ε M z hz o) = 1 := by
    simp_rw [sparseMass, ← Finset.sum_div]
    have htotal : (∑ o : Obs d, sparseUnnormalizedMass ε z o) =
        sparseNormalizerFormula d ε M z hz := by
      calc
        _ = ∑ x : Fin d, (ε * z x + 1 - ε) / d := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          simp [sparseUnnormalizedMass]
          ring
        _ = sparseNormalizerFormula d ε M z hz := by
          calc
            _ = ∑ x : Fin d, ((ε / d) * z x + (1 - ε) / d) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
            _ = (ε / d) * ∑ x : Fin d, z x + (d : ℝ) * ((1 - ε) / d) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp
            _ = sparseNormalizerFormula d ε M z hz := by
              unfold sparseNormalizerFormula
              field_simp
              ring
    rw [htotal]
    exact div_self hS.ne'
  rw [hreal]
  simp

-- @node: def:sparse-family
/-- For the displayed parameters, sparseLaw is the object specified by this definition. -/
 noncomputable def sparseLaw {d : ℕ} (hd : 0 < d) (ε M : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 2) (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M) : DiscreteLaw d := ⟨PMF.ofFintype (fun o => ENNReal.ofReal (sparseUnnormalizedMass ε z o / sparseNormalizer d ε M hε z hz)) (sparseMass_pmf_sum hd ε M hε z hz)⟩ -- @realizes \(\mathbb P_{\mathbf z}^{\mathrm{sp}}\)(normalized sparse law) 
/-- For the displayed parameters, sparseReference is the object specified by this definition. -/
 noncomputable def sparseReference (M : ℝ) (_hMpaper : 2 ≤ M) : ℝ := M / 2 -- @realizes \(z_\star\)(reference intensity M/2; paper endpoint M≥2) 
/-- For the displayed parameters, poissonCellMean is the object specified by this definition. -/
 noncomputable def poissonCellMean (B : ℝ) (n d : ℕ) (ε z : ℝ) (j : Fin 4) : ℝ := B * n * (if j = cellIdx true true then ε * (1 - ε) * z / d else if j = cellIdx true false then ε * (1 - ε) / d else ((1 - ε) ^ 2 + ε ^ 2 * z) / (2 * d)) 
/-- For the displayed parameters, poissonCellLaw is the object specified by this definition. -/
 noncomputable def poissonCellLaw (B : ℝ) (n d : ℕ) (ε z : ℝ) : Measure (Fin 4 → ℕ) := Measure.pi (fun j : Fin 4 => poissonMeasure (Real.toNNReal (poissonCellMean B n d ε z j))) 
/-- For the displayed parameters, oneCellLikelihood is the object specified by this definition. -/
noncomputable def oneCellLikelihood (B : ℝ) (n d : ℕ) (ε M z : ℝ)
    (N : Fin 4 → ℕ) (hMpaper : 2 ≤ M) : ℝ :=
  ∏ j : Fin 4,
    let μ := poissonCellMean B n d ε z j
    let μstar :=
      poissonCellMean B n d ε (sparseReference (_hMpaper := hMpaper) M) j
    Real.exp (μstar - μ) * (μ / μstar) ^ (N j)
  -- @realizes \(L_z\)(full four-coordinate likelihood ratio)
/-- For the displayed parameters, sparseGramCoefficient is the object specified by this definition. -/
 noncomputable def sparseGramCoefficient (B : ℝ) (_hB : B > 2) (n d : ℕ) (ε M : ℝ) (_hε : 0 < ε ∧ ε ≤ 1 / 2) (_hM : 2 ≤ M) : ℝ := B * n / d * (ε * (1 - ε) / sparseReference (_hMpaper := _hM) M + ε ^ 4 / ((1 - ε) ^ 2 + ε ^ 2 * sparseReference (_hMpaper := _hM) M)) -- @realizes \(\alpha\)(nonnegative full likelihood information; 0<ε≤1/2 and M≥2) -- @realizes \(B\)(Poisson inflation above two) 
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,hn,hd,hε,hεhalf,hM), the [stated conclusion](goal) holds. -/
lemma sparseGramCoefficient_bound (B : ℝ) (hB : B > 2) (n d : ℕ)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (ε M : ℝ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M) :
    sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM ≤ 2 * B * n * ε / (d * M) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hM0 : 0 < M := by linarith
  have hD : 0 < (1 - ε) ^ 2 + ε ^ 2 * (M / 2) := by positivity
  have hinner :
      ε * (1 - ε) / (M / 2) +
        ε ^ 4 / ((1 - ε) ^ 2 + ε ^ 2 * (M / 2)) ≤ 2 * ε / M := by
    field_simp
    nlinarith [sq_nonneg (1 - ε)]
  unfold sparseGramCoefficient sparseReference
  calc
    B * n / d * (ε * (1 - ε) / (M / 2) +
      ε ^ 4 / ((1 - ε) ^ 2 + ε ^ 2 * (M / 2)))
        ≤ B * n / d * (2 * ε / M) := by gcongr
    _ = 2 * B * n * ε / (d * M) := by ring

-- @node: sparseLaw_jointMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hz), the [stated conclusion](goal) holds. -/
lemma sparseLaw_jointMass {d : ℕ} (hd : 0 < d) (ε M : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1 / 2) (z : Fin d → ℝ)
    (hz : ∀ x, z x ∈ Set.Icc 0 M) (x : Fin d) (a y : Bool) :
    jointMass (sparseLaw hd ε M hε z hz) x a y =
      sparseMass ε M z hz (x, a, y) := by
  have hm : 0 ≤ sparseMass ε M z hz (x, a, y) := by
    unfold sparseMass sparseUnnormalizedMass
    have hzx : 0 ≤ z x := (hz x).1
    have hε0 : 0 ≤ ε := le_of_lt hε.1
    have hε1 : 0 ≤ 1 - ε := by linarith [hε.2]
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hden : 0 < sparseNormalizerFormula d ε M z hz := by
      unfold sparseNormalizerFormula
      have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      have hs : 0 ≤ ∑ x : Fin d, z x := Finset.sum_nonneg (fun x _ => (hz x).1)
      have : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, z x :=
        mul_nonneg (div_nonneg (le_of_lt hε.1) (le_of_lt hdR)) hs
      linarith [hε.2]
    cases a <;> cases y <;> dsimp <;> positivity
  change (ENNReal.ofReal (sparseMass ε M z hz (x, a, y))).toReal = _
  exact ENNReal.toReal_ofReal hm

-- @node: poisson_likelihood_gram_scalar
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hstar), the [stated conclusion](goal) holds. -/
lemma poisson_likelihood_gram_scalar (μstar μ ν : ℝ) (hstar : 0 < μstar) :
    (∫ N : ℕ, (Real.exp (μstar - μ) * (μ / μstar) ^ N) *
      (Real.exp (μstar - ν) * (ν / μstar) ^ N)
      ∂poissonMeasure (Real.toNNReal μstar)) =
      Real.exp ((μ - μstar) * (ν - μstar) / μstar) := by
  have hmgf (r : NNReal) (c : ℝ) :
      (∫ N : ℕ, c ^ N ∂poissonMeasure r) =
        Real.exp ((r : ℝ) * (c - 1)) := by
    rw [ProbabilityTheory.integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [show (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
        (n.factorial : ℝ) * c ^ n) =
        fun n => Real.exp (-(r : ℝ)) * (((r : ℝ) * c) ^ n /
          (n.factorial : ℝ)) by
      funext n
      rw [mul_pow]
      ring]
    rw [tsum_mul_left]
    rw [show (∑' n : ℕ, ((r : ℝ) * c) ^ n / (n.factorial : ℝ)) =
        Real.exp ((r : ℝ) * c) by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * c)).tsum_eq]
    rw [← Real.exp_add]
    congr 1
    ring
  have heq (N : ℕ) :
      (Real.exp (μstar - μ) * (μ / μstar) ^ N) *
        (Real.exp (μstar - ν) * (ν / μstar) ^ N) =
      Real.exp (μstar - μ + (μstar - ν)) *
        ((μ / μstar) * (ν / μstar)) ^ N := by
    rw [Real.exp_add, mul_pow]
    ring
  simp_rw [heq]
  rw [integral_const_mul, hmgf]
  rw [← Real.exp_add, Real.coe_toNNReal _ (le_of_lt hstar)]
  congr 1
  field_simp
  ring

-- @node: lem:sparse-likelihood
/-- In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_likelihood :
    ∀ (n d : ℕ) (ε M B : ℝ) (zv : Fin d → ℝ)
      (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
      (hM : 2 ≤ M) (hB : B > 2) (hz : ∀ x, zv x ∈ Set.Icc 0 M),
      let P := sparseLaw (Nat.lt_of_lt_of_le (by decide : 0 < 2) hd)
        ε M ⟨hε, hεhalf⟩ zv hz
      ObservedClass ε P ∧
      (∀ x : Fin d,
        cellMass P x = (1 - ε + ε * zv x) / (d * sparseNormalizerFormula d ε M zv hz) ∧
        propensity P x =
          ε * (1 - ε) * (1 + zv x) / (1 - ε + ε * zv x) ∧
        outcomeMean P false x = 1 / 2 ∧
        outcomeMean P true x = zv x / (1 + zv x)) ∧
      observedValue P =
        1 / 2 + (1 / (2 * d * sparseNormalizerFormula d ε M zv hz)) *
          ∑ x : Fin d, phiEpsFormula ε (zv x) ∧
      (∀ z w : ℝ, z ∈ Set.Icc 0 M → w ∈ Set.Icc 0 M →
        (∫ N : Fin 4 → ℕ,
          oneCellLikelihood (hMpaper := hM) B n d ε M z N *
            oneCellLikelihood (hMpaper := hM) B n d ε M w N
          ∂poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M)) =
          Real.exp (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM *
            (z - sparseReference (_hMpaper := hM) M) * (w - sparseReference (_hMpaper := hM) M))) ∧
      sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM ≤ 2 * B * n * ε / (d * M) := by
  intro n d ε M B zv hn hd hε hεhalf hM hB hz
  dsimp
  refine ⟨?_, ?_, ?_, ?_, sparseGramCoefficient_bound B hB n d hn hd ε M hε hεhalf hM⟩
  · refine ⟨?_⟩
    intro x _
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hS : 0 < sparseNormalizerFormula d ε M zv hz := by
      unfold sparseNormalizerFormula
      have hs : 0 ≤ ∑ x : Fin d, zv x :=
        Finset.sum_nonneg (fun x _ => (hz x).1)
      have : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, zv x :=
        mul_nonneg (div_nonneg (le_of_lt hε) (le_of_lt hdR)) hs
      linarith [hεhalf]
    have hzx : 0 ≤ zv x := (hz x).1
    have hc : 0 < 1 - ε + ε * zv x := by
      nlinarith [mul_nonneg (le_of_lt hε) hzx]
    let P := sparseLaw (Nat.lt_of_lt_of_le (by decide : 0 < 2) hd)
      ε M ⟨hε, hεhalf⟩ zv hz
    have hcell : cellMass P x =
        (1 - ε + ε * zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, cellMass, sparseLaw_jointMass, sparseMass,
        sparseUnnormalizedMass]
      field_simp
      ring
    have htrue : armMass P true x =
        ε * (1 - ε) * (1 + zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, armMass, sparseLaw_jointMass, sparseMass,
        sparseUnnormalizedMass]
      field_simp
      ring
    have hπ : propensity P x =
        ε * (1 - ε) * (1 + zv x) / (1 - ε + ε * zv x) := by
      rw [propensity, htrue, hcell]
      field_simp
    dsimp [P] at hπ ⊢
    rw [hπ]
    constructor
    · apply (le_div_iff₀ hc).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 2 * ε) hzx]
    · apply (div_le_iff₀ hc).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ε)
        (by linarith : 0 ≤ 1 - 2 * ε)]
  · intro x
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hS : 0 < sparseNormalizerFormula d ε M zv hz := by
      unfold sparseNormalizerFormula
      have hs : 0 ≤ ∑ x : Fin d, zv x := Finset.sum_nonneg (fun x _ => (hz x).1)
      have : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, zv x :=
        mul_nonneg (div_nonneg (le_of_lt hε) (le_of_lt hdR)) hs
      linarith [hεhalf]
    have hzx : 0 ≤ zv x := (hz x).1
    have hc : 0 < 1 - ε + ε * zv x := by nlinarith [mul_nonneg (le_of_lt hε) hzx]
    have ht : 0 < 1 + zv x := by linarith
    let P := sparseLaw (Nat.lt_of_lt_of_le (by decide : 0 < 2) hd)
      ε M ⟨hε, hεhalf⟩ zv hz
    have hcell : cellMass P x =
        (1 - ε + ε * zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, cellMass, sparseLaw_jointMass, sparseMass,
        sparseUnnormalizedMass]
      field_simp
      ring
    have htrue : armMass P true x =
        ε * (1 - ε) * (1 + zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, armMass, sparseLaw_jointMass, sparseMass,
        sparseUnnormalizedMass]
      field_simp
      ring
    have hfalse : armMass P false x =
        ((1 - ε) ^ 2 + ε ^ 2 * zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, armMass, sparseLaw_jointMass, sparseMass,
        sparseUnnormalizedMass]
      field_simp
    have hyt : jointMass P x true true =
        ε * (1 - ε) * zv x / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
      ring
    have hyf : jointMass P x false true =
        ((1 - ε) ^ 2 + ε ^ 2 * zv x) / (2 * d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
      ring
    have hε1 : 0 < 1 - ε := by linarith
    have hA : 0 < (1 - ε) ^ 2 + ε ^ 2 * zv x := by positivity
    dsimp [P] at hcell htrue hfalse hyt hyf ⊢
    refine ⟨hcell, ?_, ?_, ?_⟩
    · rw [propensity, htrue, hcell]
      field_simp
    · rw [outcomeMean, hyf, hfalse]
      field_simp
    · rw [outcomeMean, hyt, htrue]
      field_simp
  · let P := sparseLaw (Nat.lt_of_lt_of_le (by decide : 0 < 2) hd)
      ε M ⟨hε, hεhalf⟩ zv hz
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hS : 0 < sparseNormalizerFormula d ε M zv hz := by
      unfold sparseNormalizerFormula
      have hs : 0 ≤ ∑ x : Fin d, zv x :=
        Finset.sum_nonneg (fun x _ => (hz x).1)
      have : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, zv x :=
        mul_nonneg (div_nonneg (le_of_lt hε) (le_of_lt hdR)) hs
      linarith [hεhalf]
    have hden : 0 < (d : ℝ) * sparseNormalizerFormula d ε M zv hz := mul_pos hdR hS
    have hcell (x : Fin d) : cellMass P x =
        (1 - ε + ε * zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
      simp [P, cellMass, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
      field_simp
      ring
    have hmeans (x : Fin d) : outcomeMean P false x = 1 / 2 ∧
        outcomeMean P true x = zv x / (1 + zv x) := by
      have hzx : 0 ≤ zv x := (hz x).1
      have ht : 0 < 1 + zv x := by linarith
      have htrue : armMass P true x =
          ε * (1 - ε) * (1 + zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
        simp [P, armMass, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
        field_simp
        ring
      have hfalse : armMass P false x =
          ((1 - ε) ^ 2 + ε ^ 2 * zv x) / (d * sparseNormalizerFormula d ε M zv hz) := by
        simp [P, armMass, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
        field_simp
      have hyt : jointMass P x true true =
          ε * (1 - ε) * zv x / (d * sparseNormalizerFormula d ε M zv hz) := by
        simp [P, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
        ring
      have hyf : jointMass P x false true =
          ((1 - ε) ^ 2 + ε ^ 2 * zv x) / (2 * d * sparseNormalizerFormula d ε M zv hz) := by
        simp [P, sparseLaw_jointMass, sparseMass, sparseUnnormalizedMass]
        ring
      have hε1 : 0 < 1 - ε := by linarith
      have hA : 0 < (1 - ε) ^ 2 + ε ^ 2 * zv x := by positivity
      constructor
      · rw [outcomeMean, hyf, hfalse]
        field_simp
      · rw [outcomeMean, hyt, htrue]
        field_simp
    have hmax (x : Fin d) :
        max (1 / 2 : ℝ) (zv x / (1 + zv x)) =
          1 / 2 + max (zv x - 1) 0 / (2 * (1 + zv x)) := by
      have ht : 0 < 1 + zv x := by linarith [(hz x).1]
      rcases le_total (zv x) 1 with hle | hge
      · have hfrac : zv x / (1 + zv x) ≤ (1 / 2 : ℝ) := by
          apply (div_le_iff₀ ht).2
          linarith
        rw [max_eq_left hfrac, max_eq_right (by linarith : zv x - 1 ≤ 0)]
        ring
      · have hfrac : (1 / 2 : ℝ) ≤ zv x / (1 + zv x) := by
          apply (le_div_iff₀ ht).2
          linarith
        rw [max_eq_right hfrac, max_eq_left (by linarith : 0 ≤ zv x - 1)]
        field_simp
        ring
    have hpoint (x : Fin d) :
        cellMass P x * max (outcomeMean P false x) (outcomeMean P true x) =
          cellMass P x / 2 + phiEpsFormula ε (zv x) /
            (2 * d * sparseNormalizerFormula d ε M zv hz) := by
      rw [(hmeans x).1, (hmeans x).2, hmax, hcell]
      unfold phiEpsFormula
      have ht : 0 < 1 + zv x := by linarith [(hz x).1]
      field_simp
    have hsum : (∑ x : Fin d, cellMass P x) = 1 := by
      simp_rw [hcell]
      rw [← Finset.sum_div]
      have hnum : (∑ x : Fin d, (1 - ε + ε * zv x)) =
          (d : ℝ) * sparseNormalizerFormula d ε M zv hz := by
        simp [sparseNormalizerFormula, Finset.sum_add_distrib, ← Finset.mul_sum]
        field_simp
      rw [hnum]
      exact div_self hden.ne'
    dsimp [P] at hpoint hsum ⊢
    unfold observedValue
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, hsum]
    rw [← Finset.sum_div]
    ring
  · intro z w _ _
    have hstar (j : Fin 4) :
        0 < poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hMstar : 0 < sparseReference (_hMpaper := hM) M := by unfold sparseReference; linarith
      have hε1 : 0 < 1 - ε := by linarith
      fin_cases j <;> simp [poissonCellMean, cellIdx] <;> positivity
    have hfun (N : Fin 4 → ℕ) :
        oneCellLikelihood (hMpaper := hM) B n d ε M z N *
          oneCellLikelihood (hMpaper := hM) B n d ε M w N =
        ∏ j : Fin 4,
          (Real.exp (poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j -
            poissonCellMean B n d ε z j) *
              (poissonCellMean B n d ε z j /
                poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j) ^ N j) *
          (Real.exp (poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j -
            poissonCellMean B n d ε w j) *
              (poissonCellMean B n d ε w j /
                poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j) ^ N j) := by
      unfold oneCellLikelihood
      rw [← Finset.prod_mul_distrib]
    simp_rw [hfun]
    rw [show poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M) =
      Measure.pi (fun j : Fin 4 =>
        poissonMeasure (Real.toNNReal
          (poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j))) by rfl]
    rw [integral_fintype_prod_eq_prod (fun j : Fin 4 => fun k : ℕ =>
      (Real.exp (poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j -
        poissonCellMean B n d ε z j) *
          (poissonCellMean B n d ε z j /
            poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j) ^ k) *
      (Real.exp (poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j -
        poissonCellMean B n d ε w j) *
          (poissonCellMean B n d ε w j /
            poissonCellMean B n d ε (sparseReference (_hMpaper := hM) M) j) ^ k))]
    simp_rw [poisson_likelihood_gram_scalar _ _ _ (hstar _)]
    rw [← Real.exp_sum]
    congr 1
    simp [Fin.sum_univ_four, poissonCellMean, cellIdx,
      sparseGramCoefficient, sparseReference]
    field_simp
    ring
  -- @realizes \(\mu_{ax}\)(sparse regression values)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
