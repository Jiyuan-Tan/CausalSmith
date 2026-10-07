module
public import Causalean.Stat.Minimax.ChiSquaredFinite
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FixedPoissonBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedAlphabetPadding
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedFixedPredictive
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedLargeParameters
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonCountBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonPredictive
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedProductPrior
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedSimplex
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetConcentration
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetTail
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarMomentPriors

/-!
# Finite fuzzy certificates for the paired multinomial experiment

Two finite priors certify a squared-risk lower bound when their L1 targets are
separated and their fixed-sample predictive laws are close. The certificate
uses the exact neutral two-sample experiment.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory
open scoped BigOperators ENNReal

/-- The alphabet logarithm is the logarithm of Euler's number times the
alphabet size. -/
noncomputable def logAlphabet (k : ℕ) : ℝ :=
  Real.log (Real.exp 1 * (k : ℝ))

/-- The alphabet logarithm is at least one for every nonempty alphabet. -/
theorem logAlphabet_one_le (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ logAlphabet k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkR
  unfold logAlphabet
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
  linarith

/-- A finite pair of priors on pairs of probability vectors, serving as fuzzy hypotheses
for the fixed two-sample experiment: each prior has finitely many atoms (at least one) with
weights summing to one; the second center exceeds the first by at least a positive
separation δ; under each prior, the atoms whose L1 distance lies farther than δ/4 from that
prior's center carry total weight at most 1/8; and the two prior mixtures of the two-sample
laws are within total variation distance 1/16. -/
structure FuzzyCertificate (n k : ℕ) where
  m : ℕ
  m_pos : 0 < m
  w₀ : Fin m → ℝ≥0∞
  w₁ : Fin m → ℝ≥0∞
  w₀_sum : ∑ i, w₀ i = 1
  w₁_sum : ∑ i, w₁ i = 1
  θ₀ : Fin m → ProbabilitySimplex k × ProbabilitySimplex k
  θ₁ : Fin m → ProbabilitySimplex k × ProbabilitySimplex k
  center₀ : ℝ
  center₁ : ℝ
  delta : ℝ
  delta_pos : 0 < delta
  center_sep : delta ≤ center₁ - center₀
  bad₀ : (∑ i, if delta / 4 < |simplexL1 (θ₀ i).1 (θ₀ i).2 - center₀|
    then w₀ i else 0) ≤ 1 / 8
  bad₁ : (∑ i, if delta / 4 < |simplexL1 (θ₁ i).1 (θ₁ i).2 - center₁|
    then w₁ i else 0) ≤ 1 / 8
  predictive_close :
    Causalean.Stat.tvDist
      (Causalean.Stat.mixture w₀ (fun i => twoSampleLaw n (θ₀ i)))
      (Causalean.Stat.mixture w₁ (fun i => twoSampleLaw n (θ₁ i))) ≤ 1 / 16

/-- Zero-mass alphabet padding carries a finite fuzzy certificate to every
larger alphabet without changing its target separation.

Pad each parameter pair with `padSimplex`, use `padSimplex_l1` for the two
target-tail fields, and use `twoSampleLaw_pad` plus contraction of total
variation under the common measurable relabeling map for predictive closeness.
-/
theorem FuzzyCertificate.pad {n r k : ℕ} (W : FuzzyCertificate n r)
    (h : r ≤ k) :
    ∃ V : FuzzyCertificate n k, V.delta = W.delta := by
  let f : ((Fin n → Fin r) × (Fin n → Fin r)) →
      ((Fin n → Fin k) × (Fin n → Fin k)) :=
    fun z => ((fun i => Fin.castLE h (z.1 i)), (fun i => Fin.castLE h (z.2 i)))
  have hf : Measurable f := measurable_of_finite f
  have hmap (w : Fin W.m → ℝ≥0∞)
      (θ : Fin W.m → ProbabilitySimplex r × ProbabilitySimplex r) :
      Causalean.Stat.mixture w
        (fun i => twoSampleLaw n (padSimplex h (θ i).1, padSimplex h (θ i).2)) =
      Measure.map f (Causalean.Stat.mixture w (fun i => twoSampleLaw n (θ i))) := by
    unfold Causalean.Stat.mixture
    rw [Measure.map_finset_sum' hf.aemeasurable]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.map_smul, twoSampleLaw_pad]
  let μ₀ := Causalean.Stat.mixture W.w₀ (fun i => twoSampleLaw n (W.θ₀ i))
  let μ₁ := Causalean.Stat.mixture W.w₁ (fun i => twoSampleLaw n (W.θ₁ i))
  letI : IsProbabilityMeasure μ₀ := Causalean.Stat.mixture_isProbabilityMeasure
    W.w₀ W.w₀_sum _
  letI : IsProbabilityMeasure μ₁ := Causalean.Stat.mixture_isProbabilityMeasure
    W.w₁ W.w₁_sum _
  have hcontract : Causalean.Stat.tvDist (Measure.map f μ₀) (Measure.map f μ₁) ≤
      Causalean.Stat.tvDist μ₀ μ₁ := by
    unfold Causalean.Stat.tvDist
    apply ciSup_le
    rintro ⟨A, hA⟩
    rw [map_measureReal_apply_of_aemeasurable hf.aemeasurable hA,
      map_measureReal_apply_of_aemeasurable hf.aemeasurable hA]
    exact le_ciSup Causalean.Stat.bddAbove_tvDist_range
      ⟨f ⁻¹' A, hA.preimage hf⟩
  refine ⟨{
    m := W.m
    m_pos := W.m_pos
    w₀ := W.w₀
    w₁ := W.w₁
    w₀_sum := W.w₀_sum
    w₁_sum := W.w₁_sum
    θ₀ := fun i => (padSimplex h (W.θ₀ i).1, padSimplex h (W.θ₀ i).2)
    θ₁ := fun i => (padSimplex h (W.θ₁ i).1, padSimplex h (W.θ₁ i).2)
    center₀ := W.center₀
    center₁ := W.center₁
    delta := W.delta
    delta_pos := W.delta_pos
    center_sep := W.center_sep
    bad₀ := ?_
    bad₁ := ?_
    predictive_close := ?_
  }, rfl⟩
  · simpa only [padSimplex_l1] using W.bad₀
  · simpa only [padSimplex_l1] using W.bad₁
  · rw [hmap W.w₀ W.θ₀, hmap W.w₁ W.θ₁]
    exact hcontract.trans W.predictive_close

/-- A two-point fixed-sample experiment on the binary alphabet admits fuzzy
certificates with squared separation at least a positive constant over the
sample size, uniformly for sample sizes above four.

Use one atom per prior. Keep the first multinomial law fixed and move the
second law from the uniform binary vector by a small tilt proportional to
`1 / sqrt n`. The target gaps are deterministic. Bound predictive total
variation using the finite chi-squared formula and iid tensorization.
-/
theorem binary_fuzzyCertificate :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 4 < n →
      ∃ W : FuzzyCertificate n 2,
        a / (n : ℝ) ≤ W.delta ^ 2 := by
  refine ⟨1 / 4096, by norm_num, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hn0.le
  let t : ℝ := 1 / (64 * Real.sqrt (n : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    have hnr : (4 : ℝ) < n := by exact_mod_cast hn
    have hroot : 1 ≤ Real.sqrt (n : ℝ) := by
      nlinarith [hsqrt_sq]
    apply (div_le_iff₀ (by positivity : 0 < 64 * Real.sqrt (n : ℝ))).2
    linarith
  have ht_sq : t ^ 2 = 1 / (4096 * (n : ℝ)) := by
    dsimp [t]
    rw [div_pow, mul_pow, hsqrt_sq]
    norm_num
  let R : ProbabilitySimplex 2 := ⟨fun _ => 1/2, by
    constructor
    · intro i; norm_num
    · simp⟩
  let S : ProbabilitySimplex 2 := ⟨fun i => if i = 0 then (1+t)/2 else (1-t)/2, by
    constructor
    · intro i; fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_two]; ring⟩
  have hL1 : simplexL1 R S = t := by
    simp [simplexL1, R, S, Fin.sum_univ_two]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring
  have hRmass (i : Fin 2) : ((simplexPMF R).toMeasure).real {i} = 1/2 := by
    simp [measureReal_def, simplexPMF, R]
  have hSmass (i : Fin 2) : ((simplexPMF S).toMeasure).real {i} =
      if i = 0 then (1+t)/2 else (1-t)/2 := by
    simp [measureReal_def, simplexPMF, S,
      show 0 ≤ (if i = 0 then (1+t)/2 else (1-t)/2) from S.2.1 i]
  have hac : (simplexPMF S).toMeasure ≪ (simplexPMF R).toMeasure := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hnull
    have hempty : s = ∅ := by
      ext i
      constructor
      · intro hi
        have hle : (simplexPMF R).toMeasure {i} ≤ (simplexPMF R).toMeasure s :=
          measure_mono (Set.singleton_subset_iff.mpr hi)
        rw [hnull] at hle
        have hzero : ((simplexPMF R).toMeasure).real {i} = 0 := by
          simp [measureReal_def, bot_unique hle]
        linarith [hRmass i]
      · simp
    simp [hempty]
  have hchi : 1 + Causalean.Stat.chiSqDiv (simplexPMF S).toMeasure
      (simplexPMF R).toMeasure = 1 + t ^ 2 := by
    rw [Causalean.Stat.finite_one_add_chiSqDiv _ _ hac]
    simp only [Fin.sum_univ_two, hRmass, hSmass]
    norm_num
    ring
  have hpiac : simplexSampleLaw S n ≪ simplexSampleLaw R n := by
    exact Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      _ _ hac n
  have hpichi : 1 + Causalean.Stat.chiSqDiv (simplexSampleLaw S n)
      (simplexSampleLaw R n) = (1 + t ^ 2) ^ n := by
    exact (Causalean.Stat.one_add_chiSqDiv_pi_iid _ _ hac n).trans (by rw [hchi])
  have hnt : (n : ℝ) * t ^ 2 = 1 / 4096 := by
    rw [ht_sq]
    field_simp
  have hpow : (1 + t ^ 2) ^ n ≤ 4096 / 4095 := by
    calc
      (1 + t ^ 2) ^ n ≤ (Real.exp (t ^ 2)) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (t ^ 2)]
      _ = Real.exp ((n : ℝ) * t ^ 2) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (1 / 4096) := by rw [hnt]
      _ ≤ 1 / (1 - 1 / 4096) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 4096 / 4095 := by norm_num
  have hpichi_le : Causalean.Stat.chiSqDiv (simplexSampleLaw S n)
      (simplexSampleLaw R n) ≤ 1 / 64 := by
    linarith [hpichi, hpow]
  have htvPi : Causalean.Stat.tvDist (simplexSampleLaw S n)
      (simplexSampleLaw R n) ≤ 1 / 16 := by
    have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
      (simplexSampleLaw S n) (simplexSampleLaw R n) hpiac (Integrable.of_finite)
    have hsqrtle : Real.sqrt (Causalean.Stat.chiSqDiv
        (simplexSampleLaw S n) (simplexSampleLaw R n)) ≤ 1 / 8 := by
      exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [hpichi_le]⟩
    linarith
  have hprod : Causalean.Stat.tvDist (twoSampleLaw n (R, R))
      (twoSampleLaw n (R, S)) ≤ 1 / 16 := by
    have hself : Causalean.Stat.tvDist (simplexSampleLaw R n)
        (simplexSampleLaw R n) = 0 := by
      simp [Causalean.Stat.tvDist]
    calc
      Causalean.Stat.tvDist (twoSampleLaw n (R, R)) (twoSampleLaw n (R, S)) ≤
          Causalean.Stat.tvDist (simplexSampleLaw R n) (simplexSampleLaw R n) +
          Causalean.Stat.tvDist (simplexSampleLaw R n) (simplexSampleLaw S n) := by
            exact Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add
              _ _ _ _
      _ = Causalean.Stat.tvDist (simplexSampleLaw S n)
          (simplexSampleLaw R n) := by
            rw [hself, zero_add, Causalean.Stat.tvDist_symm]
      _ ≤ 1 / 16 := htvPi
  have hnot : ¬ t / 4 < 0 := by linarith [ht]
  refine ⟨{
    m := 1
    m_pos := by omega
    w₀ := fun _ => 1
    w₁ := fun _ => 1
    w₀_sum := by simp
    w₁_sum := by simp
    θ₀ := fun _ => (R, R)
    θ₁ := fun _ => (R, S)
    center₀ := 0
    center₁ := t
    delta := t
    delta_pos := ht
    center_sep := by simp
    bad₀ := by
      simp [simplexL1_self, hnot]
    bad₁ := by
      simp [hL1, hnot]
    predictive_close := by
      simpa [Causalean.Stat.mixture] using hprod
  }, ?_⟩
  rw [ht_sq]
  field_simp
  exact le_refl _

/-- Above a universal alphabet threshold, balanced moment priors give fixed
sample fuzzy certificates at the alphabet-over-samples logarithmic rate.

Take the parameters from `exists_pairedLargeParameters` and the scalar prior
from `exists_scalarMomentPriors`. The product prior supplies the weights and
centers; use `pairedProductTarget_bad_mass_le` for concentration and
`pairedFixedPredictive_tv_le` for predictive closeness. Finally pad from
`2 * b` cells to `k` cells using `FuzzyCertificate.pad`.
-/
theorem largeAlphabet_fuzzyCertificate :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ k n : ℕ, K ≤ k → k ^ 2 < n →
        ∃ W : FuzzyCertificate n k,
          a * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) ≤ W.delta ^ 2 := by
  classical
  obtain ⟨a, ha, K, hK, hparams⟩ := exists_pairedLargeParameters
  refine ⟨a, ha, K, hK, ?_⟩
  intro k n hk hn
  obtain ⟨b, L, t, δ, hb, hL, hbk, ht, ht1, hδ, hscale, hvar,
    hclose, hδgap, hrate⟩ := hparams k n hk hn
  obtain ⟨P⟩ := exists_scalarMomentPriors L (by omega)
  let e : Fin (Fintype.card (Fin b → Fin P.m)) ≃ (Fin b → Fin P.m) :=
    (Fintype.equivFin _).symm
  let θ (i : Fin (Fintype.card (Fin b → Fin P.m))) :=
    (pairedBaseVector b hb,
      pairedTiltVector b hb t ht ht1 (pairedNodeVector P (e i))
        (pairedNodeVector_abs_le_one P (e i)))
  let w (side : Bool) (i : Fin (Fintype.card (Fin b → Fin P.m))) :=
    pairedProductWeight P b side (e i)
  let c (side : Bool) :=
    ∑ i, (w side i).toReal * simplexL1 (θ i).1 (θ i).2
  letI : Nonempty (Fin b → Fin P.m) := ⟨fun _ => ⟨0, P.m_pos⟩⟩
  have hsum (side : Bool) : ∑ i, w side i = 1 := by
    exact (e.sum_comp (pairedProductWeight P b side)).trans
      (pairedProductWeight_sum P b side)
  have hmean (side : Bool) :
      c side = t * ∑ i : Fin P.m,
        scalarPriorWeight P side i * |P.node i| := by
    let f (u : Fin b → Fin P.m) :=
      (pairedProductWeight P b side u).toReal *
        simplexL1 (pairedBaseVector b hb)
          (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
            (pairedNodeVector_abs_le_one P u))
    change (∑ i, f (e i)) = _
    rw [e.sum_comp]
    exact pairedProductTarget_mean P b hb t ht ht1 side
  have hbad (side : Bool) :
      (∑ i, if δ / 4 < |simplexL1 (θ i).1 (θ i).2 - c side|
        then w side i else 0) ≤ (1 / 8 : ℝ≥0∞) := by
    rw [hmean side]
    let f (u : Fin b → Fin P.m) : ℝ≥0∞ :=
      if δ / 4 < |simplexL1 (pairedBaseVector b hb)
          (pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
            (pairedNodeVector_abs_le_one P u)) -
            t * (∑ j : Fin P.m, scalarPriorWeight P side j * |P.node j|)|
      then pairedProductWeight P b side u else 0
    change (∑ i, f (e i)) ≤ _
    rw [e.sum_comp]
    exact pairedProductTarget_bad_mass_le P b hb t ht ht1 δ hδ hvar side
  have hsep : δ ≤ c true - c false := by
    rw [hmean true, hmean false]
    have hgap := P.abs_gap
    have hmul := mul_le_mul_of_nonneg_left hgap ht
    have hδ' : δ ≤ t * ((1 / 50 : ℝ) / (L : ℝ)) := hδgap
    simpa [scalarPriorWeight, mul_sub] using hδ'.trans hmul
  have hpred :
      Causalean.Stat.tvDist
        (Causalean.Stat.mixture (w false) (fun i => twoSampleLaw n (θ i)))
        (Causalean.Stat.mixture (w true) (fun i => twoSampleLaw n (θ i))) ≤
        1 / 16 := by
    have htv := pairedFixedPredictive_tv_le P b n hb t ht ht1 hscale
    have hleft (side : Bool) :
        Causalean.Stat.mixture (w side) (fun i => twoSampleLaw n (θ i)) =
          pairedFixedPredictive P b n hb t ht ht1 side := by
      let f (u : Fin b → Fin P.m) :=
        pairedProductWeight P b side u •
          twoSampleLaw n (pairedBaseVector b hb,
            pairedTiltVector b hb t ht ht1 (pairedNodeVector P u)
              (pairedNodeVector_abs_le_one P u))
      change (∑ i, f (e i)) = _
      rw [e.sum_comp]
      rfl
    rw [hleft false, hleft true]
    exact htv.trans hclose
  let W : FuzzyCertificate n (b * 2) := {
    m := Fintype.card (Fin b → Fin P.m)
    m_pos := Fintype.card_pos
    w₀ := w false
    w₁ := w true
    w₀_sum := hsum false
    w₁_sum := hsum true
    θ₀ := θ
    θ₁ := θ
    center₀ := c false
    center₁ := c true
    delta := δ
    delta_pos := hδ
    center_sep := hsep
    bad₀ := hbad false
    bad₁ := hbad true
    predictive_close := hpred }
  obtain ⟨V, hV⟩ := W.pad hbk
  refine ⟨V, ?_⟩
  simpa only [hV, W, logAlphabet] using hrate

/-- For every finite alphabet bound, binary fuzzy certificates extend to all
alphabet sizes below that bound with one positive rate constant.

Pad `binary_fuzzyCertificate` to `k` using `FuzzyCertificate.pad`; the finite
bound `k < K` converts its `1/n` gap to `k/(n*logAlphabet k)` after proving
`logAlphabet k ≥ 1` for `k ≥ 2`.
-/
theorem boundedAlphabet_fuzzyCertificate (K : ℕ) (hK : 2 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ ∀ k n : ℕ, 2 ≤ k → k < K → k ^ 2 < n →
      ∃ W : FuzzyCertificate n k,
        a * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) ≤ W.delta ^ 2 := by
  obtain ⟨a, ha, hbinary⟩ := binary_fuzzyCertificate
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  refine ⟨a / (K : ℝ), by positivity, ?_⟩
  intro k n hk hkK hn
  have hn4 : 4 < n := by nlinarith
  obtain ⟨W, hW⟩ := hbinary n hn4
  obtain ⟨V, hV⟩ := W.pad hk
  refine ⟨V, ?_⟩
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt hkK)
  have hlog : 1 ≤ logAlphabet k := logAlphabet_one_le k (by omega)
  have hlogpos : 0 < logAlphabet k := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfrac : (k : ℝ) / ((K : ℝ) * logAlphabet k) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hKpos hlogpos)).2
    calc
      (k : ℝ) ≤ K := hkR
      _ = (K : ℝ) * 1 := by ring
      _ ≤ (K : ℝ) * logAlphabet k := mul_le_mul_of_nonneg_left hlog hKpos.le
      _ = 1 * ((K : ℝ) * logAlphabet k) := by ring
  calc
    (a / (K : ℝ)) * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) =
        (a / (n : ℝ)) * ((k : ℝ) / ((K : ℝ) * logAlphabet k)) := by ring
    _ ≤ (a / (n : ℝ)) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = a / (n : ℝ) := by ring
    _ ≤ V.delta ^ 2 := by simpa only [hV] using hW

/-- [There is a universal constant a > 0 such that for every alphabet size k ≥ 2 and every sample size n > k² a fuzzy certificate exists whose separation δ satisfies δ² ≥ a · k / (n · log(e·k))](goal). -/
theorem largeSample_fuzzyCertificate :
    ∃ a : ℝ, 0 < a ∧ ∀ k n : ℕ, 2 ≤ k → k ^ 2 < n →
      ∃ W : FuzzyCertificate n k,
        a * ((k : ℝ) / ((n : ℝ) * logAlphabet k)) ≤ W.delta ^ 2 := by
  obtain ⟨a₁, ha₁, K, hK, hlarge⟩ := largeAlphabet_fuzzyCertificate
  obtain ⟨a₂, ha₂, hbounded⟩ := boundedAlphabet_fuzzyCertificate K hK
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
  intro k n hk hn
  have hrate : 0 ≤ (k : ℝ) / ((n : ℝ) * logAlphabet k) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < logAlphabet k := by
      have h := logAlphabet_one_le k (by omega)
      linarith
    positivity
  rcases lt_or_ge k K with hsmall | hlargeK
  · obtain ⟨W, hW⟩ := hbounded k n hk hsmall hn
    exact ⟨W, (mul_le_mul_of_nonneg_right (min_le_right a₁ a₂) hrate).trans hW⟩
  · obtain ⟨W, hW⟩ := hlarge k n hlargeK hn
    exact ⟨W, (mul_le_mul_of_nonneg_right (min_le_left a₁ a₂) hrate).trans hW⟩

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
