import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Risk
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathFactorization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathKL
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathModelCertificates
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathLocalExperiments
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessKL
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.LeCamTwoPoint
import Causalean.Stat.Sample.PiTransport
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- A tail event for a nonnegative integrable loss gives a lower bound on its mean. -/
-- @node: eventProbability_mul_threshold_le_risk
lemma eventProbability_mul_threshold_le_risk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hfmeas : Measurable f)
    (hf : Integrable f μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (s : ℝ) :
    s * μ.real {ω | s ≤ f ω} ≤ ∫ ω, f ω ∂μ := by
  have hs : MeasurableSet {ω | s ≤ f ω} :=
    measurableSet_le measurable_const hfmeas
  have hi : Integrable ({ω | s ≤ f ω}.indicator fun _ => s) μ :=
    (integrable_const s).indicator hs
  have hmono : ∀ᵐ ω ∂μ, ({ω | s ≤ f ω}.indicator fun _ => s) ω ≤ f ω := by
    filter_upwards [hf0] with ω hω
    by_cases h : s ≤ f ω
    · simp [h]
    · simp [h, hω]
  calc
    s * μ.real {ω | s ≤ f ω} =
        ∫ ω, ({ω | s ≤ f ω}.indicator fun _ => s) ω ∂μ := by
      rw [integral_indicator hs, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ ∫ ω, f ω ∂μ := integral_mono_ae hi hf hmono

/-- Distance to a fixed point is integrable for measurable maps into a compact metric space. -/
-- @node: compactMetric_distance_integrable
lemma compactMetric_distance_integrable {Ω Θ : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (est : Ω → Θ) (hest : Measurable est) (θ : Θ) :
    Integrable (fun ω => dist (est ω) θ) μ := by
  have hm : Measurable (fun ω => dist (est ω) θ) := hest.dist measurable_const
  apply (integrable_const (Metric.diam (Set.univ : Set Θ))).mono hm.aestronglyMeasurable
  filter_upwards with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, abs_of_nonneg Metric.diam_nonneg] using
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ (est ω)) (Set.mem_univ θ)

/-- Le Cam's inequality, tensorisation, and tail integration give an expected metric-risk
lower bound for one member of a two-point experiment. -/
-- @node: twoPoint_expectedMetricRisk_lower
lemma twoPoint_expectedMetricRisk_lower {Ω Θ : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] [SecondCountableTopology Θ] [MeasurableSpace Θ]
    [OpensMeasurableSpace Θ]
    (n : ℕ) (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ)
    (hKL : (n : ℝ) * (InformationTheory.klDiv μ ν).toReal ≤ 2 / 5)
    (est : (Fin n → Ω) → Θ) (hest : Measurable est) (θμ θν : Θ)
    (hiμ : Integrable (fun w => dist (est w) θμ) (Measure.pi (fun _ : Fin n => μ)))
    (hiν : Integrable (fun w => dist (est w) θν) (Measure.pi (fun _ : Fin n => ν))) :
    dist θμ θν / 8 ≤ ∫ w, dist (est w) θμ ∂Measure.pi (fun _ : Fin n => μ) ∨
      dist θμ θν / 8 ≤ ∫ w, dist (est w) θν ∂Measure.pi (fun _ : Fin n => ν) := by
  let Pμ := Measure.pi (fun _ : Fin n => μ)
  let Pν := Measure.pi (fun _ : Fin n => ν)
  have hprod := Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
    n μ ν hac hint
  have hprodBound : (InformationTheory.klDiv Pμ Pν).toReal ≤ 2 / 5 := by
    dsimp [Pμ, Pν]
    rw [hprod]
    exact hKL
  have hpinsker := Causalean.Stat.pinskerBound_pi_iid μ ν hac hint n
  have hprob := Causalean.Stat.klForm_two_point_lower_bound_of_pinsker
    (P₀ := Pμ) (P₁ := Pν) hpinsker hest
    (show 2 * (dist θμ θν / 2) ≤ dist θμ θν by linarith)
  have hsqrt : Real.sqrt ((InformationTheory.klDiv Pμ Pν).toReal / 2) ≤ 1 / 2 := by
    have hnonneg : 0 ≤ (InformationTheory.klDiv Pμ Pν).toReal / 2 := by positivity
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hquarter : (1 / 4 : ℝ) ≤
      max (Pμ.real {w | dist θμ θν / 2 ≤ dist (est w) θμ})
        (Pν.real {w | dist θμ θν / 2 ≤ dist (est w) θν}) := by
    linarith
  have hrμ := eventProbability_mul_threshold_le_risk Pμ
    (fun w => dist (est w) θμ) (hest.dist measurable_const) hiμ
    (Filter.Eventually.of_forall fun _ => dist_nonneg) (dist θμ θν / 2)
  have hrν := eventProbability_mul_threshold_le_risk Pν
    (fun w => dist (est w) θν) (hest.dist measurable_const) hiν
    (Filter.Eventually.of_forall fun _ => dist_nonneg) (dist θμ θν / 2)
  rcases le_total
      (Pμ.real {w | dist θμ θν / 2 ≤ dist (est w) θμ})
      (Pν.real {w | dist θμ θν / 2 ≤ dist (est w) θν}) with hle | hle
  · right
    have hp : 1 / 4 ≤ Pν.real {w | dist θμ θν / 2 ≤ dist (est w) θν} := by
      simpa [max_eq_right hle] using hquarter
    nlinarith [mul_le_mul_of_nonneg_left hp
      (div_nonneg (dist_nonneg : 0 ≤ dist θμ θν) (by norm_num : (0:ℝ) ≤ 2))]
  · left
    have hp : 1 / 4 ≤ Pμ.real {w | dist θμ θν / 2 ≤ dist (est w) θμ} := by
      simpa [max_eq_left hle] using hquarter
    nlinarith [mul_le_mul_of_nonneg_left hp
      (div_nonneg (dist_nonneg : 0 ≤ dist θμ θν) (by norm_num : (0:ℝ) ≤ 2))]

/-- The ℓ¹ loss between two simplex-valued vectors is integrable. -/
-- @node: simplexWeightLoss_integrable
lemma simplexWeightLoss_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (est : Ω → (Fin k → ℝ))
    (hest : Measurable est) (hestSimplex : ∀ w, InSimplex (est w))
    (target : Fin k → ℝ) (htarget : InSimplex target) :
    Integrable (fun w => ∑ i, |est w i - target i|) μ := by
  have hm : Measurable (fun w => ∑ i, |est w i - target i|) := by fun_prop
  apply (integrable_const (2 : ℝ)).mono hm.aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ∑ i, |est w i - target i| ≤ ∑ i, (est w i + target i) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le_iff.mpr ⟨by linarith [hestSimplex w |>.1 i, htarget.1 i],
        by linarith [hestSimplex w |>.1 i, htarget.1 i]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, (hestSimplex w).2, htarget.2]; norm_num

/-- The scalar-coordinate Le Cam bound lower-bounds the full simplex ℓ¹ risk. -/
-- @node: twoPoint_expectedWeightRisk_lower
lemma twoPoint_expectedWeightRisk_lower {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (n : ℕ) (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ)
    (hKL : (n : ℝ) * (InformationTheory.klDiv μ ν).toReal ≤ 2 / 5)
    (est : (Fin n → Ω) → (Fin k → ℝ)) (hest : Measurable est)
    (hestSimplex : ∀ w, InSimplex (est w)) (pμ pν : Fin k → ℝ)
    (hpμ : InSimplex pμ) (hpν : InSimplex pν) (i : Fin k) :
    |pμ i - pν i| / 8 ≤ ∫ w, ∑ j, |est w j - pμ j| ∂Measure.pi (fun _ : Fin n => μ) ∨
      |pμ i - pν i| / 8 ≤ ∫ w, ∑ j, |est w j - pν j| ∂Measure.pi (fun _ : Fin n => ν) := by
  have hiμ := simplexWeightLoss_integrable (Measure.pi (fun _ : Fin n => μ)) est hest
    hestSimplex pμ hpμ
  have hiν := simplexWeightLoss_integrable (Measure.pi (fun _ : Fin n => ν)) est hest
    hestSimplex pν hpν
  have hcμ : Integrable (fun w => |est w i - pμ i|) (Measure.pi (fun _ : Fin n => μ)) := by
    have hm : Measurable (fun w => |est w i - pμ i|) := by fun_prop
    exact hiμ.mono hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => by
      have hsum : 0 ≤ ∑ j, |est w j - pμ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum]
      exact Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => abs_nonneg (est w j - pμ j)) (Finset.mem_univ i))
  have hcν : Integrable (fun w => |est w i - pν i|) (Measure.pi (fun _ : Fin n => ν)) := by
    have hm : Measurable (fun w => |est w i - pν i|) := by fun_prop
    exact hiν.mono hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => by
      have hsum : 0 ≤ ∑ j, |est w j - pν j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum]
      exact Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => abs_nonneg (est w j - pν j)) (Finset.mem_univ i))
  have hscalar := twoPoint_expectedMetricRisk_lower n μ ν hac hint hKL
    (fun w => est w i) (by fun_prop) (pμ i) (pν i) (by simpa [Real.dist_eq] using hcμ)
      (by simpa [Real.dist_eq] using hcν)
  rw [Real.dist_eq] at hscalar
  rcases hscalar with h | h
  · left
    exact h.trans (integral_mono hcμ hiμ fun w => by
      simpa [Real.dist_eq] using
        (Finset.single_le_sum
          (fun j (_ : j ∈ Finset.univ) => abs_nonneg (est w j - pμ j)) (Finset.mem_univ i)))
  · right
    exact h.trans (integral_mono hcν hiν fun w => by
      simpa [Real.dist_eq] using
        (Finset.single_le_sum
          (fun j (_ : j ∈ Finset.univ) => abs_nonneg (est w j - pν j)) (Finset.mem_univ i)))

/-- Along the separated two-class path, ordering the quotient-law atoms preserves their latent
coordinate order. -/
-- @node: path_orderedMasses_eq_latentMass
lemma path_orderedMasses_eq_latentMass (g h : ℝ) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    orderedMasses (quotientLawRaw (pathLaw g h) (effectRadius 2 2 (1 / 10))) =
      latentMass (pathLaw g h) := by
  let lo : ℝ := 1 / 4 - g / 2
  let hi : ℝ := 1 / 4 + g / 2
  have hlt : lo < hi := by dsimp [lo, hi]; linarith
  have heff0 : latentEffect (pathLaw g h) (0 : Fin 2) = lo := by
    simpa [lo] using path_latentEffect g h hg.le hg1 hh (0 : Fin 2)
  have heff1 : latentEffect (pathLaw g h) (1 : Fin 2) = hi := by
    simpa [hi] using path_latentEffect g h hg.le hg1 hh (1 : Fin 2)
  have hmass0 : latentMass (pathLaw g h) (0 : Fin 2) = 2 / 5 + h := by
    simpa using path_latentMass g h hg.le hg1 hh (0 : Fin 2)
  have hmass1 : latentMass (pathLaw g h) (1 : Fin 2) = 3 / 5 - h := by
    simpa using path_latentMass g h hg.le hg1 hh (1 : Fin 2)
  have hfilter : (Finset.univ.filter fun i : Fin 2 =>
      0 < (quotientLawRaw (pathLaw g h)
        (effectRadius 2 2 (1 / 10))).weight i) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _hi
    change 0 < latentMass (pathLaw g h) i
    rw [path_latentMass g h hg.le hg1 hh i]
    have hb := abs_le.mp hh
    split_ifs <;> linarith
  have hgood :
      (∀ i, 0 < (quotientLawRaw (pathLaw g h)
        (effectRadius 2 2 (1 / 10))).weight i) ∧
        Function.Injective (quotientLawRaw (pathLaw g h)
          (effectRadius 2 2 (1 / 10))).atom := by
    constructor
    · intro i
      change 0 < latentMass (pathLaw g h) i
      rw [path_latentMass g h hg.le hg1 hh i]
      have hb := abs_le.mp hh
      split_ifs <;> linarith
    · intro i j hij
      change latentEffect (pathLaw g h) i = latentEffect (pathLaw g h) j at hij
      fin_cases i <;> fin_cases j <;> simp_all
  funext i
  unfold orderedMasses
  rw [if_pos hgood]
  have hle : lo ≤ hi := hlt.le
  have hflo : (Finset.univ.filter fun j : Fin 2 =>
      latentEffect (pathLaw g h) j < lo) = ∅ := by
    ext j
    fin_cases j <;> simp [heff0, heff1, hle]
  have hfhi : (Finset.univ.filter fun j : Fin 2 =>
      latentEffect (pathLaw g h) j < hi) = {0} := by
    ext j
    fin_cases j <;> simp [heff0, heff1, hlt]
  fin_cases i <;> simp [hflo, hfhi, quotientLawRaw,
    heff0, heff1, hmass0, hmass1]

/-- The ordered mass vector on the separated two-class path belongs to the probability simplex. -/
-- @node: path_orderedMasses_inSimplex
lemma path_orderedMasses_inSimplex (g h : ℝ) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    InSimplex (orderedMasses
      (quotientLawRaw (pathLaw g h) (effectRadius 2 2 (1 / 10)))) := by
  rw [path_orderedMasses_eq_latentMass g h hg hg1 hh]
  constructor
  · intro i
    rw [path_latentMass g h hg.le hg1 hh]
    have hb := abs_le.mp hh
    fin_cases i <;> simp <;> linarith
  · rw [Fin.sum_univ_two]
    simp_rw [path_latentMass g h hg.le hg1 hh]
    norm_num

/-- Calibrating by the inverse square-root signal bounds the squared product displacement. -/
-- @node: calibratedDisplacement_sample_signal_sq_le
lemma calibratedDisplacement_sample_signal_sq_le (a : ℝ) (n : ℕ) (g : ℝ)
    (hn : 1 ≤ n) (hg : 0 < g) :
    (n : ℝ) * g ^ 2 * (calibratedDisplacement a n g) ^ 2 ≤ a ^ 2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  let x := Real.sqrt n * g
  let m := min 1 x⁻¹
  have hx : 0 < x := mul_pos hsqrt hg
  have hm0 : 0 ≤ m := le_of_lt (lt_min (by norm_num) (inv_pos.mpr hx))
  have hm : x * m ≤ 1 := by
    calc
      x * m ≤ x * x⁻¹ := mul_le_mul_of_nonneg_left (min_le_right 1 x⁻¹) hx.le
      _ = 1 := mul_inv_cancel₀ hx.ne'
  have hsq : (n : ℝ) = (Real.sqrt n) ^ 2 := by
    symm
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hmulSq : (x * m) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le hm0]
  rw [calibratedDisplacement]
  change (n : ℝ) * g ^ 2 * (a * m) ^ 2 ≤ a ^ 2
  rw [hsq]
  nlinarith [sq_nonneg a]

set_option maxHeartbeats 800000 in
/-- Matching local converse witnesses for quotient-law and labeled-weight loss. The existential
law form avoids supremum junk values and is equivalent to the displayed minimax lower bounds. -/
-- @node: thm:matching-local-lower-bounds
theorem matching_local_lower_bounds :
    ∃ cLoc a c C : ℝ, LocalRadiusDomain cLoc ∧
      0 < a ∧ -- @realizes \(a\)(universal path amplitude in (0,1/8])
      a ≤ 1 / 8 ∧
      0 < c ∧ -- @realizes \(c\)(positive minimax lower-bound constant)
      0 < C ∧ -- @realizes \(C\)(positive path KL upper constant)
      ∀ n : ℕ, 1 ≤ n →
      (∀ est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10)),
        ∃ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          ∃ hLocal : LocalQuotientExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) P,
            (P = witnessLaw 0 ∨ P = witnessLaw (a / Real.sqrt n)) ∧
              c / Real.sqrt n ≤ expectedLawRisk P hLocal.toUCVMWModel est) ∧
      (∀ g : ℝ, GapScaleDomain g → ∀ est : WeightEstimator 2 2 2 n,
        ∃ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          ∃ hLocal : LocalWeightExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) (g := g) P,
            (P = pathLaw g 0 ∨ P = pathLaw g (calibratedDisplacement a n g)) ∧
              c * min 1 (Real.sqrt n * g)⁻¹ ≤
              expectedWeightRisk P
                (orderedMasses (quotientLawRaw P (effectRadius 2 2 (1 / 10)))) est) ∧
      (∃ (h0 : IsProbabilityMeasure (witnessLaw 0))
          (h1 : IsProbabilityMeasure (witnessLaw (a / Real.sqrt n))),
        letI := h0
        letI := h1
        ∃ (hM0 : LocalQuotientExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) (witnessLaw 0))
          (hM1 : LocalQuotientExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) (witnessLaw (a / Real.sqrt n))),
          InformationTheory.klDiv (obsLaw (witnessLaw (a / Real.sqrt n)))
             (obsLaw (witnessLaw 0)) ≤ ENNReal.ofReal (C / n) ∧
          c / Real.sqrt n ≤ AtomicLaw.LawModulo.wass1
            (quotientLaw (witnessLaw 0) hM0.toUCVMWModel)
            (quotientLaw (witnessLaw (a / Real.sqrt n)) hM1.toUCVMWModel)) ∧
      ∀ g : ℝ, GapScaleDomain g →
        let h := calibratedDisplacement a n g
        TangentAmplitudeDomain h ∧
        ∃ (hPath : IsProbabilityMeasure (pathLaw g h))
          (hBase : IsProbabilityMeasure (pathLaw g 0)),
          letI := hPath
          letI := hBase
          LocalWeightExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) (g := g)
              (pathLaw g h) ∧
            LocalWeightExperiment (n := n) (L := 2) (pi0 := 1 / 10)
              (sigma0 := 1 / 10) (cLoc := cLoc) (g := g)
              (pathLaw g 0) ∧
            InformationTheory.klDiv (obsLaw (pathLaw g h))
                (obsLaw (pathLaw g 0)) ≤ ENNReal.ofReal (C * g ^ 2 * h ^ 2) ∧
            (∑ i, |latentMass (pathLaw g h) i -
              latentMass (pathLaw g 0) i|) = 2 * |h| := by
  refine ⟨1 / 4, 1 / 3200, 1 / 25600, 16000, ?_, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  intro n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  let eps : ℝ := (1 / 3200) / Real.sqrt n
  have heps0 : 0 ≤ eps := by dsimp [eps]; positivity
  have heps1 : eps ≤ 1 / 8 := by
    have hsqrtOne : 1 ≤ Real.sqrt n := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    dsimp [eps]
    rw [div_le_iff₀ hsqrt]
    nlinarith
  have hepsLocal : 16000 * eps ^ 2 ≤ (1 / 4 : ℝ) / n := by
    have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    dsimp [eps]
    rw [div_pow, hsqrtSq]
    field_simp [hnR.ne']
    norm_num
  let hW0 : IsProbabilityMeasure (witnessLaw 0) :=
    witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  let hW1 : IsProbabilityMeasure (witnessLaw eps) :=
    witnessLaw_isProbabilityMeasure eps heps0 heps1
  letI := hW0
  letI := hW1
  have hM0 := witness_localQuotientExperiment n (1 / 4) 0
    (by exact ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
      (by norm_num only [zero_pow, mul_zero]; positivity)
  have hM1 := witness_localQuotientExperiment n (1 / 4) eps
    (by exact ⟨by norm_num, by norm_num⟩) heps0 heps1 hepsLocal
  have hWitnessKLReal :
      (InformationTheory.klDiv (obsLaw (witnessLaw eps))
        (obsLaw (witnessLaw 0))).toReal ≤ 16000 * eps ^ 2 := by
    calc
      _ ≤ (ENNReal.ofReal (16000 * eps ^ 2)).toReal :=
        ENNReal.toReal_mono (by finiteness)
          (witnessLaw_observed_kl_bound eps heps0 heps1)
      _ = 16000 * eps ^ 2 := ENNReal.toReal_ofReal (by positivity)
  have hWitnessProductKL :
      (n : ℝ) * (InformationTheory.klDiv (obsLaw (witnessLaw eps))
        (obsLaw (witnessLaw 0))).toReal ≤ 2 / 5 := by
    calc
      _ ≤ (n : ℝ) * ((1 / 4 : ℝ) / n) :=
        mul_le_mul_of_nonneg_left (hWitnessKLReal.trans hepsLocal) hnR.le
      _ = 1 / 4 := by field_simp [hnR.ne']
      _ ≤ 2 / 5 := by norm_num
  have hLawPair (est : LawEstimator 2 2 2 n (effectRadius 2 2 (1 / 10))) :
      (1 / 25600 : ℝ) / Real.sqrt n ≤
          expectedLawRisk (witnessLaw 0) hM0.toUCVMWModel est ∨
        (1 / 25600 : ℝ) / Real.sqrt n ≤
          expectedLawRisk (witnessLaw eps) hM1.toUCVMWModel est := by
    have hsep : dist
        (quotientLaw (witnessLaw 0) hM0.toUCVMWModel)
        (quotientLaw (witnessLaw eps) hM1.toUCVMWModel) = eps := by
      simpa using witness_quotientLaw_wass1 eps heps0 heps1
    have hsep' : dist
        (quotientLaw (witnessLaw eps) hM1.toUCVMWModel)
        (quotientLaw (witnessLaw 0) hM0.toUCVMWModel) = eps := by
      rw [dist_comm, hsep]
    have hscale : eps / 8 = (1 / 25600 : ℝ) / Real.sqrt n := by
      dsimp [eps]
      ring
    have hr := twoPoint_expectedMetricRisk_lower n
      (obsLaw (witnessLaw eps)) (obsLaw (witnessLaw 0))
      (witnessObsLaw_absolutelyContinuous eps heps0 heps1)
      (witnessObsLaw_llr_integrable eps heps0 heps1) hWitnessProductKL
      est.eval est.measurable
      (quotientLaw (witnessLaw eps) hM1.toUCVMWModel)
      (quotientLaw (witnessLaw 0) hM0.toUCVMWModel)
      (compactMetric_distance_integrable _ est.eval est.measurable _)
      (compactMetric_distance_integrable _ est.eval est.measurable _)
    rcases hr with hr | hr
    · right
      rw [hsep', hscale] at hr
      simpa only [expectedLawRisk, sampleLaw,
        AtomicLaw.LawModulo.dist_eq_wass1] using hr
    · left
      rw [hsep', hscale] at hr
      simpa only [expectedLawRisk, sampleLaw,
        AtomicLaw.LawModulo.dist_eq_wass1] using hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro est
    rcases hLawPair est with hr | hr
    · exact ⟨witnessLaw 0, hW0, hM0, Or.inl rfl, hr⟩
    · exact ⟨witnessLaw eps, hW1, hM1, Or.inr (by rfl), hr⟩
  · intro g hGap est
    obtain ⟨hg, hg1⟩ := hGap
    let h := calibratedDisplacement (1 / 3200) n g
    have hhmem := calibratedDisplacement_mem (1 / 3200) n g
      (by norm_num) (by norm_num) (Nat.zero_lt_of_lt hn) hg
    have hh0 : 0 < h := hhmem.1
    have hh : |h| ≤ 1 / 100 := by
      rw [abs_of_pos hh0]
      exact hhmem.2.trans (by norm_num)
    have hdomain : TangentAmplitudeDomain h := by
      constructor <;> linarith [hhmem.2]
    let hPath : IsProbabilityMeasure (pathLaw g h) :=
      pathLaw_isProbabilityMeasure g h hg.le hg1 hdomain hh
    let hBase : IsProbabilityMeasure (pathLaw g 0) :=
      pathLaw_isProbabilityMeasure g 0 hg.le hg1
        (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    letI := hPath
    letI := hBase
    have hcal := calibratedDisplacement_sample_signal_sq_le (1 / 3200) n g hn hg
    have hpathLocal : 16000 * g ^ 2 * h ^ 2 ≤ (1 / 4 : ℝ) / n := by
      apply (le_div_iff₀ hnR).2
      nlinarith
    have hLocalPath := path_localWeightExperiment n (1 / 4) g h
      (by exact ⟨by norm_num, by norm_num⟩) hg hg1 hh hpathLocal
    have hLocalBase := path_localWeightExperiment n (1 / 4) g 0
      (by exact ⟨by norm_num, by norm_num⟩) hg hg1 (by norm_num)
        (by norm_num only [zero_pow, mul_zero]; positivity)
    have hPathKLReal :
        (InformationTheory.klDiv (obsLaw (pathLaw g h))
          (obsLaw (pathLaw g 0))).toReal ≤ 16000 * g ^ 2 * h ^ 2 := by
      calc
        _ ≤ (ENNReal.ofReal (16000 * g ^ 2 * h ^ 2)).toReal :=
          ENNReal.toReal_mono (by finiteness)
            (pathLaw_observed_kl_bound g h hg.le hg1 hh)
        _ = 16000 * g ^ 2 * h ^ 2 := ENNReal.toReal_ofReal (by positivity)
    have hPathProductKL :
        (n : ℝ) * (InformationTheory.klDiv (obsLaw (pathLaw g h))
          (obsLaw (pathLaw g 0))).toReal ≤ 2 / 5 := by
      have hscaled := mul_le_mul_of_nonneg_left hPathKLReal hnR.le
      nlinarith
    have hweights := twoPoint_expectedWeightRisk_lower n
      (obsLaw (pathLaw g h)) (obsLaw (pathLaw g 0))
      (pathObsLaw_absolutelyContinuous g h hg.le hg1 hh)
      (pathObsLaw_llr_integrable g h hg.le hg1 hh) hPathProductKL
      est.eval est.measurable est.simplex
      (orderedMasses (quotientLawRaw (pathLaw g h) (effectRadius 2 2 (1 / 10))))
      (orderedMasses (quotientLawRaw (pathLaw g 0) (effectRadius 2 2 (1 / 10))))
      (path_orderedMasses_inSimplex g h hg hg1 hh)
      (path_orderedMasses_inSimplex g 0 hg hg1 (by norm_num)) 0
    have hcoord : |orderedMasses
        (quotientLawRaw (pathLaw g h) (effectRadius 2 2 (1 / 10))) 0 -
        orderedMasses
          (quotientLawRaw (pathLaw g 0) (effectRadius 2 2 (1 / 10))) 0| = h := by
      rw [path_orderedMasses_eq_latentMass g h hg hg1 hh,
        path_orderedMasses_eq_latentMass g 0 hg hg1 (by norm_num),
        path_latentMass g h hg.le hg1 hh, path_latentMass g 0 hg.le hg1 (by norm_num)]
      norm_num
      exact hh0.le
    rw [hcoord] at hweights
    have hscale : (1 / 25600 : ℝ) * min 1 (Real.sqrt n * g)⁻¹ = h / 8 := by
      dsimp [h, calibratedDisplacement]
      ring
    rw [hscale]
    rcases hweights with hr | hr
    · exact ⟨pathLaw g h, hPath, hLocalPath, Or.inr rfl,
        by simpa [expectedWeightRisk, sampleLaw] using hr⟩
    · exact ⟨pathLaw g 0, hBase, hLocalBase, Or.inl rfl,
        by simpa [expectedWeightRisk, sampleLaw] using hr⟩
  · refine ⟨hW0, hW1, hM0, hM1, ?_, ?_⟩
    · exact (witnessLaw_observed_kl_bound eps heps0 heps1).trans
        (ENNReal.ofReal_le_ofReal (by
          have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
          dsimp [eps]
          rw [div_pow, hsqrtSq]
          field_simp [hnR.ne']
          norm_num))
    · rw [witness_quotientLaw_wass1 eps heps0 heps1]
      dsimp [eps]
      exact div_le_div_of_nonneg_right (by norm_num) hsqrt.le
  · intro g hGap
    obtain ⟨hg, hg1⟩ := hGap
    dsimp only
    let h := calibratedDisplacement (1 / 3200) n g
    have hhmem := calibratedDisplacement_mem (1 / 3200) n g
      (by norm_num) (by norm_num) (Nat.zero_lt_of_lt hn) hg
    have hh0 : 0 < h := hhmem.1
    have hh : |h| ≤ 1 / 100 := by
      rw [abs_of_pos hh0]
      exact hhmem.2.trans (by norm_num)
    have hdomain : TangentAmplitudeDomain h := by
      constructor <;> linarith [hhmem.2]
    let hPath : IsProbabilityMeasure (pathLaw g h) :=
      pathLaw_isProbabilityMeasure g h hg.le hg1 hdomain hh
    let hBase : IsProbabilityMeasure (pathLaw g 0) :=
      pathLaw_isProbabilityMeasure g 0 hg.le hg1
        (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    letI := hPath
    letI := hBase
    have hcal := calibratedDisplacement_sample_signal_sq_le (1 / 3200) n g hn hg
    have hpathLocal : 16000 * g ^ 2 * h ^ 2 ≤ (1 / 4 : ℝ) / n := by
      apply (le_div_iff₀ hnR).2
      nlinarith
    refine ⟨hdomain, hPath, hBase,
      path_localWeightExperiment n (1 / 4) g h
        (by exact ⟨by norm_num, by norm_num⟩) hg hg1 hh hpathLocal,
      path_localWeightExperiment n (1 / 4) g 0
        (by exact ⟨by norm_num, by norm_num⟩) hg hg1 (by norm_num)
          (by norm_num only [zero_pow, mul_zero]; positivity),
      ?_, path_latentMass_l1_displacement g h hg.le hg1 hh⟩
    simpa [h] using pathLaw_observed_kl_bound g h hg.le hg1 hh

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
