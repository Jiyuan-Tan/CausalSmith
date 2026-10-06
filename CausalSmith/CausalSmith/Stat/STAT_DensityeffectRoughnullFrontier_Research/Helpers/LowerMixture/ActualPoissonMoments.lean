module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.NullOutcomes
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OrderedPoisson
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
Cross moments under the actual localized Poisson null laws. Exponential count
bounds justify integration over the complete random-count sample, and identify
its likelihood cross moment with the coefficient series in equation (31).
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The localized likelihood is measurable on each actual count fiber. -/
-- @node: measurable_lowerActualCellRatio
@[fun_prop] lemma measurable_lowerActualCellRatio (theta : ℝ) (k j m : ℕ)
    (r : Fin k) (omega : Fin j → Bool) :
    Measurable (lowerActualCellRatio theta k j m r omega) := by
  have hm : Measurable (fun o : Data m =>
      (lowerLocalizedCellData k m r o, fun i => Y (o i))) := by
    apply (measurable_lowerLocalizedCellData k m r).prodMk
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).snd).snd
  convert (measurable_lowerCellOutcomeLikelihood m j (lowerTau theta k)
    (lowerGamma theta j) omega).comp hm using 1
  funext o
  rfl

/-- The finite subset envelope is a power of one numerical count factor. -/
-- @node: lowerActualCellRatio_abs_le_pow
lemma lowerActualCellRatio_abs_le_pow (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega : Fin j → Bool) (o : Data m) :
    |lowerActualCellRatio theta k j m r omega o| ≤
      (1 + 4 * |lowerGamma theta j|) ^ m := by
  have h := lowerCellOutcomeLikelihood_abs_bound (lowerTau theta k) (lowerGamma theta j)
    (by rw [abs_of_nonneg (lowerTau_mem_Icc theta k j hp).1]
        exact (lowerTau_mem_Icc theta k j hp).2)
    (lowerLocalizedCellData k m r o).1 (fun i => lowerBump_abs_le_one _)
    (lowerLocalizedCellData k m r o).2.1 j omega (fun i => Y (o i))
  have hs := Finset.prod_one_add (f := fun _ : Fin m => 4 * |lowerGamma theta j|)
    (Finset.univ : Finset (Fin m))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hs
  exact h.trans_eq hs.symm

/-- The true localized Poisson null mixture shares one propensity sign throughout
its random-count sample. -/
-- @node: lowerLocalizedPoissonNull
def lowerLocalizedPoissonNull (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega : Fin j → Bool) (xi : NNReal) :
    Measure (FiniteSample Omega) :=
  Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
    finitePoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) xi)

/-- The actual localized Poisson null mixture is normalized. -/
-- @node: lowerLocalizedPoissonNull_probability
instance lowerLocalizedPoissonNull_probability (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega : Fin j → Bool) (xi : NNReal) :
    IsProbabilityMeasure (lowerLocalizedPoissonNull theta k j hp r omega xi) :=
  Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _

/-- The localized Poisson null law is the sum of its embedded, shared-sign
fixed-count sample laws. -/
-- @node: lowerLocalizedPoissonNull_eq_sum
lemma lowerLocalizedPoissonNull_eq_sum (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega : Fin j → Bool) (xi : NNReal) :
    lowerLocalizedPoissonNull theta k j hp r omega xi =
      Measure.sum (fun m => poissonMeasure xi {m} •
        (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
          Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))).map
          (fixedSizeEmbed m)) := by
  have hcover : (⋃ m : ℕ,
      (FiniteSample.count : FiniteSample Omega → ℕ) ⁻¹' {m}) = Set.univ := by
    ext s
    simp
  have hdis : Pairwise (Function.onFun Disjoint
      (fun m : ℕ => (FiniteSample.count : FiniteSample Omega → ℕ) ⁻¹' {m})) := by
    intro m n hmn
    exact (Set.disjoint_singleton.mpr hmn).preimage _
  rw [← Measure.restrict_univ (μ := lowerLocalizedPoissonNull theta k j hp r omega xi),
    ← hcover, Measure.restrict_iUnion hdis
      (fun m => (measurableSet_singleton m).preimage measurable_finiteSample_count)]
  congr 1
  funext m
  unfold lowerLocalizedPoissonNull Causalean.Stat.Minimax.Mixture.uniformMixture
    Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.restrict_add]
  simp only [Measure.restrict_smul, finitePoissonSampleLaw_restrict_count_eq]
  rw [Fintype.sum_bool, Measure.map_add _ _ (measurable_fixedSizeEmbed m)]
  simp only [Measure.map_smul, smul_add]
  congr 1 <;> rw [smul_comm]

/-- Likelihood products on the complete actual cell Poisson experiment are
integrable, by a deterministic exponential envelope and the Poisson moments. -/
-- @node: lowerActualCellRatio_poisson_pair_integrable
lemma lowerActualCellRatio_poisson_pair_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega op : Fin j → Bool) (xi : NNReal) :
    Integrable (fun s : FiniteSample Omega =>
      lowerActualCellRatio theta k j s.count r omega s.points *
        lowerActualCellRatio theta k j s.count r op s.points)
      (lowerLocalizedPoissonNull theta k j hp r omega xi) := by
  let B : ℝ := (1 + 4 * |lowerGamma theta j|) ^ 2
  have hB : 0 ≤ B := sq_nonneg _
  have hm : Measurable (fun s : FiniteSample Omega =>
      lowerActualCellRatio theta k j s.count r omega s.points *
        lowerActualCellRatio theta k j s.count r op s.points) := by
    -- Count-fiber measurability works for arbitrary codomains by the same iInf argument.
    intro A hA
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    exact ((measurable_lowerActualCellRatio theta k j m r omega).mul
      (measurable_lowerActualCellRatio theta k j m r op)) hA
  have hb : Integrable (fun m : ℕ => B ^ m) (poissonMeasure xi) := by
    simpa using Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integrable_poisson_tilted_factorial
      xi hB 0
  have hi (b : Bool) : Integrable (fun s : FiniteSample Omega => B ^ s.count)
      (finitePoissonSampleLaw (lowerLocalizedNullLaw theta k j hp r b omega) xi) := by
    have hmap := finitePoissonSampleLaw_map_count
      (lowerLocalizedNullLaw theta k j hp r b omega) xi
    apply (integrable_map_measure (by fun_prop) measurable_finiteSample_count.aemeasurable).mp
    rw [hmap]
    exact hb
  have hi' : Integrable (fun s : FiniteSample Omega => B ^ s.count)
      (lowerLocalizedPoissonNull theta k j hp r omega xi) := by
    unfold lowerLocalizedPoissonNull Causalean.Stat.Minimax.Mixture.uniformMixture
      Causalean.Stat.mixture
    apply integrable_finsetSum_measure.mpr
    intro b hb
    exact (hi b).smul_measure (by simp)
  apply hi'.mono' hm.aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (1 + 4 * |lowerGamma theta j|) ^ s.count *
        (1 + 4 * |lowerGamma theta j|) ^ s.count :=
      mul_le_mul (lowerActualCellRatio_abs_le_pow theta k j s.count hp r omega s.points)
        (lowerActualCellRatio_abs_le_pow theta k j s.count hp r op s.points)
        (abs_nonneg _) (by positivity)
    _ = B ^ s.count := by dsimp [B]; rw [pow_right_comm]; ring

/-- The complete actual Poisson cell likelihood cross moment is K(z), including
its empty-count fiber. The count exchange uses derived integrability. -/
-- @node: lowerActualCellRatio_poisson_cross_moment
lemma lowerActualCellRatio_poisson_cross_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega op : Fin j → Bool) (xi : NNReal) :
    (∫ s : FiniteSample Omega,
      lowerActualCellRatio theta k j s.count r omega s.points *
        lowerActualCellRatio theta k j s.count r op s.points
      ∂lowerLocalizedPoissonNull theta k j hp r omega xi) =
    lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
      (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) := by
  let f : FiniteSample Omega → ℝ := fun s =>
    lowerActualCellRatio theta k j s.count r omega s.points *
      lowerActualCellRatio theta k j s.count r op s.points
  have hm : Measurable f := by
    intro A hA
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    exact ((measurable_lowerActualCellRatio theta k j m r omega).mul
      (measurable_lowerActualCellRatio theta k j m r op)) hA
  have hi := lowerActualCellRatio_poisson_pair_integrable theta k j hp r omega op xi
  rw [lowerLocalizedPoissonNull_eq_sum theta k j hp r omega xi] at hi ⊢
  rw [integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  have hmap (m : ℕ) :
      (∫ x, f x ∂(Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))).map
        (fixedSizeEmbed m)) =
      ∫ o : Data m, lowerActualCellRatio theta k j m r omega o *
        lowerActualCellRatio theta k j m r op o
        ∂Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
          Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)) :=
    integral_map (measurable_fixedSizeEmbed m).aemeasurable hm.aestronglyMeasurable
  change (∑' m : ℕ, (poissonMeasure xi {m}).toReal •
    ∫ x, f x ∂(Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
      Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))).map
      (fixedSizeEmbed m)) = _
  simp_rw [hmap]
  have hn : Integrable (fun m : ℕ => ∫ o : Data m,
      lowerActualCellRatio theta k j m r omega o * lowerActualCellRatio theta k j m r op o
      ∂Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)))
      (poissonMeasure xi) := by
    simp_rw [lowerActualCellRatio, lower_localized_outcome_cross_moment theta k j _ hp hk]
    exact lowerCellOutcomeCrossMoment_poisson_integrable _ _ xi _ j omega op
  have hc := integral_countable hn
  simp only [measureReal_def, smul_eq_mul] at hc ⊢
  change (∑' m : ℕ, (poissonMeasure xi {m}).toReal * ∫ o : Data m,
      lowerActualCellRatio theta k j m r omega o * lowerActualCellRatio theta k j m r op o
      ∂Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))) = _
  rw [← hc]
  exact lower_localized_outcome_poisson_cross_moment theta k j hp hk r omega op xi

/-- Cross products of cell likelihoods are integrable under the actual independent
Poisson cell null laws. -/
-- @node: lowerActualCellRatio_poisson_independent_integrable
lemma lowerActualCellRatio_poisson_independent_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (omega op : Fin j → Bool) (xi : NNReal) :
    Integrable (fun cells : Fin k → FiniteSample Omega =>
      ∏ r : Fin k, lowerActualCellRatio theta k j (cells r).count r omega (cells r).points *
        lowerActualCellRatio theta k j (cells r).count r op (cells r).points)
      (Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r omega xi)) :=
  Integrable.fintype_prod (fun r =>
    lowerActualCellRatio_poisson_pair_integrable theta k j hp r omega op xi)

/-- Independence of the actual complete Poisson cell laws gives the product K(z)^k.
This measure-level identity supplies the grouped experiment in equation (40). -/
-- @node: lowerActualCellRatio_poisson_independent_cross_moment
lemma lowerActualCellRatio_poisson_independent_cross_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (omega op : Fin j → Bool) (xi : NNReal) :
    (∫ cells : Fin k → FiniteSample Omega,
      ∏ r : Fin k, lowerActualCellRatio theta k j (cells r).count r omega (cells r).points *
        lowerActualCellRatio theta k j (cells r).count r op (cells r).points
      ∂Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r omega xi)) =
    lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
      (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k := by
  rw [integral_fintype_prod_eq_prod (fun r : Fin k => fun s : FiniteSample Omega =>
    lowerActualCellRatio theta k j s.count r omega s.points *
      lowerActualCellRatio theta k j s.count r op s.points)]
  simp_rw [lowerActualCellRatio_poisson_cross_moment theta k j hp hk]
  simp

/-- The redundant outcome sign has no effect on the localized Poisson null law. -/
-- @node: lowerLocalizedPoissonNull_outcome_sign_irrel
lemma lowerLocalizedPoissonNull_outcome_sign_irrel (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (omega op : Fin j → Bool) (xi : NNReal) :
    lowerLocalizedPoissonNull theta k j hp r omega xi =
      lowerLocalizedPoissonNull theta k j hp r op xi := by
  rfl

/-- The product likelihood on actual complete Poisson cell samples, at fixed
common outcome signs. -/
-- @node: lowerActualPoissonCellProduct
def lowerActualPoissonCellProduct (theta : ℝ) (k j : ℕ) (omega : Fin j → Bool)
    (cells : Fin k → FiniteSample Omega) : ℝ :=
  ∏ r : Fin k, lowerActualCellRatio theta k j (cells r).count r omega (cells r).points

/-- The common outcome-sign average of the actual grouped Poisson likelihood. -/
-- @node: lowerActualPoissonOutcomeAverage
def lowerActualPoissonOutcomeAverage (theta : ℝ) (k j : ℕ)
    (cells : Fin k → FiniteSample Omega) : ℝ :=
  (Fintype.card (Fin j → Bool) : ℝ)⁻¹ *
    ∑ omega : Fin j → Bool, lowerActualPoissonCellProduct theta k j omega cells

/-- Products of the two grouped likelihoods are integrable under a common,
outcome-sign-independent null law. -/
-- @node: lowerActualPoissonCellProduct_pair_integrable
lemma lowerActualPoissonCellProduct_pair_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (omega op base : Fin j → Bool) (xi : NNReal) :
    Integrable (fun cells => lowerActualPoissonCellProduct theta k j omega cells *
      lowerActualPoissonCellProduct theta k j op cells)
      (Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base xi)) := by
  have h := lowerActualCellRatio_poisson_independent_integrable theta k j hp omega op xi
  simp_rw [lowerLocalizedPoissonNull_outcome_sign_irrel theta k j hp _ omega base xi] at h
  simpa only [lowerActualPoissonCellProduct, Finset.prod_mul_distrib] using h

/-- The cross moment on a common grouped null law is exactly K(z)^k. -/
-- @node: lowerActualPoissonCellProduct_cross_moment
lemma lowerActualPoissonCellProduct_cross_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (omega op base : Fin j → Bool) (xi : NNReal) :
    (∫ cells, lowerActualPoissonCellProduct theta k j omega cells *
      lowerActualPoissonCellProduct theta k j op cells
      ∂Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base xi)) =
    lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
      (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k := by
  have h := lowerActualCellRatio_poisson_independent_cross_moment theta k j hp hk omega op xi
  simp_rw [lowerLocalizedPoissonNull_outcome_sign_irrel theta k j hp _ omega base xi] at h
  simpa only [lowerActualPoissonCellProduct, Finset.prod_mul_distrib] using h

/-- Squaring the common-sign average keeps both outcome sign vectors outside the
cell product, as required by equation (40). -/
-- @node: lowerActualPoissonOutcomeAverage_sq
lemma lowerActualPoissonOutcomeAverage_sq (theta : ℝ) (k j : ℕ)
    (cells : Fin k → FiniteSample Omega) :
    lowerActualPoissonOutcomeAverage theta k j cells ^ 2 =
      (Fintype.card (Fin j → Bool) : ℝ) ^ (-2 : ℤ) *
        ∑ omega : Fin j → Bool, ∑ op : Fin j → Bool,
          lowerActualPoissonCellProduct theta k j omega cells *
            lowerActualPoissonCellProduct theta k j op cells := by
  unfold lowerActualPoissonOutcomeAverage
  rw [mul_pow, pow_two (∑ omega, lowerActualPoissonCellProduct theta k j omega cells),
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  congr 1
  norm_num [zpow_neg, inv_pow]

/-- The grouped shared-sign likelihood is square-integrable under its actual
Poisson null law; finite sign integration needs no extra moment premise. -/
-- @node: lowerActualPoissonOutcomeAverage_sq_integrable
lemma lowerActualPoissonOutcomeAverage_sq_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (base : Fin j → Bool) (xi : NNReal) :
    Integrable (fun cells => lowerActualPoissonOutcomeAverage theta k j cells ^ 2)
      (Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base xi)) := by
  simp_rw [lowerActualPoissonOutcomeAverage_sq]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro omega _
  apply integrable_finsetSum
  intro op _
  exact lowerActualPoissonCellProduct_pair_integrable theta k j hp omega op base xi

/-- The second moment of the actual grouped outcome-sign mixture is precisely
the sign-pair average E K(z)^k in equation (40). -/
-- @node: lowerActualPoissonOutcomeAverage_second_moment
lemma lowerActualPoissonOutcomeAverage_second_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (base : Fin j → Bool) (xi : NNReal) :
    (∫ cells, lowerActualPoissonOutcomeAverage theta k j cells ^ 2
      ∂Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base xi)) =
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
        (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k) := by
  simp_rw [lowerActualPoissonOutcomeAverage_sq]
  rw [integral_const_mul]
  rw [integral_finsetSum _ (fun omega _ => integrable_finsetSum _
    (fun op _ => lowerActualPoissonCellProduct_pair_integrable theta k j hp omega op base xi))]
  simp_rw [integral_finsetSum _ (fun op _ =>
    lowerActualPoissonCellProduct_pair_integrable theta k j hp _ op base xi),
    lowerActualPoissonCellProduct_cross_moment theta k j hp hk]
  rfl

/-- The actual grouped likelihood's excess second moment obeys the quantitative
budget (43), using the proved posterior singleton and outcome-weight bounds. -/
-- @node: lowerActualPoissonOutcomeAverage_excess_le
lemma lowerActualPoissonOutcomeAverage_excess_le (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (hj : 0 < j)
    (base : Fin j → Bool) (xi : NNReal) (hx : (xi : ℝ) ≤ 1)
    (hr : (xi : ℝ) * lowerGamma theta j ^ 2 ≤ 1)
    (hd : 2 * ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * lowerGamma theta j ^ 4) ≤ 1 / 2)
    (ha : ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
        (xi : ℝ) ^ 2 * lowerTau theta k ^ 2 * lowerGamma theta j ^ 2) ^ 2 ≤ 1 / 2) :
    (∫ cells, lowerActualPoissonOutcomeAverage theta k j cells ^ 2
      ∂Measure.pi (fun r => lowerLocalizedPoissonNull theta k j hp r base xi)) - 1 ≤
      8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
          ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
          (xi : ℝ) ^ 2 * lowerTau theta k ^ 2 * lowerGamma theta j ^ 2) ^ 2 +
        ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * lowerGamma theta j ^ 4)) := by
  rw [lowerActualPoissonOutcomeAverage_second_moment theta k j hp hk base xi]
  exact lowerPoissonOverlap_actual_weights_excess_le (lowerTau theta k)
    (lowerTau_mem_Ioc theta k j hp hk) xi hx (lowerGamma theta j) k j hj hr hd ha

end CausalSmith.Stat.DensityEffectRoughNull
