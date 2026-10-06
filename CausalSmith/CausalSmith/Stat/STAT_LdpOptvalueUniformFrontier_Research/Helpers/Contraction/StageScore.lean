module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageDensity
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Density
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Conditional stage scores

The repaired finite row densities give positive affine stage mixtures. Their
coordinate scores have the sharp privacy bound and zero mean under the
parameter-specific conditional message law.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the function theta](hyp:theta) and [the amplitude](hyp:a). [The affine paired-input probability weights](goal). -/
-- @node: stageInputWeight
def stageInputWeight {d : ℕ} (theta : Fin d → ℝ) (a : PairedSymbol d) : ℝ :=
  (1 + signVal a.2 * theta a.1) / (2*d)

/-- Fix [the function theta](hyp:theta) and [the function f](hyp:f). [The parameter-specific stage density relative to the uniform row average](goal). -/
-- @node: stageMixtureDensity
def stageMixtureDensity {d : ℕ} (theta : Fin d → ℝ) (f : PairedSymbol d → ℝ) : ℝ :=
  ∑ a, stageInputWeight theta a * f a

/-- Fix [the function f](hyp:f) and [the coordinate index](hyp:j). [The coordinate slope of the affine conditional density](goal). -/
-- @node: stageCoordinateSlope
def stageCoordinateSlope {d : ℕ} (f : PairedSymbol d → ℝ) (j : Fin d) : ℝ :=
  (f (j, true) - f (j, false)) / (2*d)

/-- Assume [the stated htheta condition](hyp:htheta). [Cube parameters give nonnegative conditional input weights. [](](goal). -/
-- @node: stageInputWeight_nonneg
lemma stageInputWeight_nonneg {d : ℕ} (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (a : PairedSymbol d) :
    0 ≤ stageInputWeight theta a := by
  have ha := htheta a.1
  unfold stageInputWeight
  apply div_nonneg _ (by positivity)
  cases a.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_one_mul] <;> linarith [ha.1, ha.2]

/-- Assume [positive dimension](hyp:hd). [The affine input weights sum to one, even outside the cube. [](](goal). -/
-- @node: stageInputWeight_sum
lemma stageInputWeight_sum {d : ℕ} (hd : 0 < d) (theta : Fin d → ℝ) :
    ∑ a : PairedSymbol d, stageInputWeight theta a = 1 := by
  have hd0 : (2*d : ℝ) ≠ 0 := by positivity
  rw [Fintype.sum_prod_type]
  have hpair (j : Fin d) : ∑ s : Bool, stageInputWeight theta (j, s) = (d : ℝ)⁻¹ := by
    simp only [Fintype.sum_bool, stageInputWeight, signVal, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
    field_simp
    <;> ring
  simp only [hpair, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

/-- [Splitting the two signs exposes the affine coordinate coefficients. [](](goal). -/
-- @node: stageMixtureDensity_affine
lemma stageMixtureDensity_affine {d : ℕ} (theta : Fin d → ℝ)
    (f : PairedSymbol d → ℝ) :
    stageMixtureDensity theta f = (∑ a, f a) / (2*d) +
      ∑ j, theta j * stageCoordinateSlope f j := by
  unfold stageMixtureDensity stageInputWeight stageCoordinateSlope
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool, signVal, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Assume [positive dimension](hyp:hd) and [the stated hsum condition](hyp:hsum). [Exact row normalization makes the zero-contrast conditional density one](goal). -/
-- @node: stageMixtureDensity_normalized
lemma stageMixtureDensity_normalized {d : ℕ} (hd : 0 < d)
    (theta : Fin d → ℝ) (f : PairedSymbol d → ℝ)
    (hsum : ∑ a, f a = (2*d : ℝ)) :
    stageMixtureDensity theta f = 1 + ∑ j, theta j * stageCoordinateSlope f j := by
  rw [stageMixtureDensity_affine, hsum, div_self (by positivity)]

/-- [Replacing one parameter coordinate changes a stage density by its exact slope. [](](goal). -/
-- @node: stageMixtureDensity_update
lemma stageMixtureDensity_update {d : ℕ} (theta : Fin d → ℝ)
    (f : PairedSymbol d → ℝ) (j : Fin d) (x : ℝ) :
    stageMixtureDensity (Function.update theta j x) f =
      stageMixtureDensity theta f + (x - theta j) * stageCoordinateSlope f j := by
  classical
  rw [stageMixtureDensity_affine, stageMixtureDensity_affine]
  have hterm (a : Fin d) : Function.update theta j x a * stageCoordinateSlope f a =
      theta a * stageCoordinateSlope f a +
        (if a = j then (x - theta j) * stageCoordinateSlope f j else 0) := by
    by_cases ha : a = j
    · subst a; simp; ring
    · simp [Function.update_of_ne ha, ha]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- Assume [the stated hw condition](hyp:hw), [the stated hsum condition](hyp:hsum), [the stated hf condition](hyp:hf), [a privacy factor at least one](hyp:hc), and [the stated hpriv condition](hyp:hpriv). [A convex mixture of private rows inherits their minimum, and every row difference is bounded by the privacy excess times that same minimum](goal). -/
-- @node: private_row_score_bound
lemma private_row_score_bound {I : Type*} [Fintype I] [Nonempty I]
    (w f : I → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (hf : ∀ a, 0 < f a) (c : ℝ) (hc : 1 ≤ c)
    (hpriv : ∀ a b, f a ≤ c * f b) (a b : I) :
    0 < (∑ x, w x * f x) ∧
      |f a - f b| ≤ (c - 1) * (∑ x, w x * f x) := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hmin : f x ≤ ∑ y, w y * f y := by
    calc
      f x = ∑ y, w y * f x := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ y, w y * f y := Finset.sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_left (hx y hy) (hw y)
  refine ⟨lt_of_lt_of_le (hf x) hmin, ?_⟩
  have ha := hpriv a x
  have hb := hpriv b x
  have hxa := hx a (Finset.mem_univ a)
  have hxb := hx b (Finset.mem_univ b)
  have hdiff : |f a - f b| ≤ (c - 1) * f x := by
    rw [abs_le]
    constructor <;> nlinarith
  exact hdiff.trans (mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hc))

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [the stated hf condition](hyp:hf), [a nonnegative privacy budget](hyp:heps), and [the stated hpriv condition](hyp:hpriv). [The sharp coordinate score bound follows from privacy and convex weighting, without losing a factor from the lower bound on each input weight](goal). -/
-- @node: stageCoordinateScore_bound
lemma stageCoordinateScore_bound {d : ℕ} (hd : 0 < d) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (f : PairedSymbol d → ℝ)
    (hf : ∀ a, 0 < f a) (eps : ℝ) (heps : 0 ≤ eps)
    (hpriv : ∀ a b, f a ≤ Real.exp eps * f b) (j : Fin d) :
    0 < stageMixtureDensity theta f ∧
      |stageCoordinateSlope f j / stageMixtureDensity theta f| ≤ derivativeScale d eps := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hpos, hdiff⟩ := private_row_score_bound (stageInputWeight theta) f
    (stageInputWeight_nonneg theta htheta) (stageInputWeight_sum hd theta)
    hf (Real.exp eps) (Real.one_le_exp_iff.mpr heps) hpriv (j, true) (j, false)
  change 0 < stageMixtureDensity theta f at hpos
  refine ⟨hpos, ?_⟩
  have hden : (0 : ℝ) < 2*d := by positivity
  change |((f (j, true) - f (j, false)) / (2*d)) / stageMixtureDensity theta f| ≤
    (Real.exp eps - 1) / (2*d)
  rw [abs_div, abs_div, abs_of_pos hden, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  apply (div_le_iff₀ hden).mpr
  calc
    |f (j, true) - f (j, false)| ≤
        (Real.exp eps - 1) * stageMixtureDensity theta f := hdiff
    _ = ((Real.exp eps - 1) / (2*d) * stageMixtureDensity theta f) * (2*d) := by
      field_simp

/-- Assume [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the stated probability-measure property](hyp:hprob). [Every normalized probability-row density has real integral one](goal). -/
-- @node: integral_probability_row_density
lemma integral_probability_row_density {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) (f : Z → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hprob : IsProbabilityMeasure (mu.withDensity (fun z => ENNReal.ofReal (f z)))) :
    (∫ z, f z ∂mu) = 1 := by
  letI := hprob
  have hmass : (∫⁻ z, ENNReal.ofReal (f z) ∂mu) = 1 := by
    have h := measure_univ (μ := mu.withDensity (fun z => ENNReal.ofReal (f z)))
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    hf.aestronglyMeasurable, hmass]
  simp

/-- Assume [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hb condition](hyp:hb), [the stated hbound condition](hyp:hbound), [the stated probability-measure property](hyp:hprob), and [the stated hpos condition](hyp:hpos). [Under the parameter-specific conditional law, dividing the zero-integral coordinate slope by its positive density preserves zero mean](goal). -/
-- @node: stageCoordinateScore_integral_zero
lemma stageCoordinateScore_integral_zero {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (mu : Measure Z) [IsFiniteMeasure mu] (f : PairedSymbol d → Z → ℝ)
    (hf : ∀ a, Measurable (f a)) (hf0 : ∀ a z, 0 ≤ f a z)
    (hb : ℝ) (hbound : ∀ a z, |f a z| ≤ hb)
    (hprob : ∀ a, IsProbabilityMeasure (mu.withDensity (fun z => ENNReal.ofReal (f a z))))
    (theta : Fin d → ℝ) (hpos : ∀ z, 0 < stageMixtureDensity theta (fun a => f a z))
    (j : Fin d) :
    (∫ z, stageCoordinateSlope (fun a => f a z) j /
      stageMixtureDensity theta (fun a => f a z)
      ∂mu.withDensity (fun z => ENNReal.ofReal
        (stageMixtureDensity theta (fun a => f a z)))) = 0 := by
  have hM : Measurable (fun z => stageMixtureDensity theta (fun a => f a z)) := by
    unfold stageMixtureDensity
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hM.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hpos _)), smul_eq_mul]
  have hcancel : (fun z => stageMixtureDensity theta (fun a => f a z) *
      (stageCoordinateSlope (fun a => f a z) j /
        stageMixtureDensity theta (fun a => f a z))) =
      (fun z => (f (j, true) z - f (j, false) z) / (2*d)) := by
    funext z
    rw [mul_div_cancel₀ _ (ne_of_gt (hpos z))]
    rfl
  rw [hcancel, integral_div]
  have hi (a : PairedSymbol d) : Integrable (f a) mu := by
    apply Integrable.of_bound (hf a).aestronglyMeasurable hb
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs] using hbound a z
  rw [integral_sub (hi _) (hi _),
    integral_probability_row_density mu _ (hf _) (hf0 _) (hprob _),
    integral_probability_row_density mu _ (hf _) (hf0 _) (hprob _)]
  simp

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [The RN gate supplies actual jointly measurable protocol-row versions whose conditional coordinate scores satisfy both martingale prerequisites, at every history and seed (including reference-null histories)](goal). -/
-- @node: stage_score_certificate_of_gate
lemma stage_score_certificate_of_gate (hRN : MeasurableKernelRadonNikodym)
    {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      Measurable f ∧
      (∀ a r eta, (stageReferenceKernel Q i (r, eta)).withDensity
        (fun z => ENNReal.ofReal (f (((a, r), eta), z))) =
          averagedKernel Q i ((a, r), eta)) ∧
      (∀ theta, ∀ r eta z,
        stageMixtureDensity theta (fun a => f (((a, r), eta), z)) =
          1 + ∑ j, theta j * stageCoordinateSlope (fun a => f (((a, r), eta), z)) j) ∧
      (∀ theta ∈ parameterCube d, ∀ r eta z j,
        0 < stageMixtureDensity theta (fun a => f (((a, r), eta), z)) ∧
        |stageCoordinateSlope (fun a => f (((a, r), eta), z)) j /
          stageMixtureDensity theta (fun a => f (((a, r), eta), z))| ≤ derivativeScale d eps) ∧
      ∀ theta ∈ parameterCube d, ∀ r eta j,
        (∫ z, stageCoordinateSlope (fun a => f (((a, r), eta), z)) j /
          stageMixtureDensity theta (fun a => f (((a, r), eta), z))
          ∂(stageReferenceKernel Q i (r, eta)).withDensity (fun z => ENNReal.ofReal
            (stageMixtureDensity theta (fun a => f (((a, r), eta), z))))) = 0 := by
  obtain ⟨f, hf, hf0, hsum, hpriv, hbound, hrep⟩ :=
    stage_density_repaired_of_gate hRN Q i hd eps heps hQ
  have hscore (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
      (r : Q.Seed) (eta : ProtocolHistory Q i) (z : Q.Message i) (j : Fin d) :=
    stageCoordinateScore_bound hd theta htheta (fun a => f (((a, r), eta), z))
      (fun a => lt_of_lt_of_le (Real.exp_pos (-eps)) (hbound _).1)
      eps heps (fun a b => hpriv a b r eta z) j
  refine ⟨f, hf, hrep, ?_, ?_, ?_⟩
  · intro theta r eta z
    exact stageMixtureDensity_normalized hd theta _ (hsum r eta z)
  · exact hscore
  · intro theta htheta r eta j
    letI := stageReferenceKernel_markov Q i hd
    letI := averagedKernel_markov Q i
    apply stageCoordinateScore_integral_zero (stageReferenceKernel Q i (r, eta))
      (fun a z => f (((a, r), eta), z))
      (fun a => hf.comp (by fun_prop)) (fun a z => hf0 _) (Real.exp eps)
    · intro a z
      rw [abs_of_nonneg (hf0 _)]
      exact (hbound _).2
    · intro a
      rw [hrep]
      infer_instance
    · intro z
      exact (hscore theta htheta r eta z j).1


end CausalSmith.Stat.LdpOptvalueUniformFrontier
