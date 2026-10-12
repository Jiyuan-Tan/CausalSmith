module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingPosterior
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ResponseMarks
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge

/-!
# The full numerical sign laws, product reference, and donor-image energies

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Mix the full unseeded record law over a prior on schedules. -/
def mixtureRecordLaw {V Ξ : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ξ]
    (q r : ℝ) (π : Measure Ξ) (s : Ξ → Schedule V) : Measure (Record V) :=
  π.bind (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ)))
/-- The sign law is generated from the pre-experiment balanced schedules and the specified design. -/
def signLaw (n m : ℕ) (hfit : 2*m ≤ n) (D : Design (Fin n)) (σ : Bool) (δ : ℝ) :
    Measure (Record (Fin n)) :=
  (balancedParamLaw m).bind (fun ξ =>
    (D (balancedSchedule n m hfit σ δ ξ)).map (recordOf (balancedSchedule n m hfit σ δ ξ)))
-- @realizes Psign(full original-record mixture law, excluding the seed)
/-- Embed recipient responses while keeping zero donor and padding responses. -/
def referenceRecordOf (n m : ℕ) (hfit : 2*m ≤ n)
    (ω : Acq (Fin n) × (Assign (Fin n) × (Fin m → ℝ))) : Record (Fin n) :=
  (ω.1, ω.2.1, fun i => ∑ c : Fin m, if i = recipientOf n m hfit c then ω.2.2 c else 0)
/-- The reference retains the planted graph marginal and independent assignments and responses. -/
def referenceLaw (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ) : Measure (Record (Fin n)) :=
  ((plantedGraphLaw n m hfit q r).prod ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n)).prod
    (Measure.pi (fun _ : Fin m => volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y)))))).map
    (referenceRecordOf n m hfit)
-- @realizes Q(actual planted H marginal, independent uniform assignment, iid recipient g responses, zero elsewhere)
/-- The complete likelihood polynomial averages all matching products against the full-graph posterior. -/
def likelihoodPoly (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ) (σ : Bool)
    (o : Record (Fin n)) : ℝ :=
  ∑ M : Matching m, matchingPosterior n m hfit q r o.1 M *
    ∏ e ∈ M.edges, (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * responseMark δ (o.2.2 (recipientOf n m hfit e.2)) *
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (o.2.1 (donorOf n m hfit e.1)))
-- @realizes Lambda(posterior mean of product (1+σ hδ(Y_i) X_j))
/-- The collective donor image of a recipient subset. -/
def donorImage {m : ℕ} (M : Matching m) (S : Finset (Fin m)) : Finset (Fin m) :=
  (M.edges.filter (fun e => e.2 ∈ S)).image Prod.fst
/-- Every selected recipient is matched, with collective donor image exactly J. -/
def ImageEvent {m : ℕ} (M : Matching m) (S J : Finset (Fin m)) : Prop :=
  (∀ i ∈ S, ∃ j, M.1 i = some j) ∧ donorImage M S = J
/-- The posterior donor-image probability. -/
def imageProb (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ) (H : Acq (Fin n))
    (S J : Finset (Fin m)) : ℝ := -- @realizes S(recipient subset); @realizes J(donor-image subset)
  ∑ M : Matching m, if ImageEvent M S J then matchingPosterior n m hfit q r H M else 0
-- @realizes pimage(posterior probability of matching all recipients S with collective image J)
/-- Planted-marginal squared posterior image energy at order k. -/
def orderEnergy (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ) (k : ℕ) : ℝ :=
  ∫ H, ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset (Fin m) => S.card = k),
    ∑ J ∈ Finset.univ.powerset.filter (fun J : Finset (Fin m) => J.card = k),
      imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r
-- @realizes Aorder(expected sum of p_H(S,J)^2 under actual planted H marginal at |S|=|J|=k)

/-- Given [the stated assumptions](hyp:hfit,hqr), [The donor-image posterior is a probability of the specified finite event.](goal) -/
lemma imageProb_mem_Icc (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ) (hqr : ChannelDomain q r)
    (H : Acq (Fin n)) (S J : Finset (Fin m)) :
    imageProb n m hfit q r H S J ∈ Set.Icc 0 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro M _
    split_ifs
    · exact matchingPosterior_nonneg n m hfit q r hqr H M
    · exact le_rfl
  · calc
      imageProb n m hfit q r H S J ≤ ∑ M : Matching m, matchingPosterior n m hfit q r H M := by
        apply Finset.sum_le_sum
        intro M _
        split_ifs
        · exact le_rfl
        · exact matchingPosterior_nonneg n m hfit q r hqr H M
      _ = 1 := matchingPosterior_sum_one n m hfit q r hqr H
-- @realizes pimage(posterior event probability in [0,1])
/-- Given [the stated assumptions](hyp:hfit,hqr), [The full likelihood polynomial is nonnegative, including all declared channel endpoints.](goal) -/
lemma likelihoodPoly_nonneg (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) (σ : Bool) (o : Record (Fin n)) :
    0 ≤ likelihoodPoly n m hfit q r δ σ o := by
  apply Finset.sum_nonneg
  intro M _
  apply mul_nonneg (matchingPosterior_nonneg n m hfit q r hqr o.1 M)
  apply Finset.prod_nonneg
  intro e _
  have hh := responseMark_mem_Icc δ (o.2.2 (recipientOf n m hfit e.2))
  cases σ <;> cases o.2.1 (donorOf n m hfit e.1) <;>
    simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
      Bool.false_eq_true, ↓reduceIte] <;> nlinarith [hh.1, hh.2]
-- @realizes Lambda(nonnegative polynomial on every complete record)
/-- Given [the stated assumptions](hyp:hfit,hqr), [Mixing the acquisition probabilities over the finite matching prior preserves unit mass.](goal) -/
-- @node: plantedGraphLaw_probability
lemma plantedGraphLaw_probability (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) : IsProbabilityMeasure (plantedGraphLaw n m hfit q r) := by
  letI := matchingPrior_probability m
  unfold plantedGraphLaw
  apply isProbabilityMeasure_bind (Measurable.of_discrete.aemeasurable)
  exact Filter.Eventually.of_forall fun M =>
    acquisitionLaw_probability q r hqr (matchingGraphSchedule n m hfit M)

/-- [The normalized balanced real density gives a probability response measure.](goal) -/
-- @node: balancedResponseLaw_probability
lemma balancedResponseLaw_probability (δ : ℝ) :
    IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) := by
  obtain ⟨hm, hn, hi, hmass⟩ := balancedDensity_probability δ
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn), hmass]
  exact ENNReal.ofReal_one

/-- Given [the stated assumptions](hyp:hfit), [Embedding the response vector in the original record is Borel.](goal) -/
-- @node: referenceRecordOf_measurable
@[fun_prop] lemma referenceRecordOf_measurable (n m : ℕ) (hfit : 2*m ≤ n) :
    Measurable (referenceRecordOf n m hfit) := by
  unfold referenceRecordOf
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_sum
  intro c _
  by_cases h : i = recipientOf n m hfit c
  · simp only [h, ↓reduceIte]
    fun_prop
  · simp only [h, ↓reduceIte]
    fun_prop

/-- Given [the stated assumptions](hyp:hfit,hqr), [The actual product reference is a probability law.](goal) -/
-- @node: referenceLaw_probability
lemma referenceLaw_probability (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) : IsProbabilityMeasure (referenceLaw n m hfit q r δ) := by
  letI := plantedGraphLaw_probability n m hfit q r hqr
  letI := balancedResponseLaw_probability δ
  letI : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  unfold referenceLaw CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli
  exact Measure.isProbabilityMeasure_map (referenceRecordOf_measurable n m hfit).aemeasurable
-- @realizes Q(probability law on the full original-record space)
/-- [All independent pre-experiment draws in the balanced prior have unit mass.](goal) -/
-- @node: balancedParamLaw_probability
lemma balancedParamLaw_probability (m : ℕ) : IsProbabilityMeasure (balancedParamLaw m) := by
  letI := matchingPrior_probability m
  letI : IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_integrable_normalized.1
        (Filter.Eventually.of_forall
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg),
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_integrable_normalized.2]
    exact ENNReal.ofReal_one
  letI : IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
      _ (by constructor <;> norm_num)
  unfold balancedParamLaw
  infer_instance

/-- Given [the stated assumptions](hyp:hfit), [With the matching fixed, the full recording map is Borel in all remaining draws.](goal) -/
-- @node: balancedRecord_fixedMatching_measurable
@[fun_prop] lemma balancedRecord_fixedMatching_measurable (n m : ℕ) (hfit : 2*m ≤ n)
    (σ : Bool) (δ : ℝ) (M : Matching m) :
    Measurable (fun p : ((Fin m → ℝ) × (Fin m → Bool)) ×
        (Assign (Fin n) × Acq (Fin n)) =>
      recordOf (balancedSchedule n m hfit σ δ (M, p.1)) p.2) := by
  unfold recordOf
  apply measurable_snd.snd.prodMk
  apply measurable_snd.fst.prodMk
  apply measurable_pi_lambda
  intro i
  simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome,
    balancedSchedule, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd,
    zero_mul, add_zero]
  apply Measurable.add
  · apply Finset.measurable_sum
    intro c _
    by_cases hic : i = recipientOf n m hfit c
    · simp only [hic, ↓reduceIte]
      by_cases hc : M.1 c = none
      · simp only [hc, ↓reduceIte]
        fun_prop
      · simp only [hc, ↓reduceIte]
        fun_prop
    · simp only [hic, ↓reduceIte]
      fun_prop
  · fun_prop

/-- Given [the stated assumptions](hyp:hf), [A jointly Borel map gives a Borel family of pushforward laws.](goal) -/
-- @node: sign_measurable_map_parameter
lemma sign_measurable_map_parameter {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure β) [SFinite μ]
    (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => μ.map (fun b => f (a, b))) := by
  have h := (Measure.measurable_map f hf).comp
    (Measurable.map_prodMk_left (ν := μ))
  simpa only [Measure.map_map hf measurable_prodMk_left, Function.comp_def] using h

/-- Given [the stated assumptions](hyp:hfit,hqr), [The balanced full-record kernel is Borel, by conditioning on its finite matching.](goal) -/
-- @node: balancedRecord_kernel_measurable
lemma balancedRecord_kernel_measurable (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (σ : Bool) :
    Measurable (fun ξ : PriorParam m =>
      (noisyDesign q r (balancedSchedule n m hfit σ δ ξ)).map
        (recordOf (balancedSchedule n m hfit σ δ ξ))) := by
  apply measurable_from_prod_countable_right
  intro M
  letI := noisyDesign_probability q r hqr (matchingGraphSchedule n m hfit M)
  have h := sign_measurable_map_parameter
    (noisyDesign q r (matchingGraphSchedule n m hfit M)) _
    (balancedRecord_fixedMatching_measurable n m hfit σ δ M)
  exact h

/-- Given [the stated assumptions](hyp:hfit,hqr,ha,hH,hi), [The balanced sign experiments are probability laws under the admitted design atoms.](goal) -/
-- @node: signLaw_probability
lemma signLaw_probability (n m : ℕ) (hfit : 2*m ≤ n) (D : Design (Fin n)) (q r δ : ℝ)
    (hqr : ChannelDomain q r) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) (σ : Bool) : IsProbabilityMeasure (signLaw n m hfit D σ δ) := by
  rw [design_eq_noisyDesign D q r ha hH hi]
  letI := balancedParamLaw_probability m
  unfold signLaw
  apply isProbabilityMeasure_bind
    (balancedRecord_kernel_measurable n m hfit q r δ hqr σ).aemeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  letI := noisyDesign_probability q r hqr (balancedSchedule n m hfit σ δ ξ)
  exact Measure.isProbabilityMeasure_map (recordOf_measurable _).aemeasurable
-- @realizes Psign(probability law generated from the fixed pre-experiment schedule prior)

end CausalSmith.Experimentation.NoisygraphTtePrecision
