module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Basic
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.CitedGates
public import Causalean.Mathlib.Probability.Kernel.BernoulliMark
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


-- @env: S4
variable (β b h σ : ℝ) (m : ℕ) -- @realizes m(cancellation degree, at least two)
/-- Legendre block normalizer. Given [the displayed inputs and assumptions](hyp:m), [this definition specifies the stated object](goal). -/
def blockNorm (m : ℕ) : ℝ := (2 * (m : ℝ) + 1) ^ 2 - (m : ℝ) ^ 2 -- @realizes Blocknorm(block normalizer)
/-- Tapered high-degree Legendre block. Given [the displayed inputs and assumptions](hyp:m,t), [this definition specifies the stated object](goal). -/
def block (m : ℕ) (t : ℝ) : ℝ := -- @realizes Block(tapered Legendre block) @realizes t(real block argument)
  (1 - t) * (blockNorm m)⁻¹ *
    ∑ j ∈ Finset.Icc m (2 * m), (2 * (j : ℝ) + 1) * (-1 : ℝ) ^ j * legendreP j (2 * t - 1)
/-- Full-interval continuation of the lower perturbation. Given [the displayed inputs and assumptions](hyp:b,m,x), [this definition specifies the stated object](goal). -/
-- @node: def:legal-extension
def legalExtension (b : ℝ) (m : ℕ) (x : ℝ) : ℝ := -- @realizes Extension(full-interval continuation)
  if x < 0 then 1 else if x ≤ b then block m (x / b) else 0
/-- The fixed numerical perturbation size. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def kappa : ℝ := 1/100 -- @realizes kappa(fixed numerical scalar)
/-- The signs index the plus and minus law. Given [the displayed inputs and assumptions](hyp:s), [this definition specifies the stated object](goal). -/
def witnessSign (s : Bool) : ℝ := if s then 1 else -1
/-- Uniform latent score law. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def uniformScore : Measure ℝ := ENNReal.ofReal (1/2) • volume.restrict (Icc (-1) 1)
/-- The uniform score density. Given [the displayed inputs and assumptions](hyp:x), [this definition specifies the stated object](goal). -/
def uniformDensity (x : ℝ) : ℝ := if x ∈ Icc (-1 : ℝ) 1 then 1/2 else 0
/-- Independent conditional Bernoulli potentials and independent Gaussian perturbation. Given [the displayed inputs and assumptions](hyp:p), [this definition specifies the stated object](goal). -/
def witnessMeasure (p : ℝ → ℝ) : Measure Latent :=
  let M := (uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
    ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  (M.prod (gaussianReal 0 1)).map (fun z => (z.1.1.1, z.1.1.2, z.1.2, z.2))
/-- Conditional means of the constructed witness law. Given [the displayed inputs and assumptions](hyp:p,d,x), [this definition specifies the stated object](goal). -/
def witnessMu (p : ℝ → ℝ) (d : Bool) (x : ℝ) : ℝ := if d then p x else 1/2
/-- Uniform density facts, independent of the mean perturbation. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma uniformDensity_properties :
    ContinuousOn uniformDensity (Icc (-1) 1) ∧
    (∀ x ∉ Icc (-1 : ℝ) 1, uniformDensity x = 0) ∧
    (∀ x, 0 ≤ uniformDensity x) ∧ (∫ x in (-1 : ℝ)..1, uniformDensity x) = 1 := by
  have heq : EqOn uniformDensity (fun _ => (1/2 : ℝ)) (Icc (-1) 1) := by
    intro x hx
    simp [uniformDensity, hx]
  refine ⟨continuousOn_const.congr heq, ?_, ?_, ?_⟩
  · intro x hx
    simp [uniformDensity, hx]
  · intro x
    unfold uniformDensity
    split_ifs <;> norm_num
  · rw [intervalIntegral.integral_congr (by simpa using heq)]
    norm_num
/-- The uniform score construction has unit total mass. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma uniformScore_probability : IsProbabilityMeasure uniformScore := by
  constructor
  norm_num [uniformScore, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The uniform score construction is supported on the latent interval. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma uniformScore_support : ∀ᵐ x ∂uniformScore, x ∈ Icc (-1 : ℝ) 1 := by
  exact (Measure.smul_absolutelyContinuous (μ := volume.restrict (Icc (-1 : ℝ) 1))
    (c := ENNReal.ofReal (1/2))).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- A normalized Bernoulli mark preserves the base marginal, including endpoint probabilities. Given [the displayed inputs and assumptions](hyp:α,μ,p,hm,hb), [the stated mathematical conclusion holds](goal). -/
lemma bernoulli_compProd_fst {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (p : α → ℝ) (hm : Measurable p)
    (hb : ∀ᵐ x ∂μ, 0 ≤ p x ∧ p x ≤ 1) :
    (μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p).map Prod.fst = μ := by
  have hmass : ∀ᵐ x ∂μ,
      Causalean.Mathlib.Probability.bernoulliMarkKernel p x univ = 1 := by
    filter_upwards [hb] with x hx
    rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply p hm x]
    exact @IsProbabilityMeasure.measure_univ Bool _ _
      (Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hx.1 hx.2)
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    show Prod.fst ⁻¹' s = s ×ˢ univ by ext x; simp,
    Measure.compProd_apply_prod hs MeasurableSet.univ]
  calc
    _ = ∫⁻ _x in s, (1 : ENNReal) ∂μ := by
      apply setLIntegral_congr_fun_ae hs
      filter_upwards [hmass] with x hx _ using hx
    _ = μ s := setLIntegral_one s

/-- Both conditional marks and the independent Gaussian leave the score marginal unchanged. Given [the displayed inputs and assumptions](hyp:p,hm,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_score (p : ℝ → ℝ) (hm : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessMeasure p).map score = uniformScore := by
  letI := uniformScore_probability
  let K₀ := Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2)
  let M₀ := uniformScore ⊗ₘ K₀
  let K₁ := Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  have h₀ : M₀.map Prod.fst = uniformScore :=
    bernoulli_compProd_fst uniformScore _ measurable_const (by
      filter_upwards [] with x; norm_num)
  have hbound : ∀ᵐ z ∂M₀, 0 ≤ p z.1 ∧ p z.1 ≤ 1 := by
    change ∀ᵐ z ∂uniformScore ⊗ₘ K₀, 0 ≤ p z.1 ∧ p z.1 ≤ 1
    apply Measure.ae_compProd_of_ae_fst (p := fun x => 0 ≤ p x ∧ p x ≤ 1) K₀
      ((measurableSet_le measurable_const hm).inter
        (measurableSet_le hm measurable_const))
    filter_upwards [uniformScore_support] with x hx using hb x hx
  have h₁ : (M₀ ⊗ₘ K₁).map Prod.fst = M₀ :=
    bernoulli_compProd_fst M₀ _ (hm.comp measurable_fst) hbound
  unfold witnessMeasure
  rw [Measure.map_map (show Measurable score from measurable_fst) (by fun_prop)]
  change ((M₀ ⊗ₘ K₁).prod (gaussianReal 0 1)).map
    ((Prod.fst ∘ Prod.fst) ∘ Prod.fst) = uniformScore
  rw [← Measure.map_map (by fun_prop) measurable_fst,
    Measure.map_fst_prod]
  simp only [measure_univ, one_smul]
  rw [← Measure.map_map measurable_fst measurable_fst, h₁, h₀]

/-- The conditional Bernoulli construction is a probability law. Given [the displayed inputs and assumptions](hyp:p,hm,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_probability (p : ℝ → ℝ) (hm : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure (witnessMeasure p) := by
  letI := uniformScore_probability
  have hmap : IsProbabilityMeasure ((witnessMeasure p).map score) := by
    rw [witnessMeasure_score p hm hb]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map score
/-- Constructed scores stay in the latent interval. Given [the displayed inputs and assumptions](hyp:p,hm,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_support (p : ℝ → ℝ) (hm : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ᵐ ω ∂witnessMeasure p, score ω ∈ Icc (-1) 1 := by
  have hs : ∀ᵐ x ∂(witnessMeasure p).map score, x ∈ Icc (-1 : ℝ) 1 := by
    rw [witnessMeasure_score p hm hb]
    exact uniformScore_support
  exact (ae_map_iff (show Measurable score from measurable_fst).aemeasurable
    measurableSet_Icc).mp hs
/-- The score marginal has the fixed uniform density. Given [the displayed inputs and assumptions](hyp:p,hm,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_density (p : ℝ → ℝ) (hm : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessMeasure p).map score = volume.withDensity (fun x => ENNReal.ofReal (uniformDensity x)) := by
  rw [witnessMeasure_score p hm hb]
  have heq : (fun x => ENNReal.ofReal (uniformDensity x)) =
      (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1/2)) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [uniformDensity, hx]
  rw [heq, withDensity_indicator measurableSet_Icc, withDensity_const]
  rfl
/-- Integrating the successful Boolean mark over a base event recovers its probability integral. Given [the displayed inputs and assumptions](hyp:α,μ,p,hm,hp,B,hB), [the stated mathematical conclusion holds](goal). -/
lemma bernoulli_compProd_setIntegral_bit {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (p : α → ℝ) (hm : Measurable p)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (B : Set α) (hB : MeasurableSet B) :
    (∫ z in Prod.fst ⁻¹' B, bit z.2
      ∂μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p) = ∫ x in B, p x ∂μ := by
  have hleft : (∫ z in Prod.fst ⁻¹' B, bit z.2
      ∂μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p) =
      (μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p).real (B ×ˢ {true}) := by
    rw [← integral_indicator (hB.preimage measurable_fst)]
    have heq : (Prod.fst ⁻¹' B).indicator (fun z : α × Bool => bit z.2) =
        (B ×ˢ {true}).indicator (fun _ => (1 : ℝ)) := by
      funext z
      rcases z with ⟨x, y⟩
      by_cases hx : x ∈ B <;> cases y <;> simp [bit, hx]
    rw [heq]
    simpa only [Pi.one_def] using integral_indicator_one
      (μ := μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p)
      (hB.prod (measurableSet_singleton true))
  rw [hleft]
  have hmass : (μ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel p) (B ×ˢ {true}) =
      (μ.withDensity (fun x => ENNReal.ofReal (p x))) B := by
    rw [Measure.compProd_apply_prod hB (measurableSet_singleton true)]
    simp_rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_true p hm]
    exact (withDensity_apply _ hB).symm
  change ENNReal.toReal _ = _
  rw [hmass]
  calc
    _ = ∫ _x in B, (1 : ℝ) ∂μ.withDensity (fun x => ENNReal.ofReal (p x)) := by simp [measureReal_def]
    _ = ∫ x in B, (ENNReal.ofReal (p x)).toReal • (1 : ℝ) ∂μ :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul (by fun_prop)
        (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top) _ hB
    _ = ∫ x in B, p x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with x hx
      simp [ENNReal.toReal_ofReal hx]

/-- Forgetting the independent Gaussian coordinate recovers the two-mark schedule law. Given [the displayed inputs and assumptions](hyp:p), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_schedule (p : ℝ → ℝ) :
    (witnessMeasure p).map (fun ω => ((score ω, ω.2.1), ω.2.2.1)) =
      (uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
        ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1) := by
  let M := (uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
    ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  unfold witnessMeasure
  rw [Measure.map_map (by unfold score; fun_prop) (by fun_prop)]
  change (M.prod (gaussianReal 0 1)).map Prod.fst = M
  rw [Measure.map_fst_prod]
  simp

/-- The specified Bernoulli probabilities are conditional potential means. Given [the displayed inputs and assumptions](hyp:p,hm,hc,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessMeasure_version (p : ℝ → ℝ) (hm : Measurable p)
    (hc : ContinuousOn p (Icc (-1) 1))
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ d B, MeasurableSet B →
      (∫ ω in {ω | score ω ∈ B}, pot d ω ∂witnessMeasure p) =
        ∫ x in B ∩ Icc (-1) 1, witnessMu p d x * uniformDensity x := by
  letI := uniformScore_probability
  let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2)
  let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  have h₀ : M₀.map Prod.fst = uniformScore :=
    bernoulli_compProd_fst uniformScore _ measurable_const (by
      filter_upwards [] with x; norm_num)
  have hp : ∀ᵐ z ∂M₀, 0 ≤ p z.1 ∧ p z.1 ≤ 1 := by
    apply Measure.ae_compProd_of_ae_fst
      (Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
      ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const))
    filter_upwards [uniformScore_support] with x hx using hb x hx
  have h₁ : M₁.map Prod.fst = M₀ :=
    bernoulli_compProd_fst M₀ _ (hm.comp measurable_fst) hp
  intro d B hB
  have hschedule := witnessMeasure_schedule p
  have hpot : Measurable (fun z : (ℝ × Bool) × Bool => bit (if d then z.2 else z.1.2)) := by
    cases d <;> exact (measurable_of_countable bit).comp (by fun_prop)
  have hreduce : (∫ ω in {ω | score ω ∈ B}, pot d ω ∂witnessMeasure p) =
      ∫ z in {z : (ℝ × Bool) × Bool | z.1.1 ∈ B},
        bit (if d then z.2 else z.1.2) ∂M₁ := by
    have heq := setIntegral_map
      (μ := witnessMeasure p) (g := fun ω => ((score ω, ω.2.1), ω.2.2.1))
      (hB.preimage (measurable_fst.comp measurable_fst)) hpot.aestronglyMeasurable
      (show AEMeasurable (fun ω : Latent => ((score ω, ω.2.1), ω.2.2.1)) (witnessMeasure p) from
        (by unfold score; fun_prop))
    rw [hschedule] at heq
    exact heq.symm
  have hmean : (∫ ω in {ω | score ω ∈ B}, pot d ω ∂witnessMeasure p) =
      ∫ x in B, witnessMu p d x ∂uniformScore := by
    rw [hreduce]
    cases d
    · change (∫ z in Prod.fst ⁻¹' (Prod.fst ⁻¹' B), bit z.1.2 ∂M₁) =
        ∫ x in B, (1/2 : ℝ) ∂uniformScore
      have heq := setIntegral_map (μ := M₁) (g := Prod.fst)
        (f := fun z : ℝ × Bool => bit z.2) (hB.preimage measurable_fst)
        ((measurable_of_countable bit).comp measurable_snd).aestronglyMeasurable
        measurable_fst.aemeasurable
      rw [h₁] at heq
      exact heq.symm.trans (bernoulli_compProd_setIntegral_bit uniformScore
        (fun _ => 1/2) measurable_const (by filter_upwards [] with x; norm_num) B hB)
    · change (∫ z in Prod.fst ⁻¹' (Prod.fst ⁻¹' B), bit z.2 ∂M₁) = ∫ x in B, p x ∂uniformScore
      have heq := setIntegral_map (μ := M₀) (g := Prod.fst) (f := p)
        hB hm.aestronglyMeasurable measurable_fst.aemeasurable
      rw [h₀] at heq
      exact (bernoulli_compProd_setIntegral_bit M₀ (fun z => p z.1) (hm.comp measurable_fst)
        (hp.mono fun _ hx => hx.1) _ (hB.preimage measurable_fst)).trans heq.symm
  rw [hmean]
  unfold uniformScore
  rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hB]
  have heq : (fun x => witnessMu p d x * uniformDensity x) =ᵐ[volume.restrict (B ∩ Icc (-1) 1)]
      fun x => (1/2 : ℝ) • witnessMu p d x := by
    filter_upwards [ae_restrict_mem (hB.inter measurableSet_Icc)] with x hx
    simp [uniformDensity, hx.2, smul_eq_mul, mul_comm]
  rw [integral_congr_ae heq, integral_smul]
  norm_num

/-- Continuous Bernoulli probability yields continuous conditional means. Given [the displayed inputs and assumptions](hyp:p,hc), [the stated mathematical conclusion holds](goal). -/
lemma witnessMu_continuous (p : ℝ → ℝ) (hc : ContinuousOn p (Icc (-1) 1)) :
    ∀ d, ContinuousOn (witnessMu p d) (Icc (-1) 1) := by
  intro d
  cases d
  · exact continuousOn_const
  · exact hc
/-- Package the explicitly constructed measure and its versions, rather than an arbitrary witness. Given [the displayed inputs and assumptions](hyp:p,hm,hc,hb), [this definition specifies the stated object](goal). -/
def bernoulliWitness (p : ℝ → ℝ) (hm : Measurable p)
    (hc : ContinuousOn p (Icc (-1) 1))
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) : LatentLaw where
  P := witnessMeasure p
  prob := witnessMeasure_probability p hm hb
  supp := witnessMeasure_support p hm hb
  f := uniformDensity
  f_cont := uniformDensity_properties.1
  f_zero := uniformDensity_properties.2.1
  f_nonneg := uniformDensity_properties.2.2.1
  f_int := uniformDensity_properties.2.2.2
  density := witnessMeasure_density p hm hb
  mu := witnessMu p
  mu_cont := witnessMu_continuous p hc
  mu_version := witnessMeasure_version p hm hc hb
/-- Cancellation witness success probability. Given [the displayed inputs and assumptions](hyp:β,b,m,s,x), [this definition specifies the stated object](goal). -/
def altProbability (β b : ℝ) (m : ℕ) (s : Bool) (x : ℝ) : ℝ :=
  1/2 + witnessSign s * kappa * (b / (m : ℝ)^2) ^ β * legalExtension b m x
/-- The explicit coefficient formula gives the reversed Legendre left endpoint. Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma legendreP_left_endpoint (j : ℕ) : legendreP j (-1) = (-1 : ℝ)^j := by
  have hzero : (Polynomial.aeval (0 : ℝ) (Polynomial.shiftedLegendre j) : ℝ) = 1 := by
    simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_shiftedLegendre]
  have hs := Polynomial.shiftedLegendre_eval_symm j (1 : ℝ)
  simpa [legendreP, hzero] using hs

/-- The block's positive odd weights sum to its displayed normalization. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma witness_block_weight_sum (m : ℕ) :
    (∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1)) = blockNorm m := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1)) = (n : ℝ)^2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega), hs, hs]
  push_cast
  unfold blockNorm
  ring

/-- Endpoint normalization follows directly from Mathlib's polynomial coefficients. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma witness_block_zero (m : ℕ) : block m 0 = 1 := by
  have hn : 0 < blockNorm m := by
    unfold blockNorm
    nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ)]
  have hs : (∑ j ∈ Finset.Icc m (2*m),
      (2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (-1)) = blockNorm m := by
    calc
      _ = ∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [legendreP_left_endpoint, mul_assoc, ← mul_pow]
        simp
      _ = _ := witness_block_weight_sum m
  simpa [block, hs] using inv_mul_cancel₀ hn.ne'

/-- The continuation is polynomial evaluation at a clamped argument, including both seams. Given [the displayed inputs and assumptions](hyp:b,m,hb,x), [the stated mathematical conclusion holds](goal). -/
lemma witness_legalExtension_clamp (b : ℝ) (m : ℕ) (hb : 0 < b) (x : ℝ) :
    legalExtension b m x = block m (max 0 (min 1 (x/b))) := by
  by_cases hx : x < 0
  · have hxb : x/b < 0 := div_neg_of_neg_of_pos hx hb
    simp [legalExtension, hx, min_eq_right (by linarith : x/b ≤ 1),
      max_eq_left hxb.le, witness_block_zero]
  · by_cases hxb : x ≤ b
    · have h0 : 0 ≤ x/b := div_nonneg (le_of_not_gt hx) hb.le
      have h1 : x/b ≤ 1 := (div_le_one hb).mpr hxb
      simp [legalExtension, hx, hxb, min_eq_right h1, max_eq_right h0]
    · have h1 : 1 ≤ x/b := (le_div_iff₀ hb).mpr (by linarith)
      simp [legalExtension, hx, hxb, min_eq_left h1, block]

/-- Given the [positive continuation width](hyp:hb), matching endpoint values make the full continuation [continuous across both seams](goal). -/
@[fun_prop] lemma witness_legalExtension_continuous (b : ℝ) (m : ℕ) (hb : 0 < b) :
    Continuous (legalExtension b m) := by
  have heq : legalExtension b m = fun x => block m (max 0 (min 1 (x/b))) := by
    funext x
    exact witness_legalExtension_clamp b m hb x
  rw [heq]
  unfold block legendreP
  fun_prop

/-- Given the [positive continuation width](hyp:hb), affine Bernoulli perturbations [inherit continuity from the full continuation](goal). -/
@[fun_prop] lemma altProbability_continuous (β b : ℝ) (m : ℕ) (s : Bool) (hb : 0 < b) :
    Continuous (altProbability β b m s) := by
  unfold altProbability
  fun_prop

/-- The block normalizer is strictly positive, including at degree zero. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma blockNorm_pos (m : ℕ) : 0 < blockNorm m := by
  unfold blockNorm
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [sq_nonneg (m : ℝ)]

/-- The cited Legendre unit bound controls the tapered block on the whole unit interval. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,m,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma witness_block_abs_le_one (legendre_of_gate : ClassicalLegendreFacts) (m : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |block m t| ≤ 1 := by
  have hleg (j : ℕ) : |legendreP j (2*t-1)| ≤ 1 :=
    (legendre_of_gate j 0).2.2.1 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsum : |∑ j ∈ Finset.Icc m (2*m),
      (2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (2*t-1)| ≤ blockNorm m := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc m (2*m),
          |(2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (2*t-1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hw : 0 ≤ 2 * (j : ℝ) + 1 := by positivity
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
          abs_of_nonneg hw]
        exact mul_le_of_le_one_right hw (hleg j)
      _ = blockNorm m := witness_block_weight_sum m
  have hn := blockNorm_pos m
  have htaper : |1-t| ≤ 1 := by rw [abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  unfold block
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ 1 * (blockNorm m)⁻¹ * blockNorm m :=
      mul_le_mul (mul_le_mul_of_nonneg_right htaper (le_of_lt (inv_pos.mpr hn))) hsum
        (abs_nonneg _) (by positivity)
    _ = 1 := by simp [hn.ne']

/-- Clamping keeps the continuation within the Legendre block's unit bound. Given [the displayed inputs and assumptions](hyp:hleg,b,m,hb,x), [the stated mathematical conclusion holds](goal). -/
lemma witness_legalExtension_abs_le_one (hleg : ClassicalLegendreFacts)
    (b : ℝ) (m : ℕ) (hb : 0 < b) (x : ℝ) : |legalExtension b m x| ≤ 1 := by
  rw [witness_legalExtension_clamp b m hb x]
  apply witness_block_abs_le_one hleg
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The displayed scope makes the cancellation construction a continuous Bernoulli probability. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,s,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altProbability_properties (hleg : ClassicalLegendreFacts) (β b : ℝ) (m : ℕ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    Measurable (altProbability β b m s) ∧
    ContinuousOn (altProbability β b m s) (Icc (-1) 1) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ altProbability β b m s x ∧ altProbability β b m s x ≤ 1) := by
  have hc := altProbability_continuous β b m s hb.1
  refine ⟨hc.measurable, hc.continuousOn, ?_⟩
  intro x hx
  have hm1 : (1 : ℝ) ≤ (m : ℝ)^2 := by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hr0 : 0 ≤ b / (m : ℝ)^2 := div_nonneg hb.1.le (sq_nonneg _)
  have hr1 : b / (m : ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (hb.2.trans hm1)
  have hp0 := Real.rpow_nonneg hr0 β
  have hp1 := Real.rpow_le_one hr0 hr1 hβ.1.le
  have hv := witness_legalExtension_abs_le_one hleg b m hb.1 x
  have hprod : |(b/(m : ℝ)^2)^β * legalExtension b m x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact (mul_le_mul_of_nonneg_left hv hp0).trans (by simpa using hp1)
  have hbounds := abs_le.mp hprod
  cases s <;> simp only [altProbability, witnessSign, Bool.false_eq_true, if_false, if_true, kappa]
  · constructor <;> nlinarith [hbounds.1, hbounds.2]
  · constructor <;> nlinarith [hbounds.1, hbounds.2]
/-- The actual cancellation alternatives, on their stated parameter domains. Given [the displayed inputs and assumptions](hyp:hleg,β,b,m,s,hβ,hb,hm), [this definition specifies the stated object](goal). -/
-- @node: def:alternatives
def altLaw (hleg : ClassicalLegendreFacts) (β b : ℝ) (m : ℕ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) : LatentLaw := -- @realizes Alt(constructed Bernoulli latent laws)
  bernoulliWitness (altProbability β b m s) (altProbability_properties hleg β b m s hβ hb hm).1
    (altProbability_properties hleg β b m s hβ hb hm).2.1
    (altProbability_properties hleg β b m s hβ hb hm).2.2
/-- Noise-adapted support width. Given [the displayed inputs and assumptions](hyp:σ,m), [this definition specifies the stated object](goal). -/
-- @node: def:noise-support
def noiseSupport (σ : ℝ) (m : ℕ) : ℝ := min 1 (σ * Real.sqrt m / 8) -- @realizes Support(noise-adapted support)
/-- Noise-adapted endpoint resolution. Given [the displayed inputs and assumptions](hyp:σ,m), [this definition specifies the stated object](goal). -/
def noiseResolution (σ : ℝ) (m : ℕ) : ℝ := noiseSupport σ m / (m : ℝ)^2 -- @realizes Resolution(support divided by degree square)
/-- The direct local bump. Given [the displayed inputs and assumptions](hyp:h,x), [this definition specifies the stated object](goal). -/
def directBump (h x : ℝ) : ℝ := -- @realizes Directbump(full-interval direct perturbation)
  if x < 0 then 1 else max (1 - x/h) 0
/-- Direct witness success probability. Given [the displayed inputs and assumptions](hyp:β,h,s,x), [this definition specifies the stated object](goal). -/
def directProbability (β h : ℝ) (s : Bool) (x : ℝ) : ℝ :=
  1/2 + witnessSign s * kappa * h ^ β * directBump h x
/-- The direct extension is a continuous clipped linear function for positive width. Given [the displayed inputs and assumptions](hyp:h,hh,x), [the stated mathematical conclusion holds](goal). -/
lemma directBump_eq_clipped (h : ℝ) (hh : 0 < h) (x : ℝ) :
    directBump h x = max (1 - max x 0 / h) 0 := by
  by_cases hx : x < 0
  · simp [directBump, hx, max_eq_right hx.le]
  · simp [directBump, hx, max_eq_left (le_of_not_gt hx)]
/-- Given [the displayed inputs and assumptions](hyp:h,hh), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma directBump_continuous (h : ℝ) (hh : 0 < h) : Continuous (directBump h) := by
  have heq : directBump h = fun x => max (1 - max x 0 / h) 0 :=
    funext (directBump_eq_clipped h hh)
  rw [heq]
  fun_prop
/-- Clipping keeps the full direct extension between zero and one. Given [the displayed inputs and assumptions](hyp:h,hh,x), [the stated mathematical conclusion holds](goal). -/
lemma directBump_mem (h : ℝ) (hh : 0 < h) (x : ℝ) :
    directBump h x ∈ Icc (0 : ℝ) 1 := by
  rw [directBump_eq_clipped h hh x]
  refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
  have hdiv : 0 ≤ max x 0 / h := div_nonneg (le_max_right _ _) hh.le
  linarith
/-- Direct witness probabilities are valid under their stated parameter scope. Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directProbability_properties (β h : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) 1) :
    Measurable (directProbability β h s) ∧
    ContinuousOn (directProbability β h s) (Icc (-1) 1) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ directProbability β h s x ∧ directProbability β h s x ≤ 1) := by
  have hhpos : 0 < h := hh.1
  have hc : Continuous (directProbability β h s) := by
    unfold directProbability
    fun_prop
  refine ⟨?_, hc.continuousOn, ?_⟩
  · fun_prop
  · intro x hx
    have hb := directBump_mem h hh.1 x
    have hp0 := Real.rpow_nonneg hh.1.le β
    have hp1 := Real.rpow_le_one hh.1.le hh.2 hβ.1.le
    have hprod0 : 0 ≤ h ^ β * directBump h x := mul_nonneg hp0 hb.1
    have hprod1 : h ^ β * directBump h x ≤ 1 := by
      calc
        h ^ β * directBump h x ≤ 1 * 1 := mul_le_mul hp1 hb.2 hb.1 (by norm_num)
        _ = 1 := by norm_num
    cases s <;> simp only [directProbability, witnessSign, Bool.false_eq_true, if_false, if_true, kappa]
    · constructor <;> nlinarith [hprod0, hprod1]
    · constructor <;> nlinarith [hprod0, hprod1]
/-- The actual direct alternatives, with the same Bernoulli and error construction. Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh), [this definition specifies the stated object](goal). -/
-- @node: def:direct-alternatives
def directAltLaw (β h : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) : LatentLaw := -- @realizes h(real direct resolution with 0 < h and h ≤ 1) @realizes DirectAlt(constructed direct latent laws)
  bernoulliWitness (directProbability β h s) (directProbability_properties β h s hβ hh).1
    (directProbability_properties β h s hβ hh).2.1 (directProbability_properties β h s hβ hh).2.2
/-- Unmarked treated convolution density. Given [the displayed inputs and assumptions](hyp:σ,w), [this definition specifies the stated object](goal). -/
def treatedConvolution (σ w : ℝ) : ℝ := -- @realizes q(treated Gaussian convolution) @realizes w(real proxy argument)
  ∫ x in (0 : ℝ)..1, phi σ (w - x)
/-- Signed marked convolution perturbation. Given [the displayed inputs and assumptions](hyp:b,m,σ,w), [this definition specifies the stated object](goal). -/
def markedConvolution (b : ℝ) (m : ℕ) (σ w : ℝ) : ℝ := -- @realizes u(signed marked Gaussian convolution)
  ∫ x in (0 : ℝ)..b, block m (x/b) * phi σ (w - x)
/-- Support-to-noise ratio. Given [the displayed inputs and assumptions](hyp:b,σ), [this definition specifies the stated object](goal). -/
def likelihoodLambda (b σ : ℝ) : ℝ := b ^ 2 / (4 * σ ^ 2) -- @realizes lambda(support-to-noise ratio)

end CausalSmith.Stat.RdTruesideNoiseFrontier
