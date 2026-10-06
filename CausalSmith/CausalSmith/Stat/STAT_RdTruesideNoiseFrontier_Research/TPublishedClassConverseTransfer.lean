module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TUniformFrontier

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
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


/-- A benchmark law has locally continuous potential-mean versions on an open neighborhood of zero. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma benchmark_mean_neighborhood (L : LatentLaw) :
    ∃ r > 0, ∀ d, ContinuousOn (L.mu d) (Ioo (-r) r) := by
  refine ⟨1 / 2, by norm_num, fun d => (L.mu_cont d).mono ?_⟩
  intro x hx
  constructor <;> linarith [hx.1, hx.2]
/-- Zero density outside the latent interval extends the set-integral version identity. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma benchmark_version_on_real (L : LatentLaw) :
    ∀ d B, MeasurableSet B →
      (∫ ω in {ω | score ω ∈ B}, pot d ω ∂(L.P)) = ∫ x in B, L.mu d x * L.f x := by
  intro d B hB
  rw [L.mu_version d B hB]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB inter_subset_left
  intro x hx
  have hout : x ∉ Icc (-1 : ℝ) 1 := by
    intro hin
    exact hx.2 ⟨hx.1, hin⟩
  rw [L.f_zero x hout, mul_zero]
/-- The same law, density and versions on the unrestricted score carrier. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
def benchmarkEmbedding (L : LatentLaw) : GaussianLawData where
  Q := L.P
  prob := L.prob
  a := L.f
  density := L.density
  density_nonneg := L.f_nonneg
  v := L.mu
  version := benchmark_version_on_real L
  mean_cont := benchmark_mean_neighborhood L
/-- The embedding inherits local density positivity and the observed-outcome error
independence by applying the observation function to the latent schedule. Given [the displayed inputs and assumptions](hyp:β,σ,L,hL), [the stated mathematical conclusion holds](goal). -/
lemma benchmarkEmbedding_mem (β σ : ℝ) (L : LatentLaw) (hL : Model β σ L) :
    GaussianIdClass σ (benchmarkEmbedding L) := by
  refine ⟨?_, hL.gaussian, ?_, ?_⟩
  · refine ⟨1 / 2, by norm_num, L.f_cont.mono ?_, ?_⟩
    · intro x hx
      constructor <;> linarith [hx.1, hx.2]
    · intro x hx
      have hin : x ∈ Icc (-1 : ℝ) 1 := by
        constructor <;> linarith [hx.1, hx.2]
      have hlow := (hL.density x hin).1
      change 0 < L.f x
      linarith
  · let marked : ℝ × Bool × Bool → ℝ × ℝ := fun z =>
      (z.1, bit (if 0 ≤ z.1 then z.2.2 else z.2.1))
    have hm : Measurable marked := by
      have hb : Measurable bit := measurable_of_countable bit
      have hs : MeasurableSet {z : ℝ × Bool × Bool | 0 ≤ z.1} :=
        measurableSet_le measurable_const measurable_fst
      exact measurable_fst.prodMk (hb.comp
        ((measurable_snd.snd).ite hs (measurable_snd.fst)))
    have hi := hL.independent.comp measurable_id hm
    have heq : (fun ω : Latent => (score ω, bit (outcome ω))) =
        marked ∘ (fun ω : Latent => (score ω, ω.2.1, ω.2.2.1)) := by
      funext ω
      by_cases h : 0 ≤ score ω <;>
        simp [marked, outcome, side, h]
    change IndepFun errorCoord (fun ω : Latent => (score ω, bit (outcome ω))) L.P
    rw [heq]
    exact hi
  · intro d
    have hmean := hL.means d 0 (by norm_num)
    change 0 ≤ L.mu d 0 ∧ L.mu d 0 ≤ 1
    constructor <;> linarith

/-- Inclusion preserves the target, observed law, and the whole seeded experiment. Given [the displayed inputs and assumptions](hyp:β,σ,L,hL), [the stated mathematical conclusion holds](goal). -/
lemma benchmarkEmbedding_preserves (β σ : ℝ) (L : LatentLaw) (hL : Model β σ L) :
    GaussianIdClass σ (benchmarkEmbedding L) ∧
    gaussianTarget (benchmarkEmbedding L) = theta L ∧
    gaussianPobs (benchmarkEmbedding L) σ = Pobs L σ ∧
    ∀ n : ℕ, gaussianExperiment (benchmarkEmbedding L) σ n = experiment L σ n := by
  exact ⟨benchmarkEmbedding_mem β σ L hL, rfl, rfl, fun _ => rfl⟩

/-- The observation map is measurable, including its cutoff treatment coordinate. Given [the displayed inputs and assumptions](hyp:σ), [the stated mathematical conclusion holds](goal). -/
lemma observed_map_measurable (σ : ℝ) : Measurable (obs σ) := by
  have hs : Measurable score := by unfold score; fun_prop
  have he : Measurable errorCoord := by unfold errorCoord; fun_prop
  have hd : Measurable side := by
    unfold side
    have hset := measurableSet_le (measurable_const : Measurable (fun _ : Latent => (0 : ℝ))) hs
    have heq : (fun ω : Latent => decide (0 ≤ score ω)) =
        (fun ω => if 0 ≤ score ω then true else false) := by
      funext ω
      by_cases h : 0 ≤ score ω <;> simp [h]
    rw [heq]
    exact measurable_const.ite hset measurable_const
  have hy : Measurable outcome := by
    unfold outcome
    exact (measurable_snd.snd.fst).ite
      (by simpa [side] using (measurableSet_le measurable_const hs))
      (measurable_snd.fst)
  exact (hs.add (measurable_const.mul he)).prodMk (hd.prodMk hy)

/-- Every larger-class observation experiment, including the seed, has unit mass. Given [the displayed inputs and assumptions](hyp:Q,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma gaussianExperiment_probability (Q : GaussianLawData) (σ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (gaussianExperiment Q σ n) := by
  letI : IsProbabilityMeasure Q.Q := Q.prob
  letI : IsProbabilityMeasure (gaussianPobs Q σ) :=
    Measure.isProbabilityMeasure_map (observed_map_measurable σ).aemeasurable
  unfold gaussianExperiment seedLaw
  infer_instance

/-- Binary cutoff means put the causal contrast in the declared target interval. Given [the displayed inputs and assumptions](hyp:Q,σ,hQ), [the stated mathematical conclusion holds](goal). -/
lemma gaussianTarget_mem (Q : GaussianLawData) (σ : ℝ) (hQ : GaussianIdClass σ Q) :
    gaussianTarget Q ∈ Icc (-1 : ℝ) 1 := by
  have h₁ := hQ.2.2.2 true
  have h₀ := hQ.2.2.2 false
  unfold gaussianTarget
  constructor <;> linarith

/-- The constant full interval is an admissible connected closed interval procedure. Given [the displayed inputs and assumptions](hyp:n), [this definition specifies the stated object](goal). -/
def fullIntervalProc (n : ℕ) : IntervalProc n where
  lo := fun _ => -1
  hi := fun _ => 1
  lo_meas := measurable_const
  hi_meas := measurable_const
  endpoints := fun _ => by norm_num

/-- The full target interval covers every law of the larger class with probability one. Given [the displayed inputs and assumptions](hyp:n,σ), [the stated mathematical conclusion holds](goal). -/
lemma fullIntervalProc_gaussian_honest (n : ℕ) (σ : ℝ) :
    fullIntervalProc n ∈ gaussianHonestIntervals n σ := by
  intro Q hQ
  letI := gaussianExperiment_probability Q σ n
  have ht := gaussianTarget_mem Q σ hQ
  have hevent : Causalean.Stat.coverageEvent (fullIntervalProc n).lo
      (fullIntervalProc n).hi (gaussianTarget Q) = univ := by
    ext z
    simp [Causalean.Stat.coverageEvent, fullIntervalProc, ht.1, ht.2]
  rw [hevent]
  norm_num [Measure.real]

/-- The zero estimator bounds the extended minimax risk by one. Given [the displayed inputs and assumptions](hyp:n,σ), [the stated mathematical conclusion holds](goal). -/
lemma gaussian_minimax_risk_le_one (n : ℕ) (σ : ℝ) :
    Causalean.Stat.minimaxValueENNReal
      (fun (T : Estimator n) (Q : {Q // GaussianIdClass σ Q}) =>
        ∫⁻ z, ENNReal.ofReal |T.val z - gaussianTarget Q.val|
          ∂gaussianExperiment Q.val σ n) ≤ 1 := by
  refine (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (⟨fun _ => 0, measurable_const⟩ : Estimator n)).trans ?_
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro Q
  letI := gaussianExperiment_probability Q.val σ n
  have ht := gaussianTarget_mem Q.val σ Q.property
  have hb : |0 - gaussianTarget Q.val| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  calc
    _ ≤ ∫⁻ _ : Input n, (1 : ℝ≥0∞) ∂gaussianExperiment Q.val σ n :=
      lintegral_mono fun _ => (ENNReal.ofReal_le_ofReal hb).trans_eq (by norm_num)
    _ = 1 := by simp

/-- The full interval bounds the extended honest minimax length by two. Given [the displayed inputs and assumptions](hyp:n,σ), [the stated mathematical conclusion holds](goal). -/
lemma gaussian_minimax_length_le_two (n : ℕ) (σ : ℝ) :
    Causalean.Stat.minimaxValueENNReal
      (fun (I : {I // I ∈ gaussianHonestIntervals n σ}) (Q : {Q // GaussianIdClass σ Q}) =>
        ∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (I.val.lo z) (I.val.hi z))
          ∂gaussianExperiment Q.val σ n) ≤ 2 := by
  refine (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    ⟨fullIntervalProc n, fullIntervalProc_gaussian_honest n σ⟩).trans ?_
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro Q
  letI := gaussianExperiment_probability Q.val σ n
  norm_num [fullIntervalProc, Causalean.Stat.intervalLength]

/-- Honesty on the larger class implies honesty on the benchmark via the exact embedding. Given [the displayed inputs and assumptions](hyp:β,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma gaussian_honest_subset (β σ : ℝ) (n : ℕ) :
    gaussianHonestIntervals n σ ⊆ honestIntervals β n σ := by
  intro I hI L hL
  exact hI (benchmarkEmbedding L) (benchmarkEmbedding_mem β σ L hL)

/-- Minimax absolute risk increases under target-preserving experiment inclusion. Given [the displayed inputs and assumptions](hyp:β,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma benchmark_risk_le_gaussian (β σ : ℝ) (n : ℕ) :
    risk β n σ ≤ gaussianRisk n σ := by
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by norm_num) (gaussian_minimax_risk_le_one n σ))
  exact Causalean.Stat.minimaxValueENNReal_mono_class
    (fun L => ⟨benchmarkEmbedding L.val, benchmarkEmbedding_mem β σ L.val L.property⟩)
    (fun _ _ => le_rfl)

/-- Restricting honest procedures and enlarging the law class increases minimax length. Given [the displayed inputs and assumptions](hyp:β,σ,n), [the stated mathematical conclusion holds](goal). -/
lemma benchmark_length_le_gaussian (β σ : ℝ) (n : ℕ) :
    lengthRisk β n σ ≤ gaussianLength n σ := by
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by norm_num) (gaussian_minimax_length_le_two n σ))
  apply Causalean.Stat.minimaxValueENNReal_le_minimaxValue
  intro I
  refine ⟨⟨I.val, gaussian_honest_subset β σ n I.property⟩, ?_⟩
  change (⨆ L : {L // Model β σ L}, expectedLength L.val σ n I.val) ≤
    ⨆ Q : {Q // GaussianIdClass σ Q},
      ∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (I.val.lo z) (I.val.hi z))
        ∂gaussianExperiment Q.val σ n
  apply iSup_le
  intro L
  exact le_iSup_of_le
    ⟨benchmarkEmbedding L.val, benchmarkEmbedding_mem β σ L.val L.property⟩ le_rfl

/-- Scaling the independent standard error gives the three published error/density hypotheses. Given [the displayed inputs and assumptions](hyp:σ,Q,hQ), [the stated mathematical conclusion holds](goal). -/
lemma gaussian_published_hypotheses (σ : ℝ) (Q : GaussianLawData)
    (hQ : GaussianIdClass σ Q) : PeiShen1Y σ Q ∧ PeiShen2C Q ∧ PeiShen7 σ Q := by
  refine ⟨?_, ?_, ?_⟩
  · exact hQ.2.2.1.comp (by fun_prop) measurable_id
  · obtain ⟨r, hr, _, ha⟩ := hQ.1
    exact ⟨r, hr, ha⟩
  · unfold PeiShen7
    have he : Measurable errorCoord := by unfold errorCoord; fun_prop
    rw [show (fun ω => σ * errorCoord ω) = (σ * ·) ∘ errorCoord from rfl,
      ← Measure.map_map (by fun_prop) he, hQ.2.1, gaussianReal_map_const_mul]
    congr 1
    · exact mul_zero σ
    · apply NNReal.coe_injective
      change σ ^ 2 * 1 = σ ^ 2
      ring

/-- Benchmark laws embed preserving the observed experiment and target; minimax values increase
on the larger class, which receives only lower bounds. The Pei--Shen comparison is source
provenance and has no role in constructing the embedding or proving minimax class monotonicity. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
-- @node: prop:published-class-converse-transfer
theorem published_class_converse_transfer (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    (∀ σ ∈ Icc (0 : ℝ) 1, ∀ L : LatentLaw, Model β σ L →
      GaussianIdClass σ (benchmarkEmbedding L) ∧
      gaussianTarget (benchmarkEmbedding L) = theta L ∧
      gaussianPobs (benchmarkEmbedding L) σ = Pobs L σ ∧
      ∀ n : ℕ, gaussianExperiment (benchmarkEmbedding L) σ n = experiment L σ n) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      risk β n σ ≤ gaussianRisk n σ ∧ c * frontierRate β n σ ≤ risk β n σ ∧
      lengthRisk β n σ ≤ gaussianLength n σ ∧ c * frontierRate β n σ ≤ lengthRisk β n σ) ∧
    (∀ σ ∈ Ioc (0 : ℝ) 1, ∀ Q : GaussianLawData, GaussianIdClass σ Q →
      PeiShen1Y σ Q ∧ PeiShen2C Q ∧ PeiShen7 σ Q) := by
  obtain ⟨⟨c, C, hc, hC, hfrontier⟩, _⟩ :=
    uniform_frontier β hβ
  refine ⟨?_, ⟨c, hc, ?_⟩, ?_⟩
  · intro σ hσ L hL
    exact benchmarkEmbedding_preserves β σ L hL
  · intro n hn σ hσ
    have hmatched := (hfrontier n hn σ hσ).2.1
    exact ⟨benchmark_risk_le_gaussian β σ n, hmatched.1,
      benchmark_length_le_gaussian β σ n, hmatched.2.2.2.2.1⟩
  · intro σ hσ Q hQ
    exact gaussian_published_hypotheses σ Q hQ

end CausalSmith.Stat.RdTruesideNoiseFrontier
