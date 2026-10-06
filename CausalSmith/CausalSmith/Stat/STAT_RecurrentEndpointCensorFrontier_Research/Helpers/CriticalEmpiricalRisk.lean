module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalExtinction
public import Causalean.Stat.EmpiricalProcess.Countable.Composition
public import Causalean.Stat.EmpiricalProcess.Countable.Threshold

/-!
# Uniform empirical arm risk

Roadmap (5): an atom-safe threshold skeleton reduces the observed arm risk
process to a countable nested indicator class. Ghost symmetrization and the
signed partial-sum maximal inequality give a distribution-free fourth moment
of order n⁻². No continuity of the censoring distribution is assumed.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open Causalean.Stat.EmpiricalProcess.Countable

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The observed arm mark, bounded by one. -/
-- @node: empiricalRiskArmMark
def empiricalRiskArmMark (a : Arm) (o : ObsHistory) : ℝ :=
  if o.treatment = a then 1 else 0

/-- The supremum of population-centered empirical risk errors on the full
study interval, including both endpoints and every censoring atom. -/
-- @node: empiricalArmRiskError
def empiricalArmRiskError (P : SubjectLaw) (a : Arm) {n : ℕ}
    (s : Fin n → ObsHistory) : ℝ :=
  localizedThresholdSup (observedLaw P) false ObsHistory.exit (fun _ => 0)
    (empiricalRiskArmMark a) (Icc 0 1) (fun _ => 0) 0 s

/-- The arm mark is measurable. -/
-- @node: measurable_empiricalRiskArmMark
@[fun_prop] lemma measurable_empiricalRiskArmMark (a : Arm) :
    Measurable (empiricalRiskArmMark a) := by
  unfold empiricalRiskArmMark
  exact measurable_const.ite
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const) measurable_const

/-- The complete risk-error supremum is measurable, even at atoms. -/
-- @node: measurable_empiricalArmRiskError
@[fun_prop] lemma measurable_empiricalArmRiskError (P : SubjectLaw) (a : Arm) (n : ℕ) :
    Measurable (empiricalArmRiskError P a (n := n)) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  apply localizedThresholdSup_measurable (observedLaw P) false ObsHistory.exit
    (fun _ => 0) (empiricalRiskArmMark a) measurable_obsHistory_exit
    measurable_const (measurable_empiricalRiskArmMark a) 1 (by norm_num)
  intro o
  simp only [empiricalRiskArmMark, abs_zero, zero_add]
  split_ifs <;> norm_num

/-- Every centered threshold evaluation is bounded uniformly by two. -/
-- @node: empiricalRisk_centered_threshold_abs_le_two
lemma empiricalRisk_centered_threshold_abs_le_two (P : SubjectLaw) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    |Causalean.Stat.Concentration.centeredEmpiricalAverage (observedLaw P) s
      (thresholdFunction false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a) t)| ≤ 2 := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let f := thresholdFunction false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a) t
  have hb (o : ObsHistory) : |f o| ≤ 1 := by
    simp only [f, thresholdFunction, Bool.false_eq_true, ↓reduceIte, zero_add,
      empiricalRiskArmMark]
    split_ifs <;> norm_num
  have he := normalized_sum_bound (fun j => f (s j)) 1 (by norm_num) (fun j => hb (s j))
  have hi : |∫ o, f o ∂observedLaw P| ≤ 1 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := observedLaw P) (f := f) (C := 1)
        (Eventually.of_forall (fun o => by simpa only [Real.norm_eq_abs] using hb o))
  change |(n : ℝ)⁻¹ * ∑ j, f (s j) - ∫ o, f o ∂observedLaw P| ≤ 2
  exact (abs_sub _ _).trans (by linarith)

/-- The full supremum is nonnegative and uniformly bounded. -/
-- @node: empiricalArmRiskError_mem_Icc
lemma empiricalArmRiskError_mem_Icc (P : SubjectLaw) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) : empiricalArmRiskError P a s ∈ Icc 0 2 := by
  let : Nonempty {t : ℝ // t ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ≤ 0} :=
    ⟨⟨0, by norm_num⟩⟩
  exact supremum_bounds _ 2 (fun t => ⟨abs_nonneg _,
    empiricalRisk_centered_threshold_abs_le_two P a s t.1⟩)

/-- Its measurable fourth power is integrable under the genuine sample law. -/
-- @node: integrable_empiricalArmRiskError_fourth
@[fun_prop] lemma integrable_empiricalArmRiskError_fourth (P : SubjectLaw) (a : Arm) (n : ℕ) :
    Integrable (fun s => empiricalArmRiskError P a s ^ 4) (sampleLaw P n) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  apply Integrable.of_bound ((measurable_empiricalArmRiskError P a n).pow_const 4).aestronglyMeasurable 16
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (empiricalArmRiskError_mem_Icc P a s).1 _)]
  exact (pow_le_pow_left₀ (empiricalArmRiskError_mem_Icc P a s).1
    (empiricalArmRiskError_mem_Icc P a s).2 4).trans (by norm_num)

/-- A threshold evaluation is exactly the empirical arm risk minus its
population probability; the sample sum retains the actual risk-set count. -/
-- @node: empiricalRisk_centered_threshold_eq
lemma empiricalRisk_centered_threshold_eq (P : SubjectLaw) (a : Arm)
    {n : ℕ} (s : Fin n → ObsHistory) (t : ℝ) :
    Causalean.Stat.Concentration.centeredEmpiricalAverage (observedLaw P) s
      (thresholdFunction false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a) t) =
      (riskSet a s t : ℝ) / n - (observedLaw P).real
        {o | o.treatment = a ∧ t ≤ o.exit} := by
  classical
  have hf : thresholdFunction false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a) t =
      ({o : ObsHistory | o.treatment = a ∧ t ≤ o.exit}).indicator (fun _ => (1 : ℝ)) := by
    funext o
    simp only [thresholdFunction, Bool.false_eq_true, ↓reduceIte, zero_add,
      empiricalRiskArmMark, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  have hm : MeasurableSet {o : ObsHistory | o.treatment = a ∧ t ≤ o.exit} :=
    (measurableSet_eq_fun measurable_obsHistory_treatment measurable_const).inter
      (measurableSet_le measurable_const measurable_obsHistory_exit)
  rw [Causalean.Stat.Concentration.centeredEmpiricalAverage, hf,
    integral_indicator hm, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  congr 1
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  simp [Set.indicator_apply, riskSet, Finset.sum_boole]

/-- The measurable supremum controls every time in the paper's study interval. -/
-- @node: empirical_risk_error_le_sup
lemma empirical_risk_error_le_sup (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t| ≤
      empiricalArmRiskError P a s := by
  rw [← observed_arm_risk_probability P hP a ht,
    ← empiricalRisk_centered_threshold_eq P a s t]
  unfold empiricalArmRiskError localizedThresholdSup centeredSup
  let f := fun u : {u : ℝ // u ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ≤ 0} =>
    |Causalean.Stat.Concentration.centeredEmpiricalAverage (observedLaw P) s
      (thresholdFunction false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a) u.1)|
  have hb : BddAbove (range f) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact empiricalRisk_centered_threshold_abs_le_two P a s u.1
  exact le_ciSup hb (⟨t, ht, le_rfl⟩ : {u : ℝ // u ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ≤ 0})

/-- Ghost symmetrization and the nested-chain maximal inequality yield a
uniform fourth moment for the entire empirical arm risk process. -/
-- @node: empiricalArmRiskError_fourth_moment_le
lemma empiricalArmRiskError_fourth_moment_le (P : SubjectLaw) (a : Arm)
    {n : ℕ} (hn : 0 < n) :
    (∫ s, empiricalArmRiskError P a s ^ 4 ∂sampleLaw P n) ≤
      (4096 / 27 : ℝ) / (n : ℝ) ^ 2 := by
  classical
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hm := measurable_empiricalRiskArmMark a
  have hi : Integrable (empiricalRiskArmMark a) (observedLaw P) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with o
    simp only [Real.norm_eq_abs, empiricalRiskArmMark]
    split_ifs <;> norm_num
  obtain ⟨D, hD, _, _, happrox, heq⟩ := localizedThreshold_countable_reduction
    (observedLaw P) false ObsHistory.exit (fun _ => 0) (empiricalRiskArmMark a)
    measurable_obsHistory_exit (integrable_const 0) hi (Icc 0 1) (fun _ => 0) 0
  let : Countable D := hD.to_subtype
  obtain ⟨u, hu, _⟩ := happrox 0 (by norm_num) le_rfl
  let : Nonempty D := ⟨⟨u 0, hu 0⟩⟩
  let F : BoundedClass ObsHistory D := {
    f := fun t => thresholdFunction false ObsHistory.exit (fun _ => 0)
      (empiricalRiskArmMark a) t.1
    bound := 1
    bound_nonneg := by norm_num
    measurable := fun t => thresholdFunction_measurable false ObsHistory.exit
      (fun _ => 0) (empiricalRiskArmMark a) measurable_obsHistory_exit measurable_const hm t.1
    bounded := by
      intro t o
      simp only [thresholdFunction, Bool.false_eq_true, ↓reduceIte, zero_add,
        empiricalRiskArmMark]
      split_ifs <;> norm_num }
  let cover : ChainCover F 1 := {
    branch := fun _ => 0
    sets := fun t => {o | o.treatment = a ∧ t.1 ≤ o.exit}
    weight := fun _ _ => 1
    containing := fun _ => univ
    nested := by
      intro t u _
      rcases le_total t.1 u.1 with h | h
      · exact Or.inr (fun o ho => ⟨ho.1, h.trans ho.2⟩)
      · exact Or.inl (fun o ho => ⟨ho.1, h.trans ho.2⟩)
    subset_containing := fun _ => subset_univ _
    represents := by
      intro t
      funext o
      simp only [F, thresholdFunction, Bool.false_eq_true, ↓reduceIte, zero_add,
        empiricalRiskArmMark, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs <;> simp_all }
  have henergy (s : Fin n → ObsHistory) (b : Fin 1) :
      coverEnergy cover s b = (n : ℝ) := by
    simp [coverEnergy, chainEnergy, cover]
  have he := centered_fourth_le_coverEnergy (observedLaw P) F cover n hn
    (fun b => by simp_rw [henergy]; exact integrable_const _)
  simp_rw [henergy] at he
  simp only [integral_const, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_mul, one_smul, probReal_univ] at he
  have heq' (s : Fin n → ObsHistory) : empiricalArmRiskError P a s =
      centeredSup (observedLaw P) F.f s := heq n s
  simp_rw [heq']
  change (∫ s, centeredSup (observedLaw P) F.f s ^ 4
    ∂Measure.pi (fun _ : Fin n => observedLaw P)) ≤ _
  convert he using 1 <;> field_simp

/-- Markov's inequality gives the distribution-free root-n risk-process
bound in roadmap (5), with a fourth-power tail in the tolerance. -/
-- @node: empiricalArmRiskError_probability_le
lemma empiricalArmRiskError_probability_le (P : SubjectLaw) (a : Arm)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    (sampleLaw P n).real {s | r < empiricalArmRiskError P a s} ≤
      (4096 / 27 : ℝ) / ((n : ℝ) ^ 2 * r ^ 4) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun s => pow_nonneg (empiricalArmRiskError_mem_Icc P a s).1 4))
    (integrable_empiricalArmRiskError_fourth P a n) (r ^ 4)
  have hs : {s : Fin n → ObsHistory | r < empiricalArmRiskError P a s} ⊆
      {s | r ^ 4 ≤ empiricalArmRiskError P a s ^ 4} := by
    intro s hs
    exact pow_le_pow_left₀ hr.le hs.le 4
  have hb := ((mul_le_mul_of_nonneg_left (measureReal_mono hs (by finiteness))
    (pow_nonneg hr.le 4)).trans hm).trans (empiricalArmRiskError_fourth_moment_le P a hn)
  rw [← div_div]
  apply (le_div_iff₀ (pow_pos hr 4)).2
  simpa only [mul_comm] using hb

/-- The root-n scaled empirical process has a uniform fourth-power tail;
this is the explicit uniform O_P(n⁻¹ᐟ²) assertion in roadmap (5). -/
-- @node: empiricalArmRiskError_root_n_probability_le
lemma empiricalArmRiskError_root_n_probability_le (P : SubjectLaw) (a : Arm)
    {n : ℕ} (hn : 0 < n) {K : ℝ} (hK : 0 < K) :
    (sampleLaw P n).real {s | K / Real.sqrt n < empiricalArmRiskError P a s} ≤
      (4096 / 27 : ℝ) / K ^ 4 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he := empiricalArmRiskError_probability_le P a hn (div_pos hK (Real.sqrt_pos.2 hnR))
  have hs : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hnR.le]
  convert he using 1
  rw [div_pow, hs]
  field_simp

/-- The population risk floor converts the absolute empirical bound into
the uniform relative-risk estimate on the genuine cutoff horizon. -/
-- @node: critical_relative_risk_error_le_sup
lemma critical_relative_risk_error_le_sup (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n)) :
    |(riskSet a s t : ℝ) /
        ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤
      empiricalArmRiskError P a s /
        ((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * bandwidth c n) := by
  have hh := bandwidth_pos_and_le_cap c hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let b := c.pMin * c.gMin * Real.exp (-c.dMax) / 2
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _)) (by norm_num)
  have hfloor := critical_cutoff_population_risk_lower c hk P hP a hh.1 hh.2 ht
  have hq : 0 < P.p a * survival P a t * retention P a t :=
    (mul_pos hb hh.1).trans_le hfloor
  have he := empirical_risk_error_le_sup c P hP a s
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, by linarith [ht.2]⟩)
  rw [show (riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1 =
      ((riskSet a s t : ℝ) / n - P.p a * survival P a t * retention P a t) /
        (P.p a * survival P a t * retention P a t) by
        generalize P.p a * survival P a t * retention P a t = q at hq ⊢
        field_simp,
    abs_div, abs_of_pos hq]
  exact div_le_div₀ (empiricalArmRiskError_mem_Icc P a s).1 he
    (mul_pos hb hh.1) hfloor

/-- A uniform finite-sample bound for failure of any prescribed relative
risk tolerance, simultaneously over all times up to the cutoff. -/
-- @node: critical_relative_risk_probability_le
lemma critical_relative_risk_probability_le (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (sampleLaw P n).real {s | ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
      ε < |(riskSet a s t : ℝ) /
        ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1|} ≤
      (4096 / 27 : ℝ) /
        ((n : ℝ) ^ 2 * (ε * ((c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * bandwidth c n)) ^ 4) := by
  let : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  let : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  have hh := (bandwidth_pos_and_le_cap c hn).1
  have hb : 0 < (c.pMin * c.gMin * Real.exp (-c.dMax) / 2) * bandwidth c n :=
    mul_pos (div_pos (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _))
      (by norm_num)) hh
  apply (measureReal_mono (μ := sampleLaw P n) ?_ (by finiteness)).trans
    (empiricalArmRiskError_probability_le P a hn (mul_pos hε hb))
  rintro s ⟨t, ht, he⟩
  exact (lt_div_iff₀ hb).mp (he.trans_le
    (critical_relative_risk_error_le_sup c hk P hP a hn s ht))

/-- The critical bandwidth makes n h² diverge, so the relative-risk tail
bound vanishes without any extra empirical-process assumption. -/
-- @node: critical_sample_bandwidth_square_tendsto_atTop
lemma critical_sample_bandwidth_square_tendsto_atTop (c : ClassConstants)
    (hk : c.kappa = 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * bandwidth c n ^ 2) atTop atTop := by
  have hp : 0 < 1 - 2 * criticalCoefficient c := by
    linarith [(criticalCoefficient_pos_lt_half c).2]
  apply ((tendsto_rpow_atTop hp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
  filter_upwards [critical_bandwidth_eventually_sample_square c hk] with n hn
  exact hn.symm

/-- Roadmap (6) along every triangular model-law sequence, uniformly over
the full cutoff horizon; in particular the half-relative-risk event has
probability tending to one. -/
-- @node: critical_relative_risk_triangular_tendsto
lemma critical_relative_risk_triangular_tendsto (c : ClassConstants)
    (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real
      {s | ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        ε < |(riskSet a s t : ℝ) /
          ((n : ℝ) * ((Pseq n).p a * survival (Pseq n) a t * retention (Pseq n) a t)) - 1|})
      atTop (nhds 0) := by
  let b := c.pMin * c.gMin * Real.exp (-c.dMax) / 2
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (mul_pos (mul_pos c.pMin_pos c.gMin_pos) (Real.exp_pos _)) (by norm_num)
  have hi := (critical_sample_bandwidth_square_tendsto_atTop c hk).inv_tendsto_atTop
  have ht : Tendsto (fun n : ℕ => ((4096 / 27 : ℝ) / (ε * b) ^ 4) *
      (((n : ℝ) * bandwidth c n ^ 2)⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using (hi.pow 2).const_mul ((4096 / 27 : ℝ) / (ε * b) ^ 4)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := critical_relative_risk_probability_le c hk (Pseq n) (hP n) a
    (show 0 < n by omega) hε
  convert he using 1 <;> dsimp [b] <;> field_simp

/-- The two-arm version of roadmap (6) follows by a union bound, retaining
an arbitrary triangular sequence and every time in the cutoff interval. -/
-- @node: critical_relative_risk_both_arms_triangular_tendsto
lemma critical_relative_risk_both_arms_triangular_tendsto (c : ClassConstants)
    (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real
      {s | ∃ a : Arm, ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        ε < |(riskSet a s t : ℝ) /
          ((n : ℝ) * ((Pseq n).p a * survival (Pseq n) a t * retention (Pseq n) a t)) - 1|})
      atTop (nhds 0) := by
  have ht := (critical_relative_risk_triangular_tendsto c hk Pseq hP false hε).add
    (critical_relative_risk_triangular_tendsto c hk Pseq hP true hε)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using ht)
  intro n
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  have he : {s : Fin n → ObsHistory | ∃ a : Arm, ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
      ε < |(riskSet a s t : ℝ) /
        ((n : ℝ) * ((Pseq n).p a * survival (Pseq n) a t * retention (Pseq n) a t)) - 1|} =
      {s | ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        ε < |(riskSet false s t : ℝ) /
          ((n : ℝ) * ((Pseq n).p false * survival (Pseq n) false t * retention (Pseq n) false t)) - 1|} ∪
      {s | ∃ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        ε < |(riskSet true s t : ℝ) /
          ((n : ℝ) * ((Pseq n).p true * survival (Pseq n) true t * retention (Pseq n) true t)) - 1|} := by
    ext s
    simp only [mem_setOf_eq, mem_union, Bool.exists_bool]
  rw [he]
  exact measureReal_union_le _ _

/-- The model supplies a linear population risk floor at every study time,
including interior times, rather than merely a floor at the cutoff. -/
-- @node: critical_population_risk_linear_lower
lemma critical_population_risk_linear_lower (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2)) * (1 - t) ≤
      P.p a * survival P a t * retention P a t := by
  have hr : min c.Gint (c.gMin / 2) * (1 - t) ≤ retention P a t := by
    by_cases hi : t ≤ 1 - c.x0
    · calc
        _ ≤ c.Gint * (1 - t) := mul_le_mul_of_nonneg_right (min_le_left _ _)
          (by linarith [ht.2])
        _ ≤ c.Gint := by nlinarith [c.Gint_pos, ht.1]
        _ ≤ _ := hP.interiorRetention a t ⟨ht.1, hi⟩
    · have he := retention_ge_half_gMin_rpow c P hP a ⟨lt_of_not_ge hi, ht.2⟩
      simp only [hk, Real.rpow_one] at he
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith [ht.2])).trans he
  have hs := (survival_bounds_of_deathBounds c P hP.deathBounds a ⟨ht.1, ht.2.le⟩).1
  have hp := hP.treatmentOverlap a
  have he := mul_le_mul
    (mul_le_mul hp hs (Real.exp_pos _).le (c.pMin_pos.le.trans hp)) hr
    (mul_nonneg (le_of_lt (lt_min c.Gint_pos (div_pos c.gMin_pos (by norm_num))))
      (sub_nonneg.mpr ht.2.le))
    (mul_nonneg (c.pMin_pos.le.trans hp) (Real.exp_pos _).le)
  simpa only [mul_assoc] using he

/-- On the half-relative-risk event the actual empirical risk satisfies the
time-dependent floor needed by the localized optional-variation proof (28). -/
-- @node: critical_empirical_risk_linear_floor_of_relative_control
lemma critical_empirical_risk_linear_floor_of_relative_control (c : ClassConstants)
    (hk : c.kappa = 1) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 - bandwidth c n))
    (he : |(riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) - 1| ≤ 1 / 2) :
    (n : ℝ) * (c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2) * (1 - t) ≤
      riskSet a s t := by
  have hh := (bandwidth_pos_and_le_cap c hn).1
  have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hf := critical_population_risk_linear_lower c hk P hP a ht1
  have hb : 0 < c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) :=
    mul_pos (mul_pos c.pMin_pos (Real.exp_pos _))
      (lt_min c.Gint_pos (div_pos c.gMin_pos (by norm_num)))
  have hq : 0 < P.p a * survival P a t * retention P a t :=
    (mul_pos hb (by linarith [ht.2] : 0 < 1 - t)).trans_le hf
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : (1 / 2 : ℝ) ≤ (riskSet a s t : ℝ) /
      ((n : ℝ) * (P.p a * survival P a t * retention P a t)) := by
    linarith [(abs_le.mp he).1]
  have hcount := (le_div_iff₀ (mul_pos hnR hq)).mp hr
  have hnf := mul_le_mul_of_nonneg_left hf hnR.le
  nlinarith

/-- Failure of the linear empirical risk floor vanishes along triangular
laws; this discharges the risk localization probability needed in (29). -/
-- @node: critical_empirical_risk_linear_floor_failure_triangular_tendsto
lemma critical_empirical_risk_linear_floor_failure_triangular_tendsto (c : ClassConstants)
    (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (a : Arm) :
    Tendsto (fun n : ℕ => (sampleLaw (Pseq n) n).real
      {s | ¬ ∀ t ∈ Icc (0 : ℝ) (1 - bandwidth c n),
        (n : ℝ) * (c.pMin * Real.exp (-c.dMax) * min c.Gint (c.gMin / 2) / 2) * (1 - t) ≤ riskSet a s t})
      atTop (nhds 0) := by
  classical
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (critical_relative_risk_triangular_tendsto c hk Pseq hP a (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  let : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  let : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by unfold sampleLaw; infer_instance
  apply measureReal_mono _ (by finiteness)
  intro s hs
  by_contra hc
  apply hs
  intro t ht
  apply critical_empirical_risk_linear_floor_of_relative_control c hk (Pseq n) (hP n) a
    (show 0 < n by omega) s ht
  exact le_of_not_gt (fun he => hc ⟨t, ht, he⟩)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
