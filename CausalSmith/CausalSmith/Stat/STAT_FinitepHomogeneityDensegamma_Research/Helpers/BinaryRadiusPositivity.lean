module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryComparison
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-! Small signed-binary cosine alternatives give positive finite-sample critical radii. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A balanced-treatment binary law with zero baseline and a scaled cosine effect. This statement assumes [the t parameter](hyp:t). [This is the stated defined object](goal). -/
-- @node: smallCosineLaw
def smallCosineLaw (t : ℝ) : ObservedLaw :=
  binaryConversion (deterministicLaw (ContinuousMap.const unitInterval (1/2)) 0 (t • witnessCos))

/-- The cosine construction retains its literal propensity, baseline and effect. This statement assumes [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: smallCosineLaw_primitives
lemma smallCosineLaw_primitives (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    (smallCosineLaw t).e = ContinuousMap.const unitInterval (1/2) ∧
    (smallCosineLaw t).m0 = 0 ∧ (smallCosineLaw t).tau = t • witnessCos ∧
    (smallCosineLaw t).P = design ⊗ₘ recordKernel (fun _ => 1/2) measurable_const
      (fun a => binaryArm (if a then t • witnessCos else 0)) := by
  have hd := deterministicLaw_primitives (ContinuousMap.const unitInterval (1/2)) 0
    (t • witnessCos) (fun _ => by norm_num)
  have hc (x : unitInterval) : |(t • witnessCos) x| ≤ 1/2 := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
    nlinarith [witnessCos_cap x, abs_nonneg (witnessCos x)]
  have hb : BaselineCap (deterministicLaw (ContinuousMap.const unitInterval (1/2)) 0 (t • witnessCos)) := by
    simp only [BaselineCap, hd.2.1, ContinuousMap.zero_apply, abs_zero]
    norm_num
  have he : EffectCap (deterministicLaw (ContinuousMap.const unitInterval (1/2)) 0 (t • witnessCos)) := by
    simpa only [EffectCap, hd.2.2.1] using hc
  have h := binaryConversion_primitives _ hb he
  refine ⟨h.1.trans hd.1, h.2.1.trans hd.2.1, h.2.2.1.trans hd.2.2.1, ?_⟩
  have hf : (⇑(ContinuousMap.const unitInterval (1/2:ℝ))) = (fun _ => 1/2) := by
    funext x
    simp
  simpa only [smallCosineLaw, hd.1, hd.2.1, hd.2.2.1, zero_add, hf] using h.2.2.2.1

/-- Scaling down the cosine preserves every primitive predicate of the signed-binary model. This statement assumes [the hw condition](hyp:hw), [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: smallCosineLaw_inBinaryModel
lemma smallCosineLaw_inBinaryModel (w : Smooth3) (hw : w.Valid) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) : InBinaryModel w (smallCosineLaw t) := by
  apply binaryConversion_inModel
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  apply deterministicLaw_inModel _ hv
  · intro x; norm_num
  · apply holderBall_of_unit_lipschitz _ _ hw.1.2 <;> intros <;> norm_num
  · apply holderBall_of_unit_lipschitz _ _ hw.2.1.2 <;> intros <;> simp
  · have hh := witnessCos_holder w.γ hw.2.2.2
    refine ⟨(t • witnessCos).continuous, ?_, ?_⟩
    · intro x
      simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
      nlinarith [witnessCos_cap x, abs_nonneg (witnessCos x)]
    · intro x z
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_nonneg ht.1]
      calc
        _ ≤ t*(20*|(x:ℝ)-(z:ℝ)|^w.γ) := mul_le_mul_of_nonneg_left (hh.2.2 x z) ht.1
        _ ≤ 20*|(x:ℝ)-(z:ℝ)|^w.γ := mul_le_of_le_one_left (by positivity) ht.2
  · intro x; simp
  · intro x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
    nlinarith [witnessCos_cap x, abs_nonneg (witnessCos x)]

/-- The null member has a constant zero original mean effect. This statement assumes [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: smallCosineLaw_inBinaryNull
lemma smallCosineLaw_inBinaryNull (w : Smooth3) (hw : w.Valid) :
    InBinaryNull w (smallCosineLaw 0) := by
  refine { smallCosineLaw_inBinaryModel w hw 0 (by norm_num) with nullConstancy := ?_ }
  refine ⟨0, by norm_num, by norm_num, ?_⟩
  rw [(smallCosineLaw_primitives 0 (by norm_num)).2.2.1]
  simp

/-- The centered cosine distance is its amplitude multiplier times the nonempty-model witness distance. This statement assumes [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: smallCosineLaw_distance
lemma smallCosineLaw_distance (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    hetDist (smallCosineLaw t) = t*d0 := by
  have hτ := (smallCosineLaw_primitives t ht).2.2.1
  have hm : meanTau (smallCosineLaw t) = 0 := by
    simp only [meanTau, hτ, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul,
      witnessCos_integral, mul_zero]
  unfold hetDist
  rw [hm, hτ]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, sub_zero, mul_pow, integral_const_mul,
    witnessCos_sq_integral]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1]
  have hd : Real.sqrt (1/128:ℝ) = d0 := by
    have h := separatedWitness_distance
    simpa only [hetDist, meanTau, separatedWitness_tau, witnessCos_integral,
      sub_zero, witnessCos_sq_integral] using h
  rw [hd]

/-- A signed-binary arm integrates an event as its two explicit sign probabilities. This statement assumes [the hm condition](hyp:hm), [the hS condition](hyp:hS). [This is the stated conclusion](goal). -/
-- @node: binaryArm_event_real
lemma binaryArm_event_real (m : Nuisance) (hm : ∀ x, |m x| ≤ 1)
    (x : unitInterval) (S : Set ℝ) (hS : MeasurableSet S) :
    (binaryArm m x).real S =
      ((1+m x)/2)*(if (1:ℝ) ∈ S then 1 else 0)+
      ((1-m x)/2)*(if (-1:ℝ) ∈ S then 1 else 0) := by
  have hx := abs_le.mp (hm x)
  change (binaryArmMeasure m x).real S = _
  rw [binaryArmMeasure, measureReal_add_apply
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [measureReal_ennreal_smul_apply]
  simp only [Measure.real, Measure.dirac_apply' _ hS, Set.indicator, Pi.one_apply]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ (1+m x)/2),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ (1-m x)/2)]
  split_ifs <;> norm_num

/-- The balanced binary record kernel has four explicit event masses. This statement assumes [the hτ condition](hyp:hτ), [the hS condition](hyp:hS). [This is the stated conclusion](goal). -/
-- @node: binaryRecord_event_real
lemma binaryRecord_event_real (τ : Nuisance) (hτ : ∀ x, |τ x| ≤ 1)
    (x : unitInterval) (S : Set (Bool × ℝ)) (hS : MeasurableSet S) :
    (recordMeasure (fun _ => 1/2) (fun a => binaryArm (if a then τ else 0)) x).real S =
      (1/4)*((1+τ x)*(if (true,(1:ℝ)) ∈ S then 1 else 0)+
        (1-τ x)*(if (true,(-1:ℝ)) ∈ S then 1 else 0)+
        (if (false,(1:ℝ)) ∈ S then 1 else 0)+
        (if (false,(-1:ℝ)) ∈ S then 1 else 0)) := by
  letI : IsMarkovKernel (binaryArm τ) := binaryArm_markov τ hτ
  letI : IsMarkovKernel (binaryArm (0 : Nuisance)) := binaryArm_markov 0 (by simp)
  have hp (a : Bool) (μ : Measure ℝ) : (Measure.dirac a).prod μ = μ.map (Prod.mk a) := by
    rw [Measure.prod, Measure.dirac_bind (measurable_of_countable _)]
  simp only [recordMeasure, if_true, Bool.false_eq_true, if_false]
  rw [measureReal_add_apply
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [measureReal_ennreal_smul_apply]
  simp only [hp]
  rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1-1/2)]
  rw [map_measureReal_apply measurable_prodMk_left hS,
    map_measureReal_apply measurable_prodMk_left hS,
    binaryArm_event_real τ hτ x _ (hS.preimage measurable_prodMk_left),
    binaryArm_event_real 0 (by simp) x _ (hS.preimage measurable_prodMk_left)]
  simp only [Set.mem_preimage, ContinuousMap.zero_apply]
  ring

/-- Only the two treated sign masses change when a zero-effect binary record is perturbed. This statement assumes [the hτ condition](hyp:hτ), [the hS condition](hyp:hS). [This is the stated conclusion](goal). -/
-- @node: binaryRecord_event_gap
lemma binaryRecord_event_gap (τ : Nuisance) (hτ : ∀ x, |τ x| ≤ 1)
    (x : unitInterval) (S : Set (Bool × ℝ)) (hS : MeasurableSet S) :
    |(recordMeasure (fun _ => 1/2) (fun a => binaryArm (if a then (0:Nuisance) else 0)) x).real S-
      (recordMeasure (fun _ => 1/2) (fun a => binaryArm (if a then τ else 0)) x).real S| ≤ |τ x|/4 := by
  rw [binaryRecord_event_real 0 (by simp) x S hS, binaryRecord_event_real τ hτ x S hS]
  simp only [ContinuousMap.zero_apply]
  have he : (1/4)*((1+0)*(if (true,(1:ℝ)) ∈ S then 1 else 0)+
      (1-0)*(if (true,(-1:ℝ)) ∈ S then 1 else 0)+
      (if (false,(1:ℝ)) ∈ S then 1 else 0)+(if (false,(-1:ℝ)) ∈ S then 1 else 0))-
    (1/4)*((1+τ x)*(if (true,(1:ℝ)) ∈ S then 1 else 0)+
      (1-τ x)*(if (true,(-1:ℝ)) ∈ S then 1 else 0)+
      (if (false,(1:ℝ)) ∈ S then 1 else 0)+(if (false,(-1:ℝ)) ∈ S then 1 else 0)) =
    -(τ x/4)*((if (true,(1:ℝ)) ∈ S then 1 else 0)-(if (true,(-1:ℝ)) ∈ S then 1 else 0)) := by ring
  rw [he, abs_mul, abs_neg, abs_div]
  have hi : |((if (true,(1:ℝ)) ∈ S then (1:ℝ) else 0)-
      (if (true,(-1:ℝ)) ∈ S then 1 else 0))| ≤ 1 := by split_ifs <;> norm_num
  simpa using mul_le_of_le_one_right (by positivity : 0 ≤ |τ x|/|4|) hi

/-- The one-record cosine perturbation has total variation at most half its outcome-mean amplitude. This statement assumes [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: smallCosineLaw_tv
lemma smallCosineLaw_tv (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    Causalean.Stat.tvDist (smallCosineLaw 0).P (smallCosineLaw t).P ≤ t/16 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hc (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (x : unitInterval) : |(r • witnessCos) x| ≤ r/8 := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr.1]
    nlinarith [witnessCos_cap x]
  let κ (r : ℝ) := recordKernel (fun _ : unitInterval => 1/2) measurable_const
    (fun a => binaryArm (if a then r • witnessCos else 0))
  have hk (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) : IsMarkovKernel (κ r) := by
    apply recordKernel_markov _ _ _ (fun _ => by norm_num)
    intro a
    cases a
    · exact binaryArm_markov 0 (by simp)
    · exact binaryArm_markov (r • witnessCos) (fun x => (hc r hr x).trans (by linarith))
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨S,hS⟩
  have hreal (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) :
      (smallCosineLaw r).P.real S = ∫ x, (κ r x).real (Prod.mk x ⁻¹' S) ∂design := by
    letI := hk r hr
    rw [(smallCosineLaw_primitives r hr).2.2.2]
    change (design ⊗ₘ κ r).real S = _
    rw [measureReal_def, Measure.compProd_apply hS, ← integral_toReal]
    · rfl
    · exact (Kernel.measurable_kernel_prodMk_left hS).aemeasurable
    · filter_upwards with x
      exact measure_lt_top (κ r x) _
  have hi (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) :
      Integrable (fun x => (κ r x).real (Prod.mk x ⁻¹' S)) design := by
    letI := hk r hr
    apply Integrable.of_bound (Kernel.measurable_kernel_prodMk_left hS).ennreal_toReal.aestronglyMeasurable 1
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one)
  rw [hreal 0 (by norm_num), hreal t ht, ← integral_sub (hi 0 (by norm_num)) (hi t ht)]
  calc
    _ ≤ ∫ x, |(κ 0 x).real (Prod.mk x ⁻¹' S)-(κ t x).real (Prod.mk x ⁻¹' S)| ∂design :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : unitInterval, t/16 ∂design := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (integrable_const _)
      apply ae_of_all
      intro x
      have hh := binaryRecord_event_gap (t • witnessCos)
        (fun x => (hc t ht x).trans (by linarith)) x (Prod.mk x ⁻¹' S) (hS.preimage measurable_prodMk_left)
      change |(recordMeasure _ (fun a => binaryArm (if a then (0:ℝ) • witnessCos else 0)) x).real _-
        (recordMeasure _ (fun a => binaryArm (if a then t • witnessCos else 0)) x).real _| ≤ _
      simp only [zero_smul] at ⊢
      exact hh.trans (by linarith [hc t ht x])
    _ = t/16 := by simp

/-- A legal two-point experiment lower-bounds the randomized testing risk, including the public seed. This statement assumes [the h0 condition](hyp:h0), [the h1 condition](hyp:h1), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: testingRiskOn_ge_of_two_point
lemma testingRiskOn_ge_of_two_point (n : ℕ) (Null Alt : Set ObservedLaw) (r : ℝ)
    (P0 P1 : ObservedLaw) (h0 : P0 ∈ Null) (h1 : P1 ∈ Alt) (hr : r ≤ hetDist P1) :
    9/10-Causalean.Stat.tvDist (Measure.pi fun _ : Fin n => P0.P)
      (Measure.pi fun _ : Fin n => P1.P) ≤ testingRiskOn n r Null Alt := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let zeroTest : Test n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : LevelValid n Null zeroTest := by
    intro law _
    simp [rejectProb, zeroTest]
  letI : Nonempty {φ : Test n // LevelValid n Null φ} := ⟨⟨zeroTest,hz⟩⟩
  letI : Nonempty {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} := ⟨⟨P1,h1,hr⟩⟩
  unfold testingRiskOn
  apply le_ciInf
  intro φ
  have hf := seedAverage_properties n φ.1
  have htv := Causalean.Stat.tvDist_integral_range
    (Measure.pi fun _ : Fin n => P0.P) (Measure.pi fun _ : Fin n => P1.P)
    (fun data => ∫ u, φ.1.1 (data,u) ∂design) hf.1 0 1 (by norm_num)
    (fun data => by simpa using hf.2 data)
  have hex (law : ObservedLaw) :
      (∫ data, (∫ u, φ.1.1 (data,u) ∂design) ∂Measure.pi (fun _ : Fin n => law.P)) =
        rejectProb n law.P φ.1 := by
    symm
    apply integral_prod
    apply Integrable.of_bound φ.1.2.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (φ.1.2.2 z).1]
      exact (φ.1.2.2 z).2)
  rw [hex P0, hex P1] at htv
  have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} =>
      1-rejectProb n law.1.P φ.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law,rfl⟩
    linarith [(rejectProb_bounds n law.1 φ.1).1]
  have herr := le_ciSup hb ⟨P1,h1,hr⟩
  have hsize := φ.2 P0 h0
  have hgap := (abs_le.mp htv).1
  simp only [mul_one] at hgap
  linarith

/-- At each fixed sample size a nonempty binary cosine alternative forces a positive radius. This statement assumes [the hn condition](hyp:hn), [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: binaryCriticalRadius_pos
lemma binaryCriticalRadius_pos (n : ℕ) (hn : 2 ≤ n) (w : Smooth3) (hw : w.Valid) :
    0 < binaryCriticalRadius n w := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  let t : ℝ := 8/(100*(n:ℝ))
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    refine ⟨htpos.le, ?_⟩
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 100*(n:ℝ))).2
    linarith
  have h0 := smallCosineLaw_inBinaryNull w hw
  have h1 := smallCosineLaw_inBinaryModel w hw t ht
  have hd := smallCosineLaw_distance t ht
  have hd0 : 0 < d0 := by unfold d0; positivity
  have hD : d0 ≤ maxDistBinary w := by
    rw [maxDistBinary_eq_maxDistBounded]
    change d0 ≤ maxDistBounded (Params.ofBounded w).toSmooth3
    rw [maxDistBounded_eq_maxDist]
    exact model_distance_lower _ ⟨by norm_num [Params.ofBounded], hw⟩
  have htv : Causalean.Stat.tvDist (Measure.pi fun _ : Fin n => (smallCosineLaw 0).P)
      (Measure.pi fun _ : Fin n => (smallCosineLaw t).P) ≤ 1/200 := by
    calc
      _ ≤ (n:ℝ)*Causalean.Stat.tvDist (smallCosineLaw 0).P (smallCosineLaw t).P :=
        Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le n _ _
      _ ≤ (n:ℝ)*(t/16) := mul_le_mul_of_nonneg_left (smallCosineLaw_tv t ht) (by positivity)
      _ = 1/200 := by dsimp [t]; field_simp; ring
  have hfailed (r : ℝ) (hr : r ≤ t*d0) : 1/10 < binaryTestingRisk n w r := by
    have h := testingRiskOn_ge_of_two_point n {law | InBinaryNull w law}
      {law | InBinaryModel w law} r (smallCosineLaw 0) (smallCosineLaw t) h0 h1 (by simpa [hd] using hr)
    change 1/10 < testingRiskOn n r {law | InBinaryNull w law} {law | InBinaryModel w law}
    linarith
  have hradius : t*d0 ≤ binaryCriticalRadius n w := by
    unfold binaryCriticalRadius cappedRadius
    apply le_csInf ⟨maxDistBinary w, Or.inr (Set.mem_singleton _)⟩
    intro r hr
    rcases hr with hr | hr
    · by_contra h
      have hh := hfailed r (le_of_not_ge h)
      exact (not_le_of_gt hh) hr.2.2
    · rw [Set.mem_singleton_iff.mp hr]
      exact (mul_le_of_le_one_left hd0.le ht.2).trans hD
  exact (mul_pos htpos hd0).trans_le hradius

end CausalSmith.Stat.FinitepHomogeneityDensegamma
