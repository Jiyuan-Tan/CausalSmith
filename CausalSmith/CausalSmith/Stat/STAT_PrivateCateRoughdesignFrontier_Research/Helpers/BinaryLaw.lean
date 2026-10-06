module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
/-! Uniform-design binary causal laws and their conditional regression identities. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The binary probability mass is the specified success probability for one and its complement
for zero. -/
def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

/-- A valid Bernoulli parameter gives nonnegative mass to either binary outcome.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:p,hp,z). -/
-- @node: bernoulliMass_nonneg
lemma bernoulliMass_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (z : Bool) :
    0 ≤ bernoulliMass p z := by
  cases z <;> simp only [bernoulliMass, Bool.false_eq_true, if_false, if_true]
  · linarith [hp.2]
  · exact hp.1

/-- The two nonnegative Bernoulli masses add to one in extended real arithmetic.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:p,hp). -/
-- @node: bernoulliMass_sum
lemma bernoulliMass_sum {p : ℝ} (hp : p ∈ Icc 0 1) :
    ∑ z : Bool, ENNReal.ofReal (bernoulliMass p z) = 1 := by
  rw [Fintype.sum_bool, ← ENNReal.ofReal_add
    (bernoulliMass_nonneg hp true) (bernoulliMass_nonneg hp false)]
  simp [bernoulliMass]

/-- Three independent valid Bernoulli masses have unit total mass.  [the theorem's stated inputs and assumptions](hyp:hb,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,b,c,ha). -/
-- @node: bernoulliTripleMass_sum
lemma bernoulliTripleMass_sum {a b c : ℝ} (ha : a ∈ Icc 0 1)
    (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    ∑ z : Bool × Bool × Bool,
      ENNReal.ofReal (bernoulliMass a z.1 * bernoulliMass b z.2.1 *
        bernoulliMass c z.2.2) = 1 := by
  have hn (z : Bool × Bool × Bool) :
      ENNReal.ofReal (bernoulliMass a z.1 * bernoulliMass b z.2.1 *
        bernoulliMass c z.2.2) =
      ENNReal.ofReal (bernoulliMass a z.1) *
        ENNReal.ofReal (bernoulliMass b z.2.1) *
        ENNReal.ofReal (bernoulliMass c z.2.2) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (bernoulliMass_nonneg ha _)
      (bernoulliMass_nonneg hb _)),
      ENNReal.ofReal_mul (bernoulliMass_nonneg ha _)]
  simp_rw [hn, Fintype.sum_prod_type, ← Finset.mul_sum,
    bernoulliMass_sum hc, mul_one, ← Finset.mul_sum,
    bernoulliMass_sum hb, mul_one, bernoulliMass_sum ha]

/-- A uniform covariate draw is followed by independent Bernoulli treatment and potential outcomes
and the consistency observation map. -/
def binaryLaw (a b c : Covariate → ℝ) : Measure Record :=
  (volume : Measure Covariate).bind (fun x =>
    ∑ z : Bool × Bool × Bool,
      ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
        bernoulliMass (c x) z.2.2) •
      Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1))

variable (a b c : Covariate → ℝ) (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
  (hr : ∀ x, a x ∈ Icc 0 1 ∧ b x ∈ Icc 0 1 ∧ c x ∈ Icc 0 1)
include ha hb hc in
/-- The finite conditional Bernoulli record law varies measurably with the covariate.  [the asserted conclusion follows](goal). -/
-- @node: measurable_binaryRecordLaw
lemma measurable_binaryRecordLaw : Measurable (fun x : Covariate =>
    ∑ z : Bool × Bool × Bool,
      ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
        bernoulliMass (c x) z.2.2) •
      Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_fun_sum
  intro z hz
  apply Measurable.mul
  · unfold bernoulliMass
    cases z.1 <;> cases z.2.1 <;> cases z.2.2 <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> fun_prop
  · exact (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (by fun_prop))

include ha hb hc hr in
/-- The finite Bernoulli construction is a probability law for measurable probability-valued
parameters.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_probability
lemma binaryLaw_probability : IsProbabilityMeasure (binaryLaw a b c) := by
  rw [isProbabilityMeasure_iff, binaryLaw, Measure.bind_apply MeasurableSet.univ]
  · have hm : ∀ x : Covariate,
        (∑ z : Bool × Bool × Bool,
          ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
            bernoulliMass (c x) z.2.2) •
          Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1))
          Set.univ = 1 := by
      intro x
      simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
        (Set.mem_univ _), smul_eq_mul, mul_one]
      exact bernoulliTripleMass_sum (hr x).1 (hr x).2.1 (hr x).2.2
    simp_rw [hm]
    simp
  · exact (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable
include ha hb hc hr in
/-- The finite Bernoulli construction has the uniform design density.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_design
lemma binaryLaw_design :
    (binaryLaw a b c).map X = volume := by
  classical
  ext s hs
  rw [Measure.map_apply measurable_X hs, binaryLaw,
    Measure.bind_apply (measurable_X hs)
      (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable]
  have hm : ∀ x : Covariate,
      (∑ z : Bool × Bool × Bool,
        ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
          bernoulliMass (c x) z.2.2) •
        Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1))
        (X ⁻¹' s) = s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurable_X hs), Set.indicator_apply,
      Set.mem_preimage, X, smul_eq_mul, Pi.one_apply]
    change (∑ z : Bool × Bool × Bool,
      ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
        bernoulliMass (c x) z.2.2) * (if x ∈ s then 1 else 0)) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) x
    by_cases hx : x ∈ s
    · simp only [hx, if_true, mul_one, Set.indicator_of_mem hx]
      exact bernoulliTripleMass_sum (hr x).1 (hr x).2.1 (hr x).2.2
    · simp [hx]
  simp_rw [hm]
  simp [hs]
include ha hb hc hr in
/-- The uniform design has the selected constant density one. [The displayed conclusion](goal) follows. -/
-- @node: binaryLaw_density_version
lemma binaryLaw_density_version : (binaryLaw a b c).map X ≪ volume →
    (binaryLaw a b c).map X = volume.withDensity (fun _ => ENNReal.ofReal (1 : ℝ)) := by
  intro _
  simpa using binaryLaw_design a b c ha hb hc hr
include ha hb hc hr in
/-- The selected propensity is integrable under the constructed design marginal.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_e_integrable
lemma binaryLaw_e_integrable : Integrable a ((binaryLaw a b c).map X) := by
  let := binaryLaw_probability a b c ha hb hc hr
  apply Integrable.of_mem_Icc 0 1 (by fun_prop)
  exact ae_of_all _ (fun x => (hr x).1)
include ha hb hc hr in
/-- The selected control mean is integrable under the constructed control-arm covariate measure.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_mu0_integrable
lemma binaryLaw_mu0_integrable :
    Integrable b (((binaryLaw a b c).restrict {z | A z = false}).map X) := by
  let := binaryLaw_probability a b c ha hb hc hr
  apply Integrable.of_mem_Icc 0 1 (by fun_prop)
  exact ae_of_all _ (fun x => (hr x).2.1)
include ha hb hc hr in
/-- The selected treated mean is integrable under the constructed treated-arm covariate measure.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_mu1_integrable
lemma binaryLaw_mu1_integrable :
    Integrable c (((binaryLaw a b c).restrict {z | A z = true}).map X) := by
  let := binaryLaw_probability a b c ha hb hc hr
  apply Integrable.of_mem_Icc 0 1 (by fun_prop)
  exact ae_of_all _ (fun x => (hr x).2.2)
include ha hb hc hr in
/-- The constructed propensity satisfies the conditional probability identity on every measurable
covariate set.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_e_version
lemma binaryLaw_e_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, a x ∂((binaryLaw a b c).map X) =
      (binaryLaw a b c).real {z | X z ∈ s ∧ A z = true} := by
  classical
  intro s hs
  have hset : MeasurableSet {z : Record | X z ∈ s ∧ A z = true} := by
    apply MeasurableSet.inter (measurable_X hs)
    exact measurableSet_eq_fun (by unfold A; fun_prop) measurable_const
  rw [binaryLaw_design a b c ha hb hc hr,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => (hr x).1.1))
      ha.aestronglyMeasurable, measureReal_def, binaryLaw,
    Measure.bind_apply hset (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable]
  congr 1
  have hm : ∀ x : Covariate,
      (∑ z : Bool × Bool × Bool,
        ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
          bernoulliMass (c x) z.2.2) •
        Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1))
        {z | X z ∈ s ∧ A z = true} =
      s.indicator (fun x => ENNReal.ofReal (a x)) x := by
    intro x
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hset, smul_eq_mul]
    by_cases hx : x ∈ s
    · have ha0 := (hr x).1.1
      have hb0 := (hr x).2.1.1
      have hc0 := (hr x).2.2.1
      have hb1 : 0 ≤ 1 - b x := sub_nonneg.mpr (hr x).2.1.2
      have hc1 : 0 ≤ 1 - c x := sub_nonneg.mpr (hr x).2.2.2
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliMass, X, A,
        Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq,
        hx, Bool.false_eq_true, and_false, and_true, if_true, if_false,
        Set.indicator_of_mem hx, mul_one, mul_zero, add_zero, zero_add,
        Set.mem_setOf_eq]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    · simp [X, A, hx, Set.indicator_of_notMem hx]
  simp_rw [hm]
  rw [lintegral_indicator hs]
include ha hb hc in
/-- Integration under the generated record law is integration of the finite conditional masses.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:f,hf). -/
-- @node: binaryLaw_lintegral
lemma binaryLaw_lintegral (f : Record → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂binaryLaw a b c =
      ∫⁻ x : Covariate, ∑ z : Bool × Bool × Bool,
        ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
          bernoulliMass (c x) z.2.2) *
        f (x, z.1, (z.2.1, z.2.2), if z.1 then z.2.2 else z.2.1) := by
  rw [binaryLaw, Measure.lintegral_bind
    (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable hf.aemeasurable]
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

include ha hb hc hr in
/-- In each arm, the conditional mean of the observed binary response is its Bernoulli parameter.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:arm,s,hs). -/
-- @node: binaryLaw_arm_version
lemma binaryLaw_arm_version (arm : Bool) (s : Set Covariate) (hs : MeasurableSet s) :
    ∫ x in s, (if arm then c x else b x)
        ∂(((binaryLaw a b c).restrict {z | A z = arm}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = arm}, bit (Y z) ∂binaryLaw a b c := by
  classical
  have hm : Measurable (fun x => if arm then c x else b x) := by
    cases arm <;> simp <;> fun_prop
  have ht : MeasurableSet {z : Record | A z = arm} := by
    exact measurableSet_eq_fun (by unfold A; fun_prop) measurable_const
  have hset : MeasurableSet {z : Record | X z ∈ s ∧ A z = arm} :=
    (measurable_X hs).inter ht
  rw [setIntegral_map hs hm.aestronglyMeasurable measurable_X.aemeasurable,
    Measure.restrict_restrict (measurable_X hs)]
  change (∫ z in {z | X z ∈ s ∧ A z = arm}, (if arm then c (X z) else b (X z))
    ∂binaryLaw a b c) = _
  have hmy : Measurable (fun z : Record => bit (Y z)) := by
    exact (by fun_prop : Measurable bit).comp (by unfold Y; fun_prop)
  have hmf : Measurable (fun z : Record => if arm then c (X z) else b (X z)) :=
    hm.comp measurable_X
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z => by
      cases arm
      · exact (hr (X z)).2.1.1
      · exact (hr (X z)).2.2.1))
    hmf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun z => by unfold bit; split <;> norm_num))
      hmy.aestronglyMeasurable,
    ← lintegral_indicator hset, ← lintegral_indicator hset]
  congr 1
  rw [binaryLaw_lintegral a b c ha hb hc
      (fun z => {z | X z ∈ s ∧ A z = arm}.indicator
        (fun z => ENNReal.ofReal (if arm then c (X z) else b (X z))) z)
      (by simpa only [Function.comp_def] using
        (ENNReal.measurable_ofReal.comp hmf).indicator hset),
    binaryLaw_lintegral a b c ha hb hc
      (fun z => {z | X z ∈ s ∧ A z = arm}.indicator
        (fun z => ENNReal.ofReal (bit (Y z))) z)
      (by simpa only [Function.comp_def] using
        (ENNReal.measurable_ofReal.comp hmy).indicator hset)]
  apply lintegral_congr
  intro x
  have ha0 := (hr x).1.1
  have hb0 := (hr x).2.1.1
  have hc0 := (hr x).2.2.1
  have ha1 : 0 ≤ 1 - a x := sub_nonneg.mpr (hr x).1.2
  have hb1 : 0 ≤ 1 - b x := sub_nonneg.mpr (hr x).2.1.2
  have hc1 : 0 ≤ 1 - c x := sub_nonneg.mpr (hr x).2.2.2
  by_cases hx : x ∈ s
  · cases arm <;>
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator_apply,
        Set.mem_setOf_eq, bernoulliMass, X, A, Y, bit, hx, and_true, and_false,
        Bool.false_eq_true, if_true, if_false, ENNReal.ofReal_one, ENNReal.ofReal_zero,
        mul_one, mul_zero, zero_add, add_zero]
    all_goals
      try simp only [Bool.true_eq_false, and_false, if_false, mul_zero, zero_add]
      repeat rw [← ENNReal.ofReal_mul (by positivity)]
      repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
  · simp [Set.indicator_apply, X, A, hx]

include ha hb hc hr in
/-- The constructed control regression satisfies the conditional mean identity on every measurable
covariate set.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_mu0_version
lemma binaryLaw_mu0_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, b x ∂(((binaryLaw a b c).restrict {z | A z = false}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = false}, bit (Y z) ∂binaryLaw a b c := by
  intro s hs
  exact binaryLaw_arm_version a b c ha hb hc hr false s hs
include ha hb hc hr in
/-- The constructed treated regression satisfies the conditional mean identity on every measurable
covariate set.  [the asserted conclusion follows](goal). -/
-- @node: binaryLaw_mu1_version
lemma binaryLaw_mu1_version : ∀ s : Set Covariate, MeasurableSet s →
    ∫ x in s, c x ∂(((binaryLaw a b c).restrict {z | A z = true}).map X) =
      ∫ z in {z | X z ∈ s ∧ A z = true}, bit (Y z) ∂binaryLaw a b c := by
  intro s hs
  exact binaryLaw_arm_version a b c ha hb hc hr true s hs

/-- The finite Bernoulli product followed by consistency gives a concrete causal-law bundle. -/
def binaryCausalLaw : CausalLaw where
  law := binaryLaw a b c
  probability := binaryLaw_probability a b c ha hb hc hr
  f := fun _ => 1
  e := a
  mu0 := b
  mu1 := c
  f_measurable := measurable_const
  e_measurable := ha
  mu0_measurable := hb
  mu1_measurable := hc
  density_version := binaryLaw_density_version a b c ha hb hc hr
  e_integrable := binaryLaw_e_integrable a b c ha hb hc hr
  mu0_integrable := binaryLaw_mu0_integrable a b c ha hb hc hr
  mu1_integrable := binaryLaw_mu1_integrable a b c ha hb hc hr
  e_version := binaryLaw_e_version a b c ha hb hc hr
  mu0_version := binaryLaw_mu0_version a b c ha hb hc hr
  mu1_version := binaryLaw_mu1_version a b c ha hb hc hr

include ha hb hc hr in
/-- Every generated record uses the potential outcome selected by its treatment.  [the asserted conclusion follows](goal). -/
-- @node: binaryCausalLaw_consistency
lemma binaryCausalLaw_consistency : Consistency (binaryCausalLaw a b c ha hb hc hr) := by
  classical
  change ∀ᵐ z ∂binaryLaw a b c, Y z = if A z then (Ypot z).2 else (Ypot z).1
  rw [ae_iff]
  have hs : MeasurableSet {z : Record | ¬ (Y z = if A z then (Ypot z).2 else (Ypot z).1)} := by
    have hA : Measurable A := by unfold A; fun_prop
    have hY : Measurable Y := by unfold Y; fun_prop
    have hp0 : Measurable (fun z => (Ypot z).1) := by unfold Ypot; fun_prop
    have hp1 : Measurable (fun z => (Ypot z).2) := by unfold Ypot; fun_prop
    exact (measurableSet_eq_fun hY
      (hp1.ite (measurableSet_eq_fun hA measurable_const) hp0)).compl
  rw [binaryLaw, Measure.bind_apply hs
    (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable]
  have hf : ∀ x : Covariate,
      (∑ z : Bool × Bool × Bool,
        ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
          bernoulliMass (c x) z.2.2) •
        Measure.dirac (x, z.1, (z.2.1,z.2.2), if z.1 then z.2.2 else z.2.1))
        {z : Record | ¬ (Y z = if A z then (Ypot z).2 else (Ypot z).1)} = 0 := by
    intro x
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro z hz
    rw [Measure.dirac_apply' _ hs]
    simp only [Set.mem_setOf_eq, Y, A, Ypot]
    simp
    exact Or.inr rfl
  simp_rw [hf]
  simp

include ha hb hc hr in
/-- The constructed law's selected density is one and its design is exactly uniform. [The displayed conclusion](goal) follows. -/
-- @node: binaryCausalLaw_densityBounds
lemma binaryCausalLaw_densityBounds : DensityBounds (binaryCausalLaw a b c ha hb hc hr) := by
  constructor
  · change (binaryLaw a b c).map X ≪ volume
    rw [binaryLaw_design a b c ha hb hc hr]
  · filter_upwards with x
    change (1 / 2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 3 / 2
    norm_num

include ha hb hc hr in
/-- Analytic regularity and conditional exchangeability complete the binary law's model
certificate; consistency and the uniform density follow from its construction. The result uses [the stated assumptions](hyp:hex,hov,haH,hbH,htL) and establishes [the displayed conclusion](goal). -/
-- @node: binaryCausalLaw_completeModel
lemma binaryCausalLaw_completeModel
    (hex : Exchangeability (binaryCausalLaw a b c ha hb hc hr))
    (hov : ∀ x, 1 / 4 ≤ a x ∧ a x ≤ 3 / 4)
    (haH : ∀ x y, |a x - a y| ≤ L * |(x : ℝ) - y| ^ (1/10 : ℝ))
    (hbH : ∀ x y, |b x - b y| ≤ L * |(x : ℝ) - y| ^ (1/10 : ℝ))
    (htL : ∀ x y, |(c x - b x) - (c y - b y)| ≤ L * |(x : ℝ) - y|) :
    CompleteModel (binaryCausalLaw a b c ha hb hc hr) := by
  exact ⟨binaryCausalLaw_consistency a b c ha hb hc hr, hex,
    binaryCausalLaw_densityBounds a b c ha hb hc hr, hov, haH, hbH, htL⟩

/-- An observed event under the binary construction integrates the four conditional mark
masses; the unused potential outcome sums out exactly.  [the theorem's stated inputs and assumptions](hyp:hb,hc,hr,s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,b,c,ha). -/
-- @node: binaryCausalLaw_observed_apply
lemma binaryCausalLaw_observed_apply (a b c : Covariate → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ x, a x ∈ Icc 0 1 ∧ b x ∈ Icc 0 1 ∧ c x ∈ Icc 0 1)
    (s : Set O) (hs : MeasurableSet s) :
    Pobs (binaryCausalLaw a b c ha hb hc hr) s =
      ∫⁻ x : Covariate, ∑ z : Bool × Bool,
        ENNReal.ofReal (bernoulliMass (a x) z.1 *
          bernoulliMass (if z.1 then c x else b x) z.2) *
        s.indicator (fun _ => (1 : ℝ≥0∞)) (x, z.1, z.2) := by
  classical
  have hm : Measurable observe := by unfold observe X A Y; fun_prop
  change (binaryLaw a b c).map observe s = _
  rw [Measure.map_apply hm hs, ← lintegral_indicator_one (hm hs)]
  rw [binaryLaw_lintegral a b c ha hb hc ((observe ⁻¹' s).indicator (1 : Record → ℝ≥0∞))
    (measurable_const.indicator (hm hs))]
  apply lintegral_congr
  intro x
  have ha0 := (hr x).1.1
  have hb0 := (hr x).2.1.1
  have hc0 := (hr x).2.2.1
  have ha1 : 0 ≤ 1 - a x := sub_nonneg.mpr (hr x).1.2
  have hb1 : 0 ≤ 1 - b x := sub_nonneg.mpr (hr x).2.1.2
  have hc1 : 0 ≤ 1 - c x := sub_nonneg.mpr (hr x).2.2.2
  have hmass (av yv : Bool) :
      (∑ z : Bool,
        ENNReal.ofReal (bernoulliMass (a x) av * bernoulliMass (b x) z *
          bernoulliMass (c x) yv)) =
        ENNReal.ofReal (bernoulliMass (a x) av * bernoulliMass (c x) yv) := by
    cases av <;> cases yv <;>
      simp only [Fintype.sum_bool, bernoulliMass, Bool.false_eq_true, if_true, if_false] <;>
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)] <;> congr 1 <;> ring
  have hmass' (av yv : Bool) :
      (∑ z : Bool,
        ENNReal.ofReal (bernoulliMass (a x) av * bernoulliMass (b x) yv *
          bernoulliMass (c x) z)) =
        ENNReal.ofReal (bernoulliMass (a x) av * bernoulliMass (b x) yv) := by
    cases av <;> cases yv <;>
      simp only [Fintype.sum_bool, bernoulliMass, Bool.false_eq_true, if_true, if_false] <;>
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)] <;> congr 1 <;> ring
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator_apply,
    Set.mem_preimage, observe, X, A, Y, Bool.false_eq_true, if_false, if_true, Pi.one_apply]
  have ht := hmass true true
  have ht' := hmass true false
  have hf := hmass' false true
  have hf' := hmass' false false
  simp only [Fintype.sum_bool, bernoulliMass, if_true, Bool.false_eq_true, if_false] at ht ht' hf hf'
  simp only [bernoulliMass, if_true, Bool.false_eq_true, if_false]
  calc
    _ = (ENNReal.ofReal (a x * b x * c x) + ENNReal.ofReal (a x * (1-b x) * c x)) *
          (if (x, true, true) ∈ s then 1 else 0) +
        (ENNReal.ofReal (a x * b x * (1-c x)) + ENNReal.ofReal (a x * (1-b x) * (1-c x))) *
          (if (x, true, false) ∈ s then 1 else 0) +
        (ENNReal.ofReal ((1-a x) * b x * c x) + ENNReal.ofReal ((1-a x) * b x * (1-c x))) *
          (if (x, false, true) ∈ s then 1 else 0) +
        (ENNReal.ofReal ((1-a x) * (1-b x) * c x) +
          ENNReal.ofReal ((1-a x) * (1-b x) * (1-c x))) *
          (if (x, false, false) ∈ s then 1 else 0) := by ring
    _ = _ := by rw [ht, ht', hf, hf']; ring

/-- Coordinatewise measure domination is preserved by a finite product.  [the theorem's stated inputs and assumptions](hyp:μ,ν,hle), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finite_product_measure_mono
lemma finite_product_measure_mono {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ ν : ∀ i, Measure (α i))
    (hle : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs,
    toMeasure_apply _ _ hs]
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro t _ht
    exact (OuterMeasure.pi_pi_le _ _).trans
      (Finset.prod_le_prod' (fun i _ => hle i (t i)))
  exact ho s

/-- A common finite domination factor becomes its nth power for an n-record experiment.  [the theorem's stated inputs and assumptions](hyp:μ,ν,c,hle), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,α). -/
-- @node: finite_product_measure_domination
lemma finite_product_measure_domination (n : ℕ) {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite ν] (c : ℝ≥0∞) [SigmaFinite (c • ν)]
    (hle : μ ≤ c • ν) :
    Measure.pi (fun _ : Fin n => μ) ≤ c ^ n • Measure.pi (fun _ : Fin n => ν) := by
  have heq : Measure.pi (fun _ : Fin n => c • ν) =
      c ^ n • Measure.pi (fun _ : Fin n => ν) := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    simp
  rw [← heq]
  exact finite_product_measure_mono _ _ (fun _ => hle)

/-- Every probability-valued binary construction is dominated by eight times the fair
full-record law.  [the theorem's stated inputs and assumptions](hyp:hb,hc,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,b,c,ha). -/
-- @node: binaryLaw_fair_domination
lemma binaryLaw_fair_domination (a b c : Covariate → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ x, a x ∈ Icc 0 1 ∧ b x ∈ Icc 0 1 ∧ c x ∈ Icc 0 1) :
    binaryLaw a b c ≤ (8 : ℝ≥0∞) • binaryLaw (fun _ => 1/2) (fun _ => 1/2) (fun _ => 1/2) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [binaryLaw, Measure.bind_apply hs
    (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable,
    Measure.smul_apply, binaryLaw, Measure.bind_apply hs
    (measurable_binaryRecordLaw _ _ _ measurable_const measurable_const measurable_const).aemeasurable,
    smul_eq_mul, ← lintegral_const_mul' _ _ (by norm_num : (8 : ℝ≥0∞) ≠ ∞)]
  apply lintegral_mono
  intro x
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hp (p : ℝ) (hp : p ∈ Icc 0 1) (v : Bool) : bernoulliMass p v ≤ 1 := by
    cases v <;> simp [bernoulliMass] <;> linarith [hp.1, hp.2]
  have hm : bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
      bernoulliMass (c x) z.2.2 ≤ 1 := by
    exact mul_le_one₀
      (mul_le_one₀ (hp _ (hr x).1 _) (bernoulliMass_nonneg (hr x).2.1 _)
        (hp _ (hr x).2.1 _)) (bernoulliMass_nonneg (hr x).2.2 _)
      (hp _ (hr x).2.2 _)
  have hmass : ENNReal.ofReal (bernoulliMass (a x) z.1 * bernoulliMass (b x) z.2.1 *
      bernoulliMass (c x) z.2.2) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hm
  have hf (v : Bool) : bernoulliMass (1/2) v = 1/2 := by cases v <;> norm_num [bernoulliMass]
  simp only [hf]
  rw [← mul_assoc]
  have hfair : (8 : ℝ≥0∞) * ENNReal.ofReal ((1/2 : ℝ) * (1/2) * (1/2)) = 1 := by
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  rw [hfair]
  exact mul_le_mul' hmass le_rfl

/-- Finite domination makes the squared density deviation integrable under a finite reference law.  [the theorem's stated inputs and assumptions](hyp:μ,ν,c,hc0,hct,hle), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: square_rnDeriv_integrable_of_domination
lemma square_rnDeriv_integrable_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure ν] (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hle : μ ≤ c • ν) :
    Integrable (fun z => ((μ.rnDeriv ν z).toReal - 1)^2) ν := by
  letI : IsFiniteMeasure (c • ν) := Measure.smul_finite ν hct
  letI : IsFiniteMeasure μ := isFiniteMeasure_of_le (c • ν) hle
  have hsmall : μ.rnDeriv (c • ν) ≤ᵐ[ν] 1 :=
    (Measure.absolutelyContinuous_smul hc0).ae_le (Measure.rnDeriv_le_one_of_le hle)
  have hscale := Measure.rnDeriv_smul_right_of_ne_top μ ν hc0 hct
  have hbound : ∀ᵐ z ∂ν, (μ.rnDeriv ν z).toReal ≤ c.toReal := by
    filter_upwards [hsmall, hscale] with z hz hs
    rw [hs, Pi.smul_apply, smul_eq_mul] at hz
    have hz' : μ.rnDeriv ν z ≤ c := by
      calc
        _ = c * (c⁻¹ * μ.rnDeriv ν z) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
        _ ≤ c * 1 := mul_le_mul' le_rfl hz
        _ = c := mul_one _
    exact ENNReal.toReal_mono hct hz'
  apply Integrable.of_mem_Icc 0 ((c.toReal + 1)^2) (by fun_prop)
  filter_upwards [hbound] with z hz
  have hn := ENNReal.toReal_nonneg (a := μ.rnDeriv ν z)
  have hc := ENNReal.toReal_nonneg (a := c)
  constructor
  · exact sq_nonneg _
  · nlinarith

end CausalSmith.Stat.PrivateCateRoughdesign
