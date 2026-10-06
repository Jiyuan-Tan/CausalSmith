module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Completion
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CompletionEffect
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CompletionObservation
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.VersionInvariance
public import Causalean.Mathlib.MeasureTheory.UnitInterval.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Deterministic nonemptiness witnesses and analytic effect-distance bounds.
Continuous version invariance, the observed marginal, potential integrability,
and the conditional effect are proved. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Deterministicarm: the displayed mathematical construction or bound. This statement assumes [the m parameter](hyp:m). [This is the stated defined object](goal). -/
def deterministicArm (m : Nuisance) : Kernel unitInterval ℝ := Kernel.deterministic m m.continuous.measurable
/-- Literal deterministic arm kernels for the two public nonemptiness witnesses. This statement assumes [the e parameter](hyp:e), [the m0 parameter](hyp:m0), [the τ parameter](hyp:τ). [This is the stated defined object](goal). -/
def deterministicRecord (e m0 τ : Nuisance) : Measure Record :=
  design ⊗ₘ recordKernel e e.continuous.measurable (fun a => (if a then deterministicArm (m0+τ) else deterministicArm m0))
/-- The literal finite-kernel constructor has normalized probability laws and the stated original conditional means. This statement assumes [the he condition](hyp:he). [This is the stated conclusion](goal). -/
-- @node: deterministic_certificate
lemma deterministic_certificate (e m0 τ : Nuisance) (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    IsProbabilityMeasure (deterministicRecord e m0 τ) ∧
    deterministicRecord e m0 τ = ((deterministicRecord e m0 τ).map X) ⊗ₘ recordKernel e e.continuous.measurable
      (fun a => (if a then deterministicArm (m0+τ) else deterministicArm m0)) ∧
    (∀ a : Bool, IsMarkovKernel ((if a then deterministicArm (m0+τ) else deterministicArm m0))) ∧
    (∀ᵐ x ∂design, m0 x = ∫ y, y ∂deterministicArm m0 x) ∧
    (∀ᵐ x ∂design, m0 x+τ x = ∫ y, y ∂deterministicArm (m0+τ) x) := by
  let Q : Bool → Kernel unitInterval ℝ := fun a =>
    if a then deterministicArm (m0+τ) else deterministicArm m0
  have hQ : ∀ a, IsMarkovKernel (Q a) := by
    intro a
    cases a <;> dsimp [Q, deterministicArm] <;> infer_instance
  letI : ∀ a, IsMarkovKernel (Q a) := hQ
  let κ := recordKernel e e.continuous.measurable Q
  have hκ : IsMarkovKernel κ := by
    constructor
    intro x
    constructor
    change (recordMeasure e Q x) Set.univ = 1
    simp only [recordMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.prod_prod, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (he x).1 (sub_nonneg.mpr (he x).2)]
    norm_num
  letI : IsMarkovKernel κ := hκ
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  have hprob : IsProbabilityMeasure (deterministicRecord e m0 τ) := by
    change IsProbabilityMeasure (design ⊗ₘ κ)
    infer_instance
  have hmap : (deterministicRecord e m0 τ).map X = design := by
    change (design ⊗ₘ κ).fst = design
    exact Measure.fst_compProd design κ
  refine ⟨hprob, ?_, hQ, ?_, ?_⟩
  · rw [hmap]
    rfl
  · filter_upwards [] with x
    simp [deterministicArm, Kernel.deterministic]
  · filter_upwards [] with x
    simp [deterministicArm, Kernel.deterministic]
/-- Deterministiclaw: the displayed mathematical construction or bound. This statement assumes [the e parameter](hyp:e), [the m0 parameter](hyp:m0), [the τ parameter](hyp:τ). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def deterministicLaw (e m0 τ : Nuisance) : ObservedLaw :=
  if h : ∀ x, 0 ≤ e x ∧ e x ≤ 1 then
    let cert := deterministic_certificate e m0 τ h
    { P := deterministicRecord e m0 τ
      probability := cert.1
      e := e
      e_range := h
      Q := fun a => (if a then deterministicArm (m0+τ) else deterministicArm m0)
      markov := cert.2.2.1
      m0 := m0
      tau := τ
      record_version := cert.2.1
      mean0_version := cert.2.2.2.1
      mean1_version := cert.2.2.2.2 }
  else referenceLaw
/-- The specified finite construction is continuous on its covariate domain. [This is the stated conclusion](goal). -/
-- @node: continuous_witness_propensity
@[fun_prop] lemma continuous_witness_propensity : Continuous (fun x : unitInterval => (1/2:ℝ)+Real.sin (2*Real.pi*(x:ℝ))/10) := by
  fun_prop
/-- The specified finite construction is continuous on its covariate domain. [This is the stated conclusion](goal). -/
-- @node: continuous_witness_cos
@[fun_prop] lemma continuous_witness_cos : Continuous (fun x : unitInterval => Real.cos (2*Real.pi*(x:ℝ))/8) := by
  fun_prop
/-- Witnessprop: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def witnessProp : Nuisance := ⟨fun x => 1/2+Real.sin (2*Real.pi*(x:ℝ))/10,continuous_witness_propensity⟩
/-- Witnesscos: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def witnessCos : Nuisance := ⟨fun x => Real.cos (2*Real.pi*(x:ℝ))/8,continuous_witness_cos⟩
/-- Separatedwitness: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def separatedWitness : ObservedLaw := deterministicLaw witnessProp witnessCos witnessCos
/-- Constantwitness: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def constantWitness : ObservedLaw := deterministicLaw witnessProp witnessCos (ContinuousMap.const unitInterval (1/8))
/-- The witness propensity stays strictly inside the overlap interval. [This is the stated conclusion](goal). -/
-- @node: witnessProp_overlap
lemma witnessProp_overlap (x : unitInterval) :
    1/4 ≤ witnessProp x ∧ witnessProp x ≤ 3/4 := by
  change 1/4 ≤ 1/2+Real.sin (2*Real.pi*(x:ℝ))/10 ∧
    1/2+Real.sin (2*Real.pi*(x:ℝ))/10 ≤ 3/4
  constructor <;> linarith [Real.neg_one_le_sin (2*Real.pi*(x:ℝ)),
    Real.sin_le_one (2*Real.pi*(x:ℝ))]

/-- The cosine witness satisfies the stricter one-eighth envelope. [This is the stated conclusion](goal). -/
-- @node: witnessCos_cap
lemma witnessCos_cap (x : unitInterval) : |witnessCos x| ≤ 1/8 := by
  change |Real.cos (2*Real.pi*(x:ℝ))/8| ≤ 1/8
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num)

/-- Unit-interval Lipschitz increments imply every lower-order Hölder bound. This statement assumes [the hs condition](hyp:hs), [the hcap condition](hyp:hcap), [the hinc condition](hyp:hinc). [This is the stated conclusion](goal). -/
-- @node: holderBall_of_unit_lipschitz
lemma holderBall_of_unit_lipschitz (f : Nuisance) (s : ℝ) (hs : s ≤ 1)
    (hcap : ∀ x, |f x| ≤ 20)
    (hinc : ∀ x z, |f x-f z| ≤ 20*|(x:ℝ)-(z:ℝ)|) : holderBall s f := by
  refine ⟨f.continuous, hcap, ?_⟩
  intro x z
  have ht : |(x:ℝ)-(z:ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, z.property.1, z.property.2]
  exact (hinc x z).trans (mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_le_one (abs_nonneg _) ht hs) (by norm_num))

/-- The sine propensity belongs to every stipulated Hölder ball. This statement assumes [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: witnessProp_holder
lemma witnessProp_holder (s : ℝ) (hs : s ≤ 1) : holderBall s witnessProp := by
  apply holderBall_of_unit_lipschitz _ _ hs
  · intro x
    rw [abs_le]
    constructor <;> linarith [(witnessProp_overlap x).1, (witnessProp_overlap x).2]
  · intro x z
    have h := Real.abs_sin_sub_sin_le (2*Real.pi*(x:ℝ)) (2*Real.pi*(z:ℝ))
    have heq : 2*Real.pi*(x:ℝ)-2*Real.pi*(z:ℝ) = 2*Real.pi*((x:ℝ)-(z:ℝ)) := by ring
    rw [heq, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at h
    change |(1/2+Real.sin (2*Real.pi*(x:ℝ))/10)-
      (1/2+Real.sin (2*Real.pi*(z:ℝ))/10)| ≤ _
    have heq' : (1/2+Real.sin (2*Real.pi*(x:ℝ))/10)-
        (1/2+Real.sin (2*Real.pi*(z:ℝ))/10) =
        (Real.sin (2*Real.pi*(x:ℝ))-Real.sin (2*Real.pi*(z:ℝ)))/10 := by ring
    rw [heq', abs_div, abs_of_pos (by norm_num : (0:ℝ) < 10)]
    nlinarith [Real.pi_lt_four, abs_nonneg ((x:ℝ)-(z:ℝ))]

/-- The cosine baseline and effect belong to every stipulated Hölder ball. This statement assumes [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: witnessCos_holder
lemma witnessCos_holder (s : ℝ) (hs : s ≤ 1) : holderBall s witnessCos := by
  apply holderBall_of_unit_lipschitz _ _ hs
  · intro x
    linarith [witnessCos_cap x]
  · intro x z
    have h := Real.abs_cos_sub_cos_le (2*Real.pi*(x:ℝ)) (2*Real.pi*(z:ℝ))
    have heq : 2*Real.pi*(x:ℝ)-2*Real.pi*(z:ℝ) = 2*Real.pi*((x:ℝ)-(z:ℝ)) := by ring
    rw [heq, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at h
    change |Real.cos (2*Real.pi*(x:ℝ))/8-Real.cos (2*Real.pi*(z:ℝ))/8| ≤ _
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
    nlinarith [Real.pi_lt_four, abs_nonneg ((x:ℝ)-(z:ℝ))]

/-- A deterministic law exposes its literal primitives whenever its propensity is legal. This statement assumes [the he condition](hyp:he). [This is the stated conclusion](goal). -/
-- @node: deterministicLaw_primitives
lemma deterministicLaw_primitives (e m0 τ : Nuisance)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    (deterministicLaw e m0 τ).e = e ∧ (deterministicLaw e m0 τ).m0 = m0 ∧
    (deterministicLaw e m0 τ).tau = τ ∧
    (deterministicLaw e m0 τ).P = deterministicRecord e m0 τ ∧
    (deterministicLaw e m0 τ).Q =
      (fun a => if a then deterministicArm (m0+τ) else deterministicArm m0) := by
  dsimp only [deterministicLaw]
  rw [dif_pos he]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Bounded primitive means give a deterministic law every required raw-moment bound. This statement assumes [the hv condition](hyp:hv), [the he condition](hyp:he), [the heH condition](hyp:heH), [the hmH condition](hyp:hmH), [the htH condition](hyp:htH), [the hmcap condition](hyp:hmcap), [the htcap condition](hyp:htcap). [This is the stated conclusion](goal). -/
-- @node: deterministicLaw_inModel
lemma deterministicLaw_inModel (v : Params) (hv : v.Valid) (e m0 τ : Nuisance)
    (he : ∀ x, 1/4 ≤ e x ∧ e x ≤ 3/4)
    (heH : holderBall v.α e) (hmH : holderBall v.β m0) (htH : holderBall v.γ τ)
    (hmcap : ∀ x, |m0 x| ≤ 1/2) (htcap : ∀ x, |τ x| ≤ 1/2) :
    InModel v (deterministicLaw e m0 τ) := by
  have her : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x => by
    constructor <;> linarith [(he x).1, (he x).2]
  obtain ⟨heq, hmeq, hteq, hP, hQ⟩ := deterministicLaw_primitives e m0 τ her
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (deterministicLaw e m0 τ).P.map X = design
    rw [hP]
    let Q : Bool → Kernel unitInterval ℝ := fun a =>
      if a then deterministicArm (m0+τ) else deterministicArm m0
    have hmarkov : ∀ a, IsMarkovKernel (Q a) := by
      intro a
      cases a <;> dsimp [Q, deterministicArm] <;> infer_instance
    letI : IsMarkovKernel (recordKernel e e.continuous.measurable Q) :=
      recordKernel_markov _ _ _ her hmarkov
    letI : IsProbabilityMeasure design :=
      (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
    exact Measure.fst_compProd design (recordKernel e e.continuous.measurable Q)
  · simpa only [Overlap, heq] using he
  · simpa only [PropensitySmooth, heq] using heH
  · simpa only [BaselineSmooth, hmeq] using hmH
  · simpa only [EffectSmooth, hteq] using htH
  · simpa only [BaselineCap, hmeq] using hmcap
  · simpa only [EffectCap, hteq] using htcap
  · intro a
    apply ae_of_all
    intro x
    rw [hQ]
    have hb : ∀ a : Bool, |(if a then (m0+τ) else m0) x| ≤ 1 := by
      intro a
      cases a
      · simpa using (hmcap x).trans (by norm_num : (1/2:ℝ) ≤ 1)
      · exact (abs_add_le _ _).trans (by linarith [hmcap x, htcap x])
    cases a
    · simp only [Bool.false_eq_true, if_false, deterministicArm,
        Kernel.deterministic_apply, lintegral_dirac]
      have h : ENNReal.ofReal (|m0 x| ^ v.p) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal
          (Real.rpow_le_one (abs_nonneg _) (by simpa using hb false)
            (by linarith [hv.1.1]))
      exact h.trans (by norm_num)
    · simp only [if_true, deterministicArm, Kernel.deterministic_apply, lintegral_dirac]
      have h : ENNReal.ofReal (|(m0+τ) x| ^ v.p) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal
          (Real.rpow_le_one (abs_nonneg _) (by simpa using hb true)
            (by linarith [hv.1.1]))
      exact h.trans (by norm_num)

/-- The specified separated witness satisfies every original primitive predicate. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: separatedWitness_inModel
lemma separatedWitness_inModel (v : Params) (hv : v.Valid) : InModel v separatedWitness := by
  apply deterministicLaw_inModel v hv witnessProp witnessCos witnessCos witnessProp_overlap
    (witnessProp_holder _ hv.2.1.2) (witnessCos_holder _ hv.2.2.1.2)
    (witnessCos_holder _ hv.2.2.2.2)
  all_goals intro x; linarith [witnessCos_cap x]

/-- Replacing the effect by one eighth gives a legal nonzero constant null. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: constantWitness_inNull
lemma constantWitness_inNull (v : Params) (hv : v.Valid) : InNull v constantWitness := by
  have htH : holderBall v.γ (ContinuousMap.const unitInterval (1/8:ℝ)) := by
    refine ⟨continuous_const, ?_, ?_⟩
    · intro x; norm_num
    · intro x z
      simp only [ContinuousMap.const_apply, sub_self, abs_zero]
      positivity
  have hm := deterministicLaw_inModel v hv witnessProp witnessCos
    (ContinuousMap.const unitInterval (1/8:ℝ)) witnessProp_overlap
    (witnessProp_holder _ hv.2.1.2) (witnessCos_holder _ hv.2.2.1.2) htH
    (fun x => by linarith [witnessCos_cap x]) (fun x => by norm_num)
  have her : ∀ x, 0 ≤ witnessProp x ∧ witnessProp x ≤ 1 := fun x => by
    constructor <;> linarith [(witnessProp_overlap x).1, (witnessProp_overlap x).2]
  have ht := (deterministicLaw_primitives witnessProp witnessCos
    (ContinuousMap.const unitInterval (1/8:ℝ)) her).2.2.1
  exact ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth, hm.effectSmooth,
    hm.baselineCap, hm.effectCap, hm.rawMoment, 1/8, by norm_num, by norm_num,
    fun x => by change (deterministicLaw _ _ _).tau x = _; rw [ht]; rfl⟩

/-- The baseline and effect Hölder bounds combine at their smaller exponent. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: treated_mean_holder
lemma treated_mean_holder (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (x z : unitInterval) :
    |law.m1 x-law.m1 z| ≤ 40*|(x:ℝ)-(z:ℝ)|^(min v.β v.γ) := by
  have ht : |(x:ℝ)-(z:ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, z.property.1, z.property.2]
  have hs : 0 ≤ min v.β v.γ := le_min hv.2.2.1.1.le (by linarith [hv.2.2.2.1])
  have hb := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg ((x:ℝ)-(z:ℝ))) ht hs
    (min_le_left v.β v.γ)
  have hg := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg ((x:ℝ)-(z:ℝ))) ht hs
    (min_le_right v.β v.γ)
  calc
    |law.m1 x-law.m1 z| = |(law.m0 x-law.m0 z)+(law.tau x-law.tau z)| := by
      congr 1
      simp only [ObservedLaw.m1, ContinuousMap.add_apply]
      ring
    _ ≤ |law.m0 x-law.m0 z|+|law.tau x-law.tau z| := abs_add_le _ _
    _ ≤ 40*|(x:ℝ)-(z:ℝ)|^(min v.β v.γ) := by
      linarith [hm.baselineSmooth.2.2 x z, hm.effectSmooth.2.2 x z]

/-- The effect cap bounds its design average. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: meanTau_abs_le
lemma meanTau_abs_le (law : ObservedLaw) (hc : EffectCap law) : |meanTau law| ≤ 1/2 := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hi : Integrable (fun x => law.tau x) design := by
    apply (integrable_const (1/2:ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hc x)
  calc
    |meanTau law| ≤ ∫ x, |law.tau x| ∂design := abs_integral_le_integral_abs
    _ ≤ ∫ _, (1/2:ℝ) ∂design := integral_mono hi.norm (integrable_const _) (hc)
    _ = 1/2 := by simp

/-- Squared centered effects are integrable under the probability design. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: integrable_centered_effect_sq
lemma integrable_centered_effect_sq (law : ObservedLaw) (hc : EffectCap law) :
    Integrable (fun x => (law.tau x-meanTau law)^2) design := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  apply ae_of_all
  intro x
  have hb : |law.tau x-meanTau law| ≤ 1 := by
    calc
      _ ≤ |law.tau x|+|meanTau law| := abs_sub _ _
      _ ≤ 1 := by linarith [hc x, meanTau_abs_le law hc]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (law.tau x-meanTau law), abs_nonneg (law.tau x-meanTau law)]

/-- Zero distance forces pointwise constancy by continuity and full-support design. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: hetDist_zero_iff_null
lemma hetDist_zero_iff_null (v : Params) (law : ObservedLaw) (hm : InModel v law) :
    hetDist law=0 ↔ InNull v law := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  constructor
  · intro hz
    have hint : (∫ x, (law.tau x-meanTau law)^2 ∂design) = 0 :=
      (Real.sqrt_eq_zero (integral_nonneg (fun _ => sq_nonneg _))).mp hz
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (integrable_centered_effect_sq law hm.effectCap)).mp hint
    have heq : (fun x => law.tau x) =ᵐ[design] fun _ => meanTau law := by
      filter_upwards [hae] with x hx
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
    have hall : (fun x => law.tau x) = fun _ => meanTau law :=
      Measure.eq_of_ae_eq (μ := (volume : Measure unitInterval)) heq
        law.tau.continuous continuous_const
    have hb := abs_le.mp (meanTau_abs_le law hm.effectCap)
    exact ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
      hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment,
      meanTau law, by linarith [hb.1], hb.2, fun x => congrFun hall x⟩
  · intro hnull
    obtain ⟨c, hlo, hhi, heq⟩ := hnull.nullConstancy
    have hmean : meanTau law=c := by simp [meanTau, heq]
    simp [hetDist, heq, hmean]

/-- Centering subtracts the squared average from the effect's second moment. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: centered_effect_second_moment
lemma centered_effect_second_moment (law : ObservedLaw) (hc : EffectCap law) :
    (∫ x, (law.tau x-meanTau law)^2 ∂design) =
      (∫ x, law.tau x^2 ∂design)-meanTau law^2 := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hi : Integrable (fun x => law.tau x) design := by
    apply (integrable_const (1/2:ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hc x)
  have hi2 : Integrable (fun x => law.tau x^2) design := by
    apply (integrable_const (1/4:ℝ)).mono' (by fun_prop)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := abs_le.mp (hc x)
    nlinarith
  have hpoint (x : unitInterval) : (law.tau x-meanTau law)^2 =
      law.tau x^2-(2*meanTau law)*law.tau x+meanTau law^2 := by ring
  simp_rw [hpoint]
  have hsub : Integrable (fun x => law.tau x^2-(2*meanTau law)*law.tau x) design :=
    hi2.sub (hi.const_mul (2*meanTau law))
  rw [integral_add hsub (integrable_const (meanTau law^2)),
    integral_sub hi2 (hi.const_mul (2*meanTau law)), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  unfold meanTau
  ring

/-- The model effect envelope gives the sharp universal distance cap. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: hetDist_le_half
lemma hetDist_le_half (law : ObservedLaw) (hc : EffectCap law) : hetDist law ≤ 1/2 := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hbound : (∫ x, law.tau x^2 ∂design) ≤ 1/4 := by
    calc
      _ ≤ ∫ _, (1/4:ℝ) ∂design := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _)) (integrable_const _)
        apply ae_of_all
        intro x
        have hb := abs_le.mp (hc x)
        nlinarith
      _ = 1/4 := by simp
  have hcenter : (∫ x, (law.tau x-meanTau law)^2 ∂design) ≤ (1/2:ℝ)^2 := by
    rw [centered_effect_second_moment law hc]
    nlinarith [sq_nonneg (meanTau law)]
  exact (Real.sqrt_le_iff).mpr ⟨by norm_num, hcenter⟩

/-- Every model distance is bounded above, as is the nonempty model supremum. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: model_distance_upper
lemma model_distance_upper (v : Params) (law : ObservedLaw) (hm : InModel v law) :
    BddAbove (hetDist '' {law | InModel v law}) ∧ maxDist v ≤ 1/2 := by
  have hb : ∀ r ∈ hetDist '' {law | InModel v law}, r ≤ (1/2:ℝ) := by
    rintro r ⟨P, hP, rfl⟩
    exact hetDist_le_half P hP.effectCap
  refine ⟨⟨1/2, hb⟩, csSup_le ?_ hb⟩
  exact ⟨hetDist law, law, hm, rfl⟩

/-- Integrating a real function under the design is integration from zero to one. [This is the stated conclusion](goal). -/
-- @node: design_integral_eq_interval
lemma design_integral_eq_interval (f : ℝ → ℝ) :
    (∫ x : unitInterval, f x ∂design) = ∫ x in (0:ℝ)..1, f x := by
  change (∫ x : unitInterval, f x) = _
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- The displayed cosine has zero average over a complete period. [This is the stated conclusion](goal). -/
-- @node: witnessCos_integral
lemma witnessCos_integral : (∫ x, witnessCos x ∂design) = 0 := by
  change (∫ x : unitInterval, Real.cos (2*Real.pi*(x:ℝ))/8 ∂design) = 0
  rw [design_integral_eq_interval (fun x => Real.cos (2*Real.pi*x)/8)]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_mul_left _ (by positivity : 2*Real.pi ≠ 0),
    integral_cos]
  simp [Real.sin_two_pi]

/-- The squared cosine witness has average one over one hundred twenty eight. [This is the stated conclusion](goal). -/
-- @node: witnessCos_sq_integral
lemma witnessCos_sq_integral : (∫ x, (witnessCos x)^2 ∂design) = 1/128 := by
  change (∫ x : unitInterval, (Real.cos (2*Real.pi*(x:ℝ))/8)^2 ∂design) = 1/128
  rw [design_integral_eq_interval (fun x => (Real.cos (2*Real.pi*x)/8)^2)]
  simp only [div_pow]
  rw [show (8:ℝ)^2 = 64 by norm_num]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x^2)
      (by positivity : 2*Real.pi ≠ 0), integral_cos_sq]
  simp only [mul_zero, mul_one, Real.sin_two_pi, Real.sin_zero, mul_zero,
    zero_sub, add_zero, sub_zero, smul_eq_mul]
  field_simp
  <;> ring

/-- The separated deterministic law retains the literal cosine effect. [This is the stated conclusion](goal). -/
-- @node: separatedWitness_tau
lemma separatedWitness_tau : separatedWitness.tau = witnessCos := by
  have her : ∀ x, 0 ≤ witnessProp x ∧ witnessProp x ≤ 1 := fun x => by
    constructor <;> linarith [(witnessProp_overlap x).1, (witnessProp_overlap x).2]
  exact (deterministicLaw_primitives witnessProp witnessCos witnessCos her).2.2.1

/-- The cosine witness realizes precisely the stated positive separation. [This is the stated conclusion](goal). -/
-- @node: separatedWitness_distance
lemma separatedWitness_distance : hetDist separatedWitness = d0 := by
  have hmean : meanTau separatedWitness = 0 := by
    unfold meanTau
    rw [separatedWitness_tau]
    exact witnessCos_integral
  unfold hetDist
  rw [hmean, separatedWitness_tau]
  simp only [sub_zero]
  rw [witnessCos_sq_integral]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num : (0:ℝ) ≤ 1/128)
    (by unfold d0; positivity : 0 ≤ d0)).mpr
  unfold d0
  field_simp
  nlinarith

/-- The legal cosine witness lower bounds the supremum of model distances. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: model_distance_lower
lemma model_distance_lower (v : Params) (hv : v.Valid) : d0 ≤ maxDist v := by
  rw [← separatedWitness_distance]
  exact le_csSup (model_distance_upper v separatedWitness (separatedWitness_inModel v hv)).1
    ⟨separatedWitness, separatedWitness_inModel v hv, rfl⟩

/-- Integrating either potential outcome integrates its original arm kernel. This statement assumes [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: completion_arm_lintegral
lemma completion_arm_lintegral (law : ObservedLaw) (a : Bool)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r, f (if a then Y1 r else Y0 r) ∂causalCompletion law) =
      ∫⁻ x, ∫⁻ y, f y ∂law.Q a x ∂design := by
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hbern : IsMarkovKernel (bernKernel law) := by
    constructor
    intro x
    constructor
    change bernMeasure law.e x Set.univ = 1
    simp only [bernMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (law.e_range x).1 (sub_nonneg.mpr (law.e_range x).2)]
    norm_num
  letI : IsMarkovKernel (bernKernel law) := hbern
  cases a <;>
    simp only [Bool.false_eq_true, ↓reduceIte, causalCompletion, Y0, Y1] <;>
    rw [Measure.lintegral_compProd (by fun_prop)] <;>
    congr 1 <;> funext x <;>
    rw [Kernel.lintegral_prod _ _ _ (by fun_prop)] <;>
    dsimp only <;>
    rw [lintegral_const] <;>
    simp only [measure_univ, mul_one, Kernel.prod_apply]
  · rw [MeasureTheory.lintegral_prod (fun c : ℝ × ℝ => f c.1) (by fun_prop)]
    simp
  · rw [MeasureTheory.lintegral_prod_symm (fun c : ℝ × ℝ => f c.2) (by fun_prop)]
    simp

/-- The raw moment envelope controls each arm's absolute first moment. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: arm_absolute_moment_le
lemma arm_absolute_moment_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (a : Bool) :
    ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal |y| ∂law.Q a x ≤ 11 := by
  filter_upwards [hm.rawMoment a] with x hx
  have hpoint (y : ℝ) : |y| ≤ 1 + |y|^v.p := by
    by_cases hy : |y| ≤ 1
    · linarith [Real.rpow_nonneg (abs_nonneg y) v.p]
    · have := Real.self_le_rpow_of_one_le (le_of_not_ge hy) hv.1.1.le
      linarith
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (1 + |y|^v.p) ∂law.Q a x :=
      lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hpoint y))
    _ = 1 + ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x := by
      simp_rw [ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1)
        (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [lintegral_add_left (by fun_prop)]
      simp
    _ ≤ 11 := by
      calc
        _ ≤ (1:ℝ≥0∞) + 10 := add_le_add le_rfl hx
        _ = 11 := by norm_num

/-- Both potential outcomes are integrable by the armwise moment envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: completion_potential_integrable
lemma completion_potential_integrable (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (a : Bool) :
    Integrable (fun r => if a then Y1 r else Y0 r) (causalCompletion law) := by
  refine ⟨by cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Y0, Y1] <;> fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs]
  rw [completion_arm_lintegral law a (fun y => ENNReal.ofReal |y|) (by fun_prop)]
  have hbound : (∫⁻ x, ∫⁻ y, ENNReal.ofReal |y| ∂law.Q a x ∂design) ≤ 11 := by
    calc
      _ ≤ ∫⁻ _, (11 : ℝ≥0∞) ∂design :=
        lintegral_mono_ae (arm_absolute_moment_le v hv law hm a)
      _ = 11 := by simp [design]
  exact lt_of_le_of_lt hbound (by norm_num)

/-- The model is uniformly bounded and nonempty, and every law's observed measure uniquely determines its continuous representatives, even among representations outside the model. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: lem:causal-nonempty
lemma causal_nonempty (v : Params) (hv : v.Valid) :
    BddAbove (hetDist '' {law | InModel v law}) ∧ d0 ≤ maxDist v ∧ maxDist v ≤ 1/2 ∧
    InModel v separatedWitness ∧ hetDist separatedWitness=d0 ∧
    InNull v constantWitness ∧ (∀ x, constantWitness.tau x=1/8) ∧
    ∀ law : ObservedLaw, InModel v law →
      (∀ law' : ObservedLaw, law'.P=law.P → law'.e=law.e ∧ law'.m0=law.m0 ∧ law'.tau=law.tau) ∧
      (∀ x z : unitInterval, |law.m1 x-law.m1 z| ≤ 40*|(x:ℝ)-(z:ℝ)|^(min v.β v.γ)) ∧
      (causalCompletion law).map observe=law.P ∧
      CondIndepFun (MeasurableSpace.comap completionX inferInstance) measurable_completionX.comap_le
        (fun r => (Y0 r,Y1 r)) completionA (causalCompletion law) ∧
      Integrable Y0 (causalCompletion law) ∧ Integrable Y1 (causalCompletion law) ∧
      (∀ᵐ r ∂causalCompletion law,
        (causalCompletion law)[fun r => Y1 r-Y0 r | MeasurableSpace.comap completionX inferInstance] r=law.tau (completionX r)) ∧
      (hetDist law=0 ↔ InNull v law) := by
  have hsep : InModel v separatedWitness := separatedWitness_inModel v hv
  refine ⟨(model_distance_upper v separatedWitness hsep).1, model_distance_lower v hv,
    (model_distance_upper v separatedWitness hsep).2, hsep, separatedWitness_distance,
    constantWitness_inNull v hv, ?_, ?_⟩
  · have her : ∀ x, 0 ≤ witnessProp x ∧ witnessProp x ≤ 1 := fun x => by
      constructor <;> linarith [(witnessProp_overlap x).1, (witnessProp_overlap x).2]
    have hτ := (deterministicLaw_primitives witnessProp witnessCos
      (ContinuousMap.const unitInterval (1/8:ℝ)) her).2.2.1
    intro x
    change (deterministicLaw _ _ _).tau x = _
    rw [hτ]
    rfl
  · intro law hm
    refine ⟨?_, treated_mean_holder v hv law hm, completion_observed_marginal law hm.uniform,
      completion_conditional_independence law, completion_potential_integrable v hv law hm false,
      completion_potential_integrable v hv law hm true, ?_, hetDist_zero_iff_null v law hm⟩
    · intro law' hP
      have hu' : UniformDesign law' := by
        unfold UniformDesign covariateLaw
        rw [hP]
        exact hm.uniform
      exact observed_continuous_versions_unique law law' hm.uniform hu' hm.overlap hP
    · exact completion_conditional_effect law
        (completion_potential_integrable v hv law hm false)
        (completion_potential_integrable v hv law hm true)


end CausalSmith.Stat.FinitepHomogeneityDensegamma
