module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Observable marked-density reduction -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The clipping rectangle object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,v). -/

def clippingRectangle (c_f C_f : ℝ) (v : Fin 7 → ℝ) : Prop :=
  v 0 ∈ Icc c_f C_f ∧
  v 1 ∈ Icc (c_f / 4) (3 * C_f / 4) ∧
  v 2 ∈ Icc (c_f / 4) (3 * C_f / 4) ∧
  ∀ i : Fin 7, 3 ≤ i.val → v i ∈ Icc 0 (3 * C_f / 4)
/-- [The coordinate mark object](goal) is defined from [the supplied inputs](hyp:i,o). -/

def coordinateMark (i : Fin 7) (o : SourceObs) : ℝ :=
  if i.val = 1 then boolReal (!o.2.1) else
  if i.val = 2 then boolReal o.2.1 else
  if i.val = 3 then boolReal (!o.2.1) * o.2.2.2 else
  if i.val = 4 then boolReal o.2.1 * o.2.2.2 else
  if i.val = 5 then boolReal (!o.2.1) * boolReal o.2.2.1 else
  boolReal o.2.1 * boolReal o.2.2.1
/-- [The coordinate basis object](goal) is defined from [the supplied inputs](hyp:i). -/

def coordinateBasis (i : Fin 7) : Fin 7 → ℝ :=
  fun j => if j = i then 1 else 0
/-- [The fourth derivative envelope object](goal) is defined from [the supplied inputs](hyp:c_f,C_f). -/

noncomputable def fourthDerivativeEnvelope (c_f C_f : ℝ) : ℝ :=
  48 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5

-- @node: coordinateMark_mem_unit_interval
/-- Given [the supplied inputs](hyp:i,o,hy), [the stated result about coordinate mark mem unit interval holds](goal). -/
lemma coordinateMark_mem_unit_interval (i : Fin 7) (o : SourceObs)
    (hy : o.2.2.2 ∈ Icc (0 : ℝ) 1) :
    coordinateMark i o ∈ Icc (0 : ℝ) 1 := by
  rcases o with ⟨x, z, d, y⟩
  cases z <;> cases d <;> fin_cases i <;>
    simp [coordinateMark, boolReal, Set.mem_Icc] at * <;> constructor <;> nlinarith [hy.1, hy.2]

-- @node: markedDensityVector_assignment_lower_bounds
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,x,hx), [the stated result about marked density vector assignment lower bounds holds](goal). -/
lemma markedDensityVector_assignment_lower_bounds (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (x : ℝ) (hx : x ∈ covariateSpace) :
    c_f / 4 ≤ markedDensityVector c_f C_f L P n hP x 1 ∧
    c_f / 4 ≤ markedDensityVector c_f C_f L P n hP x 2 := by
  have hf := (hP.sourceBounds.2.2.2.2.2 x hx).1
  have he := hP.overlap x hx
  dsimp [markedDensityVector]
  constructor
  · calc
      c_f / 4 = c_f * (1 / 4) := by ring
      _ ≤ P.fS x * (1 / 4) := mul_le_mul_of_nonneg_right hf (by norm_num)
      _ ≤ P.fS x * (1 - P.e x) :=
        mul_le_mul_of_nonneg_left (by linarith [he.2])
          (by linarith [hP.sourceBounds.1.1])
  · calc
      c_f / 4 = c_f * (1 / 4) := by ring
      _ ≤ P.fS x * (1 / 4) := mul_le_mul_of_nonneg_right hf (by norm_num)
      _ ≤ P.fS x * P.e x :=
        mul_le_mul_of_nonneg_left he.1 (by linarith [hP.sourceBounds.1.1])

-- @node: markedDensityVector_mem_clippingRectangle
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,x,hx), [the stated result about marked density vector mem clipping rectangle holds](goal). -/
lemma markedDensityVector_mem_clippingRectangle (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (x : ℝ) (hx : x ∈ covariateSpace) :
    clippingRectangle c_f C_f (markedDensityVector c_f C_f L P n hP x) := by
  have hs := hP.sourceBounds.2.2.2.2.2 x hx
  have ht := hP.targetBounds.2.1 x hx
  have he := hP.overlap x hx
  have hm (A z : Bool) := (hP.armHolder.2.1 A z).2.2 x hx
  have hq := markedDensityVector_assignment_lower_bounds c_f C_f L P n hP x hx
  have hfs : 0 ≤ P.fS x := le_trans hP.sourceBounds.1.1.le hs.1
  have hq0 : 0 ≤ P.fS x * (1 - P.e x) ∧
      P.fS x * (1 - P.e x) ≤ 3 * C_f / 4 := by
    constructor
    · exact mul_nonneg hfs (by linarith [he.2])
    · nlinarith [mul_nonneg (show 0 ≤ C_f - P.fS x by linarith)
        (show 0 ≤ 1 - P.e x by linarith),
        mul_nonneg hfs
          (show 0 ≤ P.e x - 1 / 4 by linarith)]
  have hq1 : 0 ≤ P.fS x * P.e x ∧
      P.fS x * P.e x ≤ 3 * C_f / 4 := by
    constructor
    · exact mul_nonneg hfs (by linarith [he.1])
    · nlinarith [mul_nonneg (show 0 ≤ C_f - P.fS x by linarith)
        (show 0 ≤ P.e x by linarith),
        mul_nonneg hfs
          (show 0 ≤ 3 / 4 - P.e x by linarith)]
  have hmark (q m : ℝ) (hq' : 0 ≤ q ∧ q ≤ 3 * C_f / 4)
      (hm' : m ∈ Icc (0 : ℝ) 1) : q * m ∈ Icc 0 (3 * C_f / 4) := by
    rcases hm' with ⟨hm0, hm1⟩
    constructor
    · exact mul_nonneg hq'.1 hm0
    · calc
        q * m ≤ q * 1 := mul_le_mul_of_nonneg_left hm1 hq'.1
        _ ≤ 3 * C_f / 4 := by simpa using hq'.2
  rw [clippingRectangle]
  refine ⟨ht, ?_, ?_, ?_⟩
  · change c_f / 4 ≤ P.fS x * (1 - P.e x) ∧
        P.fS x * (1 - P.e x) ≤ 3 * C_f / 4
    constructor
    · exact hq.1
    · exact hq0.2
  · change c_f / 4 ≤ P.fS x * P.e x ∧
        P.fS x * P.e x ≤ 3 * C_f / 4
    constructor
    · exact hq.2
    · exact hq1.2
  · intro i hi
    fin_cases i <;> simp_all [markedDensityVector, Set.mem_Icc]

-- @node: Phi_markedDensityVector_eq_transport_integrand
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A,x,hx), [the stated result about phi marked density vector eq transport integrand holds](goal). -/
lemma Phi_markedDensityVector_eq_transport_integrand (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (A : Bool) (x : ℝ) (hx : x ∈ covariateSpace) :
    Phi A (markedDensityVector c_f C_f L P n hP x) =
      P.fT x * armContrast P A x := by
  have hq := markedDensityVector_assignment_lower_bounds c_f C_f L P n hP x hx
  have hq0 : P.fS x * (1 - P.e x) ≠ 0 := by
    apply ne_of_gt
    have hc := hP.sourceBounds.1.1
    dsimp [markedDensityVector] at hq
    linarith [hq.1]
  have hq1 : P.fS x * P.e x ≠ 0 := by
    apply ne_of_gt
    have hc := hP.sourceBounds.1.1
    dsimp [markedDensityVector] at hq
    linarith [hq.2]
  have hfs : P.fS x ≠ 0 := (mul_ne_zero_iff.mp hq1).1
  have he1 : P.e x ≠ 0 := (mul_ne_zero_iff.mp hq1).2
  have he0 : 1 - P.e x ≠ 0 := (mul_ne_zero_iff.mp hq0).2
  cases A <;> simp [Phi, markedDensityVector, armContrast] <;>
    field_simp [hfs, he0, he1] <;> ring <;> simp

-- @node: transportedForm_eq_integral_Phi_markedDensityVector
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated result about transported form eq integral phi marked density vector holds](goal). -/
lemma transportedForm_eq_integral_Phi_markedDensityVector (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (A : Bool) :
    transportedForm P A =
      ∫ x in (0 : ℝ)..1, Phi A (markedDensityVector c_f C_f L P n hP x) := by
  have hpoint : ∀ x ∈ covariateSpace,
      Phi A (markedDensityVector c_f C_f L P n hP x) =
        P.fT x * armContrast P A x := by
    intro x hx
    exact Phi_markedDensityVector_eq_transport_integrand c_f C_f L P n hP A x hx
  rw [transportedForm, covariateSpace, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (hpoint x (by simpa [covariateSpace] using hx)).symm

-- @node: source_marked_arm_integral
/-- Given [the supplied inputs](hyp:P,A,z,B,hB), [the stated result about source marked arm integral holds](goal). -/
lemma source_marked_arm_integral (P : TransportLaw) (A z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ o in {o : SourceObs | o.1 ∈ B},
      (if o.2.1 = z then (1 : ℝ) else 0) * armValue A o ∂sourceObsLaw P) =
      ∫ o in {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z},
        armValue A o ∂sourceObsLaw P := by
  let Z : Set SourceObs := {o | o.2.1 = z}
  have hZ : MeasurableSet Z := by
    dsimp [Z]
    measurability
  have hpoint : (fun o : SourceObs =>
      (if o.2.1 = z then (1 : ℝ) else 0) * armValue A o) =
      Z.indicator (armValue A) := by
    funext o
    by_cases ho : o.2.1 = z <;> simp [Z, Set.indicator, ho]
  rw [hpoint, setIntegral_indicator hZ]
  congr 1

-- @node: source_marked_arm_density
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,A,z,B,hB,hsub), [the stated result about source marked arm density holds](goal). -/
lemma source_marked_arm_density (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (A z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ covariateSpace) :
    (∫ x in B, P.fS x * assignmentMass P z x * P.m A z x) =
      ∫ o in {o : SourceObs | o.1 ∈ B},
        (if o.2.1 = z then (1 : ℝ) else 0) * armValue A o ∂sourceObsLaw P := by
  rw [source_marked_arm_integral P A z B hB]
  exact (hP.armHolder.2.2 A z B hB hsub).symm
/-- Given [the supplied inputs](hyp:P,z,he), [the stated result about measurable assignment mass on covariate holds](goal). -/

lemma measurable_assignmentMassOnCovariate (P : TransportLaw) (z : Bool)
    (he : MeasurableOnCovariate P.e) :
    Measurable (covariateSpace.indicator (assignmentMass P z)) := by
  cases z
  · have hone : Measurable (covariateSpace.indicator (fun _ : ℝ => (1 : ℝ))) :=
      measurable_const.indicator measurableSet_Icc
    have hpoint : covariateSpace.indicator (assignmentMass P false) =
        fun x => covariateSpace.indicator (fun _ : ℝ => (1 : ℝ)) x -
          covariateSpace.indicator P.e x := by
      funext x
      by_cases hx : x ∈ covariateSpace <;>
        simp [assignmentMass, Set.indicator, hx]
    rw [hpoint]
    exact hone.sub he
  · exact he

-- @node: source_assignment_density
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hP,z,B,hB,hsub), [the stated result about source assignment density holds](goal). -/
lemma source_assignment_density (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ covariateSpace) :
    (∫ x in B, P.fS x * assignmentMass P z x) =
      ((sourceObsLaw P) {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z}).toReal := by
  have hcov : Measurable (covariate : FullData → ℝ) := by
    unfold covariate
    fun_prop
  have hobs : Measurable (observeSource : Assigned → SourceObs) := by
    unfold observeSource covariate
    fun_prop
  have hXLaw : sourceXLaw P = (populationLaw P true).map covariate := by
    calc
      sourceXLaw P = P.assignedLaw.map (fun o : Assigned => covariate o.1) := by
        rw [sourceXLaw, sourceObsLaw, Measure.map_map (by fun_prop) hobs]
        rfl
      _ = (P.assignedLaw.map Prod.fst).map covariate := by
        rw [Measure.map_map hcov (by fun_prop)]
        rfl
      _ = (populationLaw P true).map covariate := by rw [hP.randomized.2.2.1]
  have hmass :
      ((sourceObsLaw P) {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z}).toReal =
        ∫ o in {o : FullData | covariate o ∈ B},
          assignmentMass P z (covariate o) ∂populationLaw P true := by
    have hset : MeasurableSet {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z} := by
      measurability
    have hfull : MeasurableSet {o : FullData | covariate o ∈ B} := hB.preimage hcov
    calc
      _ = (P.assignedLaw {o : Assigned |
          o.1 ∈ {o : FullData | covariate o ∈ B} ∧ o.2.1 = z}).toReal := by
            rw [sourceObsLaw, Measure.map_apply hobs hset]
            congr 1
      _ = _ := hP.randomized.2.2.2 _ hfull z
  let assignmentMassOnCovariate : ℝ → ℝ :=
    covariateSpace.indicator (assignmentMass P z)
  have hmeas : Measurable assignmentMassOnCovariate := by
    exact measurable_assignmentMassOnCovariate P z hP.randomized.2.1
  have hmap :
      (∫ o in {o : FullData | covariate o ∈ B},
        assignmentMass P z (covariate o) ∂populationLaw P true) =
        ∫ x in B, assignmentMass P z x ∂sourceXLaw P := by
    rw [hXLaw]
    calc
      _ = ∫ o in {o : FullData | covariate o ∈ B},
          assignmentMassOnCovariate (covariate o) ∂populationLaw P true := by
            apply setIntegral_congr_fun
            exact hB.preimage hcov
            intro o ho
            simp [assignmentMassOnCovariate, Set.indicator, hsub ho]
      _ = ∫ x in B, assignmentMassOnCovariate x
          ∂Measure.map covariate (populationLaw P true) :=
            (setIntegral_map hB hmeas.aestronglyMeasurable hcov.aemeasurable).symm
      _ = _ := by
        apply setIntegral_congr_fun hB
        intro x hx
        simp [assignmentMassOnCovariate, Set.indicator, hsub hx]
  have hcont : ContinuousOn P.fS covariateSpace := by
    have hcd := hP.sourceHolder.2.1.continuousOn
    have hmap' : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
        {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
      intro x hx
      simpa using hx
    simpa [Function.comp_def, Matrix.cons_val_zero] using hcd.comp hmap' hmaps
  have hae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.fS x))
      ((volume.restrict covariateSpace).restrict B) :=
    (hcont.aemeasurable measurableSet_Icc).ennreal_ofReal.restrict
  have hfinite : ∀ᵐ x ∂(volume.restrict covariateSpace).restrict B,
      ENNReal.ofReal (P.fS x) < ⊤ := by filter_upwards [] with x; simp
  have hden := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (f := fun x : ℝ => ENNReal.ofReal (P.fS x))
    (s := B) hae hfinite (assignmentMass P z) hB
  have hdensity : (∫ x in B, assignmentMass P z x ∂sourceXLaw P) =
      ∫ x in B, P.fS x * assignmentMass P z x := by
    rw [hP.sourceBounds.2.2.2.2.1]
    calc
      _ = ∫ x in B, (ENNReal.ofReal (P.fS x)).toReal • assignmentMass P z x
            ∂volume := by
              simpa only [Measure.restrict_restrict_of_subset hsub] using hden
      _ = _ := by
        apply setIntegral_congr_fun hB
        intro x hx
        simp [ENNReal.toReal_ofReal
          (le_trans hP.sourceBounds.1.1.le
            (hP.sourceBounds.2.2.2.2.2 x (hsub hx)).1)]
  exact (hdensity.symm.trans hmap.symm).trans hmass.symm

-- @node: source_assignment_mark_integral
/-- Given [the supplied inputs](hyp:P,z,B,hB), [the stated result about source assignment mark integral holds](goal). -/
lemma source_assignment_mark_integral (P : TransportLaw) (z : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ o in {o : SourceObs | o.1 ∈ B},
      if o.2.1 = z then (1 : ℝ) else 0 ∂sourceObsLaw P) =
      ((sourceObsLaw P) {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z}).toReal := by
  let Z : Set SourceObs := {o | o.2.1 = z}
  have hZ : MeasurableSet Z := by dsimp [Z]; measurability
  have hpoint : (fun o : SourceObs => if o.2.1 = z then (1 : ℝ) else 0) =
      Z.indicator (fun _ => (1 : ℝ)) := by
    funext o
    by_cases ho : o.2.1 = z <;> simp [Z, Set.indicator, ho]
  rw [hpoint, setIntegral_indicator hZ]
  have hS : MeasurableSet {o : SourceObs | o.1 ∈ B ∧ o.2.1 = z} := by
    measurability
  rw [setIntegral_one_eq_measureReal]
  congr 1

-- @node: Phi_value_abs_le_fourthDerivativeEnvelope
/-- Given [the supplied inputs](hyp:c_f,C_f,hf,hF,A,v,hv), [the stated result about phi value abs le fourth derivative envelope holds](goal). -/
lemma Phi_value_abs_le_fourthDerivativeEnvelope (c_f C_f : ℝ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (A : Bool) (v : Fin 7 → ℝ)
    (hv : clippingRectangle c_f C_f v) :
    |Phi A v| ≤ fourthDerivativeEnvelope c_f C_f := by
  let R : ℝ := 4 / c_f
  have hR : 1 ≤ R := by dsimp [R]; apply (le_div_iff₀ hf.1).2; linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hC : 0 ≤ 1 + C_f := by linarith
  have h0 := hv.1
  have h1 := hv.2.1
  have h2 := hv.2.2.1
  have hmark (j : Fin 7) (hj : 3 ≤ j.val) := hv.2.2.2 j hj
  have hr (j q : Fin 7) (hj : 3 ≤ j.val)
      (hq : c_f / 4 ≤ v q) :
      0 ≤ v 0 * v j / v q ∧
      v 0 * v j / v q ≤ (1 + C_f) ^ 2 * R := by
    have hq0 : 0 < v q := by linarith
    have hj' := hmark j hj
    constructor
    · exact div_nonneg (mul_nonneg (le_trans hf.1.le h0.1) hj'.1) hq0.le
    · apply (div_le_iff₀ hq0).2
      have hqR : 1 ≤ v q * R := by
        calc
          1 = (c_f / 4) * R := by dsimp [R]; field_simp [ne_of_gt hf.1]
          _ ≤ v q * R := mul_le_mul_of_nonneg_right hq hR0
      have hprod : v 0 * v j ≤ (1 + C_f) ^ 2 := by
        have hleft : v 0 ≤ 1 + C_f := by linarith [h0.2]
        have hright : v j ≤ 1 + C_f := by linarith [hj'.2]
        calc
          v 0 * v j ≤ (1 + C_f) * (1 + C_f) := by
            exact mul_le_mul hleft hright hj'.1 hC
          _ = (1 + C_f) ^ 2 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hqR (sq_nonneg (1 + C_f))]
  have hp := hr (if A then 4 else 6) 2 (by cases A <;> decide) h2.1
  have hm := hr (if A then 3 else 5) 1 (by cases A <;> decide) h1.1
  have hpow : R ≤ R ^ 5 := by
    calc
      R = R * 1 := by ring
      _ ≤ R * R ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hR) hR0
      _ = R ^ 5 := by ring
  have hfinal : 2 * ((1 + C_f) ^ 2 * R) ≤
      48 * (1 + C_f) ^ 2 * R ^ 5 := by
    nlinarith [mul_nonneg (sq_nonneg (1 + C_f)) (sub_nonneg.mpr hpow)]
  unfold Phi fourthDerivativeEnvelope
  change |v 0 * (v (if A then 4 else 6) / v 2 -
    v (if A then 3 else 5) / v 1)| ≤ _
  rw [mul_sub, ← mul_div_assoc, ← mul_div_assoc]
  rw [abs_le]
  constructor <;> dsimp [R] at * <;> nlinarith [hp.1, hp.2, hm.1, hm.2]

/-- The derivative of one arm contribution, evaluated along an arbitrary direction.  Under [the displayed assumptions and inputs](hyp:a,b,q,v,h,hq), [the stated conclusion holds](goal). -/
-- @node: fderiv_marked_arm_ratio_apply
lemma fderiv_marked_arm_ratio_apply (a b q : Fin 7) (v h : Fin 7 → ℝ)
    (hq : v q ≠ 0) :
    fderiv ℝ (fun y : Fin 7 → ℝ => y a * y b * (y q)⁻¹) v h =
      (h a * v b + v a * h b) * (v q)⁻¹ -
        v a * v b * h q * (v q)⁻¹ ^ 2 := by
  have ha := (ContinuousLinearMap.proj a : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := v)
  have hb := (ContinuousLinearMap.proj b : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := v)
  have hq' := (ContinuousLinearMap.proj q : (Fin 7 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := v)
  have hi := (hasFDerivAt_inv hq).comp v hq'
  have hd := (ha.mul hb).mul hi
  change HasFDerivAt (fun y : Fin 7 → ℝ => y a * y b * (y q)⁻¹) _ v at hd
  rw [hd.fderiv]
  simp [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, inv_pow]
  ring

/-- The first derivative of the transport integrand is the difference of the two arm derivatives.  Under [the displayed assumptions and inputs](hyp:A,v,h,h1,h2), [the stated conclusion holds](goal). -/
-- @node: iteratedFDeriv_one_Phi_apply
lemma iteratedFDeriv_one_Phi_apply (A : Bool) (v h : Fin 7 → ℝ)
    (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    iteratedFDeriv ℝ 1 (Phi A) v ![h] =
      ((h 0 * v (if A then 4 else 6) + v 0 * h (if A then 4 else 6)) * (v 2)⁻¹ -
        v 0 * v (if A then 4 else 6) * h 2 * (v 2)⁻¹ ^ 2) -
      ((h 0 * v (if A then 3 else 5) + v 0 * h (if A then 3 else 5)) * (v 1)⁻¹ -
        v 0 * v (if A then 3 else 5) * h 1 * (v 1)⁻¹ ^ 2) := by
  have hp : DifferentiableAt ℝ
      (fun y : Fin 7 → ℝ => y 0 * y (if A then 4 else 6) * (y 2)⁻¹) v := by
    fun_prop
  have hm : DifferentiableAt ℝ
      (fun y : Fin 7 → ℝ => y 0 * y (if A then 3 else 5) * (y 1)⁻¹) v := by
    fun_prop
  have heq : Phi A =
      (fun y : Fin 7 → ℝ => y 0 * y (if A then 4 else 6) * (y 2)⁻¹) -
      (fun y : Fin 7 → ℝ => y 0 * y (if A then 3 else 5) * (y 1)⁻¹) := by
    funext y
    simp [Phi, div_eq_mul_inv]
    ring
  rw [iteratedFDeriv_one_apply, heq, fderiv_sub hp hm, ContinuousLinearMap.sub_apply]
  simp only [Matrix.cons_val_zero]
  rw [
    fderiv_marked_arm_ratio_apply _ _ _ v h h2,
    fderiv_marked_arm_ratio_apply _ _ _ v h h1]

/-- Bounded coordinate directions give a uniform first derivative bound for one arm.  Under [the displayed assumptions and inputs](hyp:t,r,q,dt,dr,dq,C,R,hC,hR,ht,hr,hq,hdt,hdr,hdq), [the stated conclusion holds](goal). -/
-- @node: marked_arm_first_derivative_abs_le
lemma marked_arm_first_derivative_abs_le (t r q dt dr dq C R : ℝ)
    (hC : 1 ≤ C) (hR : 1 ≤ R) (ht : |t| ≤ C) (hr : |r| ≤ C)
    (hq : |q⁻¹| ≤ R) (hdt : |dt| ≤ 1) (hdr : |dr| ≤ 1) (hdq : |dq| ≤ 1) :
    |(dt * r + t * dr) * q⁻¹ - t * r * dq * q⁻¹ ^ 2| ≤
      3 * (1 + C) ^ 2 * R ^ 2 := by
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hlinear : |dt * r + t * dr| ≤ 2 * C := by
    calc
      _ ≤ |dt| * |r| + |t| * |dr| := by simpa only [abs_mul] using abs_add_le (dt * r) (t * dr)
      _ ≤ 1 * C + C * 1 := add_le_add
        (mul_le_mul hdt hr (abs_nonneg _) (by norm_num))
        (mul_le_mul ht hdr (abs_nonneg _) hC0)
      _ = 2 * C := by ring
  have hterm1 : |(dt * r + t * dr) * q⁻¹| ≤ 2 * C * R := by
    rw [abs_mul]
    exact mul_le_mul hlinear hq (abs_nonneg _) (by positivity)
  have hterm2 : |t * r * dq * q⁻¹ ^ 2| ≤ C ^ 2 * R ^ 2 := by
    simp only [abs_mul, abs_pow]
    have htr := mul_le_mul ht hr (abs_nonneg _) hC0
    have htrq := mul_le_mul htr hdq (abs_nonneg _) (mul_nonneg hC0 hC0)
    have hp := pow_le_pow_left₀ (abs_nonneg (q⁻¹)) hq 2
    simpa only [mul_one, ← sq] using mul_le_mul htrq hp (by positivity) (by positivity)
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hCC : C ≤ (1 + C) ^ 2 := by nlinarith
  have hCC2 : C ^ 2 ≤ (1 + C) ^ 2 := by nlinarith
  have hterm1' : 2 * C * R ≤ 2 * (1 + C) ^ 2 * R ^ 2 := by
    exact mul_le_mul (by nlinarith : 2 * C ≤ 2 * (1 + C) ^ 2) hRR hR0 (by positivity)
  have hterm2' := mul_le_mul_of_nonneg_right hCC2 (sq_nonneg R)
  exact (abs_sub _ _).trans (by nlinarith [hterm1, hterm2])

/-- The first coordinate derivative uses exactly the deterministic envelope from the reduction.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,hf,hF,A,v,hv,i), [the stated conclusion holds](goal). -/
-- @node: Phi_first_derivative_abs_le_fourthDerivativeEnvelope
lemma Phi_first_derivative_abs_le_fourthDerivativeEnvelope (c_f C_f : ℝ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (A : Bool) (v : Fin 7 → ℝ) (hv : clippingRectangle c_f C_f v) (i : Fin 7) :
    |iteratedFDeriv ℝ 1 (Phi A) v ![coordinateBasis i]| ≤
      fourthDerivativeEnvelope c_f C_f := by
  let R := 4 / c_f
  have hR : 1 ≤ R := by dsimp [R]; apply (le_div_iff₀ hf.1).2; linarith
  have ht : |v 0| ≤ C_f := by
    rw [abs_of_nonneg (le_trans hf.1.le hv.1.1)]
    exact hv.1.2
  have hr (j : Fin 7) (hj : 3 ≤ j.val) : |v j| ≤ C_f := by
    have h := hv.2.2.2 j hj
    rw [abs_of_nonneg h.1]
    linarith [h.2]
  have hq (j : Fin 7) (hj : c_f / 4 ≤ v j) :
      v j ≠ 0 ∧ |(v j)⁻¹| ≤ R := by
    have hj0 : 0 < v j := by linarith
    refine ⟨ne_of_gt hj0, ?_⟩
    rw [abs_of_nonneg (inv_pos.mpr hj0).le]
    calc
      (v j)⁻¹ ≤ (c_f / 4)⁻¹ := (inv_le_inv₀ hj0 (div_pos hf.1 (by norm_num))).2 hj
      _ = R := by dsimp [R]; ring
  have h1 := hq 1 hv.2.1.1
  have h2 := hq 2 hv.2.2.1.1
  have hd (j : Fin 7) : |coordinateBasis i j| ≤ 1 := by
    by_cases hji : j = i <;> simp [coordinateBasis, hji]
  rw [iteratedFDeriv_one_Phi_apply A v (coordinateBasis i) h1.1 h2.1]
  have hp := marked_arm_first_derivative_abs_le
    (v 0) (v (if A then 4 else 6)) (v 2) _ _ _ C_f R hF.le hR ht
    (hr _ (by cases A <;> decide)) h2.2 (hd 0) (hd (if A then 4 else 6)) (hd 2)
  have hm := marked_arm_first_derivative_abs_le
    (v 0) (v (if A then 3 else 5)) (v 1) _ _ _ C_f R hF.le hR ht
    (hr _ (by cases A <;> decide)) h1.2 (hd 0) (hd (if A then 3 else 5)) (hd 1)
  have hpowers : R ^ 2 ≤ R ^ 5 := by
    calc
      R ^ 2 = R ^ 2 * 1 := by ring
      _ ≤ R ^ 2 * R ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hR) (sq_nonneg R)
      _ = R ^ 5 := by ring
  have hscale := mul_le_mul_of_nonneg_left hpowers (sq_nonneg (1 + C_f))
  unfold fourthDerivativeEnvelope
  change _ ≤ 48 * (1 + C_f) ^ 2 * R ^ 5
  exact (abs_sub _ _).trans (by nlinarith [hp, hm, mul_nonneg (sq_nonneg (1 + C_f)) (sq_nonneg R)])

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
