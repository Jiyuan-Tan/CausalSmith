module
public import Causalean.Stat.Minimax.LeCam
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Order.IntermediateValue

/-! Finite-moment point-CATE frontier: Helpers/TwoPrior. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- General connected real intervals, allowing infinite endpoints through absent bounds.
Endpoint flags allow closed, open and half-open intervals; inconsistent bounds code the empty set. -/
abbrev GeneralIntervalCode := Unit ⊕ ((Unit ⊕ ℝ) × (Unit ⊕ ℝ) × Bool × Bool)
/-- The real set represented by an unrestricted interval code. -/
def GeneralIntervalCode.toSet : GeneralIntervalCode → Set ℝ
  | .inl _ => ∅
  | .inr c => {x | (match c.1 with
      | .inl _ => True
      | .inr lo => if c.2.2.1 then lo ≤ x else lo < x) ∧
      (match c.2.1 with
      | .inl _ => True
      | .inr hi => if c.2.2.2 then x ≤ hi else x < hi)}
/-- Lebesgue length includes infinite length for unbounded intervals. -/
def GeneralIntervalCode.length (c : GeneralIntervalCode) : ℝ≥0∞ := volume c.toSet
/-- The endpoint carrier represents every connected real interval, including rays and the whole line. -/
-- @node: general_interval_representation
lemma general_interval_representation (s : Set ℝ) (hs : OrdConnected s) :
    ∃ c : GeneralIntervalCode, c.toSet = s := by
  have h := hs.isPreconnected.mem_intervals
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact ⟨.inr (.inr (sInf s), .inr (sSup s), true, true), by
      simpa [GeneralIntervalCode.toSet, Set.Icc] using h.symm⟩
  · exact ⟨.inr (.inr (sInf s), .inr (sSup s), true, false), by
      simpa [GeneralIntervalCode.toSet, Set.Ico] using h.symm⟩
  · exact ⟨.inr (.inr (sInf s), .inr (sSup s), false, true), by
      simpa [GeneralIntervalCode.toSet, Set.Ioc] using h.symm⟩
  · exact ⟨.inr (.inr (sInf s), .inr (sSup s), false, false), by
      simpa [GeneralIntervalCode.toSet, Set.Ioo] using h.symm⟩
  · exact ⟨.inr (.inr (sInf s), .inl (), true, true), by
      simpa [GeneralIntervalCode.toSet, Set.Ici] using h.symm⟩
  · exact ⟨.inr (.inr (sInf s), .inl (), false, true), by
      simpa [GeneralIntervalCode.toSet, Set.Ioi] using h.symm⟩
  · exact ⟨.inr (.inl (), .inr (sSup s), true, true), by
      simpa [GeneralIntervalCode.toSet, Set.Iic] using h.symm⟩
  · exact ⟨.inr (.inl (), .inr (sSup s), true, false), by
      simpa [GeneralIntervalCode.toSet, Set.Iio] using h.symm⟩
  · exact ⟨.inr (.inl (), .inl (), true, true), by
      simpa [GeneralIntervalCode.toSet] using h.symm⟩
  · exact ⟨.inl (), by simpa [GeneralIntervalCode.toSet] using h.symm⟩
/-- Membership of a fixed target in an endpoint-coded interval is a Borel event. -/
-- @node: general_interval_membership_measurable
lemma general_interval_membership_measurable (t : ℝ) :
    MeasurableSet {c : GeneralIntervalCode | t ∈ c.toSet} := by
  have hlo (b : Bool) : MeasurableSet {a : Unit ⊕ ℝ | match a with
      | .inl _ => True | .inr lo => if b then lo ≤ t else lo < t} := by
    apply measurableSet_sum_iff.mpr
    constructor
    · simp
    · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, preimage_ofPred_eq, measurableSet_setOfPred] <;> fun_prop
  have hhi (b : Bool) : MeasurableSet {a : Unit ⊕ ℝ | match a with
      | .inl _ => True | .inr hi => if b then t ≤ hi else t < hi} := by
    apply measurableSet_sum_iff.mpr
    constructor
    · simp
    · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, preimage_ofPred_eq, measurableSet_setOfPred] <;> fun_prop
  apply measurableSet_sum_iff.mpr
  constructor
  · simp [GeneralIntervalCode.toSet]
  · let L (b : Bool) := {c : (Unit ⊕ ℝ) × (Unit ⊕ ℝ) × Bool × Bool |
        match c.1 with | .inl _ => True | .inr lo => if b then lo ≤ t else lo < t}
    let H (b : Bool) := {c : (Unit ⊕ ℝ) × (Unit ⊕ ℝ) × Bool × Bool |
        match c.2.1 with | .inl _ => True | .inr hi => if b then t ≤ hi else t < hi}
    have hL (b) : MeasurableSet (L b) := (hlo b).preimage measurable_fst
    have hH (b) : MeasurableSet (H b) := (hhi b).preimage (by fun_prop)
    have hl := (measurableSet_eq_fun (f := fun c : (Unit ⊕ ℝ) × (Unit ⊕ ℝ) × Bool × Bool =>
        c.2.2.1) (by fun_prop) (g := fun _ => true) measurable_const).ite (hL true) (hL false)
    have hh := (measurableSet_eq_fun (f := fun c : (Unit ⊕ ℝ) × (Unit ⊕ ℝ) × Bool × Bool =>
        c.2.2.2) (by fun_prop) (g := fun _ => true) measurable_const).ite (hH true) (hH false)
    convert hl.inter hh using 1
    ext c
    rcases c with ⟨lo, hi, bl, bh⟩
    cases bl <;> cases bh <;> simp [GeneralIntervalCode.toSet, Set.ite, L, H]

/-- A connected coded interval containing two targets has at least their separation in length. -/
-- @node: general_interval_separation_le_length
lemma general_interval_separation_le_length (c : GeneralIntervalCode) (t0 t1 : ℝ)
    (h0 : t0 ∈ c.toSet) (h1 : t1 ∈ c.toSet) :
    ENNReal.ofReal |t1-t0| ≤ c.length := by
  have hc : OrdConnected c.toSet := by
    cases c with
    | inl u => simp [GeneralIntervalCode.toSet] at h0
    | inr c =>
      rcases c with ⟨lo, hi, bl, bh⟩
      cases lo <;> cases hi <;> cases bl <;> cases bh <;>
        simp only [GeneralIntervalCode.toSet, Bool.false_eq_true, if_false, if_true,
          Set.ofPred_true, true_and, and_true] <;>
        constructor <;> intro x hx y hy z hz <;>
        simp only [Set.mem_ofPred_eq, Set.mem_Icc] at * <;> (try constructor) <;> first | trivial | linarith
  simpa [GeneralIntervalCode.length, Real.volume_interval, abs_sub_comm] using
    (measure_mono (hc.uIcc_subset h0 h1) : volume (uIcc t0 t1) ≤ volume c.toSet)

/-- A threshold event supplies an extended-expectation lower bound without integrability. -/
-- @node: threshold_mass_le_lintegral
lemma threshold_mass_le_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (s : ℝ)
    (hs : 0 ≤ s) (E : Set Ω) (hE : MeasurableSet E) (hbound : ∀ o ∈ E, s ≤ f o) :
    ENNReal.ofReal (s * μ.real E) ≤ ∫⁻ o, ENNReal.ofReal (f o) ∂μ := by
  rw [ENNReal.ofReal_mul hs, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ E)]
  calc
    ENNReal.ofReal s * μ E = ∫⁻ o in E, ENNReal.ofReal s ∂μ := by simp
    _ ≤ ∫⁻ o in E, ENNReal.ofReal (f o) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with o ho
      exact ENNReal.ofReal_le_ofReal (hbound o ho)
    _ ≤ ∫⁻ o, ENNReal.ofReal (f o) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- Le Cam testing and threshold losses give the two-target absolute-risk bound. -/
-- @node: two_prior_absolute_risk
lemma two_prior_absolute_risk {Ω : Type*} [MeasurableSpace Ω]
    (ν0 ν1 : Measure Ω) [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (t0 t1 v : ℝ) (hsep : 0 < |t1-t0|) (htv : Causalean.Stat.tvDist ν0 ν1 ≤ v)
    (T : Ω → ℝ) (hT : Measurable T) :
    ENNReal.ofReal (|t1-t0| * (1-v)/4) ≤
      max (∫⁻ o, ENNReal.ofReal (|T o-t0|) ∂ν0) (∫⁻ o, ENNReal.ofReal (|T o-t1|) ∂ν1) := by
  let s := |t1-t0| / 2
  let E0 := {o | s ≤ |T o-t0|}
  let E1 := {o | s ≤ |T o-t1|}
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hE0 : MeasurableSet E0 := by
    apply measurableSet_le measurable_const
    fun_prop
  have hE1 : MeasurableSet E1 := by
    apply measurableSet_le measurable_const
    fun_prop
  have htest : 1-v ≤ ν0.real E0 + ν1.real E1 := by
    have h := Causalean.Stat.one_sub_tvDist_le_error_sum (P₀ := ν0) (P₁ := ν1)
      hT (θ₀ := t0) (θ₁ := t1) (s := s) (by simp only [s, Real.dist_eq, abs_sub_comm]; linarith)
    simp only [Real.dist_eq] at h
    exact (sub_le_sub_left htv 1).trans h
  have h0 := threshold_mass_le_lintegral ν0 (fun o => |T o-t0|) s hs E0 hE0 (fun _ ho => ho)
  have h1 := threshold_mass_le_lintegral ν1 (fun o => |T o-t1|) s hs E1 hE1 (fun _ ho => ho)
  have hb : |t1-t0| * (1-v)/4 ≤ s * max (ν0.real E0) (ν1.real E1) := by
    have hmax0 := le_max_left (ν0.real E0) (ν1.real E1)
    have hmax1 := le_max_right (ν0.real E0) (ν1.real E1)
    dsimp [s]
    nlinarith [mul_nonneg (le_of_lt hsep) (by linarith : 0 ≤ 2 * max (ν0.real E0) (ν1.real E1) - (1-v))]
  apply (ENNReal.ofReal_le_ofReal hb).trans
  rcases le_total (ν0.real E0) (ν1.real E1) with h | h
  · rw [max_eq_right h]
    exact h1.trans (le_max_right _ _)
  · rw [max_eq_left h]
    exact h0.trans (le_max_left _ _)

/-- A common independent probability seed preserves total variation exactly. -/
-- @node: two_prior_seed_tv
lemma two_prior_seed_tv {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ν0 ν1 : Measure Ω) [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (η : Measure Ξ) [IsProbabilityMeasure η] :
    Causalean.Stat.tvDist (ν0.prod η) (ν1.prod η) = Causalean.Stat.tvDist ν0 ν1 := by
  simpa only [Measure.compProd_const] using
    Causalean.Stat.tvDist_compProd_eq ν0 ν1 (Kernel.const Ω η)

/-- A finite prior average is bounded by the extended worst-case expectation,
even when risks are infinite or the class has unbounded finite risks. -/
-- @node: finite_prior_risk_le_sup
lemma finite_prior_risk_le_sup {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (C : Set (Measure Ω)) (μ : ι → Measure Ω) (w : ι → ℝ≥0∞)
    (hμ : ∀ i, μ i ∈ C) (hp : ∀ i, IsProbabilityMeasure (μ i)) (hw : ∑ i, w i = 1)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂(∑ i, w i • μ i)) ≤ ⨆ Q : {Q // Q ∈ C}, ∫⁻ o, f o ∂Q.1 := by
  classical
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]
  calc
    ∑ i, w i * ∫⁻ o, f o ∂μ i ≤
        ∑ i, w i * (⨆ Q : {Q // Q ∈ C}, ∫⁻ o, f o ∂Q.1) :=
      Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (le_iSup_of_le ⟨μ i, hμ i⟩ le_rfl)
    _ = (∑ i, w i) * (⨆ Q : {Q // Q ∈ C}, ∫⁻ o, f o ∂Q.1) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hw, one_mul]

-- @node: lem:two-prior-decision-reduction
/-- All measurable real decisions satisfy the extended-expectation two-target bound;
all connected interval decisions satisfy the length bound without finite-risk restrictions.
Every finite-prior average of a measurable extended loss is bounded by its class supremum. -/
lemma two_prior_decision_reduction {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (ν0 ν1 : Measure Ω) [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (t0 t1 v : ℝ) (hsep : 0 < |t1-t0|) (hv : v < 1)
    (htv : Causalean.Stat.tvDist ν0 ν1 ≤ v) :
  (∀ T : Ω → ℝ, Measurable T →
    ENNReal.ofReal (|t1-t0| *(1-v)/4) ≤
      max (∫⁻ o, ENNReal.ofReal (|T o-t0|) ∂ν0) (∫⁻ o, ENNReal.ofReal (|T o-t1|) ∂ν1)) ∧
  (∀ I : Ω → GeneralIntervalCode, Measurable I →
    9/10 ≤ ν0.real {o | t0 ∈ (I o).toSet} → 9/10 ≤ ν1.real {o | t1 ∈ (I o).toSet} →
    ENNReal.ofReal (|t1-t0| *(4/5-v)) ≤ ∫⁻ o, (I o).length ∂ν0) ∧
  (∀ {Ξ : Type} [MeasurableSpace Ξ] (η : Measure Ξ) [IsProbabilityMeasure η],
    Causalean.Stat.tvDist (ν0.prod η) (ν1.prod η) = Causalean.Stat.tvDist ν0 ν1) ∧
  (∀ {ι : Type*} [Fintype ι] (C : Set (Measure Ω))
      (μ : ι → Measure Ω) (w : ι → ℝ≥0∞),
    (∀ i, μ i ∈ C) → (∀ i, IsProbabilityMeasure (μ i)) → (∑ i, w i = 1) →
    ∀ f : Ω → ℝ≥0∞, Measurable f →
      (∫⁻ o, f o ∂(∑ i, w i • μ i)) ≤ ⨆ Q : {Q // Q ∈ C}, ∫⁻ o, f o ∂Q.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    exact two_prior_absolute_risk ν0 ν1 t0 t1 v hsep htv T hT
  · intro I hI hc0 hc1
    let E0 := {o | t0 ∈ (I o).toSet}
    let E1 := {o | t1 ∈ (I o).toSet}
    have hE0 : MeasurableSet E0 := (general_interval_membership_measurable t0).preimage hI
    have hE1 : MeasurableSet E1 := (general_interval_membership_measurable t1).preimage hI
    have htransfer : ν1.real E1 - ν0.real E1 ≤ v :=
      (Causalean.Stat.measureReal_sub_le_tvDist (μ := ν0) (ν := ν1) hE1).trans htv
    have hmass : 4/5-v ≤ ν0.real (E0 ∩ E1) := by
      have hunion := measureReal_union_add_inter (μ := ν0) (s := E0) hE1
      have hle : ν0.real (E0 ∪ E1) ≤ 1 := measureReal_le_one
      change 9/10 ≤ ν0.real E0 at hc0
      change 9/10 ≤ ν1.real E1 at hc1
      linarith
    calc
      ENNReal.ofReal (|t1-t0| * (4/5-v)) ≤
          ENNReal.ofReal |t1-t0| * ν0 (E0 ∩ E1) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν0 (E0 ∩ E1)),
          ← ENNReal.ofReal_mul (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmass (abs_nonneg _))
      _ = ∫⁻ o in E0 ∩ E1, ENNReal.ofReal |t1-t0| ∂ν0 := by simp
      _ ≤ ∫⁻ o in E0 ∩ E1, (I o).length ∂ν0 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hE0.inter hE1)] with o ho
        exact general_interval_separation_le_length (I o) t0 t1 ho.1 ho.2
      _ ≤ ∫⁻ o, (I o).length ∂ν0 := lintegral_mono' Measure.restrict_le_self le_rfl
  · intro Ξ _ η _
    exact two_prior_seed_tv ν0 ν1 η
  · exact finite_prior_risk_le_sup

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
