module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.LowerPair

/-! # Logarithm-free adaptive weak-overlap minimax rate -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped ENNReal

/-- Expected supremum risk of the concrete estimator at one law. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP), [the `estimatorSupRisk` object being defined](goal). -/
noncomputable def estimatorSupRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (P : Measure (Obs d))
    (hP : P ∈ ModelClass d β B L C c_f γ) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ x ∈ cube d,
    ENNReal.ofReal |equalCellEstimator β B ω x - responseOf P hP x|
    ∂Measure.pi (fun _ : Fin n => P)

/-- The bounded-potential-outcome subclass used in the minimax converse. For [the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ), [the `boundedOutcomeClass` object being defined](goal). -/
def boundedOutcomeClass (d : ℕ) (β B L C c_f γ : ℝ) :
    Set (Measure (Obs d)) :=
  {P | ModelParameterDomain d β B L C c_f ∧ 1 < γ ∧
    ∃ (Pc : Measure (Completion d)) (_ : IsProbabilityMeasure Pc)
      (μ₁ e : (Fin d → ℝ) → ℝ),
      P = Pc.map observed ∧
      GlobalTailModel β B L C c_f γ Pc μ₁ e ∧
      (∀ᵐ ω ∂Pc, ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
        ω.2.2.2.1 ∈ ({0, B} : Set ℝ))}

/-- [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP), [the asserted conclusion holds](goal). -/

lemma boundedOutcomeClass_mem_model {d : ℕ} {β B L C c_f γ : ℝ}
    {P : Measure (Obs d)}
    (hP : P ∈ boundedOutcomeClass d β B L C c_f γ) :
    P ∈ ModelClass d β B L C c_f γ := by
  obtain ⟨hdom, hγ, Pc, hPc, μ₁, e, hobs, hmodel, _⟩ := hP
  exact ⟨hdom, hγ, Pc, hPc, μ₁, e, hobs, hmodel⟩

/-- The exact completion payload exported by the lower-pair construction
places either observed arm in the bounded-outcome subclass. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,a,c,x₀,hdom,hγ,ha,hc,hexact,hsupp,j), [the asserted conclusion holds](goal). -/
lemma lowerPair_mem_boundedOutcomeClass_of_exact
    {d n : ℕ} {β B L C c_f γ a c : ℝ} {x₀ : Fin d → ℝ}
    (hdom : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
    (ha : 0 < a) (hc : 0 < c)
    (hexact : LowerPairExactModelWitness d n β B L C c_f γ a c x₀)
    (hsupp : ∀ j : Bool,
      ∀ᵐ ω ∂lowerPairCompletion d n β B L γ a c x₀ j,
        ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
          ω.2.2.2.1 ∈ ({0, B} : Set ℝ))
    (j : Bool) :
    boundedLowerPair d β B L γ a c x₀ ha hc j n ∈
      boundedOutcomeClass d β B L C c_f γ := by
  unfold LowerPairExactModelWitness at hexact
  rcases hexact with ⟨hF, hT, hmodelF, hmodelT⟩
  cases j with
  | false =>
      refine ⟨hdom, hγ, lowerPairCompletion d n β B L γ a c x₀ false,
        hF, (fun x => B * pairSuccess false x₀ β B L a
          (c * oracleMesh d n β γ) x), radialPropensity x₀ γ, ?_,
        hmodelF, hsupp false⟩
      rfl
  | true =>
      refine ⟨hdom, hγ, lowerPairCompletion d n β B L γ a c x₀ true,
        hT, (fun x => B * pairSuccess true x₀ β B L a
          (c * oracleMesh d n β γ) x), radialPropensity x₀ γ, ?_,
        hmodelT, hsupp true⟩
      rfl

/-- [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP,x,hx), [the asserted conclusion holds](goal). -/

lemma responseOf_abs_le_on_cube {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) (hP : P ∈ ModelClass d β B L C c_f γ)
    (x : Fin d → ℝ) (hx : x ∈ cube d) : |responseOf P hP x| ≤ B := by
  have hPcopy := hP
  obtain ⟨hdom, hγ, Pc, hPc, μ, e, hEq, hmodel⟩ := hPcopy
  letI : IsProbabilityMeasure Pc := hPc
  rw [responseOf_eq_given_model_response P hP Pc μ e hEq hmodel x hx]
  exact holderResponse_abs_le_on_cube Pc μ e hdom hγ hmodel x hx

/-- The selected-cell estimator has one expected supremum-risk constant over
the entire compact overlap range. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma estimatorSupRisk_uniform_upper (d : ℕ)
    (β B L C c_f γ_min γ_max : ℝ)
    (hd : 0 < d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (hP : P ∈ ModelClass d β B L C c_f γ),
          estimatorSupRisk d n β B L C c_f γ P hP ≤
            ENNReal.ofReal (K * oracleRate d n β γ) := by
  obtain ⟨K, hK, n₀, hrisk⟩ := selectedMesh_uniform_equalCellCubeRisk
    d β B L C c_f γ_min γ_max (by omega) hβ hB hL hC hcf hγmin hγrange
  refine ⟨K, hK, n₀, ?_⟩
  intro n hn γ hγ P _ hP
  have hPcopy := hP
  obtain ⟨hparams, hγgt, Pc, hPc, μ, e, hEq, hmodel⟩ := hPcopy
  letI : IsProbabilityMeasure Pc := hPc
  have hb := hrisk n hn γ hγ Pc μ e hmodel P hEq
  unfold estimatorSupRisk
  calc
    (∫⁻ ω, ⨆ x, ⨆ (_hx : x ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω x - responseOf P hP x|
        ∂Measure.pi (fun _ : Fin n => P)) =
      ∫⁻ ω, ⨆ x, ⨆ (_hx : x ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω x - μ x|
        ∂Measure.pi (fun _ : Fin n => P) := by
      apply lintegral_congr
      intro ω
      apply iSup_congr
      intro x
      apply iSup_congr
      intro hx
      rw [responseOf_eq_given_model_response P hP Pc μ e hEq hmodel x hx]
    _ ≤ ENNReal.ofReal (K * oracleRate d n β γ) := hb

/-- A uniform bound for the concrete selected-cell estimator bounds the
corresponding supremum minimax risk. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,R,h), [the asserted conclusion holds](goal). -/
lemma supremumRisk_le_of_estimatorSupRisk_bound {d n : ℕ}
    {β B L C c_f γ : ℝ} {R : ℝ≥0∞}
    (h : ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
      (hP : P ∈ ModelClass d β B L C c_f γ),
      estimatorSupRisk d n β B L C c_f γ P hP ≤ R) :
    supremumRisk d n β B L C c_f γ ≤ R := by
  unfold supremumRisk Causalean.Stat.minimaxValueENNReal
    Causalean.Stat.worstCaseRiskENNReal
  let T : {T : (Fin n → Obs d) → (Fin d → ℝ) → ℝ // Measurable T} :=
    ⟨equalCellEstimator β B,
      measurable_pi_lambda _ fun x => equalCellEstimator_fixedPoint_measurable β B x⟩
  apply iInf_le_of_le T
  refine iSup_le fun P => ?_
  have hPcopy := P.2
  obtain ⟨_, _, Pc, hPc, _, _, hEq, _⟩ := hPcopy
  letI : IsProbabilityMeasure Pc := hPc
  letI : IsProbabilityMeasure P.1 := by
    rw [hEq]
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  simpa [supLossRisk, estimatorSupRisk, T] using h P.1 P.2

/-- Clipping the selected-cell estimator gives a sample-size-independent
upper bound for the supremum minimax risk. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,hB), [the asserted conclusion holds](goal). -/
lemma supremumRisk_le_two_mul (d n : ℕ) (β B L C c_f γ : ℝ)
    (hB : 0 < B) :
    supremumRisk d n β B L C c_f γ ≤ ENNReal.ofReal (2 * B) := by
  apply supremumRisk_le_of_estimatorSupRisk_bound
  intro P _ hP
  unfold estimatorSupRisk
  calc
    (∫⁻ ω, ⨆ x, ⨆ (_hx : x ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω x - responseOf P hP x|
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      ∫⁻ _ω : Fin n → Obs d, ENNReal.ofReal (2 * B)
        ∂Measure.pi (fun _ : Fin n => P) := by
      apply lintegral_mono
      intro ω
      refine iSup_le fun x => iSup_le fun hx => ?_
      exact ENNReal.ofReal_le_ofReal
        (equalCellEstimator_error_le_two_mul β B ω x (responseOf P hP x)
          hB.le (responseOf_abs_le_on_cube P hP x hx))
    _ = ENNReal.ofReal (2 * B) := by simp

/-- Pointwise loss on the bounded-potential-outcome subclass. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀,T,P), [the `boundedPointwiseLossRisk` object being defined](goal). -/
noncomputable def boundedPointwiseLossRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ)
    (T : {T : (Fin n → Obs d) → ℝ // Measurable T})
    (P : {P : Measure (Obs d) // P ∈ boundedOutcomeClass d β B L C c_f γ}) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal |T.1 ω - responseOf P.1 (boundedOutcomeClass_mem_model P.2) x₀|
    ∂Measure.pi (fun _ : Fin n => P.1)

/-- Pointwise minimax risk restricted to bounded potential outcomes. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀), [the `boundedPointwiseRisk` object being defined](goal). -/
noncomputable def boundedPointwiseRisk (d n : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (boundedPointwiseLossRisk d n β B L C c_f γ x₀)

/-- Restricting the model class to bounded potential outcomes can only reduce
the pointwise minimax risk. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀), [the asserted conclusion holds](goal). -/
lemma boundedPointwiseRisk_le_pointwiseRisk (d n : ℕ)
    (β B L C c_f γ : ℝ) (x₀ : Fin d → ℝ) :
    boundedPointwiseRisk d n β B L C c_f γ x₀ ≤
      pointwiseRisk d n β B L C c_f γ x₀ := by
  unfold boundedPointwiseRisk pointwiseRisk Causalean.Stat.minimaxValueENNReal
    Causalean.Stat.worstCaseRiskENNReal
  refine le_iInf fun T => ?_
  apply iInf_le_of_le T
  refine iSup_le fun P => ?_
  simpa [boundedPointwiseLossRisk, pointwiseLossRisk] using
    (le_iSup (fun P' : {P : Measure (Obs d) // P ∈ ModelClass d β B L C c_f γ} =>
      pointwiseLossRisk d n β B L C c_f γ x₀ T P')
      (⟨P.1, boundedOutcomeClass_mem_model P.2⟩ :
        {P : Measure (Obs d) // P ∈ ModelClass d β B L C c_f γ}))

/-- Evaluating a curve estimator at a point in the cube yields an admissible
scalar estimator whose loss is bounded by its spatial supremum loss. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,x₀,hx₀), [the asserted conclusion holds](goal). -/
lemma pointwiseRisk_le_supremumRisk (d n : ℕ)
    (β B L C c_f γ : ℝ) (x₀ : Fin d → ℝ) (hx₀ : x₀ ∈ cube d) :
    pointwiseRisk d n β B L C c_f γ x₀ ≤
      supremumRisk d n β B L C c_f γ := by
  unfold pointwiseRisk supremumRisk Causalean.Stat.minimaxValueENNReal
    Causalean.Stat.worstCaseRiskENNReal
  refine le_iInf fun T => ?_
  let T₀ : {T : (Fin n → Obs d) → ℝ // Measurable T} :=
    ⟨fun ω => T.1 ω x₀, T.2.eval⟩
  apply iInf_le_of_le T₀
  refine iSup_le fun P => ?_
  calc
    pointwiseLossRisk d n β B L C c_f γ x₀ T₀ P ≤
        supLossRisk d n β B L C c_f γ T P := by
      unfold pointwiseLossRisk supLossRisk
      apply lintegral_mono
      intro ω
      exact le_iSup_of_le x₀ (le_iSup_of_le hx₀ le_rfl)
    _ ≤ ⨆ P', supLossRisk d n β B L C c_f γ T P' := le_iSup _ P

/-- A pair in the bounded-outcome class with the standard KL budget gives an
ENNReal pointwise minimax lower bound.  Clipping arbitrary estimators makes
the finite-L¹ Le Cam lemma applicable without an integrability assumption. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,δ,x₀,hB,P₀,P₁,hP₀,hP₁,hx₀,hac,hllr,hkl,hδ,hsep), [the asserted conclusion holds](goal). -/
lemma boundedPointwiseRisk_lower_of_pair {d n : ℕ}
    {β B L C c_f γ δ : ℝ} (x₀ : Fin d → ℝ) (hB : 0 < B)
    (P₀ P₁ : Measure (Obs d)) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁]
    (hP₀ : P₀ ∈ boundedOutcomeClass d β B L C c_f γ)
    (hP₁ : P₁ ∈ boundedOutcomeClass d β B L C c_f γ)
    (hx₀ : x₀ ∈ cube d) (hac : P₀ ≪ P₁)
    (hllr : Integrable (llr P₀ P₁) P₀)
    (hkl : (n : ℝ) * (InformationTheory.klDiv P₀ P₁).toReal ≤ 1 / 8)
    (hδ : 0 ≤ δ)
    (hsep : δ ≤ |responseOf P₁ (boundedOutcomeClass_mem_model hP₁) x₀ -
      responseOf P₀ (boundedOutcomeClass_mem_model hP₀) x₀|) :
    ENNReal.ofReal ((1 / 8 : ℝ) * δ) ≤
      boundedPointwiseRisk d n β B L C c_f γ x₀ := by
  let θ₀ : {P : Measure (Obs d) //
      P ∈ boundedOutcomeClass d β B L C c_f γ} := ⟨P₀, hP₀⟩
  let θ₁ : {P : Measure (Obs d) //
      P ∈ boundedOutcomeClass d β B L C c_f γ} := ⟨P₁, hP₁⟩
  apply Causalean.Stat.le_minimaxValueENNReal_of_two_point θ₀ θ₁
  intro T
  let t₀ := responseOf P₀ (boundedOutcomeClass_mem_model hP₀) x₀
  let t₁ := responseOf P₁ (boundedOutcomeClass_mem_model hP₁) x₀
  have ht₀ : |t₀| ≤ B := responseOf_abs_le_on_cube P₀
    (boundedOutcomeClass_mem_model hP₀) x₀ hx₀
  have ht₁ : |t₁| ≤ B := responseOf_abs_le_on_cube P₁
    (boundedOutcomeClass_mem_model hP₁) x₀ hx₀
  let clip : ℝ → ℝ := fun z =>
    (Set.projIcc (-B) B (by linarith : -B ≤ B) z : ℝ)
  let Tc : (Fin n → Obs d) → ℝ := fun ω => clip (T.1 ω)
  have hTc : Measurable Tc := by
    change Measurable (fun ω => max (-B) (min B (T.1 ω)))
    exact measurable_const.max (measurable_const.min T.2)
  have hclip_t₀ : clip t₀ = t₀ := by
    rw [show clip t₀ = max (-B) (min B t₀) by rfl,
      min_eq_right (abs_le.mp ht₀).2, max_eq_right (abs_le.mp ht₀).1]
  have hclip_t₁ : clip t₁ = t₁ := by
    rw [show clip t₁ = max (-B) (min B t₁) by rfl,
      min_eq_right (abs_le.mp ht₁).2, max_eq_right (abs_le.mp ht₁).1]
  have hcontract₀ : ∀ ω, |Tc ω - t₀| ≤ |T.1 ω - t₀| := by
    intro ω
    have hc := Set.abs_projIcc_sub_projIcc
      (a := -B) (b := B) (c := T.1 ω) (d := t₀) (by linarith : -B ≤ B)
    simpa [Tc, clip, hclip_t₀] using hc
  have hcontract₁ : ∀ ω, |Tc ω - t₁| ≤ |T.1 ω - t₁| := by
    intro ω
    have hc := Set.abs_projIcc_sub_projIcc
      (a := -B) (b := B) (c := T.1 ω) (d := t₁) (by linarith : -B ≤ B)
    simpa [Tc, clip, hclip_t₁] using hc
  have hint₀ : Integrable (fun ω : Fin n → Obs d => |Tc ω - t₀|)
      (Measure.pi (fun _ : Fin n => P₀)) := by
    apply Integrable.of_bound (hTc.sub measurable_const).abs.aestronglyMeasurable (2 * B)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    have hc := (Set.projIcc (-B) B (by linarith : -B ≤ B) (T.1 ω)).property
    dsimp [Tc, clip]
    rw [abs_le]
    constructor <;> nlinarith [hc.1, hc.2, (abs_le.mp ht₀).1, (abs_le.mp ht₀).2]
  have hint₁ : Integrable (fun ω : Fin n → Obs d => |Tc ω - t₁|)
      (Measure.pi (fun _ : Fin n => P₁)) := by
    apply Integrable.of_bound (hTc.sub measurable_const).abs.aestronglyMeasurable (2 * B)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    have hc := (Set.projIcc (-B) B (by linarith : -B ≤ B) (T.1 ω)).property
    dsimp [Tc, clip]
    rw [abs_le]
    constructor <;> nlinarith [hc.1, hc.2, (abs_le.mp ht₁).1, (abs_le.mp ht₁).2]
  have hreal := Causalean.Stat.Minimax.leCam_two_point_L1_lower
    (1 / 8 : ℝ) (by norm_num) n P₀ P₁ t₀ t₁ δ hac hllr hkl hδ
      (by simpa [t₀, t₁, abs_sub_comm] using hsep) Tc hTc hint₀ hint₁
  have hlin₀ := ofReal_integral_eq_lintegral_ofReal hint₀
    (ae_of_all _ fun _ => abs_nonneg _)
  have hlin₁ := ofReal_integral_eq_lintegral_ofReal hint₁
    (ae_of_all _ fun _ => abs_nonneg _)
  have hclip : ENNReal.ofReal ((1 / 8 : ℝ) * δ) ≤
      max (∫⁻ ω, ENNReal.ofReal |Tc ω - t₀| ∂Measure.pi (fun _ : Fin n => P₀))
        (∫⁻ ω, ENNReal.ofReal |Tc ω - t₁| ∂Measure.pi (fun _ : Fin n => P₁)) := by
    rw [← hlin₀, ← hlin₁, ← ENNReal.ofReal_max]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmono₀ :
      (∫⁻ ω, ENNReal.ofReal |Tc ω - t₀| ∂Measure.pi (fun _ : Fin n => P₀)) ≤
        boundedPointwiseLossRisk d n β B L C c_f γ x₀ T θ₀ := by
    unfold boundedPointwiseLossRisk
    simpa [θ₀, t₀] using
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hcontract₀ ω))
  have hmono₁ :
      (∫⁻ ω, ENNReal.ofReal |Tc ω - t₁| ∂Measure.pi (fun _ : Fin n => P₁)) ≤
        boundedPointwiseLossRisk d n β B L C c_f γ x₀ T θ₁ := by
    unfold boundedPointwiseLossRisk
    simpa [θ₁, t₁] using
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hcontract₁ ω))
  exact hclip.trans (max_le_max hmono₀ hmono₁)

/-- The explicit bounded Bernoulli pair gives the oracle-rate pointwise
converse at every positive sample size. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,x₀,hd,hβ,hγ,hB,hL,hC,hcf,hx₀), [the asserted conclusion holds](goal). -/
lemma boundedPointwiseRisk_oracle_lower (d : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ) (hd : 0 < d) (hβ : 1 < β) (hγ : 1 < γ)
    (hB : 0 < B) (hL : 0 < L) (hC : 1 ≤ C)
    (hcf : 0 < c_f ∧ c_f ≤ 1) (hx₀ : x₀ ∈ cube d) :
    ∃ cγ : ℝ, 0 < cγ ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (cγ * oracleRate d n β γ) ≤
        boundedPointwiseRisk d n β B L C c_f γ x₀ := by
  obtain ⟨a, c, c₀, ha, hc, hc₀, hadm, hall⟩ :=
    boundedLowerPair_spec_exact_completion d β B L C c_f γ x₀
      hd hβ hγ hB hL hC hcf hx₀
  refine ⟨c₀ / 8, by positivity, ?_⟩
  intro n hn
  let P₀ := boundedLowerPair d β B L γ a c x₀ ha hc false n
  let P₁ := boundedLowerPair d β B L γ a c x₀ ha hc true n
  obtain ⟨hP₀model, hP₁model, hsupp, hac, hllr, hkl, hsep, hexact⟩ := hall n hn
  have hdom : ModelParameterDomain d β B L C c_f :=
    ⟨Nat.succ_le_iff.mpr hd, hβ, hB, hL, hC, hcf⟩
  have hP₀bounded : P₀ ∈ boundedOutcomeClass d β B L C c_f γ := by
    exact lowerPair_mem_boundedOutcomeClass_of_exact hdom hγ ha hc hexact hsupp false
  have hP₁bounded : P₁ ∈ boundedOutcomeClass d β B L C c_f γ := by
    exact lowerPair_mem_boundedOutcomeClass_of_exact hdom hγ ha hc hexact hsupp true
  have hexact' := hexact
  unfold LowerPairExactModelWitness at hexact'
  obtain ⟨hPc₀, hPc₁, -, -⟩ := hexact'
  letI : IsProbabilityMeasure P₀ := by
    dsimp [P₀, boundedLowerPair]
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure P₁ := by
    dsimp [P₁, boundedLowerPair]
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  have hsep' : c₀ * oracleRate d n β γ ≤
      |responseOf P₁ (boundedOutcomeClass_mem_model hP₁bounded) x₀ -
        responseOf P₀ (boundedOutcomeClass_mem_model hP₀bounded) x₀| := by
    simpa [P₀, P₁] using hsep
  have hlower := boundedPointwiseRisk_lower_of_pair x₀ hB P₀ P₁
    hP₀bounded hP₁bounded hx₀ hac hllr hkl
    (mul_nonneg hc₀.le (by unfold oracleRate oracleMesh; positivity)) hsep'
  convert hlower using 1
  congr 1
  ring

-- @node: thm:adaptive-minimax
/-- One count-selected estimator, whose type takes `n,d,β,B` and the data but
no overlap exponent or class constants, achieves logarithm-free expected
supremum risk uniformly on a compact overlap range. A bounded Bernoulli pair
provides the pointwise minimax converse. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
theorem adaptive_minimax_rate (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 0 < d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    (∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (hP : P ∈ ModelClass d β B L C c_f γ),
          estimatorSupRisk d n β B L C c_f γ P hP ≤
            ENNReal.ofReal (K * oracleRate d n β γ)) ∧
    (∀ γ : ℝ, 1 < γ → ∀ x₀ ∈ cube d,
      ∃ cγ Kγ : ℝ, 0 < cγ ∧ cγ ≤ Kγ ∧
        ∀ n : ℕ, 1 ≤ n →
          ENNReal.ofReal (cγ * oracleRate d n β γ) ≤
            boundedPointwiseRisk d n β B L C c_f γ x₀ ∧
          boundedPointwiseRisk d n β B L C c_f γ x₀ ≤
            pointwiseRisk d n β B L C c_f γ x₀ ∧
          pointwiseRisk d n β B L C c_f γ x₀ ≤
            supremumRisk d n β B L C c_f γ ∧
          supremumRisk d n β B L C c_f γ ≤
            ENNReal.ofReal (Kγ * oracleRate d n β γ)) := by
  constructor
  · exact estimatorSupRisk_uniform_upper d β B L C c_f γ_min γ_max
      hd hβ hB hL hC hcf hγmin hγrange
  · intro γ hγ x₀ hx₀
    obtain ⟨cγ, hcγ, hlower⟩ := boundedPointwiseRisk_oracle_lower
      d β B L C c_f γ x₀ hd hβ hγ hB hL hC hcf hx₀
    let γlo : ℝ := (γ + 1) / 2
    let γhi : ℝ := γ + 1
    have hγlo : 1 < γlo := by dsimp [γlo]; linarith
    have hγrange' : γlo < γhi := by dsimp [γlo, γhi]; linarith
    obtain ⟨K, hK, n₀, hupper⟩ := estimatorSupRisk_uniform_upper
      d β B L C c_f γlo γhi hd hβ hB hL hC hcf hγlo hγrange'
    let N : ℕ := max n₀ 1
    let q : ℝ := (N : ℝ) ^ (-2 : ℝ)
    have hN : 1 ≤ N := by exact le_max_right _ _
    have hq : 0 < q := by dsimp [q]; positivity
    let Ksmall : ℝ := (2 * B) / q
    have hKsmall : 0 < Ksmall := by dsimp [Ksmall]; positivity
    let Kγ : ℝ := max cγ (max K Ksmall)
    refine ⟨cγ, Kγ, hcγ, le_max_left _ _, ?_⟩
    intro n hn
    have hrate : 0 < oracleRate d n β γ := by
      unfold oracleRate oracleMesh
      positivity
    have hminimaxUpper : supremumRisk d n β B L C c_f γ ≤
        ENNReal.ofReal (Kγ * oracleRate d n β γ) := by
      by_cases hnlarge : n₀ ≤ n
      · have hγmem : γ ∈ adaptationRange γlo γhi ⟨hγlo, hγrange'⟩ := by
          change γ ∈ Set.Icc γlo γhi
          constructor <;> dsimp [γlo, γhi] <;> linarith
        have hest := supremumRisk_le_of_estimatorSupRisk_bound
          (hupper n hnlarge γ hγmem)
        exact hest.trans (ENNReal.ofReal_le_ofReal <|
          mul_le_mul_of_nonneg_right
            ((le_max_left K Ksmall).trans (le_max_right cγ (max K Ksmall)))
            hrate.le)
      · have hnN : n ≤ N := by
          have hnn₀ : n < n₀ := Nat.lt_of_not_ge hnlarge
          exact hnn₀.le.trans (le_max_left _ _)
        have hq_le_inv : q ≤ (n : ℝ) ^ (-2 : ℝ) := by
          apply Real.rpow_le_rpow_of_nonpos
          · exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt hn)
          · exact_mod_cast hnN
          · norm_num
        have hq_le_rate : q ≤ oracleRate d n β γ :=
          hq_le_inv.trans (inverseSquare_le_oracleRate d n β γ hn
            (by linarith) hγ)
        have htwo : 2 * B ≤ Ksmall * oracleRate d n β γ := by
          calc
            2 * B = Ksmall * q := by
              dsimp [Ksmall]
              field_simp
            _ ≤ Ksmall * oracleRate d n β γ :=
              mul_le_mul_of_nonneg_left hq_le_rate hKsmall.le
        have hsmall_le : Ksmall ≤ Kγ :=
          (le_max_right K Ksmall).trans (le_max_right cγ (max K Ksmall))
        exact (supremumRisk_le_two_mul d n β B L C c_f γ hB).trans
          (ENNReal.ofReal_le_ofReal <|
            htwo.trans (mul_le_mul_of_nonneg_right hsmall_le hrate.le))
    exact ⟨hlower n hn,
      boundedPointwiseRisk_le_pointwiseRisk d n β B L C c_f γ x₀,
      pointwiseRisk_le_supremumRisk d n β B L C c_f γ x₀ hx₀,
      hminimaxUpper⟩
end CausalSmith.Stat.WeakOverlap
