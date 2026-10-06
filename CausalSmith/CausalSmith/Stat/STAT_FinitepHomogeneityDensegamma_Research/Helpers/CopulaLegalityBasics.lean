module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaPriors
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.FrameBounds
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scales

/-! Finite-moment homogeneity testing: Helpers/CopulaLegalityBasics. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Legalitya: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K). [This is the stated defined object](goal). -/
def legalityA (v : Params) (K : ℕ) : ℝ := (K:ℝ)^(-v.α)/16
/-- Legalityb: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K). [This is the stated defined object](goal). -/
def legalityB (v : Params) (K : ℕ) : ℝ := (K:ℝ)^(-v.β)/256
/-- Legalityrarity: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K). [This is the stated defined object](goal). -/
def legalityRarity (v : Params) (K : ℕ) : ℝ := (16*legalityB v K)^(1/qExp v)
/-- Legalitymagnitude: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K). [This is the stated defined object](goal). -/
def legalityMagnitude (v : Params) (K : ℕ) : ℝ := legalityRarity v K^(-1/v.p)
/-- Legalityranks: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K), [the M parameter](hyp:M). [This is the stated defined object](goal). -/
def LegalityRanks (v : Params) (K M : ℕ) : Prop :=
  (∃ k, K=2^k) ∧ (∃ m, M=2^m) ∧ 16*M ≤ K ∧ 2 ≤ M ∧ (M:ℝ) ≤ (K:ℝ)^(sumReg v/v.γ)
/-- Copulaeffectconclusion: the displayed mathematical construction or bound. This statement assumes [the v parameter](hyp:v), [the K parameter](hyp:K), [the M parameter](hyp:M), [the idx parameter](hyp:idx), [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def CopulaEffectConclusion (v : Params) (K M : ℕ) (idx : CopulaIndex K M) (law : ObservedLaw) : Prop :=
  (∀ x : unitInterval, law.tau x = -(2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2))*smoothedTent K M idx.1 x) ∧
  meanTau law=0 ∧ (2:ℝ)^(-17:ℤ)*(K:ℝ)^(-sumReg v) ≤ hetDist law ∧
  hetDist law ≤ (2:ℝ)^(-14:ℤ)*(K:ℝ)^(-sumReg v) ∧ hetDist law < d0
/-- Positive-rank power tunings give admissible amplitudes and interior rare marks. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_tuning_bounds
lemma legality_tuning_bounds (v : Params) (hv : v.Valid) (K : ℕ) (hK : 1 ≤ K) :
    (0 < legalityA v K ∧ legalityA v K ≤ 1/16) ∧
    (0 < legalityB v K ∧ legalityB v K ≤ 1/256) ∧
    (0 < legalityRarity v K ∧ legalityRarity v K < 1) ∧
    0 < legalityMagnitude v K := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < K := by linarith
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) (by linarith [hv.1.1])
  have ha : 0 < legalityA v K ∧ legalityA v K ≤ 1/16 := by
    unfold legalityA
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [hv.2.1.1])) (by norm_num)
  have hb : 0 < legalityB v K ∧ legalityB v K ≤ 1/256 := by
    unfold legalityB
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [hv.2.2.1.1])) (by norm_num)
  have he : 0 < 16*legalityB v K := by linarith [hb.1]
  have hr : 0 < legalityRarity v K ∧ legalityRarity v K < 1 := by
    unfold legalityRarity
    exact ⟨Real.rpow_pos_of_pos he _,
      Real.rpow_lt_one he.le (by linarith [hb.2]) (by positivity)⟩
  exact ⟨ha, hb, hr, Real.rpow_pos_of_pos hr.1 _⟩

/-- The tail tuning has unit raw moment and the same marked-mean amplitude as the bounded tuning. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_tuning_identities
lemma legality_tuning_identities (v : Params) (hv : v.Valid) (K : ℕ) (hK : 1 ≤ K) :
    legalityRarity v K * legalityMagnitude v K ^ v.p = 1 ∧
    legalityRarity v K * legalityMagnitude v K * (1/16) = legalityB v K := by
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) hp
  have hr := (legality_tuning_bounds v hv K hK).2.2.1.1
  have hb := (legality_tuning_bounds v hv K hK).2.1.1
  constructor
  · simp only [legalityMagnitude, ← Real.rpow_mul hr.le]
    rw [show (-1/v.p)*v.p = -1 by field_simp, Real.rpow_neg_one]
    exact mul_inv_cancel₀ hr.ne'
  · have hexp : 1 + -1/v.p = qExp v := by unfold qExp; field_simp; ring
    calc
      _ = (legalityRarity v K)^(qExp v)*(1/16) := by
        rw [legalityMagnitude, ← hexp, Real.rpow_add hr, Real.rpow_one]
      _ = (16*legalityB v K)*(1/16) := by
        rw [legalityRarity, ← Real.rpow_mul (by positivity),
          div_mul_cancel₀ 1 hq.ne', Real.rpow_one]
      _ = _ := by ring

/-- All three atoms of a normalized table row give raw moment ε L^p. This statement assumes [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: tableArm_raw_moment
lemma tableArm_raw_moment (ξ υ ζ : unitInterval → ℝ) (ε L p : ℝ)
    (h : TableValid ξ υ ζ ε L) (hp : 0 < p) (a : Bool) (x : unitInterval) :
    (∫⁻ y, ENNReal.ofReal (|y|^p) ∂tableArm ξ υ ζ ε L h a x) =
      ENNReal.ofReal (ε*L^p) := by
  have hd := table_row_den_pos ξ υ ζ ε L h a x
  have hw (mark : Option Bool) :
      0 ≤ 2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x) :=
    div_nonneg (mul_nonneg (by norm_num) (h.2.2.2.2.2.2 x (a,mark))) hd.le
  change (∫⁻ y, ENNReal.ofReal (|y|^p) ∂tableArmMeasure ξ υ ζ ε L a x) = _
  rw [tableArmMeasure, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp only [Fintype.sum_option, Fintype.sum_bool, markValue, signVal,
    Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, abs_neg,
    abs_of_pos h.2.2.2.2.2.1, abs_zero, Real.zero_rpow hp.ne', ENNReal.ofReal_zero,
    mul_zero, zero_add]
  simp only [signVal] at hw hd
  rw [← ENNReal.ofReal_mul (hw (some true)), ← ENNReal.ofReal_mul (hw (some false)),
    ← ENNReal.ofReal_add
      (mul_nonneg (hw (some true)) (Real.rpow_nonneg h.2.2.2.2.2.1.le _))
      (mul_nonneg (hw (some false)) (Real.rpow_nonneg h.2.2.2.2.2.1.le _))]
  congr 1
  simp only [markedTable, signVal, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, mul_one, mul_neg_one]
  field_simp
  ring

/-- The exact table effect cancels the fine coefficient product and leaves the deterministic correction. [This is the stated conclusion](goal). -/
-- @node: copulaLaw_tau_formula
lemma copulaLaw_tau_formula (v : Params) (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (ν : Bool) (idx : CopulaIndex K M)
    (x : unitInterval) :
    (copulaLaw ν v K M a u ε L idx).tau x =
      2*ε*L*copulaT ν K M a u idx x := by
  have ht := copula_table_valid n K M a u ε L h ν idx
  have hd : 1-(copulaXi K M a idx x)^2 ≠ 0 := by
    have hx := abs_lt.mp (ht.2.2.2.1 x)
    nlinarith
  simp only [copulaLaw, tableObservedLaw, dif_pos ht, ContinuousMap.coe_mk, tableTau,
    copulaZeta]
  field_simp
  ring

/-- A valid copula support law has the exact raw arm moment, before any model-membership argument. This statement assumes [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: copulaLaw_raw_moment
lemma copulaLaw_raw_moment (v : Params) (n K M : ℕ) (a u ε L p : ℝ)
    (h : CopulaDomain n K M a u ε L) (hp : 0 < p) (ν : Bool)
    (idx : CopulaIndex K M) (arm : Bool) (x : unitInterval) :
    (∫⁻ y, ENNReal.ofReal (|y|^p) ∂(copulaLaw ν v K M a u ε L idx).Q arm x) =
      ENNReal.ofReal (ε*L^p) := by
  have ht := copula_table_valid n K M a u ε L h ν idx
  simpa only [copulaLaw, tableObservedLaw, dif_pos ht] using
    tableArm_raw_moment _ _ _ ε L p ht hp arm x

/-- Both prescribed tunings satisfy the complete public copula input domain. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: legality_copula_domains
lemma legality_copula_domains (v : Params) (hv : v.Valid) (K M : ℕ)
    (h : LegalityRanks v K M) :
    CopulaDomain 2 K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K) ∧
    CopulaDomain 2 K M (legalityA v K) (2*legalityB v K) (1/2) 1 := by
  obtain ⟨hk, hm, hKM, hM, hreg⟩ := h
  have hK : 1 ≤ K := by omega
  obtain ⟨ha, hb, hr, hL⟩ := legality_tuning_bounds v hv K hK
  constructor
  · exact ⟨by norm_num, hk, hm, hKM, hM, ha, by norm_num, hr, hL⟩
  · refine ⟨by norm_num, hk, hm, hKM, hM, ha, ?_, by norm_num, by norm_num⟩
    constructor <;> linarith [hb.1, hb.2]

/-- Tail and bounded tunings realize exactly the same deterministic original mean effect. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: legality_effect_formulas
lemma legality_effect_formulas (v : Params) (hv : v.Valid) (K M : ℕ)
    (h : LegalityRanks v K M) (idx : CopulaIndex K M) :
    (∀ x : unitInterval,
      (copulaLaw true v K M (legalityA v K) (1/16) (legalityRarity v K)
        (legalityMagnitude v K) idx).tau x =
        -(2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2))*smoothedTent K M idx.1 x) ∧
    (∀ x : unitInterval,
      (copulaLaw true v K M (legalityA v K) (2*legalityB v K) (1/2) 1 idx).tau x =
        -(2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2))*smoothedTent K M idx.1 x) := by
  have hK : 1 ≤ K := by have := h.2.2.1; have := h.2.2.2.1; omega
  obtain ⟨ht, hb⟩ := legality_copula_domains v hv K M h
  have htune := (legality_tuning_identities v hv K hK).2
  constructor
  · intro x
    rw [copulaLaw_tau_formula v 2 K M _ _ _ _ ht true idx x]
    simp only [copulaT, ↓reduceIte]
    calc
      _ = -(2*legalityA v K*(legalityRarity v K*legalityMagnitude v K*(1/16))*
        kappa0/(1-legalityA v K^2))*smoothedTent K M idx.1 x := by ring
      _ = _ := by rw [htune]
  · intro x
    rw [copulaLaw_tau_formula v 2 K M _ _ _ _ hb true idx x]
    simp only [copulaT, ↓reduceIte]
    ring

/-- The two tunings realize the exact unit p-moment and half-unit second moment armwise. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: legality_arm_moments
lemma legality_arm_moments (v : Params) (hv : v.Valid) (K M : ℕ)
    (h : LegalityRanks v K M) (ν : Bool) (idx : CopulaIndex K M) :
    (∀ arm : Bool, ∀ x : unitInterval,
      ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂(copulaLaw ν v K M (legalityA v K) (1/16)
        (legalityRarity v K) (legalityMagnitude v K) idx).Q arm x = 1) ∧
    (∀ arm : Bool, ∀ x : unitInterval,
      ∫⁻ y, ENNReal.ofReal (|y|^(2:ℝ)) ∂(copulaLaw ν v K M (legalityA v K)
        (2*legalityB v K) (1/2) 1 idx).Q arm x = 1/2) := by
  have hK : 1 ≤ K := by have := h.2.2.1; have := h.2.2.2.1; omega
  obtain ⟨ht, hb⟩ := legality_copula_domains v hv K M h
  constructor
  · intro arm x
    rw [copulaLaw_raw_moment v 2 K M _ _ _ _ v.p ht (by linarith [hv.1.1]),
      (legality_tuning_identities v hv K hK).1, ENNReal.ofReal_one]
  · intro arm x
    rw [copulaLaw_raw_moment v 2 K M _ _ _ _ 2 hb (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]

/-- Rank-scaled amplitudes cancel their matching Hölder powers exactly. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_amplitude_power_identities
lemma legality_amplitude_power_identities (v : Params) (K : ℕ) (hK : 0 < K) :
    legalityA v K*(K:ℝ)^v.α = 1/16 ∧
    legalityB v K*(K:ℝ)^v.β = 1/256 := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  constructor <;> simp only [legalityA, legalityB] <;>
    rw [div_mul_eq_mul_div, ← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]

/-- The null table has zero effect and its baseline is the marked frame field. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: copulaLaw_null_primitives
lemma copulaLaw_null_primitives (v : Params) (K M : ℕ) (a u ε L : ℝ)
    (hd : CopulaDomain 2 K M a u ε L) (idx : CopulaIndex K M)
    (x : unitInterval) :
    (copulaLaw false v K M a u ε L idx).e x = (1+copulaXi K M a idx x)/2 ∧
    (copulaLaw false v K M a u ε L idx).m0 x = ε*L*u*frameField K (fun i => signVal (idx.2 i).2) x ∧
    (copulaLaw false v K M a u ε L idx).tau x = 0 := by
  have ht := copula_table_valid 2 K M a u ε L hd false idx
  have hx := abs_lt.mp (ht.2.2.2.1 x)
  have hden : 1-copulaXi K M a idx x ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [copulaLaw, tableObservedLaw, dif_pos ht, ContinuousMap.coe_mk, tableProp]
  · simp only [copulaLaw, tableObservedLaw, dif_pos ht, ContinuousMap.coe_mk, tableM0,
      copulaZeta, copulaT, Bool.false_eq_true, ↓reduceIte, neg_zero, zero_mul, zero_div,
      mul_zero, add_zero]
    rw [show copulaUpsilon K M u idx x-copulaXi K M a idx x*copulaUpsilon K M u idx x =
      copulaUpsilon K M u idx x*(1-copulaXi K M a idx x) by ring,
      mul_div_assoc, mul_div_cancel_right₀ _ hden]
    simp only [copulaUpsilon]
    ring
  · rw [copulaLaw_tau_formula v 2 K M a u ε L hd false idx x]
    simp [copulaT]

/-- Every null support satisfies all original primitive predicates under either prescribed mark tuning. This statement assumes [the hv condition](hyp:hv), [the hr condition](hyp:hr), [the hd condition](hyp:hd), [the hmean condition](hyp:hmean), [the hmoment condition](hyp:hmoment). [This is the stated conclusion](goal). -/
-- @node: legality_null_inNull
lemma legality_null_inNull (v : Params) (hv : v.Valid) (K M : ℕ)
    (hr : LegalityRanks v K M) (u ε L : ℝ)
    (hd : CopulaDomain 2 K M (legalityA v K) u ε L)
    (hmean : ε*L*u = legalityB v K) (hmoment : ε*L^v.p ≤ 10)
    (idx : CopulaIndex K M) :
    InNull v (copulaLaw false v K M (legalityA v K) u ε L idx) := by
  let law := copulaLaw false v K M (legalityA v K) u ε L idx
  have hK : 0 < K := by have := hr.2.2.1; have := hr.2.2.2.1; omega
  have ht := copula_table_valid 2 K M (legalityA v K) u ε L hd false idx
  have hform := copulaLaw_null_primitives v K M (legalityA v K) u ε L hd idx
  have he (x : unitInterval) : law.e x = (1+copulaXi K M (legalityA v K) idx x)/2 := (hform x).1
  have hm (x : unitInterval) : law.m0 x = legalityB v K*frameField K (fun i => signVal (idx.2 i).2) x := by
    rw [(hform x).2.1, hmean]
  have hz (x : unitInterval) : law.tau x = 0 := (hform x).2.2
  have hsign (b : Bool) : |signVal b| ≤ 1 := by cases b <;> norm_num [signVal]
  have hα := frame_holder_bound K hK v.α hv.2.1 (fun i => signVal (idx.2 i).1) (fun i => hsign _)
  have hβ := frame_holder_bound K hK v.β hv.2.2.1 (fun i => signVal (idx.2 i).2) (fun i => hsign _)
  obtain ⟨ha, hb, _, _⟩ := legality_tuning_bounds v hv K (by omega)
  obtain ⟨hap, hbp⟩ := legality_amplitude_power_identities v K hK
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hxi (x : unitInterval) : |copulaXi K M (legalityA v K) idx x| ≤ 1/8 := by
    simp only [copulaXi, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ legalityA v K*Real.sqrt 2 := mul_le_mul_of_nonneg_left (hα.1 x) ha.1.le
      _ ≤ (1/16:ℝ)*2 := mul_le_mul ha.2 hsqrt (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hbase (x : unitInterval) : |law.m0 x| ≤ 1/2 := by
    rw [hm, abs_mul, abs_of_pos hb.1]
    calc
      _ ≤ legalityB v K*Real.sqrt 2 := mul_le_mul_of_nonneg_left (hβ.1 x) hb.1.le
      _ ≤ (1/256:ℝ)*2 := mul_le_mul hb.2 hsqrt (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have hover (x : unitInterval) : 1/4 ≤ law.e x ∧ law.e x ≤ 3/4 := by
    rw [he]
    have hx := abs_le.mp (hxi x)
    constructor <;> linarith
  refine ⟨?_, hover, ?_, ?_, ?_, hbase, ?_, ?_, ?_⟩
  · simp only [UniformDesign, covariateLaw, copulaLaw, tableObservedLaw, dif_pos ht]
    rw [tableLaw_eq_compProd _ _ _ ε L ht]
    letI : IsProbabilityMeasure design := by change IsProbabilityMeasure (volume : Measure unitInterval); infer_instance
    letI := recordKernel_markov _ (measurable_tableProp _ _ _ ε L ht) _
      (table_certificate _ _ _ ε L ht).2.2.1
      (tableArm_markov _ _ _ ε L ht)
    exact Measure.fst_compProd _ _
  · refine ⟨law.e.continuous, ?_, ?_⟩
    · intro x; rw [abs_of_nonneg (by linarith [(hover x).1])]; linarith [(hover x).2]
    · intro x z
      rw [he, he, show (1+copulaXi K M (legalityA v K) idx x)/2-
          (1+copulaXi K M (legalityA v K) idx z)/2 =
          (legalityA v K/2)*(frameField K (fun i => signVal (idx.2 i).1) x-
            frameField K (fun i => signVal (idx.2 i).1) z) by simp only [copulaXi]; ring,
        abs_mul, abs_of_pos (div_pos ha.1 (by norm_num) : 0 < legalityA v K/2)]
      calc
        _ ≤ (legalityA v K/2)*(4*(K:ℝ)^v.α*|(x:ℝ)-(z:ℝ)|^v.α) :=
          mul_le_mul_of_nonneg_left (hα.2 x z) (div_nonneg ha.1.le (by norm_num))
        _ = (1/8:ℝ)*|(x:ℝ)-(z:ℝ)|^v.α := by
          calc
            _ = 2*(legalityA v K*(K:ℝ)^v.α)*|(x:ℝ)-(z:ℝ)|^v.α := by ring
            _ = _ := by rw [hap]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · refine ⟨law.m0.continuous, ?_, ?_⟩
    · intro x; linarith [hbase x]
    · intro x z
      rw [hm, hm, ← mul_sub, abs_mul, abs_of_pos hb.1]
      calc
        _ ≤ legalityB v K*(4*(K:ℝ)^v.β*|(x:ℝ)-(z:ℝ)|^v.β) :=
          mul_le_mul_of_nonneg_left (hβ.2 x z) hb.1.le
        _ = (1/64:ℝ)*|(x:ℝ)-(z:ℝ)|^v.β := by
          calc
            _ = 4*(legalityB v K*(K:ℝ)^v.β)*|(x:ℝ)-(z:ℝ)|^v.β := by ring
            _ = _ := by rw [hbp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · refine ⟨law.tau.continuous, ?_, ?_⟩
    · intro x; rw [hz]; norm_num
    · intro x z; rw [hz, hz]; simp only [sub_self, abs_zero]; positivity
  · intro x; rw [hz]; norm_num
  · intro arm
    filter_upwards [] with x
    rw [copulaLaw_raw_moment v 2 K M _ _ ε L v.p hd (by linarith [hv.1.1]) false idx arm x]
    exact (ENNReal.ofReal_le_ofReal hmoment).trans_eq (by norm_num)
  · exact ⟨0, by norm_num, by norm_num, hz⟩

/-- A valid table with unit marks is supported on the unit outcome envelope. This statement assumes [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: tableObservedLaw_unit_bounded
lemma tableObservedLaw_unit_bounded (ξ υ ζ : unitInterval → ℝ) (ε : ℝ)
    (ht : TableValid ξ υ ζ ε 1) : BoundedOutcome (tableObservedLaw ξ υ ζ ε 1) := by
  simp only [BoundedOutcome, tableObservedLaw, dif_pos ht]
  have hp := (table_certificate ξ υ ζ ε 1 ht).1
  letI := hp
  rw [← measure_univ (μ := tableLaw ξ υ ζ ε 1)]
  rw [tableLaw, Measure.bind_apply (by unfold Y; measurability : MeasurableSet {o : Record | |Y o| ≤ 1})
    (measurable_table_record_atoms ξ υ ζ ε 1 ht).aemeasurable,
    Measure.bind_apply MeasurableSet.univ (measurable_table_record_atoms ξ υ ζ ε 1 ht).aemeasurable]
  apply lintegral_congr
  intro x
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro cat _
  rw [Measure.dirac_apply' _ (by unfold Y; measurability : MeasurableSet {o : Record | |Y o| ≤ 1}),
    Measure.dirac_apply' _ MeasurableSet.univ]
  rcases cat with ⟨a, mark⟩
  cases mark with
  | none => simp [Y, markValue]
  | some b => cases b <;> norm_num [Y, markValue, signVal]


end CausalSmith.Stat.FinitepHomogeneityDensegamma
