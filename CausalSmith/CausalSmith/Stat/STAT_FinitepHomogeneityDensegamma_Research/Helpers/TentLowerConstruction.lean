module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryTentLegality
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentIntegrals
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.EffectDistance
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairedTent
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentSmoothness
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCausalNonempty
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCopulaFrameLegality
public import Causalean.Stat.Minimax.Mixture.Iid
public import Causalean.Stat.Minimax.Mixture.SignOverlap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite-moment homogeneity testing: Helpers/TentLowerConstruction. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The prescribed rarity is an interior probability and the mark magnitude is positive. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_mark_parameters
lemma tent_mark_parameters (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (0 < tentRarity n v ∧ tentRarity n v < 1) ∧ 0 < tentMagnitude n v := by
  obtain ⟨hh, hh1⟩ := tentH_bounds v hv n hn
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) hp
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  refine ⟨⟨Real.rpow_pos_of_pos hh _, ?_⟩, Real.rpow_pos_of_pos hh _⟩
  exact Real.rpow_lt_one hh.le hh1 (div_pos hg hq)

/-- The rare-mark mean tradeoff leaves exactly the Hölder amplitude. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_rarity_mul_magnitude
lemma tent_rarity_mul_magnitude (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    tentRarity n v*tentMagnitude n v = tentH n v^v.γ := by
  have hp : v.p ≠ 0 := by linarith [hv.1.1]
  have hm : v.p-1 ≠ 0 := by linarith [hv.1.1]
  unfold tentRarity tentMagnitude
  rw [← Real.rpow_add (tentH_bounds v hv n hn).1]
  congr 1
  unfold qExp
  field_simp
  <;> ring

/-- The rare marks saturate the unit raw p-moment budget. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_rarity_moment_identity
lemma tent_rarity_moment_identity (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    tentRarity n v*(tentMagnitude n v)^v.p = 1 := by
  have hh := (tentH_bounds v hv n hn).1
  have hp : v.p ≠ 0 := by linarith [hv.1.1]
  have hm : v.p-1 ≠ 0 := by linarith [hv.1.1]
  unfold tentRarity tentMagnitude
  rw [← Real.rpow_mul hh.le, ← Real.rpow_add hh]
  have he : v.γ/qExp v+(-v.γ/(v.p-1))*v.p = 0 := by
    unfold qExp
    field_simp
    <;> ring
  rw [he, Real.rpow_zero]

/-- Upward rank rounding preserves the oracle-scale lower amplitude with factor four. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_amplitude_lower
lemma tent_amplitude_lower (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (4:ℝ)^(-v.γ)*rhoOracle n v ≤ tentH n v^v.γ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh := (tentH_bounds v hv n hn).1
  have hN : (0:ℝ) < tentRank n v := by
    exact_mod_cast (by have := (tentRank_bounds v hv n hn).1; omega : 0 < tentRank n v)
  have hg : 0 ≤ v.γ := by linarith [hv.2.2.2.1]
  have hbase : (4*(n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))⁻¹ ≤ tentH n v := by
    simpa only [one_div, tentH] using one_div_le_one_div_of_le hN (tentRank_bounds v hv n hn).2.2
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (4*(n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))⁻¹) hbase hg
  convert hr using 1
  rw [Real.inv_rpow (by positivity : 0 ≤ 4*(n:ℝ)^(2*qExp v/(2*v.γ+qExp v))),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity), mul_inv_rev,
    ← Real.rpow_neg (by positivity : 0 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v))),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
    ← Real.rpow_mul hnR.le]
  unfold rhoOracle E0
  rw [mul_comm ((n:ℝ)^_) ((4:ℝ)^_)]
  congr 1 <;> congr 1 <;> ring

/-- The chosen rank bounds the full-record sign-overlap exponent before its fixed constant. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_likelihood_exponent_bound
lemma tent_likelihood_exponent_bound (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ)^2*tentRarity n v^2*tentH n v ≤ 1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) (by linarith [hv.1.1])
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hh := (tentH_bounds v hv n hn).1
  have htarget : (n:ℝ)^(2*qExp v/(2*v.γ+qExp v)) ≤ (tentRank n v:ℝ) := by
    have ht : 0 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v)) := by positivity
    linarith [(tentRank_bounds v hv n hn).2.1]
  have hbase : tentH n v ≤ ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))⁻¹ :=
    by
      simpa only [one_div, tentH] using one_div_le_one_div_of_le
        (by positivity : 0 < (n:ℝ)^(2*qExp v/(2*v.γ+qExp v))) htarget
  have hr := Real.rpow_le_rpow hh.le hbase (show 0 ≤ 2*(v.γ/qExp v)+1 by positivity)
  have hid : tentRarity n v^2*tentH n v = tentH n v^(2*(v.γ/qExp v)+1) := by
    unfold tentRarity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, Real.rpow_add hh, Real.rpow_one]
    congr 2
    ring
  rw [mul_assoc, hid]
  have hpow : (((n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))⁻¹)^(2*(v.γ/qExp v)+1) = (n:ℝ)^(-2:ℝ) := by
    rw [Real.inv_rpow (by positivity : 0 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v))),
      ← Real.rpow_neg (by positivity : 0 ≤ (n:ℝ)^(2*qExp v/(2*v.γ+qExp v))), ← Real.rpow_mul hnR.le]
    congr 1
    field_simp
    <;> ring
  calc
    _ ≤ (n:ℝ)^2*(n:ℝ)^(-2:ℝ) := mul_le_mul_of_nonneg_left (hr.trans_eq hpow) (sq_nonneg _)
    _ = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hnR]
      norm_num

/-- The two nonzero paired-table coordinates reduce to the bounded signed tent. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_table_coordinate
lemma tent_table_coordinate (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) :
    tentEffect n v σ x/(2*tentRarity n v*tentMagnitude n v) =
      (kappa0/2)*coarseTent (tentRank n v) σ x := by
  have hh := (tentH_bounds v hv n hn).1
  rw [show 2*tentRarity n v*tentMagnitude n v = 2*(tentRarity n v*tentMagnitude n v) by ring,
    tent_rarity_mul_magnitude v hv n hn]
  unfold tentEffect
  have hp : tentH n v^v.γ ≠ 0 := (Real.rpow_pos_of_pos hh _).ne'
  field_simp
  <;> ring

/-- Each alternative uses a valid normalized six-category table, without a fallback law. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_true_table_valid
lemma tentLaw_true_table_valid (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) :
    TableValid (fun _ => 0)
      (fun x => tentEffect n v σ x/(2*tentRarity n v*tentMagnitude n v))
      (fun x => tentEffect n v σ x/(2*tentRarity n v*tentMagnitude n v))
      (tentRarity n v) (tentMagnitude n v) := by
  obtain ⟨hε, hL⟩ := tent_mark_parameters v hv n hn
  have hc : Continuous (fun x : unitInterval =>
      tentEffect n v σ x/(2*tentRarity n v*tentMagnitude n v)) := by
    fun_prop
  refine ⟨continuous_const, hc, hc, ?_, hε, hL, ?_⟩
  · intro x; norm_num
  · intro x cat
    have hg := abs_le.mp (coarseTent_abs_le_one (tentRank n v) σ x)
    dsimp only
    rw [tent_table_coordinate v hv n hn σ x]
    rcases cat with ⟨label, mark⟩
    cases mark with
    | none =>
      simp only [markedTable, mul_zero, add_zero, mul_one]
      exact div_nonneg (by linarith [hε.2]) (by norm_num)
    | some sign =>
      cases label <;> cases sign <;>
        simp only [markedTable, signVal, kappa0, Bool.false_eq_true, ↓reduceIte,
          one_mul, neg_one_mul, mul_zero, add_zero, mul_one, mul_neg_one] <;>
        apply mul_nonneg (div_nonneg hε.1.le (by norm_num)) <;> linarith

/-- Enumerating fair sign vectors gives a normalized finite prior with positive weights. [This is the stated conclusion](goal). -/
-- @node: fair_sign_prior_normalized
lemma fair_sign_prior_normalized (k : ℕ) (laws : (Fin k → Bool) → ObservedLaw) :
    PriorNormalized (finitePriorOf (fun _ => (2:ℝ)^(-(k:ℤ))) laws) ∧
    (∃ i, 0 < priorWeight (finitePriorOf (fun _ => (2:ℝ)^(-(k:ℤ))) laws) i) := by
  have hw : 0 < (2:ℝ)^(-(k:ℤ)) := by positivity
  constructor
  · constructor
    · intro i; exact hw.le
    · change (∑ _ : Fin (Fintype.card (Fin k → Bool)), (2:ℝ)^(-(k:ℤ))) = 1
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        zpow_neg, zpow_natCast]
  · let σ : Fin k → Bool := fun _ => false
    exact ⟨(Fintype.equivFin (Fin k → Bool)) σ, hw⟩

/-- Both tail priors use normalized uniform sign weights and have nonempty support. [This is the stated conclusion](goal). -/
-- @node: tentPrior_normalized
lemma tentPrior_normalized (ν : Bool) (n : ℕ) (v : Params) :
    PriorNormalized (tentPrior ν n v) ∧ (∃ i, 0 < priorWeight (tentPrior ν n v) i) :=
  fair_sign_prior_normalized _ _

/-- The separate signed-binary priors have the same normalized nonempty sign support. [This is the stated conclusion](goal). -/
-- @node: binaryTentPrior_normalized
lemma binaryTentPrior_normalized (ν : Bool) (n : ℕ) (w : Smooth3) :
    PriorNormalized (binaryTentPrior ν n w) ∧
    (∃ i, 0 < priorWeight (binaryTentPrior ν n w) i) :=
  fair_sign_prior_normalized _ _

/-- The public dyadic-pair rank diverges because its unrounded positive power does. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: tentRank_tendsto_atTop
lemma tentRank_tendsto_atTop (v : Params) (hv : v.Valid) :
    Filter.Tendsto (fun n : ℕ => (tentRank n v : ℝ)) Filter.atTop Filter.atTop := by
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hq : 0 < qExp v := div_pos (by linarith [hv.1.1]) hp
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have he : 0 < 2*qExp v/(2*v.γ+qExp v) := by positivity
  apply Filter.tendsto_atTop_mono _
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop)
  intro n
  have hc := Nat.le_ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))
  have hn : 0 ≤ (Nat.ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v))) : ℝ) := by positivity
  simp only [tentRank, Nat.cast_mul, Nat.cast_ofNat, Function.comp_def]
  linarith

/-- The rare marks grow without bound with the public rank, as required by the tail construction. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: tentMagnitude_tendsto_atTop
lemma tentMagnitude_tendsto_atTop (v : Params) (hv : v.Valid) :
    Filter.Tendsto (fun n => tentMagnitude n v) Filter.atTop Filter.atTop := by
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have he : 0 < v.γ/(v.p-1) := div_pos hg (by linarith [hv.1.1])
  have ht := (tendsto_rpow_atTop he).comp (tentRank_tendsto_atTop v hv)
  simpa only [tentMagnitude, tentH, neg_div, ← Real.rpow_neg_eq_inv_rpow, neg_neg, Function.comp_def] using ht

/-- Armsupport: the displayed mathematical construction or bound. This statement assumes [the law parameter](hyp:law), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def ArmSupport (law : ObservedLaw) (L : ℝ) : Prop :=
  ∀ a : Bool, ∀ᵐ x ∂design, law.Q a x {y | y=0 ∨ y = -L ∨ y=L}=1
/-- The zero-coordinate table is valid at every interior rarity and positive mark. This statement assumes [the hε condition](hyp:hε), [the hL condition](hyp:hL). [This is the stated conclusion](goal). -/
-- @node: zero_table_valid
lemma zero_table_valid (ε L : ℝ) (hε : 0 < ε ∧ ε < 1) (hL : 0 < L) :
    TableValid (fun _ => 0) (fun _ => 0) (fun _ => 0) ε L := by
  refine ⟨continuous_const, continuous_const, continuous_const, ?_, hε, hL, ?_⟩
  · intro x; norm_num
  · intro x cat
    rcases cat with ⟨a, mark⟩
    have he : 0 ≤ ε := hε.1.le
    have he1 : 0 ≤ 1-ε := by linarith [hε.2]
    cases mark <;> simp [markedTable] <;> positivity

/-- Every normalized table arm is concentrated on the displayed three atoms. [This is the stated conclusion](goal). -/
-- @node: tableArm_three_atom_support
lemma tableArm_three_atom_support (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) (x : unitInterval) :
    tableArm ξ υ ζ ε L h a x {y | y = 0 ∨ y = -L ∨ y = L} = 1 := by
  letI := tableArm_markov ξ υ ζ ε L h
  have hu : tableArm ξ υ ζ ε L h a x Set.univ = 1 := measure_univ
  change tableArmMeasure ξ υ ζ ε L a x _ = 1
  change tableArmMeasure ξ υ ζ ε L a x Set.univ = 1 at hu
  rw [← hu]
  simp only [tableArmMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (by measurability : MeasurableSet {y : ℝ | y = 0 ∨ y = -L ∨ y = L}),
    Measure.dirac_apply' _ MeasurableSet.univ]
  apply Finset.sum_congr rfl
  intro mark hm
  cases mark with
  | none => simp [markValue]
  | some b => cases b <;> simp [markValue, signVal]

/-- The paired null really is the balanced zero-mean table, for every sign vector. [This is the stated conclusion](goal). -/
lemma tentLaw_false_eq_zero_table (n : ℕ) (v : Params)
    (σ : Fin (tentRank n v/2) → Bool) :
    tentLaw false n v σ = pairedTentObservedLaw (fun _ => 0)
      (tentRarity n v) (tentMagnitude n v) := by
  simp [tentLaw]

/-- Every paired null has zero control raw moment, unit treated raw moment and three-atom support. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma tentLaw_false_arm_properties (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) :
    ArmSupport (tentLaw false n v σ) (tentMagnitude n v) ∧
    ∀ a : Bool, ∀ x : unitInterval,
      ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂(tentLaw false n v σ).Q a x = if a then 1 else 0 := by
  obtain ⟨hε, hL⟩ := tent_mark_parameters v hv n hn
  have ht := zero_table_valid _ _ hε hL
  rw [tentLaw_false_eq_zero_table]
  simp only [pairedTentObservedLaw, dif_pos ht]
  constructor
  · intro a
    filter_upwards [] with x
    cases a
    · simp [pairedTentArm]
    · exact tableArm_three_atom_support _ _ _ _ _ ht true x
  · intro a x
    cases a
    · simp [pairedTentArm, Real.zero_rpow (by linarith [hv.1.1] : v.p ≠ 0)]
    · change (∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂tableArm _ _ _ _ _ ht true x) = 1
      rw [tableArm_raw_moment _ _ _ _ _ _ ht (by linarith [hv.1.1]),
      tent_rarity_moment_identity v hv n hn, ENNReal.ofReal_one]

/-- Every paired alternative has balanced propensity, zero baseline, and the prescribed effect. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_true_primitives
lemma tentLaw_true_primitives (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) :
    (tentLaw true n v σ).e x = 1/2 ∧ (tentLaw true n v σ).m0 x = 0 ∧
      (tentLaw true n v σ).tau x = tentEffect n v σ x := by
  have ht := tentLaw_true_table_valid v hv n hn σ
  have hε := (tent_mark_parameters v hv n hn).1.1
  have hL := (tent_mark_parameters v hv n hn).2
  simp only [tentLaw, if_true, pairedTentObservedLaw, dif_pos ht, ContinuousMap.coe_mk,
    tableProp, tableM0, tableTau, mul_zero, zero_mul, sub_zero, sub_self,
    zero_pow (by norm_num : 2 ≠ 0), div_one, mul_one, add_zero]
  refine ⟨by norm_num, by norm_num, ?_⟩
  field_simp

/-- Every paired alternative has zero control raw moment, unit treated raw moment and three-atom support. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma tentLaw_true_arm_properties (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) :
    ArmSupport (tentLaw true n v σ) (tentMagnitude n v) ∧
    ∀ a : Bool, ∀ x : unitInterval,
      ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂(tentLaw true n v σ).Q a x = if a then 1 else 0 := by
  have ht := tentLaw_true_table_valid v hv n hn σ
  simp only [tentLaw, if_true, pairedTentObservedLaw, dif_pos ht]
  constructor
  · intro a
    filter_upwards [] with x
    cases a
    · simp [pairedTentArm]
    · exact tableArm_three_atom_support _ _ _ _ _ ht true x
  · intro a x
    cases a
    · simp [pairedTentArm, Real.zero_rpow (by linarith [hv.1.1] : v.p ≠ 0)]
    · change (∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂tableArm _ _ _ _ _ ht true x) = 1
      rw [tableArm_raw_moment _ _ _ _ _ _ ht (by linarith [hv.1.1]),
      tent_rarity_moment_identity v hv n hn, ENNReal.ofReal_one]

/-- The balanced paired null satisfies every independent model primitive and constant-null predicate. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_false_inNull
lemma tentLaw_false_inNull (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) : InNull v (tentLaw false n v σ) := by
  obtain ⟨hε, hL⟩ := tent_mark_parameters v hv n hn
  have ht := zero_table_valid _ _ hε hL
  have hraw := (tentLaw_false_arm_properties v hv n hn σ).2
  rw [tentLaw_false_eq_zero_table] at hraw ⊢
  simp only [pairedTentObservedLaw, dif_pos ht] at hraw ⊢
  constructor
  · unfold UniformDesign covariateLaw
    change (pairedTentRecordLaw (fun _ => 0) (tentRarity n v)
      (tentMagnitude n v)).map X = design
    rw [pairedTentRecordLaw_eq_compProd _ _ _ ht]
    letI := pairedTentArm_markov _ _ _ ht
    letI := recordKernel_markov _ (measurable_tableProp _ _ _ _ _ ht) _ (show ∀ x, 0 ≤ tableProp (fun _ => 0) x ∧
      tableProp (fun _ => 0) x ≤ 1 from fun x => by norm_num [tableProp])
      (pairedTentArm_markov _ _ _ ht)
    letI : IsProbabilityMeasure design := by
      change IsProbabilityMeasure (volume : Measure unitInterval)
      infer_instance
    exact Measure.fst_compProd _ _
  · intro x; norm_num [tableProp]
  · refine ⟨continuous_const, ?_, ?_⟩
    · intro x; norm_num [tableProp]
    · intro x z; simp [tableProp]; positivity
  · refine ⟨?_, ?_, ?_⟩
    · exact ContinuousMap.continuous _
    · intro x; simp [tableM0]
    · intro x z; simp [tableM0]; positivity
  · refine ⟨?_, ?_, ?_⟩
    · exact ContinuousMap.continuous _
    · intro x; simp [tableTau]
    · intro x z; simp [tableTau]; positivity
  · intro x; simp [tableM0]
  · intro x; simp [tableTau]
  · intro a; filter_upwards [] with x; rw [hraw a x]; cases a <;> norm_num
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    intro x; simp [tableTau]

/-- A normalized nonempty alternative prior close to one legal null forces original-record risk. This statement assumes [the hnull condition](hyp:hnull), [the hπ condition](hyp:hπ), [the hne condition](hyp:hne), [the halt condition](hyp:halt), [the htv condition](hyp:htv). [This is the stated conclusion](goal). -/
-- @node: single_null_testingRiskOn_lower
lemma single_null_testingRiskOn_lower (n : ℕ) (Null Alt : Set ObservedLaw) (r : ℝ)
    (P0 : ObservedLaw) (π : FinitePrior) (hnull : P0 ∈ Null)
    (hπ : PriorNormalized π) (hne : ∃ i, 0 < priorWeight π i)
    (halt : PriorSupported π {law | law ∈ Alt ∧ r ≤ hetDist law})
    (htv : Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π) < 1/2) :
    2/5 ≤ testingRiskOn n r Null Alt := by
  obtain ⟨j, hj⟩ := hne
  letI : Nonempty {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} :=
    ⟨⟨priorLaw π j, halt j hj⟩⟩
  let zeroTest : Test n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : LevelValid n Null zeroTest := by
    intro law _
    simp [rejectProb, zeroTest]
  letI : Nonempty {φ : Test n // LevelValid n Null φ} := ⟨⟨zeroTest, hz⟩⟩
  unfold testingRiskOn
  apply le_ciInf
  intro φ
  obtain ⟨i, hi, herr⟩ := single_null_prior_error_witness n P0 π hπ htv φ.1 (φ.2 P0 hnull)
  have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} =>
      1-rejectProb n law.1.P φ.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law, rfl⟩
    linarith [(rejectProb_bounds n law.1 φ.1).1]
  exact herr.trans (le_ciSup hb ⟨priorLaw π i, halt i hi⟩)

/-- Identical entire propensities let the same prior force supplied-propensity minimax risk. This statement assumes [the hnull condition](hyp:hnull), [the hπ condition](hyp:hπ), [the hne condition](hyp:hne), [the halt condition](hyp:halt), [the he condition](hyp:he), [the htv condition](hyp:htv). [This is the stated conclusion](goal). -/
-- @node: single_null_oracleTestingRisk_lower
lemma single_null_oracleTestingRisk_lower (n : ℕ) (v : Params) (r : ℝ)
    (P0 : ObservedLaw) (π : FinitePrior) (hnull : InNull v P0)
    (hπ : PriorNormalized π) (hne : ∃ i, 0 < priorWeight π i)
    (halt : PriorSupported π {law | InModel v law ∧ r ≤ hetDist law})
    (he : ∀ i, 0 < priorWeight π i → (priorLaw π i).e = P0.e)
    (htv : Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π) < 1/2) :
    2/5 ≤ oracleTestingRisk n v r := by
  obtain ⟨j, hj⟩ := hne
  letI : Nonempty {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law} :=
    ⟨⟨priorLaw π j, halt j hj⟩⟩
  let zeroTest : OracleTest n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : ∀ law, InNull v law → oracleRejectProb n law zeroTest ≤ 1/10 := by
    intro law _
    simp [oracleRejectProb, zeroTest]
  letI : Nonempty {φ : OracleTest n // ∀ law, InNull v law → oracleRejectProb n law φ ≤ 1/10} :=
    ⟨⟨zeroTest, hz⟩⟩
  unfold oracleTestingRisk
  apply le_ciInf
  intro φ
  obtain ⟨i, hi, herr⟩ := oracle_single_null_prior_error_witness n P0 π hπ he htv φ.1 (φ.2 P0 hnull)
  have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law} =>
      1-oracleRejectProb n law.1 φ.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law, rfl⟩
    linarith [(oracleRejectProb_bounds n law.1 φ.1).1]
  exact herr.trans (le_ciSup hb ⟨priorLaw π i, halt i hi⟩)

/-- The original alternative effect has the fixed tent envelope. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_true_effect_envelope
lemma tentLaw_true_effect_envelope (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) :
    |(tentLaw true n v σ).tau x| ≤ 1/16 := by
  rw [(tentLaw_true_primitives v hv n hn σ x).2.2]
  exact tentEffect_abs_le_one_sixteenth v hv n hn σ x

/-- Every paired-tent alternative remains strictly below the witness distance. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentLaw_true_distance_lt_d0
lemma tentLaw_true_distance_lt_d0 (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) : hetDist (tentLaw true n v σ) < d0 := by
  exact (hetDist_le_effect_envelope _ (1/16) (by norm_num)
    (tentLaw_true_effect_envelope v hv n hn σ)).trans_lt one_sixteenth_lt_d0


/-- Exact paired-tent distance and upward rounding give the oracle separation. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hτ condition](hyp:hτ). [This is the stated conclusion](goal). -/
-- @node: paired_effect_distance_lower
lemma paired_effect_distance_lower (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (law : ObservedLaw)
    (hτ : ∀ x : unitInterval, law.tau x = tentEffect n v σ x) :
    cOracle v*rhoOracle n v ≤ hetDist law := by
  have hN : 0 < tentRank n v := by have := (tentRank_bounds v hv n hn).1; omega
  have heven : 2*(tentRank n v/2) = tentRank n v := by unfold tentRank; omega
  have hd := (hetDist_of_paired_effect law (tentRank n v) hN heven σ
    (kappa0*tentH n v^v.γ) (mul_nonneg (by norm_num [kappa0]) (Real.rpow_nonneg (tentH_bounds v hv n hn).1.le _))
    (fun x => by rw [hτ x]; rfl)).2
  rw [hd]
  have h := mul_le_mul_of_nonneg_left (tent_amplitude_lower v hv n hn)
    (show 0 ≤ kappa0 by norm_num [kappa0])
  have hh := div_le_div_of_nonneg_right h (Real.sqrt_nonneg 3)
  calc
    _ = kappa0*((4:ℝ)^(-v.γ)*rhoOracle n v)/Real.sqrt 3 := by unfold cOracle kappa0; ring
    _ ≤ _ := hh

/-- The prescribed signed-binary finite prior has legal separated original supports. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentPrior_true_supported
lemma binaryTentPrior_true_supported (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    PriorSupported (binaryTentPrior true n v.toSmooth3)
      {law | InModel v law ∧
        cOracle (Params.ofBounded v.toSmooth3)*rhoOracle n (Params.ofBounded v.toSmooth3) ≤ hetDist law} := by
  intro i hi
  let σ := (Fintype.equivFin (Fin (tentRank n (Params.ofBounded v.toSmooth3)/2) → Bool)).symm i
  change InModel v (binaryTentLaw true n v.toSmooth3 σ) ∧ _
  have hv2 : (Params.ofBounded v.toSmooth3).Valid := ⟨by norm_num [Params.ofBounded], hv.2⟩
  refine ⟨boundedModel_inModel v hv _ (binaryModel_inBoundedModel v.toSmooth3 _
    (binaryTentLaw_inBinaryModel v.toSmooth3 hv.2 n hn true σ)), ?_⟩
  apply paired_effect_distance_lower _ hv2 n hn σ (binaryTentLaw true n v.toSmooth3 σ)
  intro x
  rw [(binaryTentLaw_primitives v.toSmooth3 hv.2 n hn true σ).2.2]
  rfl

end CausalSmith.Stat.FinitepHomogeneityDensegamma
