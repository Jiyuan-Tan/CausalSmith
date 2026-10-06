module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryComparison
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.EffectDistance
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentParameters
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentSmoothness

/-! Primitive legality of the balanced signed-binary paired-tent family. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The prescribed tent effect stays inside the fixed one-sixteenth envelope. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentEffect_abs_le_one_sixteenth
lemma tentEffect_abs_le_one_sixteenth (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) :
    |tentEffect n v σ x| ≤ 1/16 := by
  have hh : tentH n v^v.γ ≤ 1 := Real.rpow_le_one
    (tentH_bounds v hv n hn).1.le (tentH_bounds v hv n hn).2.le
    (by linarith [hv.2.2.2.1])
  rw [tentEffect, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num [kappa0] : 0 ≤ kappa0),
    abs_of_nonneg (Real.rpow_nonneg (tentH_bounds v hv n hn).1.le _)]
  calc
    _ ≤ kappa0*1*|coarseTent (tentRank n v) σ x| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by norm_num [kappa0])) (abs_nonneg _)
    _ ≤ kappa0*1*1 := mul_le_mul_of_nonneg_left
      (coarseTent_abs_le_one (tentRank n v) σ x) (by norm_num [kappa0])
    _ = 1/16 := by norm_num [kappa0]

/-- A balanced binary realization is exactly the binary conversion of its deterministic mean law. [This is the stated conclusion](goal). -/
-- @node: balanced_binaryRealization_eq_conversion
lemma balanced_binaryRealization_eq_conversion (τ : Nuisance) :
    binaryRealization (ContinuousMap.const unitInterval (1/2)) 0 τ =
      binaryConversion (deterministicLaw (ContinuousMap.const unitInterval (1/2)) 0 τ) := by
  have hd := deterministicLaw_primitives (ContinuousMap.const unitInterval (1/2)) 0 τ
    (fun _ => by norm_num)
  simp only [binaryConversion, hd.1, hd.2.1, hd.2.2.1]

/-- Both branches of the binary tent family retain their balanced propensity, zero baseline and literal effect. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_primitives
lemma binaryTentLaw_primitives (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (ν : Bool) (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    (binaryTentLaw ν n w σ).e = ContinuousMap.const unitInterval (1/2) ∧
    (binaryTentLaw ν n w σ).m0 = 0 ∧
    (binaryTentLaw ν n w σ).tau =
      (if ν then ⟨tentEffect n (Params.ofBounded w) σ, continuous_tentEffect n (Params.ofBounded w) σ⟩ else 0) := by
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  have hc : (∀ x : unitInterval, 0 ≤ (ContinuousMap.const unitInterval (1/2:ℝ)) x ∧
      (ContinuousMap.const unitInterval (1/2:ℝ)) x ≤ 1) ∧
      (∀ x : unitInterval, |(0 : Nuisance) x| ≤ 1 ∧
        |(0 : Nuisance) x +
          (if ν then (⟨tentEffect n (Params.ofBounded w) σ,
            continuous_tentEffect n (Params.ofBounded w) σ⟩ : Nuisance) else 0) x| ≤ 1) := by
    constructor
    · intro x; norm_num
    · intro x
      cases ν <;> simp only [Bool.false_eq_true, ↓reduceIte, ContinuousMap.zero_apply,
        ContinuousMap.coe_mk, zero_add, abs_zero]
      · norm_num
      · exact ⟨by norm_num,
          (tentEffect_abs_le_one_sixteenth _ hv n hn σ x).trans (by norm_num)⟩
  simp only [binaryTentLaw, binaryRealization, dif_pos hc]
  exact ⟨True.intro, True.intro, True.intro⟩

/-- Every binary tent law satisfies each original model primitive and the signed-outcome support requirement. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_inBinaryModel
lemma binaryTentLaw_inBinaryModel (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (ν : Bool) (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    InBinaryModel w (binaryTentLaw ν n w σ) := by
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  unfold binaryTentLaw
  rw [balanced_binaryRealization_eq_conversion]
  apply binaryConversion_inModel
  apply deterministicLaw_inModel _ hv
  · intro x; norm_num
  · refine ⟨continuous_const, ?_, ?_⟩
    · intro x; norm_num
    · intro x z; simp only [ContinuousMap.const_apply, sub_self, abs_zero]; positivity
  · refine ⟨continuous_const, ?_, ?_⟩
    · intro x; simp
    · intro x z; simp only [Bool.false_eq_true, ↓reduceIte, ContinuousMap.zero_apply, sub_self, abs_zero]; positivity
  · cases ν
    · refine ⟨continuous_const, ?_, ?_⟩
      · intro x; simp
      · intro x z; simp only [Bool.false_eq_true, ↓reduceIte, ContinuousMap.zero_apply, sub_self, abs_zero]; positivity
    · exact tentEffect_holderBall n _ hv
        (by have := (tentRank_bounds _ hv n hn).1; omega)
        (tentH_bounds _ hv n hn).2.le σ
  · intro x; simp
  · intro x
    cases ν
    · simp
    · exact (tentEffect_abs_le_one_sixteenth _ hv n hn σ x).trans (by norm_num)

/-- The binary null branch has constant zero mean effect and all signed-binary model predicates. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_false_inBinaryNull
lemma binaryTentLaw_false_inBinaryNull (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    InBinaryNull w (binaryTentLaw false n w σ) := by
  have hm := binaryTentLaw_inBinaryModel w hw n hn false σ
  refine ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
    hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hm.signedBinaryOutcome,
    0, by norm_num, by norm_num, ?_⟩
  rw [(binaryTentLaw_primitives w hw n hn false σ).2.2]
  simp

/-- The binary alternative has distance strictly below the fixed nonempty-model witness. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_true_distance_lt_d0
lemma binaryTentLaw_true_distance_lt_d0 (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    hetDist (binaryTentLaw true n w σ) < d0 := by
  apply (hetDist_le_effect_envelope _ (1/16) (by norm_num) ?_).trans_lt one_sixteenth_lt_d0
  intro x
  rw [(binaryTentLaw_primitives w hw n hn true σ).2.2]
  exact tentEffect_abs_le_one_sixteenth (Params.ofBounded w)
    ⟨by norm_num [Params.ofBounded], hw⟩ n hn σ x

end CausalSmith.Stat.FinitepHomogeneityDensegamma
