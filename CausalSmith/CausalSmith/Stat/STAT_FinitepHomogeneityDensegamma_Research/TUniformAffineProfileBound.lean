module
public import Causalean.Stat.Concentration.Hilbert.CrossInnerProduct
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOriginalScoreCovarianceLedger
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOriginalScoreMeanLedger

/-! Finite-moment homogeneity testing: TUniformAffineProfileBound. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Profileevent: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def profileEvent (n : ℕ) (v : Params) (law : ObservedLaw) : Set (Dataset n) :=
  {data | ∀ c : ℝ, |c| ≤ 1/2 → |ledgerW n v c data-‖ledgerTheta n v law c‖^2| ≤
    128*(Real.sqrt (ledgerCov n v)*‖ledgerTheta n v law c‖+Real.sqrt (ledgerM n v)*ledgerCov n v)}
/-- Profilebound: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def ProfileBound (n : ℕ) (v : Params) (law : ObservedLaw) : Prop :=
  MeasurableSet (profileEvent n v law) ∧
  0.9925 ≤ (Measure.pi fun _ : Fin n => law.P).real (profileEvent n v law) ∧
  (ledgerCov n v=0 → ∀ᵐ data ∂Measure.pi (fun _ : Fin n => law.P),
    ∀ c, |c| ≤ 1/2 → ledgerW n v c data=‖ledgerTheta n v law c‖^2)
/-- The score coefficients use exactly the affine convention of the profile argument. [This is the stated conclusion](goal). -/
-- @node: ledgerScore_eq_coeff
lemma ledgerScore_eq_coeff (n : ℕ) (v : Params) (b : Bool) (c : ℝ) (data : Dataset n) :
    ledgerScore n v b c data = ledgerCoeff n v b false data-c • ledgerCoeff n v b true data := by
  simpa only [ledgerCoeff, Bool.false_eq_true, if_false, if_true] using
    ledgerScore_affine n v b c data

/-- Integration preserves the affine score representation. [This is the stated conclusion](goal). -/
-- @node: ledgerTheta_affine
lemma ledgerTheta_affine (n : ℕ) (v : Params) (law : ObservedLaw) (c : ℝ) :
    ledgerTheta n v law c = ledgerTheta n v law 0-c •
      (ledgerTheta n v law 0-ledgerTheta n v law 1) := by
  have hi0 := integrable_ledgerScore n v false 0 law
  have hi1 := integrable_ledgerScore n v false 1 law
  simp only [ledgerTheta, thetaVec, ledgerScore_affine n v false c]
  integral_linearity

/-- For each sample the candidate-constant score is a continuous affine function. [This is the stated conclusion](goal). -/
-- @node: continuous_ledgerScore_constant
@[fun_prop] lemma continuous_ledgerScore_constant (n : ℕ) (v : Params) (b : Bool)
    (data : Dataset n) : Continuous (fun c => ledgerScore n v b c data) := by
  simp_rw [ledgerScore_eq_coeff]
  fun_prop

/-- The population mean is continuous in the candidate constant. [This is the stated conclusion](goal). -/
-- @node: continuous_ledgerTheta
@[fun_prop] lemma continuous_ledgerTheta (n : ℕ) (v : Params) (law : ObservedLaw) :
    Continuous (ledgerTheta n v law) := by
  have he : ledgerTheta n v law = fun c => ledgerTheta n v law 0-c •
      (ledgerTheta n v law 0-ledgerTheta n v law 1) := funext (ledgerTheta_affine n v law)
  rw [he]
  fun_prop

/-- A continuous profile inequality on a compact interval is a countable intersection of measurable fixed-constant inequalities. [This is the stated conclusion](goal). -/
-- @node: measurableSet_profileEvent
lemma measurableSet_profileEvent (n : ℕ) (v : Params) (law : ObservedLaw) :
    MeasurableSet (profileEvent n v law) := by
  let I := {c : ℝ | |c| ≤ 1/2}
  obtain ⟨S, hS, hdense⟩ := TopologicalSpace.exists_countable_dense I
  let f : ℝ → Dataset n → ℝ := fun c data =>
    |ledgerW n v c data-‖ledgerTheta n v law c‖^2|-
      128*(Real.sqrt (ledgerCov n v)*‖ledgerTheta n v law c‖+
        Real.sqrt (ledgerM n v)*ledgerCov n v)
  have hf (c : ℝ) : Measurable (f c) := by
    dsimp [f, ledgerW, quadStat]
    fun_prop
  have hc (data : Dataset n) : Continuous (fun c : I => f c data) := by
    dsimp [f, ledgerW, quadStat]
    fun_prop
  have he : profileEvent n v law = ⋂ c ∈ S, {data | f c data ≤ 0} := by
    ext data
    simp only [profileEvent, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h c hc
      dsimp only [f]
      exact sub_nonpos.mpr (h c c.property)
    · intro h c hc'
      have hclosed : IsClosed {t : I | f t data ≤ 0} :=
        isClosed_le (hc data) continuous_const
      have hsubset : S ⊆ {t : I | f t data ≤ 0} := fun t ht => h t ht
      have hall := closure_minimal hsubset hclosed
      rw [hdense.closure_eq] at hall
      have ht := @hall (⟨c, hc'⟩ : I) (mem_univ _)
      change f c data ≤ 0 at ht
      dsimp only [f] at ht
      exact sub_nonpos.mp ht
  rw [he]
  exact MeasurableSet.biInter hS (fun c _ => measurableSet_le (hf c) measurable_const)

/-- The public small-sample branch has zero mean and zero quadratic statistic. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledger_profile_small_sample
lemma ledger_profile_small_sample (n : ℕ) (v : Params) (law : ObservedLaw) (hn : n < 4) :
    (∀ c, ledgerTheta n v law c = 0) ∧ (∀ c data, ledgerW n v c data = 0) := by
  constructor
  · intro c
    simp [ledgerTheta, thetaVec, ledgerScore, hn]
  · intro c data
    simp [ledgerW, quadStat, ledgerScore, hn]

/-- The small-sample profile event is the entire sampling space. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: profileEvent_small_sample
lemma profileEvent_small_sample (n : ℕ) (v : Params) (law : ObservedLaw) (hn : n < 4) :
    profileEvent n v law = Set.univ := by
  obtain ⟨hmean, hstat⟩ := ledger_profile_small_sample n v law hn
  ext data
  simp [profileEvent, hmean, hstat, ledgerCov, hn]

/-- The declared covariance is strictly positive in every nonzero-score branch. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledgerCov_pos_of_large_sample
lemma ledgerCov_pos_of_large_sample (n : ℕ) (v : Params) (hv : v.Valid) (hn : 4 ≤ n) :
    0 < ledgerCov n v := by
  have hs : (0 : ℝ) < blockSize n := by
    have : 0 < blockSize n := by unfold blockSize; omega
    exact_mod_cast this
  have hsm : (0 : ℝ) < (blockSize n : ℝ)-1 := by
    have : 2 ≤ blockSize n := by unfold blockSize; omega
    have : (2 : ℝ) ≤ blockSize n := by exact_mod_cast this
    linarith
  have hT : 0 < ledgerT0 n v := lt_of_lt_of_le (by norm_num) (ledgerT0_ge_one n v)
  have hV : 0 < ledgerV0 n v := by unfold ledgerV0; positivity
  have hsum : 0 ≤ ∑ j : Fin (ledgerL n v),
      (dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1))) := by
    apply Finset.sum_nonneg
    intro j _
    have ht := ((ledger_cutoff_bounds n v hn hv).2.2 (j.val+1)).1
    unfold dLev aLev
    positivity
  have hL1 : 0 < ledgerL1 n v := by
    simp only [ledgerL1, if_neg (by omega : ¬ n < 4)]
    split_ifs <;> nlinarith [Real.sqrt_pos.mpr hV]
  simp only [ledgerCov, if_neg (by omega : ¬ n < 4)]
  exact add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_pos hL1) hs) (by positivity)

/-- A zero covariance ledger occurs only in the explicitly zero-score branch. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: ledgerCov_eq_zero_iff_small_sample
lemma ledgerCov_eq_zero_iff_small_sample (n : ℕ) (v : Params) (hv : v.Valid) :
    ledgerCov n v = 0 ↔ n < 4 := by
  constructor
  · intro h
    by_contra hn
    have hp := ledgerCov_pos_of_large_sample n v hv (by omega)
    linarith
  · intro hn
    simp [ledgerCov, hn]

/-- When the covariance vanishes, every candidate constant has exactly zero profile error. This statement assumes [the hv condition](hyp:hv), [the hzero condition](hyp:hzero). [This is the stated conclusion](goal). -/
-- @node: ledger_profile_zero_covariance
lemma ledger_profile_zero_covariance (n : ℕ) (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hzero : ledgerCov n v = 0) :
    ∀ᵐ data ∂Measure.pi (fun _ : Fin n => law.P),
      ∀ c, |c| ≤ 1/2 → ledgerW n v c data=‖ledgerTheta n v law c‖^2 := by
  have hn := (ledgerCov_eq_zero_iff_small_sample n v hv).mp hzero
  obtain ⟨hmean, hstat⟩ := ledger_profile_small_sample n v law hn
  exact ae_of_all _ (fun data c _ => by simp [hmean, hstat])

/-- The total fallback score satisfies the full finite-sample profile claim. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: profileBound_small_sample
lemma profileBound_small_sample (n : ℕ) (v : Params) (law : ObservedLaw) (hn : n < 4) :
    ProfileBound n v law := by
  obtain ⟨hmean, hstat⟩ := ledger_profile_small_sample n v law hn
  refine ⟨measurableSet_profileEvent n v law, ?_, ?_⟩
  · rw [profileEvent_small_sample n v law hn]
    norm_num
  · intro _
    exact ae_of_all _ (fun data c _ => by simp [hmean, hstat])

/-- The affine polynomial in the two centered coefficient errors has total absolute weight at most nine fourths on the profiling interval. This statement assumes [the hc condition](hyp:hc), [the hB condition](hyp:hB), [the hE condition](hyp:hE). [This is the stated conclusion](goal). -/
-- @node: affine_error_inner_bound
lemma affine_error_inner_bound {M : ℕ} (E : Bool → Bool → Vec M) (c B : ℝ)
    (hc : |c| ≤ 1/2) (hB : 0 ≤ B)
    (hE : ∀ r t, |inner ℝ (E false r) (E true t)| ≤ B) :
    |inner ℝ (E false false-c • E false true) (E true false-c • E true true)| ≤
      (9/4)*B := by
  have hcc : |c|^2 ≤ 1/4 := by nlinarith [abs_nonneg c]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  calc
    _ ≤ |inner ℝ (E false false) (E true false)|+
        |c| *|inner ℝ (E false false) (E true true)|+
        |c| *|inner ℝ (E false true) (E true false)|+
        |c|^2*|inner ℝ (E false true) (E true true)| := by
      have h := abs_sub
        (inner ℝ (E false false) (E true false)-c*inner ℝ (E false false) (E true true))
        (c*(inner ℝ (E false true) (E true false)-c*inner ℝ (E false true) (E true true)))
      have h1 := abs_sub (inner ℝ (E false false) (E true false))
        (c*inner ℝ (E false false) (E true true))
      have h2 := mul_le_mul_of_nonneg_left
        (abs_sub (inner ℝ (E false true) (E true false))
          (c*inner ℝ (E false true) (E true true))) (abs_nonneg c)
      simp only [abs_mul] at h h1 h2
      convert h.trans (add_le_add h1 h2) using 1 <;> first | rfl | ring_nf
    _ ≤ B+|c| *B+|c| *B+|c|^2*B := by
      gcongr <;> apply hE
    _ ≤ (9/4)*B := by nlinarith

/-- The two linear error terms have total absolute coefficient weight at most three. This statement assumes [the hc condition](hyp:hc), [the hB condition](hyp:hB), [the hE condition](hyp:hE). [This is the stated conclusion](goal). -/
-- @node: affine_error_linear_bound
lemma affine_error_linear_bound {M : ℕ} (θ : Vec M) (E : Bool → Bool → Vec M)
    (c B : ℝ) (hc : |c| ≤ 1/2) (hB : 0 ≤ B)
    (hE : ∀ b r, |inner ℝ θ (E b r)| ≤ B) :
    |inner ℝ θ ((E false false-c • E false true)+(E true false-c • E true true))| ≤
      3*B := by
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right]
  calc
    _ ≤ |inner ℝ θ (E false false)-c*inner ℝ θ (E false true)|+
        |inner ℝ θ (E true false)-c*inner ℝ θ (E true true)| := abs_add_le _ _
    _ ≤ (|inner ℝ θ (E false false)|+|c| *|inner ℝ θ (E false true)|)+
        (|inner ℝ θ (E true false)|+|c| *|inner ℝ θ (E true true)|) := by
      have h0 := abs_sub (inner ℝ θ (E false false)) (c*inner ℝ θ (E false true))
      have h1 := abs_sub (inner ℝ θ (E true false)) (c*inner ℝ θ (E true true))
      simpa only [abs_mul] using add_le_add h0 h1
    _ ≤ (B+|c| *B)+(B+|c| *B) := by gcongr <;> apply hE
    _ ≤ 3*B := by nlinarith

/-- The mean-plus-error expansion keeps both affine coefficients in each block. [This is the stated conclusion](goal). -/
-- @node: affine_profile_error_identity
lemma affine_profile_error_identity {M : ℕ} (θ e₁ e₂ : Vec M) :
    inner ℝ (θ+e₁) (θ+e₂)-‖θ‖^2 = inner ℝ θ (e₁+e₂)+inner ℝ e₁ e₂ := by
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_comm e₁ θ]
  ring

/-- On the coefficient good event, the paper's weights give the simultaneous 128-constant profile bound; this is deterministic and needs no union over constants. This statement assumes [the hc condition](hyp:hc), [the hΛ condition](hyp:hΛ), [the hlinear condition](hyp:hlinear), [the hquadratic condition](hyp:hquadratic). [This is the stated conclusion](goal). -/
-- @node: affine_profile_error_bound
lemma affine_profile_error_bound {M : ℕ} (θ : Vec M) (E : Bool → Bool → Vec M)
    (c Λ : ℝ) (hc : |c| ≤ 1/2) (hΛ : 0 ≤ Λ)
    (hlinear : ∀ b r, |inner ℝ θ (E b r)| ≤ 40*Real.sqrt Λ*‖θ‖)
    (hquadratic : ∀ r t, |inner ℝ (E false r) (E true t)| ≤ 40*Real.sqrt M*Λ) :
    |inner ℝ (θ+(E false false-c • E false true))
      (θ+(E true false-c • E true true))-‖θ‖^2| ≤
      128*(Real.sqrt Λ*‖θ‖+Real.sqrt M*Λ) := by
  rw [affine_profile_error_identity]
  have hl := affine_error_linear_bound θ E c (40*Real.sqrt Λ*‖θ‖) hc (by positivity) hlinear
  have hq := affine_error_inner_bound E c (40*Real.sqrt M*Λ) hc (by positivity) hquadratic
  calc
    _ ≤ |inner ℝ θ ((E false false-c • E false true)+(E true false-c • E true true))|+
        |inner ℝ (E false false-c • E false true) (E true false-c • E true true)| :=
      abs_add_le _ _
    _ ≤ 3*(40*Real.sqrt Λ*‖θ‖)+(9/4)*(40*Real.sqrt M*Λ) := add_le_add hl hq
    _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg Λ) (norm_nonneg θ),
      mul_nonneg (Real.sqrt_nonneg (M:ℝ)) hΛ]

private def blockExtend (n : ℕ) (b : Bool)
    (x : (i : {i // i ∈ evalBlock n b}) → Record) : Dataset n :=
  fun i => if hi : i ∈ evalBlock n b then x ⟨i, hi⟩ else (⟨0, by norm_num⟩, false, 0)

private lemma blockExtend_apply_mem (n : ℕ) (b : Bool) (data : Dataset n)
    (i : Fin n) (hi : i ∈ evalBlock n b) :
    blockExtend n b (fun j => data j.1) i = data i := by simp [blockExtend, hi]

private lemma hScore_blockExtend (n J : ℕ) (b : Bool) (T c : ℝ) (data : Dataset n) :
    hScore n b J T c (blockExtend n b (fun j => data j.1)) = hScore n b J T c data := by
  simp only [hScore, hIntercept, hTreatment]
  split_ifs
  · simp
  · have hI : (∑ i ∈ evalBlock n b,
        (treatment (blockExtend n b (fun j => data j.1) i) *
          clipY T (Y (blockExtend n b (fun j => data j.1) i))) •
          featureMap J (X (blockExtend n b (fun j => data j.1) i))) =
        ∑ i ∈ evalBlock n b, (treatment (data i) * clipY T (Y (data i))) •
          featureMap J (X (data i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [blockExtend_apply_mem n b data i hi]
    have hA : (∑ i ∈ evalBlock n b,
        treatment (blockExtend n b (fun j => data j.1) i) •
          featureMap J (X (blockExtend n b (fun j => data j.1) i))) =
        ∑ i ∈ evalBlock n b, treatment (data i) • featureMap J (X (data i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [blockExtend_apply_mem n b data i hi]
    rw [hI, hA]

private lemma uScore_blockExtend (n J : ℕ) (b : Bool)
    (G : unitInterval → unitInterval → ℝ) (T c : ℝ) (data : Dataset n) :
    uScore n b J G T c (blockExtend n b (fun j => data j.1)) = uScore n b J G T c data := by
  simp only [uScore, uIntercept, uTreatment]
  split_ifs
  · simp
  · have heq (r : Bool) : (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (treatment (blockExtend n b (fun k => data k.1) i) *
          G (X (blockExtend n b (fun k => data k.1) i))
            (X (blockExtend n b (fun k => data k.1) j)) *
          (if r then treatment (blockExtend n b (fun k => data k.1) j)
            else clipY T (Y (blockExtend n b (fun k => data k.1) j)))) •
          featureMap J (X (blockExtend n b (fun k => data k.1) i))) =
        ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (treatment (data i) * G (X (data i)) (X (data j)) *
          (if r then treatment (data j) else clipY T (Y (data j)))) •
          featureMap J (X (data i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [blockExtend_apply_mem n b data i hi,
        blockExtend_apply_mem n b data j (Finset.mem_of_mem_erase hj)]
    have h0 := heq false
    have h1 := heq true
    simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
    rw [h0, h1]

private lemma ledgerScore_blockExtend (n : ℕ) (v : Params) (b : Bool) (c : ℝ)
    (data : Dataset n) :
    ledgerScore n v b c (blockExtend n b (fun j => data j.1)) = ledgerScore n v b c data := by
  simp only [ledgerScore, multiresScore]
  split_ifs
  · rfl
  · rw [hScore_blockExtend, uScore_blockExtend]
  · rw [hScore_blockExtend, uScore_blockExtend]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [uScore_blockExtend]

private lemma measurable_blockExtend (n : ℕ) (b : Bool) : Measurable (blockExtend n b) := by
  apply measurable_pi_lambda
  intro i
  unfold blockExtend
  split <;> fun_prop

private lemma evalBlock_disjoint (n : ℕ) : Disjoint (evalBlock n false) (evalBlock n true) := by
  rw [Finset.disjoint_left]
  intro i hi0 hi1
  simp only [evalBlock, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true,
    if_false, if_true] at hi0 hi1
  omega

/-- Affine coefficients from the two deterministic evaluation blocks are independent. [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_indep_blocks
lemma ledgerCoeff_indep_blocks (n : ℕ) (v : Params) (r t : Bool) (law : ObservedLaw) :
    IndepFun (ledgerCoeff n v false r) (ledgerCoeff n v true t)
      (Measure.pi fun _ : Fin n => law.P) := by
  let μ := Measure.pi fun _ : Fin n => law.P
  have hcoord : iIndepFun (fun i : Fin n => fun data : Dataset n => data i) μ := by
    dsimp [μ]
    simpa using (iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hb := hcoord.indepFun_finset (evalBlock n false) (evalBlock n true)
    (evalBlock_disjoint n) (fun i => measurable_pi_apply i)
  have hm (b q : Bool) : Measurable (ledgerCoeff n v b q) := by
    unfold ledgerCoeff
    split <;> fun_prop
  have hc := hb.comp (hm false r |>.comp (measurable_blockExtend n false))
    (hm true t |>.comp (measurable_blockExtend n true))
  have he (b q : Bool) :
      (ledgerCoeff n v b q ∘ blockExtend n b) ∘
          (fun data : Dataset n => fun i : {i // i ∈ evalBlock n b} => data i.1) =
        ledgerCoeff n v b q := by
    funext data
    simp only [Function.comp_apply, ledgerCoeff]
    split
    · rw [ledgerScore_blockExtend, ledgerScore_blockExtend]
    · rw [ledgerScore_blockExtend]
  simpa only [he false r, he true t] using hc

/-- Every evaluation block has the same population score mean. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: ledgerScore_integral_eq_ledgerTheta
lemma ledgerScore_integral_eq_ledgerTheta (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) (b : Bool) (c : ℝ) :
    (∫ data, ledgerScore n v b c data ∂Measure.pi fun _ : Fin n => law.P) =
      ledgerTheta n v law c := by
  obtain ⟨hM, hMK, _⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
  have hdiv := ledger_coarse_dvd_fine n v hn
  by_cases hs : singleBranch v
  · have hb := singleMean_exact v hv law hm n (ledgerM n v) (ledgerK n v)
      hn hM hK hdiv b (ledgerT0 n v) (ledgerT0_ge_one n v) c
    have hf := singleMean_exact v hv law hm n (ledgerM n v) (ledgerK n v)
      hn hM hK hdiv false (ledgerT0 n v) (ledgerT0_ge_one n v) c
    simpa [ledgerTheta, thetaVec, ledgerScore, hs, if_neg (by omega : ¬ n < 4)]
      using hb.trans hf.symm
  · have hb := multiresMean_exact v hv law hm n (ledgerM n v) (ledgerL n v)
      hn hM b (ledgerT0 n v) (fun j => ledgerT n v (j.val+1))
      (ledgerT0_ge_one n v) (fun j => (ledger_cutoff_bounds n v hn hv).2.2 (j.val+1) |>.1) c
    have hf := multiresMean_exact v hv law hm n (ledgerM n v) (ledgerL n v)
      hn hM false (ledgerT0 n v) (fun j => ledgerT n v (j.val+1))
      (ledgerT0_ge_one n v) (fun j => (ledger_cutoff_bounds n v hn hv).2.2 (j.val+1) |>.1) c
    simpa [ledgerTheta, thetaVec, ledgerScore, hs, if_neg (by omega : ¬ n < 4)]
      using hb.trans hf.symm

/-- Population mean of an affine score coefficient. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law), [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def ledgerCoeffMean (n : ℕ) (v : Params) (law : ObservedLaw) (r : Bool) :
    Vec (ledgerM n v) :=
  if r then ledgerTheta n v law 0-ledgerTheta n v law 1 else ledgerTheta n v law 0

/-- Centered affine score coefficient in one evaluation block. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law), [the b parameter](hyp:b), [the r parameter](hyp:r), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def ledgerCoeffError (n : ℕ) (v : Params) (law : ObservedLaw) (b r : Bool)
    (data : Dataset n) : Vec (ledgerM n v) :=
  ledgerCoeff n v b r data-ledgerCoeffMean n v law r

private lemma ledgerCoeff_integral_eq_mean (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) (b r : Bool) :
    (∫ data, ledgerCoeff n v b r data ∂Measure.pi fun _ : Fin n => law.P) =
      ledgerCoeffMean n v law r := by
  unfold ledgerCoeff ledgerCoeffMean
  split
  · rw [integral_sub (integrable_ledgerScore n v b 0 law) (integrable_ledgerScore n v b 1 law),
      ledgerScore_integral_eq_ledgerTheta v hv n hn law hm b 0,
      ledgerScore_integral_eq_ledgerTheta v hv n hn law hm b 1]
  · exact ledgerScore_integral_eq_ledgerTheta v hv n hn law hm b 0

private lemma ledgerCoeffError_memLp (n : ℕ) (v : Params) (law : ObservedLaw) (b r : Bool) :
    MemLp (ledgerCoeffError n v law b r) 2 (Measure.pi fun _ : Fin n => law.P) := by
  exact (ledgerCoeff_memLp n v b r law).sub (memLp_const _)

private lemma ledgerCoeffError_indep (n : ℕ) (v : Params) (law : ObservedLaw) (r t : Bool) :
    IndepFun (ledgerCoeffError n v law false r) (ledgerCoeffError n v law true t)
      (Measure.pi fun _ : Fin n => law.P) := by
  have h := (ledgerCoeff_indep_blocks n v r t law).comp
    (show Measurable (fun x : Vec (ledgerM n v) => x-ledgerCoeffMean n v law r) by fun_prop)
    (show Measurable (fun x : Vec (ledgerM n v) => x-ledgerCoeffMean n v law t) by fun_prop)
  change IndepFun (fun x => ledgerCoeff n v false r x-ledgerCoeffMean n v law r)
    (fun x => ledgerCoeff n v true t x-ledgerCoeffMean n v law t)
    (Measure.pi fun _ : Fin n => law.P)
  simpa only [Function.comp_def] using h

private lemma ledgerCoeffError_inner_second_moment_le
    (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw)
    (hm : InModel v law) (b r : Bool) (u : Vec (ledgerM n v)) :
    (∫ data, inner ℝ u (ledgerCoeffError n v law b r data) ^ 2
      ∂Measure.pi fun _ : Fin n => law.P) ≤ ledgerCov n v*‖u‖^2 := by
  let μ := Measure.pi fun _ : Fin n => law.P
  let f := fun data => inner ℝ u (ledgerCoeff n v b r data)
  have hf : MemLp f 2 μ := ledgerCoeff_inner_memLp n v b r law u
  have hmean : (∫ data, f data ∂μ) = inner ℝ u (ledgerCoeffMean n v law r) := by
    rw [show (∫ data, f data ∂μ) = inner ℝ u
        (∫ data, ledgerCoeff n v b r data ∂μ) from
      (innerSL ℝ u).integral_comp_comm (ledgerCoeff_memLp n v b r law |>.integrable (by norm_num))]
    rw [ledgerCoeff_integral_eq_mean v hv n hn law hm b r]
  have hvar := (original_score_covariance_ledger v hv n (by omega) law hm).1 b r u |>.2
  rw [variance_eq_integral hf.1.aemeasurable, hmean] at hvar
  simpa only [ledgerCoeffError, inner_sub_right] using hvar

/-- The four independent pairs of centered affine coefficients have the sharp dimension-linear cross-inner-product second-moment bound. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeffError_cross_second_moment_le
lemma ledgerCoeffError_cross_second_moment_le
    (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw)
    (hm : InModel v law) (r t : Bool) :
    (∫ data, inner ℝ (ledgerCoeffError n v law false r data)
        (ledgerCoeffError n v law true t data) ^ 2
      ∂Measure.pi fun _ : Fin n => law.P) ≤
      ledgerM n v * ledgerCov n v ^ 2 := by
  apply Causalean.Stat.Concentration.indep_inner_sq_integral_le
      (Measure.pi fun _ : Fin n => law.P)
      (ledgerCoeffError n v law false r) (ledgerCoeffError n v law true t) (ledgerCov n v)
  · unfold ledgerCoeffError ledgerCoeffMean ledgerCoeff
    split <;> fun_prop
  · unfold ledgerCoeffError ledgerCoeffMean ledgerCoeff
    split <;> fun_prop
  · exact ledgerCoeffError_memLp n v law false r
  · exact ledgerCoeffError_memLp n v law true t
  · exact ledgerCoeffError_indep n v law r t
  · exact ledgerCoeffError_inner_second_moment_le v hv n hn law hm false r
  · exact ledgerCoeffError_inner_second_moment_le v hv n hn law hm true t

/-- The at-most-two-dimensional population affine profile subspace. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def ledgerThetaSpan (n : ℕ) (v : Params) (law : ObservedLaw) :
    Submodule ℝ (Vec (ledgerM n v)) :=
  Submodule.span ℝ {ledgerTheta n v law 0,
    ledgerTheta n v law 0-ledgerTheta n v law 1}

private lemma ledgerThetaSpan_finrank_le_two (n : ℕ) (v : Params) (law : ObservedLaw) :
    Module.finrank ℝ (ledgerThetaSpan n v law) ≤ 2 := by
  unfold ledgerThetaSpan
  refine (finrank_span_le_card _).trans ?_
  simpa only [Set.toFinset_insert, Set.toFinset_singleton] using
    (Finset.card_le_two (a := ledgerTheta n v law 0)
      (b := ledgerTheta n v law 0-ledgerTheta n v law 1))

private lemma ledgerTheta_mem_span (n : ℕ) (v : Params) (law : ObservedLaw) (c : ℝ) :
    ledgerTheta n v law c ∈ ledgerThetaSpan n v law := by
  rw [ledgerTheta_affine]
  apply Submodule.sub_mem
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Each centered affine coefficient has a rank-two projected-norm failure probability at most one eight-hundredth. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeffError_projection_tail
lemma ledgerCoeffError_projection_tail
    (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw)
    (hm : InModel v law) (b r : Bool) :
    (Measure.pi fun _ : Fin n => law.P).real {data |
      40*Real.sqrt (ledgerCov n v) <
        ‖(ledgerThetaSpan n v law).orthogonalProjection
          (ledgerCoeffError n v law b r data)‖} ≤ 1/800 := by
  have hΛ := (ledgerCov_pos_of_large_sample n v hv hn).le
  have ht := Causalean.Stat.Concentration.projection_norm_tail_le_two
    (Measure.pi fun _ : Fin n => law.P)
    (ledgerThetaSpan n v law) (ledgerThetaSpan_finrank_le_two n v law)
    (ledgerCoeffError n v law b r) (ledgerCov n v) (40*Real.sqrt (ledgerCov n v))
    hΛ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (ledgerCov_pos_of_large_sample n v hv hn)))
    (ledgerCoeffError_memLp n v law b r)
    (ledgerCoeffError_inner_second_moment_le v hv n hn law hm b r)
  calc
    _ ≤ 2*ledgerCov n v/(40*Real.sqrt (ledgerCov n v))^2 := ht
    _ = 1/800 := by
      rw [mul_pow, Real.sq_sqrt hΛ]
      have hp := ledgerCov_pos_of_large_sample n v hv hn
      field_simp
      ring

private lemma ledgerTheta_inner_error_le_of_projection
    (n : ℕ) (v : Params) (law : ObservedLaw) (c : ℝ) (b r : Bool) (data : Dataset n)
    (hproj : ‖(ledgerThetaSpan n v law).orthogonalProjection
      (ledgerCoeffError n v law b r data)‖ ≤ 40*Real.sqrt (ledgerCov n v)) :
    |inner ℝ (ledgerTheta n v law c) (ledgerCoeffError n v law b r data)| ≤
      40*Real.sqrt (ledgerCov n v)*‖ledgerTheta n v law c‖ := by
  let θ : ledgerThetaSpan n v law :=
    ⟨ledgerTheta n v law c, ledgerTheta_mem_span n v law c⟩
  rw [← (ledgerThetaSpan n v law).inner_orthogonalProjection_eq_of_mem_left θ]
  calc
    |inner ℝ θ ((ledgerThetaSpan n v law).orthogonalProjection
        (ledgerCoeffError n v law b r data))| ≤
        ‖θ‖*‖(ledgerThetaSpan n v law).orthogonalProjection
          (ledgerCoeffError n v law b r data)‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) θ
        ((ledgerThetaSpan n v law).orthogonalProjection
          (ledgerCoeffError n v law b r data)))
    _ ≤ ‖θ‖*(40*Real.sqrt (ledgerCov n v)) := by gcongr
    _ = _ := by rw [show ‖θ‖ = ‖ledgerTheta n v law c‖ from rfl]; ring

/-- Each centered cross-block coefficient pair exceeds its quadratic threshold with probability at most one sixteen-hundredth. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeffError_cross_tail
lemma ledgerCoeffError_cross_tail
    (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw)
    (hm : InModel v law) (r t : Bool) :
    (Measure.pi fun _ : Fin n => law.P).real {data |
      40*Real.sqrt (ledgerM n v)*ledgerCov n v <
        |inner ℝ (ledgerCoeffError n v law false r data)
          (ledgerCoeffError n v law true t data)|} ≤ 1/1600 := by
  let μ := Measure.pi fun _ : Fin n => law.P
  have hM : 0 < ledgerM n v := by
    unfold ledgerM leastPow2Ge
    split <;> positivity
  have hΛ := ledgerCov_pos_of_large_sample n v hv hn
  have ht := Causalean.Stat.Concentration.indep_inner_tail_le μ
    (ledgerCoeffError n v law false r) (ledgerCoeffError n v law true t)
    (ledgerCov n v) (40*Real.sqrt (ledgerM n v)*ledgerCov n v)
    (by unfold ledgerCoeffError ledgerCoeffMean ledgerCoeff; split <;> fun_prop)
    (by unfold ledgerCoeffError ledgerCoeffMean ledgerCoeff; split <;> fun_prop)
    (ledgerCoeffError_memLp n v law false r) (ledgerCoeffError_memLp n v law true t)
    (ledgerCoeffError_indep n v law r t) (by positivity)
    (ledgerCoeffError_cross_second_moment_le v hv n hn law hm r t)
  calc
    _ ≤ ledgerM n v*ledgerCov n v^2/
        (40*Real.sqrt (ledgerM n v)*ledgerCov n v)^2 := ht
    _ = 1/1600 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ ledgerM n v)]
      have hMr : (ledgerM n v : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp [hMr, hΛ.ne']
      ring

private lemma ledgerScore_eq_theta_add_error (n : ℕ) (v : Params) (law : ObservedLaw)
    (b : Bool) (c : ℝ) (data : Dataset n) :
    ledgerScore n v b c data = ledgerTheta n v law c+
      (ledgerCoeffError n v law b false data-c • ledgerCoeffError n v law b true data) := by
  rw [ledgerScore_eq_coeff, ledgerTheta_affine]
  simp only [ledgerCoeffError, ledgerCoeffMean, Bool.false_eq_true, if_false, if_true]
  module

/-- [Uniform affine profile bound](goal). For the explicit score construction and every \(P\in\mathcal M_v\), with probability at least \(0.9925\), simultaneously for every \(c\in[-1/2,1/2]\), \[ |W(c)-\|\theta_P(c)\|_2^2| \le128\{\sqrt{\Lambda_{n,v}}\|\theta_P(c)\|_2 +\sqrt{J_{\mathrm c}}\Lambda_{n,v}\}. \] When the right-hand side is zero the error is zero almost surely and the corresponding ratio is assigned value zero. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). -/
-- @node: lem:uniform-affine-profile-bound
lemma uniform_affine_profile_bound (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    ∀ law, InModel v law → ProfileBound n v law := by
  intro law hm
  by_cases hsmall : n < 4
  · exact profileBound_small_sample n v law hsmall
  · refine ⟨measurableSet_profileEvent n v law, ?_,
      ledger_profile_zero_covariance n v hv law⟩
    have hnlarge : 4 ≤ n := by omega
    let μ := Measure.pi fun _ : Fin n => law.P
    let Pbad : Bool → Bool → Set (Dataset n) := fun b r => {data |
      40*Real.sqrt (ledgerCov n v) <
        ‖(ledgerThetaSpan n v law).orthogonalProjection
          (ledgerCoeffError n v law b r data)‖}
    let Qbad : Bool → Bool → Set (Dataset n) := fun r t => {data |
      40*Real.sqrt (ledgerM n v)*ledgerCov n v <
        |inner ℝ (ledgerCoeffError n v law false r data)
          (ledgerCoeffError n v law true t data)|}
    let Bad : Set (Dataset n) :=
      (⋃ b, ⋃ r, Pbad b r) ∪ (⋃ r, ⋃ t, Qbad r t)
    have hEmeas (b r : Bool) : Measurable (ledgerCoeffError n v law b r) := by
      unfold ledgerCoeffError ledgerCoeffMean ledgerCoeff
      split <;> fun_prop
    have hPmeas (b r : Bool) : MeasurableSet (Pbad b r) := by
      dsimp only [Pbad]
      apply measurableSet_lt measurable_const
      exact (((ledgerThetaSpan n v law).orthogonalProjection.continuous.measurable.comp
        (hEmeas b r)).norm)
    have hQmeas (r t : Bool) : MeasurableSet (Qbad r t) := by
      dsimp only [Qbad]
      apply measurableSet_lt measurable_const
      exact (Measurable.inner (hEmeas false r) (hEmeas true t)).abs
    have hBad : MeasurableSet Bad := by
      dsimp only [Bad]
      exact (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun r => hPmeas b r).union
        (MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun t => hQmeas r t)
    have hPU : μ.real (⋃ b, ⋃ r, Pbad b r) ≤ 4/800 := by
      calc
        _ ≤ ∑ b : Bool, μ.real (⋃ r, Pbad b r) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ b : Bool, ∑ r : Bool, μ.real (Pbad b r) := by
          gcongr with b
          exact measureReal_iUnion_fintype_le _
        _ ≤ ∑ _b : Bool, ∑ _r : Bool, (1/800 : ℝ) := by
          gcongr with b r
          simpa only [μ, Pbad] using
            ledgerCoeffError_projection_tail v hv n hnlarge law hm b r
        _ = 4/800 := by norm_num
    have hQU : μ.real (⋃ r, ⋃ t, Qbad r t) ≤ 4/1600 := by
      calc
        _ ≤ ∑ r : Bool, μ.real (⋃ t, Qbad r t) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ r : Bool, ∑ t : Bool, μ.real (Qbad r t) := by
          gcongr with r
          exact measureReal_iUnion_fintype_le _
        _ ≤ ∑ _r : Bool, ∑ _t : Bool, (1/1600 : ℝ) := by
          gcongr with r t
          simpa only [μ, Qbad] using
            ledgerCoeffError_cross_tail v hv n hnlarge law hm r t
        _ = 4/1600 := by norm_num
    have hBadMass : μ.real Bad ≤ 3/400 := by
      calc
        _ ≤ μ.real (⋃ b, ⋃ r, Pbad b r)+μ.real (⋃ r, ⋃ t, Qbad r t) :=
          measureReal_union_le _ _
        _ ≤ 4/800+4/1600 := add_le_add hPU hQU
        _ = 3/400 := by norm_num
    have hgood : Badᶜ ⊆ profileEvent n v law := by
      intro data hdata c hc
      have hp (b r : Bool) :
          ‖(ledgerThetaSpan n v law).orthogonalProjection
            (ledgerCoeffError n v law b r data)‖ ≤
            40*Real.sqrt (ledgerCov n v) := by
        apply le_of_not_gt
        intro h
        apply hdata
        exact Set.mem_union_left _
          (Set.mem_iUnion_of_mem b (Set.mem_iUnion_of_mem r h))
      have hq (r t : Bool) :
          |inner ℝ (ledgerCoeffError n v law false r data)
            (ledgerCoeffError n v law true t data)| ≤
            40*Real.sqrt (ledgerM n v)*ledgerCov n v := by
        apply le_of_not_gt
        intro h
        apply hdata
        exact Set.mem_union_right _
          (Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem t h))
      rw [ledgerW, quadStat, ledgerScore_eq_theta_add_error,
        ledgerScore_eq_theta_add_error]
      apply affine_profile_error_bound (ledgerTheta n v law c)
        (fun b r => ledgerCoeffError n v law b r data) c (ledgerCov n v) hc
        (ledgerCov_pos_of_large_sample n v hv hnlarge).le
      · intro b r
        exact ledgerTheta_inner_error_le_of_projection n v law c b r data (hp b r)
      · exact hq
    calc
      0.9925 = 397/400 := by norm_num
      _ ≤ μ.real Badᶜ := by
        rw [measureReal_compl hBad, probReal_univ]
        linarith
      _ ≤ μ.real (profileEvent n v law) := measureReal_mono hgood

end CausalSmith.Stat.FinitepHomogeneityDensegamma
