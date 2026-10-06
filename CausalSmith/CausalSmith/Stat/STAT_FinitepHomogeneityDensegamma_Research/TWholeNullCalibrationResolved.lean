module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scales
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Testing
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TUniformAffineProfileBound

/-! Finite-moment homogeneity testing: TWholeNullCalibrationResolved. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Upward dyadic rounding stays between a positive number and twice that number. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
lemma dyadUp_bounds (x : ℝ) (hx : 0 < x) : x ≤ dyadUp x ∧ dyadUp x ≤ 2*x := by
  have he : dyadUp x = (2:ℝ)^((Int.ceil (Real.logb 2 x)):ℝ) := by
    simp [dyadUp, Real.rpow_intCast]
  rw [he]
  constructor
  · exact (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hx).mp (Int.le_ceil _)
  · calc
      (2:ℝ)^((Int.ceil (Real.logb 2 x)):ℝ) ≤ (2:ℝ)^(Real.logb 2 x+1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.ceil_lt_add_one _).le
      _ = 2*x := by rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]; simp; ring

/-- The coarse rank is at least one in every public sample-size branch. [This is the stated conclusion](goal). -/
-- @node: ledgerM_ge_one
lemma ledgerM_ge_one (n : ℕ) (v : Params) : 1 ≤ ledgerM n v := by
  unfold ledgerM leastPow2Ge
  split
  · omega
  · exact Nat.one_le_pow _ _ (by norm_num)

/-- Each level cutoff is positive, including its guarded branch. [This is the stated conclusion](goal). -/
-- @node: ledgerT_pos
lemma ledgerT_pos (n : ℕ) (v : Params) (j : ℕ) : 0 < ledgerT n v j := by
  unfold ledgerT dyadUp
  split <;> positivity

/-- Every summand in the public bias ledger is nonnegative. [This is the stated conclusion](goal). -/
-- @node: ledgerBias_nonneg
lemma ledgerBias_nonneg (n : ℕ) (v : Params) : 0 ≤ ledgerBias n v := by
  have hT0 : 0 < ledgerT0 n v := lt_of_lt_of_le (by norm_num) (ledgerT0_ge_one n v)
  unfold ledgerBias
  split
  · norm_num
  · apply add_nonneg (by positivity)
    split
    · norm_num
    · apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro j hj
      have hT := ledgerT_pos n v (j.val+1)
      unfold aLev
      positivity

/-- The covariance budget is strictly positive once each block has two records. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledgerCov_pos
lemma ledgerCov_pos (n : ℕ) (v : Params) (hn : 4 ≤ n) : 0 < ledgerCov n v := by
  have hs : 2 ≤ blockSize n := by unfold blockSize; omega
  have hs' : 0 < (blockSize n:ℝ) := by exact_mod_cast (by omega : 0 < blockSize n)
  have hT : 0 < ledgerT0 n v := lt_of_lt_of_le (by norm_num) (ledgerT0_ge_one n v)
  have hV : 0 < ledgerV0 n v := by unfold ledgerV0; positivity
  have hL : 0 < ledgerL1 n v := by
    unfold ledgerL1
    rw [if_neg (by omega)]
    apply add_pos_of_pos_of_nonneg (by positivity)
    split
    · norm_num
    · apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro j hj
      have hT := ledgerT_pos n v (j.val+1)
      unfold dLev aLev
      positivity
  unfold ledgerCov
  rw [if_neg (by omega)]
  apply add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_pos hL) hs')
  apply div_nonneg (by positivity)
  have hs2 : (2:ℝ) ≤ blockSize n := by exact_mod_cast hs
  exact mul_nonneg hs'.le (by linarith)

/-- The rounded cutoff retains both a lower calibration budget and a factor-two upper budget. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledgerCutoff_bounds
lemma ledgerCutoff_bounds (n : ℕ) (v : Params) (hn : 4 ≤ n) :
    2*ledgerBias n v^2+65536*Real.sqrt (ledgerM n v)*ledgerCov n v ≤ ledgerCutoff n v ∧
    ledgerCutoff n v ≤ 4*ledgerBias n v^2+131072*Real.sqrt (ledgerM n v)*ledgerCov n v := by
  have hM : 0 < (ledgerM n v:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (ledgerM_ge_one n v))
  have hx : 0 < 2*ledgerBias n v^2+65536*Real.sqrt (ledgerM n v)*ledgerCov n v :=
    add_pos_of_nonneg_of_pos (by positivity) (by positivity [ledgerCov_pos n v hn])
  have hb := dyadUp_bounds _ hx
  simp only [ledgerCutoff, if_neg (by omega : ¬n<4)]
  norm_num at hb ⊢
  constructor
  · exact hb.1
  · nlinarith [hb.2]

/-- The scalar calibration inequality follows by completing the square. This statement assumes [the hB condition](hyp:hB), [the hL condition](hyp:hL), [the hM condition](hyp:hM), [the hu condition](hyp:hu), [the huB condition](hyp:huB), [the hW condition](hyp:hW). [This is the stated conclusion](goal). -/
-- @node: profile_null_scalar
lemma profile_null_scalar (B L M u W : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hM : 1 ≤ M) (hu : 0 ≤ u) (huB : u ≤ B)
    (hW : |W-u^2| ≤ 128*(Real.sqrt L*u+Real.sqrt M*L)) :
    W ≤ 2*B^2+65536*Real.sqrt M*L := by
  have hsL := Real.sq_sqrt hL
  have hsM : 1 ≤ Real.sqrt M := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hmul : Real.sqrt L*u ≤ Real.sqrt L*B := mul_le_mul_of_nonneg_left huB (Real.sqrt_nonneg _)
  have hu2 : u^2 ≤ B^2 := by nlinarith
  have hcross : 128*Real.sqrt L*B ≤ B^2+4096*L := by
    nlinarith [sq_nonneg (B-64*Real.sqrt L)]
  have hbudget : L ≤ Real.sqrt M*L := by nlinarith
  have herr := (abs_le.mp hW).2
  nlinarith

/-- The scalar signal inequality exceeds the factor-two rounded cutoff budget. This statement assumes [the hB condition](hyp:hB), [the hL condition](hyp:hL), [the hM condition](hyp:hM), [the hu condition](hyp:hu), [the hW condition](hyp:hW). [This is the stated conclusion](goal). -/
-- @node: profile_alternative_scalar
lemma profile_alternative_scalar (B L M u W : ℝ) (hB : 0 ≤ B) (hL : 0 < L)
    (hM : 1 ≤ M) (hu : 4*B+1024*M^(1/4:ℝ)*Real.sqrt L ≤ u)
    (hW : |W-u^2| ≤ 128*(Real.sqrt L*u+Real.sqrt M*L)) :
    4*B^2+131072*Real.sqrt M*L < W := by
  have hMp : 0 < M := by linarith
  have hquarter : 1 ≤ M^(1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
  have hroot := Real.sqrt_pos.mpr hL
  have hsqL := Real.sq_sqrt hL.le
  have hsqM : (M^(1/4:ℝ))^2=Real.sqrt M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le, Real.sqrt_eq_rpow]
    norm_num
  have hprod : (M^(1/4:ℝ)*Real.sqrt L)^2=Real.sqrt M*L := by
    rw [mul_pow, hsqM, hsqL]
  have hr : 0 ≤ M^(1/4:ℝ)*Real.sqrt L := by positivity
  have huc : 256*Real.sqrt L ≤ u := by nlinarith
  have hu0 : 0 ≤ u := by nlinarith
  have hlin : 128*Real.sqrt L*u ≤ u^2/2 := by nlinarith
  have husq : (4*B+1024*M^(1/4:ℝ)*Real.sqrt L)^2 ≤ u^2 := by
    nlinarith [sq_nonneg (u-(4*B+1024*M^(1/4:ℝ)*Real.sqrt L))]
  have hsig : 16*B^2+1048576*(Real.sqrt M*L) ≤ u^2 := by
    nlinarith [mul_nonneg hB hr]
  have hp : 0 < Real.sqrt M*L := by positivity
  have herr := (abs_le.mp hW).1
  nlinarith

/-- An affine score has an attained profiled minimum on the closed candidate interval. [This is the stated conclusion](goal). -/
-- @node: ledger_profiledMin_attained
lemma ledger_profiledMin_attained (n : ℕ) (v : Params) (data : Dataset n) :
    ∃ c : ℝ, |c| ≤ 1/2 ∧ ledgerW n v c data=profiledMin (ledgerScore n v) data := by
  let z0 := ledgerScore n v false 0 data
  let z1 := ledgerScore n v true 0 data
  let a0 := z0-ledgerScore n v false 1 data
  let a1 := z1-ledgerScore n v true 1 data
  obtain ⟨c,hc,he⟩ := quadraticMin_attained (inner ℝ z0 z1)
    (-(inner ℝ a0 z1+inner ℝ z0 a1)) (inner ℝ a0 a1)
  refine ⟨c,hc,?_⟩
  change _=quadraticMin (inner ℝ z0 z1) (-(inner ℝ a0 z1+inner ℝ z0 a1)) (inner ℝ a0 a1)
  rw [← he]
  unfold ledgerW quadStat
  rw [ledgerScore_affine n v false c data, ledgerScore_affine n v true c data]
  dsimp [z0,z1,a0,a1]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  ring

/-- The profiled minimum is below the statistic at every admissible candidate. This statement assumes [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: ledger_profiledMin_le
lemma ledger_profiledMin_le (n : ℕ) (v : Params) (data : Dataset n) (c : ℝ)
    (hc : |c| ≤ 1/2) : profiledMin (ledgerScore n v) data ≤ ledgerW n v c data := by
  let z0 := ledgerScore n v false 0 data
  let z1 := ledgerScore n v true 0 data
  let a0 := z0-ledgerScore n v false 1 data
  let a1 := z1-ledgerScore n v true 1 data
  have h := quadraticMin_le (inner ℝ z0 z1)
    (-(inner ℝ a0 z1+inner ℝ z0 a1)) (inner ℝ a0 a1) c hc
  change quadraticMin _ _ _ ≤ _
  convert h using 1
  unfold ledgerW quadStat
  rw [ledgerScore_affine n v false c data, ledgerScore_affine n v true c data]
  dsimp [z0,z1,a0,a1]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The public test and its mean are zero in the two small-sample branches. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledger_small_sample
lemma ledger_small_sample (n : ℕ) (v : Params) (hn : n < 4) :
    (∀ z, (ledgerTest n v).1 z=0) ∧
    (∀ law c, ledgerTheta n v law c=0) ∧ ledgerBias n v=0 := by
  simp [ledgerTest, ledgerRule, ledgerTheta, thetaVec, ledgerScore, ledgerBias, hn]

/-- A unit-bounded rejection map that vanishes on a good event is bounded by its complement mass. This statement assumes [the hf condition](hyp:hf), [the hE condition](hyp:hE), [the hzero condition](hyp:hzero). [This is the stated conclusion](goal). -/
-- @node: integral_le_bad_event
lemma integral_le_bad_event {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hzero : ∀ x ∈ E, f x=0) :
    (∫ x, f x ∂μ) ≤ 1-μ.real E := by
  have hle : ∀ x, f x ≤ Eᶜ.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ E
    · simp [hx, hzero x hx]
    · simpa [hx] using (hf x).2
  have hi := (integrable_const (1:ℝ) (μ := μ)).indicator hE.compl
  have h := integral_mono_of_nonneg (ae_of_all μ (fun x => (hf x).1)) hi (ae_of_all μ hle)
  simpa [integral_indicator_const _ hE.compl, measureReal_compl hE] using h

/-- [Whole null calibration resolved](goal). Use the total ranks, separate cutoffs, bias ledger \(\mathfrak b_{n,v}\), covariance ledger \(\Lambda_{n,v}\), and cutoff \(h_{n,v}\) of Definition \(\mathrm{def:explicit\mbox{-}score\mbox{-}ledger}\). For every \(n\ge2\) and every \(P\in\mathcal M_v\), both centered affine coefficients have covariance at most \(\Lambda_{n,v}I_{J_{\mathrm c}}\). The simultaneous ratio in the source question is at most \(C=128\) with probability at least \(0.9925\), using zero for an identically zero numerator and denominator. Under \(P\in H_0(v)\), \(\inf_c\|\theta_P(c)\|_2\le\mathfrak b_{n,v}\). The original-record rule \(\psi_{n,v}\) of that definition has exactly finite-sample size at most \(0.0075<1/10\). For \(n\ge4\), its type-II error is at most \(0.0075\) uniformly over the nonempty alternative whenever \[ d(P)\ge R_{\mathrm{att}}(n,v) :=\frac{16}{3}\left\{16J_{\mathrm c}^{-\gamma} +5\mathfrak b_{n,v} +1024J_{\mathrm c}^{1/4}\sqrt{\Lambda_{n,v}}\right\}. \] A power claim is made only if its displayed separation is strictly below \(D_v\). The test is zero for \(n=2,3\). All covariance and profiling assertions include cross-level and cross-coefficient covariances and all two-, three-, and four-record contractions, without requiring \(J_{\mathrm f}\le n\). This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). -/
-- @node: thm:whole-null-calibration-resolved
theorem whole_null_calibration_resolved (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (∀ law, InModel v law → CovarianceLedger n v law ∧ ProfileBound n v law) ∧
    (∀ law, InNull v law → (⨅ c : {c : ℝ // |c| ≤ 1/2}, ‖ledgerTheta n v law c.1‖) ≤ ledgerBias n v) ∧
    (∀ law, InNull v law → rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
    (4 ≤ n → Ratt n v < maxDist v → ∀ law, InModel v law → Ratt n v ≤ hetDist law → 1-rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
    ((n=2 ∨ n=3) → ∀ z, (ledgerTest n v).1 z=0)  := by
  have hB := ledgerBias_nonneg n v
  have hM : (1:ℝ) ≤ ledgerM n v := by exact_mod_cast ledgerM_ge_one n v
  have hcov := original_score_covariance_ledger v hv n hn
  have hprof := uniform_affine_profile_bound v hv n hn
  refine ⟨fun law hm => ⟨hcov law hm, hprof law hm⟩, ?_, ?_, ?_, ?_⟩
  · intro law hnull
    obtain ⟨c,hcl,hcu,hc⟩ := hnull.nullConstancy
    have habs : |c| ≤ 1/2 := abs_le.mpr ⟨by linarith,hcu⟩
    have ht : ‖ledgerTheta n v law c‖ ≤ ledgerBias n v := by
      by_cases hn4 : 4 ≤ n
      · exact (original_score_mean_ledger v hv n hn4 law hnull.toInModel).2.2 hnull false c hc
      · obtain ⟨_,hz,hbias⟩ := ledger_small_sample n v (by omega)
        simp [hz,hbias]
    exact (ciInf_le (show BddBelow (Set.range (fun c : {c : ℝ // |c| ≤ 1/2} =>
      ‖ledgerTheta n v law c.1‖)) from ⟨0, by rintro _ ⟨c,rfl⟩; exact norm_nonneg _⟩)
      (⟨c,habs⟩ : {c : ℝ // |c| ≤ 1/2})).trans ht
  · intro law hnull
    letI : IsProbabilityMeasure design := by
      change IsProbabilityMeasure (volume : Measure unitInterval)
      infer_instance
    letI : IsProbabilityMeasure (expLaw n law.P) := by unfold expLaw; infer_instance
    by_cases hn4 : 4 ≤ n
    · obtain ⟨c,hcl,hcu,hc⟩ := hnull.nullConstancy
      have habs : |c| ≤ 1/2 := abs_le.mpr ⟨by linarith,hcu⟩
      have ht := (original_score_mean_ledger v hv n hn4 law hnull.toInModel).2.2 hnull false c hc
      obtain ⟨hE,hprob,_⟩ := hprof law hnull.toInModel
      let E := profileEvent n v law ×ˢ (Set.univ : Set unitInterval)
      have hzero : ∀ z ∈ E, (ledgerTest n v).1 z=0 := by
        intro z hz
        have hbound := profile_null_scalar _ _ _ _ _ hB (ledgerCov_pos n v hn4).le hM
          (norm_nonneg _) ht (hz.1 c habs)
        have hmin := ledger_profiledMin_le n v z.1 c habs
        have hcut := (ledgerCutoff_bounds n v hn4).1
        have hnlt : ¬n<4 := by omega
        have hnrej : ¬ledgerCutoff n v < profiledMin (ledgerScore n v) z.1 := by linarith
        simp [ledgerTest,ledgerRule,hnlt,hnrej]
      have hb := integral_le_bad_event (expLaw n law.P) (ledgerTest n v).1
        (ledgerTest n v).2.2 E (hE.prod MeasurableSet.univ) hzero
      have hmass : (expLaw n law.P).real E = (Measure.pi fun _ : Fin n => law.P).real (profileEvent n v law) := by
        simp [E, expLaw, measureReal_prod_prod]
      change rejectProb n law.P (ledgerTest n v) ≤ _
      rw [hmass] at hb
      unfold rejectProb
      linarith
    · have hz := (ledger_small_sample n v (by omega)).1
      simp only [rejectProb,hz,integral_zero]
      norm_num
  · intro hn4 hsep law hm hd
    letI : IsProbabilityMeasure design := by
      change IsProbabilityMeasure (volume : Measure unitInterval)
      infer_instance
    letI : IsProbabilityMeasure (expLaw n law.P) := by unfold expLaw; infer_instance
    obtain ⟨hE,hprob,_⟩ := hprof law hm
    let E := profileEvent n v law ×ˢ (Set.univ : Set unitInterval)
    have hone : ∀ z ∈ E, (ledgerTest n v).1 z=1 := by
      intro z hz
      obtain ⟨c,hc,hatt⟩ := ledger_profiledMin_attained n v z.1
      have hmean := (original_score_mean_ledger v hv n hn4 law hm).2.1 false c hc
      have hmean_lower :
          (3/16)*hetDist law-16*(ledgerM n v:ℝ)^(-v.γ)-ledgerBias n v ≤
            ‖ledgerTheta n v law c‖ := by
        simpa [ledgerTheta] using hmean.2
      have hsignal : 4*ledgerBias n v+1024*(ledgerM n v:ℝ)^(1/4:ℝ)*Real.sqrt (ledgerCov n v) ≤
          ‖ledgerTheta n v law c‖ := by
        unfold Ratt at hd
        nlinarith [hmean_lower]
      have hw := profile_alternative_scalar _ _ _ _ _ hB (ledgerCov_pos n v hn4) hM
        hsignal (hz.1 c hc)
      have hcut := (ledgerCutoff_bounds n v hn4).2
      have hrej : ledgerCutoff n v < profiledMin (ledgerScore n v) z.1 := by rw [← hatt]; linarith
      simp [ledgerTest,ledgerRule,if_neg (by omega : ¬n<4),hrej]
    have hbounds : ∀ z, 0 ≤ 1-(ledgerTest n v).1 z ∧ 1-(ledgerTest n v).1 z ≤ 1 := by
      intro z
      have hb := (ledgerTest n v).2.2 z
      constructor <;> linarith
    have hb := integral_le_bad_event (expLaw n law.P) (fun z => 1-(ledgerTest n v).1 z)
      hbounds E (hE.prod MeasurableSet.univ) (by intro z hz; simp [hone z hz])
    have hmass : (expLaw n law.P).real E = (Measure.pi fun _ : Fin n => law.P).real (profileEvent n v law) := by
      simp [E, expLaw, measureReal_prod_prod]
    have hi : Integrable (ledgerTest n v).1 (expLaw n law.P) := by
      apply Integrable.of_bound (ledgerTest n v).2.1.aestronglyMeasurable 1
      exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg ((ledgerTest n v).2.2 z).1]; exact ((ledgerTest n v).2.2 z).2)
    rw [integral_sub (integrable_const (1:ℝ)) hi, integral_const, probReal_univ, one_smul, hmass] at hb
    change 1-rejectProb n law.P (ledgerTest n v) ≤ _
    unfold rejectProb
    linarith
  · intro hnsmall
    exact (ledger_small_sample n v (by omega)).1

end CausalSmith.Stat.FinitepHomogeneityDensegamma
