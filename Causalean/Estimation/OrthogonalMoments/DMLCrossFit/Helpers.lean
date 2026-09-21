/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Helpers for K-fold cross-fitted Chernozhukov DML

This file supplies fold-normalized sum bounds and stochastic-order closure lemmas used by the
K-fold everywhere-good interface in `AsymptoticLinearity.lean`.

Reference: Chernozhukov et al. (2018), §3.2 (DML2).
-/

module
public import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Estimator
public import Causalean.Mathlib.Probability.IdentDistrib.CenteredSum
public import Causalean.Stat.EmpiricalProcess.CrossFitRate

/-! # Cross-Fitted Double Machine Learning

This helper module proves fold-normalized sum bounds and closure properties for stochastic
little-o and big-O relations used in the K-fold asymptotic-linearity proof. The estimator-level
assembly and headline theorem are in `AsymptoticLinearity.lean`. -/

@[expose] public section
namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]
/-- **Foldwise normalized-sum tightness.** For [an i.i.d. sample](hyp:sample),
[a measurable mean-zero square-integrable transform](hyp:ψ,hψ_meas,hψ_mean,hψ_sq),
[a K-fold split](hyp:split), and [a fixed fold](hyp:k), [the transform's
fold-normalized partial sum is bounded in probability](goal).

Proof: Markov + the iid second-moment bound
`Causalean.Mathlib.iid_centered_sum_sq_lintegral_le`, instantiated with the
trivial σ-algebra `m_A = ⊥` (independent of any other σ-algebra by
`ProbabilityTheory.indep_bot_left`).  The mean-zero hypothesis turns the
centered sum into the un-centered sum. -/
lemma foldNormalizedSum_isBigOp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (sample : IIDSample Ω Z μ P_Z) (ψ : Z → ℝ)
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ z, ψ z ∂P_Z = 0)
    (hψ_sq : Integrable (fun z => ψ z ^ 2) P_Z)
    {K : ℕ} (split : KFoldSplit sample K) (k : Fin K) :
    IsBigOp
      (fun n ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => (1 : ℝ)) μ := by
  have hψ_memLp : MemLp ψ 2 P_Z :=
    (memLp_two_iff_integrable_sq hψ_meas.aestronglyMeasurable).2 hψ_sq
  -- `N²` is the square of the L² norm of ψ.
  let N : ℝ := (eLpNorm ψ 2 P_Z).toReal
  have hN_nonneg : 0 ≤ N := ENNReal.toReal_nonneg
  -- iid product law for fold n k.
  have hiid : ∀ n,
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω) =
        Measure.pi (fun _ : split.fold n k => P_Z) := by
    intro n
    have hindep_s : iIndepFun (fun i : split.fold n k => sample.Z i) μ := by
      exact sample.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : split.fold n k => (sample.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω)
          = Measure.pi (fun i : split.fold n k => μ.map (sample.Z i)) := hmap
      _ = Measure.pi (fun _ : split.fold n k => P_Z) := by
          congr with i
          rw [← (sample.identDist i).map_eq, sample.law]
  -- Independence with the trivial σ-algebra ⊥.
  have hindep : ∀ n,
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : split.fold n k) => sample.Z i ω) inferInstance) μ := by
    intro n
    exact ProbabilityTheory.indep_bot_left _
  -- Apply the iid centered sum bound with g(ω, x) := ψ(x) (constant in ω).
  have hbound : ∀ n, 0 < (split.fold n k).card →
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n hn
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := split.fold n k) hn (W := sample.Z)
      (fun i _ => sample.meas i)
      (⊥ : MeasurableSpace Ω) bot_le (hindep n) (hiid n)
      (fun _ z => ψ z)
      (by
        change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z => ψ p.2)
        exact hψ_meas.comp measurable_snd)
      (fun _ => hψ_memLp)
    -- Simplify the lambda `fun _ z => ψ z` to ψ in hraw.
    simp only [hψ_mean, sub_zero] at hraw
    -- RHS: ∫ N² ∂μ = N² (μ is probability).
    refine hraw.trans ?_
    simp [N]
  have hbound_all : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2 + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos ((split.fold n k).card) with hzero | hpos
    · have hfold_empty : split.fold n k = ∅ := Finset.card_eq_zero.mp hzero
      simp [hfold_empty]
    · exact (hbound n hpos).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hY_aemeas : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) μ := by
    intro n
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => hψ_meas.comp (sample.meas i)))).aemeasurable
  have hbig : IsBigOp
      (fun n ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => Real.sqrt (N ^ 2 + 1)) μ :=
    IsBigOp.of_sq_lintegral_le hY_aemeas (fun _ => by positivity)
      (Eventually.of_forall fun _ => by positivity) hbound_all
  exact hbig.const_rate_collapse (Real.sqrt_nonneg _)

/-- **Helper.**  Variant of `foldNormalizedSum_isBigOp` with the full-sample
normalization `(1/√n)` instead of `(1/√|fold n k|)`.  Since
`(split.fold n k).card ≤ n` (from `cover` + `partition`), the second moment
is still bounded by `∫ ψ² dP_Z`, and the same Markov argument applies. -/
lemma foldNormalizedSumOverN_isBigOp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (sample : IIDSample Ω Z μ P_Z) (ψ : Z → ℝ)
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ z, ψ z ∂P_Z = 0)
    (hψ_sq : Integrable (fun z => ψ z ^ 2) P_Z)
    {K : ℕ} (split : KFoldSplit sample K) (k : Fin K) :
    IsBigOp
      (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => (1 : ℝ)) μ := by
  have hψ_memLp : MemLp ψ 2 P_Z :=
    (memLp_two_iff_integrable_sq hψ_meas.aestronglyMeasurable).2 hψ_sq
  let N : ℝ := (eLpNorm ψ 2 P_Z).toReal
  have hN_nonneg : 0 ≤ N := ENNReal.toReal_nonneg
  -- iid product law for fold n k.
  have hiid : ∀ n,
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω) =
        Measure.pi (fun _ : split.fold n k => P_Z) := by
    intro n
    have hindep_s : iIndepFun (fun i : split.fold n k => sample.Z i) μ := by
      exact sample.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : split.fold n k => (sample.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω)
          = Measure.pi (fun i : split.fold n k => μ.map (sample.Z i)) := hmap
      _ = Measure.pi (fun _ : split.fold n k => P_Z) := by
          congr with i
          rw [← (sample.identDist i).map_eq, sample.law]
  have hindep : ∀ n,
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : split.fold n k) => sample.Z i ω) inferInstance) μ := by
    intro n
    exact ProbabilityTheory.indep_bot_left _
  -- |fold n k| ≤ n via cover.
  have hfold_le_n : ∀ n, (split.fold n k).card ≤ n := by
    intro n
    have h_cov := split.cover n
    have hsub : split.fold n k ⊆ Finset.range n := by
      have : split.fold n k ⊆
          (Finset.univ : Finset (Fin K)).biUnion (split.fold n) :=
        Finset.subset_biUnion_of_mem _ (Finset.mem_univ k)
      rw [h_cov] at this
      exact this
    calc
      (split.fold n k).card ≤ (Finset.range n).card := Finset.card_le_card hsub
      _ = n := Finset.card_range n
  -- Second-moment bound.
  have hbound : ∀ n, 0 < (split.fold n k).card →
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n hn_fold
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := split.fold n k) hn_fold (W := sample.Z)
      (fun i _ => sample.meas i)
      (⊥ : MeasurableSpace Ω) bot_le (hindep n) (hiid n)
      (fun _ z => ψ z)
      (by
        change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z => ψ p.2)
        exact hψ_meas.comp measurable_snd)
      (fun _ => hψ_memLp)
    simp only [hψ_mean, sub_zero] at hraw
    -- The original bound is on (1/√|fold|) Σ. We want (1/√n) Σ. Since |fold|/n ≤ 1,
    -- (1/√n)² Σ² ≤ (1/√|fold|)² Σ² (because (1/n) ≤ (1/|fold|)).
    have hn_pos : 0 < n := lt_of_lt_of_le hn_fold (hfold_le_n n)
    have hn_R : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hfold_R : 0 < ((split.fold n k).card : ℝ) := by exact_mod_cast hn_fold
    have hfold_le_n_R : ((split.fold n k).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hfold_le_n n
    have hinv_le : (n : ℝ)⁻¹ ≤ ((split.fold n k).card : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hn_R hfold_R]
      exact hfold_le_n_R
    -- Pointwise: (1/√n)² ≤ (1/√|fold|)².
    have hpoint : ∀ ω,
        ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ≤
          ENNReal.ofReal
            (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) := by
      intro ω
      apply ENNReal.ofReal_le_ofReal
      set S := ∑ i ∈ split.fold n k, ψ (sample.Z i ω)
      have h_sqr_n : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hn_R.le]
      have h_sqr_fold : (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ ^ 2 =
          ((split.fold n k).card : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hfold_R.le]
      have hL : ((Real.sqrt (n : ℝ))⁻¹ * S) ^ 2 = (n : ℝ)⁻¹ * S ^ 2 := by
        rw [mul_pow, h_sqr_n]
      have hR : ((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ * S) ^ 2 =
          ((split.fold n k).card : ℝ)⁻¹ * S ^ 2 := by
        rw [mul_pow, h_sqr_fold]
      rw [hL, hR]
      exact mul_le_mul_of_nonneg_right hinv_le (sq_nonneg _)
    have hint_le :
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ :=
      lintegral_mono hpoint
    refine hint_le.trans ?_
    refine hraw.trans ?_
    simp [N]
  have hbound_all : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2 + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos ((split.fold n k).card) with hzero | hpos
    · have hfold_empty : split.fold n k = ∅ := Finset.card_eq_zero.mp hzero
      simp [hfold_empty]
    · exact (hbound n hpos).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hY_aemeas : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) μ := by
    intro n
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => hψ_meas.comp (sample.meas i)))).aemeasurable
  have hbig : IsBigOp
      (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => Real.sqrt (N ^ 2 + 1)) μ :=
    IsBigOp.of_sq_lintegral_le hY_aemeas (fun _ => by positivity)
      (Eventually.of_forall fun _ => by positivity) hbound_all
  exact hbig.const_rate_collapse (Real.sqrt_nonneg _)

private lemma IsLittleOp_zero_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} :
    IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hzero :
      (fun n : ℕ => μ {ω : Ω | ε * (fun _ => (1 : ℝ)) n ≤ ‖(0 : ℝ)‖}) =
        fun _ => (0 : ENNReal) := by
    funext n
    simp [not_le.mpr hε]
  rw [hzero]
  exact tendsto_const_nhds

/-- Given [two random sequences, a deterministic rate, and a measure](hyp:Ω,μ,X,Y,r), if [the
first sequence is little-o in probability at that rate](hyp:hX) and [the sequences are pointwise
equal for all sufficiently large indices](hyp:hXY), then [the second has the
same little-o property](goal). -/
lemma IsLittleOp_congr_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hX : IsLittleOp X r μ)
    (hXY : ∀ᶠ n in atTop, ∀ ω, Y n ω = X n ω) :
    IsLittleOp Y r μ := by
  intro ε hε
  exact (hX ε hε).congr' (hXY.mono fun n hn => by
    congr 1
    ext ω
    simp [hn ω])

/-- Given [two random sequences and a measure](hyp:Ω,μ,X,Y), if [each sequence is little-o in
probability relative to one](hyp:hX,hY), then [their sum is also little-o relative to one](goal). -/
lemma IsLittleOp_add_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ}
    (hX : IsLittleOp X (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Y (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => X n ω + Y n ω) (fun _ => (1 : ℝ)) μ :=
  Causalean.Stat.IsLittleOp.add_one hX hY

/-- Given [a real constant, random sequence, and measure](hyp:Ω,μ,a,X), if [the sequence is
little-o in probability relative to one](hyp:hX), then [its constant multiple is too](goal). -/
lemma IsLittleOp_const_mul_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (a : ℝ) {X : ℕ → Ω → ℝ}
    (hX : IsLittleOp X (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => a * X n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  by_cases ha : a = 0
  · subst a
    have hzero :
        (fun n => μ {ω | ε * (fun _ => (1 : ℝ)) n ≤ ‖0 * X n ω‖}) =
          fun _ => (0 : ENNReal) := by
      funext n
      simp [not_le.mpr hε]
    rw [hzero]
    exact tendsto_const_nhds
  · have hscale_pos : 0 < ε / |a| := div_pos hε (abs_pos.mpr ha)
    have hXt := hX (ε / |a|) hscale_pos
    refine hXt.congr' ?_
    filter_upwards with n
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, mul_one, norm_mul, Real.norm_eq_abs]
    rw [div_le_iff₀ (abs_pos.mpr ha)]
    ring_nf

/-- Given [a finite index set, a family of random sequences, and a measure](hyp:Ω,ι,μ,s,f), if
[every selected sequence is little-o in probability relative to one](hyp:h), then [their finite sum
is also little-o relative to one](goal). -/
lemma IsLittleOp_finset_sum_one
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → ℕ → Ω → ℝ)
    (h : ∀ i ∈ s, IsLittleOp (f i) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => ∑ i ∈ s, f i n ω) (fun _ => (1 : ℝ)) μ := by
  classical
  revert h
  refine Finset.induction_on s ?base ?step
  · intro h
    simpa using (IsLittleOp_zero_one (Ω := Ω) (μ := μ))
  · intro a s has ih h
    have ha : IsLittleOp (f a) (fun _ => (1 : ℝ)) μ :=
      h a (Finset.mem_insert_self a s)
    have hs :
        IsLittleOp (fun n ω => ∑ i ∈ s, f i n ω) (fun _ => (1 : ℝ)) μ := by
      apply ih
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    have hadd := IsLittleOp_add_one ha hs
    simpa [Finset.sum_insert, has, add_comm, add_left_comm, add_assoc] using hadd

/-- For [a finite-measure population space](hyp:Ω,μ), [a deterministic real sequence and
its proposed limit](hyp:a,c), if [the sequence converges to that limit](hyp:ha), then [viewing
the sequence as constant random variables makes it bounded in probability](goal). -/
lemma deterministic_tendsto_isBigOp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {a : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    IsBigOp (fun n (_ : Ω) => a n) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  refine ⟨|c| + 2, by positivity, ?_⟩
  have hbound : ∀ᶠ n in atTop, |a n| ≤ |c| + 1 := by
    have hdist := (Metric.tendsto_nhds.mp ha) (1 : ℝ) zero_lt_one
    filter_upwards [hdist] with n hn
    have habs_sub : |a n - c| < 1 := by
      simpa [Real.dist_eq] using hn
    calc
      |a n| = |(a n - c) + c| := by ring_nf
      _ ≤ |a n - c| + |c| := abs_add_le (a n - c) c
      _ ≤ |c| + 1 := by linarith
  filter_upwards [hbound] with n hn
  have hempty :
      {ω : Ω | (|c| + 2) * (fun _ => (1 : ℝ)) n ≤ ‖a n‖} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, mul_one, Real.norm_eq_abs,
      Set.mem_empty_iff_false, iff_false]
    linarith
  rw [hempty]
  simp

end OrthogonalMoments
end Estimation
end Causalean
