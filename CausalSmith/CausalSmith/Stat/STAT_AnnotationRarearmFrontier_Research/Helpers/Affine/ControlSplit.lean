module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ProductExperiment

/-!
The common binomial reconstruction of combined control counts into the two
original channels, with exact independent-Poisson likelihood readback.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:hu,hv,hr,ht,u,v,r,k,s), Splitting a combined Poisson count by the channel intensity ratio gives
exactly the two independent channel likelihoods.  This gives [the stated result](goal).-/
-- @node: affine_poisson_binomial_split
lemma affine_poisson_binomial_split
    (u v r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (ht : 0 < u + v) (k s : ℕ) :
    (poissonMeasure (Real.toNNReal ((u + v) * r))).real {k + s} *
        (binomial (k + s)
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval)).real {k} =
      (poissonMeasure (Real.toNNReal (u * r))).real {k} *
        (poissonMeasure (Real.toNNReal (v * r))).real {s} := by
  rw [poissonMeasure_real_singleton, binomial_real_singleton,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hfacNat :=
    Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k s)
  rw [Nat.add_sub_cancel_left] at hfacNat
  have hfac :
      ((k + s).choose k : ℝ) * (k.factorial : ℝ) * (s.factorial : ℝ) =
        ((k + s).factorial : ℝ) := by
    exact_mod_cast hfacNat
  simp only [Nat.add_sub_cancel_left]
  rw [Real.coe_toNNReal _ (mul_nonneg (add_nonneg hu hv) hr),
    Real.coe_toNNReal _ (mul_nonneg hu hr),
    Real.coe_toNNReal _ (mul_nonneg hv hr)]
  rw [show (1 - u / (u + v) : ℝ) = v / (u + v) by
    field_simp
    ring]
  have hexp : Real.exp (-((u + v) * r)) =
      Real.exp (-(u * r)) * Real.exp (-(v * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, pow_add, mul_pow, mul_pow, div_pow, div_pow]
  field_simp
  rw [← hfac]
  ring

/-- Conditional channel split of a combined control count. -/
-- @node: affineControlSplitLaw
noncomputable def affineControlSplitLaw (q : unitInterval) (c : Nat) : Measure (Nat × Nat) :=
  (binomial c q).map (fun k => (k, c - k))

/-- The split law is a probability law for every combined count. -/
-- @node: affineControlSplitLaw_isProbabilityMeasure
instance affineControlSplitLaw_isProbabilityMeasure (q : unitInterval) (c : Nat) :
    IsProbabilityMeasure (affineControlSplitLaw q c) := by
  unfold affineControlSplitLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- [Under the stated inputs and conditions](hyp:q,c,k,s), A split singleton has nonzero likelihood only at the matching total.  This gives [the stated result](goal).-/
-- @node: affineControlSplitLaw_singleton
lemma affineControlSplitLaw_singleton (q : unitInterval) (c k s : Nat) :
    affineControlSplitLaw q c {(k, s)} =
      if c = k + s then (binomial c q) {k} else 0 := by
  rw [affineControlSplitLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  by_cases hc : c = k + s
  · rw [if_pos hc]
    congr 1
    ext j
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · exact fun h => h.1
    · intro h
      subst j
      exact ⟨rfl, by omega⟩
  · rw [if_neg hc]
    have hsub : (fun j => (j, c - j)) ⁻¹' {(k, s)} ⊆ {k} := by
      intro j hj
      exact (Prod.mk.inj hj).1
    by_cases hk : k ≤ c
    · have hempty : (fun j => (j, c - j)) ⁻¹' {(k, s)} = ∅ := by
        ext j
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hj
        subst j
        omega
      rw [hempty, measure_empty]
    · have hz : (binomial c q) {k} = 0 := by
        rw [binomial_singleton, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      exact le_antisymm ((measure_mono hsub).trans_eq hz) zero_le

/-- The channel split is a common Markov kernel, independent of latent masses
and of the hypothesis's outcome marks. -/
-- @node: affineControlSplitKernel
noncomputable def affineControlSplitKernel (q : unitInterval) : Kernel Nat (Nat × Nat) :=
  Kernel.ofFunOfCountable (affineControlSplitLaw q)

/-- Each control reconstruction has total mass one. -/
-- @node: affineControlSplitKernel_isMarkovKernel
instance affineControlSplitKernel_isMarkovKernel (q : unitInterval) :
    IsMarkovKernel (affineControlSplitKernel q) where
  isProbabilityMeasure c := by
    change IsProbabilityMeasure (affineControlSplitLaw q c)
    infer_instance

/-- [Under the stated inputs and conditions](hyp:hu,hw,hr,huw,u,w,r), Applying the common control split to a combined Poisson count recovers
both independent Poisson control channels, without dropping either channel.  This gives [the stated result](goal).-/
-- @node: affineControlSplitKernel_poisson
lemma affineControlSplitKernel_poisson
    (u w r : Real) (hu : 0 ≤ u) (hw : 0 ≤ w) (hr : 0 ≤ r)
    (huw : 0 < u + w) :
    let q : unitInterval := ⟨u / (u + w), by
      constructor
      · positivity
      · rw [div_le_one huw]; linarith⟩
    (affineControlSplitKernel q) ∘ₘ poissonMeasure (Real.toNNReal ((u + w) * r)) =
      (poissonMeasure (Real.toNNReal (u * r))).prod
        (poissonMeasure (Real.toNNReal (w * r))) := by
  intro q
  apply Measure.ext_of_singleton
  rintro ⟨k, s⟩
  rw [Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  change (∫⁻ c : Nat, affineControlSplitLaw q c {(k, s)}
    ∂poissonMeasure (Real.toNNReal ((u + w) * r))) = _
  simp only [affineControlSplitLaw_singleton]
  rw [lintegral_countable']
  simp only [ite_mul, zero_mul]
  rw [tsum_eq_single (k + s)]
  · rw [if_pos rfl]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
      ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul,
      ← measureReal_def, ← measureReal_def]
    rw [mul_comm ((binomial (k + s) q).real {k})]
    exact affine_poisson_binomial_split u w r hu hw hr huw k s
  · intro c hc
    rw [if_neg hc]

/-- [Under the stated inputs and conditions](hyp:X,mu,hu,hw,hr,huw,u,w,r), Keeping independent existing coordinates while splitting a control count
preserves their laws and restores the independent channel controls.  This gives [the stated result](goal).-/
-- @node: affineControlSplitKernel_with_common
lemma affineControlSplitKernel_with_common
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (u w r : Real) (hu : 0 ≤ u) (hw : 0 ≤ w) (hr : 0 ≤ r)
    (huw : 0 < u + w) :
    let q : unitInterval := ⟨u / (u + w), by
      constructor
      · positivity
      · rw [div_le_one huw]; linarith⟩
    (Kernel.id ∥ₖ affineControlSplitKernel q) ∘ₘ
        (mu.prod (poissonMeasure (Real.toNNReal ((u + w) * r)))) =
      mu.prod ((poissonMeasure (Real.toNNReal (u * r))).prod
        (poissonMeasure (Real.toNNReal (w * r)))) := by
  intro q
  rw [Measure.comp_eq_comp_const_apply, ← Kernel.prod_const,
    Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_const,
    Kernel.prod_apply, Kernel.const_apply, Kernel.const_apply,
    affineControlSplitKernel_poisson u w r hu hw hr huw]

/-- Reconstruct the full rare-cell control channels while keeping both
complete treated outcome counts and the auxiliary treated count. -/
-- @node: affineCellControlSplitKernel
noncomputable def affineCellControlSplitKernel (q : unitInterval) :
    Kernel MarkedPoissonObservation ((Nat × Nat) × (Nat × (Nat × Nat))) :=
  Kernel.id ∥ₖ (Kernel.id ∥ₖ affineControlSplitKernel q)

/-- Full rare-cell control reconstruction is a common probability kernel. -/
-- @node: affineCellControlSplitKernel_isMarkovKernel
instance affineCellControlSplitKernel_isMarkovKernel (q : unitInterval) :
    IsMarkovKernel (affineCellControlSplitKernel q) := by
  unfold affineCellControlSplitKernel
  infer_instance

/-- [Under the stated inputs and conditions](hyp:mu,nu,kappa,eta,X,Y,Z,W), Independent coordinate reconstruction commutes with the product law.  This gives [the stated result](goal).-/
-- @node: affine_parallelComp_prod
lemma affine_parallelComp_prod
    {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W]
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    (kappa : Kernel X Z) (eta : Kernel Y W)
    [IsSFiniteKernel kappa] [IsSFiniteKernel eta] :
    (kappa ∥ₖ eta) ∘ₘ mu.prod nu = (kappa ∘ₘ mu).prod (eta ∘ₘ nu) := by
  rw [Measure.comp_eq_comp_const_apply, ← Kernel.prod_const,
    Kernel.parallelComp_comp_prod, Kernel.comp_const, Kernel.comp_const,
    Kernel.prod_apply, Kernel.const_apply, Kernel.const_apply]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hyp,z,ha,he,he',hu,hw,huw,B,eps,u,w), Splitting an actual conditional rare-cell law restores the independent
complete and auxiliary control counts, while leaving all treated counts intact.  This gives [the stated result](goal).-/
-- @node: affineCellControlSplitKernel_law
lemma affineCellControlSplitKernel_law {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L)
    (ha : 0 ≤ B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huw : 0 < u + w) :
    let q : unitInterval := ⟨u / (u + w), by
      constructor
      · positivity
      · rw [div_le_one huw]; linarith⟩
    let alpha := B / (100 * (L : Real) ^ 2)
    let s1 := alpha + (1 - eps) * latentNode sigma z
    let s0 := (1 - eps) * (alpha / eps) + eps * latentNode sigma z
    let mean := match z with
      | none => (0 : Real)
      | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
    affineCellControlSplitKernel q ∘ₘ affineCellPoissonLaw sigma u w hyp z =
      ((poissonMeasure (Real.toNNReal (u * s1 * mean))).prod
        (poissonMeasure (Real.toNNReal (u * s1 * (1 - mean))))).prod
        ((poissonMeasure (Real.toNNReal (w * s1))).prod
          ((poissonMeasure (Real.toNNReal (u * s0))).prod
            (poissonMeasure (Real.toNNReal (w * s0))))) := by
  intro q alpha s1 s0 mean
  have hv : 0 ≤ latentNode sigma z := by
    cases z with
    | none => exact le_rfl
    | some i => exact (sigma.mem i).1
  have hs0 : 0 ≤ s0 := by
    dsimp only [s0]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr he') (div_nonneg ha he.le))
      (mul_nonneg he.le hv)
  unfold affineCellControlSplitKernel affineCellPoissonLaw
  rw [affine_parallelComp_prod, affineControlSplitKernel_with_common _ u w _ hu hw hs0 huw]
  rw [Measure.id_comp]
  rfl


/-- The conditional rare-cell law with separate controls in the original two
channels. All five potentially nonzero atom counts are retained. -/
-- @node: affineCellFullPoissonLaw
noncomputable def affineCellFullPoissonLaw {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L) :
    Measure ((Nat × Nat) × (Nat × (Nat × Nat))) :=
  let alpha := B / (100 * (L : Real) ^ 2)
  let s1 := alpha + (1 - eps) * latentNode sigma z
  let s0 := (1 - eps) * (alpha / eps) + eps * latentNode sigma z
  let mean := match z with
    | none => (0 : Real)
    | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
  ((poissonMeasure (Real.toNNReal (u * s1 * mean))).prod
    (poissonMeasure (Real.toNNReal (u * s1 * (1 - mean))))).prod
    ((poissonMeasure (Real.toNNReal (w * s1))).prod
      ((poissonMeasure (Real.toNNReal (u * s0))).prod
        (poissonMeasure (Real.toNNReal (w * s0)))))

/-- The full conditional cell law has total mass one. -/
-- @node: affineCellFullPoissonLaw_isProbabilityMeasure
instance affineCellFullPoissonLaw_isProbabilityMeasure {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L) :
    IsProbabilityMeasure (affineCellFullPoissonLaw sigma u w hyp z) := by
  unfold affineCellFullPoissonLaw
  infer_instance

/-- The actual core/filler predictive law with control channels restored. -/
-- @node: affineCellFullPoissonPredictive
noncomputable def affineCellFullPoissonPredictive {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) :
    Measure ((Nat × Nat) × (Nat × (Nat × Nat))) :=
  ∑ z : Latent L, latentPMF sigma z • affineCellFullPoissonLaw sigma u w hyp z

/-- Mixing full conditional cell laws gives a probability measure. -/
-- @node: affineCellFullPoissonPredictive_isProbabilityMeasure
instance affineCellFullPoissonPredictive_isProbabilityMeasure {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) :
    IsProbabilityMeasure (affineCellFullPoissonPredictive sigma u w hyp) := by
  constructor
  simp only [affineCellFullPoissonPredictive, Measure.finsetSum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact (tsum_fintype _).symm.trans (latentPMF sigma).tsum_coe

/-- [Under the stated inputs and conditions](hyp:L,sigma,hyp,ha,he,he',hu,hw,huw,B,eps,u,w), The common channel reconstruction identifies the actual full core/filler
predictive law, rather than merely bounding an abstract postprocessing.  This gives [the stated result](goal).-/
-- @node: affineCellControlSplitKernel_predictive
lemma affineCellControlSplitKernel_predictive {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool)
    (ha : 0 ≤ B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huw : 0 < u + w) :
    let q : unitInterval := ⟨u / (u + w), by
      constructor
      · positivity
      · rw [div_le_one huw]; linarith⟩
    affineCellControlSplitKernel q ∘ₘ affineCellPoissonPredictive sigma u w hyp =
      affineCellFullPoissonPredictive sigma u w hyp := by
  intro q
  have hcond (z : Latent L) :
      affineCellControlSplitKernel q ∘ₘ affineCellPoissonLaw sigma u w hyp z =
        affineCellFullPoissonLaw sigma u w hyp z :=
    affineCellControlSplitKernel_law sigma u w hyp z ha he he' hu hw huw
  ext s hs
  rw [Measure.bind_apply hs (affineCellControlSplitKernel q).aemeasurable]
  simp only [affineCellPoissonPredictive, lintegral_finsetSum_measure,
    lintegral_smul_measure, affineCellFullPoissonPredictive, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [← Measure.bind_apply hs (affineCellControlSplitKernel q).aemeasurable]
  exact congrArg (fun mu => mu s) (hcond z)

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), Restoring both control channels preserves the calibrated joint TV budget
for the independent product of the actual full rare-cell mixtures.  This gives [the stated result](goal).-/
-- @node: affineCellFullPoissonPredictive_product_tv_small
lemma affineCellFullPoissonPredictive_product_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    Causalean.Stat.tvDist
      (Measure.pi fun _ : Fin t.Kstar => affineCellFullPoissonPredictive sigma t.u t.w true)
      (Measure.pi fun _ : Fin t.Kstar => affineCellFullPoissonPredictive sigma t.u t.w false) <
      1 / 64 := by
  intro t
  obtain ⟨_, _, _, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hu : 0 ≤ t.u := by change 0 ≤ 128 * (n : Real); positivity
  have hw : 0 ≤ t.w := by change 0 ≤ 128 * ((n : Real) + m); positivity
  have huw : 0 < t.u + t.w := by
    change 0 < 128 * (n : Real) + 128 * ((n : Real) + m)
    have hnR : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  let q : unitInterval := ⟨t.u / (t.u + t.w), by
    constructor
    · positivity
    · rw [div_le_one huw]; linarith⟩
  have htv : Causalean.Stat.tvDist
      (affineCellFullPoissonPredictive sigma t.u t.w true)
      (affineCellFullPoissonPredictive sigma t.u t.w false) ≤
      Causalean.Stat.tvDist (affineCellPoissonPredictive sigma t.u t.w true)
        (affineCellPoissonPredictive sigma t.u t.w false) := by
    rw [← affineCellControlSplitKernel_predictive sigma t.u t.w true ha.le heps
      (by linarith) hu hw huw,
      ← affineCellControlSplitKernel_predictive sigma t.u t.w false ha.le heps
        (by linarith) hu hw huw]
    exact Causalean.Stat.tvDist_bind_le _ _ (affineCellControlSplitKernel q)
  exact (Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le t.Kstar _ _).trans_lt
    ((mul_le_mul_of_nonneg_left htv (Nat.cast_nonneg t.Kstar)).trans_lt
      (affineCellPoissonPredictive_joint_tv_small n m d eps hn hd heps heps' sigma))

end CausalSmith.Stat.AnnotationRarearmFrontier
