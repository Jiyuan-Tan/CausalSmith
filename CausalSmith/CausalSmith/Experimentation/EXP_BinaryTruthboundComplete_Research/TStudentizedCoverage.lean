import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BlockArray
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.CitedGates
import Causalean.Experimentation.DesignBased.InProb
import Causalean.Experimentation.DesignBased.GaussianCDF
import Causalean.Experimentation.DesignBased.WaldCoverage
import Causalean.Experimentation.DesignBased.Slutsky
import Causalean.Experimentation.DesignBased.IndepSummandsCLT
import Causalean.Experimentation.DesignBased.DependencyCLT

/-! Asymptotic conservative studentized coverage for independently randomized blocks. -/

open scoped BigOperators
open Finset Set Filter Topology

namespace CausalSmith.Experimentation.BinaryTruthbound

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.DesignBased.FiniteDesign

/-- For [a block array, row count, and threshold](hyp:Arr,B,t), [the numerator distribution function](goal) is the randomization probability that the oracle-standardized estimation error does not exceed the threshold. -/
noncomputable def numeratorCDF (Arr : BlockArray) (B : ℕ) (t : ℝ) : ℝ :=
  (rowDesign Arr B).Pr fun w =>
    Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B) ≤ t

/-- For [a block array, row count, significance level, and critical value](hyp:Arr,B,α,zAlpha) satisfying [the stated level condition](hyp:hAlpha) and [normal-quantile condition](hyp:hzAlpha), [the coverage probability](goal) is the randomization probability that the Wald interval contains the target. -/
noncomputable def coverageProbability (Arr : BlockArray) (B : ℕ) (α zAlpha : ℝ)
    (hAlpha : 0 < α ∧ α < 1)
    (hzAlpha : 0 ≤ zAlpha ∧ stdNormalCdf zAlpha = 1 - α / 2) : ℝ :=
  by
    classical
    exact (rowDesign Arr B).Pr fun w =>
      tauBar Arr B ∈ waldInterval Arr B α zAlpha hAlpha hzAlpha w

/-- For [a block array, row count, and threshold](hyp:Arr,B,t), [the feasible studentized distribution function](goal) is the randomization probability for the statistic using the nonnegative estimated variance. -/
noncomputable def feasibleStudentizedCDF (Arr : BlockArray) (B : ℕ) (t : ℝ) : ℝ :=
  (rowDesign Arr B).Pr fun w =>
    Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
      Real.sqrt (max (WHat Arr B w) 0) ≤ t

/-- The normalized summand envelope used in the bounded product-design CLT. -/
noncomputable def blockCLTEnvelope (Arr : BlockArray) (M : ℝ) (B : ℕ) : ℝ :=
  2 * M / Real.sqrt ((B : ℝ) * VBar Arr B)

/-- Under [nondegenerate limiting average variance](hyp:hV), [the normalized score envelope converges to zero](goal). -/
-- @node: blockCLTEnvelope_tendsto_zero
lemma blockCLTEnvelope_tendsto_zero (Arr : BlockArray) (M V : ℝ)
    (hV : NondegenerateAverageVariance Arr V) :
    Tendsto (blockCLTEnvelope Arr M) atTop (𝓝 0) := by
  have hprod : Tendsto (fun B : ℕ => (B : ℝ) * VBar Arr B) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos hV.1 hV.2
  have hsqrt : Tendsto (fun B : ℕ => Real.sqrt ((B : ℝ) * VBar Arr B))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hprod
  change Tendsto (fun B : ℕ => 2 * M /
    Real.sqrt ((B : ℝ) * VBar Arr B)) atTop (𝓝 0)
  exact hsqrt.const_div_atTop (2 * M)

/-- Under [nondegenerate limiting average variance](hyp:hV), [the cubic normalized-envelope remainder converges to zero](goal). -/
-- @node: blockCLTEnvelope_cubic_rate
lemma blockCLTEnvelope_cubic_rate (Arr : BlockArray) (M V : ℝ)
    (hV : NondegenerateAverageVariance Arr V) :
    Tendsto (fun B : ℕ => (B : ℝ) * (blockCLTEnvelope Arr M B) ^ 3)
      atTop (𝓝 0) := by
  have hprod : Tendsto (fun B : ℕ => (B : ℝ) * VBar Arr B) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos hV.1 hV.2
  have hsqrt : Tendsto (fun B : ℕ => Real.sqrt ((B : ℝ) * VBar Arr B))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hprod
  have hden : Tendsto
      (fun B : ℕ => Real.sqrt ((B : ℝ) * VBar Arr B) * VBar Arr B)
      atTop atTop := hsqrt.atTop_mul_pos hV.1 hV.2
  have hlim : Tendsto
      (fun B : ℕ => (2 * M) ^ 3 /
        (Real.sqrt ((B : ℝ) * VBar Arr B) * VBar Arr B))
      atTop (𝓝 0) := hden.const_div_atTop ((2 * M) ^ 3)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (hV.2.eventually (eventually_gt_nhds hV.1))] with B hB hVB
  unfold blockCLTEnvelope
  have hBV : 0 ≤ (B : ℝ) * VBar Arr B := mul_nonneg (Nat.cast_nonneg _) hVB.le
  have hBsqrt : (Real.sqrt ((B : ℝ) * VBar Arr B)) ^ 2 =
      (B : ℝ) * VBar Arr B := Real.sq_sqrt hBV
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hVne : VBar Arr B ≠ 0 := ne_of_gt hVB
  field_simp
  rw [hBsqrt]
  ring

/-- Under [blockwise conservativeness](hyp:hCons), [the average true variance is no greater than the average variance bound](goal). -/
-- @node: VBar_le_WBar
lemma VBar_le_WBar (Arr : BlockArray) (hCons : BlockConservativeness Arr) (B : ℕ) :
    VBar Arr B ≤ WBar Arr B := by
  unfold VBar WBar
  gcongr
  exact hCons B _

/-- The exact Causalean interface instantiated after encoding the row-law score marginals as a
finite product design.  The studentized theorem derives both limit premises below from its score
bound and positive limiting average variance. -/
private lemma directProductCDFCLT
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {Ω : ∀ n, ι n → Type*} [∀ n i, Fintype (Ω n i)]
    [∀ n i, MeasurableSpace (Ω n i)] [∀ n i, MeasurableSingletonClass (Ω n i)]
    (D : ∀ n, ∀ i, FiniteDesign (Ω n i)) (Y : ∀ n, ∀ i, Ω n i → ℝ)
    (bound : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bound n)
    (hboundZero : Tendsto bound atTop (𝓝 0))
    (hbounded : ∀ n i a, |Y n i a| ≤ bound n)
    (hcardRate : Tendsto (fun n => (Fintype.card (ι n) : ℝ) * (bound n) ^ 3)
      atTop (𝓝 0))
    (hmean : ∀ n i, (D n i).E (Y n i) = 0)
    (hvar : ∀ n, (prodDesign (D n)).Var (fun w => ∑ i, Y n i (w i)) = 1)
    (t : ℝ) :
    Tendsto (fun n => (prodDesign (D n)).Pr (fun w => (∑ i, Y n i (w i)) ≤ t))
      atTop (𝓝 (stdNormalCdf t)) := by
  exact prodDesign_clt D Y bound hboundNonneg hboundZero hbounded hcardRate hmean hvar t

set_option maxHeartbeats 800000 in
-- The finite double-sum variance normalization needs extra elaboration budget.
/-- Transfer the direct product-design CLT back to the row law using the assumed factorization of
the block score/bound pairs.  The two analytic rate premises are derived by the caller. -/
-- @node: numeratorCDF_tendsto_from_productCLT
private lemma numeratorCDF_tendsto_from_productCLT (Arr : BlockArray) (M V : ℝ)
    (_hLindebergFellerIndependentArray_of_gate : LindebergFellerIndependentArray)
    (hInd : BlockIndependence Arr)
    (hBound : UniformScoreBound Arr M)
    (hV : NondegenerateAverageVariance Arr V)
    (hEnvelopeZero : Tendsto (blockCLTEnvelope Arr M) atTop (𝓝 0))
    (hEnvelopeRate :
      Tendsto (fun B : ℕ => (B : ℝ) * (blockCLTEnvelope Arr M B) ^ 3) atTop (𝓝 0)) :
    ∀ t : ℝ, Tendsto (fun B => numeratorCDF Arr B t) atTop (𝓝 (stdNormalCdf t)) := by
  classical
  letI : ∀ B, MeasurableSpace (∀ j : Fin B, Arr.Omega B j) := fun _ => ⊤
  let Y : ∀ B, Fin B → (∀ j : Fin B, Arr.Omega B j) → ℝ :=
    fun B j w => Arr.X B j (w j) - blockTau Arr B j
  have hYind : ∀ B, ProbabilityTheory.iIndepFun (Y B) (rowDesign Arr B).toMeasure := by
    intro B
    have hscore := hInd.2 B
    have hcomp := hscore.comp (fun j x => x - blockTau Arr B j) (fun _ => by fun_prop)
    simpa [Y, Function.comp_def, rowDesign] using hcomp
  let Dep : ∀ B, Causalean.SteinMethod.DepGraph (Y B) (rowDesign Arr B).toMeasure :=
    fun B => {
      G := fun i j => i = j
      decG := inferInstance
      refl := fun _ => rfl
      symm := fun _ _ h => h.symm
      meas := fun _ => Measurable.of_discrete
      indep := fun A C hAC => by
        have hdisj : Disjoint A C := by
          rw [Finset.disjoint_left]
          intro i hiA hiC
          exact hAC i hiA i hiC rfl
        exact (hYind B).indepFun_finset A C hdisj (fun _ => Measurable.of_discrete)
    }
  have hdeg : ∀ B i, ((Dep B).nbhd i).card ≤ 1 := by
    intro B i
    have hsub : (Dep B).nbhd i ⊆ {i} := by
      intro j hj
      have := (Dep B).mem_nbhd_iff.mp hj
      exact Finset.mem_singleton.mpr this.symm
    exact (Finset.card_le_card hsub).trans (by simp)
  have hYbound : ∀ B j w, |Y B j w| ≤ 2 * M := by
    intro B j w
    have hmean_abs : |blockTau Arr B j| ≤ M := by
      unfold blockTau FiniteDesign.E
      calc
        |∑ w, (Arr.rowLaw B).p w * Arr.X B j (w j)| ≤
            ∑ w, |(Arr.rowLaw B).p w * Arr.X B j (w j)| :=
              abs_sum_le_sum_abs _ Finset.univ
        _ ≤ ∑ w, (Arr.rowLaw B).p w * M := by
          apply Finset.sum_le_sum
          intro w _
          rw [abs_mul, abs_of_nonneg ((Arr.rowLaw B).p_nonneg w)]
          exact mul_le_mul_of_nonneg_left (hBound.2 B j (w j))
            ((Arr.rowLaw B).p_nonneg w)
        _ = M := by rw [← Finset.sum_mul, (Arr.rowLaw B).p_sum, one_mul]
    unfold Y
    exact (abs_sub _ _).trans (by linarith [hBound.2 B j (w j)])
  have hYmean : ∀ B j, (rowDesign Arr B).E (Y B j) = 0 := by
    intro B j
    simp [Y, rowDesign, blockTau, FiniteDesign.E_sub, FiniteDesign.E_const]
  have hvar : ∀ B, (rowDesign Arr B).E
      (fun w => Causalean.SteinMethod.depSum (Y B) w ^ 2) = (B : ℝ) * VBar Arr B := by
    intro B
    have hmeanSum : (rowDesign Arr B).E (Causalean.SteinMethod.depSum (Y B)) = 0 := by
      unfold Causalean.SteinMethod.depSum
      rw [(rowDesign Arr B).E_sum]
      simp [hYmean]
    have hEeqVar : (rowDesign Arr B).E
        (fun w => Causalean.SteinMethod.depSum (Y B) w ^ 2) =
        (rowDesign Arr B).Var (Causalean.SteinMethod.depSum (Y B)) := by
      rw [FiniteDesign.Var_eq, hmeanSum]
      ring
    rw [hEeqVar]
    have hcov (i j : Fin B) (hij : i ≠ j) :
        (rowDesign Arr B).Cov (Y B i) (Y B j) = 0 := by
      rw [FiniteDesign.Cov_eq]
      have hmul := ((hYind B).indepFun hij).integral_mul_eq_mul_integral
        (Measurable.of_discrete.aestronglyMeasurable)
        (Measurable.of_discrete.aestronglyMeasurable)
      rw [(rowDesign Arr B).integral_toMeasure,
        (rowDesign Arr B).integral_toMeasure,
        (rowDesign Arr B).integral_toMeasure] at hmul
      have hmul' : (rowDesign Arr B).E (fun z => Y B i z * Y B j z) =
          (rowDesign Arr B).E (Y B i) * (rowDesign Arr B).E (Y B j) := by
        exact hmul
      rw [hmul', sub_self]
    rw [show Causalean.SteinMethod.depSum (Y B) =
        fun w => ∑ j : Fin B, 1 * Y B j w by funext w; simp [Causalean.SteinMethod.depSum]]
    rw [(rowDesign Arr B).Var_linear_comb Finset.univ (fun _ => 1) (Y B)]
    simp only [one_mul]
    calc
      (∑ i, ∑ j, (rowDesign Arr B).Cov (Y B i) (Y B j)) =
          ∑ i, (rowDesign Arr B).Var (Y B i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · exact (rowDesign Arr B).Cov_self (Y B i)
            · intro j _ hji
              exact hcov i j hji.symm
            · simp
      _ = ∑ i, sigmaSq Arr B i := by
        apply Finset.sum_congr rfl
        intro i _
        unfold Y sigmaSq rowDesign blockTau FiniteDesign.Var
        congr 1
        funext w
        simp only [FiniteDesign.E_sub, FiniteDesign.E_const, sub_self, sub_zero]
      _ = (B : ℝ) * VBar Arr B := by
        unfold VBar
        by_cases hB : B = 0
        · subst B
          simp
        · field_simp
  have hvc : ∀ᶠ B in atTop, (V / 2) * (Fintype.card (Fin B) : ℝ) ≤
      (B : ℝ) * VBar Arr B := by
    filter_upwards [hV.2.eventually
      (eventually_gt_nhds (by linarith [hV.1] : V / 2 < V))] with B hVB
    simp only [Fintype.card_fin]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hVB.le (Nat.cast_nonneg B))
  have hcard : Tendsto (fun B => Fintype.card (Fin B)) atTop atTop := by
    rw [show (fun B => Fintype.card (Fin B)) = id by funext B; simp]
    exact tendsto_id
  intro t
  have hclt := dependency_studentized_cdf (rowDesign Arr) Y Dep 1 hdeg (2 * M)
    (mul_nonneg (by norm_num) hBound.1) hYbound hYmean
    (fun B => (B : ℝ) * VBar Arr B) hvar (V / 2) (by linarith [hV.1]) hvc hcard t
  refine hclt.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hV.2.eventually (eventually_gt_nhds hV.1)] with B hB hVB
  apply (rowDesign Arr B).Pr_congr
  intro w
  change (Causalean.SteinMethod.depSum (Y B) w /
      Real.sqrt ((B : ℝ) * VBar Arr B) ≤ t) ↔
    (Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
      Real.sqrt (VBar Arr B) ≤ t)
  simp only [Y, Causalean.SteinMethod.depSum]
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hVne : VBar Arr B ≠ 0 := ne_of_gt hVB
  apply iff_of_eq
  congr 1
  rw [Real.sqrt_mul (Nat.cast_nonneg B)]
  unfold tauHat tauBar
  rw [Finset.sum_sub_distrib]
  have hsqrtB : Real.sqrt (B : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsqrtV : Real.sqrt (VBar Arr B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hVB)
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg B)]

/-- Given [a valid significance level](hyp:hAlpha), [a nonnegative normal critical value](hyp:hz), [a positive row count](hyp:hB), and [a realized assignment vector](hyp:w), [membership in the Wald interval is equivalent to the corresponding absolute-error bound](goal). -/
lemma mem_waldInterval_iff_abs_error (Arr : BlockArray) (B : ℕ) (α z : ℝ)
    (hAlpha : 0 < α ∧ α < 1)
    (hz : 0 ≤ z ∧ stdNormalCdf z = 1 - α / 2)
    (hB : 0 < B) (w : ∀ j : Fin B, Arr.Omega B j) :
    tauBar Arr B ∈ waldInterval Arr B α z hAlpha hz w ↔
      |tauHat Arr B w - tauBar Arr B| ≤
        z * Real.sqrt (max (WHat Arr B w) 0 / B) := by
  unfold waldInterval
  rw [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

/-- If [the oracle-studentized distribution functions converge to the standard normal law](hyp:hclt) and [the band half-width is nonnegative](hyp:hc), then [the symmetric-band probability has at least its Gaussian limiting probability](goal). -/
-- @node: numerator_symmetric_band_liminf
lemma numerator_symmetric_band_liminf (Arr : BlockArray)
    (hclt : ∀ t : ℝ, Tendsto (fun B => numeratorCDF Arr B t) atTop
      (𝓝 (stdNormalCdf t))) (c : ℝ) (hc : 0 ≤ c) :
    stdNormalCdf c - stdNormalCdf (-c) ≤
      Filter.liminf (fun B => (rowDesign Arr B).Pr (fun w =>
        -c ≤ Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
            Real.sqrt (VBar Arr B) ∧
        Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
            Real.sqrt (VBar Arr B) ≤ c)) atTop := by
  let S : ℕ → ℝ := fun B => numeratorCDF Arr B c
  let Lo : ℕ → ℝ := fun B => numeratorCDF Arr B (-c)
  let J : ℕ → ℝ := fun B => (rowDesign Arr B).Pr (fun w =>
    -c ≤ Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B) ∧
    Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B) ≤ c)
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf c)) := hclt c
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-c))) := hclt (-c)
  have hlim : Tendsto (fun B => S B - Lo B) atTop
      (𝓝 (stdNormalCdf c - stdNormalCdf (-c))) := hS.sub hLo
  have hbound : ∀ B, S B - Lo B ≤ J B := by
    intro B
    let T : (∀ j : Fin B, Arr.Omega B j) → ℝ := fun w =>
      Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B)
    have hsplit := (rowDesign Arr B).Pr_split (fun w => T w ≤ c) (fun w => T w ≤ -c)
    have hfirst : (rowDesign Arr B).Pr (fun w => T w ≤ c ∧ T w ≤ -c) = Lo B := by
      apply (rowDesign Arr B).Pr_congr
      intro w
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.trans (by linarith), h⟩
    have hdiff : S B - Lo B =
        (rowDesign Arr B).Pr (fun w => T w ≤ c ∧ ¬ T w ≤ -c) := by
      have heq : S B = (rowDesign Arr B).Pr (fun w => T w ≤ c ∧ T w ≤ -c) +
          (rowDesign Arr B).Pr (fun w => T w ≤ c ∧ ¬ T w ≤ -c) := by
        simpa [S, Lo, T, numeratorCDF] using hsplit
      rw [heq, hfirst]
      ring
    rw [hdiff]
    apply (rowDesign Arr B).Pr_mono
    intro w hw
    exact ⟨le_of_not_ge hw.2, hw.1⟩
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun B => S B - Lo B) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop J :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      (fun B => (rowDesign Arr B).Pr_le_one _)
  calc
    stdNormalCdf c - stdNormalCdf (-c) =
        Filter.liminf (fun B => S B - Lo B) atTop := hlim.liminf_eq.symm
    _ ≤ Filter.liminf J atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hbdd hcobdd

/-- For [a block array and the stated score, variance, and critical-value constants](hyp:Arr,M,V,α,zAlpha), [the listed oracle and feasible studentized central-limit and conservative-coverage conclusions hold under their displayed assumptions](goal). -/
-- @node: thm:studentized-coverage
theorem studentized_wald_coverage (Arr : BlockArray) (M V α zAlpha : ℝ)
    : (∀ (_hLindebergFellerIndependentArray_of_gate : LindebergFellerIndependentArray),
        BlockIndependence Arr →
        UniformScoreBound Arr M →
        NondegenerateAverageVariance Arr V →
        ∀ t : ℝ, Tendsto (fun B => numeratorCDF Arr B t) atTop (𝓝 (stdNormalCdf t))) ∧
      (BlockIndependence Arr →
        BoundTableVarianceNegligible Arr →
        FiniteDesign.TendstoInProb (rowDesign Arr)
          (fun B w => WHat Arr B w - WBar Arr B) (fun _ => 0)) ∧
      (BlockConservativeness Arr →
        ∀ B, VBar Arr B ≤ WBar Arr B) ∧
      (∀ (_hLindebergFellerIndependentArray_of_gate : LindebergFellerIndependentArray),
        BlockIndependence Arr →
        UniformScoreBound Arr M →
        NondegenerateAverageVariance Arr V →
        BoundTableVarianceNegligible Arr →
        BlockConservativeness Arr →
        (hAlpha : 0 < α ∧ α < 1) → -- @realizes \alpha(significance level in (0,1))
        (hzAlpha : 0 ≤ zAlpha ∧ stdNormalCdf zAlpha = 1 - α / 2) →
        1 - α ≤ Filter.liminf
          (fun B => coverageProbability Arr B α zAlpha hAlpha hzAlpha) atTop) ∧
      (∀ W : ℝ,
        0 ≤ W → -- @realizes W(optional finite bound limit)
        ∀ (_hLindebergFellerIndependentArray_of_gate : LindebergFellerIndependentArray),
        BlockIndependence Arr →
        UniformScoreBound Arr M →
        NondegenerateAverageVariance Arr V →
        BoundTableVarianceNegligible Arr →
        BlockConservativeness Arr →
        (hAlpha : 0 < α ∧ α < 1) →
        (hzAlpha : 0 ≤ zAlpha ∧ stdNormalCdf zAlpha = 1 - α / 2) →
        Tendsto (WBar Arr) atTop (𝓝 W) →
        Tendsto (fun B => coverageProbability Arr B α zAlpha hAlpha hzAlpha) atTop
          (𝓝 (2 * stdNormalCdf (zAlpha * Real.sqrt (W / V)) - 1))) ∧
      (∀ (_hLindebergFellerIndependentArray_of_gate : LindebergFellerIndependentArray),
        BlockIndependence Arr →
        UniformScoreBound Arr M →
        NondegenerateAverageVariance Arr V →
        BoundTableVarianceNegligible Arr →
        Tendsto (fun B => WBar Arr B - VBar Arr B) atTop (𝓝 0) →
        ∀ t : ℝ, Tendsto (fun B => feasibleStudentizedCDF Arr B t) atTop
          (𝓝 (stdNormalCdf t))) := by
  refine ⟨?_, ?_⟩
  · intro hLindebergFellerIndependentArray_of_gate hInd hBound hV
    have hEnvelopeZero : Tendsto (blockCLTEnvelope Arr M) atTop (𝓝 0) := by
      exact blockCLTEnvelope_tendsto_zero Arr M V hV
    have hEnvelopeRate :
        Tendsto (fun B : ℕ => (B : ℝ) * (blockCLTEnvelope Arr M B) ^ 3) atTop (𝓝 0) := by
      exact blockCLTEnvelope_cubic_rate Arr M V hV
    exact numeratorCDF_tendsto_from_productCLT Arr M V
      hLindebergFellerIndependentArray_of_gate hInd hBound hV
      hEnvelopeZero hEnvelopeRate
  refine ⟨?_, ?_⟩
  · intro hInd hLLN
    exact WHat_sub_WBar_tendstoInProb Arr hInd hLLN
  refine ⟨?_, ?_⟩
  · intro hCons
    exact VBar_le_WBar Arr hCons
  refine ⟨?_, ?_⟩
  · intro hLindebergFellerIndependentArray_of_gate hInd hBound hV hLLN hCons hα hz
    classical
    have hclt : ∀ t : ℝ, Tendsto (fun B => numeratorCDF Arr B t) atTop
        (𝓝 (stdNormalCdf t)) := by
      intro t
      exact numeratorCDF_tendsto_from_productCLT Arr M V
        hLindebergFellerIndependentArray_of_gate hInd hBound hV
        (blockCLTEnvelope_tendsto_zero Arr M V hV)
        (blockCLTEnvelope_cubic_rate Arr M V hV) t
    have hden := WHat_sub_WBar_tendstoInProb Arr hInd hLLN
    have hVpos : ∀ᶠ B in atTop, 0 < VBar Arr B :=
      hV.2.eventually (eventually_gt_nhds hV.1)
    have hbad : ∀ ε : ℝ, 0 < ε → Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => WHat Arr B w < (1 - ε) * VBar Arr B))
        atTop (𝓝 0) := by
      intro ε hε
      have hδ : 0 < ε * (V / 2) := mul_pos hε (by linarith [hV.1])
      have htail := hden (ε * (V / 2)) hδ
      have hupper : ∀ᶠ B in atTop,
          (rowDesign Arr B).Pr (fun w => WHat Arr B w < (1 - ε) * VBar Arr B) ≤
            (rowDesign Arr B).Pr (fun w =>
              ε * (V / 2) ≤ |(WHat Arr B w - WBar Arr B) - 0|) := by
        filter_upwards [hV.2.eventually
          (eventually_gt_nhds (by linarith [hV.1] : V / 2 < V))] with B hVB
        apply (rowDesign Arr B).Pr_mono
        intro w hw
        have hWV := VBar_le_WBar Arr hCons B
        have hgap : ε * VBar Arr B < WBar Arr B - WHat Arr B w := by
          nlinarith
        rw [sub_zero, abs_sub_comm]
        exact (mul_le_mul_of_nonneg_left hVB.le hε.le).trans
          ((le_of_lt hgap).trans (le_abs_self _))
      exact squeeze_zero' (Filter.Eventually.of_forall
        (fun B => (rowDesign Arr B).Pr_nonneg _)) hupper htail
    let I : ℕ → ℝ := fun B => coverageProbability Arr B α zAlpha hα hz
    have hIcobdd : IsCoboundedUnder (· ≥ ·) atTop I :=
      isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
        (fun B => (rowDesign Arr B).Pr_le_one _)
    have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
        2 * stdNormalCdf (zAlpha * Real.sqrt (1 - ε)) - 1 ≤
          Filter.liminf I atTop := by
      intro ε hε0 hε1
      let c : ℝ := zAlpha * Real.sqrt (1 - ε)
      have h1ε : 0 < 1 - ε := by linarith
      have hc : 0 ≤ c := mul_nonneg hz.1 (Real.sqrt_nonneg _)
      let Band : ℕ → ℝ := fun B => (rowDesign Arr B).Pr (fun w =>
        -c ≤ Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
            Real.sqrt (VBar Arr B) ∧
        Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
            Real.sqrt (VBar Arr B) ≤ c)
      let Bad : ℕ → ℝ := fun B => (rowDesign Arr B).Pr
        (fun w => WHat Arr B w < (1 - ε) * VBar Arr B)
      have hBad0 : Tendsto Bad atTop (𝓝 0) := hbad ε hε0
      have hstep : ∀ᶠ B in atTop, Band B - Bad B ≤ I B := by
        filter_upwards [eventually_gt_atTop (0 : ℕ), hVpos] with B hB hVB
        let T : (∀ j : Fin B, Arr.Omega B j) → ℝ := fun w =>
          Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B)
        let Bev : (∀ j : Fin B, Arr.Omega B j) → Prop := fun w => -c ≤ T w ∧ T w ≤ c
        let Aev : (∀ j : Fin B, Arr.Omega B j) → Prop := fun w =>
          WHat Arr B w < (1 - ε) * VBar Arr B
        have hsplit := (rowDesign Arr B).Pr_split Bev Aev
        have hBA : (rowDesign Arr B).Pr (fun w => Bev w ∧ Aev w) ≤ Bad B := by
          apply (rowDesign Arr B).Pr_mono
          exact fun _ h => h.2
        have hdiff : Band B - Bad B ≤
            (rowDesign Arr B).Pr (fun w => Bev w ∧ ¬ Aev w) := by
          have heq : Band B = (rowDesign Arr B).Pr (fun w => Bev w ∧ Aev w) +
              (rowDesign Arr B).Pr (fun w => Bev w ∧ ¬ Aev w) := by
            simpa [Band, Bad, Bev, Aev, T, c] using hsplit
          linarith
        refine hdiff.trans ?_
        apply (rowDesign Arr B).Pr_mono
        intro w hw
        change tauBar Arr B ∈ waldInterval Arr B α zAlpha hα hz w
        rw [mem_waldInterval_iff_abs_error Arr B α zAlpha hα hz hB w]
        have habsT : |T w| ≤ c := abs_le.mpr hw.1
        have hgood : (1 - ε) * VBar Arr B ≤ max (WHat Arr B w) 0 := by
          exact (le_of_not_gt hw.2).trans (le_max_left _ _)
        have hsqrtB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by positivity)
        have hsqrtV : 0 < Real.sqrt (VBar Arr B) := Real.sqrt_pos.2 hVB
        have hdiffT : tauHat Arr B w - tauBar Arr B =
            T w * Real.sqrt (VBar Arr B) / Real.sqrt B := by
          dsimp [T]
          field_simp
        rw [hdiffT, abs_div, abs_mul, abs_of_pos hsqrtB, abs_of_pos hsqrtV]
        calc
          |T w| * Real.sqrt (VBar Arr B) / Real.sqrt B ≤
              c * Real.sqrt (VBar Arr B) / Real.sqrt B := by
                gcongr
          _ = zAlpha * Real.sqrt (((1 - ε) * VBar Arr B) / B) := by
                dsimp [c]
                rw [mul_assoc, ← Real.sqrt_mul h1ε.le,
                  Real.sqrt_div (mul_nonneg h1ε.le hVB.le)]
                ring
          _ ≤ zAlpha * Real.sqrt (max (WHat Arr B w) 0 / B) := by
                apply mul_le_mul_of_nonneg_left _ hz.1
                apply Real.sqrt_le_sqrt
                exact div_le_div_of_nonneg_right hgood (Nat.cast_nonneg B)
      have hBandLower : stdNormalCdf c - stdNormalCdf (-c) ≤
          Filter.liminf Band atTop := by
        simpa [Band, c] using numerator_symmetric_band_liminf Arr hclt c hc
      have hBandBad : Filter.liminf Band atTop ≤
          Filter.liminf (fun B => Band B - Bad B) atTop := by
        have hneg : Tendsto (fun B => -Bad B) atTop (𝓝 0) := by simpa using hBad0.neg
        have hBge : IsBoundedUnder (· ≥ ·) atTop Band :=
          isBoundedUnder_of ⟨0, fun B => (rowDesign Arr B).Pr_nonneg _⟩
        have hBle : IsBoundedUnder (· ≤ ·) atTop Band :=
          isBoundedUnder_of ⟨1, fun B => (rowDesign Arr B).Pr_le_one _⟩
        have h := le_liminf_add (u := Band) (v := fun B => -Bad B)
          hBge hBle hneg.isBoundedUnder_ge hneg.isBoundedUnder_le.isCoboundedUnder_ge
        rw [hneg.liminf_eq, add_zero] at h
        have hadd : Band + (fun B => -Bad B) = fun B => Band B - Bad B := by
          funext B
          simp [sub_eq_add_neg]
        rwa [hadd] at h
      have htoI : Filter.liminf (fun B => Band B - Bad B) atTop ≤
          Filter.liminf I atTop := by
        have hlower : IsBoundedUnder (· ≥ ·) atTop (fun B => Band B - Bad B) :=
          isBoundedUnder_of ⟨-1, fun B => by
            have hbn := (rowDesign Arr B).Pr_nonneg (fun w =>
              -c ≤ Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
                  Real.sqrt (VBar Arr B) ∧
              Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
                  Real.sqrt (VBar Arr B) ≤ c)
            have han := (rowDesign Arr B).Pr_le_one
              (fun w => WHat Arr B w < (1 - ε) * VBar Arr B)
            change (-1 : ℝ) ≤ Band B - Bad B
            dsimp [Band, Bad]
            linarith⟩
        exact Filter.liminf_le_liminf hstep hlower hIcobdd
      have hsymm : stdNormalCdf c - stdNormalCdf (-c) =
          2 * stdNormalCdf c - 1 := by rw [stdNormalCdf_neg]; ring
      calc
        2 * stdNormalCdf (zAlpha * Real.sqrt (1 - ε)) - 1 =
            stdNormalCdf c - stdNormalCdf (-c) := by
              simpa [c] using hsymm.symm
        _ ≤ Filter.liminf Band atTop := hBandLower
        _ ≤ Filter.liminf (fun B => Band B - Bad B) atTop := hBandBad
        _ ≤ Filter.liminf I atTop := htoI
    let g : ℝ → ℝ := fun ε => 2 * stdNormalCdf (zAlpha * Real.sqrt (1 - ε)) - 1
    have hg : Tendsto g (𝓝 0) (𝓝 (1 - α)) := by
      have hsqrt : Tendsto (fun ε : ℝ => Real.sqrt (1 - ε)) (𝓝 0) (𝓝 1) := by
        have hsub : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at hsub
        change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ (fun ε : ℝ => 1 - ε))
          (𝓝 0) (𝓝 1)
        simpa using (Real.continuous_sqrt.tendsto 1).comp hsub
      have harg : Tendsto (fun ε : ℝ => zAlpha * Real.sqrt (1 - ε))
          (𝓝 0) (𝓝 zAlpha) := by simpa using tendsto_const_nhds.mul hsqrt
      have hcdf := (continuous_stdNormalCdf.tendsto zAlpha).comp harg
      have hout : Tendsto g (𝓝 0) (𝓝 (2 * stdNormalCdf zAlpha - 1)) := by
        exact (tendsto_const_nhds.mul hcdf).sub tendsto_const_nhds
      convert hout using 1
      rw [hz.2]
      ring
    have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hgseq : Tendsto (fun k : ℕ => g (1 / (k + 1))) atTop (𝓝 (1 - α)) :=
      hg.comp hseq
    apply le_of_tendsto hgseq
    rw [Filter.eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hdenom : (0 : ℝ) < k + 1 := by positivity
    apply key
    · positivity
    · rw [div_lt_one hdenom]
      linarith
  refine ⟨?_, ?_⟩
  · intro W hW hLindebergFellerIndependentArray_of_gate hInd hBound hV hLLN hCons hα hz hWLimit
    classical
    have hclt : ∀ x : ℝ, Tendsto (fun B => numeratorCDF Arr B x) atTop
        (𝓝 (stdNormalCdf x)) := by
      intro x
      exact numeratorCDF_tendsto_from_productCLT Arr M V
        hLindebergFellerIndependentArray_of_gate hInd hBound hV
        (blockCLTEnvelope_tendsto_zero Arr M V hV)
        (blockCLTEnvelope_cubic_rate Arr M V hV) x
    have hVW : ∀ B, VBar Arr B ≤ WBar Arr B := VBar_le_WBar Arr hCons
    have hWpos : 0 < W := by
      have hle : V ≤ W := le_of_tendsto_of_tendsto hV.2 hWLimit
        (Filter.Eventually.of_forall hVW)
      exact hV.1.trans_le hle
    have hden := WHat_sub_WBar_tendstoInProb Arr hInd hLLN
    have hWdet : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B _ => WBar Arr B) (fun _ => W) :=
      deterministic_tendstoInProb (rowDesign Arr) (WBar Arr) W hWLimit
    have hWhat : FiniteDesign.TendstoInProb (rowDesign Arr)
        (WHat Arr) (fun _ => W) := by
      have h := hden.add hWdet
      unfold FiniteDesign.TendstoInProb at h ⊢
      simpa only [sub_zero, zero_add, sub_add_cancel] using h
    let invRoot : ℝ → ℝ := fun x => 1 / Real.sqrt (max x 0)
    have hinv : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => invRoot (WHat Arr B w)) (fun _ => 1 / Real.sqrt W) := by
      have hm := tendstoInProb_continuousMap (rowDesign Arr) (WHat Arr) W invRoot hWhat
        (by
          have hmax : ContinuousAt (fun x : ℝ => max x 0) W :=
            continuousAt_id.max continuousAt_const
          have hsqrt := Real.continuous_sqrt.continuousAt.comp hmax
          exact continuousAt_const.div hsqrt (by
            simpa [max_eq_left hWpos.le] using (Real.sqrt_pos.2 hWpos).ne'))
      simpa [invRoot, max_eq_left hWpos.le] using hm
    have hsqrtVlim : Tendsto (fun B => Real.sqrt (VBar Arr B)) atTop
        (𝓝 (Real.sqrt V)) := Real.continuous_sqrt.continuousAt.tendsto.comp hV.2
    have hsqrtVdet : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B _ => Real.sqrt (VBar Arr B)) (fun _ => Real.sqrt V) :=
      deterministic_tendstoInProb (rowDesign Arr) _ _ hsqrtVlim
    have hsqrtVbdd : FiniteDesign.BoundedInProb (rowDesign Arr)
        (fun B _ => Real.sqrt (VBar Arr B)) := by
      intro η hη
      refine ⟨Real.sqrt V + 1, ?_⟩
      have hev : ∀ᶠ B in atTop, |Real.sqrt (VBar Arr B) - Real.sqrt V| < 1 := by
        simpa [Real.dist_eq] using
          (Metric.tendsto_nhds.1 hsqrtVlim) 1 (by norm_num)
      filter_upwards [hev] with B hB
      have hlt : |Real.sqrt (VBar Arr B)| < Real.sqrt V + 1 := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        linarith [(abs_lt.1 hB).2]
      have hz : (rowDesign Arr B).Pr
          (fun _ => Real.sqrt V + 1 ≤ |Real.sqrt (VBar Arr B)|) = 0 := by
        unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
        simp [not_le.mpr hlt]
      rw [hz]
      exact hη.le
    have hinvDiff : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => invRoot (WHat Arr B w) - 1 / Real.sqrt W) (fun _ => 0) := by
      unfold FiniteDesign.TendstoInProb at hinv ⊢
      simpa only [sub_zero] using hinv
    have hsqrtVDiff : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B _ => Real.sqrt (VBar Arr B) - Real.sqrt V) (fun _ => 0) := by
      unfold FiniteDesign.TendstoInProb at hsqrtVdet ⊢
      simpa only [sub_zero] using hsqrtVdet
    let scale : ℝ := Real.sqrt V / Real.sqrt W
    let A : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ := fun B w =>
      Real.sqrt (VBar Arr B) * invRoot (WHat Arr B w)
    have hA : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => A B w - scale) (fun _ => 0) := by
      have hfirst := hinvDiff.mul_boundedInProb hsqrtVbdd
      have hsecond := hsqrtVDiff.const_mul (1 / Real.sqrt W)
      have hadd := hfirst.add hsecond
      intro ε hε
      refine (hadd ε hε).congr' (Filter.Eventually.of_forall fun B => ?_)
      apply (rowDesign Arr B).Pr_congr
      intro w
      congr 2
      dsimp [A, scale]
      ring
    let T : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ := fun B w =>
      Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B)
    let U : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ := fun B w =>
      Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
        Real.sqrt (max (WHat Arr B w) 0)
    have hTbdd : FiniteDesign.BoundedInProb (rowDesign Arr) T := by
      apply boundedInProb_of_stdNormalCDF (rowDesign Arr) T
      intro x
      simpa [T, numeratorCDF] using hclt x
    have hprod := hA.mul_boundedInProb hTbdd
    have hApprox : ∀ η : ℝ, 0 < η → Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => η ≤ |U B w - scale * T B w|))
        atTop (𝓝 0) := by
      intro η hη
      refine (hprod η hη).congr' ?_
      filter_upwards [hV.2.eventually (eventually_gt_nhds hV.1)] with B hVB
      apply (rowDesign Arr B).Pr_congr
      intro w
      congr 2
      have hsV : Real.sqrt (VBar Arr B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hVB)
      dsimp [U, T, A, invRoot]
      by_cases hm : Real.sqrt (max (WHat Arr B w) 0) = 0
      · simp [hm]
      · field_simp
        ring
    have hscale : 0 < scale := by
      dsimp [scale]
      exact div_pos (Real.sqrt_pos.2 hV.1) (Real.sqrt_pos.2 hWpos)
    have hinvScale : 1 / scale = Real.sqrt (W / V) := by
      dsimp [scale]
      rw [Real.sqrt_div hWpos.le]
      field_simp
    have hinvScale' : scale⁻¹ = Real.sqrt (W / V) := by
      simpa [one_div] using hinvScale
    let F : ℝ → ℝ := fun x => stdNormalCdf (x * Real.sqrt (W / V))
    have hscaledCDF : ∀ x : ℝ, Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => scale * T B w ≤ x)) atTop (𝓝 (F x)) := by
      intro x
      have heq : ∀ B, (rowDesign Arr B).Pr (fun w => scale * T B w ≤ x) =
          numeratorCDF Arr B (x / scale) := by
        intro B
        apply (rowDesign Arr B).Pr_congr
        intro w
        have hi := (le_div_iff₀ hscale : T B w ≤ x / scale ↔ T B w * scale ≤ x)
        simpa [mul_comm] using hi.symm
      simp_rw [heq]
      simpa [F, div_eq_mul_inv, hinvScale'] using hclt (x / scale)
    have hF : Continuous F := continuous_stdNormalCdf.comp
      (continuous_id.mul continuous_const)
    have hUcdf : ∀ x : ℝ, Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => U B w ≤ x)) atTop (𝓝 (F x)) :=
      finiteDesign_cdf_converging_together (rowDesign Arr) U
        (fun B w => scale * T B w) F hApprox hscaledCDF hF
    have hBand := finiteDesign_symmetricBand_tendsto (rowDesign Arr) U F hUcdf hF
      zAlpha hz.1
    have hBad : Tendsto (fun B => (rowDesign Arr B).Pr
        (fun w => max (WHat Arr B w) 0 = 0)) atTop (𝓝 0) := by
      have ht := hWhat (W / 2) (by positivity)
      refine squeeze_zero' (Filter.Eventually.of_forall fun B =>
        (rowDesign Arr B).Pr_nonneg _) ?_ ht
      apply Filter.Eventually.of_forall
      intro B
      apply (rowDesign Arr B).Pr_mono
      intro w hw
      have hwh : WHat Arr B w ≤ 0 := by
        exact max_eq_right_iff.mp hw
      simpa only using (show W / 2 ≤ |WHat Arr B w - W| by
        rw [abs_of_nonpos (by linarith)]
        linarith)
    let Band : ℕ → ℝ := fun B => (rowDesign Arr B).Pr
      (fun w => -zAlpha ≤ U B w ∧ U B w ≤ zAlpha)
    let Bad : ℕ → ℝ := fun B => (rowDesign Arr B).Pr
      (fun w => max (WHat Arr B w) 0 = 0)
    let Cov : ℕ → ℝ := fun B => coverageProbability Arr B α zAlpha hα hz
    have hsandwich : ∀ᶠ B in atTop, Band B - Bad B ≤ Cov B ∧ Cov B ≤ Band B + Bad B := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
      have hequiv : ∀ w, max (WHat Arr B w) 0 ≠ 0 →
          (tauBar Arr B ∈ waldInterval Arr B α zAlpha hα hz w ↔
            -zAlpha ≤ U B w ∧ U B w ≤ zAlpha) := by
        intro w hm
        rw [mem_waldInterval_iff_abs_error Arr B α zAlpha hα hz hB w]
        have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by positivity)
        have hsM : 0 < Real.sqrt (max (WHat Arr B w) 0) :=
          Real.sqrt_pos.2 (lt_of_le_of_ne (le_max_right _ _) (Ne.symm hm))
        rw [← abs_le, abs_div, abs_mul, abs_of_pos hsB, abs_of_pos hsM,
          Real.sqrt_div (le_max_right _ _)]
        field_simp
      have hcb : Cov B ≤ Band B + Bad B := by
        calc
          Cov B ≤ (rowDesign Arr B).Pr (fun w =>
              (-zAlpha ≤ U B w ∧ U B w ≤ zAlpha) ∨
                max (WHat Arr B w) 0 = 0) := by
            apply (rowDesign Arr B).Pr_mono
            intro w hw
            by_cases hm : max (WHat Arr B w) 0 = 0
            · exact Or.inr hm
            · exact Or.inl ((hequiv w hm).1 hw)
          _ ≤ Band B + Bad B := FiniteDesign.Pr_or_le _ _ _
      have hbc : Band B ≤ Cov B + Bad B := by
        calc
          Band B ≤ (rowDesign Arr B).Pr (fun w =>
              tauBar Arr B ∈ waldInterval Arr B α zAlpha hα hz w ∨
                max (WHat Arr B w) 0 = 0) := by
            apply (rowDesign Arr B).Pr_mono
            intro w hw
            by_cases hm : max (WHat Arr B w) 0 = 0
            · exact Or.inr hm
            · exact Or.inl ((hequiv w hm).2 hw)
          _ ≤ Cov B + Bad B := FiniteDesign.Pr_or_le _ _ _
      exact ⟨by linarith, hcb⟩
    have hBand' : Tendsto Band atTop (𝓝 (F zAlpha - F (-zAlpha))) := by
      simpa [Band] using hBand
    have hBad' : Tendsto Bad atTop (𝓝 0) := by simpa [Bad] using hBad
    have hCov : Tendsto Cov atTop (𝓝 (F zAlpha - F (-zAlpha))) := by
      have hlo : Tendsto (fun B => Band B - Bad B) atTop
          (𝓝 (F zAlpha - F (-zAlpha))) := by
        simpa using hBand'.sub hBad'
      have hhi : Tendsto (fun B => Band B + Bad B) atTop
          (𝓝 (F zAlpha - F (-zAlpha))) := by
        simpa using hBand'.add hBad'
      apply hlo.squeeze' hhi
      · exact hsandwich.mono fun _ h => h.1
      · exact hsandwich.mono fun _ h => h.2
    convert hCov using 1
    dsimp [Cov, F]
    rw [show -zAlpha * Real.sqrt (W / V) =
      -(zAlpha * Real.sqrt (W / V)) by ring]
    rw [stdNormalCdf_neg]
    ring
  · intro hLindebergFellerIndependentArray_of_gate hInd hBound hV hLLN hWMinusV t
    classical
    have hclt : ∀ x : ℝ, Tendsto (fun B => numeratorCDF Arr B x) atTop
        (𝓝 (stdNormalCdf x)) := by
      intro x
      exact numeratorCDF_tendsto_from_productCLT Arr M V
        hLindebergFellerIndependentArray_of_gate hInd hBound hV
        (blockCLTEnvelope_tendsto_zero Arr M V hV)
        (blockCLTEnvelope_cubic_rate Arr M V hV) x
    have hden := WHat_sub_WBar_tendstoInProb Arr hInd hLLN
    have hdet : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B _ => WBar Arr B - VBar Arr B) (fun _ => 0) :=
      deterministic_tendstoInProb (rowDesign Arr)
        (fun B => WBar Arr B - VBar Arr B) 0 hWMinusV
    have hdelta : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => WHat Arr B w - VBar Arr B) (fun _ => 0) := by
      have hadd := hden.add hdet
      unfold FiniteDesign.TendstoInProb at hadd ⊢
      simpa only [sub_zero, sub_add_sub_cancel, add_zero] using hadd
    let R : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ :=
      fun B w => max (WHat Arr B w) 0 / VBar Arr B
    have hR : FiniteDesign.TendstoInProb (rowDesign Arr) R (fun _ => 1) := by
      intro ε hε
      have hthreshold : 0 < ε * (V / 2) := mul_pos hε (by linarith [hV.1])
      have htail := hdelta (ε * (V / 2)) hthreshold
      refine squeeze_zero'
        (Filter.Eventually.of_forall (fun B => (rowDesign Arr B).Pr_nonneg _)) ?_ htail
      filter_upwards [hV.2.eventually
        (eventually_gt_nhds (by linarith [hV.1] : V / 2 < V))] with B hVB
      apply (rowDesign Arr B).Pr_mono
      intro w hw
      have hVBpos : 0 < VBar Arr B := lt_of_lt_of_le (by linarith [hV.1]) hVB.le
      have hcontract : |max (WHat Arr B w) 0 - VBar Arr B| ≤
          |WHat Arr B w - VBar Arr B| := by
        by_cases hx : 0 ≤ WHat Arr B w
        · simp [max_eq_left hx]
        · rw [max_eq_right (le_of_not_ge hx), zero_sub, abs_neg,
            abs_of_pos hVBpos]
          have : WHat Arr B w - VBar Arr B < 0 := by linarith
          rw [abs_of_neg this]
          linarith
      have hratio : |R B w - 1| =
          |max (WHat Arr B w) 0 - VBar Arr B| / VBar Arr B := by
        dsimp [R]
        rw [div_sub_one hVBpos.ne', abs_div, abs_of_pos hVBpos]
      rw [hratio] at hw
      rw [le_div_iff₀ hVBpos] at hw
      simpa only [sub_zero] using
        ((mul_le_mul_of_nonneg_left hVB.le hε.le).trans (hw.trans hcontract))
    have hInv : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => 1 / Real.sqrt (R B w) - 1) (fun _ => 0) := by
      have hmapped := tendstoInProb_continuousMap (rowDesign Arr) R 1
        (fun x => 1 / Real.sqrt x) hR (by
          exact continuousAt_const.div Real.continuous_sqrt.continuousAt (by norm_num))
      unfold FiniteDesign.TendstoInProb at hmapped ⊢
      simpa only [one_div, Real.sqrt_one, inv_one, sub_zero] using hmapped
    let T : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ := fun B w =>
      Real.sqrt B * (tauHat Arr B w - tauBar Arr B) / Real.sqrt (VBar Arr B)
    let U : ∀ B, (∀ j : Fin B, Arr.Omega B j) → ℝ := fun B w =>
      Real.sqrt B * (tauHat Arr B w - tauBar Arr B) /
        Real.sqrt (max (WHat Arr B w) 0)
    have hTbdd : FiniteDesign.BoundedInProb (rowDesign Arr) T := by
      apply boundedInProb_of_stdNormalCDF (rowDesign Arr) T
      intro x
      simpa [T, numeratorCDF] using hclt x
    have hprod : FiniteDesign.TendstoInProb (rowDesign Arr)
        (fun B w => (1 / Real.sqrt (R B w) - 1) * T B w) (fun _ => 0) :=
      hInv.mul_boundedInProb hTbdd
    have hApprox : ∀ η : ℝ, 0 < η → Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => η ≤ |U B w - T B w|)) atTop (𝓝 0) := by
      intro η hη
      refine (hprod η hη).congr' ?_
      filter_upwards [hV.2.eventually
        (eventually_gt_nhds hV.1)] with B hVB
      apply (rowDesign Arr B).Pr_congr
      intro w
      congr 2
      dsimp [U, T, R]
      rw [Real.sqrt_div (le_max_right _ _)]
      have hsV : Real.sqrt (VBar Arr B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hVB)
      by_cases hmax : max (WHat Arr B w) 0 = 0
      · simp [hmax]
      · have hsmax : Real.sqrt (max (WHat Arr B w) 0) ≠ 0 := by
          exact (Real.sqrt_ne_zero').2
            (lt_of_le_of_ne (le_max_right _ _) (Ne.symm hmax))
        field_simp
        ring
    have hTcdf : ∀ x : ℝ, Tendsto (fun B =>
        (rowDesign Arr B).Pr (fun w => T B w ≤ x)) atTop
        (𝓝 (stdNormalCdf x)) := by
      intro x
      simpa [T, numeratorCDF] using hclt x
    have hUcdf := finiteDesign_cdf_converging_together
      (rowDesign Arr) U T stdNormalCdf hApprox hTcdf continuous_stdNormalCdf t
    simpa [U, feasibleStudentizedCDF] using hUcdf

end CausalSmith.Experimentation.BinaryTruthbound
