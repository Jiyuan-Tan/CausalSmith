module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentJointLaw
public import Causalean.Stat.Minimax.MarkovKernelTransport
/-! Finite atomic product kernels identify the integrated conditional dataset laws with
the sign mixture and null product experiment, certifying the coupling marginals. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Independent finite atomic laws expand into the array of products of their weights.  [the theorem's stated inputs and assumptions](hyp:w,f,hw), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α,β). -/
-- @node: pi_finite_atomic
lemma pi_finite_atomic {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [MeasurableSpace β] (w : ι → α → ℝ≥0∞) (f : ι → α → β)
    (hw : ∀ i a, w i a ≠ ⊤) :
    Measure.pi (fun i => ∑ a, w i a • Measure.dirac (f i a)) =
      ∑ z : ι → α, (∏ i, w i (z i)) • Measure.dirac (fun i => f i (z i)) := by
  classical
  let (i : ι) : IsFiniteMeasure (∑ a, w i a • Measure.dirac (f i a)) := by
    constructor
    simpa [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using
      (ENNReal.sum_lt_top.mpr (fun a (_ : a ∈ (Finset.univ : Finset α)) => (hw i a).lt_top))
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : ∀ i, f i (z i) ∈ s i
  · simp [Set.mem_pi, hz]
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    have hprod : (∏ j, w j (z j) * (s j).indicator (1 : β → ℝ≥0∞) (f j (z j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simpa [Set.mem_pi, hz] using hprod.symm

/-- The conditional observed law for a fixed sign vector at one covariate. -/
-- @node: conditionalSignRecordLaw
def conditionalSignRecordLaw (hL : ℝ) (lam : SignVector hL) (x : Covariate) : Measure O :=
  ∑ z : Bool × Bool, ENNReal.ofReal (conditionalLikelihood hL lam x z.1 z.2 / 4) •
    Measure.dirac (x, z.1, z.2)

/-- The fixed-sign conditional record law varies measurably with the covariate. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_conditionalSignRecordLaw
@[fun_prop] lemma measurable_conditionalSignRecordLaw (hL : ℝ) (lam : SignVector hL) :
    Measurable (conditionalSignRecordLaw hL lam) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [conditionalSignRecordLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.mul
  · fun_prop
  · exact (measurable_const.indicator hE).comp (by fun_prop)

/-- Each fixed-sign conditional record law is a probability measure.  [the theorem's stated inputs and assumptions](hyp:hhL,lam,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalSignRecordLaw_isProbabilityMeasure
lemma conditionalSignRecordLaw_isProbabilityMeasure (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (lam : SignVector hL) (x : Covariate) :
    IsProbabilityMeasure (conditionalSignRecordLaw hL lam x) := by
  constructor
  simp only [conditionalSignRecordLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    div_nonneg (conditionalLikelihood_nonneg hL hhL lam x z.1 z.2) (by norm_num)),
    conditionalLikelihood_mark_sum, ENNReal.ofReal_one]

/-- The fixed-sign observation kernel attaches the covariate to its conditional marks. -/
-- @node: signRecordKernel
def signRecordKernel (hL : ℝ) (lam : SignVector hL) : Kernel Covariate O where
  toFun := conditionalSignRecordLaw hL lam
  measurable' := measurable_conditionalSignRecordLaw hL lam

/-- The fixed-sign observation kernel is everywhere probability-valued.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signRecordKernel_isMarkovKernel
lemma signRecordKernel_isMarkovKernel (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) : IsMarkovKernel (signRecordKernel hL lam) :=
  ⟨conditionalSignRecordLaw_isProbabilityMeasure hL hhL lam⟩

/-- Integrating a fixed-sign conditional record reproduces the observed causal law. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: signRecordKernel_comp_volume
lemma signRecordKernel_comp_volume (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) :
    signRecordKernel hL lam ∘ₘ (volume : Measure Covariate) =
      Pobs (cosineFamily hL hhL lam) := by
  ext E hE
  change ((volume : Measure Covariate).bind (conditionalSignRecordLaw hL lam)) E = _
  rw [Measure.bind_apply hE (measurable_conditionalSignRecordLaw hL lam).aemeasurable]
  rw [cosineFamily, binaryCausalLaw_observed_apply _ _ _ (measurable_altE hL lam)
    (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hhL lam) E hE]
  apply lintegral_congr
  intro x
  simp only [conditionalSignRecordLaw, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ hE, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  congr 2
  dsimp [conditionalLikelihood]
  ring

/-- Given fixed signs, the conditional dataset law has independent mark weights. -/
-- @node: conditionalSignDatasetLaw
def conditionalSignDatasetLaw (hL : ℝ) (n : ℕ) (lam : SignVector hL)
    (x : Fin n → Covariate) : Measure (Dataset n) :=
  ∑ z : Fin n → Bool × Bool,
    ENNReal.ofReal (∏ i, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4) •
      Measure.dirac (attachMarks n x z)

/-- The conditional fixed-sign dataset array equals the coordinatewise product kernel.  [the theorem's stated inputs and assumptions](hyp:n,lam,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalSignDatasetLaw_eq_product
lemma conditionalSignDatasetLaw_eq_product (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (lam : SignVector hL) (x : Fin n → Covariate) :
    conditionalSignDatasetLaw hL n lam x =
      Causalean.Stat.finProductKernel n (signRecordKernel hL lam) x := by
  let := signRecordKernel_isMarkovKernel hL hhL lam
  rw [Causalean.Stat.finProductKernel_apply]
  change _ = Measure.pi (fun i => conditionalSignRecordLaw hL lam (x i))
  dsimp only [conditionalSignRecordLaw, conditionalSignDatasetLaw]
  rw [pi_finite_atomic _ _ (fun _ _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro z _
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    div_nonneg (conditionalLikelihood_nonneg hL hhL lam (x i) (z i).1 (z i).2)
      (by norm_num))]
  rfl

/-- The fixed-sign conditional dataset array is Borel measurable. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_conditionalSignDatasetLaw
@[fun_prop] lemma measurable_conditionalSignDatasetLaw (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (lam : SignVector hL) :
    Measurable (conditionalSignDatasetLaw hL n lam) := by
  have heq : conditionalSignDatasetLaw hL n lam =
      Causalean.Stat.finProductKernel n (signRecordKernel hL lam) := by
    funext x
    exact conditionalSignDatasetLaw_eq_product hL hhL n lam x
  rw [heq]
  exact Kernel.measurable _

/-- Integrating a fixed-sign dataset kernel yields the observed product law.  [the theorem's stated inputs and assumptions](hyp:hhL,n,lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalSignDatasetLaw_bind_eq_dataLaw
lemma conditionalSignDatasetLaw_bind_eq_dataLaw (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (lam : SignVector hL) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
      (conditionalSignDatasetLaw hL n lam) = dataLaw n (cosineFamily hL hhL lam) := by
  let := signRecordKernel_isMarkovKernel hL hhL lam
  have heq : conditionalSignDatasetLaw hL n lam =
      Causalean.Stat.finProductKernel n (signRecordKernel hL lam) := by
    funext x
    exact conditionalSignDatasetLaw_eq_product hL hhL n lam x
  rw [heq, Causalean.Stat.finProductKernel_comp_pi, signRecordKernel_comp_volume hL hhL]
  rfl

/-- The conditional alternative law is the uniform mixture of the fixed-sign dataset kernels.  [the theorem's stated inputs and assumptions](hyp:hhL,n,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalAlternativeDatasetLaw_eq_sign_sum
lemma conditionalAlternativeDatasetLaw_eq_sign_sum (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (x : Fin n → Covariate) :
    conditionalAlternativeDatasetLaw hL n x =
      ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) •
        ∑ lam : SignVector hL, conditionalSignDatasetLaw hL n lam x := by
  classical
  have hp (z : Fin n → Bool × Bool) (lam : SignVector hL) :
      0 ≤ ∏ i, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4 := by
    apply Finset.prod_nonneg
    intro i _
    exact div_nonneg (conditionalLikelihood_nonneg hL hhL lam (x i) _ _) (by norm_num)
  simp only [conditionalAlternativeDatasetLaw, fullAlternativeMass,
    ENNReal.ofReal_mul (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)),
    ENNReal.ofReal_sum_of_nonneg (fun lam _ => hp _ lam),
    mul_smul, Finset.sum_smul, ← Finset.smul_sum, conditionalSignDatasetLaw]
  rw [Finset.sum_comm]

/-- Integrating the alternative conditional law gives the specified mixture of product laws.  [the theorem's stated inputs and assumptions](hyp:hhL,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalAlternativeDatasetLaw_bind_eq_signMixture
lemma conditionalAlternativeDatasetLaw_bind_eq_signMixture (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
      (conditionalAlternativeDatasetLaw hL n) = signMixture hL hhL n := by
  classical
  ext E hE
  rw [Measure.bind_apply hE (measurable_conditionalAlternativeDatasetLaw hL n).aemeasurable]
  simp_rw [conditionalAlternativeDatasetLaw_eq_sign_sum hL hhL n]
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum (Finset.univ : Finset (SignVector hL)) (fun lam _ =>
      (show Measurable (fun x => (conditionalSignDatasetLaw hL n lam x) E) from
        (Measure.measurable_coe hE).comp (measurable_conditionalSignDatasetLaw hL hhL n lam)))]
  simp only [signMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro lam _
  rw [← conditionalSignDatasetLaw_bind_eq_dataLaw hL hhL n lam,
    Measure.bind_apply hE (measurable_conditionalSignDatasetLaw hL hhL n lam).aemeasurable]

/-- The constructed dataset coupling's first marginal is the actual sign-mixture experiment.  [the theorem's stated inputs and assumptions](hyp:hhL,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: commonMassCoupling_map_fst_signMixture
lemma commonMassCoupling_map_fst_signMixture (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    (commonMassCoupling hL n).map Prod.fst = signMixture hL hhL n := by
  rw [commonMassCoupling_map_fst_bind hL hhL,
    conditionalAlternativeDatasetLaw_bind_eq_signMixture hL hhL]

/-- The fair observation kernel attaches independent uniform binary marks to its covariate. -/
-- @node: fairRecordKernel
def fairRecordKernel : Kernel Covariate O where
  toFun x := ∑ z : Bool × Bool, ENNReal.ofReal (1/4 : ℝ) • Measure.dirac (x, z.1, z.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hE, smul_eq_mul]
    apply Finset.measurable_sum
    intro z _
    exact measurable_const.mul ((measurable_const.indicator hE).comp (by fun_prop))

/-- The fair observation kernel is a Markov kernel. -/
-- @node: fairRecordKernel_isMarkovKernel
instance fairRecordKernel_isMarkovKernel : IsMarkovKernel fairRecordKernel where
  isProbabilityMeasure x := by
    constructor
    change (∑ z : Bool × Bool, ENNReal.ofReal (1/4 : ℝ) • Measure.dirac (x, z.1, z.2)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by norm_num)]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The fair conditional observation integrates to the observed null law. [The displayed conclusion](goal) follows. -/
-- @node: fairRecordKernel_comp_volume
lemma fairRecordKernel_comp_volume :
    fairRecordKernel ∘ₘ (volume : Measure Covariate) = Pobs fairNull := by
  ext E hE
  rw [Measure.bind_apply hE (Kernel.measurable fairRecordKernel).aemeasurable,
    fairNull, binaryCausalLaw_observed_apply _ _ _ measurable_const measurable_const
      measurable_const fair_parameters_range E hE]
  apply lintegral_congr
  intro x
  change (∑ z : Bool × Bool, ENNReal.ofReal (1/4 : ℝ) • Measure.dirac (x, z.1, z.2)) E = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  cases z.1 <;> cases z.2 <;> norm_num [bernoulliMass, Set.indicator, Pi.one_apply]

/-- The fair conditional dataset array equals the coordinatewise fair observation kernel.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,x). -/
-- @node: conditionalNullDatasetLaw_eq_product
lemma conditionalNullDatasetLaw_eq_product (n : ℕ) (x : Fin n → Covariate) :
    conditionalNullDatasetLaw n x = Causalean.Stat.finProductKernel n fairRecordKernel x := by
  rw [Causalean.Stat.finProductKernel_apply]
  change _ = Measure.pi (fun i => ∑ z : Bool × Bool,
    ENNReal.ofReal (1/4 : ℝ) • Measure.dirac (x i, z.1, z.2))
  rw [pi_finite_atomic _ _ (fun _ _ => ENNReal.ofReal_ne_top)]
  dsimp only [conditionalNullDatasetLaw]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/4)]
  congr 1
  simp [zpow_neg, zpow_natCast, one_div]

/-- Integrating the fair conditional dataset law yields the null observed product law. [The displayed conclusion](goal) follows. -/
-- @node: conditionalNullDatasetLaw_bind_eq_dataLaw
lemma conditionalNullDatasetLaw_bind_eq_dataLaw (n : ℕ) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).bind
      (conditionalNullDatasetLaw n) = dataLaw n fairNull := by
  have heq : conditionalNullDatasetLaw n = Causalean.Stat.finProductKernel n fairRecordKernel := by
    funext x
    exact conditionalNullDatasetLaw_eq_product n x
  rw [heq, Causalean.Stat.finProductKernel_comp_pi, fairRecordKernel_comp_volume]
  rfl

/-- The Borel common-mass construction couples the two specified dataset experiments.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n). -/
-- @node: commonMassCoupling_isCoupling
lemma commonMassCoupling_isCoupling (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    Causalean.Stat.IsCoupling (commonMassCoupling hL n)
      (signMixture hL hhL n) (dataLaw n fairNull) := by
  have h := commonMassCoupling_isCoupling_bind hL hhL n
  rw [conditionalAlternativeDatasetLaw_bind_eq_signMixture hL hhL,
    conditionalNullDatasetLaw_bind_eq_dataLaw] at h
  exact h
end CausalSmith.Stat.PrivateCateRoughdesign
