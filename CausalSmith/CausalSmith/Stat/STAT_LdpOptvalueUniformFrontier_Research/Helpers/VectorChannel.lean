module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Protocol
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Helpers/VectorChannel

Finite original-record private value frontiers: Helpers/VectorChannel.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}
-- @env: S4
variable {m : ℕ}
/-- Fix [the sample size and the block size](hyp:n,m). [Standing admissibility of a signed-message block in the n-person experiment](goal). -/
def BlockAdmissible (n m : ℕ) : Prop :=
  1 ≤ m ∧ -- @realizes m(positive block size)
  m ≤ n -- @realizes m(block size at most n)

/-- Fix [the sample size](hyp:n). [Block sizes in the standing paper domain, with both bounds carried by the type](goal). -/
abbrev SignedBlockSize (n : ℕ) := {m : ℕ // BlockAdmissible n m}
  -- @realizes m(integer block size in {1,…,n})

variable (mBlock : SignedBlockSize n) -- @realizes m(standing bounded block-size binder)
/-- Fix [the privacy budget](hyp:eps). [Local noise parameter](goal). -/
def privacyDelta (eps : ℝ) : ℝ := Real.tanh (eps/2) -- @realizes \delta(tanh ε/2)
/-- Fix [the dimension](hyp:d) and [the privacy budget](hyp:eps). [Scaled sign noise](goal). -/
def noiseScale (d : ℕ) (eps : ℝ) : ℝ := d / privacyDelta eps -- @realizes b(d/δ)
/-- Fix [the privacy budget](hyp:eps), [the observed participant record](hyp:o), and [the function z](hyp:z). [Signed-vector atom weight](goal). -/
def vectorMass (eps : ℝ) (o : ObsRecord d) (z : Fin d → Bool) : ℝ :=
  (2 : ℝ)^(-(d : ℤ)) * (1 + privacyDelta eps * obsSign o * signVal (z o.1))
  -- @realizes z(sign-vector message)

-- @node: def:vector-kernel
/-- Fix [the dimension](hyp:d) and [the privacy budget](hyp:eps). [Explicit finite signed-vector channel](goal). -/
def vectorKernel (d : ℕ) (eps : ℝ) : Kernel (ObsRecord d) (Fin d → Bool) :=
  ⟨fun o => atomLaw (vectorMass eps o), measurable_of_countable _⟩
  -- @realizes Q^{\mathrm{vec}}(2⁻ᵈ(1+δSzj))
/-- [Flipping one coordinate pairs the positive and negative signs](goal). -/
-- @node: sum_vector_coordinate_sign
lemma sum_vector_coordinate_sign (j : Fin d) :
    ∑ z : Fin d → Bool, signVal (z j) = 0 := by
  classical
  apply Finset.sum_ninvolution (fun z => Function.update z j (!(z j)))
  · intro z
    cases h : z j <;> simp [signVal, h]
  · intro z _ heq
    have h := congrFun heq j
    cases hz : z j <;> simp [hz] at h
  · intro z
    exact Finset.mem_univ _
  · intro z
    ext l
    by_cases h : l = j
    · subst l
      simp
    · simp [Function.update_of_ne h]
/-- [Signed-vector masses are nonnegative for every real privacy parameter](goal). -/
-- @node: vectorMass_nonneg
lemma vectorMass_nonneg (eps : ℝ) (o : ObsRecord d) (z : Fin d → Bool) :
    0 ≤ vectorMass eps o z := by
  have hlo := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).1
  have hhi := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).2
  unfold vectorMass privacyDelta obsSign signVal
  apply mul_nonneg (by positivity)
  cases o.2.1 <;> cases o.2.2 <;> cases z o.1 <;> norm_num <;> linarith
/-- [Uniform signs cancel the perturbation in the mass sum](goal). -/
-- @node: vectorMass_sum
lemma vectorMass_sum (eps : ℝ) (o : ObsRecord d) :
    ∑ z : Fin d → Bool, vectorMass eps o z = 1 := by
  simp only [vectorMass, Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    sum_vector_coordinate_sign, mul_zero, add_zero, nsmul_eq_mul, mul_one]
  simp [zpow_neg, zpow_natCast]
/-- [Markov certificate for the finite vector channel](goal). -/
-- @node: vectorKernel_markov
lemma vectorKernel_markov (d : ℕ) (eps : ℝ) : IsMarkovKernel (vectorKernel d eps) := by
  constructor
  intro o
  constructor
  change atomLaw (vectorMass eps o) Set.univ = 1
  simp only [atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => vectorMass_nonneg eps o z),
    vectorMass_sum]
  simp
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Constant-history vector stage](goal). -/
def vectorStageKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel ((ObsRecord d × Fin 1) ×
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
        (fun _ : Fin n => Fin d → Bool) i.val (Nat.le_of_lt i.isLt)) (Fin d → Bool) :=
  (vectorKernel d eps).comap (fun w => w.1.1) (measurable_fst.comp measurable_fst)
/-- [Stagewise Markov certificate after ignoring seed and history](goal). -/
-- @node: vectorStage_markov
lemma vectorStage_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (vectorStageKernel n d eps i) := by
  letI := vectorKernel_markov d eps
  unfold vectorStageKernel
  infer_instance
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Original-input vector protocol with a singleton public seed](goal). -/
def vectorProtocol (n d : ℕ) (eps : ℝ) : LocalProtocol n (ObsRecord d) where
  Seed := Fin 1
  seedMeasurable := inferInstance
  seedStandard := inferInstance
  seedLaw := Measure.dirac (0 : Fin 1)
  seedProbability := inferInstance
  Message := fun _ => Fin d → Bool
  messageMeasurable := fun _ => inferInstance
  messageStandard := fun _ => inferInstance
  kernels := vectorStageKernel n d eps
  markov := vectorStage_markov n d eps
/-- Fix [the probability law P](hyp:P) and [the privacy budget](hyp:eps). [One signed-vector message law](goal). -/
def vectorMessageLaw (P : Measure (FullRecord d)) (eps : ℝ) : Measure (Fin d → Bool) :=
  (observedLaw P).bind (vectorKernel d eps)
/-- Fix [the probability law P](hyp:P), [the privacy budget](hyp:eps), and [the block size](hyp:m). [Independent m-row vector-message law](goal). -/
def vectorBlockLaw (P : Measure (FullRecord d)) (eps : ℝ) (m : ℕ) :
    Measure (Fin m → Fin d → Bool) :=
  Measure.pi (fun _ => vectorMessageLaw P eps)
/-- Fix [the privacy budget](hyp:eps), [the function z](hyp:z), [the participant index](hyp:i), and [the coordinate index](hyp:j). [Scaled message matrix](goal). -/
def scaledMessages (eps : ℝ) (z : Fin m → Fin d → Bool) (i : Fin m) (j : Fin d) : ℝ :=
  noiseScale d eps * signVal (z i j) -- @realizes W(b Z_ij)
/-- Fix [the privacy budget](hyp:eps) and [the observed participant record](hyp:o). [Direct product sampler: distinguished coordinate has mean δS; others are fair](goal). -/
def vectorSamplerLaw (eps : ℝ) (o : ObsRecord d) : Measure (Fin d → Bool) :=
  Measure.pi (fun j => atomLaw (fun s : Bool =>
    if j = o.1 then (1 + privacyDelta eps * obsSign o * signVal s)/2 else 1/2))
/-- [A finite atomic law assigns the declared nonnegative mass to each singleton](goal). -/
-- @node: atomLaw_singleton
lemma atomLaw_singleton {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (a : α) :
    atomLaw w {a} = ENNReal.ofReal (w a) := by
  classical
  simp [atomLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', Pi.single_apply]

/-- [The sampler's coordinate weights multiply to the vector-channel mass](goal). -/
-- @node: vectorSamplerMass_product
lemma vectorSamplerMass_product (eps : ℝ) (o : ObsRecord d) (z : Fin d → Bool) :
    (∏ j : Fin d, (if j = o.1 then
      (1 + privacyDelta eps * obsSign o * signVal (z j))/2 else 1/2)) =
      vectorMass eps o z := by
  classical
  have hfactor : ∀ j : Fin d, (if j = o.1 then
      (1 + privacyDelta eps * obsSign o * signVal (z j))/2 else 1/2) =
      (if j = o.1 then 1 + privacyDelta eps * obsSign o * signVal (z j) else 1) * (1/2) := by
    intro j
    split_ifs <;> ring
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_eq_single o.1]
  · simp [vectorMass, zpow_neg, zpow_natCast, inv_pow, mul_comm, one_div]
  · intro j hj hne
    simp [hne]
  · simp

/-- [The finite channel is the stated total product sampler](goal). -/
-- @node: vectorKernel_eq_sampler
lemma vectorKernel_eq_sampler (eps : ℝ) (o : ObsRecord d) :
    vectorKernel d eps o = vectorSamplerLaw eps o := by
  classical
  let w : Fin d → Bool → ℝ := fun j s =>
    if j = o.1 then (1 + privacyDelta eps * obsSign o * signVal s)/2 else 1/2
  have hw : ∀ j s, 0 ≤ w j s := by
    intro j s
    have hlo := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).1
    have hhi := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).2
    dsimp [w, privacyDelta, obsSign, signVal]
    split_ifs <;> cases o.2.1 <;> cases o.2.2 <;> cases s <;> norm_num <;> linarith
  letI : ∀ j : Fin d, IsFiniteMeasure (atomLaw (w j)) := fun j => by
    constructor
    simp only [atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
      Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
    exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)
  apply Measure.ext_of_singleton
  intro z
  change atomLaw (vectorMass eps o) {z} = (Measure.pi (fun j => atomLaw (w j))) {z}
  rw [atomLaw_singleton, Measure.pi_singleton]
  simp_rw [atomLaw_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hw j (z j))]
  congr 1
  exact (vectorSamplerMass_product eps o z).symm
/-- [The tanh parametrization gives the exact randomized-response odds](goal). -/
-- @node: privacyDelta_exp_formula
lemma privacyDelta_exp_formula (eps : ℝ) :
    privacyDelta eps = (Real.exp eps - 1) / (Real.exp eps + 1) := by
  have he : Real.exp (eps/2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have he2 : Real.exp eps = Real.exp (eps/2) * Real.exp (eps/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [privacyDelta, Real.tanh_eq, Real.exp_neg, he2]
  field_simp
  <;> ring

/-- Assume [a nonnegative privacy budget](hyp:heps). [The local sign bias is nonnegative and strictly below one](goal). -/
-- @node: privacyDelta_bounds
lemma privacyDelta_bounds (eps : ℝ) (heps : 0 ≤ eps) :
    0 ≤ privacyDelta eps ∧ privacyDelta eps < 1 := by
  rw [privacyDelta_exp_formula]
  have he := Real.one_le_exp_iff.mpr heps
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_lt_one (by positivity : 0 < Real.exp eps + 1)).mpr
    linarith

/-- [The two extreme sign weights have exactly the pure-privacy ratio](goal). -/
-- @node: privacyDelta_odds_identity
lemma privacyDelta_odds_identity (eps : ℝ) :
    1 + privacyDelta eps = Real.exp eps * (1 - privacyDelta eps) := by
  rw [privacyDelta_exp_formula]
  have he : Real.exp eps + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

/-- Assume [a nonnegative privacy budget](hyp:heps). [Every vector atom satisfies the full original-input privacy bound](goal). -/
-- @node: vectorMass_privacy
lemma vectorMass_privacy (eps : ℝ) (heps : 0 ≤ eps)
    (o o' : ObsRecord d) (z : Fin d → Bool) :
    vectorMass eps o z ≤ Real.exp eps * vectorMass eps o' z := by
  have hdelta := (privacyDelta_bounds eps heps).1
  have hsign : ∀ v : ObsRecord d,
      -privacyDelta eps ≤ privacyDelta eps * obsSign v * signVal (z v.1) ∧
      privacyDelta eps * obsSign v * signVal (z v.1) ≤ privacyDelta eps := by
    intro v
    unfold obsSign signVal
    cases v.2.1 <;> cases v.2.2 <;> cases z v.1 <;> norm_num <;> linarith
  have hupper := (hsign o).2
  have hlower := (hsign o').1
  have hodds := privacyDelta_odds_identity eps
  have hinner : 1 + privacyDelta eps * obsSign o * signVal (z o.1) ≤
      Real.exp eps * (1 + privacyDelta eps * obsSign o' * signVal (z o'.1)) := by
    calc
      _ ≤ 1 + privacyDelta eps := by linarith
      _ = Real.exp eps * (1 - privacyDelta eps) := hodds
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos eps).le
  unfold vectorMass
  calc
    _ ≤ (2 : ℝ)^(-(d : ℤ)) *
        (Real.exp eps * (1 + privacyDelta eps * obsSign o' * signVal (z o'.1))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by ring

/-- Assume [a nonnegative privacy budget](hyp:heps) and [the set hE](hyp:hE). [Summing the atom bounds proves privacy for every measurable message event](goal). -/
-- @node: vectorKernel_privacy
lemma vectorKernel_privacy (eps : ℝ) (heps : 0 ≤ eps)
    (o o' : ObsRecord d) (E : Set (Fin d → Bool)) (hE : MeasurableSet E) :
    vectorKernel d eps o E ≤ ENNReal.ofReal (Real.exp eps) * vectorKernel d eps o' E := by
  classical
  change (atomLaw (vectorMass eps o)) E ≤
    ENNReal.ofReal (Real.exp eps) * (atomLaw (vectorMass eps o')) E
  simp only [atomLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos eps).le]
  simpa only [mul_comm] using
    mul_le_mul_right (ENNReal.ofReal_le_ofReal (vectorMass_privacy eps heps o o' z))
      ((Measure.dirac z) E)

/-- Assume [a nonnegative privacy budget](hyp:heps). [The fixed signed-vector mechanism is noninteractive and pure private](goal). -/
-- @node: vectorProtocol_noninteractive
lemma vectorProtocol_noninteractive (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    NoninteractiveClass (vectorProtocol n d eps) eps := by
  constructor
  · intro i o o' eta r E hE
    exact vectorKernel_privacy eps heps o o' E hE
  · intro i o eta eta' r
    rfl

/-- [One release is a probability law whenever the original record law is](goal). -/
-- @node: vectorMessageLaw_probability
lemma vectorMessageLaw_probability (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) : IsProbabilityMeasure (vectorMessageLaw P eps) := by
  letI := vectorKernel_markov d eps
  letI : IsProbabilityMeasure (observedLaw P) := by
    unfold observedLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  unfold vectorMessageLaw
  exact isProbabilityMeasure_bind (vectorKernel d eps).measurable.aemeasurable
    (Filter.Eventually.of_forall (fun _ => inferInstance))

/-- [Independent rows of the signed-vector mechanism form a probability law](goal). -/
-- @node: vectorBlockLaw_probability
lemma vectorBlockLaw_probability (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (m : ℕ) : IsProbabilityMeasure (vectorBlockLaw P eps m) := by
  letI := vectorMessageLaw_probability P eps
  unfold vectorBlockLaw
  infer_instance

/-- Fix [the dimension](hyp:d) and [the privacy budget](hyp:eps). [Binary outcome randomized response](goal). -/
def binaryOutcomeKernel (d : ℕ) (eps : ℝ) : Kernel (ObsRecord d) Bool :=
  ⟨fun o => atomLaw (fun z => (1 + privacyDelta eps * signVal o.2.2 * signVal z)/2),
    measurable_of_countable _⟩



end CausalSmith.Stat.LdpOptvalueUniformFrontier
