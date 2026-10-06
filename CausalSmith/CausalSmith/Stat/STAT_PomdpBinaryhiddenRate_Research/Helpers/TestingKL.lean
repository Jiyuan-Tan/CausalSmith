module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingFamilyBasics
public import Causalean.Mathlib.InformationTheory.FiniteKL
public import Causalean.Mathlib.Analysis.BernoulliKL

/-!
# Quantitative divergence of the testing pair

Cancel the common state and action factors and sum the conditional Bernoulli
reward divergences before projecting the finite path law to observed data.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators

/-- Independent finite factors with common masses and bounded one-factor
entropy have a product entropy bounded by the sum of their budgets. [Under the listed formal conditions](hyp:hp,hq,hm,hs,hb), [the stated conclusion holds](goal).-/
-- @node: testing_product_entropy_le
lemma testing_product_entropy_le {A : Type*} [Fintype A] (n : Nat)
    (p q : Fin n → A → ℝ) (m : Fin n → ℝ) (C : ℝ)
    (hp : ∀ i a, 0 < p i a) (hq : ∀ i a, 0 < q i a)
    (hm : ∀ i, 0 ≤ m i) (hs : ∀ i, ∑ a, p i a = m i)
    (hb : ∀ i, (∑ a, p i a * Real.log (p i a / q i a)) ≤ C * m i) :
    (∑ f : Fin n → A, (∏ i, p i (f i)) *
      Real.log ((∏ i, p i (f i)) / (∏ i, q i (f i)))) ≤
        (n : ℝ) * C * ∏ i, m i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let pt : Fin n → A → ℝ := fun i => p i.succ
    let qt : Fin n → A → ℝ := fun i => q i.succ
    let mt : Fin n → ℝ := fun i => m i.succ
    let D : ℝ := ∑ f : Fin n → A, (∏ i, pt i (f i)) *
      Real.log ((∏ i, pt i (f i)) / (∏ i, qt i (f i)))
    let H : ℝ := ∑ a, p 0 a * Real.log (p 0 a / q 0 a)
    let M : ℝ := ∏ i, mt i
    have htail : D ≤ (n : ℝ) * C * M :=
      ih pt qt mt (by intro i a; exact hp _ _) (by intro i a; exact hq _ _)
        (by intro i; exact hm _) (by intro i; exact hs _) (by intro i; exact hb _)
    have hsum : (∑ f : Fin n → A, ∏ i, pt i (f i)) = M := by
      simpa [M, mt, pt, Fintype.piFinset_univ, hs] using
        (Finset.sum_prod_piFinset (Finset.univ : Finset A) pt)
    have hM : 0 ≤ M := Finset.prod_nonneg (by intro i _; exact hm _)
    have heq : (∑ f : Fin (n + 1) → A, (∏ i, p i (f i)) *
        Real.log ((∏ i, p i (f i)) / (∏ i, q i (f i)))) = H * M + m 0 * D := by
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => A))
        (fun z : A × (Fin n → A) => (∏ i, p i ((Fin.cons (α := fun _ => A) z.1 z.2) i)) *
          Real.log ((∏ i, p i ((Fin.cons (α := fun _ => A) z.1 z.2) i)) /
            (∏ i, q i ((Fin.cons (α := fun _ => A) z.1 z.2) i)))) _ (by intro z; rfl)]
      simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hlog (a : A) (f : Fin n → A) :
          Real.log ((p 0 a * ∏ i, p i.succ (f i)) /
            (q 0 a * ∏ i, q i.succ (f i))) =
          Real.log (p 0 a / q 0 a) +
            Real.log ((∏ i, pt i (f i)) / (∏ i, qt i (f i))) := by
        rw [mul_div_mul_comm, Real.log_mul (ne_of_gt (div_pos (hp _ _) (hq _ _)))
          (ne_of_gt (div_pos (Finset.prod_pos (by intro i _; exact hp _ _))
            (Finset.prod_pos (by intro i _; exact hq _ _))))]
      simp_rw [hlog]
      simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [show ∀ (a : A) (f : Fin n → A), (p 0 a * ∏ i, p i.succ (f i)) *
          Real.log (p 0 a / q 0 a) =
          (p 0 a * Real.log (p 0 a / q 0 a)) * ∏ i, pt i (f i) by
            intro a f; dsimp [pt]; ring]
      simp_rw [← Finset.mul_sum, hsum]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp only [← Finset.sum_mul, hs, H, D]
      simp only [← mul_assoc, ← Finset.sum_mul, pt]
    rw [heq, Fin.prod_univ_succ, Nat.cast_add, Nat.cast_one]
    calc
      H * M + m 0 * D ≤ (C * m 0) * M + m 0 * ((n : ℝ) * C * M) :=
        add_le_add (mul_le_mul_of_nonneg_right (hb 0) hM)
          (mul_le_mul_of_nonneg_left htail (hm 0))
      _ = _ := by dsimp [M, mt]; ring

/-- One fair-action epoch mass, with a Boolean reward. -/
-- @node: testingKLStep
noncomputable def testingKLStep (v : ℝ) (s sp : JointState 2 2)
    (ay : Bool × Bool) : ℝ :=
  (1 / 2 : ℝ) *
    (if ay.2 then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
    (if sp.2 = 1 then testingHiddenProb ay.1 else 1 - testingHiddenProb ay.1) *
    testingEmission sp.1 sp.2

/-- Every single-epoch testing mass is positive. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingKLStep_pos
lemma testingKLStep_pos (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s sp : JointState 2 2) (ay : Bool × Bool) : 0 < testingKLStep v s sp ay := by
  have hq := testingRewardProb_mem_Icc v hv s.2
  unfold testingKLStep
  apply mul_pos
  · apply mul_pos
    · apply mul_pos (by norm_num)
      split_ifs <;> linarith [hq.1, hq.2]
    · cases ay.1 <;> split_ifs <;> norm_num [testingHiddenProb]
  · unfold testingEmission
    split_ifs <;> norm_num

/-- Reward and action marginalization leaves the common next-state mass. [the stated conclusion holds](goal).-/
-- @node: testingKLStep_sum
lemma testingKLStep_sum (v : ℝ) (s sp : JointState 2 2) :
    ∑ ay, testingKLStep v s sp ay = testingNextStateMass sp :=
  testingStepMarginal_sum v s sp

/-- The common transition factors cancel from the one-epoch KL contribution. [Under the listed formal conditions](hyp:hv,hw), [the stated conclusion holds](goal).-/
-- @node: testingKLStep_entropy_le
lemma testingKLStep_entropy_le (v w : ℝ) (hv : |v| ≤ 1 / 16)
    (hw : |w| ≤ 1 / 16) (s sp : JointState 2 2) :
    (∑ ay, testingKLStep v s sp ay *
      Real.log (testingKLStep v s sp ay / testingKLStep w s sp ay)) ≤
        (4 * (v - w) ^ 2) * testingNextStateMass sp := by
  let p := testingRewardProb v s.2
  let q := testingRewardProb w s.2
  let c (a : Bool) : ℝ := (1 / 2 : ℝ) *
    (if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
    testingEmission sp.1 sp.2
  have hc (a : Bool) : 0 < c a := by
    dsimp [c]
    apply mul_pos
    · apply mul_pos (by norm_num)
      cases a <;> split_ifs <;> norm_num [testingHiddenProb]
    · unfold testingEmission
      split_ifs <;> norm_num
  have hp := testingRewardProb_mem_Icc v hv s.2
  have hq := testingRewardProb_mem_Icc w hw s.2
  have hbern := Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
    hp.1 hp.2 hq.1 hq.2
  have hdiff : p - q = v - w := by
    dsimp [p, q, testingRewardProb]
    ring
  have hstep (a y : Bool) : testingKLStep v s sp (a, y) =
      c a * (if y then p else 1 - p) := by
    dsimp [testingKLStep, c, p]
    ring
  have hstep' (a y : Bool) : testingKLStep w s sp (a, y) =
      c a * (if y then q else 1 - q) := by
    dsimp [testingKLStep, c, q]
    ring
  have hmass : (∑ a, c a) = testingNextStateMass sp := by
    rcases sp with ⟨x, h⟩
    fin_cases x <;> fin_cases h <;>
      norm_num [c, testingNextStateMass, testingHiddenProb, testingEmission, Fintype.sum_bool]
  calc
    _ = (∑ a, c a) * (p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q))) := by
      rw [Fintype.sum_prod_type]
      simp_rw [hstep, hstep', mul_div_mul_left _ _ (ne_of_gt (hc _))]
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      ring
    _ ≤ (∑ a, c a) * (4 * (v - w) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [← hdiff] using hbern
      · exact Finset.sum_nonneg (by intro a _; exact (hc a).le)
    _ = _ := by rw [hmass]; ring

/-- Canceling the common initial mass and adding epoch budgets bounds the
complete-data finite path entropy. [Under the listed formal conditions](hyp:hv,hw), [the stated conclusion holds](goal).-/
-- @node: testingPath_entropy_le
lemma testingPath_entropy_le (T : Nat) (v w : ℝ)
    (hv : |v| ≤ 1 / 16) (hw : |w| ≤ 1 / 16) :
    (∑ c : TestingPath T, testingPathWeight v c *
      Real.log (testingPathWeight v c / testingPathWeight w c)) ≤
        (T : ℝ) * (4 * (v - w) ^ 2) := by
  let init (xs : Fin (T + 1) → JointState 2 2) : ℝ :=
    (1 / 2 : ℝ) * testingEmission (xs 0).1 (xs 0).2
  have hi (xs : Fin (T + 1) → JointState 2 2) : 0 < init xs := by
    dsimp [init]
    apply mul_pos (by norm_num)
    unfold testingEmission
    split_ifs <;> norm_num
  have hm (sp : JointState 2 2) : 0 ≤ testingNextStateMass sp := by
    rcases sp with ⟨x, h⟩
    fin_cases x <;> fin_cases h <;>
      norm_num [testingNextStateMass, testingHiddenProb, testingEmission]
  calc
    _ = ∑ xs : Fin (T + 1) → JointState 2 2, init xs *
          (∑ ay : Fin T → Bool × Bool,
            (∏ t, testingKLStep v (xs t.castSucc) (xs t.succ) (ay t)) *
            Real.log ((∏ t, testingKLStep v (xs t.castSucc) (xs t.succ) (ay t)) /
              (∏ t, testingKLStep w (xs t.castSucc) (xs t.succ) (ay t)))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro xs _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ay _
      change (init xs * ∏ t, testingKLStep v (xs t.castSucc) (xs t.succ) (ay t)) *
          Real.log ((init xs * ∏ t, testingKLStep v (xs t.castSucc) (xs t.succ) (ay t)) /
            (init xs * ∏ t, testingKLStep w (xs t.castSucc) (xs t.succ) (ay t))) = _
      rw [mul_div_mul_left _ _ (ne_of_gt (hi xs))]
      ring
    _ ≤ ∑ xs : Fin (T + 1) → JointState 2 2, init xs *
          ((T : ℝ) * (4 * (v - w) ^ 2) * ∏ t : Fin T, testingNextStateMass (xs t.succ)) := by
      apply Finset.sum_le_sum
      intro xs _
      apply mul_le_mul_of_nonneg_left _ (hi xs).le
      exact testing_product_entropy_le T
        (fun t ay => testingKLStep v (xs t.castSucc) (xs t.succ) ay)
        (fun t ay => testingKLStep w (xs t.castSucc) (xs t.succ) ay)
        (fun t => testingNextStateMass (xs t.succ)) (4 * (v - w) ^ 2)
        (by intro t ay; exact testingKLStep_pos v hv _ _ ay)
        (by intro t ay; exact testingKLStep_pos w hw _ _ ay)
        (by intro t; exact hm _) (by intro t; exact testingKLStep_sum v _ _)
        (by intro t; exact testingKLStep_entropy_le v w hv hw _ _)
    _ = _ := by
      simp_rw [show ∀ xs : Fin (T + 1) → JointState 2 2,
        init xs * ((T : ℝ) * (4 * (v - w) ^ 2) *
          ∏ t : Fin T, testingNextStateMass (xs t.succ)) =
        ((T : ℝ) * (4 * (v - w) ^ 2)) *
          (init xs * ∏ t : Fin T, testingNextStateMass (xs t.succ)) by
            intro xs; ring]
      rw [← Finset.mul_sum]
      have hmass := testingStateMass_sum T testingNextStateMass testingNextStateMass_sum
      change (T : ℝ) * (4 * (v - w) ^ 2) *
        (∑ xs : Fin (T + 1) → JointState 2 2, ((1 / 2 : ℝ) * testingEmission (xs 0).1 (xs 0).2) *
          ∏ t : Fin T, testingNextStateMass (xs t.succ)) = _
      rw [hmass, mul_one]

/-- Keep the finite Boolean path carrier before decoding to real rewards. -/
-- @node: testingFinitePathLaw
noncomputable def testingFinitePathLaw (T : Nat) (v : ℝ) : Measure (TestingPath T) :=
  ∑ c : TestingPath T, ENNReal.ofReal (testingPathWeight v c) • Measure.dirac c

/-- The finite path law assigns its displayed weight to each singleton. [the stated conclusion holds](goal).-/
-- @node: testingFinitePathLaw_mass
lemma testingFinitePathLaw_mass (T : Nat) (v : ℝ) (c : TestingPath T) :
    testingFinitePathLaw T v {c} = ENNReal.ofReal (testingPathWeight v c) := by
  classical
  simp [testingFinitePathLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator, eq_comm]

/-- The finite path measure is normalized throughout the perturbation range. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFinitePathLaw_probability
lemma testingFinitePathLaw_probability (T : Nat) (v : ℝ) (hv : |v| ≤ 1 / 16) :
    IsProbabilityMeasure (testingFinitePathLaw T v) := by
  constructor
  simp only [testingFinitePathLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro c _; exact testingPathWeight_nonneg v hv c),
    testingPathWeight_sum]
  norm_num

/-- Strictly positive finite path weights give common support. [Under the listed formal conditions](hyp:hw), [the stated conclusion holds](goal).-/
-- @node: testingFinitePathLaw_ac
lemma testingFinitePathLaw_ac (T : Nat) (v w : ℝ) (hw : |w| ≤ 1 / 16) :
    testingFinitePathLaw T v ≪ testingFinitePathLaw T w := by
  intro A hA
  simp only [testingFinitePathLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul] at hA ⊢
  have hzero := Finset.sum_eq_zero_iff.mp hA
  apply Finset.sum_eq_zero_iff.mpr
  intro c hc
  have hc0 := hzero c hc
  have hpos : ENNReal.ofReal (testingPathWeight w c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (testingPathWeight_pos w hw c))
  rw [(mul_eq_zero.mp hc0).resolve_left hpos, mul_zero]

/-- Decoding the finite path measure gives the declared full trajectory law. [the stated conclusion holds](goal).-/
-- @node: testingFinitePathLaw_map
lemma testingFinitePathLaw_map (T : Nat) (v : ℝ) :
    (testingFinitePathLaw T v).map decodeTestingPath = testingTrajectoryLaw T v := by
  have hf : Measurable (decodeTestingPath (T := T)) := by fun_prop
  unfold testingFinitePathLaw testingTrajectoryLaw
  have hmap (F : Finset (TestingPath T)) :
      (∑ c ∈ F, ENNReal.ofReal (testingPathWeight v c) • Measure.dirac c).map
          decodeTestingPath =
        ∑ c ∈ F, ENNReal.ofReal (testingPathWeight v c) •
          Measure.dirac (decodeTestingPath c) := by
    classical
    induction F using Finset.induction_on with
    | empty => simp
    | @insert c F hc ih =>
      simp only [Finset.sum_insert hc]
      rw [Measure.map_add _ _ hf, ih]
      simp [Measure.map_smul, Measure.map_dirac' hf]
  exact hmap Finset.univ

/-- Each reward contributes its Bernoulli divergence; data processing then
bounds the observed-law divergence without assumptions on history identities. [Under the listed formal conditions](hyp:hvFamily,hv,hwFamily,hw), [the stated conclusion holds](goal).-/
-- @node: testingObservedLaw_klDiv_le
lemma testingObservedLaw_klDiv_le (T : Nat) (v w : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (hwFamily : w = vT T ∨ w = -(vT T)) (hw : |w| ≤ 1 / 16) :
    InformationTheory.klDiv
      (obsLaw (testingExperiment T v hvFamily hv))
      (obsLaw (testingExperiment T w hwFamily hw)) ≤
        ENNReal.ofReal ((T : ℝ) * (4 * (v - w) ^ 2)) := by
  let := testingFinitePathLaw_probability T v hv
  let := testingFinitePathLaw_probability T w hw
  have hac := testingFinitePathLaw_ac T v w hw
  have hfin : InformationTheory.klDiv (testingFinitePathLaw T v)
      (testingFinitePathLaw T w) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac (Integrable.of_finite)
  have hbound : (InformationTheory.klDiv (testingFinitePathLaw T v)
      (testingFinitePathLaw T w)).toReal ≤ (T : ℝ) * (4 * (v - w) ^ 2) := by
    rw [Causalean.Mathlib.InformationTheory.klDiv_toReal_eq_sum_measureReal _ _ hac]
    simp only [measureReal_def, testingFinitePathLaw_mass,
      ENNReal.toReal_ofReal (testingPathWeight_nonneg v hv _),
      ENNReal.toReal_ofReal (testingPathWeight_nonneg w hw _)]
    exact testingPath_entropy_le T v w hv hw
  have hfull : InformationTheory.klDiv (testingTrajectoryLaw T v)
      (testingTrajectoryLaw T w) ≤
      InformationTheory.klDiv (testingFinitePathLaw T v) (testingFinitePathLaw T w) := by
    rw [← testingFinitePathLaw_map T v, ← testingFinitePathLaw_map T w]
    exact InformationTheory.klDiv_map_le _ _ (by fun_prop)
  have hobs : InformationTheory.klDiv
      (obsLaw (testingExperiment T v hvFamily hv))
      (obsLaw (testingExperiment T w hwFamily hw)) ≤
        InformationTheory.klDiv (testingTrajectoryLaw T v) (testingTrajectoryLaw T w) := by
    have hf : Measurable (obsProj (T := T) (nX := 2) (nH := 2)) := by
      unfold obsProj curState actionAt rewardAt
      fun_prop
    exact InformationTheory.klDiv_map_le _ _ hf
  apply hobs.trans (hfull.trans _)
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hbound

end CausalSmith.Stat.PomdpBinaryhiddenRate
