import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Causalean.Experimentation.DesignBased.TwoStage
import Causalean.Stat.FiniteRaoBlackwell.DesignPushforward
import Mathlib.Algebra.Order.Group.CompleteLattice

/-! Paper-local sign-group embedding for the unrestricted two-arm converse. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Experimentation.DesignBased
open Causalean.Stat.FiniteRaoBlackwell

-- @node: signGroupScale
/-- Half of the contrast's `ℓ₁` norm, the scale of the sign-group embedding. -/
noncomputable def signGroupScale (c : Contrast ℝ K) : ℝ := Lc c / 2

-- @node: signGroupScale_pos
/-- [the sign group scale is positive](goal). -/
lemma signGroupScale_pos (c : Contrast ℝ K) : 0 < signGroupScale c := by
  exact div_pos (Lc_pos c) (by norm_num)

-- @node: signGroupScale_sq
/-- [the sign group scale squared property holds](goal). -/
lemma signGroupScale_sq (c : Contrast ℝ K) : signGroupScale c ^ 2 = C0 c := by
  unfold signGroupScale C0
  ring

-- @node: positiveCoefficientSum
/-- [the positive coefficient sums](goal). -/
lemma positiveCoefficientSum (c : Contrast ℝ K) :
    ∑ a with 0 < c a, c a = signGroupScale c := by
  classical
  let P : ℝ := ∑ a with 0 < c a, c a
  let N : ℝ := ∑ a with c a < 0, c a
  have hsum : P + N = 0 := by
    rw [← c.sum_zero]
    dsimp [P, N]
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp : 0 < c a
    · simp [hp, not_lt.mpr hp.le]
    · by_cases hn : c a < 0
      · simp [hp, hn]
      · have hz : c a = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        simp [hp, hn, hz]
  have habs : Lc c =
      P - N := by
    unfold Lc
    dsimp [P, N]
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp : 0 < c a
    · simp [hp, not_lt.mpr hp.le, abs_of_pos hp]
    · by_cases hn : c a < 0
      · simp [hp, hn, abs_of_neg hn]
      · have hz : c a = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        simp [hp, hn, hz]
  unfold signGroupScale
  dsimp [P, N] at hsum habs ⊢
  linarith

-- @node: negativeCoefficientSum
/-- [the negative coefficient sums](goal). -/
lemma negativeCoefficientSum (c : Contrast ℝ K) :
    ∑ a with c a < 0, c a = -signGroupScale c := by
  have hp := positiveCoefficientSum c
  have hs : (∑ a with 0 < c a, c a) + (∑ a with c a < 0, c a) = 0 := by
    classical
    calc
      _ = ∑ a, c a := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        by_cases hpa : 0 < c a
        · simp [hpa, not_lt.mpr hpa.le]
        · by_cases hna : c a < 0
          · simp [hpa, hna]
          · have hz : c a = 0 := le_antisymm (le_of_not_gt hpa) (le_of_not_gt hna)
            simp [hpa, hna, hz]
      _ = 0 := c.sum_zero
  linarith

-- @node: signGroupAssignment
/-- Coarsen a `K`-arm assignment to its positive/negative sign group, using a fair
coin on zero-coefficient arms. -/
noncomputable def signGroupAssignment (c : Contrast ℝ K)
    (w : Assign K n × (Unit n → Bool)) : Assign 2 n := fun i =>
  if 0 < c (w.1 i) then 0 else if c (w.1 i) < 0 then 1 else if w.2 i then 0 else 1

-- @node: embeddedSignSchedule
/-- Embed a two-arm binary schedule by copying its coordinates over the corresponding
positive and negative sign groups and fixing inactive outcomes to zero. -/
noncomputable def embeddedSignSchedule (c : Contrast ℝ K) (z : Schedule 2 n) : Schedule K n := fun i a =>
  if 0 < c a then z i 0 else if c a < 0 then z i 1 else false

-- @node: inactiveZeroObservation
/-- The pseudo-observation supplied to the original estimator: retain active-arm outcomes
and replace inactive-arm outcomes by the fixed embedded value zero. -/
noncomputable def inactiveZeroObservation (c : Contrast ℝ K) (A : Assign K n)
    (y : ObservedOutcome n) : ObservedOutcome n := fun i => if c (A i) = 0 then false else y i

-- @node: embeddedSignSchedule_observation
/-- [the embedded sign schedule observation property holds](goal). -/
lemma embeddedSignSchedule_observation (c : Contrast ℝ K) (z : Schedule 2 n)
    (w : Assign K n × (Unit n → Bool)) :
    inactiveZeroObservation c w.1 (obsOutcome z (signGroupAssignment c w)) =
      obsOutcome (embeddedSignSchedule c z) w.1 := by
  funext i
  unfold inactiveZeroObservation obsOutcome potentialOutcome signGroupAssignment embeddedSignSchedule
  by_cases hp : 0 < c (w.1 i)
  · simp [hp, ne_of_gt hp]
  by_cases hn : c (w.1 i) < 0
  · simp [hp, hn, ne_of_lt hn]
  have hz : c (w.1 i) = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
  simp [hp, hn, hz]

-- @node: embeddedSignSchedule_target
/-- [the embedded sign schedule target property holds](goal). -/
lemma embeddedSignSchedule_target (c : Contrast ℝ K) (z : Schedule 2 n) :
    tauC c (embeddedSignSchedule c z) = signGroupScale c * tauC twoArmContrast z := by
  classical
  have hi (i : Unit n) :
      (∑ a, c a * if embeddedSignSchedule c z i a then 1 else 0) =
        signGroupScale c *
          (∑ a, twoArmContrast a * if z i a then 1 else 0) := by
    have hp := positiveCoefficientSum c
    have hn := negativeCoefficientSum c
    cases z0 : z i 0 <;> cases z1 : z i 1 <;>
      simp [embeddedSignSchedule, twoArmContrast, ratContrastToReal, twoArmContrastQ,
        Fin.sum_univ_succ, z0, z1, Finset.sum_filter] at hp hn ⊢
    · simpa [and_iff_right_of_imp (fun h : c _ < 0 => h.le)] using hn
    · exact hp
    · calc
        (∑ x, if 0 = c x then 0 else c x) = ∑ x, c x := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hz : c a = 0 <;> simp [hz]
        _ = 0 := c.sum_zero
  unfold tauC
  simp_rw [hi]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  ring

-- @node: fairBoolDesign
/-- A fair coin as a finite design. -/
noncomputable def fairBoolDesign : FiniteDesign Bool where
  p := fun _ => 1 / 2
  p_nonneg := by intro; norm_num
  p_sum := by simp [Fintype.sum_bool]

-- @node: signLatentDesign
/-- The original arbitrary assignment design augmented by independent fair inactive-arm coins. -/
noncomputable def signLatentDesign (D : FiniteDesign (Assign K n)) :
    FiniteDesign (Assign K n × (Unit n → Bool)) :=
  compound D (fun _ _ => fairBoolDesign)

-- @node: signLatentDesign_E_fst
/-- [the sign latent design e fst property holds](goal). -/
lemma signLatentDesign_E_fst (D : FiniteDesign (Assign K n)) (f : Assign K n → ℝ) :
    (signLatentDesign D).E (fun w => f w.1) = D.E f := by
  classical
  rw [signLatentDesign, FiniteDesign.E_compound]
  unfold FiniteDesign.E
  apply Finset.sum_congr rfl
  intro A _
  calc
    (∑ s : Unit n → Bool,
        D.p A * (∏ i, fairBoolDesign.p (s i)) * f A) =
        D.p A * f A * ∑ s : Unit n → Bool, ∏ i, fairBoolDesign.p (s i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = D.p A * f A := by
      rw [show (∑ s : Unit n → Bool, ∏ i, fairBoolDesign.p (s i)) = 1 from
        (prodDesign (fun _ : Unit n => fairBoolDesign)).p_sum, mul_one]

-- @node: scaledLatentEstimator
/-- The original estimator, evaluated on the pseudo-observation and rescaled to the
two-arm natural action interval. -/
noncomputable def scaledLatentEstimator (c : Contrast ℝ K) (p : Procedure K n c)
    (w : Assign K n × (Unit n → Bool)) (y : ObservedOutcome n) : ℝ :=
  (signGroupScale c)⁻¹ * (p.2 w.1 (inactiveZeroObservation c w.1 y) : ℝ)

-- @node: scaledLatentEstimator_mem_Icc
/-- [the scaled latent estimator belongs to closed interval](goal). -/
lemma scaledLatentEstimator_mem_Icc (c : Contrast ℝ K) (p : Procedure K n c)
    (w : Assign K n × (Unit n → Bool)) (y : ObservedOutcome n) :
    scaledLatentEstimator c p w y ∈ Set.Icc (-1 : ℝ) 1 := by
  have ha := signGroupScale_pos c
  have hv := (p.2 w.1 (inactiveZeroObservation c w.1 y)).property
  unfold scaledLatentEstimator
  constructor
  · rw [inv_mul_eq_div]
    apply (le_div_iff₀ ha).2
    simpa only [neg_one_mul, signGroupScale, neg_div] using hv.1
  · rw [inv_mul_eq_div]
    apply (div_le_iff₀ ha).2
    simpa only [one_mul, signGroupScale] using hv.2

-- @node: inducedTwoArmProcedure
/-- Rao--Blackwellize the scaled latent estimator along the deterministic sign-group map. -/
noncomputable def inducedTwoArmProcedure (c : Contrast ℝ K) (p : Procedure K n c) :
    Procedure 2 n twoArmContrast :=
  let D := signLatentDesign p.1
  let φ := signGroupAssignment (n := n) c
  (D.map φ, fun b y =>
    ⟨conditionalMeanAlongMap D φ 0 (scaledLatentEstimator c p) b y,
      by
        simpa [Lc, twoArmContrast, ratContrastToReal, twoArmContrastQ,
          Fin.sum_univ_succ] using
          conditionalMeanAlongMap_mem_Icc D φ 0 (scaledLatentEstimator c p) b y
            (by norm_num) (scaledLatentEstimator_mem_Icc c p)⟩)

-- @node: inducedTwoArmProcedure_statewiseRisk
/-- [Statewise squared risk contracts after sign-group coarsening and rescaling.](goal) -/
lemma inducedTwoArmProcedure_statewiseRisk (c : Contrast ℝ K) (p : Procedure K n c)
    (z : Schedule 2 n) :
    labeledRisk twoArmContrast (inducedTwoArmProcedure c p) z ≤
      (signGroupScale c)⁻¹ ^ 2 * labeledRisk c p (embeddedSignSchedule c z) := by
  let D := signLatentDesign p.1
  let φ := signGroupAssignment (n := n) c
  let v : Assign 2 n → ObservedOutcome n := fun b => obsOutcome z b
  have hRB := E_map_conditionalMeanAlongMap_sq_le D φ 0
    (scaledLatentEstimator c p) v (tauC twoArmContrast z)
  unfold labeledRisk FiniteDesign.mse inducedTwoArmProcedure
  change (D.map φ).E (fun b =>
      (conditionalMeanAlongMap D φ 0 (scaledLatentEstimator c p) b (v b) -
        tauC twoArmContrast z) ^ 2) ≤ _
  refine hRB.trans ?_
  rw [show D.E (fun w =>
      (scaledLatentEstimator c p w (v (φ w)) - tauC twoArmContrast z) ^ 2) =
      D.E (fun w => (signGroupScale c)⁻¹ ^ 2 *
        (((p.2 w.1 (obsOutcome (embeddedSignSchedule c z) w.1) : ℝ) -
          tauC c (embeddedSignSchedule c z)) ^ 2)) by
    apply D.E_congr
    intro w
    unfold scaledLatentEstimator
    rw [show v (φ w) = obsOutcome z (signGroupAssignment c w) by rfl,
      embeddedSignSchedule_observation]
    rw [embeddedSignSchedule_target]
    field_simp [(signGroupScale_pos c).ne']]
  rw [D.E_const_mul]
  change (signGroupScale c)⁻¹ ^ 2 *
      D.E (fun w => ((p.2 w.1 (obsOutcome (embeddedSignSchedule c z) w.1) : ℝ) -
        tauC c (embeddedSignSchedule c z)) ^ 2) ≤ _
  rw [show D.E (fun w => ((p.2 w.1 (obsOutcome (embeddedSignSchedule c z) w.1) : ℝ) -
      tauC c (embeddedSignSchedule c z)) ^ 2) =
      p.1.E (fun A => ((p.2 A (obsOutcome (embeddedSignSchedule c z) A) : ℝ) -
        tauC c (embeddedSignSchedule c z)) ^ 2) by
    simpa [D] using signLatentDesign_E_fst p.1
      (fun A => ((p.2 A (obsOutcome (embeddedSignSchedule c z) A) : ℝ) -
        tauC c (embeddedSignSchedule c z)) ^ 2)]

-- @node: inducedTwoArmProcedure_worstCaseRisk
/-- [the induced two arm procedure worst case risk property holds](goal). -/
lemma inducedTwoArmProcedure_worstCaseRisk (c : Contrast ℝ K) (p : Procedure K n c) :
    Causalean.Stat.worstCaseRisk
        (fun (q : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
          labeledRisk twoArmContrast q z) (inducedTwoArmProcedure c p) ≤
      (signGroupScale c)⁻¹ ^ 2 *
        Causalean.Stat.worstCaseRisk
          (fun (q : Procedure K n c) (z : Schedule K n) => labeledRisk c q z) p := by
  apply Causalean.Stat.worstCaseRisk_le
  intro z
  calc
    labeledRisk twoArmContrast (inducedTwoArmProcedure c p) z ≤
        (signGroupScale c)⁻¹ ^ 2 * labeledRisk c p (embeddedSignSchedule c z) :=
      inducedTwoArmProcedure_statewiseRisk c p z
    _ ≤ (signGroupScale c)⁻¹ ^ 2 *
        Causalean.Stat.worstCaseRisk
          (fun (q : Procedure K n c) (z : Schedule K n) => labeledRisk c q z) p := by
      gcongr
      exact Causalean.Stat.le_worstCaseRisk (Finite.bddAbove_range _) _

-- @node: embeddedTwoArmLowerBound
/-- [Every unrestricted `K`-arm procedure induces a no-better two-arm procedure, yielding the sign-group minimax lower bound for arbitrary dependent designs and biased estimators.](goal) -/
lemma embeddedTwoArmLowerBound (K n : ℕ) (c : Contrast ℝ K) :
    C0 c * rho2 n ≤ rhoN K n c := by
  let _ : Nonempty (Procedure K n c) := ⟨contrastWeightedProcedure K n c⟩
  unfold rho2 rhoN
  rw [← signGroupScale_sq c]
  apply Causalean.Stat.le_minimaxValue
  intro p
  have hmin : Causalean.Stat.minimaxValue
      (fun (q : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
        labeledRisk twoArmContrast q z) ≤
      Causalean.Stat.worstCaseRisk
        (fun (q : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
          labeledRisk twoArmContrast q z) (inducedTwoArmProcedure c p) :=
    Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun q z => q.1.mse_nonneg _ _) _
  have h := hmin.trans (inducedTwoArmProcedure_worstCaseRisk c p)
  have ha : signGroupScale c ≠ 0 := (signGroupScale_pos c).ne'
  calc
    signGroupScale c ^ 2 * Causalean.Stat.minimaxValue
        (fun (q : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
          labeledRisk twoArmContrast q z) ≤
        signGroupScale c ^ 2 * ((signGroupScale c)⁻¹ ^ 2 *
          Causalean.Stat.worstCaseRisk
            (fun (q : Procedure K n c) (z : Schedule K n) => labeledRisk c q z) p) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = Causalean.Stat.worstCaseRisk
          (fun (q : Procedure K n c) (z : Schedule K n) => labeledRisk c q z) p := by
      field_simp [ha]

-- @node: exists_positive_contrast_arm
/-- [the exists positive contrast arm](goal). -/
lemma exists_positive_contrast_arm (c : Contrast ℝ K) : ∃ a, 0 < c a := by
  by_contra h
  push_neg at h
  have hp := positiveCoefficientSum c
  have hempty : Finset.univ.filter (fun a => 0 < c a) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun a _ => not_lt.mpr (h a))
  simp only [hempty, Finset.sum_empty] at hp
  exact (signGroupScale_pos c).ne' hp.symm

-- @node: exists_negative_contrast_arm
/-- [the exists negative contrast arm](goal). -/
lemma exists_negative_contrast_arm (c : Contrast ℝ K) : ∃ a, c a < 0 := by
  by_contra h
  push_neg at h
  have hn := negativeCoefficientSum c
  have hempty : Finset.univ.filter (fun a => c a < 0) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun a _ => not_lt.mpr (h a))
  simp only [hempty, Finset.sum_empty] at hn
  exact (signGroupScale_pos c).ne' (neg_eq_zero.mp hn.symm)

-- @node: positiveContrastArm
/-- The positive contrast arm property holds. -/
noncomputable def positiveContrastArm (c : Contrast ℝ K) : Arm K :=
  Classical.choose (exists_positive_contrast_arm c)

-- @node: negativeContrastArm
/-- The negative contrast arm property holds. -/
noncomputable def negativeContrastArm (c : Contrast ℝ K) : Arm K :=
  Classical.choose (exists_negative_contrast_arm c)

-- @node: positiveContrastArm_pos
/-- [the positive contrast arm is positive](goal). -/
lemma positiveContrastArm_pos (c : Contrast ℝ K) : 0 < c (positiveContrastArm c) :=
  Classical.choose_spec (exists_positive_contrast_arm c)

-- @node: negativeContrastArm_neg
/-- [the negative contrast arm neg property holds](goal). -/
lemma negativeContrastArm_neg (c : Contrast ℝ K) : c (negativeContrastArm c) < 0 :=
  Classical.choose_spec (exists_negative_contrast_arm c)

-- @node: support_eq_positive_negative_of_card_two
/-- [the stated side condition holds](hyp:hcard), [the support equals positive negative when cardinality two](goal). -/
lemma support_eq_positive_negative_of_card_two (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) :
    Sc c = {positiveContrastArm c, negativeContrastArm c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (positiveContrastArm_pos c).ne'⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (negativeContrastArm_neg c).ne⟩
  · rw [hcard]
    have hne : positiveContrastArm c ≠ negativeContrastArm c := by
      intro h
      have hp := positiveContrastArm_pos c
      rw [h] at hp
      linarith [negativeContrastArm_neg c]
    simp [hne]

-- @node: coefficient_eq_zero_of_card_two
/-- [the stated side condition holds](hyp:hcard), [the stated side condition holds](hyp:haP), [the stated side condition holds](hyp:haN), [the coefficient equals zero when cardinality two](goal). -/
lemma coefficient_eq_zero_of_card_two (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) {a : Arm K}
    (haP : a ≠ positiveContrastArm c) (haN : a ≠ negativeContrastArm c) : c a = 0 := by
  by_contra ha
  have hm : a ∈ Sc c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  rw [support_eq_positive_negative_of_card_two c hcard] at hm
  simpa [haP, haN] using hm

-- @node: positiveContrastArm_coeff
/-- [the stated side condition holds](hyp:hcard), [the positive contrast arm coeff property holds](goal). -/
lemma positiveContrastArm_coeff (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) : c (positiveContrastArm c) = signGroupScale c := by
  have hp := positiveCoefficientSum c
  classical
  rw [show (∑ a with 0 < c a, c a) = c (positiveContrastArm c) by
    rw [Finset.sum_eq_single (positiveContrastArm c)]
    · intro b hb hne
      have hb0 := coefficient_eq_zero_of_card_two c hcard hne
        (fun h => by
          rw [h] at hb
          linarith [negativeContrastArm_neg c, (Finset.mem_filter.mp hb).2])
      simp [hb0]
    · simp [positiveContrastArm_pos c]
    ] at hp
  exact hp

-- @node: negativeContrastArm_coeff
/-- [the stated side condition holds](hyp:hcard), [the negative contrast arm coeff property holds](goal). -/
lemma negativeContrastArm_coeff (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) : c (negativeContrastArm c) = -signGroupScale c := by
  have hn := negativeCoefficientSum c
  classical
  rw [show (∑ a with c a < 0, c a) = c (negativeContrastArm c) by
    rw [Finset.sum_eq_single (negativeContrastArm c)]
    · intro b hb hne
      have hb0 := coefficient_eq_zero_of_card_two c hcard
        (fun h => by
          rw [h] at hb
          linarith [positiveContrastArm_pos c, (Finset.mem_filter.mp hb).2]) hne
      simp [hb0]
    · simp [negativeContrastArm_neg c]
    ] at hn
  exact hn

-- @node: twoToActiveAssignment
/-- The two to active assignment property holds. -/
noncomputable def twoToActiveAssignment (c : Contrast ℝ K) (B : Assign 2 n) : Assign K n :=
  fun i => if B i = 0 then positiveContrastArm c else negativeContrastArm c

-- @node: activeToTwoAssignment
/-- The active to two assignment property holds. -/
noncomputable def activeToTwoAssignment (c : Contrast ℝ K) (A : Assign K n) : Assign 2 n :=
  fun i => if A i = positiveContrastArm c then 0 else 1

-- @node: positiveContrastArm_ne_negativeContrastArm
/-- [the positive contrast arm ne negative contrast arm property holds](goal). -/
lemma positiveContrastArm_ne_negativeContrastArm (c : Contrast ℝ K) :
    positiveContrastArm c ≠ negativeContrastArm c := by
  intro h
  have hp := positiveContrastArm_pos c
  rw [h] at hp
  linarith [negativeContrastArm_neg c]

-- @node: activeToTwo_twoToActive
/-- [the active to two two to active property holds](goal). -/
lemma activeToTwo_twoToActive (c : Contrast ℝ K) (B : Assign 2 n) :
    activeToTwoAssignment c (twoToActiveAssignment c B) = B := by
  funext i
  generalize hB : B i = b
  fin_cases b
  · simp [activeToTwoAssignment, twoToActiveAssignment, hB]
  · simp [activeToTwoAssignment, twoToActiveAssignment, hB,
      (positiveContrastArm_ne_negativeContrastArm c).symm]

-- @node: activeSchedule
/-- The active schedule property holds. -/
noncomputable def activeSchedule (c : Contrast ℝ K) (z : Schedule K n) : Schedule 2 n :=
  fun i b => z i (if b = 0 then positiveContrastArm c else negativeContrastArm c)

-- @node: activeSchedule_observation
/-- [the active schedule observation property holds](goal). -/
lemma activeSchedule_observation (c : Contrast ℝ K) (z : Schedule K n)
    (B : Assign 2 n) :
    obsOutcome (activeSchedule c z) B = obsOutcome z (twoToActiveAssignment c B) := by
  rfl

-- @node: activeSchedule_target
/-- [the stated side condition holds](hyp:hcard), [the active schedule target property holds](goal). -/
lemma activeSchedule_target (c : Contrast ℝ K) (hcard : (Sc c).card = 2)
    (z : Schedule K n) :
    tauC c z = signGroupScale c * tauC twoArmContrast (activeSchedule c z) := by
  classical
  have hi (i : Unit n) :
      (∑ a, c a * if z i a then 1 else 0) =
        signGroupScale c *
          (∑ b, twoArmContrast b * if activeSchedule c z i b then 1 else 0) := by
    rw [show (∑ a, c a * if z i a then 1 else 0) =
        c (positiveContrastArm c) * (if z i (positiveContrastArm c) then 1 else 0) +
        c (negativeContrastArm c) * (if z i (negativeContrastArm c) then 1 else 0) by
      calc
        _ = ∑ a ∈ {positiveContrastArm c, negativeContrastArm c},
            c a * if z i a then 1 else 0 := by
          symm
          apply Finset.sum_subset (by simp)
          intro a _ ha
          have haP : a ≠ positiveContrastArm c := fun h => ha (by simp [h])
          have haN : a ≠ negativeContrastArm c := fun h => ha (by simp [h])
          simp [coefficient_eq_zero_of_card_two c hcard haP haN]
        _ = _ := by
          have hne : positiveContrastArm c ≠ negativeContrastArm c := by
            intro h
            have hp := positiveContrastArm_pos c
            rw [h] at hp
            linarith [negativeContrastArm_neg c]
          simp [hne]]
    rw [positiveContrastArm_coeff c hcard, negativeContrastArm_coeff c hcard]
    simp [activeSchedule, twoArmContrast, ratContrastToReal, twoArmContrastQ,
      Fin.sum_univ_succ]
    by_cases hP : z i (positiveContrastArm c) <;>
      by_cases hN : z i (negativeContrastArm c) <;> simp [hP, hN] <;> ring
  unfold tauC
  simp_rw [hi, ← mul_assoc]
  rw [← Finset.mul_sum]
  ring

-- @node: liftTwoArmProcedure
/-- The lift two arm procedure property holds. -/
noncomputable def liftTwoArmProcedure (c : Contrast ℝ K) (p : Procedure 2 n twoArmContrast) :
    Procedure K n c :=
  (p.1.map (twoToActiveAssignment c), fun A y =>
    ⟨signGroupScale c * (p.2 (activeToTwoAssignment c A) y : ℝ), by
      have hv := (p.2 (activeToTwoAssignment c A) y).property
      have hLc2 : Lc twoArmContrast = 2 := by
        norm_num [Lc, twoArmContrast, ratContrastToReal, twoArmContrastQ,
          Fin.sum_univ_succ]
      have ha := (signGroupScale_pos c).le
      have hv' : (p.2 (activeToTwoAssignment c A) y : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [hLc2] using hv
      constructor
      · change -Lc c / 2 ≤ signGroupScale c * _
        have hh := mul_le_mul_of_nonneg_left hv'.1 ha
        simpa [signGroupScale, neg_div] using hh
      · change signGroupScale c * _ ≤ Lc c / 2
        simpa [signGroupScale] using mul_le_mul_of_nonneg_left hv'.2 ha⟩)

-- @node: liftTwoArmProcedure_statewiseRisk
/-- [the stated side condition holds](hyp:hcard), [the lift two arm procedure statewise risk property holds](goal). -/
lemma liftTwoArmProcedure_statewiseRisk (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) (p : Procedure 2 n twoArmContrast) (z : Schedule K n) :
    labeledRisk c (liftTwoArmProcedure c p) z =
      signGroupScale c ^ 2 * labeledRisk twoArmContrast p (activeSchedule c z) := by
  unfold labeledRisk FiniteDesign.mse liftTwoArmProcedure
  rw [p.1.E_map]
  rw [← p.1.E_const_mul]
  apply p.1.E_congr
  intro B
  change (signGroupScale c *
      (p.2 (activeToTwoAssignment c (twoToActiveAssignment c B))
        (obsOutcome z (twoToActiveAssignment c B)) : ℝ) - tauC c z) ^ 2 =
    signGroupScale c ^ 2 *
      ((p.2 B (obsOutcome (activeSchedule c z) B) : ℝ) -
        tauC twoArmContrast (activeSchedule c z)) ^ 2
  rw [activeToTwo_twoToActive, activeSchedule_observation, activeSchedule_target c hcard]
  ring

-- @node: supportTwoUpperBound
/-- [the stated side condition holds](hyp:hcard), [the support two upper bound property holds](goal). -/
lemma supportTwoUpperBound (K n : ℕ) (c : Contrast ℝ K)
    (hcard : (Sc c).card = 2) : rhoN K n c ≤ C0 c * rho2 n := by
  let _ : Nonempty (Procedure 2 n twoArmContrast) :=
    ⟨contrastWeightedProcedure 2 n twoArmContrast⟩
  unfold rhoN rho2
  rw [← signGroupScale_sq c]
  let A : ℝ := signGroupScale c ^ 2
  have hA : 0 < A := by dsimp [A]; exact sq_pos_of_pos (signGroupScale_pos c)
  have hscale : A * Causalean.Stat.minimaxValue
      (fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
        labeledRisk twoArmContrast p z) =
      Causalean.Stat.minimaxValue
        (fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
          A * labeledRisk twoArmContrast p z) := by
    unfold Causalean.Stat.minimaxValue Causalean.Stat.worstCaseRisk
    have hbdd : BddBelow (Set.range (fun p : Procedure 2 n twoArmContrast =>
        ⨆ z : Schedule 2 n, labeledRisk twoArmContrast p z)) :=
      Causalean.Stat.bddBelow_range_worstCaseRisk
        (fun (p : Procedure 2 n twoArmContrast) z => p.1.mse_nonneg _ _)
    calc
      A * (⨅ p : Procedure 2 n twoArmContrast,
          ⨆ z : Schedule 2 n, labeledRisk twoArmContrast p z) =
          ⨅ p : Procedure 2 n twoArmContrast,
            A * (⨆ z : Schedule 2 n, labeledRisk twoArmContrast p z) :=
        (OrderIso.mulLeft₀ A hA).map_ciInf hbdd
      _ = ⨅ p : Procedure 2 n twoArmContrast,
          ⨆ z : Schedule 2 n, A * labeledRisk twoArmContrast p z := by
        congr with p
        exact (OrderIso.mulLeft₀ A hA).map_ciSup (Finite.bddAbove_range _)
  change Causalean.Stat.minimaxValue
      (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z) ≤
    A * Causalean.Stat.minimaxValue
      (fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
        labeledRisk twoArmContrast p z)
  rw [hscale]
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk (fun p z => p.1.mse_nonneg _ _))
  intro p
  refine ⟨liftTwoArmProcedure c p, ?_⟩
  apply Causalean.Stat.worstCaseRisk_le
  intro z
  rw [liftTwoArmProcedure_statewiseRisk c hcard]
  change A * labeledRisk twoArmContrast p (activeSchedule c z) ≤ _
  exact Causalean.Stat.le_worstCaseRisk
    (risk := fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
      A * labeledRisk twoArmContrast p z)
    (e := p) (Finite.bddAbove_range _) (activeSchedule c z)

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
