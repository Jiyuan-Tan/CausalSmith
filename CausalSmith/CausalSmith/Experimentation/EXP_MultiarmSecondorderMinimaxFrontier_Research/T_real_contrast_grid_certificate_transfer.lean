import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_rational_contrast_grid_certificate_sandwich
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_contrast_risk_continuity
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_embedded_two_arm_converse
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.Symmetrization
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.RationalContrastApproximation

/-! Transfer of exact rational finite-program certificates to real contrasts. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The full-data rule uses exactly `pi`'s uniform allocation-orbit lift and the
projection of the same upstream barycenter `delta`. -/
def IsProjectedUpperProcedureCertificate (K n : ℕ) (c : Contrast ℝ K)
    (pi : GridPi K n) (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
    (p : Procedure K n c) (Rplus : ℝ) : Prop :=
  (∀ A, p.1.p A = (pi (assignmentCounts A) : ℝ) /
    allocationOrbitCard (assignmentCounts A)) ∧
  (∀ A y, (p.2 A y : ℝ) =
    clip c (delta (assignmentCounts A) (observedCounts A y))) ∧
  Causalean.Stat.worstCaseRisk
    (fun (q : Procedure K n c) (z : Schedule K n) => labeledRisk c q z) p ≤ Rplus

/-- Cardinality of the labeled-schedule orbit having response counts `m`. -/
noncomputable def responseCountOrbitCard (m : CountVec K n) : ℕ :=
  by
    exact Nat.card {z : Schedule K n // scheduleCounts z = m}

-- @node: responseCountOrbitCard_pos
/-- [the response count orbit cardinality is positive](goal). -/
lemma responseCountOrbitCard_pos (m : CountVec K n) :
    0 < responseCountOrbitCard m := by
  obtain ⟨z, hz⟩ := exists_fun_card_fiber_eq
    (C := RespType K) (fun t => (m.1 t : ℕ)) m.2
  have hm : scheduleCounts z = m := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    simpa [scheduleCounts, rawScheduleCount] using hz t
  unfold responseCountOrbitCard
  letI : Nonempty {z : Schedule K n // scheduleCounts z = m} := ⟨⟨z, hm⟩⟩
  exact Nat.card_pos (α := {z : Schedule K n // scheduleCounts z = m})

-- @node: responseCountFiber_card
/-- [the response count fiber cardinality property holds](goal). -/
lemma responseCountFiber_card (m : CountVec K n) :
    Nat.card {z : Schedule K n // scheduleCounts z = m} =
      responseCountOrbitCard m := by
  rfl

-- @node: scheduleCounts_permute_eq
/-- [the schedule counts permute equals property holds](goal). -/
lemma scheduleCounts_permute_eq (sigma : Equiv.Perm (Unit n)) (z : Schedule K n) :
    scheduleCounts (permuteSchedule sigma z) = scheduleCounts z := by
  apply Subtype.ext
  funext t
  apply Fin.ext
  change (Finset.univ.filter fun i => z (sigma.symm i) = t).card =
    (Finset.univ.filter fun i => z i = t).card
  let e : {i : Unit n // z i = t} ≃
      {i : Unit n // z (sigma.symm i) = t} :=
    { toFun := fun i => ⟨sigma i.1, by simpa using i.2⟩
      invFun := fun i => ⟨sigma.symm i.1, i.2⟩
      left_inv := by intro i; apply Subtype.ext; exact sigma.symm_apply_apply i.1
      right_inv := by intro i; apply Subtype.ext; exact sigma.apply_symm_apply i.1 }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e |>.symm

-- @node: schedulePriorOfRationalPrior
/-- A rational prior on response-count orbits induces a labeled schedule prior by spreading each orbit mass uniformly over its schedules. -/
noncomputable def schedulePriorOfRationalPrior
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Schedule K n) where
  p z := (nu (scheduleCounts z) : ℝ) /
    responseCountOrbitCard (scheduleCounts z)
  p_nonneg z := div_nonneg (by exact_mod_cast hnu.1 (scheduleCounts z)) (Nat.cast_nonneg _)
  p_sum := by
    classical
    rw [← Finset.sum_fiberwise Finset.univ scheduleCounts
      (fun z => (nu (scheduleCounts z) : ℝ) /
        responseCountOrbitCard (scheduleCounts z))]
    calc
      ∑ m : CountVec K n,
          ∑ z : Schedule K n with scheduleCounts z = m,
            (nu (scheduleCounts z) : ℝ) / responseCountOrbitCard (scheduleCounts z) =
          ∑ m : CountVec K n, (nu m : ℝ) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_congr rfl (fun z hz => by
          simp only [Finset.mem_filter] at hz
          rw [hz.2])]
        rw [Finset.sum_const, nsmul_eq_mul]
        letI := Fintype.ofFinite {z : Schedule K n // scheduleCounts z = m}
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
          responseCountFiber_card]
        have hm : (responseCountOrbitCard m : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (responseCountOrbitCard_pos m))
        exact mul_div_cancel₀ _ hm
      _ = 1 := by exact_mod_cast hnu.2

-- @node: schedulePriorOfRationalPrior_permute
/-- [the stated side condition holds](hyp:hnu), [the schedule prior when rational prior permute property holds](goal). -/
lemma schedulePriorOfRationalPrior_permute
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu)
    (sigma : Equiv.Perm (Unit n)) (z : Schedule K n) :
    (schedulePriorOfRationalPrior nu hnu).p (permuteSchedule sigma z) =
      (schedulePriorOfRationalPrior nu hnu).p z := by
  simp [schedulePriorOfRationalPrior, scheduleCounts_permute_eq]

-- @node: schedulePriorOfRationalPrior_E_permute
/-- [the stated side condition holds](hyp:hnu), [the schedule prior when rational prior e permute property holds](goal). -/
lemma schedulePriorOfRationalPrior_E_permute
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu)
    (sigma : Equiv.Perm (Unit n)) (f : Schedule K n → ℝ) :
    (schedulePriorOfRationalPrior nu hnu).E (fun z => f (permuteSchedule sigma z)) =
      (schedulePriorOfRationalPrior nu hnu).E f := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  let e : Equiv.Perm (Schedule K n) :=
    { toFun := permuteSchedule sigma
      invFun := permuteSchedule sigma.symm
      left_inv := by
        intro z
        funext i
        change z (sigma.symm (sigma i)) = z i
        rw [sigma.symm_apply_apply]
      right_inv := by
        intro z
        funext i
        change z (sigma (sigma.symm i)) = z i
        rw [sigma.apply_symm_apply] }
  have hsum := Equiv.sum_comp e (fun z =>
    (schedulePriorOfRationalPrior nu hnu).p z * f z)
  dsimp [e] at hsum
  simpa only [e, schedulePriorOfRationalPrior_permute] using hsum

-- @node: schedulePriorOfRationalPrior_E_count
/-- [the stated side condition holds](hyp:hnu), [the schedule prior when rational prior e count property holds](goal). -/
lemma schedulePriorOfRationalPrior_E_count
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu)
    (f : CountVec K n → ℝ) :
    (schedulePriorOfRationalPrior nu hnu).E (fun z => f (scheduleCounts z)) =
      ∑ m, (nu m : ℝ) * f m := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [← Finset.sum_fiberwise Finset.univ scheduleCounts
    (fun z => (schedulePriorOfRationalPrior nu hnu).p z * f (scheduleCounts z))]
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = ∑ _z : Schedule K n with scheduleCounts _z = m,
        (nu m : ℝ) / responseCountOrbitCard m * f m := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.mem_filter] at hz
      simp [schedulePriorOfRationalPrior, hz.2]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      letI := Fintype.ofFinite {z : Schedule K n // scheduleCounts z = m}
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        responseCountFiber_card]
      have hm : (responseCountOrbitCard m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (responseCountOrbitCard_pos m))
      field_simp

-- @node: lowerCertificate_le_schedulePriorRisk
/-- [the population size is positive](hyp:hn), [the stated side condition holds](hyp:hnu), [the lower certificate is at most schedule prior risk](goal). -/
lemma lowerCertificate_le_schedulePriorRisk
    (q : RatContrast K) (hn : 0 < n)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu)
    (p : Procedure K n (ratContrastToReal q)) :
    lowerCertificate q nu ≤
      (schedulePriorOfRationalPrior nu hnu).E (fun z =>
        labeledRisk (ratContrastToReal q) p z) := by
  classical
  have hK := rationalContrast_admissibleArmCount q
  have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
  letI : Nonempty (Arm K) := Fintype.card_pos_iff.mp (by simpa using hKpos)
  letI : Nonempty (AllocVec K n) :=
    ⟨assignmentCounts (fun _ => Classical.choice inferInstance)⟩
  letI : Fintype (Equiv.Perm (Unit n)) := Fintype.ofFinite _
  obtain ⟨pbar, qo, _hinv, _havg, _hpbar, hdom⟩ :=
    lossless_symmetrization (ratContrastToReal q) p
  let qo' : Causalean.Stat.Minimax.FiniteSquaredLoss.Procedure
      (fun r : AllocVec K n => ObsVec r)
      (-Lc (ratContrastToReal q) / 2) (Lc (ratContrastToReal q) / 2) :=
    ⟨qo.1, qo.2⟩
  have horbit : lowerCertificate q nu ≤
      ∑ m, (nu m : ℝ) * orbitRisk (ratContrastToReal q) qo m := by
    rw [lowerCertificate_eq_posteriorResidual_sInf q nu hnu]
    simpa [rationalPriorOf, rationalOrbitModel, orbitRisk, tauCountRat_cast,
      Causalean.Stat.Minimax.FiniteSquaredLoss.risk, qo'] using
      (rationalOrbitModel (n := n) q).sInf_posteriorResidual_le_priorRisk
        (rationalPriorOf nu hnu) qo'
  calc
    lowerCertificate q nu ≤
        (schedulePriorOfRationalPrior nu hnu).E (fun z =>
          orbitRisk (ratContrastToReal q) qo (scheduleCounts z)) := by
      simpa [schedulePriorOfRationalPrior_E_count] using horbit
    _ ≤ (schedulePriorOfRationalPrior nu hnu).E (fun z =>
        (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
          ∑ sigma : Equiv.Perm (Unit n),
            labeledRisk (ratContrastToReal q) p (permuteSchedule sigma z)) := by
      unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left
      · change orbitRisk (ratContrastToReal q) qo (scheduleCounts z) ≤ _
        simpa only [] using hdom z
      · exact
        ((schedulePriorOfRationalPrior nu hnu).p_nonneg z)
    _ = (schedulePriorOfRationalPrior nu hnu).E (fun z =>
        labeledRisk (ratContrastToReal q) p z) := by
      rw [(schedulePriorOfRationalPrior nu hnu).E_const_mul]
      rw [(schedulePriorOfRationalPrior nu hnu).E_sum]
      rw [Finset.sum_congr rfl (fun sigma _ =>
        schedulePriorOfRationalPrior_E_permute nu hnu sigma
          (fun z => labeledRisk (ratContrastToReal q) p z))]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Equiv.Perm (Unit n)) : ℝ) ≠ 0 := by positivity
      field_simp

-- @node: lowerCertificate_nonneg
/-- [the stated side condition holds](hyp:hnu), [the lower certificate is nonnegative](goal). -/
lemma lowerCertificate_nonneg (q : RatContrast K) (nu : CountVec K n → ℚ)
    (hnu : IsRationalPrior nu) : 0 ≤ lowerCertificate q nu := by
  have hK := rationalContrast_admissibleArmCount q
  have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
  letI : Nonempty (Arm K) := Fintype.card_pos_iff.mp (by simpa using hKpos)
  letI : Nonempty (AllocVec K n) :=
    ⟨assignmentCounts (fun _ => Classical.choice inferInstance)⟩
  rw [lowerCertificate_eq_posteriorResidual_sInf q nu hnu]
  apply le_csInf
  · exact Set.range_nonempty _
  · rintro _ ⟨r, rfl⟩
    exact (rationalOrbitModel q).posteriorResidual_nonneg (rationalPriorOf nu hnu) r

-- @node: transferredSchedulePrior_lowerBound
/-- [the population size is positive](hyp:hn), [the stated side condition holds](hyp:hnu), [the transferred schedule prior lower bound property holds](goal). -/
lemma transferredSchedulePrior_lowerBound
    (c : Contrast ℝ K) (q : RatContrast K) (hn : 0 < n)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu)
    (p : Procedure K n c) :
    (max 0 (Real.sqrt (lowerCertificate q nu) -
      contrastDistance c (ratContrastToReal q))) ^ 2 ≤
      (schedulePriorOfRationalPrior nu hnu).E (fun z => labeledRisk c p z) := by
  let prior := schedulePriorOfRationalPrior nu hnu
  let eta := contrastDistance c (ratContrastToReal q)
  let V := prior.E (fun z => labeledRisk c p z)
  have heta : 0 ≤ eta := by unfold eta contrastDistance; positivity
  have hV : 0 ≤ V := prior.E_nonneg (fun z => p.1.mse_nonneg _ _)
  have hroot (z : Schedule K n) :
      Real.sqrt (labeledRisk (ratContrastToReal q)
        (transferProcedure (ratContrastToReal q) p) z) ≤
        Real.sqrt (labeledRisk c p z) + eta := by
    have hsymm : contrastDistance (ratContrastToReal q) c = eta := by
      unfold eta contrastDistance
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact abs_sub_comm _ _
    simpa [hsymm] using transferred_root_risk_le
      (ratContrastToReal q) c p z hn
  have hpoint (z : Schedule K n) :
      labeledRisk (ratContrastToReal q)
          (transferProcedure (ratContrastToReal q) p) z ≤
        labeledRisk c p z + 2 * eta * Real.sqrt (labeledRisk c p z) + eta ^ 2 := by
    have hc0 : 0 ≤ labeledRisk c p z := p.1.mse_nonneg _ _
    have hq0 : 0 ≤ labeledRisk (ratContrastToReal q)
        (transferProcedure (ratContrastToReal q) p) z :=
      (transferProcedure (ratContrastToReal q) p).1.mse_nonneg _ _
    have hsqc := Real.sq_sqrt hc0
    have hsqq := Real.sq_sqrt hq0
    nlinarith [hroot z, Real.sqrt_nonneg (labeledRisk c p z),
      Real.sqrt_nonneg (labeledRisk (ratContrastToReal q)
        (transferProcedure (ratContrastToReal q) p) z)]
  have hsqrtE : prior.E (fun z => Real.sqrt (labeledRisk c p z)) ≤ Real.sqrt V := by
    have hcs := finiteDesign_E_abs_le_sqrt_E_sq prior
      (fun z => Real.sqrt (labeledRisk c p z))
    have habs (z : Schedule K n) :
        |Real.sqrt (labeledRisk c p z)| = Real.sqrt (labeledRisk c p z) :=
      abs_of_nonneg (Real.sqrt_nonneg _)
    rw [show prior.E (fun z => Real.sqrt (labeledRisk c p z) ^ 2) = V by
      apply prior.E_congr
      intro z
      exact Real.sq_sqrt (p.1.mse_nonneg _ _)] at hcs
    simpa only [habs] using hcs
  have htransfer : prior.E (fun z => labeledRisk (ratContrastToReal q)
      (transferProcedure (ratContrastToReal q) p) z) ≤
      (Real.sqrt V + eta) ^ 2 := by
    calc
      _ ≤ prior.E (fun z => labeledRisk c p z +
          2 * eta * Real.sqrt (labeledRisk c p z) + eta ^ 2) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hpoint z) (prior.p_nonneg z)
      _ = V + 2 * eta * prior.E (fun z => Real.sqrt (labeledRisk c p z)) +
          eta ^ 2 := by
        rw [prior.E_add, prior.E_add, prior.E_const_mul, prior.E_const]
      _ ≤ V + 2 * eta * Real.sqrt V + eta ^ 2 := by gcongr
      _ = (Real.sqrt V + eta) ^ 2 := by
        nlinarith [Real.sq_sqrt hV]
  have hB : lowerCertificate q nu ≤ (Real.sqrt V + eta) ^ 2 :=
    (lowerCertificate_le_schedulePriorRisk q hn nu hnu
      (transferProcedure (ratContrastToReal q) p)).trans htransfer
  by_cases hB0 : lowerCertificate q nu ≤ 0
  · have hsqrt : Real.sqrt (lowerCertificate q nu) = 0 := Real.sqrt_eq_zero_of_nonpos hB0
    change (max 0 (Real.sqrt (lowerCertificate q nu) - eta)) ^ 2 ≤ V
    rw [hsqrt]
    simp [heta, hV]
  · have hBpos : 0 < lowerCertificate q nu := lt_of_not_ge hB0
    have hsqrt_le : Real.sqrt (lowerCertificate q nu) ≤ Real.sqrt V + eta := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · simpa [Real.sq_sqrt hBpos.le] using hB
    by_cases hsub : Real.sqrt (lowerCertificate q nu) - eta ≤ 0
    · change (max 0 (Real.sqrt (lowerCertificate q nu) - eta)) ^ 2 ≤ V
      rw [max_eq_left hsub]
      simpa using hV
    · rw [max_eq_right (le_of_not_ge hsub)]
      change (Real.sqrt (lowerCertificate q nu) - eta) ^ 2 ≤ V
      nlinarith [Real.sq_sqrt hV]

-- @node: projectedUpperProcedureCertificate
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the delta condition holds](hyp:delta), [the stated side condition holds](hyp:hcert), [the stated side condition holds](hyp:hbar), [the projected upper procedure certificate property holds](goal). -/
lemma projectedUpperProcedureCertificate
    (c : Contrast ℝ K) (q : RatContrast K) (hn : 0 < n) (hM : 0 < M)
    (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
    (nu : CountVec K n → ℚ)
    (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
    (hcert : ExactGridPrimalDualCertificate q pi w u nu)
    (hbar : IsGridBarycenter q pi w delta) :
    ∃ p : Procedure K n c,
      IsProjectedUpperProcedureCertificate K n c pi delta p
        ((Real.sqrt (upperCertificate q pi delta) +
          contrastDistance c (ratContrastToReal q)) ^ 2) := by
  classical
  rcases hcert with ⟨wQ, y, hw, hpr, hy, hnu, hu⟩
  subst w
  let piD := rationalGridDesignOf pi hpr.2.2.1 hpr.1
  let wR : GridWeight K n M := rationalGridWeightToReal M wQ
  have hwR : ∀ r x g, 0 ≤ wR r x g := by
    intro r x g
    dsimp [wR, rationalGridWeightToReal]
    exact_mod_cast hpr.2.2.2.1 r x g
  have hocc : ∀ r x, ∑ g, wR r x g = piD.p r := by
    intro r x
    dsimp [wR, piD, rationalGridDesignOf, rationalGridWeightToReal]
    exact_mod_cast hpr.2.1 r x
  have hzero : (0 : ℝ) ∈ Set.Icc
      (-Lc (ratContrastToReal q) / 2) (Lc (ratContrastToReal q) / 2) := by
    have hL := Lc_pos (ratContrastToReal q)
    constructor <;> linarith
  have hgamma (g : Fin (2 * M + 1)) : (gammaMC M q g : ℝ) ∈
      Set.Icc (-Lc (ratContrastToReal q) / 2) (Lc (ratContrastToReal q) / 2) := by
    simpa [hRat_cast, neg_div] using gammaMC_mem_gridInterval q hM g
  let qoFS :=
    Causalean.Stat.Minimax.FiniteSquaredLoss.barycenterProcedure
      piD wR (fun g => (gammaMC M q g : ℝ)) 0 hwR hocc hzero hgamma
  let qo : OrbitProcedure K n (ratContrastToReal q) :=
    (qoFS.design, qoFS.decision)
  have hdelta (r : AllocVec K n) (x : ObsVec r) :
      delta r x = (qo.2 r x : ℝ) := by
    change delta r x = (qoFS.decision r x : ℝ)
    change delta r x =
      Causalean.Stat.Minimax.FiniteSquaredLoss.conditionalBarycenter
        piD wR (fun g => (gammaMC M q g : ℝ)) 0 r x
    simpa [piD, wR] using gridBarycenter_eq_conditionalBarycenter
      q pi (rationalGridWeightToReal M wQ) delta hpr.2.2.1 hpr.1 hbar r x
  let pRat : Procedure K n (ratContrastToReal q) :=
    (orbitToInvariantProcedure (ratContrastToReal q) qo).1
  let p : Procedure K n c := transferProcedure c pRat
  refine ⟨p, ?_, ?_, ?_⟩
  · intro A
    change pRat.1.p A = (pi (assignmentCounts A) : ℝ) /
      allocationOrbitCard (assignmentCounts A)
    rw [(orbitToInvariantProcedure_realizes (ratContrastToReal q) qo).1 A]
    change piD.p (assignmentCounts A) / allocationOrbitCard (assignmentCounts A) = _
    rfl
  · intro A obs
    change clip c (pRat.2 A obs) = clip c (delta (assignmentCounts A)
      (observedCounts A obs))
    congr 1
    rw [(orbitToInvariantProcedure_realizes (ratContrastToReal q) qo).2 A obs]
    exact (hdelta _ _).symm
  · apply Causalean.Stat.worstCaseRisk_le
    intro z
    have hriskEq : labeledRisk (ratContrastToReal q) pRat z =
        orbitRisk (ratContrastToReal q) qo (scheduleCounts z) :=
      labeledRisk_eq_orbitRisk_of_realizes (ratContrastToReal q) pRat qo
        (orbitToInvariantProcedure_realizes (ratContrastToReal q) qo).1
        (orbitToInvariantProcedure_realizes (ratContrastToReal q) qo).2 z
    have horbit : orbitRisk (ratContrastToReal q) qo (scheduleCounts z) ≤
        upperCertificate q pi delta := by
      unfold upperCertificate
      have hle := le_ciSup (Set.finite_range (fun m : CountVec K n =>
        ∑ r, (pi r : ℝ) * ∑ x : ObsVec r,
          (orbitLik m r x : ℝ) *
            (delta r x - (tauCountRat q m : ℝ)) ^ 2)).bddAbove (scheduleCounts z)
      apply le_trans ?_ hle
      unfold orbitRisk
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro r _
      change (pi r : ℝ) *
          (∑ x, (orbitLik (scheduleCounts z) r x : ℝ) *
            ((qo.2 r x : ℝ) - tauCount (ratContrastToReal q) (scheduleCounts z)) ^ 2) = _
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [← hdelta, tauCountRat_cast]
    have hroot := transferred_root_risk_le c (ratContrastToReal q) pRat z hn
    have hrat0 : 0 ≤ labeledRisk (ratContrastToReal q) pRat z := pRat.1.mse_nonneg _ _
    have hriskRat : labeledRisk (ratContrastToReal q) pRat z ≤
        upperCertificate q pi delta := by rw [hriskEq]; exact horbit
    have hU0 : 0 ≤ upperCertificate q pi delta := hrat0.trans hriskRat
    have hsqrt : Real.sqrt (labeledRisk c p z) ≤
        Real.sqrt (upperCertificate q pi delta) +
          contrastDistance c (ratContrastToReal q) := by
      calc
        _ ≤ Real.sqrt (labeledRisk (ratContrastToReal q) pRat z) +
            contrastDistance c (ratContrastToReal q) := hroot
        _ ≤ Real.sqrt (upperCertificate q pi delta) +
            contrastDistance c (ratContrastToReal q) := by
          gcongr
    have hc0 : 0 ≤ labeledRisk c p z := p.1.mse_nonneg _ _
    nlinarith [Real.sq_sqrt hc0, Real.sq_sqrt hU0,
      Real.sqrt_nonneg (labeledRisk c p z),
      Real.sqrt_nonneg (upperCertificate q pi delta)]

/-- The schedule prior is exactly the uniform-within-orbit lift of the same
upstream rational response-count prior `nu`, and gives the all-procedure bound. -/
def IsTransferredPriorCertificate (K n : ℕ) (c : Contrast ℝ K)
    (nu : CountVec K n → ℚ)
    (prior : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule K n))
    (Rminus : ℝ) : Prop :=
  (∀ z, prior.p z = (nu (scheduleCounts z) : ℝ) /
    responseCountOrbitCard (scheduleCounts z)) ∧
  ∀ p : Procedure K n c, Rminus ≤ prior.E (fun z => labeledRisk c p z)

/-- One exact rational program together with its transferred real-contrast endpoints. -/
def RealContrastTransferCertificate (K n M : ℕ) (c : Contrast ℝ K)
    (q : RatContrast K) (B U Rminus Rplus : ℝ) : Prop :=
  ∃ (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
      (nu : CountVec K n → ℚ)
      (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
      (upperProcedure : Procedure K n c)
      (schedulePrior : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule K n)),
    ExactGridPrimalDualCertificate q pi w u nu ∧
    IsGridBarycenter q pi w delta ∧
    B = lowerCertificate q nu ∧ U = upperCertificate q pi delta ∧
    (u : ℝ) = gridLPValueRaw K n M q ∧
    lowerCertificate q nu ≤ rhoN K n (ratContrastToReal q) ∧
    rhoN K n (ratContrastToReal q) ≤ upperCertificate q pi delta ∧
    upperCertificate q pi delta ≤ (u : ℝ) ∧
    (u : ℝ) ≤ lowerCertificate q nu +
      C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) ∧
    Rminus = (max 0 (Real.sqrt B - contrastDistance c (ratContrastToReal q))) ^ 2 ∧
    Rplus = (Real.sqrt U + contrastDistance c (ratContrastToReal q)) ^ 2 ∧
    Rminus ≤ rhoN K n c ∧ rhoN K n c ≤ Rplus ∧
    Rplus - Rminus ≤
      5 * C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
      4 * Real.sqrt (C0 (ratContrastToReal q)) *
        contrastDistance c (ratContrastToReal q) * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
      3 * contrastDistance c (ratContrastToReal q) ^ 2 ∧
    IsProjectedUpperProcedureCertificate K n c pi delta upperProcedure Rplus ∧
    IsTransferredPriorCertificate K n c nu schedulePrior Rminus

-- @node: fixedRealContrastTransferCertificate
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the fixed real contrast transfer certificate property holds](goal). -/
lemma fixedRealContrastTransferCertificate
    (K n M : ℕ) (c : Contrast ℝ K) (q : RatContrast K)
    (hn : 0 < n) (hM : 0 < M) :
    ∃ B U Rminus Rplus : ℝ,
      RealContrastTransferCertificate K n M c q B U Rminus Rplus := by
  classical
  obtain ⟨pi, w, u, nu, delta, hcert, hbar, hu, hBρ, hρU, hUu, huB,
      _hcM, _hcR, _hcRX, _hasymp⟩ :=
    rational_contrast_grid_certificate_sandwich K n M q hn hM
  have hnu : IsRationalPrior nu := by
    rcases hcert with ⟨wQ, y, hw, hpr, hy, hnu, huy⟩
    rw [hnu]
    exact ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩
  let B := lowerCertificate q nu
  let U := upperCertificate q pi delta
  let eta := contrastDistance c (ratContrastToReal q)
  let Rminus := (max 0 (Real.sqrt B - eta)) ^ 2
  let Rplus := (Real.sqrt U + eta) ^ 2
  obtain ⟨upperProcedure, hupper⟩ :=
    projectedUpperProcedureCertificate c q hn hM pi w u nu delta hcert hbar
  let prior := schedulePriorOfRationalPrior nu hnu
  have hlowerAll : ∀ p : Procedure K n c,
      Rminus ≤ prior.E (fun z => labeledRisk c p z) := by
    intro p
    exact transferredSchedulePrior_lowerBound c q hn nu hnu p
  have hRminus : Rminus ≤ rhoN K n c := by
    letI : Nonempty (Procedure K n c) := ⟨upperProcedure⟩
    unfold rhoN
    apply Causalean.Stat.le_minimaxValue
    intro p
    calc
      Rminus ≤ prior.E (fun z => labeledRisk c p z) := hlowerAll p
      _ ≤ Causalean.Stat.worstCaseRisk
          (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z) p := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        calc
          _ ≤ ∑ z, prior.p z * Causalean.Stat.worstCaseRisk
              (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z) p := by
            apply Finset.sum_le_sum
            intro z _
            apply mul_le_mul_of_nonneg_left
            · exact Causalean.Stat.le_worstCaseRisk (Set.finite_range _).bddAbove z
            · exact prior.p_nonneg z
          _ = _ := by rw [← Finset.sum_mul, prior.p_sum, one_mul]
  have hRplus : rhoN K n c ≤ Rplus :=
    (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun p z => p.1.mse_nonneg _ _) upperProcedure).trans hupper.2.2
  have hB0 : 0 ≤ B := lowerCertificate_nonneg q nu hnu
  have hU0 : 0 ≤ U := hB0.trans (hBρ.trans hρU)
  have heta0 : 0 ≤ eta := by unfold eta contrastDistance; positivity
  have hC0 : 0 ≤ C0 (ratContrastToReal q) := by unfold C0; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρbound := (embedded_two_arm_converse K n (ratContrastToReal q)
    (rationalContrast_admissibleArmCount q) hn).2.1
  have hgap : U - B ≤ C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) := by
    dsimp [U, B]
    linarith
  have hsqrtU : Real.sqrt U ≤
      Real.sqrt (C0 (ratContrastToReal q)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
      Real.sqrt (C0 (ratContrastToReal q)) / (2 * M) := by
    let a := Real.sqrt (C0 (ratContrastToReal q)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
    let b := Real.sqrt (C0 (ratContrastToReal q)) / (2 * M)
    have hUbd : U ≤ C0 (ratContrastToReal q) / n +
        C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) := by linarith
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hb0 : 0 ≤ b := by dsimp [b]; positivity
    have haSq : a ^ 2 = C0 (ratContrastToReal q) / n := by
      dsimp [a]
      rw [mul_pow, Real.sq_sqrt hC0]
      have hp : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hnR.le]
        norm_num
        exact Real.rpow_neg_one _
      rw [hp, div_eq_mul_inv]
    have hbSq : b ^ 2 = C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) := by
      dsimp [b]
      rw [div_pow, Real.sq_sqrt hC0]
      ring
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · rw [add_sq, haSq, hbSq]
      nlinarith
  have hwidth : Rplus - Rminus ≤
      5 * C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
      4 * Real.sqrt (C0 (ratContrastToReal q)) * eta *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) + 3 * eta ^ 2 := by
    have hsB := Real.sq_sqrt hB0
    have hsU := Real.sq_sqrt hU0
    have hmax : B - (max 0 (Real.sqrt B - eta)) ^ 2 ≤
        2 * eta * Real.sqrt B + eta ^ 2 := by
      by_cases h : Real.sqrt B - eta ≤ 0
      · rw [max_eq_left h]
        nlinarith [Real.sqrt_nonneg B]
      · rw [max_eq_right (le_of_not_ge h)]
        nlinarith
    have hsqrtB : Real.sqrt B ≤ Real.sqrt U := Real.sqrt_le_sqrt (hBρ.trans hρU)
    have hsqrtC : (Real.sqrt (C0 (ratContrastToReal q))) ^ 2 =
        C0 (ratContrastToReal q) := Real.sq_sqrt hC0
    have hcross : 2 * Real.sqrt (C0 (ratContrastToReal q)) * eta / M ≤
        C0 (ratContrastToReal q) / (M : ℝ) ^ 2 + eta ^ 2 := by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      have hsq := sq_nonneg (Real.sqrt (C0 (ratContrastToReal q)) / M - eta)
      have hdivsq : (Real.sqrt (C0 (ratContrastToReal q)) / M) ^ 2 =
          C0 (ratContrastToReal q) / (M : ℝ) ^ 2 := by
        rw [div_pow, hsqrtC]
      rw [show (Real.sqrt (C0 (ratContrastToReal q)) / M - eta) ^ 2 =
          (Real.sqrt (C0 (ratContrastToReal q)) / M) ^ 2 -
            2 * (Real.sqrt (C0 (ratContrastToReal q)) / M) * eta + eta ^ 2 by ring,
        hdivsq] at hsq
      have hxy : 2 * (Real.sqrt (C0 (ratContrastToReal q)) / M) * eta ≤
          (Real.sqrt (C0 (ratContrastToReal q)) / M) ^ 2 + eta ^ 2 := by
        nlinarith
      calc
        _ = 2 * (Real.sqrt (C0 (ratContrastToReal q)) / M) * eta := by ring
        _ ≤ (Real.sqrt (C0 (ratContrastToReal q)) / M) ^ 2 + eta ^ 2 := hxy
        _ = _ := by rw [hdivsq]
    dsimp [Rplus, Rminus]
    have hpre : (Real.sqrt U + eta) ^ 2 -
        (max 0 (Real.sqrt B - eta)) ^ 2 ≤
        C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
        4 * eta * Real.sqrt U + 2 * eta ^ 2 := by nlinarith
    have hrootTerm : 4 * eta * Real.sqrt U ≤
        4 * Real.sqrt (C0 (ratContrastToReal q)) * eta *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        2 * Real.sqrt (C0 (ratContrastToReal q)) * eta / M := by
      have h4eta : 0 ≤ 4 * eta := mul_nonneg (by norm_num) heta0
      have hm := mul_le_mul_of_nonneg_left hsqrtU h4eta
      calc
        _ ≤ 4 * eta * (Real.sqrt (C0 (ratContrastToReal q)) *
            (n : ℝ) ^ (-(1 / 2 : ℝ)) +
            Real.sqrt (C0 (ratContrastToReal q)) / (2 * M)) := hm
        _ = _ := by ring
    have hcoef : C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
        C0 (ratContrastToReal q) / (M : ℝ) ^ 2 =
        5 * C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) := by
      field_simp
      ring
    calc
      _ ≤ C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
          4 * eta * Real.sqrt U + 2 * eta ^ 2 := hpre
      _ ≤ C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
          (4 * Real.sqrt (C0 (ratContrastToReal q)) * eta *
            (n : ℝ) ^ (-(1 / 2 : ℝ)) +
           2 * Real.sqrt (C0 (ratContrastToReal q)) * eta / M) +
          2 * eta ^ 2 := by linarith
      _ ≤ _ := by linarith [hcross, hcoef]
  refine ⟨B, U, Rminus, Rplus, pi, w, u, nu, delta, upperProcedure, prior,
    hcert, hbar, rfl, rfl, ?_, hBρ, hρU, ?_, ?_, rfl, rfl,
    hRminus, hRplus, hwidth, hupper, ?_⟩
  · simpa [gridLPValue] using hu
  · exact hUu.trans_eq hu.symm
  · exact hu ▸ huB
  · exact ⟨fun z => rfl, hlowerAll⟩

-- @node: realContrastTransferCertificate_bounds
/-- [the real contrast transfer certificate bounds property holds](goal). -/
lemma realContrastTransferCertificate_bounds
    (K n M : ℕ) (c : Contrast ℝ K) (q : RatContrast K)
    (B U Rminus Rplus : ℝ)
    (h : RealContrastTransferCertificate K n M c q B U Rminus Rplus) :
    0 ≤ Rplus - Rminus ∧
    Rplus - Rminus ≤
      5 * C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) +
      4 * Real.sqrt (C0 (ratContrastToReal q)) *
        contrastDistance c (ratContrastToReal q) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) +
      3 * contrastDistance c (ratContrastToReal q) ^ 2 ∧
    U - B ≤ C0 (ratContrastToReal q) / (4 * (M : ℝ) ^ 2) := by
  rcases h with ⟨pi, w, u, nu, delta, p, prior, _hcert, _hbar,
    hB, hU, _huval, _hBρ, _hρU, hUu, huB, _hRmDef, _hRpDef,
    hRm, hRp, hwidth, _hp, _hprior⟩
  refine ⟨by linarith, hwidth, ?_⟩
  rw [hU, hB]
  linarith

-- @node: thm:real-contrast-grid-certificate-transfer
/-- [there are at least two treatment arms](hyp:hK), [exact rational grid certificates transfer to every real contrast with the stated approximation error bounds](goal). -/
theorem real_contrast_grid_certificate_transfer
    (K : ℕ) (c : Contrast ℝ K) (hK : AdmissibleArmCount K) :
    (∀ (q : RatContrast K) (n M : ℕ), 0 < n → 0 < M →
      ∃ B U Rminus Rplus : ℝ,
        RealContrastTransferCertificate K n M c q B U Rminus Rplus) ∧
    (∃ (cq : ℕ → RatContrast K) (B U Rminus Rplus : ℕ → ℝ),
      (∀ a, Tendsto (fun n => ratContrastToReal (cq n) a) atTop (nhds (c a))) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (5 / 6 : ℝ) *
        contrastDistance c (ratContrastToReal (cq n))) atTop (nhds 0) ∧
      (∀ n, 0 < n →
        RealContrastTransferCertificate K n n c (cq n)
          (B n) (U n) (Rminus n) (Rplus n)) ∧
      Tendsto (fun n => secondOrderScale n * (Rplus n - Rminus n)) atTop (nhds 0)) ∧
    (∀ q : RatContrast K, ratContrastToReal q = c →
      ∀ n, 0 < n →
        ∃ B U Rminus Rplus : ℝ,
          RealContrastTransferCertificate K n n c q B U Rminus Rplus ∧
          U - B ≤ C0 c / (4 * (n : ℝ) ^ 2)) := by
  classical
  have hLc : 0 < Lc c := Lc_pos c
  let eps : ℕ → ℝ := fun n =>
    if n = 0 then Lc c / 4
    else min (Lc c / 4) ((n : ℝ) ^ (-3 : ℝ))
  have hepspos (n : ℕ) : 0 < eps n := by
    dsimp [eps]
    split_ifs with hn
    · positivity
    · apply lt_min
      · positivity
      · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  have hepslt (n : ℕ) : eps n < Lc c / 2 := by
    calc
      eps n ≤ Lc c / 4 := by
        dsimp [eps]
        split_ifs <;> simp
      _ < Lc c / 2 := by linarith
  choose cq hcq using fun n =>
    exists_ratContrast_close K c hK (eps n) (hepspos n) (hepslt n)
  have hdistPow : ∀ᶠ n : ℕ in atTop,
      contrastDistance c (ratContrastToReal (cq n)) ≤ (n : ℝ) ^ (-3 : ℝ) := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    exact (hcq n).trans (by simp [eps, ne_of_gt hnpos])
  have hpow3 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp
      tendsto_natCast_atTop_atTop
  have hdist0 : Tendsto (fun n =>
      contrastDistance c (ratContrastToReal (cq n))) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow3
    · exact Filter.Eventually.of_forall fun n => by
        unfold contrastDistance
        positivity
    · exact hdistPow
  have hcoord (a : Arm K) : Tendsto
      (fun n => ratContrastToReal (cq n) a) atTop (nhds (c a)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hu : Tendsto (fun n => 2 *
        contrastDistance c (ratContrastToReal (cq n))) atTop (nhds 0) := by
      simpa using hdist0.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · exact Filter.Eventually.of_forall fun n => by
        simpa [Real.dist_eq, abs_sub_comm] using
          coordinate_le_two_contrastDistance c (ratContrastToReal (cq n)) a
  have hetaScaled : Tendsto (fun n : ℕ => (n : ℝ) ^ (5 / 6 : ℝ) *
      contrastDistance c (ratContrastToReal (cq n))) atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(13 / 6 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 6)).comp
        tendsto_natCast_atTop_atTop
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
    · filter_upwards [Ici_mem_atTop 1] with n hn
      exact mul_nonneg
        (Real.rpow_nonneg (le_of_lt (by exact_mod_cast hn : (0 : ℝ) < n)) _)
        (by unfold contrastDistance; positivity)
    · filter_upwards [hdistPow, Ici_mem_atTop 1] with n hd hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      calc
        (n : ℝ) ^ (5 / 6 : ℝ) *
            contrastDistance c (ratContrastToReal (cq n)) ≤
            (n : ℝ) ^ (5 / 6 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by gcongr
        _ = (n : ℝ) ^ (-(13 / 6 : ℝ)) := by
          rw [← Real.rpow_add hnR]
          norm_num
  choose Bp Up Rmp Rpp hcertp using fun m : PositiveNat =>
    fixedRealContrastTransferCertificate K m m c (cq m) m.2 m.2
  let B : ℕ → ℝ := fun n => if hn : 0 < n then Bp ⟨n, hn⟩ else 0
  let U : ℕ → ℝ := fun n => if hn : 0 < n then Up ⟨n, hn⟩ else 0
  let Rminus : ℕ → ℝ := fun n => if hn : 0 < n then Rmp ⟨n, hn⟩ else 0
  let Rplus : ℕ → ℝ := fun n => if hn : 0 < n then Rpp ⟨n, hn⟩ else 0
  have hcert (n : ℕ) (hn : 0 < n) :
      RealContrastTransferCertificate K n n c (cq n)
        (B n) (U n) (Rminus n) (Rplus n) := by
    simpa [B, U, Rminus, Rplus, hn] using hcertp ⟨n, hn⟩
  have hLcconv : Tendsto (fun n => Lc (ratContrastToReal (cq n)))
      atTop (nhds (Lc c)) := by
    unfold Lc
    simpa using tendsto_finset_sum Finset.univ (fun a _ => (hcoord a).abs)
  have hCconv : Tendsto (fun n => C0 (ratContrastToReal (cq n)))
      atTop (nhds (C0 c)) := by
    unfold C0
    exact (hLcconv.pow 2).div_const 4
  have hsqrtCconv : Tendsto (fun n => Real.sqrt (C0 (ratContrastToReal (cq n))))
      atTop (nhds (Real.sqrt (C0 c))) := hCconv.sqrt
  have hscale2 : Tendsto (fun n : ℕ => secondOrderScale n / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 / 3 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
        tendsto_natCast_atTop_atTop
    apply hp.congr'
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold secondOrderScale
    calc
      (n : ℝ) ^ (-(2 / 3 : ℝ)) =
          (n : ℝ) ^ (4 / 3 - 2 : ℝ) := by norm_num
      _ = (n : ℝ) ^ (4 / 3 : ℝ) / (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_sub hnR _ _
      _ = (n : ℝ) ^ (4 / 3 : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
        congr 1
        exact Real.rpow_natCast _ 2
  have hterm1 : Tendsto (fun n => secondOrderScale n *
      (5 * C0 (ratContrastToReal (cq n)) / (4 * (n : ℝ) ^ 2)))
      atTop (nhds 0) := by
    have h := (hCconv.const_mul (5 / 4 : ℝ)).mul hscale2
    have h0 : Tendsto (fun n => (5 / 4 : ℝ) *
        C0 (ratContrastToReal (cq n)) *
          (secondOrderScale n / (n : ℝ) ^ 2)) atTop (nhds 0) := by
      simpa using h
    convert h0 using 1
    funext n
    ring
  have hterm2 : Tendsto (fun n => secondOrderScale n *
      (4 * Real.sqrt (C0 (ratContrastToReal (cq n))) *
        contrastDistance c (ratContrastToReal (cq n)) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)))) atTop (nhds 0) := by
    have h := (hsqrtCconv.const_mul 4).mul hetaScaled
    have h0 : Tendsto (fun n => 4 * Real.sqrt (C0 (ratContrastToReal (cq n))) *
        ((n : ℝ) ^ (5 / 6 : ℝ) *
          contrastDistance c (ratContrastToReal (cq n)))) atTop (nhds 0) := by
      simpa using h
    apply h0.congr'
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold secondOrderScale
    rw [show (n : ℝ) ^ (4 / 3 : ℝ) *
        (4 * Real.sqrt (C0 (ratContrastToReal (cq n))) *
          contrastDistance c (ratContrastToReal (cq n)) *
            (n : ℝ) ^ (-(1 / 2 : ℝ))) =
        4 * Real.sqrt (C0 (ratContrastToReal (cq n))) *
          ((n : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
            contrastDistance c (ratContrastToReal (cq n))) by ring,
      ← Real.rpow_add hnR]
    norm_num
  have hterm3 : Tendsto (fun n => secondOrderScale n *
      (3 * contrastDistance c (ratContrastToReal (cq n)) ^ 2))
      atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => 3 * (n : ℝ) ^ (-(14 / 3 : ℝ)))
        atTop (nhds 0) := by
      simpa using ((tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 14 / 3)).comp
          tendsto_natCast_atTop_atTop).const_mul 3
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
    · filter_upwards [Ici_mem_atTop 1] with n hn
      exact mul_nonneg (by unfold secondOrderScale; positivity)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    · filter_upwards [hdistPow, Ici_mem_atTop 1] with n hd hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hsquare : contrastDistance c (ratContrastToReal (cq n)) ^ 2 ≤
          ((n : ℝ) ^ (-3 : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by unfold contrastDistance; positivity)
          (Real.rpow_nonneg hnR.le _)).2 hd
      calc
        secondOrderScale n *
            (3 * contrastDistance c (ratContrastToReal (cq n)) ^ 2) ≤
            secondOrderScale n * (3 * ((n : ℝ) ^ (-3 : ℝ)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsquare (by norm_num))
                (by unfold secondOrderScale; positivity)
        _ = 3 * (n : ℝ) ^ (-(14 / 3 : ℝ)) := by
          unfold secondOrderScale
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hnR.le]
          norm_num only [Nat.cast_ofNat]
          rw [show (n : ℝ) ^ (4 / 3 : ℝ) *
              (3 * (n : ℝ) ^ (-6 : ℝ)) =
              3 * ((n : ℝ) ^ (4 / 3 : ℝ) *
                (n : ℝ) ^ (-6 : ℝ)) by ring,
            ← Real.rpow_add hnR]
          norm_num
  have hwidth : Tendsto (fun n => secondOrderScale n *
      (Rplus n - Rminus n)) atTop (nhds 0) := by
    have hup := hterm1.add (hterm2.add hterm3)
    have hup0 : Tendsto (fun n =>
        secondOrderScale n *
            (5 * C0 (ratContrastToReal (cq n)) / (4 * (n : ℝ) ^ 2)) +
          (secondOrderScale n *
              (4 * Real.sqrt (C0 (ratContrastToReal (cq n))) *
                contrastDistance c (ratContrastToReal (cq n)) *
                  (n : ℝ) ^ (-(1 / 2 : ℝ))) +
            secondOrderScale n *
              (3 * contrastDistance c (ratContrastToReal (cq n)) ^ 2)))
        atTop (nhds 0) := by simpa using hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup0
    · filter_upwards [Ici_mem_atTop 1] with n hn
      have hb := (realContrastTransferCertificate_bounds K n n c (cq n)
        (B n) (U n) (Rminus n) (Rplus n) (hcert n hn)).1
      exact mul_nonneg (by unfold secondOrderScale; positivity) hb
    · filter_upwards [Ici_mem_atTop 1] with n hn
      have hb := (realContrastTransferCertificate_bounds K n n c (cq n)
        (B n) (U n) (Rminus n) (Rplus n) (hcert n hn)).2.1
      have hs : 0 ≤ secondOrderScale n := by unfold secondOrderScale; positivity
      have := mul_le_mul_of_nonneg_left hb hs
      linarith
  refine ⟨?_, ⟨cq, B, U, Rminus, Rplus, hcoord, hetaScaled, hcert, hwidth⟩, ?_⟩
  · intro q n M hn hM
    exact fixedRealContrastTransferCertificate K n M c q hn hM
  · intro q hq n hn
    obtain ⟨B, U, Rminus, Rplus, hcert⟩ :=
      fixedRealContrastTransferCertificate K n n c q hn hn
    refine ⟨B, U, Rminus, Rplus, hcert, ?_⟩
    have hgap := (realContrastTransferCertificate_bounds K n n c q
      B U Rminus Rplus hcert).2.2
    simpa [hq] using hgap

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
