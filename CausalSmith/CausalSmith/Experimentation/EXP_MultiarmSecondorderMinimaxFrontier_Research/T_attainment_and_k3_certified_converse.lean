import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_exact_response_type_game
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_universal_second_order_rate
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_real_contrast_grid_certificate_transfer
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_k3_grid_certificate_sandwich

/-! Capstone: exact support-two saddle, universal order attainment, and certificates. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: schedulePriorOfCountPrior
/-- A prior on response-type counts induces a prior on labeled schedules by spreading each count-vector mass uniformly over its schedule orbit. -/
noncomputable def schedulePriorOfCountPrior
    (nu : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n)) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Schedule K n) where
  p z := nu.p (scheduleCounts z) / responseCountOrbitCard (scheduleCounts z)
  p_nonneg z := div_nonneg (nu.p_nonneg _) (Nat.cast_nonneg _)
  p_sum := by
    classical
    rw [← Finset.sum_fiberwise Finset.univ scheduleCounts
      (fun z => nu.p (scheduleCounts z) /
        responseCountOrbitCard (scheduleCounts z))]
    calc
      ∑ m : CountVec K n,
          ∑ z : Schedule K n with scheduleCounts z = m,
            nu.p (scheduleCounts z) / responseCountOrbitCard (scheduleCounts z) =
          ∑ m : CountVec K n, nu.p m := by
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
      _ = 1 := nu.p_sum

-- @node: schedulePriorOfCountPrior_E_count
/-- [the schedule prior when count prior e count property holds](goal). -/
lemma schedulePriorOfCountPrior_E_count
    (nu : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n))
    (f : CountVec K n → ℝ) :
    (schedulePriorOfCountPrior nu).E (fun z => f (scheduleCounts z)) = nu.E f := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [← Finset.sum_fiberwise Finset.univ scheduleCounts
    (fun z => (schedulePriorOfCountPrior nu).p z * f (scheduleCounts z))]
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = ∑ _z : Schedule K n with scheduleCounts _z = m,
        (nu.p m / responseCountOrbitCard m) * f m := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.mem_filter] at hz
      simp [schedulePriorOfCountPrior, hz.2]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      letI := Fintype.ofFinite {z : Schedule K n // scheduleCounts z = m}
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        responseCountFiber_card]
      have hm : (responseCountOrbitCard m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (responseCountOrbitCard_pos m))
      field_simp

-- @node: schedulePriorOfCountPrior_E_permute
/-- [the schedule prior when count prior e permute property holds](goal). -/
lemma schedulePriorOfCountPrior_E_permute
    (nu : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n))
    (sigma : Equiv.Perm (Unit n)) (f : Schedule K n → ℝ) :
    (schedulePriorOfCountPrior nu).E (fun z => f (permuteSchedule sigma z)) =
      (schedulePriorOfCountPrior nu).E f := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  let e : Equiv.Perm (Schedule K n) :=
    { toFun := permuteSchedule sigma
      invFun := permuteSchedule sigma.symm
      left_inv := by intro z; funext i; simp [permuteSchedule]
      right_inv := by intro z; funext i; simp [permuteSchedule] }
  have hsum := Equiv.sum_comp e (fun z =>
    (schedulePriorOfCountPrior nu).p z * f z)
  dsimp [e] at hsum
  simpa only [e, schedulePriorOfCountPrior, scheduleCounts_permute_eq] using hsum

-- @node: orbitSaddle_labeledBayesLower
/-- [the stated side condition holds](hyp:hlower), [the orbit saddle labeled bayes lower property holds](goal). -/
lemma orbitSaddle_labeledBayesLower
    (nu : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n))
    (hlower : ∀ q, orbitGameValue K n c ≤ nu.E (fun m => orbitRisk c q m))
    (p : Procedure K n c) :
    orbitGameValue K n c ≤
      (schedulePriorOfCountPrior nu).E (fun z => labeledRisk c p z) := by
  classical
  letI : Fintype (Equiv.Perm (Unit n)) := Fintype.ofFinite _
  obtain ⟨pbar, q, _hinv, _havg, _hpbar, hdom⟩ := lossless_symmetrization c p
  calc
    orbitGameValue K n c ≤ nu.E (fun m => orbitRisk c q m) := hlower q
    _ = (schedulePriorOfCountPrior nu).E
        (fun z => orbitRisk c q (scheduleCounts z)) := by
      symm
      exact schedulePriorOfCountPrior_E_count nu _
    _ ≤ (schedulePriorOfCountPrior nu).E (fun z =>
        (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
          ∑ sigma : Equiv.Perm (Unit n),
            labeledRisk c p (permuteSchedule sigma z)) := by
      unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hdom z)
        ((schedulePriorOfCountPrior nu).p_nonneg z)
    _ = (schedulePriorOfCountPrior nu).E (fun z => labeledRisk c p z) := by
      rw [(schedulePriorOfCountPrior nu).E_const_mul]
      rw [(schedulePriorOfCountPrior nu).E_sum]
      rw [Finset.sum_congr rfl (fun sigma _ =>
        schedulePriorOfCountPrior_E_permute nu sigma (fun z => labeledRisk c p z))]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Equiv.Perm (Unit n)) : ℝ) ≠ 0 := by positivity
      field_simp

-- keep: public nonassertive payload preserving the frozen theorem's delivery-scope clauses.
/-- The attainment and three-arm certified converse scope property holds. -/
def attainmentAndK3CertifiedConverseScope : List String :=
  ["the internal finite two-arm saddle does not specify the published scalar posterior mean or least-favorable prior",
   "the exact-rational calculations through n=5 are a finite three-arm showcase and do not infer a cross-n limit",
   "for support of size at least three, convergence of the normalized improvement is not determined",
   "for support of size at least three, the sharp second-order constant is not determined",
   "sharp second-order optimality of qStar is not determined",
   "convergence of finite-program optimizers or priors is not determined",
   "no analytic limiting feedback rule is determined",
   "no limiting Hamilton--Jacobi--Bellman, spectral, separable, or other operator is determined"]

-- @node: thm:attainment-and-k3-certified-converse
/-- [there are at least two treatment arms](hyp:hK), [the orbit game attains its saddle value, the universal second-order rate is achieved, and the certified three-arm converse establishes the stated strict separation](goal). -/
theorem attainment_and_k3_certified_converse
    (K : ℕ) (c : Contrast ℝ K) (hK : AdmissibleArmCount K) :
    let _deliveryScope : List String := attainmentAndK3CertifiedConverseScope
    (∀ n, 0 < n → (Sc c).card = 2 →
      rhoN K n c = C0 c * rho2 n ∧
      ∃ (q2 : OrbitProcedure 2 n twoArmContrast)
        (nu2 : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec 2 n))
        (p2 : Procedure 2 n twoArmContrast)
        (prior2 : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n))
        (pK : Procedure K n c)
        (priorK : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule K n)),
        (∀ m, orbitRisk twoArmContrast q2 m ≤ orbitGameValue 2 n twoArmContrast) ∧
        (∀ q2', orbitGameValue 2 n twoArmContrast ≤
          nu2.E (fun m => orbitRisk twoArmContrast q2' m)) ∧
        p2 = (orbitToInvariantProcedure twoArmContrast q2).1 ∧
        (∀ z, prior2.p z = nu2.p (scheduleCounts z) /
          responseCountOrbitCard (scheduleCounts z)) ∧
        pK = liftTwoArmProcedure c p2 ∧
        priorK = prior2.map (embeddedSignSchedule c) ∧
        (∀ z, labeledRisk twoArmContrast p2 z ≤ rho2 n) ∧
        (∀ p2', rho2 n ≤ prior2.E (fun z => labeledRisk twoArmContrast p2' z)) ∧
        (∀ z, labeledRisk c pK z ≤ rhoN K n c) ∧
        (∀ pK', rhoN K n c ≤ priorK.E (fun z => labeledRisk c pK' z))) ∧
    C0 c * kappaC c ≤ liminf (fun n => secondOrderScale n * dN K c n) atTop ∧
    liminf (fun n => secondOrderScale n * dN K c n) atTop ≤
      limsup (fun n => secondOrderScale n * dN K c n) atTop ∧
    limsup (fun n => secondOrderScale n * dN K c n) atTop ≤ 43 * C0 c ∧
    (∃ N : ℕ, ∀ n ≥ N,
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
        (shrinkageProcedure K n c) ≤
          C0 c * ((n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)))) ∧
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
          U - B ≤ C0 c / (4 * (n : ℝ) ^ 2)) ∧
    (∀ n M, 0 < n → 0 < M →
      ∃ (pi : GridPi 3 n) (w : GridWeight 3 n M) (u : ℚ)
        (nu : CountVec 3 n → ℚ)
        (delta : ∀ r : AllocVec 3 n, ObsVec r → ℝ),
        ExactGridPrimalDualCertificate cDaggerQ pi w u nu ∧
        IsGridBarycenter cDaggerQ pi w delta ∧
        lowerCertificate cDaggerQ nu ≤ rhoNDagger n ∧
        rhoNDagger n ≤ upperCertificate cDaggerQ pi delta ∧
        upperCertificate cDaggerQ pi delta ≤
          lowerCertificate cDaggerQ nu + 1 / (4 * (M : ℝ) ^ 2)) := by
  have huniv := universal_second_order_rate K c hK
  rcases huniv with
    ⟨_hlambdaPos, _hlambdaLe, _hkappaPos, _henvelope, ⟨N, _htail, hshrink⟩,
      hliminfLower, hliminfLe, hlimsupUpper, _hregular⟩
  have htransfer := real_contrast_grid_certificate_transfer K c hK
  rcases htransfer with ⟨htransferFinite, htransferAsymptotic, htransferRational⟩
  refine ⟨?_, hliminfLower, hliminfLe, hlimsupUpper, ⟨N, hshrink⟩,
    htransferFinite, htransferAsymptotic, ?_, ?_⟩
  · intro n hn hsupport
    have hembedded := embedded_two_arm_converse K n c hK hn
    have hvalue : rhoN K n c = C0 c * rho2 n := (hembedded.2.2.2 hsupport).1
    refine ⟨hvalue, ?_⟩
    have hK2 : AdmissibleArmCount 2 := by norm_num [AdmissibleArmCount]
    obtain ⟨_hsymm, _hcorr, _htau, horbitValue, q2, nu2, hupper, hlower⟩ :=
      exact_response_type_game 2 n twoArmContrast hK2
    let p2 : Procedure 2 n twoArmContrast :=
      (orbitToInvariantProcedure twoArmContrast q2).1
    let prior2 := schedulePriorOfCountPrior nu2
    let pK : Procedure K n c := liftTwoArmProcedure c p2
    let priorK := prior2.map (embeddedSignSchedule c)
    have horbitRho : orbitGameValue 2 n twoArmContrast = rho2 n := by
      simpa [rho2] using horbitValue.symm
    have hp2upper (z : Schedule 2 n) :
        labeledRisk twoArmContrast p2 z ≤ rho2 n := by
      rw [show labeledRisk twoArmContrast p2 z =
          orbitRisk twoArmContrast q2 (scheduleCounts z) by
        exact labeledRisk_eq_orbitRisk_of_realizes twoArmContrast p2 q2
          ((orbitToInvariantProcedure_realizes twoArmContrast q2).1)
          ((orbitToInvariantProcedure_realizes twoArmContrast q2).2) z]
      rw [← horbitRho]
      exact hupper _
    have hprior2 (p : Procedure 2 n twoArmContrast) :
        rho2 n ≤ prior2.E (fun z => labeledRisk twoArmContrast p z) := by
      rw [← horbitRho]
      exact orbitSaddle_labeledBayesLower nu2 hlower p
    have hpKupper (z : Schedule K n) : labeledRisk c pK z ≤ rhoN K n c := by
      rw [show labeledRisk c pK z = signGroupScale c ^ 2 *
          labeledRisk twoArmContrast p2 (activeSchedule c z) by
        exact liftTwoArmProcedure_statewiseRisk c hsupport p2 z]
      rw [hvalue, ← signGroupScale_sq c]
      exact mul_le_mul_of_nonneg_left (hp2upper _) (sq_nonneg _)
    have hpriorK (p : Procedure K n c) :
        rhoN K n c ≤ priorK.E (fun z => labeledRisk c p z) := by
      have hpoint (z : Schedule 2 n) :
          labeledRisk twoArmContrast (inducedTwoArmProcedure c p) z ≤
            (signGroupScale c)⁻¹ ^ 2 *
              labeledRisk c p (embeddedSignSchedule c z) :=
        inducedTwoArmProcedure_statewiseRisk c p z
      have hE : prior2.E (fun z =>
            labeledRisk twoArmContrast (inducedTwoArmProcedure c p) z) ≤
          (signGroupScale c)⁻¹ ^ 2 *
            priorK.E (fun z => labeledRisk c p z) := by
        calc
          _ ≤ prior2.E (fun z => (signGroupScale c)⁻¹ ^ 2 *
              labeledRisk c p (embeddedSignSchedule c z)) := by
            unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
            apply Finset.sum_le_sum
            intro z _
            exact mul_le_mul_of_nonneg_left (hpoint z) (prior2.p_nonneg z)
          _ = _ := by
            rw [prior2.E_const_mul]
            rw [show priorK.E (fun z => labeledRisk c p z) =
                prior2.E (fun z => labeledRisk c p (embeddedSignSchedule c z)) by
              simp [priorK, prior2, Causalean.Experimentation.DesignBased.FiniteDesign.E_map]]
      have h := (hprior2 (inducedTwoArmProcedure c p)).trans hE
      rw [hvalue, ← signGroupScale_sq c]
      calc
        signGroupScale c ^ 2 * rho2 n ≤
            signGroupScale c ^ 2 * ((signGroupScale c)⁻¹ ^ 2 *
              priorK.E (fun z => labeledRisk c p z)) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = priorK.E (fun z => labeledRisk c p z) := by
          field_simp [(signGroupScale_pos c).ne']
    exact ⟨q2, nu2, p2, prior2, pK, priorK, hupper, hlower, rfl,
      fun _ => rfl, rfl, rfl, hp2upper, hprior2, hpKupper, hpriorK⟩
  · intro q hq n hn
    simpa [hq] using htransferRational q hq n hn
  · intro n M hn hM
    obtain ⟨pi, w, u, nu, delta, hcert, hbary, _hu, hlow, hrho, hupp,
        hlp, _hscale, _hlimit⟩ := k3_grid_certificate_sandwich n M hn hM
    exact ⟨pi, w, u, nu, delta, hcert, hbary, hlow, hrho,
      le_trans hupp hlp⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
