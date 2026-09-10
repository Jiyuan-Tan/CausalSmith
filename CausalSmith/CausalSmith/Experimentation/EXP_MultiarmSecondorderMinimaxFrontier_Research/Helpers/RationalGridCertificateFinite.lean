import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.GridApprox
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.FiniteGame
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.OrbitCounting
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_exact_response_type_game
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_contrast_risk_continuity
import Causalean.Stat.Minimax.FiniteSquaredLoss.PosteriorBarycenter


/-! Finite-sample algebra for exact rational grid certificates. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Filter
open scoped BigOperators
open Finset Set

-- @node: rationalContrast_admissibleArmCount
/-- [the rational contrast admissible arm count property holds](goal). -/
lemma rationalContrast_admissibleArmCount (c : RatContrast K) : AdmissibleArmCount K := by
  unfold AdmissibleArmCount
  by_contra hK
  have hK' : K < 2 := by omega
  interval_cases K
  · apply c.nonzero
    funext a
    exact Fin.elim0 a
  · apply c.nonzero
    funext a
    fin_cases a
    simpa using c.sum_zero

-- @node: tauCountRat_cast
/-- [the tau count rat real-valued identity property holds](goal). -/
lemma tauCountRat_cast (c : RatContrast K) (m : CountVec K n) :
    (tauCountRat c m : ℝ) = tauCount (ratContrastToReal c) m := by
  unfold tauCountRat tauCount ratContrastToReal
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hta : t a = true <;> simp [hta]

-- @node: rationalOrbitModel
/-- The rational orbit model uses exact rational orbit likelihoods, contrast targets, and allocation designs. -/
noncomputable def rationalOrbitModel (c : RatContrast K) :
    Causalean.Stat.Minimax.FiniteSquaredLoss.Model
      (CountVec K n) (AllocVec K n) (fun r => ObsVec r) where
  P m r x := (orbitLik m r x : ℝ)
  P_nonneg m r x := by exact_mod_cast orbitLik_nonneg m r x
  P_sum m r := by exact_mod_cast orbitLik_sum_obs m r
  tau m := tauCount (ratContrastToReal c) m

-- @node: rationalPriorOf
/-- A rational response-count prior is interpreted as a real finite probability design. -/
noncomputable def rationalPriorOf (nu : CountVec K n → ℚ)
    (hnu : IsRationalPrior nu) :
    Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n) where
  p m := (nu m : ℝ)
  p_nonneg m := by exact_mod_cast hnu.1 m
  p_sum := by exact_mod_cast hnu.2

-- @node: rationalGridDesignOf
/-- Rational grid weights induce a real finite design on allocation-count vectors. -/
noncomputable def rationalGridDesignOf (pi : GridPi K n)
    (hpi0 : ∀ r, 0 ≤ pi r) (hpi1 : ∑ r, pi r = 1) :
    Causalean.Experimentation.DesignBased.FiniteDesign (AllocVec K n) where
  p r := (pi r : ℝ)
  p_nonneg r := by exact_mod_cast hpi0 r
  p_sum := by exact_mod_cast hpi1

-- @node: posteriorResidual_eq_secondMoment_sub
variable {Theta B : Type*} [Fintype Theta] [Fintype B]
  {X : B → Type*} [∀ b, Fintype (X b)]

/-- [the posterior residual equals second moment sub](goal). -/
lemma posteriorResidual_eq_secondMoment_sub
    (Mdl : Causalean.Stat.Minimax.FiniteSquaredLoss.Model Theta B X)
    (prior : Causalean.Experimentation.DesignBased.FiniteDesign Theta) (b : B) :
    Mdl.posteriorResidual prior b =
      (∑ theta, prior.p theta * Mdl.tau theta ^ 2) -
        ∑ x, if Mdl.predictiveMass prior b x = 0 then 0
          else Mdl.predictiveTarget prior b x ^ 2 /
            Mdl.predictiveMass prior b x := by
  classical
  unfold Causalean.Stat.Minimax.FiniteSquaredLoss.Model.posteriorResidual
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  calc
    (∑ x, ∑ theta, prior.p theta * Mdl.P theta b x *
        (Mdl.posteriorMean prior b x - Mdl.tau theta) ^ 2) =
        ∑ x, ((∑ theta, prior.p theta * Mdl.P theta b x * Mdl.tau theta ^ 2) -
          if Mdl.predictiveMass prior b x = 0 then 0
          else Mdl.predictiveTarget prior b x ^ 2 /
            Mdl.predictiveMass prior b x) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Mdl.predictiveMass prior b x = 0
      · rw [if_pos hx]
        have hjoint := Mdl.joint_eq_zero_of_predictiveMass_eq_zero prior hx
        simp only [Causalean.Stat.Minimax.FiniteSquaredLoss.Model.posteriorMean, hx,
          if_pos, zero_sub]
        simp_rw [hjoint]
        simp
      · rw [if_neg hx, Causalean.Stat.Minimax.FiniteSquaredLoss.Model.posteriorMean,
          if_neg hx]
        let D := Mdl.predictiveMass prior b x
        let N := Mdl.predictiveTarget prior b x
        let Q := ∑ theta, prior.p theta * Mdl.P theta b x * Mdl.tau theta ^ 2
        have hD : D ≠ 0 := hx
        have hsumD : (∑ theta, prior.p theta * Mdl.P theta b x) = D := rfl
        have hsumN : (∑ theta, prior.p theta * Mdl.P theta b x * Mdl.tau theta) = N := rfl
        change (∑ theta, prior.p theta * Mdl.P theta b x *
          (N / D - Mdl.tau theta) ^ 2) = Q - N ^ 2 / D
        calc
          _ = ∑ theta, (prior.p theta * Mdl.P theta b x * (N / D) ^ 2 -
              2 * (prior.p theta * Mdl.P theta b x * Mdl.tau theta) * (N / D) +
              prior.p theta * Mdl.P theta b x * Mdl.tau theta ^ 2) := by
                apply Finset.sum_congr rfl
                intro theta _
                ring
          _ = D * (N / D) ^ 2 - 2 * N * (N / D) + Q := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.sum_mul, ← Finset.sum_mul, hsumD]
            rw [← Finset.mul_sum, hsumN]
          _ = Q - N ^ 2 / D := by field_simp; ring
    _ = (∑ theta, prior.p theta * Mdl.tau theta ^ 2) -
        ∑ x, if Mdl.predictiveMass prior b x = 0 then 0
          else Mdl.predictiveTarget prior b x ^ 2 /
            Mdl.predictiveMass prior b x := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro theta _
      calc
        (∑ x, prior.p theta * Mdl.P theta b x * Mdl.tau theta ^ 2) =
            prior.p theta * Mdl.tau theta ^ 2 * ∑ x, Mdl.P theta b x := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = prior.p theta * Mdl.tau theta ^ 2 := by rw [Mdl.P_sum, mul_one]

-- @node: posteriorResidual_eq_allocationBayesRisk
/-- [the stated side condition holds](hyp:hnu), [the posterior residual equals allocation bayes risk](goal). -/
lemma posteriorResidual_eq_allocationBayesRisk (c : RatContrast K)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu) (r : AllocVec K n) :
    (rationalOrbitModel c).posteriorResidual (rationalPriorOf nu hnu) r =
      (allocationBayesRisk c nu r : ℝ) := by
  classical
  rw [posteriorResidual_eq_secondMoment_sub]
  unfold allocationBayesRisk
    Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveMass
    Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveTarget
    rationalOrbitModel rationalPriorOf
  push_cast
  simp_rw [tauCountRat_cast]
  apply congrArg₂ (fun x y : ℝ => x - y)
  · apply Finset.sum_congr rfl
    intro m _
    ring
  · apply Finset.sum_congr rfl
    intro x _
    have hmass : (0 : ℝ) ≤ ∑ m, (nu m : ℝ) * (orbitLik m r x : ℝ) :=
      Finset.sum_nonneg fun m _ => mul_nonneg (by exact_mod_cast hnu.1 m)
        (by exact_mod_cast orbitLik_nonneg m r x)
    by_cases hq : 0 < predictiveMass c nu r x
    · have hr : (0 : ℝ) < ∑ m, (nu m : ℝ) * (orbitLik m r x : ℝ) := by
        exact_mod_cast hq
      rw [if_neg (ne_of_gt hr), dif_pos hq]
      unfold predictiveTarget predictiveMass
      push_cast
      simp_rw [tauCountRat_cast]
    · have hq0 : predictiveMass c nu r x = 0 := by
        have : 0 ≤ predictiveMass c nu r x :=
          Finset.sum_nonneg fun m _ => mul_nonneg (hnu.1 m) (orbitLik_nonneg m r x)
        linarith
      have hr0 : (∑ m, (nu m : ℝ) * (orbitLik m r x : ℝ)) = 0 := by
        exact_mod_cast hq0
      rw [if_pos hr0, dif_neg hq]
      norm_num

-- @node: Lc_ratContrastToReal
/-- [the contrast norm rat contrast to real property holds](goal). -/
lemma Lc_ratContrastToReal (c : RatContrast K) :
    Lc (ratContrastToReal c) = (LcRat c : ℝ) := by
  unfold Lc LcRat ratContrastToReal
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  exact_mod_cast rfl

-- @node: hRat_cast
/-- [the h rat real-valued identity property holds](goal). -/
lemma hRat_cast (c : RatContrast K) :
    (hRat c : ℝ) = Lc (ratContrastToReal c) / 2 := by
  rw [Lc_ratContrastToReal]
  unfold hRat
  push_cast
  ring

-- @node: hRat_sq_eq_C0
/-- [the h rat squared equals c0](goal). -/
lemma hRat_sq_eq_C0 (c : RatContrast K) :
    (hRat c : ℝ) ^ 2 = C0 (ratContrastToReal c) := by
  rw [hRat_cast]
  unfold C0
  ring

-- @node: tauCount_mem_gridInterval
/-- [the population size is positive](hyp:hn), [the tau count belongs to grid interval](goal). -/
lemma tauCount_mem_gridInterval (c : RatContrast K) (m : CountVec K n) (hn : 0 < n) :
    tauCount (ratContrastToReal c) m ∈ Set.Icc (-(hRat c : ℝ)) (hRat c : ℝ) := by
  obtain ⟨z, hz⟩ := exists_fun_card_fiber_eq
    (C := RespType K) (fun t => (m.1 t : ℕ)) m.2
  have hm : scheduleCounts z = m := by
    apply Subtype.ext
    funext t
    apply Fin.ext
    simpa [scheduleCounts, rawScheduleCount] using hz t
  rw [← hm, ← tauC_eq_tauCount_scheduleCounts, hRat_cast]
  simpa [neg_div] using tauC_mem_naturalInterval (ratContrastToReal c) z hn

-- @node: gammaMC_mem_gridInterval
/-- [the grid resolution is positive](hyp:hM), [the gamma mc belongs to grid interval](goal). -/
lemma gammaMC_mem_gridInterval (c : RatContrast K) (hM : 0 < M)
    (g : Fin (2 * M + 1)) :
    (gammaMC M c g : ℝ) ∈ Set.Icc (-(hRat c : ℝ)) (hRat c : ℝ) := by
  have hhQ : 0 ≤ hRat c := by
    unfold hRat LcRat
    positivity
  have hh : (0 : ℝ) ≤ (hRat c : ℝ) := by exact_mod_cast hhQ
  have hMR : (0 : ℝ) < M := by positivity
  have hg : ((g : ℕ) : ℝ) ≤ 2 * M := by
    exact_mod_cast (Nat.le_of_lt_succ g.2)
  unfold gammaMC
  push_cast
  constructor <;> (field_simp; nlinarith)

-- @node: posteriorMean_mem_gridInterval
/-- [the stated side condition holds](hyp:hnu), [the population size is positive](hyp:hn), [the posterior mean belongs to grid interval](goal). -/
lemma posteriorMean_mem_gridInterval (c : RatContrast K)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu) (hn : 0 < n)
    (r : AllocVec K n) (x : ObsVec r) :
    (rationalOrbitModel c).posteriorMean (rationalPriorOf nu hnu) r x ∈
      Set.Icc (-(hRat c : ℝ)) (hRat c : ℝ) := by
  classical
  let Mdl := rationalOrbitModel (n := n) c
  let prior := rationalPriorOf nu hnu
  by_cases hx : Mdl.predictiveMass prior r x = 0
  · rw [Causalean.Stat.Minimax.FiniteSquaredLoss.Model.posteriorMean, if_pos hx]
    have hh : (0 : ℝ) ≤ (hRat c : ℝ) := by
      exact_mod_cast (show 0 ≤ hRat c by unfold hRat LcRat; positivity)
    exact ⟨by linarith, hh⟩
  · have hD : 0 < Mdl.predictiveMass prior r x :=
      lt_of_le_of_ne (Mdl.predictiveMass_nonneg prior r x) (Ne.symm hx)
    rw [Causalean.Stat.Minimax.FiniteSquaredLoss.Model.posteriorMean, if_neg hx]
    constructor
    · rw [le_div_iff₀ hD]
      unfold Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveMass
        Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveTarget
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      have hj : 0 ≤ prior.p m * Mdl.P m r x :=
        mul_nonneg (prior.p_nonneg m) (Mdl.P_nonneg m r x)
      calc
        -(hRat c : ℝ) * (prior.p m * Mdl.P m r x) =
            (prior.p m * Mdl.P m r x) * -(hRat c : ℝ) := by ring
        _ ≤ (prior.p m * Mdl.P m r x) * Mdl.tau m := by
          exact mul_le_mul_of_nonneg_left (tauCount_mem_gridInterval c m hn).1 hj
    · rw [div_le_iff₀ hD]
      unfold Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveMass
        Causalean.Stat.Minimax.FiniteSquaredLoss.Model.predictiveTarget
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      have hj : 0 ≤ prior.p m * Mdl.P m r x :=
        mul_nonneg (prior.p_nonneg m) (Mdl.P_nonneg m r x)
      calc
        (prior.p m * Mdl.P m r x) * Mdl.tau m ≤
            (prior.p m * Mdl.P m r x) * (hRat c : ℝ) := by
          exact mul_le_mul_of_nonneg_left (tauCount_mem_gridInterval c m hn).2 hj
        _ = (hRat c : ℝ) * (prior.p m * Mdl.P m r x) := by ring

-- @node: lowerCertificate_eq_posteriorResidual_sInf
/-- [the stated side condition holds](hyp:hnu), [the lower certificate equals posterior residual s inf](goal). -/
lemma lowerCertificate_eq_posteriorResidual_sInf (c : RatContrast K)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu) :
    lowerCertificate c nu =
      sInf (Set.range ((rationalOrbitModel c).posteriorResidual
        (rationalPriorOf nu hnu))) := by
  unfold lowerCertificate
  congr 1
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, posteriorResidual_eq_allocationBayesRisk c nu hnu r⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, posteriorResidual_eq_allocationBayesRisk c nu hnu r⟩

-- @node: orbitModel_minimax_eq_orbitGameValue
/-- [the orbit model minimax equals orbit game value](goal). -/
lemma orbitModel_minimax_eq_orbitGameValue (c : RatContrast K) :
    Causalean.Stat.minimaxValue
      (Causalean.Stat.Minimax.FiniteSquaredLoss.risk
        (l := -Lc (ratContrastToReal c) / 2)
        (u := Lc (ratContrastToReal c) / 2)
        (rationalOrbitModel (n := n) c).P (rationalOrbitModel (n := n) c).tau) =
      orbitGameValue K n (ratContrastToReal c) := by
  let e : OrbitProcedure K n (ratContrastToReal c) ≃
      Causalean.Stat.Minimax.FiniteSquaredLoss.Procedure
        (fun r : AllocVec K n => ObsVec r)
        (-Lc (ratContrastToReal c) / 2) (Lc (ratContrastToReal c) / 2) :=
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun q => (q.design, q.decision)
      left_inv := fun _ => rfl
      right_inv := fun q => by cases q; rfl }
  unfold orbitGameValue Causalean.Stat.minimaxValue
  rw [← e.iInf_comp]
  rfl

-- @node: lowerCertificate_le_rhoN
/-- [the population size is positive](hyp:hn), [the stated side condition holds](hyp:hnu), [the lower certificate is at most rho n](goal). -/
lemma lowerCertificate_le_rhoN (c : RatContrast K) (hn : 0 < n)
    (nu : CountVec K n → ℚ) (hnu : IsRationalPrior nu) :
    lowerCertificate c nu ≤ rhoN K n (ratContrastToReal c) := by
  classical
  have hK := rationalContrast_admissibleArmCount c
  have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
  letI : Nonempty (Arm K) := Fintype.card_pos_iff.mp (by simpa using hKpos)
  letI : Nonempty (AllocVec K n) :=
    ⟨assignmentCounts (fun _ => Classical.choice inferInstance)⟩
  letI : Nonempty (CountVec K n) := ⟨scheduleCounts (fun _ _ => false)⟩
  have hlu : -Lc (ratContrastToReal c) / 2 ≤ Lc (ratContrastToReal c) / 2 := by
    have := Lc_pos (ratContrastToReal c)
    linarith
  rw [lowerCertificate_eq_posteriorResidual_sInf c nu hnu]
  calc
    sInf (Set.range ((rationalOrbitModel (n := n) c).posteriorResidual
        (rationalPriorOf nu hnu))) ≤
        Causalean.Stat.minimaxValue
          (Causalean.Stat.Minimax.FiniteSquaredLoss.risk
            (l := -Lc (ratContrastToReal c) / 2)
            (u := Lc (ratContrastToReal c) / 2)
            (rationalOrbitModel (n := n) c).P
            (rationalOrbitModel (n := n) c).tau) :=
      (rationalOrbitModel (n := n) c).sInf_posteriorResidual_le_minimaxValue
        (rationalPriorOf nu hnu) hlu
    _ = orbitGameValue K n (ratContrastToReal c) :=
      orbitModel_minimax_eq_orbitGameValue (n := n) c
    _ = rhoN K n (ratContrastToReal c) :=
      (exact_response_type_game K n (ratContrastToReal c) hK).2.2.2.1.symm

-- @node: gridBarycenter_eq_conditionalBarycenter
/-- [the delta condition holds](hyp:delta), [the stated side condition holds](hyp:hpi0), [the stated side condition holds](hyp:hpi1), [the stated side condition holds](hyp:hbar), [the grid barycenter equals conditional barycenter](goal). -/
lemma gridBarycenter_eq_conditionalBarycenter (c : RatContrast K)
    (pi : GridPi K n) (w : GridWeight K n M)
    (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
    (hpi0 : ∀ r, 0 ≤ pi r) (hpi1 : ∑ r, pi r = 1)
    (hbar : IsGridBarycenter c pi w delta) (r : AllocVec K n) (x : ObsVec r) :
    delta r x =
      Causalean.Stat.Minimax.FiniteSquaredLoss.conditionalBarycenter
        (rationalGridDesignOf pi hpi0 hpi1) w
        (fun g => (gammaMC M c g : ℝ)) 0 r x := by
  classical
  rw [hbar r x]
  unfold Causalean.Stat.Minimax.FiniteSquaredLoss.conditionalBarycenter
    rationalGridDesignOf
  by_cases hp : pi r = 0
  · have hpr : ((pi r : ℚ) : ℝ) = 0 := by rw [hp]; norm_num
    have hnpos : ¬ 0 < pi r := by rw [hp]; exact lt_irrefl 0
    rw [dif_neg hnpos, if_pos hpr]
  · have hpq : 0 < pi r := lt_of_le_of_ne (hpi0 r) (Ne.symm hp)
    have hpr : (0 : ℝ) < (pi r : ℝ) := by exact_mod_cast hpq
    rw [dif_pos hpq, if_neg (ne_of_gt hpr), Finset.sum_div]

-- @node: upperCertificate_le_gridObjective
/-- [the delta condition holds](hyp:delta), [the stated side condition holds](hyp:hcert), [the stated side condition holds](hyp:hbar), [the upper certificate is at most grid objective](goal). -/
lemma upperCertificate_le_gridObjective (c : RatContrast K)
    (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
    (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
    (nu : CountVec K n → ℚ)
    (hcert : ExactGridPrimalDualCertificate c pi w u nu)
    (hbar : IsGridBarycenter c pi w delta) :
    upperCertificate c pi delta ≤ (u : ℝ) := by
  classical
  rcases hcert with ⟨wQ, y, rfl, hpr, _hy, _hnu, _hu⟩
  let piD := rationalGridDesignOf pi hpr.2.2.1 hpr.1
  let wR : GridWeight K n M := rationalGridWeightToReal M wQ
  letI : Nonempty (CountVec K n) := ⟨scheduleCounts (fun _ _ => false)⟩
  have hw : ∀ r x g, 0 ≤ wR r x g := by
    intro r x g
    dsimp [wR, rationalGridWeightToReal]
    exact_mod_cast hpr.2.2.2.1 r x g
  have hocc : ∀ r x, ∑ g, wR r x g = piD.p r := by
    intro r x
    dsimp [wR, piD, rationalGridDesignOf, rationalGridWeightToReal]
    exact_mod_cast hpr.2.1 r x
  unfold upperCertificate
  apply ciSup_le
  intro m
  have hbary := (rationalOrbitModel c).conditionalBarycenter_risk_le
    piD wR (fun g => (gammaMC M c g : ℝ)) 0 hw hocc m
  have hdelta (r : AllocVec K n) (x : ObsVec r) :
      delta r x = Causalean.Stat.Minimax.FiniteSquaredLoss.conditionalBarycenter
        piD wR (fun g => (gammaMC M c g : ℝ)) 0 r x := by
    simpa [piD, wR] using
      gridBarycenter_eq_conditionalBarycenter c pi
        (rationalGridWeightToReal M wQ) delta hpr.2.2.1 hpr.1 hbar r x
  calc
    (∑ r, (pi r : ℝ) * ∑ x : ObsVec r,
        (orbitLik m r x : ℝ) *
          (delta r x - (tauCountRat c m : ℝ)) ^ 2) ≤
        ∑ r, ∑ x : ObsVec r, ∑ g,
          (orbitLik m r x : ℝ) * wR r x g *
            ((gammaMC M c g : ℝ) - tauCount (ratContrastToReal c) m) ^ 2 := by
      simpa [piD, rationalGridDesignOf, rationalOrbitModel, hdelta,
        tauCountRat_cast] using hbary
    _ ≤ (u : ℝ) := by
      rw [← tauCountRat_cast]
      dsimp [wR, rationalGridWeightToReal]
      exact_mod_cast hpr.2.2.2.2 m

-- @node: rhoN_le_upperCertificate
/-- [the grid resolution is positive](hyp:hM), [the delta condition holds](hyp:delta), [the stated side condition holds](hyp:hprimal), [the stated side condition holds](hyp:hbar), [the rho n is at most upper certificate](goal). -/
lemma rhoN_le_upperCertificate (c : RatContrast K) (hM : 0 < M)
    (pi : GridPi K n) (w : GridWeight K n M)
    (delta : ∀ r : AllocVec K n, ObsVec r → ℝ)
    (hprimal : ∃ wQ : RationalGridWeight K n M, ∃ u : ℚ,
      w = rationalGridWeightToReal M wQ ∧ GridLPFeasible K n M c pi wQ u)
    (hbar : IsGridBarycenter c pi w delta) :
    rhoN K n (ratContrastToReal c) ≤ upperCertificate c pi delta := by
  classical
  rcases hprimal with ⟨wQ, u, rfl, hpr⟩
  have hK := rationalContrast_admissibleArmCount c
  have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
  letI : Nonempty (Arm K) := Fintype.card_pos_iff.mp (by simpa using hKpos)
  letI : Nonempty (AllocVec K n) :=
    ⟨assignmentCounts (fun _ => Classical.choice inferInstance)⟩
  letI : Nonempty (CountVec K n) := ⟨scheduleCounts (fun _ _ => false)⟩
  let piD := rationalGridDesignOf pi hpr.2.2.1 hpr.1
  let wR : GridWeight K n M := rationalGridWeightToReal M wQ
  have hw : ∀ r x g, 0 ≤ wR r x g := by
    intro r x g
    dsimp [wR, rationalGridWeightToReal]
    exact_mod_cast hpr.2.2.2.1 r x g
  have hocc : ∀ r x, ∑ g, wR r x g = piD.p r := by
    intro r x
    dsimp [wR, piD, rationalGridDesignOf, rationalGridWeightToReal]
    exact_mod_cast hpr.2.1 r x
  have hzero : (0 : ℝ) ∈
      Set.Icc (-Lc (ratContrastToReal c) / 2) (Lc (ratContrastToReal c) / 2) := by
    have := Lc_pos (ratContrastToReal c)
    constructor <;> linarith
  have hgamma (g : Fin (2 * M + 1)) : (gammaMC M c g : ℝ) ∈
      Set.Icc (-Lc (ratContrastToReal c) / 2) (Lc (ratContrastToReal c) / 2) := by
    simpa [hRat_cast, neg_div] using gammaMC_mem_gridInterval c hM g
  let q := Causalean.Stat.Minimax.FiniteSquaredLoss.barycenterProcedure
    piD wR (fun g => (gammaMC M c g : ℝ)) 0 hw hocc hzero hgamma
  have hdelta (r : AllocVec K n) (x : ObsVec r) :
      delta r x = (q.decision r x : ℝ) := by
    change delta r x =
      Causalean.Stat.Minimax.FiniteSquaredLoss.conditionalBarycenter
        piD wR (fun g => (gammaMC M c g : ℝ)) 0 r x
    simpa [piD, wR] using
      gridBarycenter_eq_conditionalBarycenter c pi
        (rationalGridWeightToReal M wQ) delta hpr.2.2.1 hpr.1 hbar r x
  calc
    rhoN K n (ratContrastToReal c) = orbitGameValue K n (ratContrastToReal c) :=
      (exact_response_type_game K n (ratContrastToReal c) hK).2.2.2.1
    _ = Causalean.Stat.minimaxValue
        (Causalean.Stat.Minimax.FiniteSquaredLoss.risk
          (l := -Lc (ratContrastToReal c) / 2)
          (u := Lc (ratContrastToReal c) / 2)
          (rationalOrbitModel (n := n) c).P
          (rationalOrbitModel (n := n) c).tau) :=
      (orbitModel_minimax_eq_orbitGameValue (n := n) c).symm
    _ ≤ Causalean.Stat.worstCaseRisk
        (Causalean.Stat.Minimax.FiniteSquaredLoss.risk
          (rationalOrbitModel (n := n) c).P
          (rationalOrbitModel (n := n) c).tau) q :=
      Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (fun q' m => Causalean.Stat.Minimax.FiniteSquaredLoss.risk_nonneg
          (rationalOrbitModel (n := n) c).P
          (rationalOrbitModel (n := n) c).tau
          (rationalOrbitModel (n := n) c).P_nonneg q' m) q
    _ = upperCertificate c pi delta := by
      unfold Causalean.Stat.worstCaseRisk upperCertificate
      congr with m
      unfold Causalean.Stat.Minimax.FiniteSquaredLoss.risk
      apply Finset.sum_congr rfl
      intro r _
      apply congrArg (fun z : ℝ => (pi r : ℝ) * z)
      apply Finset.sum_congr rfl
      intro x _
      rw [← hdelta r x, tauCountRat_cast]
      rfl

-- @node: gridDualObjective_le_fixedGridBayesRisk
/-- [the dual vector is feasible](hyp:hy), [the grid dual objective is at most fixed grid bayes risk](goal). -/
lemma gridDualObjective_le_fixedGridBayesRisk (c : RatContrast K)
    (y : GridDualMultipliers K n M) (hy : GridDualFeasible c y)
    (r : AllocVec K n) (gsel : ObsVec r → Fin (2 * M + 1)) :
    gridDualObjective y ≤
      ∑ m, (y.risk m : ℝ) * ∑ x : ObsVec r,
        (orbitLik m r x : ℝ) *
          ((gammaMC M c (gsel x) : ℝ) - (tauCountRat c m : ℝ)) ^ 2 := by
  classical
  let alpha : ObsVec r → ℚ := fun x =>
    y.occupancyUpper r x - y.occupancyLower r x
  have hx (x : ObsVec r) :
      -alpha x ≤ ∑ m, y.risk m * orbitLik m r x *
        (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 := by
    have hs := hy.2.2.2.2.2.2.2.2 r x (gsel x)
    have hw := hy.2.2.2.2.1 r x (gsel x)
    dsimp [alpha]
    linarith
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (ObsVec r))) => hx x)
  have hnorm := hy.2.2.2.2.2.2.2.1 r
  have hpi := hy.2.2.2.1 r
  have hq : gridDualObjective y ≤
      ∑ x, ∑ m, y.risk m * orbitLik m r x *
        (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 := by
    calc
      gridDualObjective y = -(∑ x, (y.occupancyUpper r x -
          y.occupancyLower r x)) - y.piNonnegative r := by
        unfold gridDualObjective
        linarith
      _ ≤ -(∑ x, (y.occupancyUpper r x - y.occupancyLower r x)) := by
        linarith
      _ = ∑ x, -(y.occupancyUpper r x - y.occupancyLower r x) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ ∑ x, ∑ m, y.risk m * orbitLik m r x *
          (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 := hsum
  exact_mod_cast (show gridDualObjective y ≤
      ∑ m, y.risk m * ∑ x : ObsVec r,
        orbitLik m r x * (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 by
    calc
      gridDualObjective y ≤ ∑ x, ∑ m, y.risk m * orbitLik m r x *
          (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 := hq
      _ = ∑ m, y.risk m * ∑ x : ObsVec r,
          orbitLik m r x * (gammaMC M c (gsel x) - tauCountRat c m) ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring)

-- @node: gridObjective_le_lowerCertificate_add_mesh
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the stated side condition holds](hyp:hcert), [the grid objective is at most lower certificate add mesh](goal). -/
lemma gridObjective_le_lowerCertificate_add_mesh (c : RatContrast K)
    (hn : 0 < n) (hM : 0 < M)
    (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
    (nu : CountVec K n → ℚ)
    (hcert : ExactGridPrimalDualCertificate c pi w u nu) :
    (u : ℝ) ≤ lowerCertificate c nu +
      C0 (ratContrastToReal c) / (4 * (M : ℝ) ^ 2) := by
  classical
  rcases hcert with ⟨wQ, y, hw, hpr, hy, hnuEq, hu⟩
  subst nu
  have hnu : IsRationalPrior y.risk := ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩
  let Mdl := rationalOrbitModel (n := n) c
  let prior := rationalPriorOf y.risk hnu
  let err : ℝ := (hRat c : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2)
  have hper (r : AllocVec K n) :
      (u : ℝ) ≤ (allocationBayesRisk c y.risk r : ℝ) + err := by
    let gsel : ObsVec r → Fin (2 * M + 1) := fun x =>
      Classical.choose (nearest_grid_error c M hM
        (Mdl.posteriorMean prior r x)
        (posteriorMean_mem_gridInterval c y.risk hnu hn r x))
    have hgsel (x : ObsVec r) :
        |Mdl.posteriorMean prior r x - (gammaMC M c (gsel x) : ℝ)| ≤
          (hRat c : ℝ) / (2 * M) :=
      Classical.choose_spec (nearest_grid_error c M hM
        (Mdl.posteriorMean prior r x)
        (posteriorMean_mem_gridInterval c y.risk hnu hn r x))
    have hdual := gridDualObjective_le_fixedGridBayesRisk c y hy r gsel
    rw [← hu] at hdual
    have hsquare := Mdl.squaredRisk_eq_posteriorResidual_add prior r
      (fun x => (gammaMC M c (gsel x) : ℝ))
    have hround :
        ∑ x : ObsVec r, Mdl.predictiveMass prior r x *
          ((gammaMC M c (gsel x) : ℝ) - Mdl.posteriorMean prior r x) ^ 2 ≤ err := by
      calc
        _ ≤ ∑ x : ObsVec r, Mdl.predictiveMass prior r x *
            ((hRat c : ℝ) / (2 * M)) ^ 2 := by
          apply Finset.sum_le_sum
          intro x _
          have habs := hgsel x
          rw [abs_sub_comm] at habs
          apply mul_le_mul_of_nonneg_left _ (Mdl.predictiveMass_nonneg prior r x)
          apply (sq_le_sq).2
          have hhQ : (0 : ℚ) ≤ hRat c := by unfold hRat LcRat; positivity
          have hh : (0 : ℝ) ≤ (hRat c : ℝ) := by exact_mod_cast hhQ
          have hb : (0 : ℝ) ≤ (hRat c : ℝ) / (2 * M) := by positivity
          simpa [abs_of_nonneg hb] using habs
        _ = err := by
          rw [← Finset.sum_mul, Mdl.sum_predictiveMass]
          dsimp [err]
          field_simp
          ring
    have hrisk :
        ∑ m, prior.p m * ∑ x : ObsVec r, Mdl.P m r x *
          ((gammaMC M c (gsel x) : ℝ) - Mdl.tau m) ^ 2 ≤
          (allocationBayesRisk c y.risk r : ℝ) + err := by
      rw [hsquare, posteriorResidual_eq_allocationBayesRisk c y.risk hnu r]
      simpa [add_comm] using
        (add_le_add_left hround (allocationBayesRisk c y.risk r : ℝ))
    calc
      (u : ℝ) ≤ ∑ m, (y.risk m : ℝ) * ∑ x : ObsVec r,
          (orbitLik m r x : ℝ) *
            ((gammaMC M c (gsel x) : ℝ) - (tauCountRat c m : ℝ)) ^ 2 := hdual
      _ ≤ (allocationBayesRisk c y.risk r : ℝ) + err := by
        simpa [prior, Mdl, rationalPriorOf, rationalOrbitModel, tauCountRat_cast] using hrisk
  have hne : ({v : ℝ | ∃ r : AllocVec K n,
      v = (allocationBayesRisk c y.risk r : ℝ)}).Nonempty := by
    let r : AllocVec K n := assignmentCounts (fun _ => (Classical.choice
      (show Nonempty (Arm K) from Fintype.card_pos_iff.mp (by
        have hK := rationalContrast_admissibleArmCount c
        unfold AdmissibleArmCount at hK
        simpa using (show 0 < K by omega)))))
    exact ⟨_, r, rfl⟩
  have hinf : (u : ℝ) - err ≤ lowerCertificate c y.risk := by
    unfold lowerCertificate
    apply le_csInf hne
    rintro v ⟨r, rfl⟩
    linarith [hper r]
  dsimp [err] at hinf ⊢
  rw [hRat_sq_eq_C0] at hinf
  linarith

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
