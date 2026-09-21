module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMM.Basic

/-!
# Deterministic expansions for smooth feasible GMM

This module supplies the finite-sample Taylor and absorption bounds used in the conditional
bootstrap linearization of smooth feasible GMM estimators.
-/

public section

namespace Causalean.Stat

open ContinuousLinearMap Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators RealInnerProductSpace Topology

noncomputable section

variable {Omega X E F : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
  {mu : Measure Omega} {P : Measure X}

/-- For [a GMM problem](hyp:prob), [smooth moment regularity](hyp:reg), [a nonzero sample
size](hyp:hn), [finite data](hyp:x), [a parameter](hyp:theta), [a weight](hyp:W), [nonnegative
error and magnitude bounds](hyp:C,D,q,K,hC,hD,hq,hK), [a moment expansion bound](hyp:hExpansion),
[an operator approximation bound](hyp:hOperator), [a first-order-condition residual bound](hyp:hFOC),
[a target-moment bound](hyp:hMoment), and [an absorption condition](hyp:hAbsorb), [the normalized
feasible-GMM estimation error is bounded by the displayed deterministic remainder](goal). -/
theorem feasibleGMM_populationRemainder_le
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob)
    {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) (theta : E) (W : F →L[ℝ] F)
    {C D q K : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hExpansion :
      ‖gmmNormalizedMomentFn prob theta x -
        (gmmNormalizedMomentFn prob prob.θ₀ x +
          prob.G (Real.sqrt (n : ℝ) • (theta - prob.θ₀)))‖ ≤
        C * ‖Real.sqrt (n : ℝ) • (theta - prob.θ₀)‖)
    (hOperator :
      ‖(adjoint (gmmSampleJacobianFn reg theta x) ∘L W) -
        (adjoint prob.G ∘L prob.W)‖ ≤ D)
    (hFOC : ‖feasibleGMMFOCResidualFn prob reg theta W x‖ ≤ q)
    (hMoment : ‖gmmNormalizedMomentFn prob prob.θ₀ x‖ ≤ K)
    (hAbsorb : ‖prob.breadInv‖ *
      (D * (‖prob.G‖ + C) + ‖adjoint prob.G ∘L prob.W‖ * C) ≤ 1 / 2) :
    ‖Real.sqrt (n : ℝ) • (theta - prob.θ₀) -
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (x i)‖ ≤
      ‖prob.breadInv‖ *
        (D * (K + (‖prob.G‖ + C) *
          (2 * ‖prob.breadInv‖ *
            (D * K + q + ‖adjoint prob.G ∘L prob.W‖ * K))) + q +
          ‖adjoint prob.G ∘L prob.W‖ * C *
            (2 * ‖prob.breadInv‖ *
              (D * K + q + ‖adjoint prob.G ∘L prob.W‖ * K))) := by
  let A0 : F →L[ℝ] E := adjoint prob.G ∘L prob.W
  let An : F →L[ℝ] E := adjoint (gmmSampleJacobianFn reg theta x) ∘L W
  let T : F := gmmNormalizedMomentFn prob theta x
  let U : F := gmmNormalizedMomentFn prob prob.θ₀ x
  let v : E := Real.sqrt (n : ℝ) • (theta - prob.θ₀)
  let err : F := T - (U + prob.G v)
  let M : ℝ := 2 * ‖prob.breadInv‖ * (D * K + q + ‖A0‖ * K)
  have hleft : prob.breadInv (A0 (prob.G v)) = v := by
    rw [show A0 (prob.G v) = gmmBread prob.G prob.W v by rfl,
      ← comp_apply, prob.breadInv_left, id_apply]
  have hvid : v = prob.breadInv
      ((A0 - An) T + An T - A0 U - A0 err) := by
    rw [show (A0 - An) T + An T - A0 U - A0 err = A0 (prob.G v) by
      simp only [sub_apply]
      dsimp [err]
      simp only [map_sub, map_add]
      abel]
    exact hleft.symm
  have hOperator' : ‖A0 - An‖ ≤ D := by
    simpa [A0, An, norm_sub_rev] using hOperator
  have herr : ‖err‖ ≤ C * ‖v‖ := by
    simpa [T, U, v, err] using hExpansion
  have hTbound : ‖T‖ ≤ K + (‖prob.G‖ + C) * ‖v‖ := by
    calc
      ‖T‖ = ‖(U + prob.G v) + err‖ := by
        congr 1
        dsimp [err]
        abel
      _ ≤ ‖U + prob.G v‖ + ‖err‖ := norm_add_le _ _
      _ ≤ (‖U‖ + ‖prob.G‖ * ‖v‖) + C * ‖v‖ := by
        exact add_le_add
          ((norm_add_le _ _).trans (add_le_add le_rfl (prob.G.le_opNorm v)))
          (by simpa [T, U, v, err] using hExpansion)
      _ = ‖U‖ + (‖prob.G‖ + C) * ‖v‖ := by ring
      _ ≤ K + (‖prob.G‖ + C) * ‖v‖ := by
        gcongr
  have hvpre : ‖v‖ ≤
      ‖prob.breadInv‖ * (D * K + q + ‖A0‖ * K) +
        (‖prob.breadInv‖ *
          (D * (‖prob.G‖ + C) + ‖A0‖ * C)) * ‖v‖ := by
    calc
      ‖v‖ = ‖prob.breadInv ((A0 - An) T + An T - A0 U - A0 err)‖ := by
        rw [hvid]
      _ ≤ ‖prob.breadInv‖ * ‖(A0 - An) T + An T - A0 U - A0 err‖ :=
        prob.breadInv.le_opNorm _
      _ ≤ ‖prob.breadInv‖ *
          (D * ‖T‖ + q + ‖A0‖ * ‖U‖ + ‖A0‖ * ‖err‖) := by
        gcongr
        calc
          ‖(A0 - An) T + An T - A0 U - A0 err‖ ≤
              ‖(A0 - An) T‖ + ‖An T‖ + ‖A0 U‖ + ‖A0 err‖ := by
            exact (norm_sub_le _ _).trans <| add_le_add
              ((norm_sub_le _ _).trans <| add_le_add (norm_add_le _ _) le_rfl) le_rfl
          _ ≤ D * ‖T‖ + q + ‖A0‖ * ‖U‖ + ‖A0‖ * ‖err‖ := by
            gcongr
            · have hop := (A0 - An).le_opNorm T
              exact hop.trans
                (mul_le_mul_of_nonneg_right hOperator' (norm_nonneg T))
            · simpa [An, T, feasibleGMMFOCResidualFn] using hFOC
            · exact A0.le_opNorm U
            · exact A0.le_opNorm err
      _ ≤ ‖prob.breadInv‖ *
          (D * (K + (‖prob.G‖ + C) * ‖v‖) + q + ‖A0‖ * K +
            ‖A0‖ * (C * ‖v‖)) := by
        gcongr
      _ = ‖prob.breadInv‖ * (D * K + q + ‖A0‖ * K) +
          (‖prob.breadInv‖ *
            (D * (‖prob.G‖ + C) + ‖A0‖ * C)) * ‖v‖ := by ring
  have hv : ‖v‖ ≤ M := by
    dsimp [M]
    nlinarith [hvpre, norm_nonneg v,
      mul_nonneg (norm_nonneg prob.breadInv)
        (add_nonneg (add_nonneg (mul_nonneg hD hK) hq)
          (mul_nonneg (norm_nonneg A0) hK))]
  have hinfluence :
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (x i) =
        -prob.breadInv (A0 U) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hcoef : (Real.sqrt (n : ℝ))⁻¹ =
        Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hnpos.le]
    have hU : (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i : Fin n, prob.g prob.θ₀ (x i) = U := by
      dsimp [U]
      unfold gmmNormalizedMomentFn
      rfl
    calc
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, prob.influence (x i) =
          -(Real.sqrt (n : ℝ))⁻¹ •
            prob.breadInv (A0 (∑ i : Fin n, prob.g prob.θ₀ (x i))) := by
              simp [GMMProblem.influence, gmmIF, A0, map_sum, Finset.smul_sum]
      _ = -prob.breadInv (A0 ((Real.sqrt (n : ℝ))⁻¹ •
            ∑ i : Fin n, prob.g prob.θ₀ (x i))) := by
              rw [map_smul, map_smul]
              simp
      _ = -prob.breadInv (A0 U) := by rw [hU]
  rw [hinfluence, sub_neg_eq_add]
  have hremid : v + prob.breadInv (A0 U) =
      prob.breadInv ((A0 - An) T + An T - A0 err) := by
    rw [← hleft, ← map_add]
    congr 1
    simp only [sub_apply]
    dsimp [err]
    simp only [map_sub, map_add]
    abel
  rw [show Real.sqrt (n : ℝ) • (theta - prob.θ₀) = v by rfl, hremid]
  calc
    ‖prob.breadInv ((A0 - An) T + An T - A0 err)‖ ≤
        ‖prob.breadInv‖ * ‖(A0 - An) T + An T - A0 err‖ :=
      prob.breadInv.le_opNorm _
    _ ≤ ‖prob.breadInv‖ * (D * ‖T‖ + q + ‖A0‖ * ‖err‖) := by
      gcongr
      exact (norm_sub_le _ _).trans <| add_le_add
        ((norm_add_le _ _).trans <| add_le_add
          (by
            have hop := (A0 - An).le_opNorm T
            exact hop.trans
              (mul_le_mul_of_nonneg_right hOperator' (norm_nonneg T)))
          (by simpa [An, T, feasibleGMMFOCResidualFn] using hFOC))
        (A0.le_opNorm err)
    _ ≤ ‖prob.breadInv‖ *
        (D * (K + (‖prob.G‖ + C) * M) + q + ‖A0‖ * C * M) := by
      have hTM : ‖T‖ ≤ K + (‖prob.G‖ + C) * M :=
        hTbound.trans <| add_le_add_right
          (mul_le_mul_of_nonneg_left hv (add_nonneg (norm_nonneg _) hC)) K
      have herrM : ‖err‖ ≤ C * M :=
        herr.trans (mul_le_mul_of_nonneg_left hv hC)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg prob.breadInv)
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hTM hD) le_rfl)
        (by simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left herrM (norm_nonneg A0))
    _ = ‖prob.breadInv‖ *
        (D * (K + (‖prob.G‖ + C) *
          (2 * ‖prob.breadInv‖ * (D * K + q + ‖A0‖ * K))) + q +
          ‖A0‖ * C *
            (2 * ‖prob.breadInv‖ * (D * K + q + ‖A0‖ * K))) := by rfl

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- For [smooth GMM regularity](hyp:reg), [a nonnegative Lipschitz envelope](hyp:L,hLnonneg), [a
derivative Lipschitz bound](hyp:hLbound), [a nonzero sample size](hyp:hn), [finite data](hyp:x),
and [a parameter](hyp:theta), [the normalized sample moment differs from its population-Jacobian
linearization by the displayed Taylor bound](goal). -/
theorem gmmNormalizedMomentFn_expansion_le
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob)
    {L : X → ℝ} (hLnonneg : ∀ x, 0 ≤ L x)
    (hLbound : ∀ theta theta' x,
      ‖reg.deriv theta x - reg.deriv theta' x‖ ≤ L x * ‖theta - theta'‖)
    {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) (theta : E) :
    ‖gmmNormalizedMomentFn prob theta x -
        (gmmNormalizedMomentFn prob prob.θ₀ x +
          prob.G (Real.sqrt (n : ℝ) • (theta - prob.θ₀)))‖ ≤
      (‖Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G‖ +
        Causalean.Stat.finMean (fun i ↦ L (x i)) * ‖theta - prob.θ₀‖) *
        ‖Real.sqrt (n : ℝ) • (theta - prob.θ₀)‖ := by
  let Delta : E := theta - prob.θ₀
  let R : Fin n → F := fun i ↦
    prob.g theta (x i) - prob.g prob.θ₀ (x i) -
      reg.deriv prob.θ₀ (x i) Delta
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hcoef : (Real.sqrt (n : ℝ))⁻¹ =
      Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ := by
    field_simp [hsqrt.ne']
    rw [Real.sq_sqrt hnpos.le]
  have hR : ∀ i : Fin n, ‖R i‖ ≤ L (x i) * ‖Delta‖ ^ 2 := by
    intro i
    exact reg.taylor_remainder_le theta hLnonneg hLbound (x i)
  have hmeanExpansion :
      Causalean.Stat.finMean (fun i ↦ prob.g theta (x i)) =
        Causalean.Stat.finMean (fun i ↦ prob.g prob.θ₀ (x i)) +
          Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) Delta +
          Causalean.Stat.finMean R := by
    unfold Causalean.Stat.finMean
    simp only [smul_apply]
    rw [← smul_add, ← smul_add]
    apply congrArg
    simp only [sum_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [R, Delta]
    abel
  have hRmean : ‖Causalean.Stat.finMean R‖ ≤
      Causalean.Stat.finMean (fun i ↦ L (x i)) * ‖Delta‖ ^ 2 := by
    unfold Causalean.Stat.finMean
    rw [norm_smul_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    calc
      (n : ℝ)⁻¹ * ‖∑ i, R i‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖R i‖ := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ i, L (x i) * ‖Delta‖ ^ 2 := by
        gcongr with i
        exact hR i
      _ = ((n : ℝ)⁻¹ * ∑ i, L (x i)) * ‖Delta‖ ^ 2 := by
        rw [← Finset.sum_mul]
        ring
  have hscaledR : ‖Real.sqrt (n : ℝ) • Causalean.Stat.finMean R‖ ≤
      (Causalean.Stat.finMean (fun i ↦ L (x i)) * ‖Delta‖) *
        ‖Real.sqrt (n : ℝ) • Delta‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt.le,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
    calc
      Real.sqrt (n : ℝ) * ‖Causalean.Stat.finMean R‖ ≤
          Real.sqrt (n : ℝ) *
            (Causalean.Stat.finMean (fun i ↦ L (x i)) * ‖Delta‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hRmean hsqrt.le
      _ = (Causalean.Stat.finMean (fun i ↦ L (x i)) * ‖Delta‖) *
          (Real.sqrt (n : ℝ) * ‖Delta‖) := by ring
  have hid :
      gmmNormalizedMomentFn prob theta x -
          (gmmNormalizedMomentFn prob prob.θ₀ x + prob.G
            (Real.sqrt (n : ℝ) • Delta)) =
        (Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G)
            (Real.sqrt (n : ℝ) • Delta) +
          Real.sqrt (n : ℝ) • Causalean.Stat.finMean R := by
    unfold gmmNormalizedMomentFn
    rw [show (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g theta (x i) =
        Real.sqrt (n : ℝ) • Causalean.Stat.finMean
          (fun i ↦ prob.g theta (x i)) by
      unfold Causalean.Stat.finMean
      rw [smul_smul, hcoef]]
    rw [show (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g prob.θ₀ (x i) =
        Real.sqrt (n : ℝ) • Causalean.Stat.finMean
          (fun i ↦ prob.g prob.θ₀ (x i)) by
      unfold Causalean.Stat.finMean
      rw [smul_smul, hcoef]]
    rw [hmeanExpansion]
    simp only [smul_add, map_smul, sub_apply]
    module
  rw [show theta - prob.θ₀ = Delta by rfl, hid]
  exact (norm_add_le _ _).trans <| le_trans
    (add_le_add
      ((Causalean.Stat.finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G).le_opNorm _)
      hscaledR) (by ring_nf; rfl)

end

end Causalean.Stat
