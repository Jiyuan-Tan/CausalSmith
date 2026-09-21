module

public import Causalean.Stat.Bootstrap.SmoothFunctionOfMeans.Basic
public import Causalean.Stat.GMM.SmoothFeasibleGeneral

/-!
# Feasible GMM: sample-function objects and the deterministic remainder bounds

This module holds the finite-sample building blocks of the feasible-GMM bootstrap argument: the
sample-function forms of the smooth GMM Jacobian, the normalized moment and the first-order-condition
residual, together with the two deterministic inequalities they satisfy on a single fixed sample.
`gmmNormalizedMomentFn_expansion_le` is the one-sample Taylor expansion of the normalized moment
around the target parameter, and `feasibleGMM_populationRemainder_le` turns operator, residual and
moment budgets on one sample into a bound on the influence-function linearization remainder.
Neither statement mentions probability; the probabilistic argument that supplies the budgets lives in
`Causalean.Stat.Bootstrap.SmoothZEstimator.FeasibleGMMLinearization`, and the user-facing constructor
in `…SmoothZEstimator.FeasibleGMM`.
-/

@[expose] public section

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

/-- Given [smooth GMM regularity](hyp:reg), [a parameter](hyp:theta), and [finite
data](hyp:data), the [sample-function GMM Jacobian](goal) averages the observationwise moment
derivatives. -/
def gmmSampleJacobianFn {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob) (theta : E)
    {n : ℕ} (data : Fin n → X) : E →L[ℝ] F :=
  finMean (fun i ↦ reg.deriv theta (data i))

/-- Given [a GMM problem](hyp:prob), [a parameter](hyp:theta), and [finite data](hyp:data), the
[sample-function normalized moment](goal) is the moment sum divided by the square root of sample
size. -/
def gmmNormalizedMomentFn (prob : GMMProblem (E := E) (F := F) P)
    (theta : E) {n : ℕ} (data : Fin n → X) : F :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g theta (data i)

/-- Given [a smooth GMM problem](hyp:prob,reg), [an estimated parameter and weight](hyp:theta,W),
and [finite data](hyp:data), the [normalized feasible-GMM first-order-condition residual](goal)
applies the empirical Jacobian adjoint and estimated weight to the normalized moment. -/
def feasibleGMMFOCResidualFn
    (prob : GMMProblem (E := E) (F := F) P)
    (reg : SmoothGMomentRegularity prob) (theta : E) (W : F →L[ℝ] F)
    {n : ℕ} (data : Fin n → X) : E :=
  (adjoint (gmmSampleJacobianFn reg theta data) ∘L W)
  (gmmNormalizedMomentFn prob theta data)

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace F] in
/-- On [a single nonempty sample](hyp:hn,x) from [a smooth feasible-GMM problem](hyp:prob,reg), at
[a parameter value and a weight operator](hyp:theta,W) with [nonnegative budgets](hyp:hC,hD,hq,hK)
that bound [the Taylor error of the normalized moment](hyp:hExpansion), [the drift of the weighted
sample Jacobian from its population counterpart](hyp:hOperator), [the first-order-condition
residual](hyp:hFOC) and [the normalized moment at the target](hyp:hMoment), and where [the drift is
small enough for the absorption step](hyp:hAbsorb), [the influence-function linearization remainder
is bounded by an explicit expression in those budgets](goal).

This is the deterministic core of the feasible-GMM bootstrap linearization: it is applied once to the
observed sample and once to a resample, and the probabilistic work is to show that each budget holds
with high probability.  The explicit right-hand side is a proof artifact, not a quantity to cite. -/
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
/-- On [a single nonempty sample](hyp:hn,x) from [a smooth GMM problem](hyp:reg), at [a parameter
value](hyp:theta), given [a nonnegative](hyp:hLnonneg) [Lipschitz constant for the moment
derivative on a ball](hyp:hLbound), [a parameter in that ball](hyp:theta,htheta), [the normalized moment differs from its first-order expansion around the
target by at most the Jacobian drift plus the Lipschitz term, times the scaled parameter
displacement](goal).

The mean-value form of the one-sample Taylor expansion; it supplies the `hExpansion` budget of
`feasibleGMM_populationRemainder_le`. -/
theorem gmmNormalizedMomentFn_expansion_le
    {prob : GMMProblem (E := E) (F := F) P}
    (reg : SmoothGMomentRegularity prob)
    {L : X → ℝ} {delta : ℝ} (hLnonneg : ∀ x, 0 ≤ L x)
    (hLbound : ∀ theta ∈ Metric.closedBall prob.θ₀ delta,
      ∀ theta' ∈ Metric.closedBall prob.θ₀ delta, ∀ x,
      ‖reg.deriv theta x - reg.deriv theta' x‖ ≤ L x * ‖theta - theta'‖)
    {n : ℕ} (hn : n ≠ 0) (x : Fin n → X) (theta : E)
    (htheta : theta ∈ Metric.closedBall prob.θ₀ delta) :
    ‖gmmNormalizedMomentFn prob theta x -
        (gmmNormalizedMomentFn prob prob.θ₀ x +
          prob.G (Real.sqrt (n : ℝ) • (theta - prob.θ₀)))‖ ≤
      (‖finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G‖ +
        finMean (fun i ↦ L (x i)) * ‖theta - prob.θ₀‖) *
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
    exact reg.taylor_remainder_le theta hLnonneg hLbound htheta (x i)
  have hmeanExpansion :
      finMean (fun i ↦ prob.g theta (x i)) =
        finMean (fun i ↦ prob.g prob.θ₀ (x i)) +
          finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) Delta +
          finMean R := by
    unfold finMean
    simp only [smul_apply]
    rw [← smul_add, ← smul_add]
    apply congrArg
    simp only [sum_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [R, Delta]
    abel
  have hRmean : ‖finMean R‖ ≤
      finMean (fun i ↦ L (x i)) * ‖Delta‖ ^ 2 := by
    unfold finMean
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
  have hscaledR : ‖Real.sqrt (n : ℝ) • finMean R‖ ≤
      (finMean (fun i ↦ L (x i)) * ‖Delta‖) *
        ‖Real.sqrt (n : ℝ) • Delta‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt.le,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
    calc
      Real.sqrt (n : ℝ) * ‖finMean R‖ ≤
          Real.sqrt (n : ℝ) *
            (finMean (fun i ↦ L (x i)) * ‖Delta‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hRmean hsqrt.le
      _ = (finMean (fun i ↦ L (x i)) * ‖Delta‖) *
          (Real.sqrt (n : ℝ) * ‖Delta‖) := by ring
  have hid :
      gmmNormalizedMomentFn prob theta x -
          (gmmNormalizedMomentFn prob prob.θ₀ x + prob.G
            (Real.sqrt (n : ℝ) • Delta)) =
        (finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G)
            (Real.sqrt (n : ℝ) • Delta) +
          Real.sqrt (n : ℝ) • finMean R := by
    unfold gmmNormalizedMomentFn
    rw [show (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g theta (x i) =
        Real.sqrt (n : ℝ) • finMean
          (fun i ↦ prob.g theta (x i)) by
      unfold finMean
      rw [smul_smul, hcoef]]
    rw [show (Real.sqrt (n : ℝ))⁻¹ • ∑ i, prob.g prob.θ₀ (x i) =
        Real.sqrt (n : ℝ) • finMean
          (fun i ↦ prob.g prob.θ₀ (x i)) by
      unfold finMean
      rw [smul_smul, hcoef]]
    rw [hmeanExpansion]
    simp only [smul_add, map_smul, sub_apply]
    module
  rw [show theta - prob.θ₀ = Delta by rfl, hid]
  exact (norm_add_le _ _).trans <| le_trans
    (add_le_add
      ((finMean (fun i ↦ reg.deriv prob.θ₀ (x i)) - prob.G).le_opNorm _)
      hscaledR) (by ring_nf; rfl)

end

end Causalean.Stat
