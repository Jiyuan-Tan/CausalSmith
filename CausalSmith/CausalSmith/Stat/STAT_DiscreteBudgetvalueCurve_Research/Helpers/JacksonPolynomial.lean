module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Tensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CoefficientEnvelopeFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Pilot-local Jackson polynomial and factorial lift

The polynomial is chosen from its normalized cosine representation. This lets
the estimator use its actual monomial coefficients without choosing a minimizer.
-/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open scoped BigOperators

/-- the cell four equiv definition specifies [the stated object](goal). -/
abbrev CellFourEquiv : Cell ≃ Fin 4 := finProdFinEquiv

/-- Restricted to the unit threshold interval, the extended threshold
functional is continuous in the threshold. With [the specified inputs and conditions](hyp:epsilon,u), [the stated relationship holds](goal). -/
-- @node: thresholdFunReal_continuous_time
lemma thresholdFunReal_continuous_time (epsilon : ℝ) (u : Cell → ℝ) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      thresholdFunReal epsilon lambda u) := by
  have heq : (fun lambda : Set.Icc (0 : ℝ) 1 =>
      thresholdFunReal epsilon lambda u) = fun lambda =>
        armValue epsilon 0 u +
          max 0 (armValue epsilon 1 u - armValue epsilon 0 u -
            lambda.1 * totalMass u) := by
    funext lambda
    simp only [thresholdFunReal, dif_pos lambda.property, thresholdFun]
  rw [heq]
  fun_prop

/-- At a fixed cell vector, the threshold functional is Lipschitz in the
threshold with constant equal to the absolute total cell mass. With [the specified inputs and conditions](hyp:epsilon,u,lambda,mu), [the stated relationship holds](goal). -/
-- @node: thresholdFunReal_lambda_lipschitz
lemma thresholdFunReal_lambda_lipschitz (epsilon : ℝ) (u : Cell → ℝ)
    (lambda mu : Set.Icc (0 : ℝ) 1) :
    |thresholdFunReal epsilon lambda u - thresholdFunReal epsilon mu u| ≤
      |(lambda : ℝ) - mu| * |totalMass u| := by
  simp only [thresholdFunReal, dif_pos lambda.property, dif_pos mu.property,
    thresholdFun]
  have h := abs_max_sub_max_le_abs
    (armValue epsilon 1 u - armValue epsilon 0 u - lambda.1 * totalMass u)
    (armValue epsilon 1 u - armValue epsilon 0 u - mu.1 * totalMass u) 0
  have heq :
      (armValue epsilon 1 u - armValue epsilon 0 u - lambda.1 * totalMass u) -
        (armValue epsilon 1 u - armValue epsilon 0 u - mu.1 * totalMass u) =
      -(lambda.1 - mu.1) * totalMass u := by ring
  rw [max_comm 0
      (armValue epsilon 1 u - armValue epsilon 0 u - lambda.1 * totalMass u),
    max_comm 0
      (armValue epsilon 1 u - armValue epsilon 0 u - mu.1 * totalMass u)]
  simpa only [add_sub_add_left_eq_sub, heq, abs_mul, abs_neg] using h

/-- The threshold functional at a fixed cell vector is a Lipschitz function
of the threshold on the unit interval. With [the specified inputs and conditions](hyp:epsilon,u), [the stated relationship holds](goal). -/
-- @node: thresholdFunReal_lipschitz_time
lemma thresholdFunReal_lipschitz_time (epsilon : ℝ) (u : Cell → ℝ) :
    LipschitzWith ⟨|totalMass u|, abs_nonneg _⟩
      (fun lambda : Set.Icc (0 : ℝ) 1 => thresholdFunReal epsilon lambda u) := by
  apply LipschitzWith.of_dist_le_mul
  intro lambda mu
  rw [Real.dist_eq]
  change |thresholdFunReal epsilon lambda u - thresholdFunReal epsilon mu u| ≤
    |totalMass u| * |(lambda : ℝ) - mu|
  simpa only [mul_comm] using
    thresholdFunReal_lambda_lipschitz epsilon u lambda mu

/-- The fixed pilot-radius multiplier. -/
def pilotRadiusConstant : ℝ := 4096
  -- @realizes H_0(fixed multiplier 4096)

/-- The fixed inverse degree multiplier. -/
noncomputable def jacksonDegreeConstant : ℝ := 1 / 512
  -- @realizes \kappa(fixed value 1/512)

/-- The bounded-alphabet cutoff. -/
def boundedAlphabetCutoff : ℕ := 16
  -- @realizes D_0(fixed cutoff 16)

/-- The paper's structural Jackson degree. -/
noncomputable def jacksonDegree (d : ℕ) : ℕ :=
  max 2 ⌊jacksonDegreeConstant * logAlphabet d⌋₊

/-- Poisson pilot or evaluation count for a permuted and marked sample. -/
def markedCellCount {n d : ℕ} (sample : Fin n → Obs d)
    (perm : Equiv.Perm (Fin n)) (M : ℕ) (marks : Fin n → Bool)
    (pilot : Bool) (j : Fin d) (zeta : Cell) : ℕ :=
  ∑ i : Fin n, if i.1 < M ∧ marks i = pilot ∧
      (sample (perm i)).1 = j ∧
      (sample (perm i)).2.1 = finTwoEquiv zeta.1 ∧
      (sample (perm i)).2.2 = finTwoEquiv zeta.2 then 1 else 0

/-- Coordinatewise pilot center. -/
noncomputable def pilotCenter (m : ℝ) (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  (pilot zeta : ℝ) / m

/-- Coordinatewise pilot half-width. -/
noncomputable def pilotHalfWidth (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  pilotRadiusConstant *
    (Real.sqrt (pilotCenter m pilot zeta * logAlphabet d / m) + logAlphabet d / m)

/-- The lower endpoint, truncated at zero. -/
noncomputable def pilotLower (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  max 0 (pilotCenter m pilot zeta - pilotHalfWidth m d pilot zeta)

/-- The upper endpoint. -/
noncomputable def pilotUpper (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  pilotCenter m pilot zeta + pilotHalfWidth m d pilot zeta

/-- Midpoint of the truncated pilot interval. -/
noncomputable def pilotMidpoint (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  (pilotLower m d pilot zeta + pilotUpper m d pilot zeta) / 2

/-- Radius of the truncated pilot interval. -/
noncomputable def pilotRadius (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (zeta : Cell) : ℝ :=
  (pilotUpper m d pilot zeta - pilotLower m d pilot zeta) / 2

/-- The exact tensor convolution of the cell threshold on its pilot rectangle. -/
noncomputable def localJacksonConvolution (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (theta : Fin 4 → ℝ) : ℝ :=
  Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K
    (fun z => thresholdFunReal epsilon lambda
      (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
        (fun i => center (CellFourEquiv.symm i))
        (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c))) theta

/-- If every fixed-threshold pullback is continuous on the normalized cube,
the local Jackson convolution is Lipschitz, hence continuous, in the threshold.
The proof uses only thresholdwise continuity in the integration coordinate. With [the specified inputs and conditions](hyp:epsilon,K,center,radius,theta,hK,hpull), [the stated relationship holds](goal). -/
-- @node: localJacksonConvolution_lipschitz_time
lemma localJacksonConvolution_lipschitz_time (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (theta : Fin 4 → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    ∃ C : NNReal, LipschitzWith C (fun lambda : Set.Icc (0 : ℝ) 1 =>
      localJacksonConvolution epsilon lambda K center radius theta) := by
  let v (u : Fin 4 → ℝ) : Cell → ℝ := fun c =>
    Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
      (fun i => center (CellFourEquiv.symm i))
      (fun i => radius (CellFourEquiv.symm i))
      (Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (theta - u))
      (CellFourEquiv c)
  let kernel (u : Fin 4 → ℝ) : ℝ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson K 4 u
  let envelope (u : Fin 4 → ℝ) : ℝ := |totalMass (v u)| * kernel u
  let B : ℝ := ∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
    envelope u
  have hbox : IsCompact
      (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) := by
    change IsCompact {u : Fin 4 → ℝ | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi}
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hcos : Continuous (fun u : Fin 4 → ℝ =>
      Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint (theta - u)) := by
    unfold Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint
    fun_prop
  have hkernel : Continuous kernel := by
    unfold kernel Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson
    fun_prop
  have henv : Continuous envelope := by
    unfold envelope v totalMass armMassFn
    unfold Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
    fun_prop
  have henvInt : IntegrableOn envelope
      (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) :=
    henv.continuousOn.integrableOn_compact hbox
  have hB : 0 ≤ B := by
    apply integral_nonneg
    intro u
    exact mul_nonneg (abs_nonneg _) <|
      Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_nonneg hK u
  refine ⟨⟨B, hB⟩, LipschitzWith.of_dist_le_mul fun lambda mu => ?_⟩
  have hfInt (t : Set.Icc (0 : ℝ) 1) : IntegrableOn
      (fun u => thresholdFunReal epsilon t (v u) * kernel u)
      (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) := by
    have ht : ContinuousOn (fun u => thresholdFunReal epsilon t (v u))
        (Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4) := by
      apply (hpull t).comp hcos.continuousOn
      intro u hu
      exact Causalean.Mathlib.Analysis.JacksonApproximation.cosPoint_mem_normalizedCube _
    exact (ht.mul hkernel.continuousOn).integrableOn_compact hbox
  change dist
      (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
        thresholdFunReal epsilon lambda (v u) * kernel u)
      (∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
        thresholdFunReal epsilon mu (v u) * kernel u) ≤
      B * dist lambda mu
  rw [Real.dist_eq, ← integral_sub (hfInt lambda) (hfInt mu)]
  calc
    |∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
        (thresholdFunReal epsilon lambda (v u) * kernel u -
          thresholdFunReal epsilon mu (v u) * kernel u)| ≤
        ∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
          |thresholdFunReal epsilon lambda (v u) * kernel u -
            thresholdFunReal epsilon mu (v u) * kernel u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in Causalean.Mathlib.Analysis.JacksonApproximation.periodBox 4,
          (|(lambda : ℝ) - mu| * envelope u) := by
      apply integral_mono
      · exact (hfInt lambda).sub (hfInt mu) |>.abs
      · exact henvInt.const_mul _
      · intro u
        have hk := Causalean.Mathlib.Analysis.JacksonApproximation.tensorJackson_nonneg hK u
        have ht := thresholdFunReal_lambda_lipschitz epsilon (v u) lambda mu
        dsimp [envelope, kernel]
        rw [← sub_mul, abs_mul, abs_of_nonneg hk]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ht hk
    _ = |(lambda : ℝ) - mu| * B := by rw [integral_const_mul]
    _ = B * dist lambda mu := by
      change |(lambda : ℝ) - mu| * B = B * |(lambda : ℝ) - mu|
      ring

/-- The local Jackson convolution is continuous in the threshold under the
same pointwise pullback regularity used to construct its polynomial. With [the specified inputs and conditions](hyp:epsilon,K,center,radius,theta,hK,hpull), [the stated relationship holds](goal). -/
-- @node: localJacksonConvolution_continuous_time
lemma localJacksonConvolution_continuous_time (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (theta : Fin 4 → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      localJacksonConvolution epsilon lambda K center radius theta) := by
  obtain ⟨C, hC⟩ := localJacksonConvolution_lipschitz_time
    epsilon K center radius theta hK hpull
  exact hC.continuous

/-- The normalized tensor convolution has a monomial polynomial representative
when its pullback is continuous on the normalized cube. With [the specified inputs and conditions](hyp:epsilon,lambda,K,center,radius,hK,hcont), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_exists
lemma localJacksonPolynomial_exists (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hcont : ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    ∃ q : MvPolynomial (Fin 4) ℝ,
      (∀ theta : Fin 4 → ℝ,
        MvPolynomial.eval (fun i => Real.cos (theta i)) q =
          localJacksonConvolution epsilon lambda K center radius theta -
            thresholdFunReal epsilon lambda center) ∧
      (∀ i, q.degreeOf i ≤ 2 * (K - 1)) := by
  let f : (Fin 4 → ℝ) → ℝ := fun z => thresholdFunReal epsilon lambda
    (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
      (fun i => center (CellFourEquiv.symm i))
      (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c))
  obtain ⟨p, hp, hsupport, _⟩ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution_exists_mvPolynomial
      hK f hcont
  refine ⟨p - MvPolynomial.C (thresholdFunReal epsilon lambda center), ?_, ?_⟩
  · intro theta
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_C]
    change MvPolynomial.eval (fun i => Real.cos (theta i)) p - _ =
      Causalean.Mathlib.Analysis.JacksonApproximation.tensorConvolution K f theta - _
    rw [← hp theta]
    rfl
  · intro i
    have hdeg : p.degreeOf i ≤ 2 * (K - 1) := by
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro m hm
      exact hsupport m hm i
    have hc : (MvPolynomial.C (thresholdFunReal epsilon lambda center) :
        MvPolynomial (Fin 4) ℝ).degreeOf i ≤ 2 * (K - 1) := by simp
    exact (MvPolynomial.degreeOf_sub_le i p _).trans (max_le hdeg hc)

/-- A canonical normalized polynomial obtained by choice from the Jackson construction.
It defaults to zero outside the degree and continuity domain of that construction. -/
noncomputable def localJacksonPolynomial (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) : MvPolynomial (Fin 4) ℝ :=
  letI := Classical.propDecidable
  if hK : 0 < K then
    if hcont : ContinuousOn
        (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
          (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
        (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) then
      Classical.choose (localJacksonPolynomial_exists epsilon lambda K center radius hK hcont)
    else 0
  else 0

/-- On the Jackson construction domain, the chosen local polynomial has the
required coordinatewise degree. With [the specified inputs and conditions](hyp:epsilon,lambda,K,center,radius,hK,hcont,i), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_degreeOf_le
lemma localJacksonPolynomial_degreeOf_le (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hcont : ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (i : Fin 4) :
    (localJacksonPolynomial epsilon lambda K center radius).degreeOf i ≤
      2 * (K - 1) := by
  unfold localJacksonPolynomial
  simp only [dif_pos hK, dif_pos hcont]
  exact (Classical.choose_spec
    (localJacksonPolynomial_exists epsilon lambda K center radius hK hcont)).2 i

/-- On the Jackson construction domain, evaluating the chosen polynomial on
the cosine cube recovers the centered tensor convolution. With [the specified inputs and conditions](hyp:epsilon,lambda,K,center,radius,hK,hcont,theta), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_eval_cos
lemma localJacksonPolynomial_eval_cos (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hcont : ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (theta : Fin 4 → ℝ) :
    MvPolynomial.eval (fun i => Real.cos (theta i))
        (localJacksonPolynomial epsilon lambda K center radius) =
      localJacksonConvolution epsilon lambda K center radius theta -
        thresholdFunReal epsilon lambda center := by
  unfold localJacksonPolynomial
  simp only [dif_pos hK, dif_pos hcont]
  exact (Classical.choose_spec
    (localJacksonPolynomial_exists epsilon lambda K center radius hK hcont)).1 theta

/-- At each fixed point of the normalized cube, the chosen local Jackson
polynomial has a continuous evaluation path in the threshold. With [the specified inputs and conditions](hyp:epsilon,K,center,radius,hK,hpull,x,hx), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_eval_continuous_time
lemma localJacksonPolynomial_eval_continuous_time (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (x : Fin 4 → ℝ)
    (hx : x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda K center radius)) := by
  let theta : Fin 4 → ℝ := fun i => Real.arccos (x i)
  have hcos : (fun i => Real.cos (theta i)) = x := by
    funext i
    exact Real.cos_arccos (hx i).1 (hx i).2
  have heq : (fun lambda : Set.Icc (0 : ℝ) 1 =>
      MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda K center radius)) =
      fun lambda : Set.Icc (0 : ℝ) 1 =>
        localJacksonConvolution epsilon lambda K center radius theta -
        thresholdFunReal epsilon lambda center := by
    funext lambda
    rw [← hcos]
    exact localJacksonPolynomial_eval_cos epsilon lambda K center radius hK
      (hpull lambda) theta
  rw [heq]
  exact (localJacksonConvolution_continuous_time epsilon K center radius theta hK hpull).sub
    (thresholdFunReal_continuous_time epsilon center)

/-- At every fixed point of the normalized cube, evaluation of the chosen
local Jackson polynomial is Lipschitz in the threshold. With [the specified inputs and conditions](hyp:epsilon,K,center,radius,hK,hpull,x,hx), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_eval_lipschitz_time
lemma localJacksonPolynomial_eval_lipschitz_time (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (x : Fin 4 → ℝ)
    (hx : x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
    ∃ C : NNReal, LipschitzWith C (fun lambda : Set.Icc (0 : ℝ) 1 =>
      MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda K center radius)) := by
  let theta : Fin 4 → ℝ := fun i => Real.arccos (x i)
  have hcos : (fun i => Real.cos (theta i)) = x := by
    funext i
    exact Real.cos_arccos (hx i).1 (hx i).2
  obtain ⟨C, hC⟩ := localJacksonConvolution_lipschitz_time
    epsilon K center radius theta hK hpull
  let T : NNReal := ⟨|totalMass center|, abs_nonneg _⟩
  refine ⟨C + T, ?_⟩
  have heq : (fun lambda : Set.Icc (0 : ℝ) 1 =>
      MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda K center radius)) =
      fun lambda : Set.Icc (0 : ℝ) 1 =>
        localJacksonConvolution epsilon lambda K center radius theta -
          thresholdFunReal epsilon lambda center := by
    funext lambda
    rw [← hcos]
    exact localJacksonPolynomial_eval_cos epsilon lambda K center radius hK
      (hpull lambda) theta
  rw [heq]
  exact hC.sub (thresholdFunReal_lipschitz_time epsilon center)

/-- The normalized monomial coefficient. -/
noncomputable def jacksonCoefficient (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (alpha : Fin 4 → ℕ) : ℝ :=
  (localJacksonPolynomial epsilon lambda K center radius).coeff
    (Finsupp.equivFunOnFinite.symm alpha)

/-- A bounded multi-index Jackson coefficient is the corresponding fixed
tensor-basis coefficient of the local polynomial. With [the specified inputs and conditions](hyp:D,epsilon,lambda,K,center,radius,a), [the stated relationship holds](goal). -/
-- @node: jacksonCoefficient_eq_tensorCoeffs
lemma jacksonCoefficient_eq_tensorCoeffs {D : ℕ} (epsilon lambda : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (a : Fin 4 → Fin (D + 1)) :
    jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs
        (D := D) (localJacksonPolynomial epsilon lambda K center radius) a := by
  rfl

/-- Continuous fixed-grid evaluations remove the apparent incoherence of the
pointwise chosen Jackson representatives: every bounded coefficient then
varies continuously with the threshold. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,hgrid,a), [the stated relationship holds](goal). -/
-- @node: jacksonCoefficient_continuous_time_of_grid
lemma jacksonCoefficient_continuous_time_of_grid {D : ℕ} (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D)
    (hgrid : ∀ a : Fin 4 → Fin (D + 1),
      Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
        MvPolynomial.eval (fun i => (a i : ℝ))
          (localJacksonPolynomial epsilon lambda K center radius)))
    (a : Fin 4 → Fin (D + 1)) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ))) := by
  change Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs
      (D := D) (localJacksonPolynomial epsilon lambda K center radius) a)
  apply Causalean.Mathlib.Analysis.Approximation.Chebyshev.continuous_tensorCoeffs_of_grid
    (fun lambda : Set.Icc (0 : ℝ) 1 =>
      localJacksonPolynomial epsilon lambda K center radius)
  · intro lambda i
    exact (localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
      (hpull lambda) i).trans hD
  · exact hgrid

/-- Every bounded coefficient of the local Jackson polynomial varies
continuously with the threshold. The proof recovers it from a fixed finite
tensor grid lying inside the normalized cube. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,a), [the stated relationship holds](goal). -/
-- @node: jacksonCoefficient_continuous_time
lemma jacksonCoefficient_continuous_time {D : ℕ} (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (a : Fin 4 → Fin (D + 1)) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ))) := by
  let p : Set.Icc (0 : ℝ) 1 → MvPolynomial (Fin 4) ℝ := fun lambda =>
    localJacksonPolynomial epsilon lambda K center radius
  have hdeg (lambda : Set.Icc (0 : ℝ) 1) (i : Fin 4) :
      (p lambda).degreeOf i ≤ D :=
    (localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
      (hpull lambda) i).trans hD
  have heq : (fun lambda : Set.Icc (0 : ℝ) 1 =>
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ))) =
      fun lambda => ∑ b : Fin 4 → Fin (D + 1),
        Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorGridWeight a b *
          MvPolynomial.eval
            (Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorGridPoint b)
            (p lambda) := by
    funext lambda
    rw [jacksonCoefficient_eq_tensorCoeffs]
    exact Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorGrid_coeff_recovery
      (p lambda) (hdeg lambda) a
  rw [heq]
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul
    (localJacksonPolynomial_eval_continuous_time epsilon K center radius hK hpull _
      (Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorGridPoint_mem_cube b))

/-- Every fixed evaluation of the degree-bounded local Jackson polynomial is
continuous in the threshold. In particular, this supplies the integer-grid
premise used by the generic tensor coefficient path API. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,y), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_fixed_eval_continuous_time
lemma localJacksonPolynomial_fixed_eval_continuous_time {D : ℕ} (epsilon : ℝ)
    (K : ℕ) (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (y : Fin 4 → ℝ) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      MvPolynomial.eval y
        (localJacksonPolynomial epsilon lambda K center radius)) := by
  let p : Set.Icc (0 : ℝ) 1 → MvPolynomial (Fin 4) ℝ := fun lambda =>
    localJacksonPolynomial epsilon lambda K center radius
  have hdeg (lambda : Set.Icc (0 : ℝ) 1) (i : Fin 4) :
      (p lambda).degreeOf i ≤ D :=
    (localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
      (hpull lambda) i).trans hD
  have hformula (lambda : Set.Icc (0 : ℝ) 1) :
      MvPolynomial.eval y (p lambda) =
        ∑ a : Fin 4 → Fin (D + 1),
          Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs
            (D := D) (p lambda) a *
            ∏ i : Fin 4, y i ^ (a i : ℕ) := by
    calc
      _ = MvPolynomial.eval y
          (Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorPolynomial
            (Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs
              (D := D) (p lambda))) := by
        rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorPolynomial_tensorCoeffs
          (p lambda) (hdeg lambda)]
      _ = _ := by
        unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorPolynomial
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [MvPolynomial.eval_monomial]
        congr 1
        rw [Finsupp.prod_fintype _ _ (by simp)]
        simp [Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorExponent]
  rw [show (fun lambda : Set.Icc (0 : ℝ) 1 => MvPolynomial.eval y (p lambda)) =
      fun lambda => ∑ a : Fin 4 → Fin (D + 1),
        Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs
          (D := D) (p lambda) a * ∏ i : Fin 4, y i ^ (a i : ℕ) by
    funext lambda
    exact hformula lambda]
  apply continuous_finsetSum
  intro a ha
  exact (jacksonCoefficient_continuous_time epsilon K center radius hK hpull hD a).mul
    continuous_const

/-- Centered factorial polynomial for a single count and monomial degree. -/
noncomputable def centeredFactorial (m z : ℝ) (N h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1),
    (h.choose t : ℝ) * (-z) ^ (h - t) * (N.descFactorial t : ℝ) / m ^ t

/-- The uncapped polynomial statistic for one cell and one shadow price. -/
noncomputable def jacksonCellRaw (epsilon lambda m : ℝ) (d : ℕ)
    (pilot eval : Cell → ℕ) : ℝ :=
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  let K := jacksonDegree d
  thresholdFunReal epsilon lambda center +
    ∑ alpha : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoefficient epsilon lambda K center radius (fun i => (alpha i : ℕ)) *
        ∏ i : Fin 4,
          centeredFactorial m (center (CellFourEquiv.symm i))
            (eval (CellFourEquiv.symm i)) (alpha i : ℕ) /
            radius (CellFourEquiv.symm i) ^ (alpha i : ℕ)

/-- The clipped cellwise Jackson-factorial statistic. -/
noncomputable def jacksonCellStatistic (epsilon lambda m : ℝ) (d : ℕ)
    (pilot eval : Cell → ℕ) : ℝ :=
  let center := pilotMidpoint m d pilot
  let scale := (d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta : Cell, pilotRadius m d pilot zeta
  let delta := jacksonCellRaw epsilon lambda m d pilot eval - thresholdFunReal epsilon lambda center
  thresholdFunReal epsilon lambda center + min scale (max (-scale) delta)

/-- Under the same fixed-threshold cube regularity used by the Jackson
construction, the complete clipped cell statistic is continuous in the
threshold. With [the specified inputs and conditions](hyp:epsilon,m,d,pilot,eval,hpull), [the stated relationship holds](goal). -/
-- @node: jacksonCellStatistic_continuous_time
lemma jacksonCellStatistic_continuous_time (epsilon m : ℝ) (d : ℕ)
    (pilot eval : Cell → ℕ)
    (hpull : ∀ lambda : Set.Icc (0 : ℝ) 1, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      jacksonCellStatistic epsilon lambda m d pilot eval) := by
  let K := jacksonDegree d
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  have hK : 0 < K := by
    unfold K jacksonDegree
    omega
  have hcoeff (a : Fin 4 → Fin (2 * (K - 1) + 1)) :
      Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : ℕ))) :=
    jacksonCoefficient_continuous_time epsilon K center radius hK hpull
      (le_refl _) a
  have hraw : Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      jacksonCellRaw epsilon lambda m d pilot eval) := by
    unfold jacksonCellRaw
    change Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
      thresholdFunReal epsilon lambda center +
        ∑ a : Fin 4 → Fin (2 * (K - 1) + 1),
          jacksonCoefficient epsilon lambda K center radius
            (fun i => (a i : ℕ)) * _)
    apply (thresholdFunReal_continuous_time epsilon center).add
    apply continuous_finsetSum
    intro a ha
    exact (hcoeff a).mul continuous_const
  unfold jacksonCellStatistic
  change Continuous (fun lambda : Set.Icc (0 : ℝ) 1 =>
    thresholdFunReal epsilon lambda center +
      min _ (max (-_) (jacksonCellRaw epsilon lambda m d pilot eval -
        thresholdFunReal epsilon lambda center)))
  exact (thresholdFunReal_continuous_time epsilon center).add
    (continuous_const.min (continuous_const.max
      (hraw.sub (thresholdFunReal_continuous_time epsilon center))))

end CausalSmith.Stat.DiscreteBudgetvalueCurve
