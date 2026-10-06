module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CapTransfer
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary

/-! Boundary-adaptive Jackson approximation and scalar cell bias. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.BoundedVariation

set_option maxHeartbeats 3000000 in
-- The affine substitution and normalized-polynomial simplification are elaboration intensive.
/-- The paper's canonical normalized polynomial, after affine substitution,
inherits the promoted physical-coordinate boundary-adaptive estimate. With [the specified inputs and conditions](hyp:epsilon,he,lambda,hlambda,K,hK,center,radius,y,hR,hlower,hy), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_boundary_adaptive
lemma localJacksonPolynomial_boundary_adaptive
    (epsilon : ℝ) (he : 0 < epsilon) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) (K : ℕ) (hK : 0 < K)
    (center radius y : Cell → ℝ) (hR : ∀ zeta, 0 < radius zeta)
    (hlower : ∀ zeta, 0 ≤ center zeta - radius zeta)
    (hy : ∀ zeta, |y zeta - center zeta| ≤ radius zeta) :
    |thresholdFunReal epsilon lambda center +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i))
            (fun i => y (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda K center radius) -
        thresholdFunReal epsilon lambda y| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) * ∑ i : Fin 4,
        (Real.sqrt
            ((y (CellFourEquiv.symm i) -
                (center (CellFourEquiv.symm i) - radius (CellFourEquiv.symm i))) *
              ((center (CellFourEquiv.symm i) + radius (CellFourEquiv.symm i)) -
                y (CellFourEquiv.symm i))) / (K : ℝ) +
          radius (CellFourEquiv.symm i) / (K : ℝ) ^ 2) := by
  classical
  let c : Fin 4 → ℝ := fun i => center (CellFourEquiv.symm i)
  let r : Fin 4 → ℝ := fun i => radius (CellFourEquiv.symm i)
  let yy : Fin 4 → ℝ := fun i => y (CellFourEquiv.symm i)
  let f : (Fin 4 → ℝ) → ℝ := fun u =>
    thresholdFunReal epsilon lambda (fun zeta => u (CellFourEquiv zeta))
  let L : ℝ := 3 * (1 + epsilon⁻¹) + 1
  let q : MvPolynomial (Fin 4) ℝ :=
    localJacksonPolynomial epsilon lambda K center radius +
      MvPolynomial.C (thresholdFunReal epsilon lambda center)
  have hr : ∀ i, 0 < r i := fun i => hR (CellFourEquiv.symm i)
  have hrect_nonneg {u : Fin 4 → ℝ} (hu : u ∈ centeredRectangle c r) (i : Fin 4) :
      0 ≤ u i := by
    have hlo := hlower (CellFourEquiv.symm i)
    have hui := hu i
    dsimp [c, r] at hlo hui
    have hleft := (abs_le.mp hui).1
    linarith
  have hL : 0 ≤ L := by
    dsimp [L]
    have hie : 0 < epsilon⁻¹ := inv_pos.mpr he
    positivity
  have hlip : ∀ u ∈ centeredRectangle c r, ∀ v ∈ centeredRectangle c r,
      |f u - f v| ≤ L * ∑ i, |u i - v i| := by
    intro u hu v hv
    have hb := budget_thresholdFunReal_pointwise_lipschitz he lambda hlambda
      (fun zeta => u (CellFourEquiv zeta))
      (fun zeta => v (CellFourEquiv zeta))
      (fun zeta => hrect_nonneg hu (CellFourEquiv zeta))
      (fun zeta => hrect_nonneg hv (CellFourEquiv zeta))
    have hsum : (∑ zeta : Cell,
        |u (CellFourEquiv zeta) - v (CellFourEquiv zeta)|) =
        ∑ i : Fin 4, |u i - v i| :=
      CellFourEquiv.sum_comp (fun i => |u i - v i|)
    simpa [f, L, hsum] using hb
  have hf : ContinuousOn f (centeredRectangle c r) := by
    have hLip : LipschitzOnWith ⟨4 * L, mul_nonneg (by norm_num) hL⟩ f
        (centeredRectangle c r) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      rw [Real.dist_eq]
      have h := hlip u hu v hv
      apply h.trans
      change L * ∑ i, |u i - v i| ≤ (4 * L) * dist u v
      have hsum : ∑ i : Fin 4, |u i - v i| ≤ 4 * dist u v := by
        calc
          _ ≤ ∑ _i : Fin 4, dist u v := by
            gcongr with i
            simpa [Real.dist_eq] using dist_le_pi_dist u v i
          _ = 4 * dist u v := by simp
      nlinarith
    exact hLip.continuousOn
  have hpull : ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun zeta => affinePoint c r z (CellFourEquiv zeta)))
      (normalizedCube 4) := by
    have haff : Continuous (affinePoint c r) := by
      apply continuous_pi
      intro i
      exact continuous_const.add (continuous_const.mul (continuous_apply i))
    exact hf.comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle c r z hr hz)
  have hqeval (x : Fin 4 → ℝ) :
      MvPolynomial.eval (cosPoint x) q =
        tensorConvolution K (fun z => f (affinePoint c r z)) x := by
    rw [show MvPolynomial.eval (cosPoint x) q =
        MvPolynomial.eval (cosPoint x)
            (localJacksonPolynomial epsilon lambda K center radius) +
          thresholdFunReal epsilon lambda center by simp [q]]
    have heval := localJacksonPolynomial_eval_cos epsilon lambda K center radius hK
      (by simpa [c, r, affinePoint] using hpull) x
    change MvPolynomial.eval (fun i => Real.cos (x i))
        (localJacksonPolynomial epsilon lambda K center radius) +
          thresholdFunReal epsilon lambda center = _
    rw [heval]
    simp [localJacksonConvolution, f, c, r, affinePoint]
  have hqcoord : ∀ m ∈ q.support, ∀ i, m i ≤ 2 * (K - 1) := by
    intro m hm i
    apply (MvPolynomial.monomial_le_degreeOf i hm).trans
    refine (MvPolynomial.degreeOf_add_le i _ _).trans (max_le ?_ ?_)
    · exact localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
        (by simpa [c, r] using hpull) i
    · simp
  obtain ⟨p, hpeval, _, _, _⟩ :=
    mvPolynomial_affine_substitution_four q c r (2 * (K - 1)) hr hqcoord
  have hyy : yy ∈ centeredRectangle c r := by
    intro i
    exact hy (CellFourEquiv.symm i)
  have happ := affineJackson_boundary_adaptive_four hK c r hr f hf L hL hlip
    p q hpeval hqeval yy hyy
  rw [hpeval yy] at happ
  simpa [c, r, yy, f, q, L, add_assoc, add_comm, add_left_comm] using happ

/-- On a good pilot cell, the promoted boundary-adaptive estimate applies at
the true four-cell vector, including coordinates of zero mass. With [the specified inputs and conditions](hyp:n,d,epsilon,he,lambda,hlambda,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: goodPilot_localJacksonPolynomial_boundary_adaptive
lemma goodPilot_localJacksonPolynomial_boundary_adaptive
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d)
    (hgood : idealPilotGood (n := n) P counts j) :
    let m : ℝ := (n : ℝ) / 8
    let center := pilotMidpoint m d (counts.1 j)
    let radius := pilotRadius m d (counts.1 j)
    let q := cellVector P j
    |thresholdFunReal epsilon lambda center +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i))
            (fun i => q (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d) center radius) -
        thresholdFunReal epsilon lambda q| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) * ∑ i : Fin 4,
        (Real.sqrt
            ((q (CellFourEquiv.symm i) -
                (center (CellFourEquiv.symm i) - radius (CellFourEquiv.symm i))) *
              ((center (CellFourEquiv.symm i) + radius (CellFourEquiv.symm i)) -
                q (CellFourEquiv.symm i))) / (jacksonDegree d : ℝ) +
          radius (CellFourEquiv.symm i) / (jacksonDegree d : ℝ) ^ 2) := by
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let center := pilotMidpoint m d (counts.1 j)
  let radius := pilotRadius m d (counts.1 j)
  have hm : 0 < m := by dsimp [m]; positivity
  have hR : ∀ zeta, 0 < radius zeta := fun zeta => by
    exact pilotRadius_pos_of_pos hm hd (counts.1 j) zeta
  have hlower : ∀ zeta, 0 ≤ center zeta - radius zeta := fun zeta => by
    dsimp [center, radius]
    unfold pilotMidpoint pilotRadius
    have hlo : 0 ≤ pilotLower m d (counts.1 j) zeta := le_max_left _ _
    linarith
  exact localJacksonPolynomial_boundary_adaptive epsilon he lambda hlambda
    (jacksonDegree d) (by unfold jacksonDegree; omega) center radius
    (cellVector P j) hR hlower
    (idealPilotGood_center_mem_radius hn P counts j hgood)

/-- The boundary-adaptive Jackson remainder on a good pilot cell is bounded
by the pilot radius sum times the usual first and second degree factors. With [the specified inputs and conditions](hyp:n,d,epsilon,he,lambda,hlambda,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: goodPilot_localJacksonPolynomial_boundary_le_radiusSum
lemma goodPilot_localJacksonPolynomial_boundary_le_radiusSum
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (lambda : Real)
    (hlambda : lambda ∈ Set.Icc (0 : Real) 1) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → Nat) × (Fin d → Cell → Nat)) (j : Fin d)
    (hgood : idealPilotGood (n := n) P counts j) :
    let m : Real := (n : Real) / 8
    let center := pilotMidpoint m d (counts.1 j)
    let radius := pilotRadius m d (counts.1 j)
    let q := cellVector P j
    |thresholdFunReal epsilon lambda center +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i))
            (fun i => q (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d) center radius) -
        thresholdFunReal epsilon lambda q| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (2 / (jacksonDegree d : Real) + 1 / (jacksonDegree d : Real) ^ 2) *
        ∑ zeta : Cell, radius zeta := by
  dsimp only
  let m : Real := (n : Real) / 8
  let center := pilotMidpoint m d (counts.1 j)
  let radius := pilotRadius m d (counts.1 j)
  let q := cellVector P j
  let K : Real := jacksonDegree d
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (show 0 < jacksonDegree d by unfold jacksonDegree; omega)
  have hr (zeta : Cell) : 0 ≤ radius zeta := by
    exact (pilotRadius_pos_of_pos (by dsimp [m]; positivity) hd (counts.1 j) zeta).le
  have hmem := idealPilotGood_center_mem_radius hn P counts j hgood
  have hterm (i : Fin 4) :
      Real.sqrt
          ((q (CellFourEquiv.symm i) -
              (center (CellFourEquiv.symm i) - radius (CellFourEquiv.symm i))) *
            ((center (CellFourEquiv.symm i) + radius (CellFourEquiv.symm i)) -
              q (CellFourEquiv.symm i))) / K +
        radius (CellFourEquiv.symm i) / K ^ 2 ≤
      (2 / K + 1 / K ^ 2) * radius (CellFourEquiv.symm i) := by
    let zeta := CellFourEquiv.symm i
    have habs := abs_le.mp (hmem zeta)
    have ha : 0 ≤ q zeta - (center zeta - radius zeta) := by linarith
    have hb : 0 ≤ (center zeta + radius zeta) - q zeta := by linarith
    have ha' : q zeta - (center zeta - radius zeta) ≤ 2 * radius zeta := by
      linarith
    have hb' : (center zeta + radius zeta) - q zeta ≤ 2 * radius zeta := by
      linarith
    have hprod : (q zeta - (center zeta - radius zeta)) *
        ((center zeta + radius zeta) - q zeta) ≤ (2 * radius zeta) ^ 2 := by
      simpa [pow_two] using mul_le_mul ha' hb' hb
        (mul_nonneg (by norm_num) (hr zeta))
    have hsqrt : Real.sqrt ((q zeta - (center zeta - radius zeta)) *
        ((center zeta + radius zeta) - q zeta)) ≤ 2 * radius zeta := by
      exact (Real.sqrt_le_iff).2 ⟨mul_nonneg (by norm_num) (hr zeta),
        by simpa using hprod⟩
    dsimp only [zeta] at hsqrt ⊢
    calc
      _ ≤ (2 * radius (CellFourEquiv.symm i)) / K +
          radius (CellFourEquiv.symm i) / K ^ 2 := by
        gcongr
      _ = _ := by ring
  have hbase := goodPilot_localJacksonPolynomial_boundary_adaptive epsilon he
    lambda hlambda hn hd P counts j hgood
  calc
    _ ≤ 32 * (3 * (1 + epsilon⁻¹) + 1) * ∑ i : Fin 4,
        (Real.sqrt
            ((q (CellFourEquiv.symm i) -
                (center (CellFourEquiv.symm i) - radius (CellFourEquiv.symm i))) *
              ((center (CellFourEquiv.symm i) + radius (CellFourEquiv.symm i)) -
                q (CellFourEquiv.symm i))) / K +
          radius (CellFourEquiv.symm i) / K ^ 2) := by
      simpa [m, center, radius, q, K] using hbase
    _ ≤ 32 * (3 * (1 + epsilon⁻¹) + 1) *
        ∑ i : Fin 4, (2 / K + 1 / K ^ 2) * radius (CellFourEquiv.symm i) := by
      gcongr with i
      exact hterm i
    _ = _ := by
      rw [← Finset.mul_sum]
      rw [CellFourEquiv.symm.sum_comp]
      simp [K, radius, m]
      ring

/-- Projection onto a symmetric interval differs from its input by at most
the input square divided by the positive clipping radius. With [the specified inputs and conditions](hyp:t,x,ht), [the stated relationship holds](goal). -/
-- @node: scalarClip_sub_le_sq_div
lemma scalarClip_sub_le_sq_div (t x : ℝ) (ht : 0 < t) :
    |Causalean.Stat.Concentration.BoundedVariation.scalarClip t x - x| ≤
      x ^ 2 / t := by
  unfold Causalean.Stat.Concentration.BoundedVariation.scalarClip
  by_cases hxlow : x < -t
  · rw [max_eq_left (le_of_lt hxlow), min_eq_right (by linarith),
      abs_of_nonneg (by linarith)]
    have hs := sq_nonneg (x + t)
    apply (le_div_iff₀ ht).2
    nlinarith
  · have hxlow' : -t ≤ x := le_of_not_gt hxlow
    rw [max_eq_right hxlow']
    by_cases hxhigh : x ≤ t
    · rw [min_eq_right hxhigh, sub_self, abs_zero]
      positivity
    · have hxhigh' : t < x := lt_of_not_ge hxhigh
      rw [min_eq_left (le_of_lt hxhigh'), abs_of_nonpos (by linarith)]
      have hs := sq_nonneg (x - t)
      apply (le_div_iff₀ ht).2
      nlinarith

set_option maxHeartbeats 600000 in
-- Unfolding the finite factorial polynomial requires additional elaboration budget.
/-- A centered normalized factorial lift has a finite first absolute moment
under every Poisson law. With [the specified inputs and conditions](hyp:rate,m,z,h), [the stated relationship holds](goal). -/
-- @node: poisson_factorialLift_integrable_run
lemma poisson_factorialLift_integrable_run (rate : NNReal) (m z : ℝ) (h : ℕ) :
    Integrable (fun N : ℕ => factorialLift m z N h) (poissonMeasure rate) := by
  unfold factorialLift
  apply integrable_finsetSum
  intro t ht
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (poisson_descFactorial_integrable rate t).const_mul
      ((h.choose t : ℝ) * (-z) ^ (h - t) * (m ^ t)⁻¹)

/-- A finite product of centered factorial lifts is integrable under
independent Poisson coordinates. With [the specified inputs and conditions](hyp:W,rate,hWlaw,hWindep,m,z,h), [the stated relationship holds](goal). -/
-- @node: factorialProduct_integrable_run
lemma factorialProduct_integrable_run
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω → ℕ)
    (rate : ι → NNReal) (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m : ℝ) (z : ι → ℝ) (h : ι → ℕ) :
    Integrable (factorialProduct W m z h) μ := by
  let X : Ω → (ι → ℕ) := fun omega i => W i omega
  let F : (ι → ℕ) → ℝ := fun x => ∏ i, factorialLift m (z i) (x i) (h i)
  have hF : Integrable F (Measure.pi fun i => poissonMeasure (rate i)) := by
    exact Integrable.fintype_prod fun i =>
      poisson_factorialLift_integrable_run (rate i) m (z i) (h i)
  have hXmeas : AEMeasurable X μ := by
    exact aemeasurable_pi_lambda _ fun i => (hWlaw i).aemeasurable
  have hmap : Measure.map X μ = Measure.pi (fun i => poissonMeasure (rate i)) := by
    calc
      Measure.map X μ = Measure.pi (fun i => Measure.map (W i) μ) := by
        exact hWindep.map_fun_eq_pi_map (fun i => (hWlaw i).aemeasurable)
      _ = Measure.pi (fun i => poissonMeasure (rate i)) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq
  have hFmeas : AEStronglyMeasurable F (Measure.map X μ) := by
    rw [hmap]
    exact hF.1
  have hcomp := (integrable_map_measure hFmeas hXmeas).1 (by simpa [hmap] using hF)
  change Integrable (fun omega => ∏ i, factorialLift m (z i) (W i omega) (h i)) μ
  dsimp only [F, X, Function.comp_apply] at hcomp
  exact hcomp

/-- A product of two falling factorials has a finite Poisson first moment. With [the specified inputs and conditions](hyp:rate,h,t), [the stated relationship holds](goal). -/
-- @node: poisson_descFactorial_mul_integrable_run
lemma poisson_descFactorial_mul_integrable_run (rate : NNReal) (h t : ℕ) :
    Integrable (fun N : ℕ => (N.descFactorial h : ℝ) * N.descFactorial t)
      (poissonMeasure rate) := by
  rw [show (fun N : ℕ => (N.descFactorial h : ℝ) * N.descFactorial t) =
      fun N => ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          (N.descFactorial (h + t - r) : ℝ) by
    funext N
    exact descFactorial_mul N h t]
  apply integrable_finsetSum
  intro r hr
  exact (poisson_descFactorial_integrable rate (h + t - r)).const_mul _

/-- A finite sum is square integrable when every pair of summands has an
integrable product. With [the specified inputs and conditions](hyp:mu,s,f,h), [the stated relationship holds](goal). -/
-- @node: integrable_finsetSum_sq_of_mul
lemma integrable_finsetSum_sq_of_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun omega => f i omega * f j omega) mu) :
    Integrable (fun omega => (∑ i ∈ s, f i omega) ^ 2) mu := by
  rw [show (fun omega => (∑ i ∈ s, f i omega) ^ 2) =
      fun omega => ∑ i ∈ s, ∑ j ∈ s, f i omega * f j omega by
    funext omega
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact h i hi j hj

/-- The square of a centered normalized factorial lift is Poisson integrable. With [the specified inputs and conditions](hyp:rate,m,z,h), [the stated relationship holds](goal). -/
-- @node: poisson_factorialLift_sq_integrable_run
lemma poisson_factorialLift_sq_integrable_run
    (rate : NNReal) (m z : ℝ) (h : ℕ) :
    Integrable (fun N : ℕ => factorialLift m z N h ^ 2) (poissonMeasure rate) := by
  unfold factorialLift
  apply integrable_finsetSum_sq_of_mul (poissonMeasure rate) (Finset.range (h + 1))
  intro t ht s hs
  have hprod := poisson_descFactorial_mul_integrable_run rate t s
  convert hprod.const_mul
    (((h.choose t : ℝ) * (-z) ^ (h - t) / m ^ t) *
      ((h.choose s : ℝ) * (-z) ^ (h - s) / m ^ s)) using 1
  funext N
  ring

/-- A finite product of centered factorial lifts has an integrable square
under independent Poisson coordinates. With [the specified inputs and conditions](hyp:W,rate,hWlaw,hWindep,m,z,h), [the stated relationship holds](goal). -/
-- @node: factorialProduct_sq_integrable_run
lemma factorialProduct_sq_integrable_run
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω → ℕ)
    (rate : ι → NNReal) (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m : ℝ) (z : ι → ℝ) (h : ι → ℕ) :
    Integrable (fun omega => factorialProduct W m z h omega ^ 2) μ := by
  let X : Ω → (ι → ℕ) := fun omega i => W i omega
  let F : (ι → ℕ) → ℝ := fun x =>
    ∏ i, factorialLift m (z i) (x i) (h i) ^ 2
  have hF : Integrable F (Measure.pi fun i => poissonMeasure (rate i)) := by
    exact Integrable.fintype_prod fun i =>
      poisson_factorialLift_sq_integrable_run (rate i) m (z i) (h i)
  have hXmeas : AEMeasurable X μ :=
    aemeasurable_pi_lambda _ fun i => (hWlaw i).aemeasurable
  have hmap : Measure.map X μ = Measure.pi (fun i => poissonMeasure (rate i)) := by
    calc
      Measure.map X μ = Measure.pi (fun i => Measure.map (W i) μ) := by
        exact hWindep.map_fun_eq_pi_map (fun i => (hWlaw i).aemeasurable)
      _ = Measure.pi (fun i => poissonMeasure (rate i)) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq
  have hFmeas : AEStronglyMeasurable F (Measure.map X μ) := by
    rw [hmap]
    exact hF.1
  have hcomp := (integrable_map_measure hFmeas hXmeas).1 (by simpa [hmap] using hF)
  dsimp only [F, X, Function.comp_apply] at hcomp
  have hcomp' : Integrable
      (fun omega => ∏ i, factorialLift m (z i) (W i omega) (h i) ^ 2) μ := by
    exact hcomp
  have heq : (fun omega => factorialProduct W m z h omega ^ 2) =
      fun omega => ∏ i, factorialLift m (z i) (W i omega) (h i) ^ 2 := by
    funext omega
    unfold factorialProduct
    exact (Finset.prod_pow Finset.univ 2
      (fun i => factorialLift m (z i) (W i omega) (h i))).symm
  rw [heq]
  exact hcomp'

/-- The unprojected centered Jackson factorial polynomial has an integrable
square under independent Poisson evaluation counts. With [the specified inputs and conditions](hyp:epsilon,lambda,m,d,pilot,W,rate,hWlaw,hWindep), [the stated relationship holds](goal). -/
-- @node: jacksonCellRaw_centered_sq_integrable
lemma jacksonCellRaw_centered_sq_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (epsilon lambda m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) :
    Integrable (fun omega =>
      (jacksonCellRaw epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) -
          thresholdFunReal epsilon lambda (pilotMidpoint m d pilot)) ^ 2) μ := by
  classical
  let K := jacksonDegree d
  let D := 2 * (K - 1)
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  have hmono (a : Fin 4 → Fin (D + 1)) :
      let M := fun omega => factorialMonomial m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))
      Integrable M μ ∧ Integrable (fun omega => M omega ^ 2) μ := by
    dsimp only
    have hfirst := (factorialProduct_integrable_run μ W rate hWlaw hWindep m
      (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : ℕ))).div_const
        (∏ i, radius (CellFourEquiv.symm i) ^ (a i : ℕ))
    have hsecond := (factorialProduct_sq_integrable_run μ W rate hWlaw hWindep m
      (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : ℕ))).const_mul
        ((∏ i, radius (CellFourEquiv.symm i) ^ (a i : ℕ)) ^ 2)⁻¹
    constructor
    · rw [show (fun omega => factorialMonomial m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) =
          fun omega => factorialProduct W m
            (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : ℕ)) omega /
              ∏ i, radius (CellFourEquiv.symm i) ^ (a i : ℕ) by
          funext omega
          exact factorialMonomial_eq_fourFactorialMonomial m d pilot W a omega]
      exact hfirst
    · convert hsecond using 1
      funext omega
      rw [factorialMonomial_eq_fourFactorialMonomial]
      simp only [fourFactorialMonomial, div_pow]
      dsimp only [center, radius]
      rw [div_eq_mul_inv]
      ring
  have hterm (a : Fin 4 → Fin (D + 1)) : MemLp
      (fun omega =>
        jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) *
          factorialMonomial m d pilot
            (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) 2 μ := by
    have hm := hmono a
    apply (memLp_two_iff_integrable_sq (hm.1.const_mul _).1).2
    convert hm.2.const_mul
      (jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) ^ 2) using 1
    funext omega
    ring
  have hsum : MemLp (fun omega => ∑ a : Fin 4 → Fin (D + 1),
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) *
        factorialMonomial m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) 2 μ := by
    simpa only [Finset.sum_attach] using
      memLp_finsetSum Finset.univ (fun a _ => hterm a)
  have hsquare := (memLp_two_iff_integrable_sq hsum.1).1 hsum
  simpa [jacksonCellRaw, factorialMonomial, K, D, center, radius] using hsquare

set_option maxHeartbeats 1200000 in
-- The expanded finite tensor sum and integral comparison are elaboration intensive.
/-- On a pilot rectangle containing the true normalized rate, the conditional
second moment of the raw Jackson factorial polynomial is controlled by the
coefficient BV envelope and the promoted factorial-product envelope. With [the specified inputs and conditions](hyp:Omega,mu,epsilon,hepsilon,lambda,hlambda,m,L,hm,hL,d,hd,pilot,W,rate,hWlaw,hWindep,hcenter,hvariance), [the stated relationship holds](goal). -/
-- @node: jacksonCellRaw_centered_sq_integral_le
lemma jacksonCellRaw_centered_sq_integral_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (m L : Real) (hm : 0 < m) (hL : 0 < L) (d : Nat) (hd : 1 ≤ d)
    (pilot : Cell → Nat) (W : Fin 4 → Omega → Nat) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) mu)
    (hWindep : iIndepFun W mu)
    (hcenter : ∀ i, |(rate i : Real) / m -
      pilotMidpoint m d pilot (CellFourEquiv.symm i)| ≤
        pilotRadius m d pilot (CellFourEquiv.symm i))
    (hvariance : ∀ i, (rate i : Real) /
      (m ^ 2 * pilotRadius m d pilot (CellFourEquiv.symm i) ^ 2) ≤ 1 / L) :
    (∫ omega, (jacksonCellRaw epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) -
          thresholdFunReal epsilon lambda (pilotMidpoint m d pilot)) ^ 2 ∂mu) ≤
      4 * jacksonCoefficientBV epsilon m d pilot ^ 2 *
        ∑ _a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
          Real.exp (4 * ((2 * (jacksonDegree d - 1) : Nat) : Real) ^ 2 / L) := by
  classical
  let K := jacksonDegree d
  let D := 2 * (K - 1)
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  let hpull := fun t : Time => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := m) (d := d) (pilot := pilot)
    hepsilon hm hd t
  let c : (Fin 4 → Fin (D + 1)) → Path := fun a =>
    localJacksonCoefficientPath epsilon K center radius
      (by dsimp [K]; unfold jacksonDegree; omega) hpull (le_refl D) a
  let X : Omega → (Fin 4 → Fin (D + 1)) → Real := fun omega a =>
    factorialMonomial m d pilot (fun zeta => W (CellFourEquiv zeta) omega)
      (fun i => (a i : Nat))
  have hR (i : Fin 4) : 0 < radius (CellFourEquiv.symm i) := by
    exact pilotRadius_pos_of_pos hm hd pilot _
  have hXint (a : Fin 4 → Fin (D + 1)) :
      Integrable (fun omega => (X omega a) ^ 2) mu := by
    have h := (factorialProduct_sq_integrable_run mu W rate hWlaw hWindep m
      (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : Nat))).const_mul
        ((∏ i, radius (CellFourEquiv.symm i) ^ (a i : Nat)) ^ 2)⁻¹
    convert h using 1
    funext omega
    dsimp only [X]
    rw [factorialMonomial_eq_fourFactorialMonomial]
    simp only [fourFactorialMonomial, div_pow]
    rw [div_eq_mul_inv]
    ring
  have hsumXint : Integrable
      (fun omega => ∑ a : Fin 4 → Fin (D + 1), (X omega a) ^ 2) mu := by
    apply integrable_finsetSum
    intro a ha
    exact hXint a
  have hrawInt : Integrable (fun omega =>
      (jacksonCellRaw epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) -
          thresholdFunReal epsilon lambda center) ^ 2) mu := by
    simpa [center] using jacksonCellRaw_centered_sq_integrable
      mu epsilon lambda m d pilot W rate hWlaw hWindep
  have hcoeffpoint :
      (∑ a : Fin 4 → Fin (D + 1),
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : Nat)) ^ 2) ≤
      ∑ a : Fin 4 → Fin (D + 1), pathSize (c a) ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    have heval : |jacksonCoefficient epsilon lambda K center radius
        (fun i => (a i : Nat))| ≤ pathSize (c a) := by
      calc
        _ = ‖c a ⟨lambda, hlambda⟩‖ := by
          simp [c, localJacksonCoefficientPath]
        _ ≤ ‖c a‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ pathSize (c a) := by
          unfold pathSize
          exact le_add_of_nonneg_right (pathTV_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) heval 2
  have hcoeffBV :
      (∑ a : Fin 4 → Fin (D + 1),
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : Nat)) ^ 2) ≤
        4 * jacksonCoefficientBV epsilon m d pilot ^ 2 := by
    exact hcoeffpoint.trans (by
      simpa [c, K, D, center, radius, hpull] using
        localJacksonCoefficientPath_sq_sum_le_jacksonCoefficientBV
          epsilon m d pilot (by unfold jacksonDegree; omega) hpull)
  have hpoint (omega : Omega) :
      (jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) -
        thresholdFunReal epsilon lambda center) ^ 2 ≤
      (∑ a : Fin 4 → Fin (D + 1),
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : Nat)) ^ 2) *
      ∑ a : Fin 4 → Fin (D + 1), (X omega a) ^ 2 := by
    rw [show jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) -
          thresholdFunReal epsilon lambda center =
        ∑ a : Fin 4 → Fin (D + 1),
          jacksonCoefficient epsilon lambda K center radius
            (fun i => (a i : Nat)) * X omega a by
      simp [jacksonCellRaw, factorialMonomial, X, K, D, center, radius]]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hfactorInt : Integrable (fun omega =>
      (∑ a : Fin 4 → Fin (D + 1),
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : Nat)) ^ 2) *
      ∑ a : Fin 4 → Fin (D + 1), (X omega a) ^ 2) mu :=
    hsumXint.const_mul _
  calc
    _ ≤ ∫ omega, (∑ a : Fin 4 → Fin (D + 1),
          jacksonCoefficient epsilon lambda K center radius
            (fun i => (a i : Nat)) ^ 2) *
        ∑ a : Fin 4 → Fin (D + 1), (X omega a) ^ 2 ∂mu :=
      integral_mono hrawInt hfactorInt hpoint
    _ = (∑ a : Fin 4 → Fin (D + 1),
          jacksonCoefficient epsilon lambda K center radius
            (fun i => (a i : Nat)) ^ 2) *
        ∑ a : Fin 4 → Fin (D + 1),
          ∫ omega, (X omega a) ^ 2 ∂mu := by
      rw [integral_const_mul, integral_finsetSum]
      exact fun a _ => hXint a
    _ ≤ (4 * jacksonCoefficientBV epsilon m d pilot ^ 2) *
        ∑ _a : Fin 4 → Fin (D + 1),
          Real.exp (4 * (D : Real) ^ 2 / L) := by
      apply mul_le_mul hcoeffBV
      · apply Finset.sum_le_sum
        intro a ha
        exact factorialMonomial_square_envelope mu m L hm hL d pilot W rate
          hWlaw hWindep hR hcenter hvariance a
      · exact Finset.sum_nonneg fun a _ => integral_nonneg fun omega => sq_nonneg _
      · positivity
    _ = _ := by rfl

/-- The paper's choice of Jackson degree absorbs the factorial index count,
coefficient growth, and factorial square moment into `d^(1/16)`. With [the specified inputs and conditions](hyp:d,hd,B,C,S,hC,hS,hB,hcoeff), [the stated relationship holds](goal). -/
-- @node: jacksonRaw_factorial_envelope_absorb
lemma jacksonRaw_factorial_envelope_absorb
    {d : Nat} (hd : 16 ≤ d) (B C S : Real) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hB : 0 ≤ B)
    (hcoeff : B ≤ C * S * Real.exp (12 * jacksonDegree d)) :
    (4 * B ^ 2) *
        ∑ _a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
          Real.exp (4 * ((2 * (jacksonDegree d - 1) : Nat) : Real) ^ 2 /
            logAlphabet d) ≤
      4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) * S ^ 2 := by
  let K := jacksonDegree d
  let L := logAlphabet d
  have hL : 0 < L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hd1 : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg hd1]
  have hcoeff' : B ^ 2 ≤ C ^ 2 * S ^ 2 * Real.exp (24 * K) := by
    have hrhs0 : 0 ≤ C * S * Real.exp (12 * K) := by positivity
    have hsquare := (sq_le_sq₀ hB hrhs0).mpr (by
      simpa [K] using hcoeff)
    calc
      _ ≤ (C * S * Real.exp (12 * K)) ^ 2 := hsquare
      _ = C ^ 2 * S ^ 2 * Real.exp (24 * K) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hsum :
      (∑ _a : Fin 4 → Fin (2 * (K - 1) + 1),
        Real.exp (4 * ((2 * (K - 1) : Nat) : Real) ^ 2 / L)) ≤
      ((2 * (K - 1) + 1 : Nat) : Real) ^ 4 *
        Real.exp (16 * (K : Real) ^ 2 / L) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Fintype.card
        (Fin 4 → Fin (2 * (K - 1) + 1)) : Nat) : Real) =
        ((2 * (K - 1) + 1 : Nat) : Real) ^ 4 := by
      rw [Fintype.card_fun]
      simp
    rw [Finset.card_univ, hcard]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hsub : ((K - 1 : Nat) : Real) ≤ K := by
      exact_mod_cast Nat.sub_le K 1
    have hsq : ((2 * (K - 1) : Nat) : Real) ^ 2 ≤ 4 * (K : Real) ^ 2 := by
      push_cast
      nlinarith [sq_nonneg ((K - 1 : Nat) : Real), sq_nonneg (K : Real)]
    apply (div_le_div_iff_of_pos_right hL).2
    nlinarith
  have habsorb := jacksonDegree_factorial_index_exponential_budget d hd
  calc
    _ ≤ (4 * (C ^ 2 * S ^ 2 * Real.exp (24 * K))) *
        (((2 * (K - 1) + 1 : Nat) : Real) ^ 4 *
          Real.exp (16 * (K : Real) ^ 2 / L)) := by gcongr
    _ ≤ 4 * C ^ 2 * S ^ 2 *
        (Real.exp 123 * (d : Real) ^ (1 / 16 : Real)) := by
      calc
        _ = 4 * C ^ 2 * S ^ 2 *
            (((2 * (K - 1) + 1 : Nat) : Real) ^ 4 *
              Real.exp (24 * K + 16 * (K : Real) ^ 2 / L)) := by
          rw [Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [K, L] using habsorb)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) (sq_nonneg S))
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
-- The conditional Poisson table law and exponential absorption are elaboration intensive.
/-- Equation (23)'s raw conditional second-moment input, for a fixed good
pilot table and one evaluation cell. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood), [the shadow-price range](hyp:hlambda), [the positive envelope constant](hyp:hC), and [the coefficient envelope](hyp:hcoeff). -/
-- @node: goodPilot_jacksonCellRaw_centered_sq_integral_le
lemma goodPilot_jacksonCellRaw_centered_sq_integral_le
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → Nat) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (C : Real) (hC : 0 ≤ C)
    (hcoeff : jacksonCoefficientBV epsilon ((n : Real) / 8) d
        (curryCountTable p j) ≤
      C * (∑ zeta : Cell,
        pilotRadius ((n : Real) / 8) d (curryCountTable p j) zeta) *
        Real.exp (12 * jacksonDegree d)) :
    let m : Real := (n : Real) / 8
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
      fun i e => poissonTableCell j e i
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    (∫ e, (jacksonCellRaw epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) e) -
          thresholdFunReal epsilon lambda (pilotMidpoint m d pilot)) ^ 2 ∂mu) ≤
      4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2 := by
  dsimp only
  let m : Real := (n : Real) / 8
  let L := logAlphabet d
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) mu := by
    simpa [W, mu, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) p (j, i)
  have hWindep : iIndepFun W mu := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) mu = poissonTableLaw (rate j) := by
        simpa [W, mu] using (poissonTable_eval_cell_law rate rate p j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) mu) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have hL : 0 < L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hd1 : (1 : Real) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg hd1]
  have hraw := jacksonCellRaw_centered_sq_integral_le mu epsilon he lambda hlambda
    m L (by dsimp [m]; positivity) hL d (show 1 ≤ d by omega) pilot W (rate j)
    hWlaw hWindep
    (fun i => idealPilotGood_flatRate_center_mem_radius hn P
      (curryCountTable p, fun _ _ => 0) j hgood i)
    (fun i => idealPilotGood_rate_div_radius_sq hn hd P
      (curryCountTable p, fun _ _ => 0) j hgood i)
  let S := ∑ zeta : Cell, pilotRadius m d pilot zeta
  have hS : 0 ≤ S := Finset.sum_nonneg fun z _ =>
    (pilotRadius_pos_of_pos (by dsimp [m]; positivity)
      (show 1 ≤ d by omega) pilot z).le
  exact hraw.trans (by
    simpa [m, L, rate, mu, pilot, W, S] using
      jacksonRaw_factorial_envelope_absorb hd
        (jacksonCoefficientBV epsilon m d pilot) C S hC hS
        (by unfold jacksonCoefficientBV; positivity)
        (by simpa [m, pilot, S] using hcoeff))

/-- Conditional clipping changes the mean of the Jackson factorial polynomial
by at most its centered second moment divided by the clipping radius. With [the specified inputs and conditions](hyp:epsilon,lambda,m,hm,d,hd,pilot,W,rate,hWlaw,hWindep), [the stated relationship holds](goal). -/
-- @node: jacksonCellStatistic_mean_sub_raw_mean_le
lemma jacksonCellStatistic_mean_sub_raw_mean_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (epsilon lambda m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) :
    let cap := (d : ℝ) ^ (1 / 4 : ℝ) *
      ∑ zeta : Cell, pilotRadius m d pilot zeta
    |∫ omega, jacksonCellStatistic epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) ∂μ -
        ∫ omega, jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) ∂μ| ≤
      (∫ omega, (jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) -
            thresholdFunReal epsilon lambda (pilotMidpoint m d pilot)) ^ 2 ∂μ) / cap := by
  dsimp only
  let center := thresholdFunReal epsilon lambda (pilotMidpoint m d pilot)
  let Y : Ω → ℝ := fun omega =>
    jacksonCellRaw epsilon lambda m d pilot
      (fun zeta => W (CellFourEquiv zeta) omega) - center
  let cap := (d : ℝ) ^ (1 / 4 : ℝ) *
    ∑ zeta : Cell, pilotRadius m d pilot zeta
  have hcap : 0 < cap := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hsum : 0 < ∑ zeta : Cell, pilotRadius m d pilot zeta := by
      exact Finset.sum_pos (fun z _ => pilotRadius_pos_of_pos hm hd pilot z)
        (by simp)
    exact mul_pos (Real.rpow_pos_of_pos hdpos _) hsum
  have hYsq : Integrable (fun omega => Y omega ^ 2) μ := by
    simpa [Y, center] using jacksonCellRaw_centered_sq_integrable
      μ epsilon lambda m d pilot W rate hWlaw hWindep
  let X : Ω → (Fin 4 → ℕ) := fun omega i => W i omega
  have hX : AEMeasurable X μ :=
    aemeasurable_pi_lambda _ fun i => (hWlaw i).aemeasurable
  have hYmeas : AEStronglyMeasurable Y μ := by
    have hg : Measurable (fun x : Fin 4 → ℕ =>
        jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => x (CellFourEquiv zeta)) - center) := Measurable.of_discrete
    exact hg.comp_aemeasurable hX |>.aestronglyMeasurable
  have hYint : Integrable Y μ := by
    apply Integrable.mono' (hYsq.add (integrable_const 1)) hYmeas
    filter_upwards with omega
    change |Y omega| ≤ Y omega ^ 2 + 1
    nlinarith [sq_nonneg (|Y omega| - 1 / 2), sq_abs (Y omega)]
  let Z : Ω → ℝ := fun omega =>
    Causalean.Stat.Concentration.BoundedVariation.scalarClip cap (Y omega) - Y omega
  have hclipMeas : AEStronglyMeasurable (fun omega =>
      Causalean.Stat.Concentration.BoundedVariation.scalarClip cap (Y omega)) μ := by
    exact (AEMeasurable.min aemeasurable_const
      (AEMeasurable.max aemeasurable_const hYmeas.aemeasurable)).aestronglyMeasurable
  have hclipInt : Integrable (fun omega =>
      Causalean.Stat.Concentration.BoundedVariation.scalarClip cap (Y omega)) μ := by
    apply Integrable.mono' (integrable_const cap) hclipMeas
    filter_upwards with omega
    unfold Causalean.Stat.Concentration.BoundedVariation.scalarClip
    simp only [Real.norm_eq_abs]
    exact abs_le.2 ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have hZint : Integrable Z μ := hclipInt.sub hYint
  have hboundInt : Integrable (fun omega => Y omega ^ 2 / cap) μ :=
    hYsq.div_const cap
  have hpoint (omega : Ω) : |Z omega| ≤ Y omega ^ 2 / cap :=
    scalarClip_sub_le_sq_div cap (Y omega) hcap
  have hidentity :
      (∫ omega, jacksonCellStatistic epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) ∂μ) -
        ∫ omega, jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) ∂μ = ∫ omega, Z omega ∂μ := by
    rw [← integral_sub]
    · apply integral_congr_ae
      filter_upwards with omega
      dsimp only [Z, Y, center, cap]
      unfold jacksonCellStatistic
      dsimp only
      unfold Causalean.Stat.Concentration.BoundedVariation.scalarClip
      ring
    · apply ((integrable_const center).add hclipInt).congr
      exact Filter.Eventually.of_forall fun omega => by
        dsimp only [Y, center, cap]
        unfold jacksonCellStatistic
        rfl
    · apply (hYint.add (integrable_const center)).congr
      exact Filter.Eventually.of_forall fun omega => by
        change Y omega + center = _
        dsimp only [Y, center]
        ring
  rw [hidentity]
  calc
    |∫ omega, Z omega ∂μ| ≤ ∫ omega, |Z omega| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ omega, Y omega ^ 2 / cap ∂μ := by
      apply integral_mono hZint.abs hboundInt
      exact hpoint
    _ = _ := by
      rw [integral_div]

set_option maxHeartbeats 800000 in
-- The paired table-law specialization unfolds several finite product measures.
/-- On a fixed good pilot table, clipping changes the conditional cell mean
by the raw second-moment envelope divided by the paper's clipping scale. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood), [the shadow-price range](hyp:hlambda), [the positive envelope constant](hyp:hC), and [the coefficient envelope](hyp:hcoeff). -/
-- @node: goodPilot_jacksonCellStatistic_mean_sub_raw_mean_le
lemma goodPilot_jacksonCellStatistic_mean_sub_raw_mean_le
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → Nat) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (C : Real) (hC : 0 ≤ C)
    (hcoeff : jacksonCoefficientBV epsilon ((n : Real) / 8) d
        (curryCountTable p j) ≤
      C * (∑ zeta : Cell,
        pilotRadius ((n : Real) / 8) d (curryCountTable p j) zeta) *
        Real.exp (12 * jacksonDegree d)) :
    let m : Real := (n : Real) / 8
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
      fun i e => poissonTableCell j e i
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    |(∫ e, jacksonCellStatistic epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
        ∫ e, jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2) /
      ((d : Real) ^ (1 / 4 : Real) *
        ∑ zeta, pilotRadius m d pilot zeta) := by
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) mu := by
    simpa [W, mu, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) p (j, i)
  have hWindep : iIndepFun W mu := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) mu = poissonTableLaw (rate j) := by
        simpa [W, mu] using (poissonTable_eval_cell_law rate rate p j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) mu) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have hclip := jacksonCellStatistic_mean_sub_raw_mean_le mu epsilon lambda m
    (by dsimp [m]; positivity) d (show 1 ≤ d by omega) pilot W (rate j)
    hWlaw hWindep
  have hraw := goodPilot_jacksonCellRaw_centered_sq_integral_le epsilon he hn hd
    P p j hgood lambda hlambda C hC hcoeff
  have hcap : 0 ≤ (d : Real) ^ (1 / 4 : Real) *
      ∑ zeta : Cell, pilotRadius m d pilot zeta := by
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    exact Finset.sum_nonneg fun z _ =>
      (pilotRadius_pos_of_pos (by dsimp [m]; positivity)
        (show 1 ≤ d by omega) pilot z).le
  exact hclip.trans (by
    apply div_le_div_of_nonneg_right _ hcap
    simpa [m, rate, mu, pilot, W] using hraw)

/-- Independent Poisson evaluation counts make the unprojected paper
factorial polynomial exactly unbiased for the canonical Jackson polynomial. With [the specified inputs and conditions](hyp:epsilon,he,lambda,hlambda,m,hm,d,hd,pilot,W,rate,hWlaw,hWindep), [the stated relationship holds](goal). -/
-- @node: jacksonCellRaw_mean
lemma jacksonCellRaw_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (epsilon : ℝ) (he : 0 < epsilon) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) (m : ℝ) (hm : 0 < m)
    (d : ℕ) (hd : 1 ≤ d) (pilot : Cell → ℕ)
    (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) :
    (∫ omega, jacksonCellRaw epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) ∂μ) =
      thresholdFunReal epsilon lambda (pilotMidpoint m d pilot) +
        MvPolynomial.eval
          (fun i => ((rate i : ℝ) / m -
              pilotMidpoint m d pilot (CellFourEquiv.symm i)) /
            pilotRadius m d pilot (CellFourEquiv.symm i))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d)
            (pilotMidpoint m d pilot) (pilotRadius m d pilot)) := by
  classical
  let K := jacksonDegree d
  let D := 2 * (K - 1)
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  let p := localJacksonPolynomial epsilon lambda K center radius
  let x : Fin 4 → ℝ := fun i =>
    ((rate i : ℝ) / m - center (CellFourEquiv.symm i)) /
      radius (CellFourEquiv.symm i)
  have hK : 0 < K := by dsimp [K]; unfold jacksonDegree; omega
  have hpull : ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (normalizedCube 4) := by
    exact pilotRectangle_threshold_pullback_continuousOn
      (epsilon := epsilon) (m := m) (d := d) (pilot := pilot)
      he hm hd ⟨lambda, hlambda⟩
  have hdeg : ∀ i, p.degreeOf i ≤ D := fun i =>
    localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK hpull i
  have hmono (a : Fin 4 → Fin (D + 1)) : Integrable
      (fun omega => factorialMonomial m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) μ := by
    rw [show (fun omega => factorialMonomial m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) =
      fun omega => factorialProduct W m
        (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : ℕ)) omega /
          ∏ i, radius (CellFourEquiv.symm i) ^ (a i : ℕ) by
      funext omega
      exact factorialMonomial_eq_fourFactorialMonomial m d pilot W a omega]
    exact (factorialProduct_integrable_run μ W rate hWlaw hWindep m
      (fun i => center (CellFourEquiv.symm i)) (fun i => (a i : ℕ))).div_const _
  have hsumInt : Integrable (fun omega => ∑ a : Fin 4 → Fin (D + 1),
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) *
        factorialMonomial m d pilot
          (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ))) μ := by
    apply integrable_finsetSum
    intro a ha
    exact (hmono a).const_mul _
  have hmean (a : Fin 4 → Fin (D + 1)) :
      (∫ omega, factorialMonomial m d pilot
        (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ)) ∂μ) =
        ∏ i, x i ^ (a i : ℕ) := by
    rw [factorialMonomial_mean μ m (ne_of_gt hm) d pilot W rate hWlaw hWindep a]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [div_pow]
  have heval : (∑ a : Fin 4 → Fin (D + 1),
      jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) *
        ∏ i, x i ^ (a i : ℕ)) = MvPolynomial.eval x p := by
    rw [← Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorPolynomial_tensorCoeffs
      p hdeg]
    unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorPolynomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [MvPolynomial.eval_monomial, jacksonCoefficient_eq_tensorCoeffs]
    congr 1
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp [Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorExponent]
  change (∫ omega, thresholdFunReal epsilon lambda center +
      ∑ a : Fin 4 → Fin (D + 1),
        jacksonCoefficient epsilon lambda K center radius (fun i => (a i : ℕ)) *
          factorialMonomial m d pilot
            (fun zeta => W (CellFourEquiv zeta) omega) (fun i => (a i : ℕ)) ∂μ) = _
  rw [integral_add (integrable_const _) hsumInt, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hmean]
    simpa [K, D, center, radius, p, x] using heval
  · intro a ha
    exact (hmono a).const_mul _

set_option maxHeartbeats 1000000 in
-- Combining the exact factorial mean with the two conditional bounds is elaboration intensive.
/-- Conditional on a fixed good pilot table, the cell mean bias is the sum
of the clipping correction and the boundary-adaptive Jackson remainder. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood), [the shadow-price range](hyp:hlambda), [the positive envelope constant](hyp:hC), and [the coefficient envelope](hyp:hcoeff). -/
-- @node: goodPilot_jacksonCellStatistic_conditional_bias_le
lemma goodPilot_jacksonCellStatistic_conditional_bias_le
    {n d : Nat} (epsilon : Real) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → Nat) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j)
    (lambda : Real) (hlambda : lambda ∈ Set.Icc (0 : Real) 1)
    (C : Real) (hC : 0 ≤ C)
    (hcoeff : jacksonCoefficientBV epsilon ((n : Real) / 8) d
        (curryCountTable p j) ≤
      C * (∑ zeta : Cell,
        pilotRadius ((n : Real) / 8) d (curryCountTable p j) zeta) *
        Real.exp (12 * jacksonDegree d)) :
    let m : Real := (n : Real) / 8
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
      fun i e => poissonTableCell j e i
    let mu := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    |(∫ e, jacksonCellStatistic epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) -
        thresholdFunReal epsilon lambda (cellVector P j)| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2) /
        ((d : Real) ^ (1 / 4 : Real) *
          ∑ zeta, pilotRadius m d pilot zeta) +
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (2 / (jacksonDegree d : Real) + 1 / (jacksonDegree d : Real) ^ 2) *
        ∑ zeta, pilotRadius m d pilot zeta := by
  dsimp only
  let m : Real := (n : Real) / 8
  let rate : Fin d → Fin 4 → NNReal := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, poissonTableLaw]
    infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → Nat) → Nat :=
    fun i e => poissonTableCell j e i
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) mu := by
    simpa [W, mu, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) p (j, i)
  have hWindep : iIndepFun W mu := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) mu = poissonTableLaw (rate j) := by
        simpa [W, mu] using (poissonTable_eval_cell_law rate rate p j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) mu) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have hclip := goodPilot_jacksonCellStatistic_mean_sub_raw_mean_le epsilon he
    hn hd P p j hgood lambda hlambda C hC hcoeff
  have hmean := jacksonCellRaw_mean mu epsilon he lambda hlambda m
    (by dsimp [m]; positivity) d (show 1 ≤ d by omega) pilot W (rate j)
    hWlaw hWindep
  have hrate (i : Fin 4) : (rate j i : Real) / m =
      cellVector P j (CellFourEquiv.symm i) := by
    have hq : 0 ≤ cellVector P j (CellFourEquiv.symm i) := ENNReal.toReal_nonneg
    dsimp [rate, idealFlatRate, m]
    rw [max_eq_left (mul_nonneg (by positivity) hq)]
    field_simp
  have hmean' : (∫ e, jacksonCellRaw epsilon lambda m d pilot
          (fun zeta => W (CellFourEquiv zeta) e) ∂mu) =
      thresholdFunReal epsilon lambda (pilotMidpoint m d pilot) +
        MvPolynomial.eval
          (normalizedPoint
            (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
            (fun i => pilotRadius m d pilot (CellFourEquiv.symm i))
            (fun i => cellVector P j (CellFourEquiv.symm i)))
          (localJacksonPolynomial epsilon lambda (jacksonDegree d)
            (pilotMidpoint m d pilot) (pilotRadius m d pilot)) := by
    rw [hmean]
    congr 2
    rw [show (fun i => ((rate j i : Real) / m -
          pilotMidpoint m d pilot (CellFourEquiv.symm i)) /
        pilotRadius m d pilot (CellFourEquiv.symm i)) =
      normalizedPoint
        (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
        (fun i => pilotRadius m d pilot (CellFourEquiv.symm i))
        (fun i => cellVector P j (CellFourEquiv.symm i)) by
      funext i
      simp only [normalizedPoint, hrate]]
  have hboundary := goodPilot_localJacksonPolynomial_boundary_le_radiusSum
    epsilon he lambda hlambda hn (show 1 ≤ d by omega) P
      (curryCountTable p, fun _ _ => 0) j hgood
  let A : Real := ∫ e, jacksonCellStatistic epsilon lambda m d pilot
    (fun zeta => W (CellFourEquiv zeta) e) ∂mu
  let R : Real := ∫ e, jacksonCellRaw epsilon lambda m d pilot
    (fun zeta => W (CellFourEquiv zeta) e) ∂mu
  let T : Real := thresholdFunReal epsilon lambda (cellVector P j)
  change |A - T| ≤ _
  have hclip' : |A - R| ≤
      (4 * C ^ 2 * Real.exp 123 * (d : Real) ^ (1 / 16 : Real) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2) /
        ((d : Real) ^ (1 / 4 : Real) *
          ∑ zeta, pilotRadius m d pilot zeta) := by
    simpa [A, R, m, rate, mu, pilot, W] using hclip
  have hboundary' : |R - T| ≤
      32 * (3 * (1 + epsilon⁻¹) + 1) *
        (2 / (jacksonDegree d : Real) + 1 / (jacksonDegree d : Real) ^ 2) *
        ∑ zeta, pilotRadius m d pilot zeta := by
    dsimp [R, T]
    rw [hmean']
    simpa [m, pilot] using hboundary
  calc
    |A - T| = |(A - R) + (R - T)| := by
      congr 1
      ring
    _ ≤ |A - R| + |R - T| := abs_add_le _ _
    _ ≤ _ := add_le_add hclip' hboundary'

end CausalSmith.Stat.DiscreteBudgetvalueCurve
