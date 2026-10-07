module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.JacksonCoefficientEnvelope
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PilotRadiusMoment
public import Causalean.Stat.Concentration.BoundedVariation.Main
public import Causalean.Stat.Concentration.Poisson.ConditionalCellComposition
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius

/-! Good-pilot and bad-pilot centered continuum processes. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Stat.Concentration.BoundedVariation
open Causalean.Stat.Concentration.Poisson

/-- Cell statistic restricted to good or bad pilot draws. -/
noncomputable def pilotPartCell {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (perm : Equiv.Perm (Fin n)) (M : ℕ) (marks : Fin n → Bool)
    (j : Fin d) (good : Bool) : ℝ := by
  classical
  let stat := jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
      (fun zeta => markedCellCount sample perm M marks false j zeta)
      (fun zeta => markedCellCount sample perm M marks true j zeta)
  exact if good then (if pilotGood P sample perm M marks j then stat else 0)
    else (if pilotGood P sample perm M marks j then 0 else stat)

/-- Sum of the good-pilot or bad-pilot cell statistics. -/
noncomputable def pilotPartProcess {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (perm : Equiv.Perm (Fin n)) (M : ℕ) (marks : Fin n → Bool)
    (good : Bool) : ℝ :=
  ∑ j, pilotPartCell epsilon lambda P sample perm M marks j good

/-- Joint data/auxiliary mean of one pilot part. -/
noncomputable def pilotPartMean {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (good : Bool) : ℝ :=
  ∫ sample : Fin n → Obs d,
    auxiliaryAverage n (fun M perm marks =>
      pilotPartProcess epsilon lambda P sample perm M marks good)
    ∂productLaw P n

/-- Expected squared supremum of the centered good or bad pilot contribution. -/
noncomputable def centeredPilotPartRisk {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (good : Bool) : ℝ :=
  ∫ sample : Fin n → Obs d,
    auxiliaryAverage n (fun M perm marks =>
      (sSup ((fun lambda : ℝ =>
        |pilotPartProcess epsilon lambda P sample perm M marks good -
          pilotPartMean (n := n) epsilon lambda P good|) '' Set.Icc 0 1)) ^ 2)
    ∂productLaw P n

/-- Good pilot event in the ideal, uncapped count experiment. -/
def idealPilotGood {n d : ℕ} (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) : Prop :=
  ∀ zeta : Cell,
    |pilotCenter ((n : ℝ) / 8) (counts.1 j) zeta - cellVector P j zeta| ≤
      pilotHalfWidth ((n : ℝ) / 8) d (counts.1 j) zeta / 4

/-- On a good pilot draw, the true cell mass lies in the truncated pilot
rectangle, equivalently within one pilot radius of its midpoint. With [the specified inputs and conditions](hyp:n,d,hn,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealPilotGood_center_mem_radius
lemma idealPilotGood_center_mem_radius {n d : ℕ} (hn : 1 ≤ n)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (hgood : idealPilotGood (n := n) P counts j)
    (zeta : Cell) :
    |cellVector P j zeta -
        pilotMidpoint ((n : ℝ) / 8) d (counts.1 j) zeta| ≤
      pilotRadius ((n : ℝ) / 8) d (counts.1 j) zeta := by
  let m : ℝ := (n : ℝ) / 8
  let x := pilotCenter m (counts.1 j) zeta
  let q := cellVector P j zeta
  let h := pilotHalfWidth m d (counts.1 j) zeta
  have hm : 0 < m := by dsimp [m]; positivity
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hg := hgood zeta
  change |x - q| ≤ h / 4 at hg
  have hh : 0 ≤ h := by linarith [abs_nonneg (x - q)]
  have hg' := (abs_le.mp hg)
  have hlo : max 0 (x - h) ≤ q := by
    apply max_le hq
    linarith
  have hup : q ≤ x + h := by linarith
  change |q - ((max 0 (x - h) + (x + h)) / 2)| ≤
    ((x + h) - max 0 (x - h)) / 2
  rw [abs_le]
  constructor <;> linarith

/-- Flattened-rate form of good-pilot rectangle containment, matching the
`hcenter` premise of `localJacksonFourPoissonFactorialPath_sq_bound`. With [the specified inputs and conditions](hyp:n,d,hn,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealPilotGood_flatRate_center_mem_radius
lemma idealPilotGood_flatRate_center_mem_radius {n d : ℕ} (hn : 1 ≤ n)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (hgood : idealPilotGood (n := n) P counts j)
    (i : Fin 4) :
    |(idealFlatRate (n := n) P j i : ℝ) / ((n : ℝ) / 8) -
        pilotMidpoint ((n : ℝ) / 8) d (counts.1 j)
          (CellFourEquiv.symm i)| ≤
      pilotRadius ((n : ℝ) / 8) d (counts.1 j)
        (CellFourEquiv.symm i) := by
  have hm : 0 < (n : ℝ) / 8 := by positivity
  have hq : 0 ≤ cellVector P j (CellFourEquiv.symm i) := ENNReal.toReal_nonneg
  have hrate : (idealFlatRate (n := n) P j i : ℝ) =
      ((n : ℝ) / 8) * cellVector P j (CellFourEquiv.symm i) := by
    dsimp [idealFlatRate]
    exact max_eq_left (mul_nonneg hm.le hq)
  rw [hrate, mul_div_cancel_left₀ _ hm.ne']
  exact idealPilotGood_center_mem_radius hn P counts j hgood (CellFourEquiv.symm i)

/-- On a good pilot draw, every evaluation Poisson coordinate satisfies the
normalized variance-to-radius condition used by the factorial-path bound. With [the specified inputs and conditions](hyp:n,d,hn,hd,P,counts,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: idealPilotGood_rate_div_radius_sq
lemma idealPilotGood_rate_div_radius_sq {n d : ℕ} (hn : 1 ≤ n)
    (hd : 16 ≤ d) (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (hgood : idealPilotGood (n := n) P counts j)
    (i : Fin 4) :
    ((idealFlatRate (n := n) P j i : ℝ) /
      ((((n : ℝ) / 8) ^ 2) *
        pilotRadius ((n : ℝ) / 8) d (counts.1 j)
          (CellFourEquiv.symm i) ^ 2)) ≤
      1 / logAlphabet d := by
  let m : ℝ := (n : ℝ) / 8
  let L : ℝ := logAlphabet d
  let zeta := CellFourEquiv.symm i
  let x := pilotCenter m (counts.1 j) zeta
  let q := cellVector P j zeta
  let h := pilotHalfWidth m d (counts.1 j) zeta
  let R := pilotRadius m d (counts.1 j) zeta
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 0 < L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg hdreal]
  have hx : 0 ≤ x := by dsimp [x]; unfold pilotCenter; positivity
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hg := hgood zeta
  change |x - q| ≤ h / 4 at hg
  have hh : 0 ≤ h := by linarith [abs_nonneg (x - q)]
  have hq_up : q ≤ x + h / 4 := by
    have := (abs_le.mp hg).1
    linarith
  let s := Real.sqrt (x * L / m)
  let delta := L / m
  have hdelta : 0 < delta := div_pos hL hm
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = x * delta := by
    dsimp [s, delta]
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg hx hL.le) hm.le)]
    ring
  have hh_formula : h = 4096 * (s + delta) := by
    dsimp [h, s, delta, x, L]
    unfold pilotHalfWidth pilotRadiusConstant
    rfl
  have hs_le : 4 * s ≤ h := by rw [hh_formula]; nlinarith
  have hd_le : 4 * delta ≤ h := by rw [hh_formula]; nlinarith
  have hR : h / 2 ≤ R := by
    dsimp [R]
    unfold pilotRadius pilotUpper pilotLower
    have hlo : max 0 (x - h) ≤ x := max_le hx (by linarith)
    change h / 2 ≤ (x + h - max 0 (x - h)) / 2
    linarith
  have hmain : q * delta ≤ R ^ 2 := by
    have hxdelta : x * delta = s ^ 2 := hs_sq.symm
    have hR0 : 0 ≤ R := le_trans (div_nonneg hh (by norm_num)) hR
    have hR_sq : (h / 2) ^ 2 ≤ R ^ 2 := by nlinarith
    have hs_bound : s ^ 2 ≤ h ^ 2 / 16 := by nlinarith
    have hd_bound : h * delta / 4 ≤ h ^ 2 / 16 := by nlinarith
    calc
      q * delta ≤ (x + h / 4) * delta :=
        mul_le_mul_of_nonneg_right hq_up hdelta.le
      _ = x * delta + h * delta / 4 := by ring
      _ ≤ h ^ 2 / 8 := by rw [hxdelta]; linarith
      _ ≤ R ^ 2 := by nlinarith
  have hrate : (idealFlatRate (n := n) P j i : ℝ) = m * q := by
    dsimp [idealFlatRate, m, q, zeta]
    exact max_eq_left (mul_nonneg hm.le hq)
  rw [hrate]
  change m * q / (m ^ 2 * R ^ 2) ≤ 1 / L
  have hRpos : 0 < R := by
    have hhpos : 0 < h := by rw [hh_formula]; positivity
    linarith
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hRpos)) hL).2
  field_simp
  have hscaled := mul_le_mul_of_nonneg_left hmain hm.le
  have hrewrite : m * (q * delta) = q * L := by
    dsimp [delta]
    field_simp
  rw [hrewrite] at hscaled
  nlinarith

/-- The paper's good or bad summand includes the cellwise target subtraction. -/
noncomputable def idealPilotErrorPart {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (good : Bool) : ℝ := by
  classical
  exact ∑ j : Fin d,
    if (if good then idealPilotGood (n := n) P counts j
        else ¬ idealPilotGood (n := n) P counts j) then
      jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
        (counts.1 j) (counts.2 j) -
          thresholdFunReal epsilon lambda (cellVector P j)
    else 0

/-- The contribution of one cell to the good or bad ideal pilot error process. -/
-- @node: idealPilotErrorCell
noncomputable def idealPilotErrorCell {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (good : Bool) : ℝ := by
  classical
  exact if (if good then idealPilotGood (n := n) P counts j
      else ¬ idealPilotGood (n := n) P counts j) then
      jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
        (counts.1 j) (counts.2 j) -
          thresholdFunReal epsilon lambda (cellVector P j)
    else 0

/-- On the nonnegative cone, a fixed-threshold cell functional is continuous.
This is the local regularity needed on every pilot rectangle. With [the specified inputs and conditions](hyp:epsilon,lambda,he,hlambda), [the stated relationship holds](goal). -/
-- @node: thresholdFunReal_continuousOn_nonnegative
lemma thresholdFunReal_continuousOn_nonnegative {epsilon lambda : ℝ}
    (he : 0 < epsilon) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (thresholdFunReal epsilon lambda)
      {u : Cell → ℝ | ∀ z, 0 ≤ u z} := by
  let A : ℝ := 3 * (1 + epsilon⁻¹) + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let K : NNReal := ⟨4 * A, mul_nonneg (by norm_num) hA⟩
  apply (LipschitzOnWith.of_dist_le_mul (K := K) ?_).continuousOn
  intro u hu v hv
  rw [Real.dist_eq]
  have hbase := budget_thresholdFunReal_pointwise_lipschitz
    he lambda hlambda u v hu hv
  have hsum : (∑ z : Cell, |u z - v z|) ≤ 4 * dist u v := by
    calc
      (∑ z : Cell, |u z - v z|) ≤ ∑ _z : Cell, dist u v := by
        apply Finset.sum_le_sum
        intro z _
        rw [← Real.dist_eq]
        exact (dist_pi_le_iff (dist_nonneg : 0 ≤ dist u v)).mp le_rfl z
      _ = 4 * dist u v := by
        norm_num [Fintype.card_congr finProdFinEquiv]
  calc
    |thresholdFunReal epsilon lambda u - thresholdFunReal epsilon lambda v| ≤
        A * ∑ z, |u z - v z| := hbase
    _ ≤ A * (4 * dist u v) := mul_le_mul_of_nonneg_left hsum hA
    _ = (K : ℝ) * dist u v := by
      change A * (4 * dist u v) = (4 * A) * dist u v
      ring

/-- Every point in the affine image of a pilot rectangle has nonnegative
coordinates when the Poisson scale and alphabet are positive. With [the specified inputs and conditions](hyp:m,hm,d,hd,pilot,z,hz,i), [the stated relationship holds](goal). -/
-- @node: pilotRectangle_affinePoint_nonnegative
lemma pilotRectangle_affinePoint_nonnegative {m : ℝ} (hm : 0 < m)
    {d : ℕ} (hd : 1 ≤ d) (pilot : Cell → ℕ)
    (z : Fin 4 → ℝ)
    (hz : z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)
    (i : Fin 4) :
    0 ≤ Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
      (fun k => pilotMidpoint m d pilot (CellFourEquiv.symm k))
      (fun k => pilotRadius m d pilot (CellFourEquiv.symm k)) z i := by
  have hlo : 0 ≤ pilotLower m d pilot (CellFourEquiv.symm i) :=
    le_max_left _ _
  have hc : 0 ≤ pilotCenter m pilot (CellFourEquiv.symm i) := by
    unfold pilotCenter
    positivity
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have := Real.log_nonneg hdreal
    linarith
  have hhalf :
      0 ≤ pilotHalfWidth m d pilot (CellFourEquiv.symm i) := by
    unfold pilotHalfWidth pilotRadiusConstant
    positivity
  have hup : 0 ≤ pilotUpper m d pilot (CellFourEquiv.symm i) := by
    unfold pilotUpper
    positivity
  have hzlo := (hz i).1
  have hzup := (hz i).2
  simp only [Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint,
    pilotMidpoint, pilotRadius]
  nlinarith

/-- Every coordinate of a positive-scale pilot rectangle has strictly positive
radius. With [the specified inputs and conditions](hyp:m,hm,d,hd,pilot,zeta), [the stated relationship holds](goal). -/
-- @node: pilotRadius_pos_of_pos
lemma pilotRadius_pos_of_pos {m : ℝ} (hm : 0 < m) {d : ℕ} (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (zeta : Cell) :
    0 < pilotRadius m d pilot zeta := by
  have hc : 0 ≤ pilotCenter m pilot zeta := by
    unfold pilotCenter
    positivity
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have := Real.log_nonneg hdreal
    linarith
  have hhalf : 0 < pilotHalfWidth m d pilot zeta := by
    unfold pilotHalfWidth pilotRadiusConstant
    positivity
  unfold pilotRadius pilotUpper pilotLower
  by_cases h : 0 ≤ pilotCenter m pilot zeta - pilotHalfWidth m d pilot zeta
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left (le_of_not_ge h)]
    linarith

/-- The threshold pullback to every positive-scale pilot rectangle is
continuous, discharging the regularity premise of the Jackson construction. With [the specified inputs and conditions](hyp:epsilon,m,he,hm,d,hd,pilot,lambda), [the stated relationship holds](goal). -/
-- @node: pilotRectangle_threshold_pullback_continuousOn
lemma pilotRectangle_threshold_pullback_continuousOn {epsilon m : ℝ}
    (he : 0 < epsilon) (hm : 0 < m) {d : ℕ} (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (lambda : Time) :
    ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda.1
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) := by
  let A : (Fin 4 → ℝ) → (Cell → ℝ) := fun z c =>
    Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
      (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
      (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
      (CellFourEquiv c)
  have hA : Continuous A := by
    apply continuous_pi
    intro c
    exact continuous_const.add (continuous_const.mul (continuous_apply _))
  apply (thresholdFunReal_continuousOn_nonnegative he lambda.2).comp
    hA.continuousOn
  intro z hz c
  exact pilotRectangle_affinePoint_nonnegative hm hd pilot z hz (CellFourEquiv c)

/-- One positive constant depending only on the overlap level bounds every
pilot-local Jackson coefficient BV envelope by the paper's radius sum and
`exp (12 K)` factor. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: jacksonCoefficientBV_pilot_le
lemma jacksonCoefficientBV_pilot_le (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ), 0 < m → ∀ (d : ℕ), 1 ≤ d →
      ∀ pilot : Cell → ℕ,
      jacksonCoefficientBV epsilon m d pilot ≤
        C * (∑ zeta : Cell, pilotRadius m d pilot zeta) *
          Real.exp (12 * jacksonDegree d) := by
  obtain ⟨C₀, hC₀, hthreshold⟩ := thresholdFun_bv_lipschitz epsilon he he'
  refine ⟨2 * C₀ + 1, by linarith, ?_⟩
  intro m hm d hd pilot
  let S := ∑ zeta : Cell, pilotRadius m d pilot zeta
  have hR (zeta : Cell) : 0 ≤ pilotRadius m d pilot zeta :=
    (pilotRadius_pos_of_pos hm hd pilot zeta).le
  have hS : 0 ≤ S := Finset.sum_nonneg fun z _ => hR z
  have hcenter (zeta : Cell) : 0 ≤ pilotMidpoint m d pilot zeta := by
    let z : Fin 4 → ℝ := fun _ => 0
    have hz : z ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4 := by
      intro i
      constructor <;> norm_num
    have h := pilotRectangle_affinePoint_nonnegative hm hd pilot z hz
      (CellFourEquiv zeta)
    simpa [z, Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint] using h
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := m) he hm hd pilot lambda
  have hcube (x : Fin 4 → ℝ)
      (hx : x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
      pathSize (⟨fun lambda : Time => MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)),
        localJacksonPolynomial_eval_continuous_time epsilon (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          (by unfold jacksonDegree; omega) hpull x hx⟩ : Path) ≤ 2 * C₀ * S := by
    exact localJacksonPolynomial_cube_pathSize_le epsilon (jacksonDegree d)
      (pilotMidpoint m d pilot) (pilotRadius m d pilot)
      (by unfold jacksonDegree; omega) hpull hcenter hR
      (fun x hx zeta => pilotRectangle_affinePoint_nonnegative hm hd pilot x hx
        (CellFourEquiv zeta)) C₀ hC₀
      hthreshold x hx
  have hcoeff := jacksonCoefficientBV_le_of_cube_pathSize epsilon m d pilot
    (by unfold jacksonDegree; omega) hpull (2 * C₀ * S)
    (mul_nonneg (mul_nonneg (by norm_num) hC₀) hS) hcube
  calc
    jacksonCoefficientBV epsilon m d pilot ≤
        Real.exp (12 * jacksonDegree d) * (2 * C₀ * S) := hcoeff
    _ ≤ (2 * C₀ + 1) * S * Real.exp (12 * jacksonDegree d) := by
      have hexp := Real.exp_pos (12 * jacksonDegree d)
      nlinarith

/-- Conditional on a fixed good flattened pilot table, the promoted
four-Poisson factorial-path theorem gives the complete measurable BV and
square-path-size package for one evaluation cell. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: goodPilot_localJacksonFourPoissonFactorialPath_sq_bound
lemma goodPilot_localJacksonFourPoissonFactorialPath_sq_bound
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → ℕ) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j) :
    let m : ℝ := (n : ℝ) / 8
    let L : ℝ := logAlphabet d
    let K := jacksonDegree d
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
      fun i e => poissonTableCell j e i
    let μ := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    Measurable (localJacksonFourPoissonFactorialPath epsilon K
        (pilotMidpoint m d pilot) (pilotRadius m d pilot)
        (by unfold K jacksonDegree; omega)
        (fun lambda => pilotRectangle_threshold_pullback_continuousOn
          (epsilon := epsilon) (m := m) he (by positivity)
          (show 1 ≤ d by omega) pilot lambda)
        (le_refl _) W m
        ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta)) ∧
      (∀ e, eVariationOn
        (localJacksonFourPoissonFactorialPath epsilon K
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          (by unfold K jacksonDegree; omega)
          (fun lambda => pilotRectangle_threshold_pullback_continuousOn
            (epsilon := epsilon) (m := m) he (by positivity)
            (show 1 ≤ d by omega) pilot lambda)
          (le_refl _) W m
          ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta) e)
          Set.univ < ⊤) ∧
      Integrable (fun e => (pathSize
        (localJacksonFourPoissonFactorialPath epsilon K
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          (by unfold K jacksonDegree; omega)
          (fun lambda => pilotRectangle_threshold_pullback_continuousOn
            (epsilon := epsilon) (m := m) he (by positivity)
            (show 1 ≤ d by omega) pilot lambda)
          (le_refl _) W m
          ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta) e)) ^ 2) μ := by
  dsimp only
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, poissonTableLaw]
    infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
    fun i e => poissonTableCell j e i
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
    (show 1 ≤ d by omega) pilot lambda
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) μ := by
    simpa [W, μ, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) (j, i)
  have hWindep : iIndepFun W μ := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) μ = poissonTableLaw (rate j) := by
        simpa [W, μ] using (poissonTable_eval_cell_law rate j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) μ) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have h := localJacksonFourPoissonFactorialPath_sq_bound μ epsilon
    (jacksonDegree d) (pilotMidpoint ((n : ℝ) / 8) d pilot)
    (pilotRadius ((n : ℝ) / 8) d pilot)
    (by unfold jacksonDegree; omega) hpull (le_refl _)
    W (rate j) (by intro i; fun_prop) hWlaw hWindep
    ((n : ℝ) / 8) (logAlphabet d) (by positivity)
    (by
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
        Real.log_exp]
      have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith [Real.log_nonneg this])
    (fun i => pilotRadius_pos_of_pos (by positivity) (show 1 ≤ d by omega) pilot _)
    (fun i => idealPilotGood_flatRate_center_mem_radius hn P
      (curryCountTable p, fun _ _ => 0) j hgood i)
    (fun i => idealPilotGood_rate_div_radius_sq hn hd P
      (curryCountTable p, fun _ _ => 0) j hgood i)
    ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg
      (fun z _ => (pilotRadius_pos_of_pos (by positivity)
        (show 1 ≤ d by omega) pilot z).le)))
  simpa [rate, μ, pilot, W, hpull] using
    (show _ ∧ _ ∧ _ from ⟨h.1, h.2.1, h.2.2.2.1⟩)

/-- Equation (21), conditionally on a fixed good pilot table: the evaluation
factorial path has squared path-size bounded by the pilot radius sum squared,
the structural `d^(1/16)` loss, and a coefficient-envelope constant. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood), [the positive envelope constant](hyp:hC), and [the coefficient envelope](hyp:hcoeff). -/
-- @node: goodPilot_localJacksonFourPoissonFactorialPath_sq_integral_le
lemma goodPilot_localJacksonFourPoissonFactorialPath_sq_integral_le
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (p : (Fin d × Fin 4) → ℕ) (j : Fin d)
    (hgood : idealPilotGood (n := n) P
      (curryCountTable p, fun _ _ => 0) j)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : jacksonCoefficientBV epsilon ((n : ℝ) / 8) d
        (curryCountTable p j) ≤
      C * (∑ zeta : Cell,
        pilotRadius ((n : ℝ) / 8) d (curryCountTable p j) zeta) *
        Real.exp (12 * jacksonDegree d)) :
    let m : ℝ := (n : ℝ) / 8
    let K := jacksonDegree d
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
      fun i e => poissonTableCell j e i
    let μ := poissonTableLaw (fun iz : Fin d × Fin 4 =>
      idealFlatRate (n := n) P iz.1 iz.2)
    (∫ e, pathSize (localJacksonFourPoissonFactorialPath epsilon K
      (pilotMidpoint m d pilot) (pilotRadius m d pilot)
      (by unfold K jacksonDegree; omega)
      (fun lambda => pilotRectangle_threshold_pullback_continuousOn
        (epsilon := epsilon) (m := m) he (by positivity)
        (show 1 ≤ d by omega) pilot lambda)
      (le_refl _) W m
      ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta) e) ^ 2
      ∂μ) ≤
      4 * C ^ 2 * Real.exp 123 * (d : ℝ) ^ (1 / 16 : ℝ) *
        (∑ zeta, pilotRadius m d pilot zeta) ^ 2 := by
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let K := jacksonDegree d
  let L := logAlphabet d
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, poissonTableLaw]
    infer_instance
  let pilot := curryCountTable p j
  let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
    fun i e => poissonTableCell j e i
  let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
    (epsilon := epsilon) (m := m) he (by dsimp [m]; positivity)
    (show 1 ≤ d by omega) pilot lambda
  have hWlaw (i : Fin 4) : HasLaw (W i) (poissonMeasure (rate j i)) μ := by
    simpa [W, μ, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2) (j, i)
  have hWindep : iIndepFun W μ := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    calc
      Measure.map (fun e i => W i e) μ = poissonTableLaw (rate j) := by
        simpa [W, μ] using (poissonTable_eval_cell_law rate j).map_eq
      _ = Measure.infinitePi (fun i => poissonMeasure (rate j i)) := rfl
      _ = Measure.infinitePi (fun i => Measure.map (W i) μ) := by
        congr 1
        funext i
        exact (hWlaw i).map_eq.symm
  have hL : 0 < L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg this]
  have hraw := localJacksonFourPoissonFactorialPath_sq_integral_le_coefficientBV
    μ epsilon m d pilot (by unfold jacksonDegree; omega) hpull W (rate j)
    (by intro i; fun_prop) hWlaw hWindep L (by dsimp [m]; positivity) hL
    (fun i => pilotRadius_pos_of_pos (by dsimp [m]; positivity)
      (show 1 ≤ d by omega) pilot _)
    (fun i => idealPilotGood_flatRate_center_mem_radius hn P
      (curryCountTable p, fun _ _ => 0) j hgood i)
    (fun i => idealPilotGood_rate_div_radius_sq hn hd P
      (curryCountTable p, fun _ _ => 0) j hgood i)
    ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg
      (fun z _ => (pilotRadius_pos_of_pos (by dsimp [m]; positivity)
        (show 1 ≤ d by omega) pilot z).le)))
  let S := ∑ zeta : Cell, pilotRadius m d pilot zeta
  have hS : 0 ≤ S := Finset.sum_nonneg fun z _ =>
    (pilotRadius_pos_of_pos (by dsimp [m]; positivity)
      (show 1 ≤ d by omega) pilot z).le
  have hcoeff' : jacksonCoefficientBV epsilon m d pilot ^ 2 ≤
      C ^ 2 * S ^ 2 * Real.exp (24 * K) := by
    have hcoeff0 : 0 ≤ jacksonCoefficientBV epsilon m d pilot := by
      unfold jacksonCoefficientBV
      exact Finset.sum_nonneg fun a _ =>
        add_nonneg (abs_nonneg _) ENNReal.toReal_nonneg
    have hrhs0 : 0 ≤ C * S * Real.exp (12 * K) := by positivity
    have hsquare := (sq_le_sq₀ hcoeff0 hrhs0).mpr (by
      simpa [m, K, pilot, S] using hcoeff)
    calc
      _ ≤ (C * S * Real.exp (12 * K)) ^ 2 := hsquare
      _ = C ^ 2 * S ^ 2 * Real.exp (24 * K) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hsum :
      (∑ _a : Fin 4 → Fin (2 * (K - 1) + 1),
        Real.exp (4 * ((2 * (K - 1) : ℕ) : ℝ) ^ 2 / L)) ≤
      (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        Real.exp (16 * (K : ℝ) ^ 2 / L) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Fintype.card
        (Fin 4 → Fin (2 * (K - 1) + 1)) : ℕ) : ℝ) =
        (↑(2 * (K - 1) + 1) : ℝ) ^ 4 := by
      rw [Fintype.card_fun]
      simp
    rw [Finset.card_univ, hcard]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hsub : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
    have hsq : ((2 * (K - 1) : ℕ) : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 := by
      push_cast
      nlinarith [sq_nonneg ((K - 1 : ℕ) : ℝ), sq_nonneg (K : ℝ)]
    apply (div_le_div_iff_of_pos_right hL).2
    nlinarith
  have habsorb := jacksonDegree_factorial_index_exponential_budget d hd
  calc
    _ ≤ (4 * jacksonCoefficientBV epsilon m d pilot ^ 2) *
        ∑ _a : Fin 4 → Fin (2 * (K - 1) + 1),
          Real.exp (4 * ((2 * (K - 1) : ℕ) : ℝ) ^ 2 / L) := by
      simpa [m, K, L, rate, μ, pilot, W, hpull] using hraw
    _ ≤ (4 * (C ^ 2 * S ^ 2 * Real.exp (24 * K))) *
        ((↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
          Real.exp (16 * (K : ℝ) ^ 2 / L)) := by
      gcongr
    _ ≤ 4 * C ^ 2 * S ^ 2 *
        (Real.exp 123 * (d : ℝ) ^ (1 / 16 : ℝ)) := by
      calc
        _ = 4 * C ^ 2 * S ^ 2 *
            ((↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
              Real.exp (24 * K + 16 * (K : ℝ) ^ 2 / L)) := by
          rw [Real.exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [K, L] using habsorb)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) (sq_nonneg S))
    _ = _ := by ring

/-- The epsilon-dependent coefficient estimate instantiates the conditional
equation (21) bound for every good pilot table. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,p,j), [the stated relationship holds](goal). The argument assumes [the good-pilot premise](hyp:hgood). -/
-- @node: goodPilot_factorialPath_equation21
lemma goodPilot_factorialPath_equation21
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (p : (Fin d × Fin 4) → ℕ) (j : Fin d)
    (hgood : idealPilotGood (n := n) P (curryCountTable p, fun _ _ => 0) j) :
    ∃ C : ℝ, 0 < C ∧
      let m : ℝ := (n : ℝ) / 8
      let K := jacksonDegree d
      let pilot := curryCountTable p j
      let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
        fun i e => poissonTableCell j e i
      let μ := poissonTableLaw (fun iz : Fin d × Fin 4 =>
        idealFlatRate (n := n) P iz.1 iz.2)
      (∫ e, pathSize (localJacksonFourPoissonFactorialPath epsilon K
        (pilotMidpoint m d pilot) (pilotRadius m d pilot)
        (by unfold K jacksonDegree; omega)
        (fun lambda => pilotRectangle_threshold_pullback_continuousOn
          (epsilon := epsilon) (m := m) he (by positivity)
          (show 1 ≤ d by omega) pilot lambda)
        (le_refl _) W m
        ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta, pilotRadius m d pilot zeta) e) ^ 2
        ∂μ) ≤ C * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∑ zeta, pilotRadius m d pilot zeta) ^ 2 := by
  obtain ⟨C₀, hC₀, hcoeff⟩ := jacksonCoefficientBV_pilot_le epsilon he he'
  refine ⟨4 * C₀ ^ 2 * Real.exp 123, by positivity, ?_⟩
  exact goodPilot_localJacksonFourPoissonFactorialPath_sq_integral_le
    epsilon he hn hd P p j hgood C₀ hC₀.le
    (hcoeff ((n : ℝ) / 8) (by positivity) d (by omega)
      (curryCountTable p j))

/-- The ideal cell-error summand is continuous in the threshold whenever its
pilot-local threshold pullbacks satisfy the Jackson construction regularity. With [the specified inputs and conditions](hyp:n,d,epsilon,P,counts,j,good,hpull), [the stated relationship holds](goal). -/
-- @node: idealPilotErrorCell_continuous_time
lemma idealPilotErrorCell_continuous_time {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (good : Bool)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint ((n : ℝ) / 8) d (counts.1 j)
            (CellFourEquiv.symm i))
          (fun i => pilotRadius ((n : ℝ) / 8) d (counts.1 j)
            (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j good) := by
  classical
  by_cases hcond : (if good then idealPilotGood (n := n) P counts j
      else ¬ idealPilotGood (n := n) P counts j)
  · exact (jacksonCellStatistic_continuous_time epsilon ((n : ℝ) / 8) d
      (counts.1 j) (counts.2 j) hpull).sub
        (thresholdFunReal_continuous_time epsilon (cellVector P j)) |>.congr
          (fun lambda => by simp [idealPilotErrorCell, hcond])
  · have hz : Continuous (fun _ : Time => (0 : ℝ)) := continuous_const
    exact hz.congr (fun lambda => by simp [idealPilotErrorCell, hcond])

/-- Positive sample size and nonempty alphabet automatically supply the pilot
rectangle pullback regularity for an ideal cell-error path. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts,j,good), [the stated relationship holds](goal). -/
-- @node: idealPilotErrorCell_continuous_time_of_pos
lemma idealPilotErrorCell_continuous_time_of_pos {n d : ℕ} {epsilon : ℝ}
    (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (good : Bool) :
    Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j good) := by
  apply idealPilotErrorCell_continuous_time epsilon P counts j good
  intro lambda
  apply pilotRectangle_threshold_pullback_continuousOn he
  · positivity
  · exact hd

/-- The ideal good or bad error process is the sum of its cell contributions. With [the specified inputs and conditions](hyp:n,d,epsilon,lambda,P,counts,good), [the stated relationship holds](goal). -/
-- @node: idealPilotErrorPart_eq_sum_cells
lemma idealPilotErrorPart_eq_sum_cells {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (good : Bool) :
    idealPilotErrorPart (n := n) epsilon lambda P counts good =
      ∑ j, idealPilotErrorCell (n := n) epsilon lambda P counts j good := by
  classical
  simp only [idealPilotErrorPart, idealPilotErrorCell]

/-- A continuous cell contribution, restricted to the threshold interval, as a
bounded-variation maximal-inequality path. -/
-- @node: idealPilotErrorCellPath
noncomputable def idealPilotErrorCellPath {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (good : Bool)
    (hcont : Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j good)) : Path :=
  ⟨fun lambda => idealPilotErrorCell (n := n) epsilon lambda P counts j good, hcont⟩

/-- The uniform norm of a continuous real path restricted to `[0,1]` is the
real supremum of its absolute values in the paper's `sSup` notation. With [the specified inputs and conditions](hyp:g,hg), [the stated relationship holds](goal). -/
-- @node: path_norm_eq_sSup_abs_restrict
lemma path_norm_eq_sSup_abs_restrict (g : ℝ → ℝ)
    (hg : Continuous (fun t : Time => g t.1)) :
    ‖(⟨fun t : Time => g t.1, hg⟩ : Path)‖ =
      sSup ((fun lambda : ℝ => |g lambda|) '' Set.Icc 0 1) := by
  let f : Path := ⟨fun t : Time => g t.1, hg⟩
  let S : Set ℝ := (fun lambda : ℝ => |g lambda|) '' Set.Icc 0 1
  have hSne : S.Nonempty :=
    ⟨|g 0|, ⟨0, by constructor <;> norm_num, rfl⟩⟩
  have hSbdd : BddAbove S := by
    refine ⟨‖f‖, ?_⟩
    rintro y ⟨lambda, hlambda, rfl⟩
    simpa [f, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm f (⟨lambda, hlambda⟩ : Time)
  have hs0 : 0 ≤ sSup S := (abs_nonneg (g 0)).trans
    (le_csSup hSbdd ⟨0, by constructor <;> norm_num, rfl⟩)
  apply le_antisymm
  · apply (ContinuousMap.norm_le f hs0).2
    intro t
    rw [Real.norm_eq_abs]
    exact le_csSup hSbdd ⟨t.1, t.2, rfl⟩
  · apply csSup_le hSne
    rintro y ⟨lambda, hlambda, rfl⟩
    simpa [f, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm f (⟨lambda, hlambda⟩ : Time)

/-- Norm identification for the paper's ideal good or bad cell-error path. With [the specified inputs and conditions](hyp:n,d,epsilon,P,counts,j,good), [the stated relationship holds](goal). The argument assumes [path continuity](hyp:hcont). -/
-- @node: idealPilotErrorCellPath_norm_eq_sSup
lemma idealPilotErrorCellPath_norm_eq_sSup {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) (good : Bool)
    (hcont : Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j good)) :
    ‖idealPilotErrorCellPath epsilon P counts j good hcont‖ =
      sSup ((fun lambda : ℝ =>
        |idealPilotErrorCell (n := n) epsilon lambda P counts j good|) ''
          Set.Icc 0 1) := by
  exact path_norm_eq_sSup_abs_restrict
    (fun lambda => idealPilotErrorCell (n := n) epsilon lambda P counts j good)
    hcont

/-- The abstract bounded-variation maximal theorem specialized to the ideal
Poisson cell-error paths.  Its hypotheses isolate the remaining paper-specific
work: continuity in the threshold, measurability and integrability in the
counts, the cellwise path-size moment, and independence across cells. With [the specified inputs and conditions](hyp:n,d,epsilon,P,good), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob), [path continuity](hyp:hcont), [measurability](hyp:hmeas), [Bochner integrability](hyp:hint), [the bounded-variation control](hyp:hBV), [the path moment bound](hyp:hmom), and [cross-cell independence](hyp:hind). -/
-- @node: idealPilotErrorCellPath_centered_maximal
lemma idealPilotErrorCellPath_centered_maximal {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (good : Bool)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P))
    (hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j good))
    (hmeas : ∀ j, Measurable (fun counts =>
      idealPilotErrorCellPath epsilon P counts j good (hcont j counts)))
    (hint : ∀ j, Integrable (fun counts =>
      idealPilotErrorCellPath epsilon P counts j good (hcont j counts))
      (idealCountLaw (n := n) P))
    (hBV : ∀ j, ∀ᵐ counts ∂idealCountLaw (n := n) P,
      eVariationOn
        (idealPilotErrorCellPath epsilon P counts j good (hcont j counts))
        Set.univ < ⊤)
    (hmom : ∀ j, Integrable (fun counts =>
      (pathSize
        (idealPilotErrorCellPath epsilon P counts j good (hcont j counts))) ^ 2)
      (idealCountLaw (n := n) P))
    (hind : ProbabilityTheory.iIndepFun (fun j counts =>
      idealPilotErrorCellPath epsilon P counts j good (hcont j counts))
      (idealCountLaw (n := n) P)) :
    (∫ counts, ‖∑ j, (idealPilotErrorCellPath epsilon P counts j good
          (hcont j counts) -
        ∫ x, idealPilotErrorCellPath epsilon P x j good (hcont j x)
          ∂idealCountLaw (n := n) P)‖ ^ 2
      ∂idealCountLaw (n := n) P) ≤
      16384 * ∑ j, (∫ counts,
        (pathSize
          (idealPilotErrorCellPath epsilon P counts j good (hcont j counts))) ^ 2
        ∂idealCountLaw (n := n) P) := by
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) := hprob
  exact centered_path_sum_maximal (idealCountLaw (n := n) P)
    (fun j counts =>
      idealPilotErrorCellPath epsilon P counts j good (hcont j counts))
    hmeas hint hBV hmom hind

/-- Mean of the uncapped good or bad error part. -/
noncomputable def idealPilotErrorMean {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (good : Bool) : ℝ :=
  ∫ counts, idealPilotErrorPart (n := n) epsilon lambda P counts good
    ∂idealCountLaw (n := n) P

/-- Centered risk of the paper's good or bad cellwise error sum. -/
noncomputable def centeredIdealPilotErrorRisk {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (good : Bool) : ℝ :=
  ∫ counts,
    (sSup ((fun lambda : ℝ =>
      |idealPilotErrorPart (n := n) epsilon lambda P counts good -
        idealPilotErrorMean (n := n) epsilon lambda P good|) ''
        Set.Icc 0 1)) ^ 2
    ∂idealCountLaw (n := n) P

/-- The clipped cell path from the common Jackson polynomial. -/
noncomputable def idealClippedCellPath {n d : ℕ} (epsilon lambda : ℝ)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ))
    (j : Fin d) : ℝ :=
  jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
    (counts.1 j) (counts.2 j)

/-- The uncentered bad-pilot cell envelope in proof (28). -/
noncomputable def badPilotCellEnvelope {n d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (j : Fin d) : ℝ := by
  classical
  exact Real.sqrt (∫ counts,
    (if idealPilotGood (n := n) P counts j then 0 else
      sSup ((fun lambda : ℝ =>
        |idealClippedCellPath (n := n) epsilon lambda counts j -
          thresholdFunReal epsilon lambda (cellVector P j)|) ''
          Set.Icc 0 1)) ^ 2
    ∂idealCountLaw (n := n) P)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
