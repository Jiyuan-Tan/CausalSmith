module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CoefficientOneNorm
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CountBridge
public import Mathlib.Data.Nat.Choose.Bounds

/-! The exact coefficient-overlap expression controlling the marked factorial second moment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
attribute [local instance] Classical.propDecidable

/-- For [the specified inputs and assumptions](hyp:lam,v,w), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def factorialOverlap
    (lam : ℝ≥0) -- @realizes \(t\)(generic Poisson intensity in [0,∞))
    (v w : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (min v w + 1),
    (v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ) *
      (lam : ℝ) ^ (v + w - r)

/-- For [the specified inputs and assumptions](hyp:n,d,q,lam), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def needleCoefficientOverlap (n d : ℕ) (q : ℝ)
    (lam : ℝ≥0) : ℝ := -- @realizes \(t\)(generic Poisson intensity in [0,∞))
  ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
    ∑ w ∈ Finset.Icc 1 (needleDegree n q - 1),
      |needleCoeff n d q v * needleCoeff n d q w| * factorialOverlap lam v w

private lemma choose_product_factorial_le (v w r : ℕ) :
    (v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ) ≤
      ((v : ℝ) * w) ^ r / (Nat.factorial r : ℝ) := by
  have hv := Nat.choose_le_pow_div (α := ℝ) r v
  have hw := Nat.choose_le_pow_div (α := ℝ) r w
  have hfac : (0 : ℝ) < Nat.factorial r := by positivity
  calc
    _ ≤ ((v : ℝ) ^ r / Nat.factorial r) *
        ((w : ℝ) ^ r / Nat.factorial r) * Nat.factorial r := by gcongr
    _ = _ := by rw [mul_pow]; field_simp

private lemma factorialOverlap_le_exp (lam : ℝ≥0) (v w k : ℕ) (B : ℝ)
    (hB : 0 < B) (hlam : (lam : ℝ) ≤ B) (hv : v ≤ k) (hw : w ≤ k) :
    factorialOverlap lam v w ≤ B ^ (v + w) * Real.exp ((k : ℝ) ^ 2 / B) := by
  let x : ℝ := (k : ℝ) ^ 2 / B
  have hx : 0 ≤ x := by dsimp [x]; positivity
  calc
    factorialOverlap lam v w ≤
        B ^ (v + w) *
          (∑ r ∈ Finset.range (min v w + 1), x ^ r / (Nat.factorial r : ℝ)) := by
      unfold factorialOverlap
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hrv : r ≤ v :=
        le_trans (Nat.le_of_lt_succ (by simpa using hr)) (min_le_left _ _)
      have hrw : r ≤ w :=
        le_trans (Nat.le_of_lt_succ (by simpa using hr)) (min_le_right _ _)
      have hrsum : r ≤ v + w := hrv.trans (Nat.le_add_right _ _)
      have hcomb := choose_product_factorial_le v w r
      have hlamPow : (lam : ℝ) ^ (v + w - r) ≤ B ^ (v + w - r) := by
        gcongr
      calc
        (v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ) *
            (lam : ℝ) ^ (v + w - r) ≤
            (((v : ℝ) * w) ^ r / (Nat.factorial r : ℝ)) *
              B ^ (v + w - r) := by gcongr
        _ = B ^ (v + w) * ((((v : ℝ) * w) / B) ^ r /
              (Nat.factorial r : ℝ)) := by
                rw [div_pow]
                field_simp
                calc
                  ((v : ℝ) * w) ^ r * B ^ (v + w - r) * B ^ r =
                      ((v : ℝ) * w) ^ r *
                        (B ^ (v + w - r) * B ^ r) := by ring
                  _ = _ := by rw [← pow_add, Nat.sub_add_cancel hrsum]
        _ ≤ B ^ (v + w) * (x ^ r / (Nat.factorial r : ℝ)) := by
              gcongr
              dsimp [x]
              apply div_le_div_of_nonneg_right _ hB.le
              nlinarith [show (v : ℝ) ≤ k by exact_mod_cast hv,
                show (w : ℝ) ≤ k by exact_mod_cast hw,
                show (0 : ℝ) ≤ v by positivity, show (0 : ℝ) ≤ w by positivity]
    _ ≤ B ^ (v + w) * Real.exp x := by
      gcongr
      exact Real.sum_le_exp_of_nonneg hx (min v w + 1)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hbranch), [the stated mathematical conclusion holds](goal). -/
lemma needle_scaled_polynomial_oneNorm_le (n d : ℕ) (q : ℝ)
    (hbranch : needleBranch n d q) :
    polynomialCoeffOneNorm
      ((1 - chebNeedle n d q).comp (Polynomial.C (needleRadius n q) * Polynomial.X)) ≤
        (8 : ℝ) ^ needleDegree n q := by
  let k := needleDegree n q
  let B := needleRadius n q
  let T := Polynomial.Chebyshev.T ℝ (k : ℤ)
  let p : Polynomial ℝ :=
    1 - T.comp (Polynomial.C 1 - Polynomial.C (2 / B) * Polynomial.X)
  let r : Polynomial ℝ :=
    1 - T.comp (Polynomial.C 1 - Polynomial.C 2 * Polynomial.X)
  have hell : 128 ≤ logScale n q := hbranch.1
  have hB : 0 < B := by dsimp [B, needleRadius]; positivity
  have hk : 2 ≤ k := by
    dsimp [k, needleDegree]
    exact Nat.le_floor (by linarith)
  have hpcomp : p.comp (Polynomial.C B * Polynomial.X) = r := by
    dsimp [p, r]
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.comp_assoc]
    congr 2
    rw [Polynomial.sub_comp, Polynomial.C_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    ext i
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
    split_ifs <;> field_simp [hB.ne']
  have hscaled :
      (chebNeedle n d q).comp (Polynomial.C B * Polynomial.X) =
        Polynomial.C (1 / (2 * (k : ℝ) ^ 2)) * r.divX := by
    rw [chebNeedle, if_pos hbranch]
    dsimp [k, B, p] at hpcomp ⊢
    rw [Polynomial.mul_comp, Polynomial.C_comp]
    have hshift := C_mul_divX_comp_scale p B
    rw [hpcomp] at hshift
    calc
      Polynomial.C (B / (2 * (k : ℝ) ^ 2)) *
          p.divX.comp (Polynomial.C B * Polynomial.X) =
          Polynomial.C (1 / (2 * (k : ℝ) ^ 2)) *
            (Polynomial.C B * p.divX.comp (Polynomial.C B * Polynomial.X)) := by
              rw [← mul_assoc]
              congr 1
              rw [← Polynomial.C_mul]
              congr 1
              field_simp [hB.ne']
      _ = _ := by rw [hshift]
  have hrnorm : polynomialCoeffOneNorm r ≤
      1 + (1 + Real.sqrt 2) ^ k * 3 ^ k := by
    dsimp [r, T]
    calc
      polynomialCoeffOneNorm
          (1 - (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
            (Polynomial.C 1 - Polynomial.C 2 * Polynomial.X)) ≤
          1 + polynomialCoeffOneNorm
            ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
              (Polynomial.C 1 - Polynomial.C 2 * Polynomial.X)) := by
              calc
                _ ≤ polynomialCoeffOneNorm (1 : Polynomial ℝ) +
                    polynomialCoeffOneNorm
                      ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
                        (Polynomial.C 1 - Polynomial.C 2 * Polynomial.X)) :=
                  polynomialCoeffOneNorm_sub_le _ _
                _ = _ := by
                  rw [show (1 : Polynomial ℝ) = Polynomial.C 1 by simp,
                    polynomialCoeffOneNorm_C]
                  norm_num
      _ ≤ 1 + (polynomialCoeffOneNorm (Polynomial.Chebyshev.T ℝ (k : ℤ)) *
            polynomialCoeffOneNorm
              (Polynomial.C 1 - Polynomial.C 2 * Polynomial.X) ^
                (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree) := by
                  gcongr
                  apply polynomialCoeffOneNorm_comp_le
                  rw [polynomialCoeffOneNorm_one_sub_two_X]
                  norm_num
      _ = 1 + polynomialCoeffOneNorm
          (Polynomial.Chebyshev.T ℝ (k : ℤ)) * 3 ^ k := by
            rw [polynomialCoeffOneNorm_one_sub_two_X,
              Polynomial.Chebyshev.natDegree_T]
            simp
      _ ≤ _ := by
            gcongr
            exact polynomialCoeffOneNorm_chebyshev_le k
  rw [Polynomial.sub_comp, Polynomial.one_comp, hscaled]
  calc
    polynomialCoeffOneNorm
        (1 - Polynomial.C (1 / (2 * (k : ℝ) ^ 2)) * r.divX) ≤
        1 + (1 / (2 * (k : ℝ) ^ 2)) * polynomialCoeffOneNorm r := by
          calc
            _ ≤ polynomialCoeffOneNorm 1 +
                polynomialCoeffOneNorm
                  (Polynomial.C (1 / (2 * (k : ℝ) ^ 2)) * r.divX) :=
              polynomialCoeffOneNorm_sub_le _ _
            _ ≤ 1 + (1 / (2 * (k : ℝ) ^ 2)) *
                polynomialCoeffOneNorm r.divX := by
              rw [show (1 : Polynomial ℝ) = Polynomial.C 1 by simp,
                polynomialCoeffOneNorm_C, abs_one]
              gcongr
              calc
                polynomialCoeffOneNorm
                    (Polynomial.C (1 / (2 * (k : ℝ) ^ 2)) * r.divX) ≤
                    polynomialCoeffOneNorm
                        (Polynomial.C (1 / (2 * (k : ℝ) ^ 2))) *
                      polynomialCoeffOneNorm r.divX :=
                  polynomialCoeffOneNorm_mul_le _ _
                _ = _ := by
                  rw [polynomialCoeffOneNorm_C, abs_of_nonneg]
                  positivity
            _ ≤ _ := by
              gcongr
              exact polynomialCoeffOneNorm_divX_le r
    _ ≤ (8 : ℝ) ^ k := by
      have hsqrt : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
        rw [Real.sqrt_le_iff]
        constructor <;> norm_num
      have hbase : 3 * (1 + Real.sqrt 2) ≤ 8 := by linarith
      have hr8 : polynomialCoeffOneNorm r ≤ 1 + (8 : ℝ) ^ k := by
        calc
          _ ≤ 1 + (1 + Real.sqrt 2) ^ k * 3 ^ k := hrnorm
          _ = 1 + (3 * (1 + Real.sqrt 2)) ^ k := by rw [mul_pow]; ring
          _ ≤ 1 + 8 ^ k := by gcongr
      have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hc0 : 0 ≤ 1 / (2 * (k : ℝ) ^ 2) := by positivity
      have hc8 : 1 / (2 * (k : ℝ) ^ 2) ≤ (1 : ℝ) / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ) ^ 2)).2
        nlinarith
      have hpow : (64 : ℝ) ≤ 8 ^ k := by
        calc
          (64 : ℝ) = 8 ^ 2 := by norm_num
          _ ≤ 8 ^ k := pow_le_pow_right₀ (by norm_num) hk
      nlinarith [mul_le_mul_of_nonneg_left hr8 hc0]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hbranch), [the stated mathematical conclusion holds](goal). -/
lemma needle_scaled_coefficient_oneNorm_le (n d : ℕ) (q : ℝ)
    (hbranch : needleBranch n d q) :
    (∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
      |needleCoeff n d q v * needleRadius n q ^ v|) ≤
        (8 : ℝ) ^ needleDegree n q := by
  let B := needleRadius n q
  let R := (1 - chebNeedle n d q).comp (Polynomial.C B * Polynomial.X)
  calc
    (∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
      |needleCoeff n d q v * needleRadius n q ^ v|) =
        ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), |R.coeff v| := by
          apply Finset.sum_congr rfl
          intro v hv
          dsimp [R, B]
          rw [Polynomial.comp_C_mul_X_coeff]
          simp only [needleCoeff, if_pos hbranch]
    _ ≤ polynomialCoeffOneNorm R :=
      sum_abs_coeff_le_polynomialCoeffOneNorm R _
    _ ≤ (8 : ℝ) ^ needleDegree n q :=
      needle_scaled_polynomial_oneNorm_le n d q hbranch

private lemma needleCoefficientOverlap_le_exp_mul_sq
    (n d : ℕ) (q : ℝ) (lam : ℝ≥0)
    (hbranch : needleBranch n d q) (hlam : (lam : ℝ) ≤ needleRadius n q)
    (L : ℝ)
    (hcoeff : (∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
      |needleCoeff n d q v * needleRadius n q ^ v|) ≤ L) :
    needleCoefficientOverlap n d q lam ≤
      Real.exp ((needleDegree n q : ℝ) ^ 2 / needleRadius n q) * L ^ 2 := by
  let S := Finset.Icc 1 (needleDegree n q - 1)
  let k := needleDegree n q
  let B := needleRadius n q
  have hell := hbranch.1
  have hB : 0 < B := by
    dsimp [B, needleRadius]
    positivity
  have hcoeff0 : 0 ≤ L :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) hcoeff
  unfold needleCoefficientOverlap
  change (∑ v ∈ S, ∑ w ∈ S,
    |needleCoeff n d q v * needleCoeff n d q w| * factorialOverlap lam v w) ≤ _
  calc
    _ ≤ ∑ v ∈ S, ∑ w ∈ S,
        (|needleCoeff n d q v * B ^ v| *
          |needleCoeff n d q w * B ^ w|) *
            Real.exp ((k : ℝ) ^ 2 / B) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      have hvk : v ≤ k := by
        have hh := (Finset.mem_Icc.mp hv).2
        dsimp [k] at hh ⊢
        omega
      have hwk : w ≤ k := by
        have hh := (Finset.mem_Icc.mp hw).2
        dsimp [k] at hh ⊢
        omega
      have hover := factorialOverlap_le_exp lam v w k B hB
        (by simpa [B] using hlam) hvk hwk
      calc
        _ ≤ |needleCoeff n d q v * needleCoeff n d q w| *
            (B ^ (v + w) * Real.exp ((k : ℝ) ^ 2 / B)) := by gcongr
        _ = _ := by
          rw [pow_add, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
            abs_of_pos hB]
          ring
    _ = Real.exp ((k : ℝ) ^ 2 / B) *
        (∑ v ∈ S, |needleCoeff n d q v * B ^ v|) ^ 2 := by
      let A : ℕ → ℝ := fun v => |needleCoeff n d q v * B ^ v|
      change (∑ v ∈ S, ∑ w ∈ S, A v * A w *
        Real.exp ((k : ℝ) ^ 2 / B)) =
          Real.exp ((k : ℝ) ^ 2 / B) * (∑ v ∈ S, A v) ^ 2
      calc
        (∑ v ∈ S, ∑ w ∈ S, A v * A w *
            Real.exp ((k : ℝ) ^ 2 / B)) =
            (∑ v ∈ S, A v * (∑ w ∈ S, A w)) *
                Real.exp ((k : ℝ) ^ 2 / B) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro v hv
                  rw [Finset.mul_sum]
                  rw [Finset.sum_mul]
        _ = _ := by
          rw [← Finset.sum_mul]
          ring
    _ ≤ Real.exp ((k : ℝ) ^ 2 / B) * L ^ 2 := by gcongr

private lemma needle_overlap_exponential_budget (n d : ℕ) (q : ℝ)
    (hbranch : needleBranch n d q) :
    Real.exp ((needleDegree n q : ℝ) ^ 2 / needleRadius n q) *
        ((8 : ℝ) ^ needleDegree n q) ^ 2 ≤
      Real.exp (logScale n q / 8) := by
  let ell := logScale n q
  let k := needleDegree n q
  let B := needleRadius n q
  have hell : 128 ≤ ell := hbranch.1
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hk : (k : ℝ) ≤ ell / 64 := by
    dsimp [k, needleDegree]
    exact Nat.floor_le (by positivity)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hB : B = 256 * ell := by rfl
  have hx : (k : ℝ) ^ 2 / B ≤ ell / 64 := by
    rw [hB]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * ell)).2
    nlinarith [sq_nonneg ((k : ℝ) - ell / 64)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpow : ((8 : ℝ) ^ k) ^ 2 ≤ Real.exp (6 * (k : ℝ)) := by
    calc
      ((8 : ℝ) ^ k) ^ 2 = (8 : ℝ) ^ (k * 2) := by rw [← pow_mul]
      _ = ((2 : ℝ) ^ 3) ^ (k * 2) := by norm_num
      _ = 2 ^ (3 * (k * 2)) := by rw [← pow_mul]
      _ = 2 ^ (6 * k) := by congr 1; omega
      _ ≤ (Real.exp 1) ^ (6 * k) := by gcongr
      _ = Real.exp (6 * (k : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
  calc
    _ ≤ Real.exp ((k : ℝ) ^ 2 / B) * Real.exp (6 * (k : ℝ)) := by gcongr
    _ = Real.exp ((k : ℝ) ^ 2 / B + 6 * (k : ℝ)) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (ell / 8) := by
      gcongr
      nlinarith


/-- For [the specified inputs and assumptions](hyp:n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def NeedleCoefficientOverlapBound (n d : ℕ) (q : ℝ) : Prop :=
  needleBranch n d q → ∀ lam : ℝ≥0, (lam : ℝ) ≤ needleRadius n q →
    needleCoefficientOverlap n d q lam ≤ Real.exp (logScale n q / 8)

/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
lemma needleCoefficientOverlap_bound (n d : ℕ) (q : ℝ) :
    NeedleCoefficientOverlapBound n d q := by
  intro hbranch lam hlam
  exact (needleCoefficientOverlap_le_exp_mul_sq n d q lam hbranch hlam
    ((8 : ℝ) ^ needleDegree n q)
    (needle_scaled_coefficient_oneNorm_le n d q hbranch)).trans
      (needle_overlap_exponential_budget n d q hbranch)

/-- Given [the specified inputs and assumptions](hyp:X,A,B,hAB,v,hv,s), [the stated mathematical conclusion holds](goal). -/
lemma weightedFactorial_le_eventCount_descFactorial
    {X : Type*} [MeasurableSpace X] (A B : Set X) (hAB : A ⊆ B)
    (v : ℕ) (hv : 1 ≤ v) (s : FiniteSample X) :
    weightedFactorial A B v s ≤ (eventCount s B).descFactorial v := by
  have hcount : eventCount s A ≤ eventCount s B := eventCount_mono s hAB
  cases v with
  | zero => omega
  | succ v =>
      unfold weightedFactorial
      simp only [Nat.add_sub_cancel]
      by_cases hB : eventCount s B = 0
      · have hA : eventCount s A = 0 := by omega
        simp [hA, hB]
      · have hpos : 0 < eventCount s B := Nat.pos_of_ne_zero hB
        rw [show eventCount s B = (eventCount s B - 1) + 1 by omega,
          Nat.succ_descFactorial_succ]
        push_cast
        gcongr
        exact_mod_cast (show eventCount s A ≤ eventCount s B - 1 + 1 by omega)

/-- Given [the specified inputs and assumptions](hyp:X,Q,lam,A,B,hA,hB,hAB,v,w,hv,hw), [the stated mathematical conclusion holds](goal). -/
lemma integral_mul_weightedFactorial_le_effective
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    [DecidableEq X] (Q : Measure X) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (v w : ℕ) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    (∫ s, weightedFactorial A B v s * weightedFactorial A B w s
      ∂finitePoissonSampleLaw Q lam) ≤
      factorialOverlap (lam * (Q B).toNNReal) v w := by
  let t : ℝ≥0 := lam * (Q B).toNNReal
  have hWeighted := integrable_mul_weightedFactorial Q lam A B A B
    hA hB hA hB hAB hAB v w hv hw
  have hPoisson : Integrable (fun N : ℕ =>
      (N.descFactorial v : ℝ) * (N.descFactorial w : ℝ))
      (poissonMeasure t) := by
    have hsum := integrable_finsetSum (Finset.range (min v w + 1))
      (fun r _ =>
        (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
          t (v + w - r)).const_mul
            ((v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ)))
    refine hsum.congr (Filter.Eventually.of_forall fun N => ?_)
    change (∑ r ∈ Finset.range (min v w + 1),
      (v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ) *
        (N.descFactorial (v + w - r) : ℝ)) =
          (N.descFactorial v : ℝ) * (N.descFactorial w : ℝ)
    rw [Causalean.Stat.Concentration.Poisson.descFactorial_mul N v w]
  have hmap : Measure.map (fun s : FiniteSample X => eventCount s B)
      (finitePoissonSampleLaw Q lam) = poissonMeasure t := by
    exact finitePoissonSampleLaw_map_eventCount Q lam B hB
  have hCount : Integrable (fun s : FiniteSample X =>
      ((eventCount s B).descFactorial v : ℝ) *
        ((eventCount s B).descFactorial w : ℝ))
      (finitePoissonSampleLaw Q lam) := by
    rw [← hmap] at hPoisson
    exact hPoisson.comp_aemeasurable (measurable_eventCount B hB).aemeasurable
  calc
    _ ≤ ∫ s, ((eventCount s B).descFactorial v : ℝ) *
          ((eventCount s B).descFactorial w : ℝ)
        ∂finitePoissonSampleLaw Q lam := by
      apply integral_mono hWeighted hCount
      intro s
      exact mul_le_mul
        (weightedFactorial_le_eventCount_descFactorial A B hAB v hv s)
        (weightedFactorial_le_eventCount_descFactorial A B hAB w hw s)
        (weightedFactorial_nonneg_le_countFactorial A B hAB w hw s).1
        (by positivity)
    _ = factorialOverlap t v w := by
      unfold factorialOverlap
      have hmixed :=
        Causalean.Stat.Concentration.Poisson.poisson_descFactorial_mixed t v w
      rw [← hmixed, ← hmap]
      have hMap : Integrable (fun N : ℕ =>
          (N.descFactorial v : ℝ) * (N.descFactorial w : ℝ))
          (Measure.map (fun s : FiniteSample X => eventCount s B)
            (finitePoissonSampleLaw Q lam)) := by
        rw [hmap]
        exact hPoisson
      exact (integral_map (measurable_eventCount B hB).aemeasurable
        hMap.aestronglyMeasurable).symm

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,Q,lam), [the stated mathematical conclusion holds](goal). -/
lemma integral_sq_poissonFactorialBranch_le_effective_overlap (n d : ℕ) (q : ℝ)
    (j : Cell d) (Q : Measure (ObsRecord d × Fin 3)) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) :
    (∫ s, (poissonFactorialBranch n d q j s) ^ 2
      ∂finitePoissonSampleLaw Q lam) ≤
      needleCoefficientOverlap n d q
        (lam * (Q (streamEvent 2 j true false)).toNNReal) := by
  by_cases hb : needleBranch n d q
  · let S := Finset.Icc 1 (needleDegree n q - 1)
    let A := streamEvent 2 j true true
    let B := streamEvent 2 j true false
    have hA : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite _)
    have hB : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite _)
    have hAB : A ⊆ B := streamEvent_ones_subset_arrived 2 j
    have hv (v : ℕ) (hvS : v ∈ S) : 1 ≤ v := (Finset.mem_Icc.mp hvS).1
    have hint (v w : ℕ) (hvS : v ∈ S) (hwS : w ∈ S) :
        Integrable (fun s : FiniteSample (ObsRecord d × Fin 3) =>
          (needleCoeff n d q v * weightedFactorial A B v s) *
          (needleCoeff n d q w * weightedFactorial A B w s))
          (finitePoissonSampleLaw Q lam) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (integrable_mul_weightedFactorial Q lam A B A B hA hB hA hB hAB hAB
          v w (hv v hvS) (hv w hwS)).const_mul
            (needleCoeff n d q v * needleCoeff n d q w)
    simp only [poissonFactorialBranch, hb, if_true, pow_two]
    change (∫ s, (∑ v ∈ S, needleCoeff n d q v * weightedFactorial A B v s) *
      (∑ w ∈ S, needleCoeff n d q w * weightedFactorial A B w s)
      ∂finitePoissonSampleLaw Q lam) ≤
        needleCoefficientOverlap n d q (lam * (Q B).toNNReal)
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_le_sum
      intro v hvS
      rw [integral_finsetSum]
      · apply Finset.sum_le_sum
        intro w hwS
        have hfun : (fun s : FiniteSample (ObsRecord d × Fin 3) =>
            (needleCoeff n d q v * weightedFactorial A B v s) *
              (needleCoeff n d q w * weightedFactorial A B w s)) =
            (fun s => (needleCoeff n d q v * needleCoeff n d q w) *
              (weightedFactorial A B v s * weightedFactorial A B w s)) := by
          funext s
          ring
        rw [hfun, integral_const_mul]
        change needleCoeff n d q v * needleCoeff n d q w *
            (∫ s, weightedFactorial A B v s * weightedFactorial A B w s
              ∂finitePoissonSampleLaw Q lam) ≤
          |needleCoeff n d q v * needleCoeff n d q w| *
            factorialOverlap (lam * (Q B).toNNReal) v w
        have hcross := integral_mul_weightedFactorial_le_effective Q lam A B
          hA hB hAB v w (hv v hvS) (hv w hwS)
        have hcross0 : 0 ≤ (∫ s, weightedFactorial A B v s *
            weightedFactorial A B w s ∂finitePoissonSampleLaw Q lam) :=
          integral_nonneg fun s => mul_nonneg
            (weightedFactorial_nonneg_le_countFactorial A B hAB v (hv v hvS) s).1
            (weightedFactorial_nonneg_le_countFactorial A B hAB w (hv w hwS) s).1
        calc
          _ ≤ |needleCoeff n d q v * needleCoeff n d q w| *
              (∫ s, weightedFactorial A B v s * weightedFactorial A B w s
                ∂finitePoissonSampleLaw Q lam) := by
              gcongr
              exact le_abs_self _
          _ ≤ _ := mul_le_mul_of_nonneg_left hcross (abs_nonneg _)
      · intro w hwS
        exact hint v w hvS hwS
    · intro v hvS
      exact integrable_finsetSum S fun w hwS => hint v w hvS hwS
  · simp [poissonFactorialBranch, needleCoefficientOverlap, needleCoeff, hb]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,Q,lam,hbranch,hlam), [the stated mathematical conclusion holds](goal). -/
lemma integral_sq_poissonFactorialBranch_le_exp_effective
    (n d : ℕ) (q : ℝ) (j : Cell d)
    (Q : Measure (ObsRecord d × Fin 3)) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) (hbranch : needleBranch n d q)
    (hlam : ((lam * (Q (streamEvent 2 j true false)).toNNReal : ℝ≥0) : ℝ) ≤
      needleRadius n q) :
    (∫ s, (poissonFactorialBranch n d q j s) ^ 2
      ∂finitePoissonSampleLaw Q lam) ≤ Real.exp (logScale n q / 8) :=
  (integral_sq_poissonFactorialBranch_le_effective_overlap n d q j Q lam).trans
    (needleCoefficientOverlap_bound n d q hbranch _ hlam)

end CausalSmith.Stat.MarRareqLogfrontier
