import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialLift
import Causalean.Mathlib.Analysis.WeightedCauchySchwarz
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Integral.Pi

/-! Generic risk bounds and exact moments for centered factorial polynomials. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: centeredNormalizedPolynomial
/-- Translate a polynomial to normalized coordinates around a center and
subtract its value at that center. -/
noncomputable def centeredNormalizedPolynomial (p : MvPolynomial Cell ℝ)
    (center radius : Cell → ℝ) (centerValue : ℝ) : MvPolynomial Cell ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j => MvPolynomial.C (center j) + MvPolynomial.C (radius j) * MvPolynomial.X j) p -
    MvPolynomial.C centerValue

-- @node: factorialPolynomialLift
/-- Centered factorial lift of every monomial of a normalized polynomial. -/
noncomputable def factorialPolynomialLift (m : ℝ) (p : MvPolynomial Cell ℝ)
    (eval : Cell → ℕ) (center radius : Cell → ℝ) (centerValue : ℝ) : ℝ :=
  let centered := centeredNormalizedPolynomial p center radius centerValue
  ∑ alpha ∈ centered.support, centered.coeff alpha *
    ∏ j : Cell, centeredFactorial m (alpha j) (eval j) (center j) / radius j ^ alpha j

set_option maxHeartbeats 1000000 in
-- The finite polynomial expansion elaborates slowly in this imported helper layer.
-- @node: factorialPolynomialLift_expectation
/-- Under independent Poisson coordinates, the centered factorial lift is
unbiased for the original polynomial minus the declared center value. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated r condition holds](hyp:hr). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma factorialPolynomialLift_expectation
    (m : ℝ) (hm : 0 < m) (q center radius : Cell → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hr : ∀ j, 0 < radius j)
    (p : MvPolynomial Cell ℝ) (centerValue : ℝ) :
    ∫ eval : Cell → ℕ, factorialPolynomialLift m p eval center radius centerValue
      ∂Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal) =
      MvPolynomial.eval q p - centerValue := by
  let mu : Measure (Cell → ℕ) :=
    Measure.pi (fun j : Cell => poissonMeasure (m * q j).toNNReal)
  let centered := centeredNormalizedPolynomial p center radius centerValue
  have hcoordScalar (j : Cell) (h : ℕ) :
      Integrable (fun N : ℕ =>
        centeredFactorial m h N (center j) / radius j ^ h)
        (poissonMeasure (m * q j).toNNReal) := by
    have hscalar : Integrable (fun N : ℕ => centeredFactorial m h N (center j))
        (poissonMeasure (m * q j).toNNReal) := by
      simp only [centeredFactorial]
      apply integrable_finsetSum
      intro t _ht
      have hi := (integrable_fallingFactorial_poisson
        (m * q j).toNNReal t).const_mul
          ((Nat.choose h t : ℝ) * (-center j) ^ (h - t) / m ^ t)
      exact hi.congr (Filter.Eventually.of_forall fun N => by ring)
    exact hscalar.div_const _
  have hprodInt (alpha : Cell →₀ ℕ) :
      Integrable (fun eval : Cell → ℕ => ∏ j : Cell,
        centeredFactorial m (alpha j) (eval j) (center j) /
          radius j ^ alpha j) mu := by
    exact Integrable.fintype_prod fun j => hcoordScalar j (alpha j)
  have hmonomial (alpha : Cell →₀ ℕ) :
      (∫ eval : Cell → ℕ, ∏ j : Cell,
          centeredFactorial m (alpha j) (eval j) (center j) /
            radius j ^ alpha j ∂mu) =
        ∏ j : Cell, ((q j - center j) / radius j) ^ alpha j := by
    dsimp [mu]
    rw [MeasureTheory.integral_fintype_prod_eq_prod
      (fun j N => centeredFactorial m (alpha j) N (center j) /
        radius j ^ alpha j)]
    apply Finset.prod_congr rfl
    intro j _hj
    rw [integral_div,
      integral_centeredFactorial_poisson m (q j) (center j) hm (hq j), div_pow]
  unfold factorialPolynomialLift
  dsimp only
  rw [integral_finsetSum]
  · apply Eq.trans (Finset.sum_congr rfl (fun alpha _ => by
      rw [integral_const_mul, hmonomial]))
    rw [← MvPolynomial.eval_eq']
    change MvPolynomial.eval (fun j => (q j - center j) / radius j) centered = _
    unfold centered centeredNormalizedPolynomial
    rw [map_sub, MvPolynomial.map_eval₂Hom]
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_X]
    congr 1
    apply MvPolynomial.eval₂Hom_congr
    · ext r
      simp
    · funext j
      field_simp [ne_of_gt (hr j)]
      ring
    · rfl
  · intro alpha _halpha
    exact (hprodInt alpha).const_mul _

-- @node: chooseSqFactorialSum_le_exp
/-- The binomial-overlap sum occurring in a centered factorial second moment
is bounded by its exponential generating function. This uses [the exponential-moment parameter is below one](hyp:hrho). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma chooseSqFactorialSum_le_exp (h : ℕ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (∑ l ∈ Finset.range (h + 1),
        (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l * rho ^ l) ≤
      Real.exp ((h : ℝ) ^ 2 * rho) := by
  refine (Finset.sum_le_sum ?_).trans
    (Real.sum_le_exp_of_nonneg (mul_nonneg (sq_nonneg _) hrho) (h + 1))
  intro l hl
  have hc : (Nat.choose h l : ℝ) ≤
      (h : ℝ) ^ l / (Nat.factorial l : ℝ) :=
    Nat.choose_le_pow_div l h
  have hfac : 0 < (Nat.factorial l : ℝ) := by positivity
  have hchoose : 0 ≤ (Nat.choose h l : ℝ) := by positivity
  have hdiv : 0 ≤ (h : ℝ) ^ l / (Nat.factorial l : ℝ) := by positivity
  have hsq : (Nat.choose h l : ℝ) ^ 2 ≤
      ((h : ℝ) ^ l / (Nat.factorial l : ℝ)) ^ 2 :=
    (sq_le_sq₀ hchoose hdiv).2 hc
  have hbase : (Nat.choose h l : ℝ) ^ 2 * (Nat.factorial l : ℝ) ≤
      ((h : ℝ) ^ 2) ^ l / (Nat.factorial l : ℝ) := by
    calc
      (Nat.choose h l : ℝ) ^ 2 * (Nat.factorial l : ℝ) ≤
          ((h : ℝ) ^ l / (Nat.factorial l : ℝ)) ^ 2 *
            (Nat.factorial l : ℝ) :=
        mul_le_mul_of_nonneg_right hsq (le_of_lt hfac)
      _ = ((h : ℝ) ^ 2) ^ l / (Nat.factorial l : ℝ) := by
        field_simp
        ring
  calc
    (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l * rho ^ l ≤
        (((h : ℝ) ^ 2) ^ l / (Nat.factorial l : ℝ)) * rho ^ l :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg hrho _)
    _ = (((h : ℝ) ^ 2 * rho) ^ l) / (Nat.factorial l : ℝ) := by
      rw [mul_pow]
      ring

/-- Clip a real number to the interval of radius `t` around `c`. -/
def clipAround (c t w : ℝ) : ℝ := max (c - t) (min w (c + t))

/-- Clipping around a center cannot increase distance from that center. This uses [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma abs_clipAround_sub_center_le (c t w : ℝ) (ht : 0 ≤ t) :
    |clipAround c t w - c| ≤ |w - c| := by
  unfold clipAround
  by_cases hlo : w < c - t
  · have hmin : min w (c + t) = w := min_eq_left (by linarith)
    rw [hmin, max_eq_left (le_of_lt hlo)]
    rw [abs_of_nonpos (by linarith : c - t - c ≤ 0),
      abs_of_nonpos (by linarith : w - c ≤ 0)]
    linarith
  · have hlo_not : c - t ≤ w := le_of_not_gt hlo
    by_cases hhi : w ≤ c + t
    · rw [min_eq_left hhi, max_eq_right hlo_not]
    · have hhi_not : c + t < w := lt_of_not_ge hhi
      rw [min_eq_right (le_of_lt hhi_not), max_eq_right (by linarith)]
      rw [abs_of_nonneg (by linarith : 0 ≤ c + t - c),
        abs_of_nonneg (by linarith : 0 ≤ w - c)]
      linarith

-- @node: abs_clipAround_sub_center_le_radius
/-- Clipping to the interval centered at `c` with nonnegative radius `t`
stays within distance `t` of its center. This uses [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma abs_clipAround_sub_center_le_radius (c t w : ℝ) (ht : 0 ≤ t) :
    |clipAround c t w - c| ≤ t := by
  unfold clipAround
  by_cases hlo : w < c - t
  · have hmin : min w (c + t) = w := min_eq_left (by linarith)
    rw [hmin, max_eq_left (le_of_lt hlo)]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hlo_not : c - t ≤ w := le_of_not_gt hlo
    by_cases hhi : w ≤ c + t
    · rw [min_eq_left hhi, max_eq_right hlo_not]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    · have hhi_not : c + t < w := lt_of_not_ge hhi
      rw [min_eq_right (le_of_lt hhi_not), max_eq_right (by linarith)]
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- The clipping displacement is controlled by squared distance divided by the radius. This uses [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma abs_clipAround_sub_self_le_sq_div (c t w : ℝ) (ht : 0 < t) :
    |clipAround c t w - w| ≤ (w - c) ^ 2 / t := by
  unfold clipAround
  by_cases hlo : w < c - t
  · have hmin : min w (c + t) = w := min_eq_left (by linarith)
    rw [hmin, max_eq_left (le_of_lt hlo)]
    rw [abs_of_pos (by linarith : 0 < c - t - w)]
    apply (le_div_iff₀ ht).2
    nlinarith [sq_nonneg (w - c + t)]
  · have hlo_not : c - t ≤ w := le_of_not_gt hlo
    by_cases hhi : w ≤ c + t
    · rw [min_eq_left hhi, max_eq_right hlo_not]
      simp only [sub_self, abs_zero]
      exact div_nonneg (sq_nonneg _) (le_of_lt ht)
    · have hhi_not : c + t < w := lt_of_not_ge hhi
      rw [min_eq_right (le_of_lt hhi_not), max_eq_right (by linarith)]
      rw [abs_of_neg (by linarith : c + t - w < 0)]
      apply (le_div_iff₀ ht).2
      nlinarith [sq_nonneg (w - c - t)]

/-- A finite linear combination whose summands have a common `L²` bound is controlled by the coefficient ℓ₁ norm. This uses [the stated r condition holds](hyp:hR), and [the stated x condition holds](hyp:hX), and [the stated x2 condition holds](hyp:hX2). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_sq_finset_sum_le_coeffL1
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hX : ∀ i ∈ S, MemLp (X i) 2 μ)
    (hX2 : ∀ i ∈ S, ∫ ω, (X i ω) ^ 2 ∂μ ≤ R ^ 2) :
    ∫ ω, (∑ i ∈ S, a i * X i ω) ^ 2 ∂μ ≤
      (∑ i ∈ S, |a i|) ^ 2 * R ^ 2 := by
  classical
  let sgn : ι → ℝ := fun i => if 0 ≤ a i then 1 else -1
  have ha (i : ι) : |a i| * sgn i = a i := by
    dsimp [sgn]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have hpoint (ω : Ω) :
      (∑ i ∈ S, a i * X i ω) ^ 2 ≤
        (∑ i ∈ S, |a i|) * ∑ i ∈ S, |a i| * (X i ω) ^ 2 := by
    have hcs := Causalean.Mathlib.Analysis.weighted_inner_sq_le S
      (fun i => |a i|) (fun _ => 1) (fun i => sgn i * X i ω)
      (fun i _ => abs_nonneg (a i))
    have hsgn (i : ι) : (sgn i) ^ 2 = 1 := by
      dsimp [sgn]
      split_ifs <;> norm_num
    calc
      (∑ i ∈ S, a i * X i ω) ^ 2 =
          (∑ i ∈ S, |a i| * (1 * (sgn i * X i ω))) ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [one_mul, ← mul_assoc, ha]
      _ ≤ (∑ i ∈ S, |a i| * 1 ^ 2) *
          ∑ i ∈ S, |a i| * (sgn i * X i ω) ^ 2 := hcs
      _ = (∑ i ∈ S, |a i|) * ∑ i ∈ S, |a i| * (X i ω) ^ 2 := by
        simp only [one_pow, mul_one, mul_pow, hsgn, one_mul]
  have hXi2 (i : ι) (hi : i ∈ S) : Integrable (fun ω => (X i ω) ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq (hX i hi).1).mp (hX i hi)
  have hsumLp : MemLp (fun ω => ∑ i ∈ S, a i * X i ω) 2 μ := by
    exact memLp_finsetSum S fun i hi => (hX i hi).const_mul (a i)
  have hSum : Integrable (fun ω => (∑ i ∈ S, a i * X i ω) ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq hsumLp.1).mp hsumLp
  have hRight : Integrable
      (fun ω => (∑ i ∈ S, |a i|) * ∑ i ∈ S, |a i| * (X i ω) ^ 2) μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i hi
    exact (hXi2 i hi).const_mul _
  calc
    (∫ ω, (∑ i ∈ S, a i * X i ω) ^ 2 ∂μ) ≤
        ∫ ω, (∑ i ∈ S, |a i|) * ∑ i ∈ S, |a i| * (X i ω) ^ 2 ∂μ :=
      integral_mono hSum hRight hpoint
    _ = (∑ i ∈ S, |a i|) *
        ∑ i ∈ S, |a i| * ∫ ω, (X i ω) ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      · apply congrArg
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
      · intro i hi
        exact (hXi2 i hi).const_mul _
    _ ≤ (∑ i ∈ S, |a i|) * ∑ i ∈ S, |a i| * R ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hX2 i hi) (abs_nonneg _)
      · exact Finset.sum_nonneg fun i _ => abs_nonneg _
    _ = (∑ i ∈ S, |a i|) ^ 2 * R ^ 2 := by
      rw [← Finset.sum_mul]
      ring

open Finset

-- @node: cast_choose_mul_choose
private lemma cast_choose_mul_choose {h a l : ℕ} (hla : l ≤ a) (hah : a ≤ h) :
    (Nat.choose h a : ℝ) * Nat.choose a l =
      Nat.choose h l * Nat.choose (h - l) (a - l) := by
  rw [Nat.cast_choose ℝ hah, Nat.cast_choose ℝ hla,
    Nat.cast_choose ℝ (Nat.sub_le_sub_right hah l), Nat.cast_choose ℝ (hla.trans hah)]
  have h1 : h - l - (a - l) = h - a := by omega
  rw [h1]
  field_simp [Nat.factorial_ne_zero]

-- @node: rawTerm
private noncomputable def rawTerm (m q z : ℝ) (h t a b l : ℕ) : ℝ :=
  ((Nat.choose h a : ℝ) * (-z) ^ (h - a) / m ^ a) *
    ((Nat.choose t b : ℝ) * (-z) ^ (t - b) / m ^ b) *
      ((Nat.choose a l : ℝ) * Nat.choose b l * Nat.factorial l *
        (m * q) ^ (a + b - l))

-- @node: rawTerm_eq_zero_of_min_lt
private lemma rawTerm_eq_zero_of_min_lt (m q z : ℝ) (h t a b l : ℕ)
    (hlab : min a b < l) : rawTerm m q z h t a b l = 0 := by
  by_cases ha : a < l
  · rw [rawTerm, Nat.choose_eq_zero_of_lt ha]
    ring
  · have hb : b < l := by omega
    rw [rawTerm, Nat.choose_eq_zero_of_lt hb]
    ring

-- @node: raw_inner_extend
private lemma raw_inner_extend (m q z : ℝ) (h t a b : ℕ) (ha : a ≤ h) (hb : b ≤ t) :
    ∑ l ∈ range (min a b + 1), rawTerm m q z h t a b l =
      ∑ l ∈ range (min h t + 1), rawTerm m q z h t a b l := by
  apply Finset.sum_subset
  · intro l hl
    rw [Finset.mem_range] at hl ⊢
    omega
  · intro l hlbig hlsmall
    apply rawTerm_eq_zero_of_min_lt
    simp only [Finset.mem_range, not_lt] at hlsmall
    omega

-- @node: shiftedTerm
private noncomputable def shiftedTerm (q z : ℝ) (h l a : ℕ) : ℝ :=
  (Nat.choose (h - l) (a - l) : ℝ) * (-z) ^ (h - a) * q ^ (a - l)

-- @node: shiftedTerm0
private noncomputable def shiftedTerm0 (q z : ℝ) (h l a : ℕ) : ℝ :=
  if l ≤ a then shiftedTerm q z h l a else 0

-- @node: rawTerm_factor
private lemma rawTerm_factor (m q z : ℝ) (hm : m ≠ 0) (h t a b l : ℕ)
    (hla : l ≤ a) (ha : a ≤ h) (hlb : l ≤ b) (hb : b ≤ t) :
    rawTerm m q z h t a b l =
      ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
        shiftedTerm q z h l a * shiftedTerm q z t l b := by
  rw [rawTerm, shiftedTerm, shiftedTerm]
  have habsub : a + b - l = (a - l) + (b - l) + l := by omega
  rw [habsub, pow_add, pow_add, mul_pow, div_pow]
  field_simp
  simp only [mul_pow]
  have hh := cast_choose_mul_choose hla ha
  have ht := cast_choose_mul_choose hlb hb
  have hprod :
      (Nat.choose h a : ℝ) * Nat.choose a l * Nat.choose t b * Nat.choose b l =
        Nat.choose h l * Nat.choose (h - l) (a - l) *
          Nat.choose t l * Nat.choose (t - l) (b - l) := by
    calc
      _ = ((Nat.choose h a : ℝ) * Nat.choose a l) *
          ((Nat.choose t b : ℝ) * Nat.choose b l) := by ring
      _ = ((Nat.choose h l : ℝ) * Nat.choose (h - l) (a - l)) *
          ((Nat.choose t l : ℝ) * Nat.choose (t - l) (b - l)) := by rw [hh, ht]
      _ = _ := by ring
  have hmexp : m ^ (a - l) * m ^ (b - l) * m ^ (l * 2) = m ^ a * m ^ b := by
    rw [show l * 2 = l + l by omega, pow_add]
    calc
      m ^ (a - l) * m ^ (b - l) * (m ^ l * m ^ l) =
          (m ^ (a - l) * m ^ l) * (m ^ (b - l) * m ^ l) := by ring
      _ = _ := by
        rw [← pow_add, Nat.sub_add_cancel hla, ← pow_add, Nat.sub_add_cancel hlb]
  let R := z ^ (h - a) * z ^ (t - b) * q ^ (a - l) * q ^ (b - l) * q ^ l *
    (-1 : ℝ) ^ (h - a) * (-1 : ℝ) ^ (t - b)
  calc
    _ = ((Nat.choose h a : ℝ) * Nat.choose a l * Nat.choose t b * Nat.choose b l) *
        (m ^ (a - l) * m ^ (b - l) * m ^ (l * 2)) * R := by ring
    _ = ((Nat.choose h l : ℝ) * Nat.choose (h - l) (a - l) *
          Nat.choose t l * Nat.choose (t - l) (b - l)) *
        (m ^ a * m ^ b) * R := by rw [hprod, hmexp]
    _ = _ := by ring

-- @node: rawTerm_factor0
private lemma rawTerm_factor0 (m q z : ℝ) (hm : m ≠ 0) (h t a b l : ℕ)
    (ha : a ≤ h) (hb : b ≤ t) :
    rawTerm m q z h t a b l =
      ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
        shiftedTerm0 q z h l a * shiftedTerm0 q z t l b := by
  by_cases hla : l ≤ a
  · by_cases hlb : l ≤ b
    · simp only [shiftedTerm0, hla, hlb, ↓reduceIte]
      exact rawTerm_factor m q z hm h t a b l hla ha hlb hb
    · have hbl : b < l := Nat.lt_of_not_ge hlb
      have hzero := rawTerm_eq_zero_of_min_lt m q z h t a b l (by omega)
      simp only [shiftedTerm0, hla, hlb, ↓reduceIte, mul_zero]
      exact hzero
  · have hal : a < l := Nat.lt_of_not_ge hla
    rw [shiftedTerm0, if_neg hla, mul_zero, zero_mul]
    exact rawTerm_eq_zero_of_min_lt m q z h t a b l (by omega)

-- @node: sum_shiftedTerm0
private lemma sum_shiftedTerm0 (q z : ℝ) (h l : ℕ) (hlh : l ≤ h) :
    ∑ a ∈ range (h + 1), shiftedTerm0 q z h l a = (q - z) ^ (h - l) := by
  calc
    _ = ∑ a ∈ Icc l h, shiftedTerm0 q z h l a := by
      symm
      apply Finset.sum_subset
      · intro a ha
        simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢
        omega
      · intro a haRange haIcc
        have hal : a < l := by
          simp only [Finset.mem_range] at haRange
          simp only [Finset.mem_Icc, not_and_or, not_le] at haIcc
          rcases haIcc with haIcc | haIcc
          · exact haIcc
          · omega
        simp [shiftedTerm0, Nat.not_le_of_lt hal]
    _ = ∑ A ∈ range (h - l + 1), shiftedTerm0 q z h l (A + l) := by
      apply Finset.sum_bij (fun a _ => a - l)
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        simp only [Finset.mem_range]
        omega
      · intro a₁ ha₁ a₂ ha₂ heq
        simp only [Finset.mem_Icc] at ha₁ ha₂
        omega
      · intro A hA
        refine ⟨A + l, ?_, ?_⟩
        · simp only [Finset.mem_Icc, Finset.mem_range] at hA ⊢
          omega
        · omega
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        rw [Nat.sub_add_cancel ha.1]
    _ = ∑ A ∈ range (h - l + 1),
        (Nat.choose (h - l) A : ℝ) * (-z) ^ (h - l - A) * q ^ A := by
      apply Finset.sum_congr rfl
      intro A hA
      have hA' : A ≤ h - l := by
        simp only [Finset.mem_range] at hA
        omega
      simp only [shiftedTerm0, shiftedTerm, Nat.le_add_left, ↓reduceIte,
        Nat.add_sub_cancel_right]
      congr 2
      rw [Nat.sub_sub, Nat.add_comm]
    _ = (q + (-z)) ^ (h - l) := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ = _ := by ring

-- @node: rawMoment_collapse
private lemma rawMoment_collapse (m q z : ℝ) (hm : m ≠ 0) (h t : ℕ) :
    (∑ b ∈ range (t + 1), ∑ a ∈ range (h + 1),
      ∑ l ∈ range (min a b + 1), rawTerm m q z h t a b l) =
    ∑ l ∈ range (min h t + 1),
      (Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
        (q / m) ^ l * (q - z) ^ (h + t - 2 * l) := by
  calc
    _ = ∑ b ∈ range (t + 1), ∑ a ∈ range (h + 1),
        ∑ l ∈ range (min h t + 1), rawTerm m q z h t a b l := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      exact raw_inner_extend m q z h t a b
        (by simp only [Finset.mem_range] at ha; omega)
        (by simp only [Finset.mem_range] at hb; omega)
    _ = ∑ a ∈ range (h + 1), ∑ b ∈ range (t + 1),
        ∑ l ∈ range (min h t + 1), rawTerm m q z h t a b l := by
      exact Finset.sum_comm
    _ = ∑ a ∈ range (h + 1), ∑ l ∈ range (min h t + 1),
        ∑ b ∈ range (t + 1), rawTerm m q z h t a b l := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ l ∈ range (min h t + 1), ∑ a ∈ range (h + 1),
        ∑ b ∈ range (t + 1), rawTerm m q z h t a b l := by
      exact Finset.sum_comm
    _ = ∑ l ∈ range (min h t + 1), ∑ b ∈ range (t + 1),
        ∑ a ∈ range (h + 1), rawTerm m q z h t a b l := by
      apply Finset.sum_congr rfl
      intro l _hl
      exact Finset.sum_comm
    _ = ∑ l ∈ range (min h t + 1),
        ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
          (∑ a ∈ range (h + 1), shiftedTerm0 q z h l a) *
          (∑ b ∈ range (t + 1), shiftedTerm0 q z t l b) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlh : l ≤ h := by
        simp only [Finset.mem_range] at hl
        omega
      have hlt : l ≤ t := by
        simp only [Finset.mem_range] at hl
        omega
      calc
        _ = ∑ b ∈ range (t + 1), ∑ a ∈ range (h + 1),
            ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
              shiftedTerm0 q z h l a * shiftedTerm0 q z t l b := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          have ha' : a ≤ h := by simp only [Finset.mem_range] at ha; omega
          have hb' : b ≤ t := by simp only [Finset.mem_range] at hb; omega
          rw [rawTerm_factor0 m q z hm h t a b l ha' hb']
        _ = ∑ b ∈ range (t + 1),
            (∑ a ∈ range (h + 1),
              ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
                shiftedTerm0 q z h l a) *
                shiftedTerm0 q z t l b := by
          apply Finset.sum_congr rfl
          intro b _hb
          exact (Finset.sum_mul (range (h + 1))
            (fun a => ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
              (q / m) ^ l) * shiftedTerm0 q z h l a)
            (shiftedTerm0 q z t l b)).symm
        _ = (∑ a ∈ range (h + 1),
              ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
                (q / m) ^ l) * shiftedTerm0 q z h l a) *
              (∑ b ∈ range (t + 1), shiftedTerm0 q z t l b) := by
          exact (Finset.mul_sum (range (t + 1))
            (fun b => shiftedTerm0 q z t l b)
            (∑ a ∈ range (h + 1),
              ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
                (q / m) ^ l) * shiftedTerm0 q z h l a)).symm
        _ = _ := by
          congr 1
          exact (Finset.mul_sum (range (h + 1))
            (fun a => shiftedTerm0 q z h l a)
            ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
              (q / m) ^ l)).symm
    _ = ∑ l ∈ range (min h t + 1),
        ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l * (q / m) ^ l) *
          (q - z) ^ (h - l) * (q - z) ^ (t - l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlh : l ≤ h := by
        simp only [Finset.mem_range] at hl
        omega
      have hlt : l ≤ t := by
        simp only [Finset.mem_range] at hl
        omega
      rw [sum_shiftedTerm0 q z h l hlh, sum_shiftedTerm0 q z t l hlt]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlh : l ≤ h := by
        simp only [Finset.mem_range] at hl
        omega
      have hlt : l ≤ t := by
        simp only [Finset.mem_range] at hl
        omega
      have hexp : h - l + (t - l) = h + t - 2 * l := by omega
      calc
        _ = ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
            (q / m) ^ l) * ((q - z) ^ (h - l) * (q - z) ^ (t - l)) := by ring
        _ = ((Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
            (q / m) ^ l) * (q - z) ^ (h - l + (t - l)) := by rw [pow_add]
        _ = _ := by rw [hexp]

-- @node: integral_centeredFactorial_mul_poisson
/-- If [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), then [the stated integral centered factorial product poisson relation holds](goal). -/
lemma integral_centeredFactorial_mul_poisson
    (m q z : ℝ) (hm : 0 < m) (hq : 0 ≤ q) (h t : ℕ) :
    (∫ N : ℕ, centeredFactorial m h N z * centeredFactorial m t N z
      ∂ProbabilityTheory.poissonMeasure (m * q).toNNReal) =
      ∑ l ∈ Finset.range (min h t + 1),
        (Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
          (q / m) ^ l * (q - z) ^ (h + t - 2 * l) := by
  rw [integral_centeredFactorial_mul_poisson_expanded]
  have hmq : 0 ≤ m * q := mul_nonneg (le_of_lt hm) hq
  simp only [Real.coe_toNNReal (m * q) hmq]
  simp_rw [Finset.mul_sum]
  change (∑ b ∈ range (t + 1), ∑ a ∈ range (h + 1),
    ∑ l ∈ range (min a b + 1), rawTerm m q z h t a b l) = _
  exact rawMoment_collapse m q z (ne_of_gt hm) h t

-- @node: integral_sq_normalizedCenteredFactorial_le_exp
/-- If the true mean lies within radius `r` of the centering point and the
Poisson noise-to-radius ratio is at most `rho`, the normalized centered
factorial monomial has the exponential L² bound used by the Jackson lift. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated r condition holds](hyp:hr), and [the stated z condition holds](hyp:hz), and [the intensity-to-center ratio satisfies the stated bound](hyp:hratio). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_sq_normalizedCenteredFactorial_le_exp
    (m q z r rho : ℝ) (hm : 0 < m) (hq : 0 ≤ q) (hr : 0 < r)
    (hz : |q - z| ≤ r) (hratio : q / (m * r ^ 2) ≤ rho) (h : ℕ) :
    (∫ N : ℕ, (centeredFactorial m h N z / r ^ h) ^ 2
      ∂ProbabilityTheory.poissonMeasure (m * q).toNNReal) ≤
      Real.exp ((h : ℝ) ^ 2 * rho) := by
  have hrho : 0 ≤ rho :=
    le_trans (by positivity : 0 ≤ q / (m * r ^ 2)) hratio
  have hnorm : |(q - z) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr]
    exact (div_le_one hr).2 hz
  have hnormpow (l : ℕ) (hl : l ≤ h) :
      ((q - z) / r) ^ (2 * (h - l)) ≤ 1 := by
    have habs : |(q - z) / r| ^ (2 * (h - l)) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hnorm
    have hnonneg : 0 ≤ ((q - z) / r) ^ (2 * (h - l)) := by
      rw [pow_mul]
      positivity
    calc
      ((q - z) / r) ^ (2 * (h - l)) =
          |((q - z) / r) ^ (2 * (h - l))| :=
        (abs_of_nonneg hnonneg).symm
      _ = |(q - z) / r| ^ (2 * (h - l)) := abs_pow _ _
      _ ≤ 1 := habs
  rw [show (fun N : ℕ => (centeredFactorial m h N z / r ^ h) ^ 2) =
      fun N => (1 / r ^ (2 * h)) *
        (centeredFactorial m h N z * centeredFactorial m h N z) by
    funext N
    field_simp
    ring]
  rw [integral_const_mul, integral_centeredFactorial_mul_poisson m q z hm hq h h]
  rw [Finset.mul_sum]
  simp only [Nat.min_self]
  refine (Finset.sum_le_sum ?_).trans (chooseSqFactorialSum_le_exp h rho hrho)
  intro l hl
  have hlh : l ≤ h := by
    simp only [Finset.mem_range] at hl
    omega
  have hexp : h + h - 2 * l = 2 * (h - l) := by omega
  rw [hexp]
  have halg :
      1 / r ^ (2 * h) *
          ((Nat.choose h l : ℝ) * Nat.choose h l * Nat.factorial l *
            (q / m) ^ l * (q - z) ^ (2 * (h - l))) =
        (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l *
          (q / (m * r ^ 2)) ^ l * ((q - z) / r) ^ (2 * (h - l)) := by
    simp only [div_pow]
    field_simp [ne_of_gt hm, ne_of_gt hr]
    simp only [mul_pow, pow_mul]
    have hrpow : (r ^ 2) ^ l * (r ^ 2) ^ (h - l) = (r ^ 2) ^ h := by
      rw [← pow_add, Nat.add_sub_of_le hlh]
    rw [← hrpow]
    ring
  rw [halg]
  calc
    (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l *
          (q / (m * r ^ 2)) ^ l * ((q - z) / r) ^ (2 * (h - l)) ≤
        (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l *
          (q / (m * r ^ 2)) ^ l := by
      have hcoefficient : 0 ≤ (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l *
          (q / (m * r ^ 2)) ^ l := by positivity
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hnormpow l hlh) hcoefficient
    _ ≤ (Nat.choose h l : ℝ) ^ 2 * Nat.factorial l * rho ^ l := by
      gcongr

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
