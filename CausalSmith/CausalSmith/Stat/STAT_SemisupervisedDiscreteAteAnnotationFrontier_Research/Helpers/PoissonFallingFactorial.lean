module
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialLift
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Paper-local aliases for the raw Poisson falling-factorial identities. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Finset

private abbrev fallingFactorial (N r : Nat) : Nat :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fallingFactorial N r

/-- A Poisson falling factorial is unbiased for the corresponding power.  [the stated conclusion](goal). -/
lemma integral_descFactorial_poisson (lambda : NNReal) (r : Nat) :
    ∫ N : Nat, (N.descFactorial r : Real) ∂poissonMeasure lambda =
      (lambda : Real) ^ r := by
  simpa [fallingFactorial,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fallingFactorial_eq_descFactorial]
    using CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.integral_fallingFactorial_poisson
      lambda r

/-- A scalar Poisson falling factorial is integrable.  [the stated conclusion](goal). -/
lemma integrable_descFactorial_poisson (lambda : NNReal) (r : Nat) :
    Integrable (fun N : Nat ↦ (N.descFactorial r : Real))
      (poissonMeasure lambda) := by
  simpa [fallingFactorial,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fallingFactorial_eq_descFactorial]
    using CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.integrable_fallingFactorial_poisson
      lambda r

/-- Exact second cross-moment of two Poisson falling factorials.  [the stated conclusion](goal). -/
lemma integral_descFactorial_mul_poisson (lambda : NNReal) (r v : Nat) :
    (∫ N : Nat, (N.descFactorial r : Real) * N.descFactorial v
      ∂poissonMeasure lambda) =
      ∑ h ∈ range (min r v + 1),
        (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h *
          (lambda : Real) ^ (r + v - h) := by
  simpa [fallingFactorial,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fallingFactorial_eq_descFactorial]
    using CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.integral_fallingFactorial_mul_poisson
      lambda r v

/-- Exact scalar Poisson second moment.  [the stated conclusion](goal). -/
lemma integral_natCast_sq_poisson (lambda : NNReal) :
    (∫ N : Nat, (N : Real) ^ 2 ∂poissonMeasure lambda) =
      (lambda : Real) + (lambda : Real) ^ 2 := by
  have h := integral_descFactorial_mul_poisson lambda 1 1
  norm_num [Finset.sum_range_succ] at h
  simpa [pow_two, add_comm] using h

/-- Products of Poisson falling factorials are integrable.  [the stated conclusion](goal). -/
lemma integrable_descFactorial_mul_poisson (lambda : NNReal) (r v : Nat) :
    Integrable (fun N : Nat ↦
      (N.descFactorial r : Real) * N.descFactorial v)
      (poissonMeasure lambda) := by
  simpa [fallingFactorial,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fallingFactorial_eq_descFactorial]
    using CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.integrable_fallingFactorial_mul_poisson
      lambda r v

/-- A Poisson falling factorial has every fixed finite second moment.  [the stated conclusion](goal). -/
lemma memLp_descFactorial_poisson (lambda : NNReal) (r : Nat) :
    MemLp (fun N : Nat ↦ (N.descFactorial r : Real)) 2
      (poissonMeasure lambda) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_of_countable _).aestronglyMeasurable).2
  convert integrable_descFactorial_mul_poisson lambda r r using 1
  funext N
  ring

/-- The overlap coefficient in a joint falling-factorial moment has the
exponential-series bound used by the paper.  [the stated conditions](hyp:hr,hv) [the stated conclusion](goal). -/
lemma choose_choose_factorial_div_le
    {L r v h : Nat} (hr : r ≤ L) (hv : v ≤ L) :
    (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h /
        (L : Real) ^ h ≤
      (L : Real) ^ h / Nat.factorial h := by
  by_cases hL0 : L = 0
  · subst L
    have : r = 0 ∧ v = 0 := ⟨Nat.eq_zero_of_le_zero hr, Nat.eq_zero_of_le_zero hv⟩
    rcases this with ⟨rfl, rfl⟩
    cases h <;> norm_num
  have hLp : (0 : Real) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  by_cases hh : h ≤ r ∧ h ≤ v
  · have hfac : (0 : Real) < Nat.factorial h := by positivity
    have hcr : (Nat.choose r h : Real) ≤
        (r : Real) ^ h / Nat.factorial h := Nat.choose_le_pow_div h r
    have hcv : (Nat.choose v h : Real) ≤
        (v : Real) ^ h / Nat.factorial h := Nat.choose_le_pow_div h v
    have hrL : (r : Real) ≤ L := by exact_mod_cast hr
    have hvL : (v : Real) ≤ L := by exact_mod_cast hv
    have hrpow : (r : Real) ^ h ≤ (L : Real) ^ h :=
      pow_le_pow_left₀ (by positivity) hrL h
    have hvpow : (v : Real) ^ h ≤ (L : Real) ^ h :=
      pow_le_pow_left₀ (by positivity) hvL h
    have hcr' : (Nat.choose r h : Real) ≤ (L : Real) ^ h / Nat.factorial h :=
      hcr.trans (div_le_div_of_nonneg_right hrpow hfac.le)
    have hcv' : (Nat.choose v h : Real) ≤ (L : Real) ^ h / Nat.factorial h :=
      hcv.trans (div_le_div_of_nonneg_right hvpow hfac.le)
    have hc0 : (0 : Real) ≤ Nat.choose r h := by positivity
    have hv0 : (0 : Real) ≤ Nat.choose v h := by positivity
    calc
      (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h /
          (L : Real) ^ h ≤
          (((L : Real) ^ h / Nat.factorial h) *
            ((L : Real) ^ h / Nat.factorial h) * Nat.factorial h) /
              (L : Real) ^ h := by gcongr
      _ = (L : Real) ^ h / Nat.factorial h := by field_simp
  · rcases not_and_or.mp hh with hh | hh
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hh)]
      simp
      exact div_nonneg (pow_nonneg (show (0 : Real) ≤ L by positivity) _)
        (show (0 : Real) ≤ Nat.factorial h by positivity)
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hh)]
      simp
      exact div_nonneg (pow_nonneg (show (0 : Real) ≤ L by positivity) _)
        (show (0 : Real) ≤ Nat.factorial h by positivity)

/-- A finite initial segment of the exponential series at a natural argument
is bounded by `3^L`.  [the stated conclusion](goal). -/
lemma sum_pow_div_factorial_le_three_pow (L : Nat) :
    ∑ h ∈ range (L + 1), (L : Real) ^ h / Nat.factorial h ≤ (3 : Real) ^ L := by
  calc
    ∑ h ∈ range (L + 1), (L : Real) ^ h / Nat.factorial h ≤
        Real.exp (L : Real) := by
          simpa using Real.sum_le_exp_of_nonneg (show (0 : Real) ≤ L by positivity) (L + 1)
    _ ≤ Real.exp (Real.log 3 * L) := by
      apply Real.exp_le_exp.mpr
      have hlog : (1 : Real) ≤ Real.log 3 := by
        apply Real.exp_le_exp.mp
        rw [Real.exp_log (by norm_num : (0 : Real) < 3)]
        exact Real.exp_one_lt_three.le
      nlinarith
    _ = (3 : Real) ^ L := by
      rw [Real.exp_mul, Real.exp_log (by norm_num)]
      norm_num

/-- One overlap layer of a normalized joint factorial moment is bounded by
the corresponding exponential-series layer.  [the stated conditions](hyp:hD,hz,hLD,hr,hv,hh) [the stated conclusion](goal). -/
lemma normalized_overlap_term_le
    {L r v h : Nat} {D z : Real} (hD : 0 < D) (hz : 0 ≤ z)
    (hLD : (L : Real) ≤ D) (hr : r ≤ L) (hv : v ≤ L)
    (hh : h ≤ min r v) :
    ((Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h *
        (D * z) ^ (r + v - h)) / D ^ (r + v) ≤
      ((L : Real) ^ h / Nat.factorial h) * (1 + z) ^ (r + v) := by
  by_cases hL0 : L = 0
  · subst L
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    have hv0 : v = 0 := Nat.eq_zero_of_le_zero hv
    subst r
    subst v
    have hh0 : h = 0 := by simpa using hh
    subst h
    norm_num
  have hhR : h ≤ r := hh.trans (min_le_left _ _)
  have hhV : h ≤ v := hh.trans (min_le_right _ _)
  have hhSum : h ≤ r + v := hhR.trans (Nat.le_add_right r v)
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hLr : (0 : Real) < L := by exact_mod_cast hLpos
  have hDpow : (L : Real) ^ h ≤ D ^ h :=
    pow_le_pow_left₀ hLr.le hLD h
  have hcoef0 : 0 ≤
      (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h := by positivity
  have hcoefD :
      (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h / D ^ h ≤
        (Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h /
          (L : Real) ^ h := by
    exact div_le_div_of_nonneg_left hcoef0 (pow_pos hLr h) hDpow
  have hcoef := hcoefD.trans (choose_choose_factorial_div_le hr hv)
  have hzbase : z ≤ 1 + z := by linarith
  have hzpow : z ^ (r + v - h) ≤ (1 + z) ^ (r + v) := by
    calc
      z ^ (r + v - h) ≤ (1 + z) ^ (r + v - h) :=
        pow_le_pow_left₀ hz hzbase _
      _ ≤ (1 + z) ^ (r + v) :=
        pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hid :
      ((Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h *
          (D * z) ^ (r + v - h)) / D ^ (r + v) =
        ((Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h / D ^ h) *
          z ^ (r + v - h) := by
    rw [mul_pow]
    field_simp
    have hp : D ^ (r + v - h) * D ^ h = D ^ (r + v) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (Nat.choose r h : Real) * Nat.choose v h * D ^ (r + v - h) *
          z ^ (r + v - h) * D ^ h =
          ((Nat.choose r h : Real) * Nat.choose v h) *
            (D ^ (r + v - h) * D ^ h) * z ^ (r + v - h) := by ring
      _ = ((Nat.choose r h : Real) * Nat.choose v h) * D ^ (r + v) *
          z ^ (r + v - h) := by rw [hp]
      _ = (Nat.choose r h : Real) * Nat.choose v h * z ^ (r + v - h) *
          D ^ (r + v) := by ring
  rw [hid]
  exact mul_le_mul hcoef hzpow (pow_nonneg hz _) (by positivity)

/-- Uniform normalized cross-moment sum for orders at most `L`.  [the stated conditions](hyp:hD,hz,hLD,hr,hv) [the stated conclusion](goal). -/
lemma normalized_overlap_sum_le
    {L r v : Nat} {D z : Real} (hD : 0 < D) (hz : 0 ≤ z)
    (hLD : (L : Real) ≤ D) (hr : r ≤ L) (hv : v ≤ L) :
    ∑ h ∈ range (min r v + 1),
        ((Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h *
          (D * z) ^ (r + v - h)) / D ^ (r + v) ≤
      (3 : Real) ^ L * (1 + z) ^ (r + v) := by
  calc
    ∑ h ∈ range (min r v + 1),
        ((Nat.choose r h : Real) * Nat.choose v h * Nat.factorial h *
          (D * z) ^ (r + v - h)) / D ^ (r + v) ≤
        ∑ h ∈ range (min r v + 1),
          ((L : Real) ^ h / Nat.factorial h) * (1 + z) ^ (r + v) := by
            apply Finset.sum_le_sum
            intro h hh
            exact normalized_overlap_term_le hD hz hLD hr hv
              (Nat.le_of_lt_succ (Finset.mem_range.mp hh))
    _ ≤ ∑ h ∈ range (L + 1),
          ((L : Real) ^ h / Nat.factorial h) * (1 + z) ^ (r + v) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        simp only [Finset.mem_range] at hh ⊢
        omega
      · intro h _ _
        positivity
    _ = (∑ h ∈ range (L + 1), (L : Real) ^ h / Nat.factorial h) *
          (1 + z) ^ (r + v) := by rw [Finset.sum_mul]
    _ ≤ (3 : Real) ^ L * (1 + z) ^ (r + v) := by
      gcongr
      exact sum_pow_div_factorial_le_three_pow L

/-- Product-Poisson `L²` control for two normalized falling factorials.  [the stated conditions](hyp:hD,hz,hLD,hr,hv) [the stated conclusion](goal). -/
lemma integral_normalized_descFactorial_cross_le
    {L r v : Nat} {D z : Real} (hD : 0 < D) (hz : 0 ≤ z)
    (hLD : (L : Real) ≤ D) (hr : r ≤ L) (hv : v ≤ L) :
    (∫ N : Nat,
        ((N.descFactorial r : Real) * N.descFactorial v) / D ^ (r + v)
      ∂poissonMeasure (Real.toNNReal (D * z))) ≤
      (3 : Real) ^ L * (1 + z) ^ (r + v) := by
  rw [integral_div]
  rw [integral_descFactorial_mul_poisson]
  have hDz : 0 ≤ D * z := mul_nonneg hD.le hz
  rw [Real.coe_toNNReal _ hDz]
  rw [Finset.sum_div]
  exact normalized_overlap_sum_le hD hz hLD hr hv

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
