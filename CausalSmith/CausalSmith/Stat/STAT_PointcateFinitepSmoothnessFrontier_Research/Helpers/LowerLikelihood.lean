module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerDerivativeProduct
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerRegularity
public import Causalean.Stat.Minimax.HellingerAffinity
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Logic.Equiv.Bool

/-! Finite-moment point-CATE frontier: Helpers/LowerLikelihood. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


-- @node: fair_sign_sum
lemma fair_sign_sum {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (∑ v : ι → Bool, sign (v i)) = 0 := by
  let e : (ι → Bool) ≃ (ι → Bool) :=
    Equiv.piCongrRight (fun j => if j = i then Equiv.boolNot else Equiv.refl Bool)
  have he : ∀ v, sign (e v i) = - sign (v i) := by
    intro v
    simp [e, Equiv.piCongrRight, Pi.map_apply]
    cases v i <;> norm_num [sign]
  have h := Equiv.sum_comp e (fun v => sign (v i))
  simp only [he, Finset.sum_neg_distrib] at h
  linarith
-- @node: fair_sign_cross_sum
lemma fair_sign_cross_sum {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    (∑ v : ι → Bool, sign (v i) * sign (v j)) = 0 := by
  let e : (ι → Bool) ≃ (ι → Bool) :=
    Equiv.piCongrRight (fun k => if k = i then Equiv.boolNot else Equiv.refl Bool)
  have he : ∀ v, sign (e v i) * sign (e v j) = -(sign (v i) * sign (v j)) := by
    intro v
    simp [e, Equiv.piCongrRight, Pi.map_apply, hij.symm]
    cases v i <;> cases v j <;> norm_num [sign]
  have h := Equiv.sum_comp e (fun v => sign (v i) * sign (v j))
  simp only [he, Finset.sum_neg_distrib] at h
  linarith

/-- Averaging independent fair signs removes every off-diagonal product. -/
-- @node: fair_sign_weighted_moments
lemma fair_sign_weighted_moments {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (∑ v : ι → Bool, ∑ i, sign (v i) * a i) = 0 ∧
    (∑ v : ι → Bool, (∑ i, sign (v i) * a i)^2) =
      (Fintype.card (ι → Bool) : ℝ) * ∑ i, (a i)^2 := by
  constructor
  · rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, fair_sign_sum, zero_mul]
    simp
  · have hc (i j : ι) : (∑ v : ι → Bool, sign (v i) * sign (v j)) =
        if i = j then (Fintype.card (ι → Bool) : ℝ) else 0 := by
      split_ifs with h
      · subst j
        have hs (v : ι → Bool) : sign (v i) * sign (v i) = 1 := by
          cases v i <;> norm_num [sign]
        simp [hs]
      · exact fair_sign_cross_sum i j h
    simp_rw [pow_two, Fintype.sum_mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    simp_rw [show ∀ v : ι → Bool, ∀ j, (sign (v i) * a i) * (sign (v j) * a j) =
      (sign (v i) * sign (v j)) * (a i * a j) by intros; ring,
      ← Finset.sum_mul, hc]
    simp

variable (κ : Params) (n : ℕ)
/-- Common conditional reference mark law keeps the rare-outcome weights. -/
def referenceMarks : Measure (Bool × ℝ) :=
  (ENNReal.ofReal lowerP0 • Measure.dirac true + ENNReal.ofReal (1-lowerP0) • Measure.dirac false).prod
    (ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (lowerAmplitude κ n) +
     ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (-lowerAmplitude κ n) +
     ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0)
/-- Reference treatment score. -/
def markU (a : Bool) : ℝ := if a then 1/lowerP0 else -1/(1-lowerP0)
/-- Unscaled reference rare-outcome score. -/
def markV (y : ℝ) : ℝ := y/(lowerRare κ n*lowerAmplitude κ n^2)
/-- Normalized intermediate one-record conditional density. -/
def lowerDensity (s t : ℝ) (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ) : ℝ :=
  (1+s*markU z.1*lowerField κ n v x)*
    (1+t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x))
/-- Conditional finite-sign mixture density for any collection of covariate locations. -/
def componentDensity (m : ℕ) (x : Fin m → unitInterval) (s t : ℝ) (z : Fin m → Bool × ℝ) : ℝ :=
  (Fintype.card (Signs κ n) : ℝ)⁻¹ * ∑ v : Signs κ n,
    ∏ i : Fin m, lowerDensity κ n s t v (x i) (z i)
/-- The squared frame makes the sign-averaged field variance deterministic. -/
-- @node: lower_field_sign_moments
lemma lower_field_sign_moments (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (x : unitInterval) :
    (∑ v : Signs κ n, lowerField κ n v x) = 0 ∧
    (∑ v : Signs κ n, (lowerField κ n v x)^2) =
      (Fintype.card (Signs κ n) : ℝ) * lowerSquare κ n x := by
  obtain ⟨hmean, hsecond⟩ := fair_sign_weighted_moments (fun j => frame κ n j x)
  have hframe := (lower_frame_geometry κ n hκ hb hn).1 x
  constructor
  · simp only [lowerField, ← Finset.mul_sum, hmean, mul_zero]
  · simp only [lowerField, mul_pow, ← Finset.mul_sum, hsecond, hframe, mul_one,
      lowerSquare]
    ring

/-- Singleton cancellation is exact on the full rectangle of intermediate amplitudes. -/
-- @node: singleton_cancellation
lemma singleton_cancellation (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (s t : ℝ) (hs : |s| ≤ lowerA κ n) (ht : |t| ≤ lowerB κ n) (x : unitInterval) (z : Bool × ℝ) :
  (Fintype.card (Signs κ n) : ℝ)⁻¹ * (∑ v : Signs κ n, lowerDensity κ n s t v x z) = 1 := by
  obtain ⟨hmean, hsecond⟩ := lower_field_sign_moments κ n hκ hb hn x
  have hcard : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hexpand (v : Signs κ n) : lowerDensity κ n s t v x z =
      (1 - s*t*markU z.1*markV κ n z.2*lowerSquare κ n x) +
      (s*markU z.1 + t*markV κ n z.2 -
        s^2*t*(markU z.1)^2*markV κ n z.2*lowerSquare κ n x) * lowerField κ n v x +
      (s*t*markU z.1*markV κ n z.2) * (lowerField κ n v x)^2 := by
    unfold lowerDensity
    ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hmean, hsecond, mul_zero, add_zero]
  field_simp
  ring
/-- Simultaneous reversal of every latent sign reverses the localized field. -/
-- @node: lower_field_reverse_signs
lemma lower_field_reverse_signs (v : Signs κ n) (x : unitInterval) :
    lowerField κ n (fun j => !(v j)) x = -lowerField κ n v x := by
  have hs (j) : sign (!(v j)) = -sign (v j) := by
    cases v j <;> norm_num [sign]
  simp only [lowerField, hs, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- The finite sign mixture is even in the outcome amplitude on the zero-treatment axis. -/
-- @node: component_density_zero_axis_symmetry
lemma component_density_zero_axis_symmetry (m : ℕ) (x : Fin m → unitInterval)
    (t : ℝ) (z : Fin m → Bool × ℝ) :
    componentDensity κ n m x 0 t z = componentDensity κ n m x 0 (-t) z := by
  let e : Signs κ n ≃ Signs κ n := Equiv.piCongrRight (fun _ => Equiv.boolNot)
  have he (v : Signs κ n) :
      (∏ i, lowerDensity κ n 0 t (e v) (x i) (z i)) =
        ∏ i, lowerDensity κ n 0 (-t) v (x i) (z i) := by
    apply Finset.prod_congr rfl
    intro i _
    have hf : lowerField κ n (e v) (x i) = -lowerField κ n v (x i) := by
      have hev : e v = fun j => !(v j) := by
        funext j
        simp [e, Equiv.piCongrRight, Pi.map_apply, Equiv.boolNot]
      rw [hev]
      exact lower_field_reverse_signs κ n v (x i)
    simp only [lowerDensity, hf, zero_mul, one_mul, add_zero, sub_zero]
    ring
  unfold componentDensity
  congr 1
  rw [← Equiv.sum_comp e (fun v => ∏ i, lowerDensity κ n 0 t v (x i) (z i))]
  exact Finset.sum_congr rfl (fun v _ => he v)

/-- Integrating a function of the reference response is the explicit three-atom average. -/
-- @node: reference_marks_response_integral
lemma reference_marks_response_integral (hκ : κ.Valid) (hn : 2 ≤ n) (f : ℝ → ℝ) :
    (∫ z, f z.2 ∂referenceMarks κ n) =
      (lowerRare κ n/2)*f (lowerAmplitude κ n) +
      (lowerRare κ n/2)*f (-lowerAmplitude κ n) + (1-lowerRare κ n)*f 0 := by
  obtain ⟨hB, hr, _⟩ := lower_rare_scale κ n hκ hn
  have hr0 : 0 ≤ lowerRare κ n := by unfold lowerRare; positivity
  have hi (a w : ℝ) : Integrable f (ENNReal.ofReal w • Measure.dirac a) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold referenceMarks
  rw [integral_fun_snd, integral_add_measure ((hi _ _).add_measure (hi _ _)) (hi _ _),
    integral_add_measure (hi _ _) (hi _ _)]
  have hm : (ENNReal.ofReal lowerP0 • Measure.dirac true +
      ENNReal.ofReal (1-lowerP0) • Measure.dirac false : Measure Bool).real univ = 1 := by
    simp only [Measure.real, lowerP0, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [hm, one_smul]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (div_nonneg hr0 (by norm_num : (0 : ℝ) ≤ 2)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hr)]

/-- The centered unscaled rare-response score has exactly the finite-p second moment. -/
-- @node: reference_markV_moments
lemma reference_markV_moments (hκ : κ.Valid) (hn : 2 ≤ n) :
    (∫ z, markV κ n z.2 ∂referenceMarks κ n) = 0 ∧
    (∫ z, (markV κ n z.2)^2 ∂referenceMarks κ n) =
      lowerAmplitude κ n ^ (κ.p-2)/4 := by
  have hB := (lower_rare_scale κ n hκ hn).1
  have hr : 0 < lowerRare κ n := by unfold lowerRare; positivity
  constructor
  · rw [reference_marks_response_integral κ n hκ hn]
    unfold markV
    ring
  · rw [reference_marks_response_integral κ n hκ hn (fun y => (markV κ n y)^2)]
    simp only [markV, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    calc
      _ = 1/(lowerRare κ n*lowerAmplitude κ n^2) := by field_simp; ring
      _ = lowerAmplitude κ n ^ (κ.p-2)/4 := by
        unfold lowerRare
        rw [← Real.rpow_two, mul_assoc, ← Real.rpow_add hB]
        rw [show -κ.p+2 = -(κ.p-2) by ring, Real.rpow_neg hB.le]
        field_simp

/-- The squared partition and two-active-coordinate property give the sharp field norm. -/
-- @node: lower_field_abs_le_sqrt_two
lemma lower_field_abs_le_sqrt_two (hn : 0 < n) (v : Signs κ n) (x : unitInterval) :
    |lowerField κ n v x| ≤ Real.sqrt 2 := by
  let S := Finset.univ.filter (fun j => frame κ n j x ≠ 0)
  have hs : (∑ j, sign (v j)*frame κ n j x) = ∑ j ∈ S, sign (v j)*frame κ n j x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : frame κ n j x = 0 := by simpa [S] using hj
    simp [hz]
  have hsq : (∑ j ∈ S, (frame κ n j x)^2) = 1 := by
    rw [← frame_square_partition κ n hn x]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : frame κ n j x = 0 := by simpa [S] using hj
    simp [hz]
  have hsign (j) : (sign (v j))^2 = 1 := by cases v j <;> norm_num [sign]
  have hc : (S.card : ℝ) ≤ 2 := by exact_mod_cast frame_active_card κ n x
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => sign (v j)) (fun j => frame κ n j x)
  simp only [hsign, Finset.sum_const, nsmul_eq_mul, mul_one, hsq] at hCS
  have hab : |∑ j, sign (v j)*frame κ n j x| ≤ Real.sqrt 2 := by
    rw [hs]
    have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [sq_abs (∑ j ∈ S, sign (v j)*frame κ n j x)]
  have hk : |lowerCutoff κ n x| ≤ 1 := by
    have hh : 0 ≤ lowerH κ n := by unfold lowerH lowerEll lowerC; positivity
    have hz := div_nonneg (abs_nonneg ((x : ℝ)-1/2)) hh
    rw [lowerCutoff, abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (by linarith)
  rw [lowerField, abs_mul]
  exact (mul_le_mul hk hab (abs_nonneg _) (by norm_num)).trans (by simp)

/-- The derivative ledger uses the rational relaxation of the sharp field norm. -/
-- @node: lower_field_abs_le_three_halves
lemma lower_field_abs_le_three_halves (hn : 0 < n) (v : Signs κ n) (x : unitInterval) :
    |lowerField κ n v x| ≤ 3/2 := by
  apply (lower_field_abs_le_sqrt_two κ n hn v x).trans
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hpos := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The treatment score is uniformly bounded on both reference arms. -/
-- @node: reference_markU_abs_le_three
lemma reference_markU_abs_le_three (a : Bool) : |markU a| ≤ 3 := by
  cases a <;> norm_num [markU, lowerP0]

/-- Polynomial treatment derivative of the one-record density. -/
-- @node: lowerDensityS
def lowerDensityS (s t : ℝ) (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ) : ℝ :=
  markU z.1*lowerField κ n v x + t*markU z.1*markV κ n z.2*
    ((lowerField κ n v x)^2-lowerSquare κ n x) -
    2*s*t*(markU z.1)^2*markV κ n z.2*lowerField κ n v x*lowerSquare κ n x

/-- Polynomial outcome derivative retains the unscaled rare mark. -/
-- @node: lowerDensityT
def lowerDensityT (s : ℝ) (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ) : ℝ :=
  markV κ n z.2*(lowerField κ n v x + s*markU z.1*
    ((lowerField κ n v x)^2-lowerSquare κ n x) -
    s^2*(markU z.1)^2*lowerField κ n v x*lowerSquare κ n x)

/-- Polynomial mixed derivative contains exactly one unscaled rare mark. -/
-- @node: lowerDensityST
def lowerDensityST (s : ℝ) (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ) : ℝ :=
  markV κ n z.2*(markU z.1*((lowerField κ n v x)^2-lowerSquare κ n x) -
    2*s*(markU z.1)^2*lowerField κ n v x*lowerSquare κ n x)

/-- Differentiate the treatment parameter by the ordinary product rule. -/
-- @node: hasDerivAt_lowerDensityS
lemma hasDerivAt_lowerDensityS (s t : ℝ) (v : Signs κ n) (x : unitInterval)
    (z : Bool × ℝ) :
    HasDerivAt (fun s' => lowerDensity κ n s' t v x z) (lowerDensityS κ n s t v x z) s := by
  unfold lowerDensity lowerDensityS
  convert (((hasDerivAt_id s).mul_const (markU z.1*lowerField κ n v x)).const_add 1).mul
    (((((hasDerivAt_id s).mul_const (markU z.1*lowerSquare κ n x)).const_sub
      (lowerField κ n v x)).const_mul (t*markV κ n z.2)).const_add 1) using 1 <;> try rfl
  all_goals (try funext u) <;> (try simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring

/-- Differentiate the affine outcome parameter. -/
-- @node: hasDerivAt_lowerDensityT
lemma hasDerivAt_lowerDensityT (s t : ℝ) (v : Signs κ n) (x : unitInterval)
    (z : Bool × ℝ) :
    HasDerivAt (fun t' => lowerDensity κ n s t' v x z) (lowerDensityT κ n s v x z) t := by
  unfold lowerDensity lowerDensityT
  convert ((((hasDerivAt_id t).mul_const
    (markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x))).const_add 1).const_mul (1+s*markU z.1*lowerField κ n v x)) using 1 <;> try rfl
  all_goals (try funext u) <;> (try simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring

/-- The second derivative follows by differentiating the quadratic treatment polynomial. -/
-- @node: hasDerivAt_lowerDensityST
lemma hasDerivAt_lowerDensityST (s : ℝ) (v : Signs κ n) (x : unitInterval)
    (z : Bool × ℝ) :
    HasDerivAt (fun s' => lowerDensityT κ n s' v x z) (lowerDensityST κ n s v x z) s := by
  unfold lowerDensityT lowerDensityST
  convert (((((hasDerivAt_id s).mul_const
    (markU z.1*((lowerField κ n v x)^2-lowerSquare κ n x))).const_add
    (lowerField κ n v x)).sub (((hasDerivAt_id s).pow 2).mul_const
      ((markU z.1)^2*lowerField κ n v x*lowerSquare κ n x))).const_mul
        (markV κ n z.2)) using 1 <;> try rfl
  all_goals (try funext u) <;> (try simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring

/-- On the intermediate rectangle the four polynomial factors admit a normalized ledger.
Only the outcome and mixed derivatives carry an unscaled rare-mark factor. -/
-- @node: lower_density_derivative_ledger
lemma lower_density_derivative_ledger (hn : 0 < n) (s t : ℝ)
    (hs : |s| ≤ 1/1024) (v : Signs κ n) (x : unitInterval) (z : Bool × ℝ)
    (htv : |t*markV κ n z.2| ≤ 1/4) :
    |lowerDensity κ n s t v x z| ≤ 3/2 ∧
    |lowerDensityS κ n s t v x z| ≤ 6*(3/2) ∧
    |lowerDensityT κ n s v x z| ≤ 2*(3/2)*|markV κ n z.2| ∧
    |lowerDensityST κ n s v x z| ≤ 12*(3/2)*|markV κ n z.2| := by
  have hF := lower_field_abs_le_three_halves κ n hn v x
  have hU := reference_markU_abs_le_three z.1
  have hk := lower_cutoff_range κ n x
  have hK : |lowerSquare κ n x| ≤ 1 := by
    rw [lowerSquare, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hdelta : |(lowerField κ n v x)^2-lowerSquare κ n x| ≤ 13/4 := by
    calc
      _ ≤ |(lowerField κ n v x)^2|+|lowerSquare κ n x| := abs_sub _ _
      _ ≤ 13/4 := by rw [abs_pow]; nlinarith [abs_nonneg (lowerField κ n v x)]
  have hsf : |s*markU z.1*lowerField κ n v x| ≤ (1/1024)*3*(3/2) := by
    simp only [abs_mul]
    gcongr
  have hinner : |t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x)| ≤
      (1/4)*((3/2)+(1/1024)*3) := by
    rw [abs_mul]
    apply mul_le_mul htv _ (abs_nonneg _) (by norm_num)
    calc
      _ ≤ |lowerField κ n v x|+|s*markU z.1*lowerSquare κ n x| := abs_sub _ _
      _ ≤ _ := by simp only [abs_mul]; nlinarith [mul_nonneg (abs_nonneg s) (abs_nonneg (markU z.1)),
        mul_le_mul hs hU (abs_nonneg _) (by norm_num),
        mul_le_mul_of_nonneg_left hK (mul_nonneg (abs_nonneg s) (abs_nonneg (markU z.1)))]
  have hds : |lowerDensityS κ n s t v x z| ≤
      3*(3/2)+(1/4)*3*(13/4)+2*(1/1024)*(1/4)*3^2*(3/2)*1 := by
    unfold lowerDensityS
    calc
      _ ≤ |markU z.1*lowerField κ n v x|+
          |t*markU z.1*markV κ n z.2*((lowerField κ n v x)^2-lowerSquare κ n x)|+
          |2*s*t*(markU z.1)^2*markV κ n z.2*lowerField κ n v x*lowerSquare κ n x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |markU z.1| *|lowerField κ n v x|+
          |t*markV κ n z.2| *|markU z.1| *|(lowerField κ n v x)^2-lowerSquare κ n x|+
          2*|s| *|t*markV κ n z.2| *|markU z.1|^2*|lowerField κ n v x| *|lowerSquare κ n x| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
      _ ≤ _ := by gcongr
  have hdt : |lowerDensityT κ n s v x z| ≤
      |markV κ n z.2| *((3/2)+(1/1024)*3*(13/4)+(1/1024)^2*3^2*(3/2)*1) := by
    unfold lowerDensityT
    rw [abs_mul]
    gcongr
    calc
      _ ≤ |lowerField κ n v x|+|s*markU z.1*((lowerField κ n v x)^2-lowerSquare κ n x)|+
          |s^2*(markU z.1)^2*lowerField κ n v x*lowerSquare κ n x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by simp only [abs_mul, abs_pow]; gcongr
  have hdst : |lowerDensityST κ n s v x z| ≤
      |markV κ n z.2| *(3*(13/4)+2*(1/1024)*3^2*(3/2)*1) := by
    unfold lowerDensityST
    rw [abs_mul]
    gcongr
    calc
      _ ≤ |markU z.1*((lowerField κ n v x)^2-lowerSquare κ n x)|+
          |2*s*(markU z.1)^2*lowerField κ n v x*lowerSquare κ n x| := abs_sub _ _
      _ ≤ _ := by simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; gcongr
  refine ⟨?_, hds.trans (by norm_num), ?_, ?_⟩
  · unfold lowerDensity
    rw [abs_mul]
    have h1 : |1+s*markU z.1*lowerField κ n v x| ≤ 1+|s*markU z.1*lowerField κ n v x| := by
      simpa only [abs_one] using abs_add_le (1 : ℝ) (s*markU z.1*lowerField κ n v x)
    have h2 : |1+t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x)| ≤
        1+|t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x)| := by
      simpa only [abs_one] using abs_add_le (1 : ℝ)
        (t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x))
    calc
      _ ≤ (1+|s*markU z.1*lowerField κ n v x|)*
          (1+|t*markV κ n z.2*(lowerField κ n v x-s*markU z.1*lowerSquare κ n x)|) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (1+(1/1024)*3*(3/2))*(1+(1/4)*((3/2)+(1/1024)*3)) := by gcongr
      _ ≤ 3/2 := by norm_num
  · apply hdt.trans
    nlinarith [abs_nonneg (markV κ n z.2)]
  · apply hdst.trans
    nlinarith [abs_nonneg (markV κ n z.2)]

/-- Averaging the finite sign prior preserves the product-rule envelope. -/
-- @node: component_mixed_derivative_pointwise
lemma component_mixed_derivative_pointwise (hn : 0 < n) (m : ℕ)
    (x : Fin m → unitInterval) (s t : ℝ) (hs : |s| ≤ 1/1024)
    (z : Fin m → Bool × ℝ) (hz : ∀ i, |t*markV κ n (z i).2| ≤ 1/4) :
    |deriv (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s| ≤
      12*(m : ℝ)*(3/2 : ℝ)^m*(∑ i, |markV κ n (z i).2|) := by
  have hjet (v : Signs κ n) := lower_product_derivative_ledger Finset.univ
    (fun i s t => lowerDensity κ n s t v (x i) (z i))
    (fun i s t => lowerDensityS κ n s t v (x i) (z i))
    (fun i s => lowerDensityT κ n s v (x i) (z i))
    (fun i s => lowerDensityST κ n s v (x i) (z i))
    (fun i => |markV κ n (z i).2|) s t
    (fun i => hasDerivAt_lowerDensityS κ n s t v (x i) (z i))
    (fun i u => hasDerivAt_lowerDensityT κ n u t v (x i) (z i))
    (fun i => hasDerivAt_lowerDensityST κ n s v (x i) (z i))
    (fun i => abs_nonneg _)
    (fun i _ => lower_density_derivative_ledger κ n hn s t hs v (x i) (z i) (hz i))
  classical
  choose dS dST dT hS hT hST hP hdS hdT hdST using hjet
  have hinner (u : ℝ) :
      HasDerivAt (fun v => componentDensity κ n m x u v z)
        ((Fintype.card (Signs κ n) : ℝ)⁻¹*∑ v, dT v u) t := by
    exact (HasDerivAt.fun_sum (fun v _ => hT v u)).const_mul _
  have heq : (fun u => deriv (fun v => componentDensity κ n m x u v z) t) =
      (fun u => (Fintype.card (Signs κ n) : ℝ)⁻¹*∑ v, dT v u) := by
    funext u
    exact (hinner u).deriv
  rw [heq, ((HasDerivAt.fun_sum (fun v _ => hST v)).const_mul
    (Fintype.card (Signs κ n) : ℝ)⁻¹).deriv, abs_mul, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hc : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card (Signs κ n) : ℝ)⁻¹*∑ v, |dST v| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card (Signs κ n) : ℝ)⁻¹*
        ∑ v : Signs κ n, (12*(m : ℝ)*(3/2 : ℝ)^m*∑ i, |markV κ n (z i).2|) := by
      gcongr with v
      simpa using hdST v
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, hc]

/-- The reference mark law is a probability measure on the valid construction domain. -/
-- @node: reference_marks_probability
lemma reference_marks_probability (hκ : κ.Valid) (hn : 2 ≤ n) :
    IsProbabilityMeasure (referenceMarks κ n) := by
  have hr := (lower_rare_scale κ n hκ hn).2.1
  have hr0 : 0 ≤ lowerRare κ n := by
    unfold lowerRare
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (lower_rare_scale κ n hκ hn).1.le _)
  constructor
  unfold referenceMarks
  rw [← univ_prod_univ, Measure.prod_prod]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num [lowerP0]) (by norm_num [lowerP0])]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (sub_nonneg.mpr hr)]
  norm_num

/-- Every response function is integrable against the finite reference atoms. -/
-- @node: reference_marks_response_integrable
lemma reference_marks_response_integrable (hκ : κ.Valid) (hn : 2 ≤ n) (f : ℝ → ℝ) :
    Integrable (fun z => f z.2) (referenceMarks κ n) := by
  have hi (a w : ℝ) : Integrable f (ENNReal.ofReal w • Measure.dirac a) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  letI : IsFiniteMeasure (ENNReal.ofReal lowerP0 • Measure.dirac true +
      ENNReal.ofReal (1-lowerP0) • Measure.dirac false : Measure Bool) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    finiteness
  letI : IsFiniteMeasure (ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (lowerAmplitude κ n) +
      ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (-lowerAmplitude κ n) +
      ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0 : Measure ℝ) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    finiteness
  unfold referenceMarks
  exact ((memLp_one_iff_integrable.mpr (((hi _ _).add_measure (hi _ _)).add_measure (hi _ _))).comp_snd _).integrable le_rfl

/-- Intermediate outcome amplitudes times the reference rare mark are bounded almost surely. -/
-- @node: reference_markV_scaled_bound
lemma reference_markV_scaled_bound (hκ : κ.Valid) (hn : 2 ≤ n) (t : ℝ)
    (ht : |t| ≤ lowerB κ n) :
    ∀ᵐ z ∂referenceMarks κ n, |t*markV κ n z.2| ≤ 1/4 := by
  have hB := (lower_rare_scale κ n hκ hn).1
  have hb := (lower_scale_small κ n hκ hn).2.2.1
  have hrB := (lower_rare_scale κ n hκ hn).2.2
  have hatom : ∀ y ∈ ({lowerAmplitude κ n, -lowerAmplitude κ n, 0} : Set ℝ),
      |t*markV κ n y| ≤ 1/4 := by
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · have hid : markV κ n (lowerAmplitude κ n) = 1/(4*lowerB κ n) := by
        unfold markV
        rw [pow_two, ← mul_assoc, hrB]
        field_simp
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 1/(4*lowerB κ n))]
      exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans (by field_simp; norm_num)
    · have hid : markV κ n (-lowerAmplitude κ n) = -(1/(4*lowerB κ n)) := by
        unfold markV
        rw [neg_div, pow_two, ← mul_assoc, hrB]
        congr 1
        field_simp
      rw [hid, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/(4*lowerB κ n))]
      exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans (by field_simp; norm_num)
    · simp [markV]
  have hsupp : ∀ᵐ y ∂(ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (lowerAmplitude κ n) +
      ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (-lowerAmplitude κ n) +
      ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0),
      y ∈ ({lowerAmplitude κ n, -lowerAmplitude κ n, 0} : Set ℝ) := by
    rw [ae_add_measure_iff, ae_add_measure_iff]
    refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩, Measure.ae_smul_measure ?_ _⟩ <;> simp
  unfold referenceMarks
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact Filter.Eventually.of_forall (fun _ => hsupp.mono (fun y hy => hatom y hy))
  · exact measurableSet_le (by unfold markV; fun_prop) measurable_const

/-- Rare-mark second moments, rather than suprema, control the mixed derivative. -/
-- keep: Reusable rare-mark L2 mixed-derivative estimate for the finite-p component likelihood; the current Hellinger assembly uses its finer pointwise estimate directly.
lemma component_mixed_derivative_bound (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (m : ℕ) (x : Fin m → unitInterval) (s t : ℝ)
    (hs : |s| ≤ lowerA κ n) (ht : |t| ≤ lowerB κ n) :
  Real.sqrt (∫ z, (deriv (fun s' => deriv (fun t' => componentDensity κ n m x s' t' z) t) s)^2
    ∂Measure.pi (fun _ : Fin m => referenceMarks κ n)) ≤
  12*(m : ℝ)^2*(3/2 : ℝ)^m*Real.sqrt (lowerAmplitude κ n ^ (κ.p-2)/4) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  let μ := Measure.pi (fun _ : Fin m => referenceMarks κ n)
  let C : ℝ := 12*(m : ℝ)*(3/2 : ℝ)^m
  let σ2 : ℝ := lowerAmplitude κ n ^ (κ.p-2)/4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hσ : 0 ≤ σ2 := by
    dsimp [σ2]
    exact div_nonneg (Real.rpow_nonneg (lower_rare_scale κ n hκ hn).1.le _) (by norm_num)
  have hmarks : ∀ᵐ z ∂μ, ∀ i, |t*markV κ n (z i).2| ≤ 1/4 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => referenceMarks κ n) (i := i)).eventually
      (reference_markV_scaled_bound κ n hκ hn t ht)
  have hi (i : Fin m) : Integrable (fun z : Fin m → Bool × ℝ => (markV κ n (z i).2)^2) μ :=
    integrable_comp_eval (μ := fun _ : Fin m => referenceMarks κ n) (i := i)
      (reference_marks_response_integrable κ n hκ hn (fun y => (markV κ n y)^2))
  have hiSum : Integrable (fun z : Fin m → Bool × ℝ => ∑ i, (markV κ n (z i).2)^2) μ :=
    integrable_finset_sum _ (fun i _ => hi i)
  have hmono : ∀ᵐ z ∂μ,
      (deriv (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s)^2 ≤
        C^2*(m : ℝ)*(∑ i, (markV κ n (z i).2)^2) := by
    filter_upwards [hmarks] with z hz
    have hpoint := component_mixed_derivative_pointwise κ n (by omega) m x s t
      (hs.trans (lower_scale_small κ n hκ hn).2.1.2) z hz
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => |markV κ n (z i).2|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at hCS
    calc
      _ = |deriv (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s|^2 := (sq_abs _).symm
      _ ≤ (C*(∑ i, |markV κ n (z i).2|))^2 :=
        pow_le_pow_left₀ (abs_nonneg _) hpoint 2
      _ ≤ C^2*((m : ℝ)*(∑ i, (markV κ n (z i).2)^2)) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hCS (sq_nonneg C)
      _ = _ := by ring
  have hint : (∫ z, (deriv (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s)^2 ∂μ) ≤
      (12*(m : ℝ)^2*(3/2 : ℝ)^m)^2*σ2 := by
    calc
      _ ≤ ∫ z, C^2*(m : ℝ)*(∑ i, (markV κ n (z i).2)^2) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          (hiSum.const_mul _) hmono
      _ = C^2*(m : ℝ)*∑ i : Fin m, ∫ z : Fin m → Bool × ℝ, (markV κ n (z i).2)^2 ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => hi i)]
      _ = C^2*(m : ℝ)*((m : ℝ)*σ2) := by
        have he (i : Fin m) : (∫ z : Fin m → Bool × ℝ, (markV κ n (z i).2)^2 ∂μ) = σ2 := by
          rw [integral_comp_eval (μ := fun _ : Fin m => referenceMarks κ n) (i := i)
            (reference_marks_response_integrable κ n hκ hn
            (fun y => (markV κ n y)^2)).aestronglyMeasurable]
          exact (reference_markV_moments κ n hκ hn).2
        simp_rw [he]
        simp
      _ = _ := by dsimp [C]; ring
  change Real.sqrt (∫ z, (deriv (fun u => deriv (fun v => componentDensity κ n m x u v z) t) s)^2 ∂μ) ≤ _
  calc
    _ ≤ Real.sqrt ((12*(m : ℝ)^2*(3/2 : ℝ)^m)^2*σ2) := Real.sqrt_le_sqrt hint
    _ = 12*(m : ℝ)^2*(3/2 : ℝ)^m*Real.sqrt σ2 := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
