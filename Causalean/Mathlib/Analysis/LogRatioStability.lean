import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

/-!
# Uniform C1 stability of positive log-ratio derivatives

This module defines explicit uniform `C¹` and `C²` control on a set.  It proves continuity of
reciprocal, quotient, logarithm, and the within-derivative of a positive log ratio under uniform
`C¹` convergence, then packages openness of a strict fixed-sign derivative margin on a compact
real interval.
-/

open Set Filter

noncomputable section

namespace Causalean.Mathlib.Analysis

/-- A sequence of real-valued functions converges uniformly on `K` when every positive error
tolerance eventually controls all points of `K`. -/
def UniformlyOn {α : Type*} (K : Set α) (f : ℕ → α → ℝ) (g : α → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ K, |f n x - g x| < ε

/-- Uniform `C¹` convergence on a real set means uniform convergence of both function values and
their first within-derivatives. -/
def UniformC1On (K : Set ℝ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  UniformlyOn K f g ∧
    UniformlyOn K (fun n x ↦ derivWithin (f n) K x) (fun x ↦ derivWithin g K x)

/-- Two real functions are uniformly `C¹`-close on a set when both values and first
within-derivatives differ by less than the same radius everywhere on the set. -/
def C1CloseOn (K : Set ℝ) (ε : ℝ) (f g : ℝ → ℝ) : Prop :=
  (∀ x ∈ K, |f x - g x| < ε) ∧
    ∀ x ∈ K, |derivWithin f K x - derivWithin g K x| < ε

/-- Two real functions are uniformly `C²`-close when they are uniformly `C¹`-close and their
second within-derivatives differ by less than the same radius. -/
def C2CloseOn (K : Set ℝ) (ε : ℝ) (f g : ℝ → ℝ) : Prop :=
  C1CloseOn K ε f g ∧
    ∀ x ∈ K,
      |derivWithin (fun y ↦ derivWithin f K y) K x -
        derivWithin (fun y ↦ derivWithin g K y) K x| < ε

/-- The log ratio of `q` to `p` is the pointwise function `x ↦ log (q x / p x)`. -/
def logRatio (q p : ℝ → ℝ) (x : ℝ) : ℝ := Real.log (q x / p x)

/-- Uniform convergence is preserved by reciprocals when every approximating denominator and its
limit share one strictly positive lower bound. -/
theorem uniformlyOn_inv_of_lowerBound {α : Type*} {K : Set α}
    {f : ℕ → α → ℝ} {g : α → ℝ} {m : ℝ}
    (hm : 0 < m) (hconv : UniformlyOn K f g)
    (hlower : ∀ n x, x ∈ K → m ≤ f n x)
    (hlower_limit : ∀ x, x ∈ K → m ≤ g x) :
    UniformlyOn K (fun n x ↦ (f n x)⁻¹) (fun x ↦ (g x)⁻¹) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε * m ^ 2) (mul_pos hε (sq_pos_of_pos hm))
  refine ⟨N, fun n hn x hx ↦ ?_⟩
  have hfn : 0 < f n x := hm.trans_le (hlower n x hx)
  have hg : 0 < g x := hm.trans_le (hlower_limit x hx)
  rw [inv_sub_inv hfn.ne' hg.ne', abs_div, abs_of_pos (mul_pos hfn hg)]
  apply (div_lt_iff₀ (mul_pos hfn hg)).2
  calc
    |g x - f n x| = |f n x - g x| := abs_sub_comm _ _
    _ < ε * m ^ 2 := hN n hn x hx
    _ ≤ ε * (f n x * g x) := by
      gcongr
      nlinarith [hlower n x hx, hlower_limit x hx]

/-- Uniform convergence is preserved by quotients on a compact set when numerators converge to a
continuous limit and denominators share a strictly positive lower bound. -/
theorem uniformlyOn_div_of_lowerBound {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K)
    {u : ℕ → α → ℝ} {v : ℕ → α → ℝ} {u₀ v₀ : α → ℝ} {m : ℝ}
    (hm : 0 < m) (hu : UniformlyOn K u u₀) (hv : UniformlyOn K v v₀)
    (hu₀ : ContinuousOn u₀ K)
    (hlower : ∀ n x, x ∈ K → m ≤ v n x)
    (hlower_limit : ∀ x, x ∈ K → m ≤ v₀ x) :
    UniformlyOn K (fun n x ↦ u n x / v n x) (fun x ↦ u₀ x / v₀ x) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu₀
  have hinv := uniformlyOn_inv_of_lowerBound hm hv hlower hlower_limit
  intro ε hε
  let B := |C| + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one
  obtain ⟨Nu, hNu⟩ := hu (ε * m / 2) (by positivity)
  obtain ⟨Nv, hNv⟩ := hinv (ε / (2 * B)) (by positivity)
  refine ⟨max Nu Nv, fun n hn x hx ↦ ?_⟩
  have hnu := hNu n (le_trans (le_max_left _ _) hn) x hx
  have hnv := hNv n (le_trans (le_max_right _ _) hn) x hx
  have hvpos : 0 < v n x := hm.trans_le (hlower n x hx)
  have hv_inv : |(v n x)⁻¹| ≤ m⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hvpos)]
    exact (inv_le_inv₀ hvpos hm).2 (hlower n x hx)
  have hu₀_bound : |u₀ x| < B :=
    (hC x hx).trans_lt (lt_of_le_of_lt (le_abs_self C) (lt_add_one _))
  have hfirst : |u n x - u₀ x| * |(v n x)⁻¹| < (ε * m / 2) * m⁻¹ := by
    calc
      _ < (ε * m / 2) * |(v n x)⁻¹| :=
        mul_lt_mul_of_pos_right hnu (abs_pos.mpr (inv_ne_zero hvpos.ne'))
      _ ≤ (ε * m / 2) * m⁻¹ := mul_le_mul_of_nonneg_left hv_inv (by positivity)
  have hsecond : |u₀ x| * |(v n x)⁻¹ - (v₀ x)⁻¹| < B * (ε / (2 * B)) := by
    calc
      _ ≤ B * |(v n x)⁻¹ - (v₀ x)⁻¹| :=
        mul_le_mul_of_nonneg_right hu₀_bound.le (abs_nonneg _)
      _ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hnv hB
  change |u n x / v n x - u₀ x / v₀ x| < ε
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    |u n x * (v n x)⁻¹ - u₀ x * (v₀ x)⁻¹| =
        |(u n x - u₀ x) * (v n x)⁻¹ + u₀ x * ((v n x)⁻¹ - (v₀ x)⁻¹)| := by
          congr 1
          ring
    _ ≤ |u n x - u₀ x| * |(v n x)⁻¹| +
        |u₀ x| * |(v n x)⁻¹ - (v₀ x)⁻¹| := by
          simpa only [abs_mul] using
            abs_add_le ((u n x - u₀ x) * (v n x)⁻¹)
              (u₀ x * ((v n x)⁻¹ - (v₀ x)⁻¹))
    _ < (ε * m / 2) * m⁻¹ + B * (ε / (2 * B)) := add_lt_add hfirst hsecond
    _ = ε := by field_simp; ring

/-- Uniform convergence is preserved by the real logarithm when all functions share a strictly
positive lower bound. -/
theorem uniformlyOn_log_of_lowerBound {α : Type*} {K : Set α}
    {f : ℕ → α → ℝ} {g : α → ℝ} {m : ℝ}
    (hm : 0 < m) (hconv : UniformlyOn K f g)
    (hlower : ∀ n x, x ∈ K → m ≤ f n x)
    (hlower_limit : ∀ x, x ∈ K → m ≤ g x) :
    UniformlyOn K (fun n x ↦ Real.log (f n x)) (fun x ↦ Real.log (g x)) := by
  have hlog_lip : ∀ {r s : ℝ}, m ≤ r → m ≤ s →
      |Real.log r - Real.log s| ≤ m⁻¹ * |r - s| := by
    intro r s hr hs
    simpa only [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := Real.log) (f' := fun y : ℝ ↦ y⁻¹) (C := m⁻¹)
        (fun y hy ↦ (Real.hasDerivAt_log (hm.trans_le hy).ne').hasDerivWithinAt)
        (fun y hy ↦ by
          have hypos : 0 < y := hm.trans_le hy
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hypos)]
          exact (inv_le_inv₀ hypos hm).2 hy)
        (convex_Ici m) hs hr)
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε * m) (mul_pos hε hm)
  refine ⟨N, fun n hn x hx ↦ ?_⟩
  change |Real.log (f n x) - Real.log (g x)| < ε
  calc
    _ ≤ m⁻¹ * |f n x - g x| := hlog_lip (hlower n x hx) (hlower_limit x hx)
    _ < m⁻¹ * (ε * m) := mul_lt_mul_of_pos_left (hN n hn x hx) (inv_pos.mpr hm)
    _ = ε := by field_simp

/-- On a nondegenerate compact interval, the within-derivative of a positive log ratio is the
difference of the two logarithmic derivatives. -/
theorem derivWithin_logRatio {a b : ℝ} (hab : a < b)
    {q p : ℝ → ℝ} (hq : DifferentiableOn ℝ q (Icc a b))
    (hp : DifferentiableOn ℝ p (Icc a b))
    (hqpos : ∀ x ∈ Icc a b, 0 < q x) (hppos : ∀ x ∈ Icc a b, 0 < p x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    derivWithin (logRatio q p) (Icc a b) x =
      derivWithin q (Icc a b) x / q x - derivWithin p (Icc a b) x / p x := by
  have hq_at := hq x hx
  have hp_at := hp x hx
  have hqne : q x ≠ 0 := (hqpos x hx).ne'
  have hpne : p x ≠ 0 := (hppos x hx).ne'
  have hunique := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt hx
  have hdiv : DifferentiableWithinAt ℝ (fun y ↦ q y / p y) (Icc a b) x :=
    hq_at.div hp_at hpne
  have hdiv_deriv := derivWithin_div hq_at hp_at hpne
  change derivWithin (fun y ↦ q y / p y) (Icc a b) x = _ at hdiv_deriv
  change derivWithin (fun y ↦ Real.log (q y / p y)) (Icc a b) x = _
  rw [derivWithin.log hdiv (div_ne_zero hqne hpne) hunique]
  rw [hdiv_deriv]
  field_simp

/-- Positive pairs converging uniformly in `C¹` to `C¹` limits on a compact interval have log
ratios converging uniformly in `C¹`, provided the whole family shares one positive lower bound. -/
theorem uniformC1On_logRatio {a b m : ℝ} (hab : a < b) (hm : 0 < m)
    {q p : ℕ → ℝ → ℝ} {q₀ p₀ : ℝ → ℝ}
    (hqdiff : ∀ n, DifferentiableOn ℝ (q n) (Icc a b))
    (hpdiff : ∀ n, DifferentiableOn ℝ (p n) (Icc a b))
    (hq₀diff : ContDiffOn ℝ 1 q₀ (Icc a b))
    (hp₀diff : ContDiffOn ℝ 1 p₀ (Icc a b))
    (hqconv : UniformC1On (Icc a b) q q₀)
    (hpconv : UniformC1On (Icc a b) p p₀)
    (hqlower : ∀ n x, x ∈ Icc a b → m ≤ q n x)
    (hplower : ∀ n x, x ∈ Icc a b → m ≤ p n x)
    (hq₀lower : ∀ x, x ∈ Icc a b → m ≤ q₀ x)
    (hp₀lower : ∀ x, x ∈ Icc a b → m ≤ p₀ x) :
    UniformC1On (Icc a b) (fun n ↦ logRatio (q n) (p n)) (logRatio q₀ p₀) := by
  have hqpos : ∀ n x, x ∈ Icc a b → 0 < q n x :=
    fun n x hx ↦ hm.trans_le (hqlower n x hx)
  have hppos : ∀ n x, x ∈ Icc a b → 0 < p n x :=
    fun n x hx ↦ hm.trans_le (hplower n x hx)
  have hq₀pos : ∀ x, x ∈ Icc a b → 0 < q₀ x :=
    fun x hx ↦ hm.trans_le (hq₀lower x hx)
  have hp₀pos : ∀ x, x ∈ Icc a b → 0 < p₀ x :=
    fun x hx ↦ hm.trans_le (hp₀lower x hx)
  have hsub : ∀ {u v : ℕ → ℝ → ℝ} {u₀ v₀ : ℝ → ℝ},
      UniformlyOn (Icc a b) u u₀ → UniformlyOn (Icc a b) v v₀ →
      UniformlyOn (Icc a b) (fun n x ↦ u n x - v n x) (fun x ↦ u₀ x - v₀ x) := by
    intro u v u₀ v₀ hu hv ε hε
    obtain ⟨Nu, hNu⟩ := hu (ε / 2) (by positivity)
    obtain ⟨Nv, hNv⟩ := hv (ε / 2) (by positivity)
    refine ⟨max Nu Nv, fun n hn x hx ↦ ?_⟩
    calc
      |(u n x - v n x) - (u₀ x - v₀ x)| =
          |(u n x - u₀ x) - (v n x - v₀ x)| := by ring_nf
      _ ≤ |u n x - u₀ x| + |v n x - v₀ x| := by
        simpa only [sub_eq_add_neg, Real.norm_eq_abs, norm_neg] using
          norm_add_le (u n x - u₀ x) (-(v n x - v₀ x))
      _ < ε / 2 + ε / 2 := add_lt_add
        (hNu n (le_trans (le_max_left _ _) hn) x hx)
        (hNv n (le_trans (le_max_right _ _) hn) x hx)
      _ = ε := by ring
  have hqlog := uniformlyOn_log_of_lowerBound hm hqconv.1 hqlower hq₀lower
  have hplog := uniformlyOn_log_of_lowerBound hm hpconv.1 hplower hp₀lower
  have hvalue := hsub hqlog hplog
  have hqderiv_cont : ContinuousOn (fun x ↦ derivWithin q₀ (Icc a b) x) (Icc a b) :=
    hq₀diff.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hpderiv_cont : ContinuousOn (fun x ↦ derivWithin p₀ (Icc a b) x) (Icc a b) :=
    hp₀diff.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hqquot := uniformlyOn_div_of_lowerBound isCompact_Icc hm hqconv.2 hqconv.1
    hqderiv_cont hqlower hq₀lower
  have hpquot := uniformlyOn_div_of_lowerBound isCompact_Icc hm hpconv.2 hpconv.1
    hpderiv_cont hplower hp₀lower
  refine ⟨?_, ?_⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hvalue ε hε
    refine ⟨N, fun n hn x hx ↦ ?_⟩
    change |Real.log (q n x / p n x) - Real.log (q₀ x / p₀ x)| < ε
    rw [Real.log_div (hqpos n x hx).ne' (hppos n x hx).ne',
      Real.log_div (hq₀pos x hx).ne' (hp₀pos x hx).ne']
    exact hN n hn x hx
  · intro ε hε
    obtain ⟨N, hN⟩ := hsub hqquot hpquot ε hε
    refine ⟨N, fun n hn x hx ↦ ?_⟩
    change |derivWithin (logRatio (q n) (p n)) (Icc a b) x -
      derivWithin (logRatio q₀ p₀) (Icc a b) x| < ε
    rw [derivWithin_logRatio hab (hqdiff n) (hpdiff n) (hqpos n) (hppos n) hx,
      derivWithin_logRatio hab (hq₀diff.differentiableOn (by norm_num))
        (hp₀diff.differentiableOn (by norm_num))
        hq₀pos hp₀pos hx]
    exact hN n hn x hx

private theorem abs_div_sub_div_lt {m B ε u u' du du' : ℝ}
    (hm : 0 < m) (hB : 0 < B) (hε : 0 < ε) (hεm : ε ≤ m / 2)
    (hu : m ≤ u) (huB : |u| ≤ B) (hduB : |du| ≤ B)
    (huclose : |u' - u| < ε) (hduclose : |du' - du| < ε) :
    |du' / u' - du / u| < (2 * B * ε) / (m ^ 2 / 2) := by
  have hupos : 0 < u := hm.trans_le hu
  have hu'pos : 0 < u' := by
    have := (neg_lt_of_abs_lt huclose)
    nlinarith
  have hden : m ^ 2 / 2 ≤ u' * u := by
    have hu'lower : m / 2 < u' := by
      have := neg_lt_of_abs_lt huclose
      nlinarith
    nlinarith [mul_pos (sub_pos.mpr hu'lower) hupos]
  have hfirst : |du' - du| * |u| < ε * B := by
    calc
      _ < ε * |u| := mul_lt_mul_of_pos_right hduclose (abs_pos.mpr hupos.ne')
      _ ≤ ε * B := mul_le_mul_of_nonneg_left huB hε.le
  have hsecond : |du| * |u - u'| < B * ε := by
    calc
      _ ≤ B * |u - u'| := mul_le_mul_of_nonneg_right hduB (abs_nonneg _)
      _ < B * ε := mul_lt_mul_of_pos_left (by simpa [abs_sub_comm] using huclose) hB
  have hnum : |(du' - du) * u + du * (u - u')| < 2 * B * ε := by
    calc
      _ ≤ |du' - du| * |u| + |du| * |u - u'| := by
        simpa only [abs_mul] using abs_add_le ((du' - du) * u) (du * (u - u'))
      _ < ε * B + B * ε := add_lt_add hfirst hsecond
      _ = 2 * B * ε := by ring
  rw [show du' / u' - du / u = ((du' - du) * u + du * (u - u')) / (u' * u) by
    field_simp [hu'pos.ne', hupos.ne'] <;> ring]
  rw [abs_div, abs_of_pos (mul_pos hu'pos hupos)]
  exact div_lt_div₀ hnum hden (by positivity) (by positivity)

/-- A [nondegenerate compact interval and positive lower and derivative margins](hyp:a,b,m,margin,hab,hm,hmargin),
[two continuously differentiable center functions](hyp:q,p,hq,hp), [their shared lower bounds](hyp:hqlower,hplower),
[a chosen orientation](hyp:sign,hsign), and [a derivative margin in that orientation](hyp:hfixed)
ensure [a positive uniform C¹ neighborhood in which both perturbed functions stay positive and
their log-ratio derivative retains that orientation](goal). -/
theorem logRatioDerivative_fixedSign_open_C1 {a b m margin : ℝ}
    (hab : a < b) (hm : 0 < m) (hmargin : 0 < margin)
    {q p : ℝ → ℝ} (hq : ContDiffOn ℝ 1 q (Icc a b))
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hqlower : ∀ x ∈ Icc a b, m ≤ q x)
    (hplower : ∀ x ∈ Icc a b, m ≤ p x)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (hfixed : ∀ x ∈ Icc a b,
      margin ≤ sign * derivWithin (logRatio q p) (Icc a b) x) :
    ∃ ε > 0, ∀ q' p' : ℝ → ℝ,
      DifferentiableOn ℝ q' (Icc a b) →
      DifferentiableOn ℝ p' (Icc a b) →
      C1CloseOn (Icc a b) ε q' q → C1CloseOn (Icc a b) ε p' p →
      (∀ x ∈ Icc a b, 0 < q' x ∧ 0 < p' x ∧
        0 < sign * derivWithin (logRatio q' p') (Icc a b) x) := by
  have hunique := uniqueDiffOn_Icc hab
  have hqderiv_cont : ContinuousOn (fun x ↦ derivWithin q (Icc a b) x) (Icc a b) :=
    hq.continuousOn_derivWithin hunique (by norm_num)
  have hpderiv_cont : ContinuousOn (fun x ↦ derivWithin p (Icc a b) x) (Icc a b) :=
    hp.continuousOn_derivWithin hunique (by norm_num)
  obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨Dq, hDq⟩ := isCompact_Icc.exists_bound_of_continuousOn hqderiv_cont
  obtain ⟨Dp, hDp⟩ := isCompact_Icc.exists_bound_of_continuousOn hpderiv_cont
  let B := |Cq| + |Cp| + |Dq| + |Dp| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hqB : ∀ x ∈ Icc a b, |q x| ≤ B := by
    intro x hx
    calc
      |q x| ≤ Cq := hCq x hx
      _ ≤ |Cq| := le_abs_self Cq
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cp, abs_nonneg Dq, abs_nonneg Dp]
  have hpB : ∀ x ∈ Icc a b, |p x| ≤ B := by
    intro x hx
    calc
      |p x| ≤ Cp := hCp x hx
      _ ≤ |Cp| := le_abs_self Cp
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Dq, abs_nonneg Dp]
  have hDqB : ∀ x ∈ Icc a b, |derivWithin q (Icc a b) x| ≤ B := by
    intro x hx
    calc
      |derivWithin q (Icc a b) x| ≤ Dq := hDq x hx
      _ ≤ |Dq| := le_abs_self Dq
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Cp, abs_nonneg Dp]
  have hDpB : ∀ x ∈ Icc a b, |derivWithin p (Icc a b) x| ≤ B := by
    intro x hx
    calc
      |derivWithin p (Icc a b) x| ≤ Dp := hDp x hx
      _ ≤ |Dp| := le_abs_self Dp
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Cp, abs_nonneg Dq]
  let L := (2 * B) / (m ^ 2 / 2)
  have hL : 0 < L := by dsimp [L]; positivity
  let ε := min (m / 2) (margin / (4 * L))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεm : ε ≤ m / 2 := min_le_left _ _
  have hεmargin : 2 * L * ε ≤ margin / 2 := by
    have hεL : ε ≤ margin / (4 * L) := min_le_right _ _
    have hL4 : 0 < 4 * L := by positivity
    calc
      2 * L * ε ≤ 2 * L * (margin / (4 * L)) := by gcongr
      _ = margin / 2 := by field_simp; ring
  refine ⟨ε, hε, ?_⟩
  intro q' p' hq'diff hp'diff hqclose hpclose x hx
  have hqpos : 0 < q x := hm.trans_le (hqlower x hx)
  have hppos : 0 < p x := hm.trans_le (hplower x hx)
  have hq'pos : 0 < q' x := by
    have hneg := neg_lt_of_abs_lt (hqclose.1 x hx)
    linarith [hqlower x hx, hεm, hm]
  have hp'pos : 0 < p' x := by
    have hneg := neg_lt_of_abs_lt (hpclose.1 x hx)
    linarith [hplower x hx, hεm, hm]
  refine ⟨hq'pos, hp'pos, ?_⟩
  have hqfrac := abs_div_sub_div_lt hm hB hε hεm (hqlower x hx) (hqB x hx)
    (hDqB x hx) (hqclose.1 x hx) (hqclose.2 x hx)
  have hpfrac := abs_div_sub_div_lt hm hB hε hεm (hplower x hx) (hpB x hx)
    (hDpB x hx) (hpclose.1 x hx) (hpclose.2 x hx)
  have hqfrac' :
      |derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x| < L * ε := by
    convert hqfrac using 1 <;> dsimp [L] <;> ring
  have hpfrac' :
      |derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x| < L * ε := by
    convert hpfrac using 1 <;> dsimp [L] <;> ring
  have hderivdiff :
      |derivWithin (logRatio q' p') (Icc a b) x -
        derivWithin (logRatio q p) (Icc a b) x| < 2 * L * ε := by
    rw [derivWithin_logRatio hab hq'diff hp'diff (fun y hy ↦ by
        have hneg := neg_lt_of_abs_lt (hqclose.1 y hy)
        nlinarith [hqlower y hy]) (fun y hy ↦ by
        have hneg := neg_lt_of_abs_lt (hpclose.1 y hy)
        nlinarith [hplower y hy]) hx,
      derivWithin_logRatio hab (hq.differentiableOn (by norm_num))
        (hp.differentiableOn (by norm_num))
        (fun y hy ↦ hm.trans_le (hqlower y hy))
        (fun y hy ↦ hm.trans_le (hplower y hy)) hx]
    calc
      |(derivWithin q' (Icc a b) x / q' x - derivWithin p' (Icc a b) x / p' x) -
          (derivWithin q (Icc a b) x / q x - derivWithin p (Icc a b) x / p x)| =
          |(derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x) -
            (derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x)| := by
            congr 1 <;> ring
      _ ≤ |derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x| +
          |derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x| := by
            simpa only [sub_eq_add_neg, Real.norm_eq_abs, norm_neg] using
              norm_add_le
                (derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x)
                (-(derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x))
      _ < L * ε + L * ε := add_lt_add hqfrac' hpfrac'
      _ = 2 * L * ε := by ring
  have hsignabs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hsignedDiff :
      |sign * derivWithin (logRatio q' p') (Icc a b) x -
        sign * derivWithin (logRatio q p) (Icc a b) x| < margin / 2 := by
    rw [← mul_sub, abs_mul, hsignabs, one_mul]
    exact hderivdiff.trans_le hεmargin
  have hlowerSigned := hfixed x hx
  have hneg := neg_lt_of_abs_lt hsignedDiff
  nlinarith

/-- The same strict fixed-sign derivative property is open under uniform `C²` perturbations,
because uniform `C²` control includes the required uniform `C¹` control. -/
theorem logRatioDerivative_fixedSign_open_C2 {a b m margin : ℝ}
    (hab : a < b) (hm : 0 < m) (hmargin : 0 < margin)
    {q p : ℝ → ℝ} (hq : ContDiffOn ℝ 1 q (Icc a b))
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hqlower : ∀ x ∈ Icc a b, m ≤ q x)
    (hplower : ∀ x ∈ Icc a b, m ≤ p x)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (hfixed : ∀ x ∈ Icc a b,
      margin ≤ sign * derivWithin (logRatio q p) (Icc a b) x) :
    ∃ ε > 0, ∀ q' p' : ℝ → ℝ,
      DifferentiableOn ℝ q' (Icc a b) →
      DifferentiableOn ℝ p' (Icc a b) →
      C2CloseOn (Icc a b) ε q' q → C2CloseOn (Icc a b) ε p' p →
      (∀ x ∈ Icc a b, 0 < q' x ∧ 0 < p' x ∧
        0 < sign * derivWithin (logRatio q' p') (Icc a b) x) := by
  obtain ⟨ε, hε, hopen⟩ := logRatioDerivative_fixedSign_open_C1 hab hm hmargin hq hp
    hqlower hplower sign hsign hfixed
  refine ⟨ε, hε, ?_⟩
  intro q' p' hq'diff hp'diff hqclose hpclose
  exact hopen q' p' hq'diff hp'diff hqclose.1 hpclose.1

end Causalean.Mathlib.Analysis
