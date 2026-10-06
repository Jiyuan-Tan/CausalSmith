module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# One-cell Poisson occupancy estimates

These observed-design lemmas isolate the light- and heavy-cell estimates for
two independent Poisson arm counts. They are the local inputs to the finite
partition Laplace argument; neither potential outcomes nor a causal model
appear in their statements.
-/

@[expose] public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The usable count of an independent Poisson arm-count pair is their sum
when both counts are positive, and zero otherwise. -/
def usablePoissonPairCount (r : ℕ × ℕ) : ℕ :=
  if 0 < r.1 ∧ 0 < r.2 then r.1 + r.2 else 0

/-- The one-cell Laplace factor averages the exponential of minus the usable
count under independent Poisson arm counts. -/
noncomputable def poissonCellLaplace (u v : ℝ≥0) : ℝ :=
  ∫ r : ℕ × ℕ, Real.exp (-(usablePoissonPairCount r : ℝ))
    ∂(poissonMeasure u).prod (poissonMeasure v)

/-- If a cell's total Poisson intensity is at most one and each arm receives
at least an `epsilon` fraction, its usable-count Laplace factor loses at least
a positive multiple of the squared total intensity. The coefficient depends
only on `epsilon`, including the zero-intensity case. -/
theorem poissonCellLaplace_light_rate (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (u v : ℝ≥0) (x : ℝ),
        (u : ℝ) + (v : ℝ) = x →
        epsilon * x ≤ (u : ℝ) → epsilon * x ≤ (v : ℝ) →
        x ≤ 1 →
        poissonCellLaplace u v ≤ Real.exp (-(c * x ^ 2)) := by
  -- The (1,1) atom has mass exp (-x) * u * v. On x ≤ 1 this is
  -- uniformly at least exp (-1) * epsilon² * x². Bound 1-y by exp (-y).
  let c : ℝ := (1 - Real.exp (-2)) * Real.exp (-1) * epsilon ^ 2
  have hc₀ : 0 ≤ 1 - Real.exp (-2 : ℝ) := by
    have : Real.exp (-2 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    linarith
  have hc : 0 < c := by
    have : Real.exp (-2 : ℝ) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro u v x hx hu hv hx₁
  let μ := (poissonMeasure u).prod (poissonMeasure v)
  let ind : ℕ × ℕ → ℝ := fun r ↦ if r = (1, 1) then 1 else 0
  have hpoint (r : ℕ × ℕ) :
      Real.exp (-(usablePoissonPairCount r : ℝ)) ≤
        1 - (1 - Real.exp (-2)) * ind r := by
    by_cases hr : r = (1, 1)
    · subst r
      norm_num [usablePoissonPairCount, ind]
    · simp only [ind, if_neg hr, mul_zero, sub_zero]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hfun : Integrable (fun r : ℕ × ℕ ↦
      Real.exp (-(usablePoissonPairCount r : ℝ))) μ := by
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hind : Integrable ind μ := by
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards with r
    dsimp [ind]
    split <;> simp
  have hmono : poissonCellLaplace u v ≤
      1 - (1 - Real.exp (-2)) * (∫ r, ind r ∂μ) := by
    have henv : Integrable (fun r : ℕ × ℕ ↦
        1 - (1 - Real.exp (-2)) * ind r) μ :=
      (integrable_const (1 : ℝ)).sub (hind.const_mul _)
    have hle := integral_mono_ae hfun henv (Filter.Eventually.of_forall hpoint)
    unfold poissonCellLaplace
    calc
      _ ≤ ∫ r, (1 - (1 - Real.exp (-2)) * ind r) ∂μ := hle
      _ = 1 - (1 - Real.exp (-2)) * (∫ r, ind r ∂μ) := by
        rw [integral_sub (integrable_const (1 : ℝ)) (hind.const_mul _)]
        rw [integral_const_mul]
        simp
  have hOne (a : ℝ≥0) :
      (∫ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ∂poissonMeasure a) =
        Real.exp (-(a : ℝ)) * a := by
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [tsum_eq_single 1]
    · norm_num
    · intro n hn
      simp [hn]
  have hatom : (∫ r, ind r ∂μ) =
      Real.exp (-x) * (u : ℝ) * (v : ℝ) := by
    calc
      (∫ r, ind r ∂μ) =
          (∫ r : ℕ × ℕ, (if r.1 = 1 then (1 : ℝ) else 0) *
            (if r.2 = 1 then (1 : ℝ) else 0) ∂μ) := by
              congr with r
              rcases r with ⟨m, n⟩
              simp only [ind, Prod.mk.injEq]
              by_cases hm : m = 1 <;> by_cases hn : n = 1 <;> simp [hm, hn]
      _ = (∫ m : ℕ, (if m = 1 then (1 : ℝ) else 0) ∂poissonMeasure u) *
          (∫ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ∂poissonMeasure v) := by
            simpa only [μ] using (integral_prod_mul
              (μ := poissonMeasure u) (ν := poissonMeasure v) (L := ℝ)
              (fun m : ℕ ↦ if m = 1 then (1 : ℝ) else 0)
              (fun n : ℕ ↦ if n = 1 then (1 : ℝ) else 0))
      _ = _ := by
        rw [hOne, hOne]
        have he : Real.exp (-(u : ℝ)) * Real.exp (-(v : ℝ)) =
            Real.exp (-x) := by
          rw [← Real.exp_add]
          congr 1
          linarith
        calc
          Real.exp (-(u : ℝ)) * (u : ℝ) *
              (Real.exp (-(v : ℝ)) * (v : ℝ)) =
              (Real.exp (-(u : ℝ)) * Real.exp (-(v : ℝ))) *
                (u : ℝ) * (v : ℝ) := by ring
          _ = _ := by rw [he]
  have hx₀ : 0 ≤ x := by rw [← hx]; positivity
  have hprod : epsilon ^ 2 * x ^ 2 ≤ (u : ℝ) * (v : ℝ) := by
    have h := mul_le_mul hu hv (mul_nonneg hepsilon.le hx₀) (by positivity)
    nlinarith
  have hexp : Real.exp (-1) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcore : c * x ^ 2 ≤
      (1 - Real.exp (-2)) * (Real.exp (-x) * (u : ℝ) * (v : ℝ)) := by
    dsimp [c]
    have h := mul_le_mul hexp hprod (by positivity) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left h hc₀]
  calc
    poissonCellLaplace u v ≤
        1 - (1 - Real.exp (-2)) * (Real.exp (-x) * (u : ℝ) * (v : ℝ)) := by
          simpa only [hatom] using hmono
    _ ≤ 1 - c * x ^ 2 := by linarith
    _ ≤ Real.exp (-(c * x ^ 2)) := Real.one_sub_le_exp_neg _

/-- Given [an overlap margin below one half](hyp:epsilon,hepsilon,hepsilon_half)
and [two arm intensities with their total intensity](hyp:u,v,x), [the one-cell
usable-count Laplace factor decays at a positive exponential rate](goal). -/
theorem poissonCellLaplace_heavy_rate (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (u v : ℝ≥0) (x : ℝ),
        (u : ℝ) + (v : ℝ) = x →
        epsilon * x ≤ (u : ℝ) → epsilon * x ≤ (v : ℝ) →
        1 ≤ x →
        poissonCellLaplace u v ≤ Real.exp (-(c * x)) := by
  -- For bounded x, the (1,1) atom gives a uniform strict gap below one.
  -- For sufficiently large x, split by whether both arms occur: the matched
  -- contribution is bounded by exp (-(1-exp (-1))*x), while either missing
  -- arm costs exp (-u) or exp (-v). Absorb the factor three beyond a fixed
  -- epsilon-dependent threshold and choose the smaller exponent constant.
  let T : ℝ := 4 / epsilon
  let a : ℝ := (1 - Real.exp (-2)) * Real.exp (-T) * epsilon ^ 2
  let c : ℝ := min a (epsilon / 2)
  have hgap : 0 < 1 - Real.exp (-2 : ℝ) := by
    have : Real.exp (-2 : ℝ) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := lt_min ha (by positivity)
  refine ⟨c, hc, ?_⟩
  intro u v x hx hu hv hx₁
  have hx₀ : 0 ≤ x := le_trans (by norm_num) hx₁
  have hprod : epsilon ^ 2 * x ^ 2 ≤ (u : ℝ) * (v : ℝ) := by
    have h := mul_le_mul hu hv (mul_nonneg hepsilon.le hx₀) (by positivity)
    nlinarith
  by_cases hbounded : x ≤ T
  · let μ := (poissonMeasure u).prod (poissonMeasure v)
    let ind : ℕ × ℕ → ℝ := fun r ↦ if r = (1, 1) then 1 else 0
    have hpoint (r : ℕ × ℕ) :
        Real.exp (-(usablePoissonPairCount r : ℝ)) ≤
          1 - (1 - Real.exp (-2)) * ind r := by
      by_cases hr : r = (1, 1)
      · subst r
        norm_num [usablePoissonPairCount, ind]
      · simp only [ind, if_neg hr, mul_zero, sub_zero]
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (Nat.cast_nonneg _)
    have hfun : Integrable (fun r : ℕ × ℕ ↦
        Real.exp (-(usablePoissonPairCount r : ℝ))) μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    have hind : Integrable ind μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      dsimp [ind]
      split <;> simp
    have hmono : poissonCellLaplace u v ≤
        1 - (1 - Real.exp (-2)) * (∫ r, ind r ∂μ) := by
      have henv : Integrable (fun r : ℕ × ℕ ↦
          1 - (1 - Real.exp (-2)) * ind r) μ :=
        (integrable_const (1 : ℝ)).sub (hind.const_mul _)
      have hle := integral_mono_ae hfun henv (Filter.Eventually.of_forall hpoint)
      unfold poissonCellLaplace
      calc
        _ ≤ ∫ r, (1 - (1 - Real.exp (-2)) * ind r) ∂μ := hle
        _ = 1 - (1 - Real.exp (-2)) * (∫ r, ind r ∂μ) := by
          rw [integral_sub (integrable_const (1 : ℝ)) (hind.const_mul _)]
          rw [integral_const_mul]
          simp
    have hOne (r : ℝ≥0) :
        (∫ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ∂poissonMeasure r) =
          Real.exp (-(r : ℝ)) * r := by
      rw [integral_poissonMeasure]
      simp only [smul_eq_mul]
      rw [tsum_eq_single 1]
      · norm_num
      · intro n hn
        simp [hn]
    have hatom : (∫ r, ind r ∂μ) =
        Real.exp (-x) * (u : ℝ) * (v : ℝ) := by
      calc
        (∫ r, ind r ∂μ) =
            (∫ r : ℕ × ℕ, (if r.1 = 1 then (1 : ℝ) else 0) *
              (if r.2 = 1 then (1 : ℝ) else 0) ∂μ) := by
                congr with r
                rcases r with ⟨m, n⟩
                simp only [ind, Prod.mk.injEq]
                by_cases hm : m = 1 <;> by_cases hn : n = 1 <;> simp [hm, hn]
        _ = (∫ m : ℕ, (if m = 1 then (1 : ℝ) else 0) ∂poissonMeasure u) *
            (∫ n : ℕ, (if n = 1 then (1 : ℝ) else 0) ∂poissonMeasure v) := by
              simpa only [μ] using (integral_prod_mul
                (μ := poissonMeasure u) (ν := poissonMeasure v) (L := ℝ)
                (fun m : ℕ ↦ if m = 1 then (1 : ℝ) else 0)
                (fun n : ℕ ↦ if n = 1 then (1 : ℝ) else 0))
        _ = _ := by
          rw [hOne, hOne]
          have he : Real.exp (-(u : ℝ)) * Real.exp (-(v : ℝ)) =
              Real.exp (-x) := by
            rw [← Real.exp_add]
            congr 1
            linarith
          calc
            Real.exp (-(u : ℝ)) * (u : ℝ) *
                (Real.exp (-(v : ℝ)) * (v : ℝ)) =
                (Real.exp (-(u : ℝ)) * Real.exp (-(v : ℝ))) *
                  (u : ℝ) * (v : ℝ) := by ring
            _ = _ := by rw [he]
    have hexp : Real.exp (-T) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (neg_le_neg hbounded)
    have hcore : a * x ≤
        (1 - Real.exp (-2)) * (Real.exp (-x) * (u : ℝ) * (v : ℝ)) := by
      have hx2 : x ≤ x ^ 2 := by nlinarith
      have h := mul_le_mul hexp hprod (by positivity) (Real.exp_pos _).le
      have hh := mul_le_mul_of_nonneg_left h hgap.le
      have hxa : a * x ≤ a * x ^ 2 := mul_le_mul_of_nonneg_left hx2 ha.le
      dsimp [a] at hxa ⊢
      nlinarith
    have hca : c ≤ a := min_le_left _ _
    calc
      poissonCellLaplace u v ≤
          1 - (1 - Real.exp (-2)) *
            (Real.exp (-x) * (u : ℝ) * (v : ℝ)) := by
            simpa only [hatom] using hmono
      _ ≤ 1 - c * x := by nlinarith [mul_le_mul_of_nonneg_right hca hx₀]
      _ ≤ Real.exp (-(c * x)) := Real.one_sub_le_exp_neg _
  · have hlarge : T < x := lt_of_not_ge hbounded
    have hpgf (r : ℝ≥0) :
        (∫ n : ℕ, Real.exp (-(n : ℝ)) ∂poissonMeasure r) =
          Real.exp (-(1 - Real.exp (-1)) * (r : ℝ)) := by
      rw [integral_poissonMeasure]
      simp only [smul_eq_mul]
      calc
        ∑' n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / Nat.factorial n *
              Real.exp (-(n : ℝ)) =
            Real.exp (-(r : ℝ)) *
              ∑' n : ℕ, (((r : ℝ) * Real.exp (-1)) ^ n / Nat.factorial n) := by
                rw [← tsum_mul_left]
                apply tsum_congr
                intro n
                rw [show -(n : ℝ) = (n : ℝ) * (-1) by ring, Real.exp_nat_mul]
                ring
        _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp (-1)) := by
          have hs := (NormedSpace.expSeries_div_hasSum_exp
            ((r : ℝ) * Real.exp (-1))).tsum_eq
          rw [← Real.exp_eq_exp_ℝ] at hs
          rw [hs]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hzero (r : ℝ≥0) :
        (∫ n : ℕ, (if n = 0 then (1 : ℝ) else 0) ∂poissonMeasure r) =
          Real.exp (-(r : ℝ)) := by
      rw [integral_poissonMeasure]
      simp only [smul_eq_mul]
      rw [tsum_eq_single 0]
      · norm_num
      · intro n hn
        simp [hn]
    let μ := (poissonMeasure u).prod (poissonMeasure v)
    let F : ℕ × ℕ → ℝ := fun r ↦ Real.exp (-((r.1 : ℝ) + r.2))
    let Z₀ : ℕ × ℕ → ℝ := fun r ↦ if r.1 = 0 then 1 else 0
    let Z₁ : ℕ × ℕ → ℝ := fun r ↦ if r.2 = 0 then 1 else 0
    have hpoint (r : ℕ × ℕ) :
        Real.exp (-(usablePoissonPairCount r : ℝ)) ≤ F r + Z₀ r + Z₁ r := by
      rcases r with ⟨m, n⟩
      by_cases hm : m = 0
      · subst m
        simp only [usablePoissonPairCount, lt_self_iff_false, false_and, ↓reduceIte,
          Nat.cast_zero, neg_zero, Real.exp_zero, F, Z₀, Z₁]
        have he : 0 ≤ Real.exp (-((0 : ℝ) + n)) := (Real.exp_pos _).le
        split <;> linarith
      by_cases hn : n = 0
      · subst n
        simp only [usablePoissonPairCount, lt_self_iff_false, and_false, ↓reduceIte,
          Nat.cast_zero, add_zero, neg_zero, Real.exp_zero, F, Z₀, Z₁, hm]
        have he : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
        linarith
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [usablePoissonPairCount, F, Z₀, Z₁, hm, hn, hmpos, hnpos]
    have hfun : Integrable (fun r : ℕ × ℕ ↦
        Real.exp (-(usablePoissonPairCount r : ℝ))) μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    have hF : Integrable F μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hZ₀ : Integrable Z₀ μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      dsimp [Z₀]
      split <;> simp
    have hZ₁ : Integrable Z₁ μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with r
      dsimp [Z₁]
      split <;> simp
    have hFint : (∫ r, F r ∂μ) =
        Real.exp (-(1 - Real.exp (-1)) * x) := by
      calc
        (∫ r, F r ∂μ) =
            (∫ r : ℕ × ℕ, Real.exp (-(r.1 : ℝ)) *
              Real.exp (-(r.2 : ℝ)) ∂μ) := by
                congr with r
                dsimp [F]
                rw [← Real.exp_add]
                congr 1
                ring
        _ = (∫ m : ℕ, Real.exp (-(m : ℝ)) ∂poissonMeasure u) *
            (∫ n : ℕ, Real.exp (-(n : ℝ)) ∂poissonMeasure v) := by
              simpa only [μ] using (integral_prod_mul
                (μ := poissonMeasure u) (ν := poissonMeasure v) (L := ℝ)
                (fun m : ℕ ↦ Real.exp (-(m : ℝ)))
                (fun n : ℕ ↦ Real.exp (-(n : ℝ))))
        _ = _ := by
          rw [hpgf, hpgf, ← Real.exp_add]
          congr 1
          rw [← hx]
          ring
    have hZ₀int : (∫ r, Z₀ r ∂μ) = Real.exp (-(u : ℝ)) := by
      calc
        _ = (∫ m : ℕ, (if m = 0 then (1 : ℝ) else 0) ∂poissonMeasure u) *
            (∫ _n : ℕ, (1 : ℝ) ∂poissonMeasure v) := by
              simpa only [μ, Z₀, mul_one] using (integral_prod_mul
                (μ := poissonMeasure u) (ν := poissonMeasure v) (L := ℝ)
                (fun m : ℕ ↦ if m = 0 then (1 : ℝ) else 0)
                (fun _n : ℕ ↦ (1 : ℝ)))
        _ = _ := by rw [hzero]; simp
    have hZ₁int : (∫ r, Z₁ r ∂μ) = Real.exp (-(v : ℝ)) := by
      calc
        _ = (∫ _m : ℕ, (1 : ℝ) ∂poissonMeasure u) *
            (∫ n : ℕ, (if n = 0 then (1 : ℝ) else 0) ∂poissonMeasure v) := by
              simpa only [μ, Z₁, one_mul] using (integral_prod_mul
                (μ := poissonMeasure u) (ν := poissonMeasure v) (L := ℝ)
                (fun _m : ℕ ↦ (1 : ℝ))
                (fun n : ℕ ↦ if n = 0 then (1 : ℝ) else 0))
        _ = _ := by rw [hzero]; simp
    have henv : Integrable (fun r ↦ F r + Z₀ r + Z₁ r) μ :=
      (hF.add hZ₀).add hZ₁
    have hbound : poissonCellLaplace u v ≤
        Real.exp (-(1 - Real.exp (-1)) * x) +
          Real.exp (-(u : ℝ)) + Real.exp (-(v : ℝ)) := by
      have hle := integral_mono_ae hfun henv (Filter.Eventually.of_forall hpoint)
      unfold poissonCellLaplace
      calc
        _ ≤ ∫ r, (F r + Z₀ r + Z₁ r) ∂μ := hle
        _ = _ := by
          have hadd₀ : (∫ r, F r + Z₀ r ∂μ) =
              (∫ r, F r ∂μ) + (∫ r, Z₀ r ∂μ) := by
            simpa only [Pi.add_apply] using integral_add hF hZ₀
          have hadd₁ : (∫ r, F r + Z₀ r + Z₁ r ∂μ) =
              (∫ r, F r + Z₀ r ∂μ) + (∫ r, Z₁ r ∂μ) := by
            simpa only [Pi.add_apply] using integral_add (hF.add hZ₀) hZ₁
          rw [hadd₁, hadd₀, hFint, hZ₀int, hZ₁int]
    have hnegone : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      have hmul : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
        rw [Real.exp_neg]
        exact inv_mul_cancel₀ (Real.exp_ne_zero _)
      nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos (-1 : ℝ)]
    have heps : epsilon ≤ 1 - Real.exp (-1) := by linarith
    have hfirst : Real.exp (-(1 - Real.exp (-1)) * x) ≤
        Real.exp (-epsilon * x) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right heps hx₀
      linarith
    have hzero₀ : Real.exp (-(u : ℝ)) ≤ Real.exp (-epsilon * x) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hu)
    have hzero₁ : Real.exp (-(v : ℝ)) ≤ Real.exp (-epsilon * x) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hv)
    have hthree : (3 : ℝ) ≤ Real.exp (epsilon * x / 2) := by
      have hepsx : 4 < epsilon * x := by
        have := (div_lt_iff₀ hepsilon).mp hlarge
        simpa only [T, mul_comm] using this
      have htwo : (3 : ℝ) < Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos (1 : ℝ)]
      exact htwo.le.trans (Real.exp_le_exp.mpr (by linarith))
    have hceps : c ≤ epsilon / 2 := min_le_right _ _
    calc
      poissonCellLaplace u v ≤
          Real.exp (-(1 - Real.exp (-1)) * x) +
            Real.exp (-(u : ℝ)) + Real.exp (-(v : ℝ)) := hbound
      _ ≤ 3 * Real.exp (-epsilon * x) := by linarith
      _ ≤ Real.exp (epsilon * x / 2) * Real.exp (-epsilon * x) :=
        mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
      _ = Real.exp (-(epsilon / 2 * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(c * x)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hceps hx₀])

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
