/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample quantile (generalized inverse of the empirical cdf)

Causal-agnostic statistical primitive: the `τ`-**sample quantile** of an i.i.d.
real sample, defined as the (lower) generalized inverse of the empirical cdf

    q̂ₙ(τ) := quantile (νₙ) τ,     νₙ := (1/n) Σ_{i<n} δ_{Zᵢ},

where `νₙ` is the **empirical measure** and `quantile` is the CDF inverse from
`Stat/Quantile/Quantile.lean`. Because `cdf νₙ = F̂ₙ` (the `empiricalCDF` from
`Stat/Quantile/EmpiricalCDF.lean`), the sample quantile inherits the Galois connection

    q̂ₙ(τ) ≤ x  ↔  τ ≤ F̂ₙ(x)        (switching relation, `0 < τ < 1`).

This file supplies the empirical measure, the cdf bridge, the switching
relation, monotonicity of `F̂ₙ` in `y`, and the **atom bound**

    |F̂ₙ(q̂ₙ) − τ| ≤ 1/n        a.s. (under an atomless population),

which are the deterministic / structural facts feeding the Bahadur
derivation in `Stat/Quantile/SampleQuantileBahadur.lean`.

Project-agnostic; upstream-candidate.
-/

module
public import Causalean.Stat.Quantile.EmpiricalCDF
public import Causalean.Stat.Quantile.Quantile

/-! # Empirical Measures and Sample Quantiles

This file builds the sample quantile from the empirical measure of an i.i.d.
real sample. The central definitions are `IIDSample.empiricalMeasure`, the
finite empirical probability measure, and `IIDSample.sampleQuantile`, the
generalized inverse of that measure's cdf.

The main structural results are the cdf bridge
`IIDSample.empiricalMeasure_cdf`, the switching relation
`IIDSample.sampleQuantile_le_iff`, monotonicity of `IIDSample.empiricalCDF` in
its real argument, and the atom bound `IIDSample.sampleQuantile_atom_bound`.
Together these deterministic facts feed the derived Bahadur representation for
the ordinary empirical sample quantile.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-! ## Empirical measure -/

/-- For [an independent and identically distributed real-valued sample](hyp:S), [a
nonnegative integer sample size](hyp:n), and [a sample-space outcome](hyp:ω), [the empirical
measure](goal) is the sum of point masses at the first $n$ observed values, multiplied by the
reciprocal of $n$; at sample size zero it is the zero measure. -/
noncomputable def IIDSample.empiricalMeasure (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) :
    Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (S.Z i ω)

/-- For `0 < n` the empirical measure is a probability measure. -/
lemma IIDSample.empiricalMeasure_isProbabilityMeasure (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    IsProbabilityMeasure (S.empiricalMeasure n ω) := by
  constructor
  unfold IIDSample.empiricalMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp only [MeasureTheory.measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hn.ne'
  · exact ENNReal.natCast_ne_top n

/-- The empirical measure and empirical CDF agree on lower rays: for [an i.i.d.
real sample](hyp:S), [a positive sample size](hyp:_hn), [an outcome](hyp:ω),
and [a real threshold](hyp:y), [the empirical mass of observations at or below
the threshold equals the empirical CDF there](goal).

The identity is total at sample size zero as well; the positivity premise is
retained by this interface. -/
lemma IIDSample.empiricalMeasure_real_Iic (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (_hn : 0 < n) (ω : Ω) (y : ℝ) :
    (S.empiricalMeasure n ω).real (Set.Iic y) = S.empiricalCDF y n ω := by
  unfold IIDSample.empiricalMeasure IIDSample.empiricalCDF IIDSample.sampleMean
  rw [Measure.real, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  simp only [Measure.dirac_apply' _ measurableSet_Iic]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  rw [ENNReal.toReal_sum (fun i _ => by
    by_cases h : S.Z i ω ∈ Set.Iic y <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])]
  apply Finset.sum_congr rfl
  intro i _
  unfold cdfStat
  by_cases h : S.Z i ω ∈ Set.Iic y
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, ENNReal.toReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.toReal_zero]

/-- **cdf bridge.** For [a positive sample size $n$](hyp:hn), the cumulative distribution function
of the empirical measure `S.empiricalMeasure n ω` built from an i.i.d. sample at outcome `ω`
[coincides pointwise, at every threshold `y`, with the empirical cdf `S.empiricalCDF y n
ω`](goal). -/
lemma IIDSample.empiricalMeasure_cdf (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) (y : ℝ) :
    cdf (S.empiricalMeasure n ω) y = S.empiricalCDF y n ω := by
  haveI := S.empiricalMeasure_isProbabilityMeasure hn ω
  rw [cdf_eq_real, S.empiricalMeasure_real_Iic hn ω y]

/-! ## Sample quantile -/

/-- For [an independent and identically distributed real-valued sample](hyp:S) and [a real
quantile level](hyp:τ), [the sample quantile](goal) maps each nonnegative integer sample size
and sample-space outcome to the lower generalized inverse, at that level, of the empirical
cumulative distribution function.

The **sample `τ`-quantile** `q̂ₙ(τ) = quantile νₙ τ`, the generalized inverse
of the empirical cdf. -/
noncomputable def IIDSample.sampleQuantile (S : IIDSample Ω ℝ μ P) (τ : ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => quantile (S.empiricalMeasure n ω) τ

/-- **Switching relation.** For [a positive sample size $n$](hyp:hn) and [an interior quantile
level $\tau\in(0,1)$](hyp:hτ0,hτ1), [the sample $\tau$-quantile $\hat q_n(\tau)$ is at most a given
point `x` exactly when $\tau$ is at most the empirical cdf at `x`](goal). -/
lemma IIDSample.sampleQuantile_le_iff (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) (ω : Ω) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (x : ℝ) :
    S.sampleQuantile τ n ω ≤ x ↔ τ ≤ S.empiricalCDF x n ω := by
  haveI := S.empiricalMeasure_isProbabilityMeasure hn ω
  rw [IIDSample.sampleQuantile, quantile_le_iff hτ0 hτ1, S.empiricalMeasure_cdf hn ω]

/-- **Measurability of the sample quantile.** For [a positive sample size](hyp:hn) and
[an interior quantile level](hyp:hτ0,hτ1), [the sample quantile is measurable](goal). -/
@[fun_prop]
lemma IIDSample.measurable_sampleQuantile (S : IIDSample Ω ℝ μ P)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Measurable (S.sampleQuantile τ n) := by
  apply measurable_of_Iic
  intro x
  have hpre : S.sampleQuantile τ n ⁻¹' Set.Iic x = {ω | τ ≤ S.empiricalCDF x n ω} := by
    ext ω
    exact S.sampleQuantile_le_iff hn ω hτ0 hτ1 x
  rw [hpre]
  exact measurableSet_le measurable_const (S.measurable_sampleMean (measurable_cdfStat x) n)

/-! ## Monotonicity of the empirical cdf in the argument -/

/-- The empirical cdf is monotone in its real argument `y` (a sum of monotone
lower-ray indicators). -/
lemma IIDSample.empiricalCDF_monotone (S : IIDSample Ω ℝ μ P) (n : ℕ) (ω : Ω) :
    Monotone (fun y => S.empiricalCDF y n ω) := by
  intro y y' hyy'
  unfold IIDSample.empiricalCDF IIDSample.sampleMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  unfold cdfStat
  by_cases h : S.Z i ω ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h),
      Set.indicator_of_mem (Set.mem_Iic.mpr (h.trans hyy'))]
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic]; exact h)]
    exact cdfStat_nonneg y' _

/-! ## Atom bound (locally tie-free near the population quantile) -/

/-- **Local atom bound.** If [the radius around the target quantile is positive](hyp:hρ),
[the population cdf is continuous on the corresponding closed neighborhood](hyp:hcont),
[the sample size is positive](hyp:hn), and [the quantile level is interior](hyp:hτ0,hτ1), then
[almost surely, whenever the sample quantile lies in the open neighborhood, its empirical-cdf
overshoot is at most one observation](goal).

Local continuity makes population singletons null inside the neighborhood, which is enough to
exclude ties whenever the sample quantile lies there. -/
lemma IIDSample.sampleQuantile_atom_bound [IsProbabilityMeasure μ] (S : IIDSample Ω ℝ μ P)
    {q₀ ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun y => cdf P y) (Set.Icc (q₀ - ρ) (q₀ + ρ)))
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∀ᵐ ω ∂μ, S.sampleQuantile τ n ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ) →
      |S.empiricalCDF (S.sampleQuantile τ n ω) n ω - τ| ≤ (n : ℝ)⁻¹ := by
  -- Local continuity of the cdf makes each singleton in the open neighborhood null.
  haveI hP : IsProbabilityMeasure P := by
    rw [← S.law]
    exact MeasureTheory.Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hsingleton : ∀ x ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ), P {x} = 0 := by
    intro x hx
    have hxnhds : Set.Icc (q₀ - ρ) (q₀ + ρ) ∈ nhds x := by simpa using hx
    have hcx : ContinuousAt (fun y => cdf P y) x := hcont.continuousAt hxnhds
    have heq : P = (cdf P).measure := (measure_cdf P).symm
    rw [heq, StieltjesFunction.measure_singleton,
      ContinuousWithinAt.leftLim_eq hcx.continuousWithinAt, sub_self, ENNReal.ofReal_zero]
  -- Each coordinate has law `P`.
  have hlaw : ∀ i : ℕ, μ.map (S.Z i) = P := fun i => (S.identDist i).map_eq.symm.trans S.law
  -- Pairwise local distinctness follows from independence and the local singleton nullity.
  have hpair : ∀ i j : ℕ, i ≠ j →
      μ {ω | S.Z i ω = S.Z j ω ∧
        S.Z i ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)} = 0 := by
    intro i j hij
    have hind : IndepFun (S.Z i) (S.Z j) μ := S.indep.indepFun hij
    let A : Set (ℝ × ℝ) :=
      {p | p.1 = p.2 ∧ p.1 ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)}
    have hmeas : MeasurableSet A :=
      (measurableSet_eq_fun measurable_fst measurable_snd).inter
        (measurableSet_Ioo.preimage measurable_fst)
    have hpre : {ω | S.Z i ω = S.Z j ω ∧
        S.Z i ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)} =
        (fun ω => (S.Z i ω, S.Z j ω)) ⁻¹' A := rfl
    rw [hpre, ← Measure.map_apply ((S.meas i).prodMk (S.meas j)) hmeas,
      (indepFun_iff_map_prod_eq_prod_map_map
        (S.meas i).aemeasurable (S.meas j).aemeasurable).mp hind,
      hlaw i, hlaw j, Measure.measure_prod_null hmeas]
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)
    · have hsing : Prod.mk x ⁻¹' A = {x} := by
        ext y
        simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, hx⟩⟩
      change P (Prod.mk x ⁻¹' A) = 0
      rw [hsing, hsingleton x hx]
    · have hempty : Prod.mk x ⁻¹' A = ∅ := by
        ext y
        simp only [A, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.2
      change P (Prod.mk x ⁻¹' A) = 0
      rw [hempty, measure_empty]
  -- Assemble into one a.s. event with no ties whose common value is local.
  have hae : ∀ᵐ ω ∂μ, ∀ i ∈ (Finset.range n : Set ℕ),
      ∀ j ∈ (Finset.range n : Set ℕ), i ≠ j →
        ¬ (S.Z i ω = S.Z j ω ∧
          S.Z i ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)) := by
    rw [ae_ball_iff (Set.to_countable _)]
    intro i _
    rw [ae_ball_iff (Set.to_countable _)]
    intro j _
    by_cases hij : i = j
    · exact ae_of_all _ (fun ω hne => absurd hij hne)
    · rw [ae_iff]
      have heqset : {ω | ¬ (i ≠ j →
          ¬ (S.Z i ω = S.Z j ω ∧
            S.Z i ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)))} =
          {ω | S.Z i ω = S.Z j ω ∧
            S.Z i ω ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ)} := by
        ext ω; simp [hij]
      rw [heqset, hpair i j hij]
  -- The empirical-cdf sum counts the sample points below the threshold.
  have hcard : ∀ (x : ℝ) (ω : Ω), ∑ i ∈ Finset.range n, cdfStat x (S.Z i ω)
      = (((Finset.range n).filter (fun i => S.Z i ω ≤ x)).card : ℝ) := by
    intro x ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold cdfStat
    by_cases h : S.Z i ω ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h)]; simp [h]
    · rw [Set.indicator_of_notMem (by simpa using h)]; simp [h]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  filter_upwards [hae] with ω haeω
  intro hq_local
  set q := S.sampleQuantile τ n ω with hq
  -- LOWER bound `τ ≤ F̂ₙ(q)` is deterministic (switching at `x = q`, reflexivity).
  have hlower : τ ≤ S.empiricalCDF q n ω :=
    (S.sampleQuantile_le_iff hn ω hτ0 hτ1 q).mp (le_refl q)
  -- Strict switching: any `x < q` has `F̂ₙ(x) < τ`.
  have hstrict : ∀ x : ℝ, x < q → S.empiricalCDF x n ω < τ := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    exact absurd ((S.sampleQuantile_le_iff hn ω hτ0 hτ1 x).mpr hcon) (not_le.mpr hx)
  -- Abbreviations for the three counts.
  set Cle : ℝ → Finset ℕ :=
    fun x => (Finset.range n).filter (fun i => S.Z i ω ≤ x) with hCle
  set Clt : Finset ℕ := (Finset.range n).filter (fun i => S.Z i ω < q) with hClt
  set Ceq : Finset ℕ := (Finset.range n).filter (fun i => S.Z i ω = q) with hCeq
  -- `F̂ₙ(x) = (Cle x).card / n`.
  have hFcard : ∀ x : ℝ, S.empiricalCDF x n ω = (n : ℝ)⁻¹ * ((Cle x).card : ℝ) := by
    intro x
    rw [IIDSample.empiricalCDF, IIDSample.sampleMean, hcard x ω]
  -- `Cle q = Clt ∪ Ceq`, disjointly: `Zᵢ ≤ q ↔ Zᵢ < q ∨ Zᵢ = q`.
  have hdisj : Disjoint Clt Ceq := by
    rw [hClt, hCeq, Finset.disjoint_filter]
    intro i _ hlt heq; exact absurd heq (ne_of_lt hlt)
  have hunion : Cle q = Clt ∪ Ceq := by
    rw [hCle, hClt, hCeq, ← Finset.filter_or]
    refine Finset.filter_congr (fun i _ => ?_)
    exact ⟨fun h => h.lt_or_eq, fun h => h.elim le_of_lt le_of_eq⟩
  have hcountsplit : (Cle q).card = Clt.card + Ceq.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- Tie-free ⇒ at most one index equals `q`.
  have hCeq_le : Ceq.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hCeq, Finset.mem_filter] at ha hb
    by_contra hab
    have hqlocalq : q ∈ Set.Ioo (q₀ - ρ) (q₀ + ρ) := by simpa [hq] using hq_local
    exact haeω a (by simpa using ha.1) b (by simpa using hb.1) hab
      ⟨ha.2.trans hb.2.symm, by rw [ha.2]; exact hqlocalq⟩
  -- Strict part: `(Clt.card : ℝ) ≤ n·τ`, via a threshold `x < q` with `Cle x = Clt`.
  have hClt_le : (Clt.card : ℝ) ≤ (n : ℝ) * τ := by
    rcases Finset.eq_empty_or_nonempty Clt with hempty | hne
    · rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
    · -- `m = max{Zᵢ : Zᵢ < q}`; choose threshold `x = m < q`, then `Cle m = Clt`.
      set T : Finset ℝ := Clt.image (fun i => S.Z i ω) with hT
      have hTne : T.Nonempty := hne.image _
      set m : ℝ := T.max' hTne with hm
      have hmlt : m < q := by
        obtain ⟨a, haT, ham⟩ := Finset.mem_image.mp (T.max'_mem hTne)
        rw [hClt, Finset.mem_filter] at haT
        rw [hm, ← ham]; exact haT.2
      have hCleq : Cle m = Clt := by
        rw [hCle, hClt]
        refine Finset.filter_congr (fun i hi => ?_)
        constructor
        · intro hle; exact lt_of_le_of_lt hle hmlt
        · intro hlt
          refine Finset.le_max' T _ ?_
          rw [hT]
          exact Finset.mem_image.mpr
            ⟨i, by rw [hClt, Finset.mem_filter]; exact ⟨hi, hlt⟩, rfl⟩
      have hlt2 : S.empiricalCDF m n ω < τ := hstrict m hmlt
      rw [hFcard m, hCleq] at hlt2
      -- `(n)⁻¹ * card < τ`  ⟹  `card < n·τ`.
      have hkey := (inv_mul_lt_iff₀ hnR).mp hlt2
      linarith [hkey]
  -- Combine: `n·F̂ₙ(q) = (Cle q).card ≤ n·τ + 1`, so `F̂ₙ(q) ≤ τ + 1/n`.
  have hupper : S.empiricalCDF q n ω ≤ τ + (n : ℝ)⁻¹ := by
    rw [hFcard q, hcountsplit]
    push_cast
    rw [mul_add]
    have h1 : (n : ℝ)⁻¹ * (Clt.card : ℝ) ≤ τ := by
      rw [inv_mul_le_iff₀ hnR]; linarith [hClt_le]
    have h2 : (n : ℝ)⁻¹ * (Ceq.card : ℝ) ≤ (n : ℝ)⁻¹ := by
      have : (Ceq.card : ℝ) ≤ 1 := by exact_mod_cast hCeq_le
      nlinarith [inv_nonneg.mpr hnR.le, this]
    linarith
  rw [abs_le]
  exact ⟨by linarith [inv_nonneg.mpr hnR.le], by linarith⟩

end Causalean.Stat
