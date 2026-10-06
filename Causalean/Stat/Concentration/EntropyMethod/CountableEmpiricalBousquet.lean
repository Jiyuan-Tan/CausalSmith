module
public import Causalean.Stat.Concentration.EntropyMethod.FiniteEmpiricalBousquet
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bousquet's inequality for countable empirical classes

This file passes the finite empirical-supremum inequality to a countable class through an
increasing sequence of finite prefixes.  The full supremum is never equipped with a maximizing
index: a countable supremum need not be attained.  Bounded dominated convergence supplies the
expectation limit, while strict upper-tail events are the increasing union of their finite-prefix
counterparts.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Causalean.Stat.Concentration.EntropyMethod

universe u v

/-- For [a nonempty countable type `I`](hyp:I), the [canonical countable-class
enumeration](goal) is a chosen surjection from the natural numbers onto `I`. -/
noncomputable def countableClassEnumeration (I : Type v) [Nonempty I] [Countable I] : ℕ → I :=
  Classical.choose (exists_surjective_nat I)

/-- The [canonical enumeration of a nonempty countable type](hyp:I) [visits every index](goal). -/
theorem countableClassEnumeration_surjective (I : Type v) [Nonempty I] [Countable I] :
    Function.Surjective (countableClassEnumeration I) :=
  Classical.choose_spec (exists_surjective_nat I)

/-- Given [a nonempty countable score class `g`](hyp:I,g), [a sample size `n`](hyp:n), [a
finite-prefix length `m + 1`](hyp:m), and [a sample `s`](hyp:s), the [finite-truncation empirical
supremum](goal) is the maximum of the first `m + 1` enumerated zero-offset scores. -/
noncomputable def countableEmpiricalSupremumTruncation {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) (n m : ℕ) (s : Fin n → X) : ℝ :=
  finiteEmpiricalSupremum (Fin (m + 1))
    (fun j => g (countableClassEnumeration I j)) n (fun _ => 0) s

/-- Given [a nonempty countable score class `g`](hyp:I,g), [a sample size `n`](hyp:n), and [a
sample `s`](hyp:s), the [countable empirical supremum](goal) is the supremum of all zero-offset
empirical scores; it does not choose or assume a maximizing index. -/
noncomputable def countableEmpiricalSupremum {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) (n : ℕ) (s : Fin n → X) : ℝ :=
  ⨆ i : I, finiteEmpiricalScore g n (fun _ => 0) i s

/-- For [a nonempty countable score class](hyp:I,g), [sample size `n`](hyp:n), and [sample
`s`](hyp:s), its [finite-prefix empirical suprema increase with the prefix length](goal). -/
theorem countableEmpiricalSupremumTruncation_monotone {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) (n : ℕ) (s : Fin n → X) :
    Monotone (fun m => countableEmpiricalSupremumTruncation I g n m s) := by
  intro m m' hmm'
  change finiteEmpiricalSupremum (Fin (m + 1))
      (fun k => g (countableClassEnumeration I k)) n (fun _ => 0) s ≤
    finiteEmpiricalSupremum (Fin (m' + 1))
      (fun k => g (countableClassEnumeration I k)) n (fun _ => 0) s
  rw [finiteEmpiricalSupremum_eq_score]
  let j : Fin (m' + 1) :=
    ⟨(finiteEmpiricalMaximizer (Fin (m + 1))
      (fun k => g (countableClassEnumeration I k)) n (fun _ => 0) s : ℕ),
      lt_of_lt_of_le (Fin.isLt _) (Nat.add_le_add_right hmm' 1)⟩
  have hle := finiteEmpiricalScore_le_supremum
    (fun k : Fin (m' + 1) => g (countableClassEnumeration I k)) n
    (fun _ => 0) s j
  simpa [j, finiteEmpiricalScore] using hle

/-- If [the score class is uniformly bounded in absolute value by `B`](hyp:hbound), then [every
finite-prefix empirical supremum has absolute value at most `n B`](goal) for [every prefix and
sample](hyp:I,g,n,m,s). -/
theorem abs_countableEmpiricalSupremumTruncation_le {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n m : ℕ) (s : Fin n → X) :
    |countableEmpiricalSupremumTruncation I g n m s| ≤ (n : ℝ) * B := by
  simpa [countableEmpiricalSupremumTruncation] using
    (abs_finiteEmpiricalSupremum_le
      (fun j : Fin (m + 1) => g (countableClassEnumeration I j))
      (A := 0) (B := B) (fun j x => hbound _ x) n (fun _ => 0)
      (fun _ => by simp) s)

/-- If [the score class is uniformly bounded in absolute value by `B`](hyp:hbound), then [the
countable empirical supremum has absolute value at most `n B`](goal) for [every sample](hyp:I,g,n,s).
-/
theorem abs_countableEmpiricalSupremum_le {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (s : Fin n → X) :
    |countableEmpiricalSupremum I g n s| ≤ (n : ℝ) * B := by
  have hupper : ∀ i : I, finiteEmpiricalScore g n (fun _ => 0) i s ≤ (n : ℝ) * B := by
    intro i
    have habs := abs_finiteEmpiricalScore_le (A := 0) (B := B) g hbound n
      (fun _ : I => (0 : ℝ)) (fun _ => by simp) i s
    exact (le_abs_self _).trans (by simpa using habs)
  have hbdd : BddAbove (Set.range fun i : I => finiteEmpiricalScore g n (fun _ => 0) i s) :=
    ⟨(n : ℝ) * B, by rintro _ ⟨i, rfl⟩; exact hupper i⟩
  apply abs_le.mpr
  constructor
  · let i0 : I := Classical.choice inferInstance
    have hi0 : -((n : ℝ) * B) ≤ finiteEmpiricalScore g n (fun _ => 0) i0 s := by
      have habs := abs_finiteEmpiricalScore_le (A := 0) (B := B) g hbound n
        (fun _ : I => (0 : ℝ)) (fun _ => by simp) i0 s
      simpa using (abs_le.mp (by simpa using habs)).1
    unfold countableEmpiricalSupremum
    exact hi0.trans (le_ciSup hbdd i0)
  · unfold countableEmpiricalSupremum
    exact ciSup_le hupper

/-- If [every score is measurable](hyp:hg), then [each finite-prefix empirical supremum is
measurable](goal) for [the countable class and sample size](hyp:I,g,n,m). -/
@[fun_prop]
theorem measurable_countableEmpiricalSupremumTruncation {X : Type u} (I : Type v)
    [MeasurableSpace X] [Nonempty I] [Countable I] (g : I → X → ℝ)
    (hg : ∀ i, Measurable (g i)) (n m : ℕ) :
    Measurable (countableEmpiricalSupremumTruncation I g n m) := by
  exact measurable_finiteEmpiricalSupremum _ (fun j => hg _) n (fun _ => 0)

/-- If [every score is measurable](hyp:hg), then [the countable empirical supremum is
measurable](goal) for [the countable class and sample size](hyp:I,g,n). -/
@[fun_prop]
theorem measurable_countableEmpiricalSupremum {X : Type u} (I : Type v)
    [MeasurableSpace X] [Nonempty I] [Countable I] (g : I → X → ℝ)
    (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    Measurable (countableEmpiricalSupremum I g n) := by
  unfold countableEmpiricalSupremum
  exact Measurable.iSup (fun i => measurable_finiteEmpiricalScore g hg n (fun _ => 0) i)

/-- Under [a uniform absolute score bound](hyp:hbound), the [increasing finite-prefix empirical
suprema converge pointwise to the full countable supremum](goal) for [every sample](hyp:I,g,n,s).
-/
theorem tendsto_countableEmpiricalSupremumTruncation {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (s : Fin n → X) :
    Tendsto (fun m => countableEmpiricalSupremumTruncation I g n m s) atTop
      (nhds (countableEmpiricalSupremum I g n s)) := by
  have hbdd : BddAbove (Set.range fun m => countableEmpiricalSupremumTruncation I g n m s) := by
    refine ⟨(n : ℝ) * B, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact (le_abs_self _).trans (abs_countableEmpiricalSupremumTruncation_le I g hbound n m s)
  have ht := tendsto_atTop_ciSup
    (countableEmpiricalSupremumTruncation_monotone I g n s) hbdd
  have hfullBdd : BddAbove
      (Set.range fun i : I => finiteEmpiricalScore g n (fun _ => 0) i s) :=
    ⟨(n : ℝ) * B, by
      rintro _ ⟨i, rfl⟩
      have habs := abs_finiteEmpiricalScore_le (A := 0) (B := B) g hbound n
        (fun _ : I => (0 : ℝ)) (fun _ => by simp) i s
      exact (le_abs_self _).trans (by simpa using habs)⟩
  have heq : (⨆ m, countableEmpiricalSupremumTruncation I g n m s) =
      countableEmpiricalSupremum I g n s := by
    apply le_antisymm
    · apply ciSup_le
      intro m
      rw [countableEmpiricalSupremumTruncation, finiteEmpiricalSupremum_eq_score]
      exact le_ciSup hfullBdd
        (countableClassEnumeration I
          (finiteEmpiricalMaximizer (Fin (m + 1))
            (fun j => g (countableClassEnumeration I j)) n (fun _ => 0) s))
    · unfold countableEmpiricalSupremum
      apply ciSup_le
      intro i
      obtain ⟨k, hk⟩ := countableClassEnumeration_surjective I i
      have hscore := finiteEmpiricalScore_le_supremum
        (fun j : Fin (k + 1) => g (countableClassEnumeration I j)) n
        (fun _ => 0) s (⟨k, Nat.lt_add_one k⟩ : Fin (k + 1))
      have hle : finiteEmpiricalScore g n (fun _ => 0) i s ≤
          countableEmpiricalSupremumTruncation I g n k s := by
        simpa [countableEmpiricalSupremumTruncation, finiteEmpiricalScore, hk] using hscore
      exact hle.trans (le_ciSup hbdd k)
  rw [← heq]
  exact ht

/-- Under [measurability and a uniform absolute bound](hyp:hg,hbound), [the expectations of the
increasing finite-prefix suprema converge to the expectation of the countable supremum](goal)
under [the product probability law](hyp:mu) for [the specified sample size](hyp:I,g,n). -/
theorem tendsto_integral_countableEmpiricalSupremumTruncation {X : Type u} (I : Type v)
    [MeasurableSpace X] [Nonempty I] [Countable I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) :
    Tendsto
      (fun m => ∫ s, countableEmpiricalSupremumTruncation I g n m s
        ∂Measure.pi (fun _ : Fin n => mu)) atTop
      (nhds (∫ s, countableEmpiricalSupremum I g n s
        ∂Measure.pi (fun _ : Fin n => mu))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (n : ℝ) * B)
  · intro m
    exact (measurable_countableEmpiricalSupremumTruncation I g hg n m).aestronglyMeasurable
  · exact integrable_const ((n : ℝ) * B)
  · intro m
    filter_upwards with s
    simpa [Real.norm_eq_abs] using
      abs_countableEmpiricalSupremumTruncation_le I g hbound n m s
  · filter_upwards with s
    exact tendsto_countableEmpiricalSupremumTruncation I g hbound n s

/-- For [a uniformly bounded countable score class](hyp:hbound), [a strict threshold `t`](hyp:t),
and [sample size `n`](hyp:I,g,n), the [strict upper-tail event of the full countable supremum is
the increasing union of the finite-prefix strict upper-tail events](goal). -/
theorem countableEmpiricalSupremum_tailEvent_eq_iUnion {X : Type u} (I : Type v)
    [Nonempty I] [Countable I] (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (t : ℝ) :
    {s | t < countableEmpiricalSupremum I g n s} =
      ⋃ m : ℕ, {s | t < countableEmpiricalSupremumTruncation I g n m s} := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hs
    have htend := tendsto_countableEmpiricalSupremumTruncation I g hbound n s
    have hev := htend.eventually (Ioi_mem_nhds hs)
    rw [eventually_atTop] at hev
    obtain ⟨m, hm⟩ := hev
    exact ⟨m, hm m le_rfl⟩
  · rintro ⟨m, hm⟩
    have hbdd : BddAbove
        (Set.range fun i : I => finiteEmpiricalScore g n (fun _ => 0) i s) := by
      refine ⟨(n : ℝ) * B, ?_⟩
      rintro _ ⟨i, rfl⟩
      have habs := abs_finiteEmpiricalScore_le (A := 0) (B := B) g hbound n
        (fun _ : I => (0 : ℝ)) (fun _ => by simp) i s
      exact (le_abs_self _).trans (by simpa using habs)
    have hle : countableEmpiricalSupremumTruncation I g n m s ≤
        countableEmpiricalSupremum I g n s := by
      rw [countableEmpiricalSupremumTruncation, finiteEmpiricalSupremum_eq_score]
      unfold countableEmpiricalSupremum
      exact le_ciSup hbdd _
    exact hm.trans_le hle

/-- **Countable-class centered MGF bound, with conservative constants.** Under [an i.i.d.
probability law mu](hyp:mu), a [nonempty countable measurable centered score class
g](hyp:I,g,hg,hmean) whose scores are [bounded in absolute value by the nonnegative constant
B](hyp:hB,hbound), [at most one](hyp:hupper), and have [second moments at most the nonnegative
proxy sigma2](hyp:hsigma,hsecond), the [centered MGF of the countable n-coordinate empirical
supremum](goal) obeys the same bound as its finite truncations at [a nonnegative tilt below one
half](hyp:hlam,hlam_half). -/
theorem countableEmpiricalSupremum_mgf_centered_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Nonempty I] [Countable I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {B sigma2 : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (hlam_half : 2 * lam < 1) :
    mgf
        (fun s => countableEmpiricalSupremum I g n s -
          ∫ r, countableEmpiricalSupremum I g n r
            ∂Measure.pi (fun _ : Fin n => mu))
        (Measure.pi (fun _ : Fin n => mu)) lam ≤
      Real.exp
        ((2 * (∫ s, countableEmpiricalSupremum I g n s
            ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2) * lam ^ 2 /
          (1 - 2 * lam)) := by
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  let Zm : ℕ → (Fin n → X) → ℝ :=
    fun m => countableEmpiricalSupremumTruncation I g n m
  let Z : (Fin n → X) → ℝ := countableEmpiricalSupremum I g n
  let C : ℝ := (n : ℝ) * B
  have hZm_meas : ∀ m, Measurable (Zm m) := by
    intro m
    exact measurable_countableEmpiricalSupremumTruncation I g hg n m
  have hZ_meas : Measurable Z := measurable_countableEmpiricalSupremum I g hg n
  have hZm_abs : ∀ m s, |Zm m s| ≤ C := by
    intro m s
    exact abs_countableEmpiricalSupremumTruncation_le I g hbound n m s
  have hZ_abs : ∀ s, |Z s| ≤ C := by
    intro s
    exact abs_countableEmpiricalSupremum_le I g hbound n s
  have hZm_int : ∀ m, Integrable (Zm m) productMeasure := by
    intro m
    exact Integrable.of_bound (hZm_meas m).aestronglyMeasurable C
      (ae_of_all _ fun s => by simpa [Real.norm_eq_abs] using hZm_abs m s)
  have hmean_tend : Tendsto (fun m => ∫ s, Zm m s ∂productMeasure) atTop
      (nhds (∫ s, Z s ∂productMeasure)) := by
    simpa [Zm, Z, productMeasure] using
      tendsto_integral_countableEmpiricalSupremumTruncation I mu g hg hbound n
  have hmean_abs : ∀ m, |∫ s, Zm m s ∂productMeasure| ≤ C := by
    intro m
    calc
      |∫ s, Zm m s ∂productMeasure| ≤ ∫ s, |Zm m s| ∂productMeasure :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _s, C ∂productMeasure := by
        exact integral_mono (hZm_int m).abs (integrable_const C) (hZm_abs m)
      _ = C := by simp [productMeasure]
  have hcenter_tend : ∀ s, Tendsto
      (fun m => Zm m s - ∫ r, Zm m r ∂productMeasure) atTop
      (nhds (Z s - ∫ r, Z r ∂productMeasure)) := by
    intro s
    exact (tendsto_countableEmpiricalSupremumTruncation I g hbound n s).sub hmean_tend
  have hmgf_tend : Tendsto
      (fun m => mgf (fun s => Zm m s - ∫ r, Zm m r ∂productMeasure)
        productMeasure lam) atTop
      (nhds (mgf (fun s => Z s - ∫ r, Z r ∂productMeasure)
        productMeasure lam)) := by
    simp only [mgf]
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (|lam| * (2 * C)))
    · intro m
      exact ((hZm_meas m).sub measurable_const).const_mul lam |>.exp.aestronglyMeasurable
    · exact integrable_const _
    · intro m
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        lam * (Zm m s - ∫ r, Zm m r ∂productMeasure)
            ≤ |lam * (Zm m s - ∫ r, Zm m r ∂productMeasure)| := le_abs_self _
        _ = |lam| * |Zm m s - ∫ r, Zm m r ∂productMeasure| := abs_mul _ _
        _ ≤ |lam| * (2 * C) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg lam)
          exact (abs_sub _ _).trans (by linarith [hZm_abs m s, hmean_abs m])
    · filter_upwards with s
      exact Real.continuous_exp.continuousAt.tendsto.comp
        ((hcenter_tend s).const_mul lam)
  have hfinite : ∀ m,
      mgf (fun s => Zm m s - ∫ r, Zm m r ∂productMeasure) productMeasure lam ≤
        Real.exp
          ((2 * (∫ s, Zm m s ∂productMeasure) + (n : ℝ) * sigma2) * lam ^ 2 /
            (1 - 2 * lam)) := by
    intro m
    simpa [Zm, productMeasure, countableEmpiricalSupremumTruncation] using
      Causalean.Stat.Concentration.EntropyMethod.finiteEmpiricalSupremum_mgf_centered_le mu
        (fun j : Fin (m + 1) => g (countableClassEnumeration I j))
        (fun j => hg _) hB (fun j x => hbound _ x) (fun j x => hupper _ x)
        (fun j => hmean _) hsigma (fun j => hsecond _) n hlam hlam_half
  have hrhs_tend : Tendsto
      (fun m => Real.exp
        ((2 * (∫ s, Zm m s ∂productMeasure) + (n : ℝ) * sigma2) * lam ^ 2 /
          (1 - 2 * lam))) atTop
      (nhds (Real.exp
        ((2 * (∫ s, Z s ∂productMeasure) + (n : ℝ) * sigma2) * lam ^ 2 /
          (1 - 2 * lam)))) := by
    let phi : ℝ → ℝ := fun x => Real.exp
      ((2 * x + (n : ℝ) * sigma2) * lam ^ 2 / (1 - 2 * lam))
    have hphi : Continuous phi := by
      dsimp [phi]
      fun_prop
    exact hphi.continuousAt.tendsto.comp hmean_tend
  exact le_of_tendsto_of_tendsto hmgf_tend hrhs_tend
    (Filter.Eventually.of_forall hfinite)

/-- **Countable-class Bousquet upper tail, with conservative constants.** Under [an i.i.d.
probability law mu](hyp:mu), a [nonempty countable measurable centered score class
g](hyp:I,g,hg,hmean) whose scores are [bounded in absolute value by the nonnegative constant
B](hyp:hB,hbound), [at most one](hyp:hupper), and have [second moments at most the nonnegative
proxy sigma2](hyp:hsigma,hsecond), every [positive deviation t](hyp:ht) [obeys the stated
variance-sensitive upper tail](goal) for the [countable n-coordinate empirical supremum](hyp:n),
provided its [mean plus half the total variance proxy is positive](hyp:hscale). The denominator
is the explicit conservative value 8 E Z + 4 n sigma2 + 4 t. -/
theorem countableEmpiricalSupremum_upper_tail
    {X : Type u} {I : Type v} [MeasurableSpace X] [Nonempty I] [Countable I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {B sigma2 : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (n : ℕ)
    (hscale : 0 < (∫ s, countableEmpiricalSupremum I g n s
        ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2 / 2)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {s | t ≤ countableEmpiricalSupremum I g n s -
          ∫ r, countableEmpiricalSupremum I g n r
            ∂Measure.pi (fun _ : Fin n => mu)} ≤
      Real.exp (-t ^ 2 /
        (8 * ((∫ s, countableEmpiricalSupremum I g n s
          ∂Measure.pi (fun _ : Fin n => mu)) + (n : ℝ) * sigma2 / 2) + 4 * t)) := by
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  let Z := countableEmpiricalSupremum I g n
  let meanZ := ∫ s, Z s ∂productMeasure
  let C := 2 * (meanZ + (n : ℝ) * sigma2 / 2)
  let lam := t / (2 * C + 2 * t)
  have hC : 0 < C := by dsimp [C, meanZ, Z, productMeasure]; positivity
  have hden : 0 < 2 * C + 2 * t := by positivity
  have hlam : 0 ≤ lam := (div_pos ht hden).le
  have hlamHalf : 2 * lam < 1 := by
    dsimp [lam]
    rw [show 2 * (t / (2 * C + 2 * t)) = (2 * t) / (2 * C + 2 * t) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hZInt : Integrable Z productMeasure :=
    Integrable.of_bound (measurable_countableEmpiricalSupremum I g hg n).aestronglyMeasurable
      ((n : ℝ) * B) (ae_of_all _ fun s => by
        simpa [Z, Real.norm_eq_abs] using abs_countableEmpiricalSupremum_le I g hbound n s)
  have hmeanZ_abs : |meanZ| ≤ (n : ℝ) * B := by
    dsimp [meanZ]
    calc
      |∫ s, Z s ∂productMeasure| ≤ ∫ s, |Z s| ∂productMeasure :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _s, (n : ℝ) * B ∂productMeasure := by
        exact integral_mono hZInt.abs (integrable_const _)
          (fun s => abs_countableEmpiricalSupremum_le I g hbound n s)
      _ = (n : ℝ) * B := by simp [productMeasure]
  have hint : Integrable (fun s => Real.exp (lam * (Z s - meanZ))) productMeasure := by
    apply Integrable.of_bound
      (((measurable_countableEmpiricalSupremum I g hg n).sub measurable_const).const_mul lam
        |>.exp.aestronglyMeasurable)
      (Real.exp (|lam| * (2 * ((n : ℝ) * B))))
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * (Z s - meanZ) ≤ |lam * (Z s - meanZ)| := le_abs_self _
      _ = |lam| * |Z s - meanZ| := abs_mul _ _
      _ ≤ |lam| * (2 * ((n : ℝ) * B)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg lam)
        exact (abs_sub _ _).trans (by linarith [abs_countableEmpiricalSupremum_le I g hbound n s,
          hmeanZ_abs])
  have hchernoff := measure_ge_le_exp_mul_mgf t hlam hint
  have hmgf : mgf (fun s => Z s - meanZ) productMeasure lam ≤
      Real.exp (C * lam ^ 2 / (1 - 2 * lam)) := by
    have h := countableEmpiricalSupremum_mgf_centered_le mu g hg hB hbound hupper
      hmean hsigma hsecond n hlam hlamHalf
    dsimp [C, meanZ, Z, productMeasure] at h ⊢
    convert h using 1 <;> ring_nf
  calc
    productMeasure.real {s | t ≤ Z s - meanZ} ≤
        Real.exp (-lam * t) * mgf (fun s => Z s - meanZ) productMeasure lam := hchernoff
    _ ≤ Real.exp (-lam * t) * Real.exp (C * lam ^ 2 / (1 - 2 * lam)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (4 * C + 4 * t)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      have hpole : 1 - 2 * (t / (2 * C + 2 * t)) ≠ 0 :=
        ne_of_gt (sub_pos.mpr hlamHalf)
      field_simp [hden.ne', hpole, hC.ne']
      ring
    _ = Real.exp (-t ^ 2 / (8 * (meanZ + (n : ℝ) * sigma2 / 2) + 4 * t)) := by
      congr 2
      dsimp [C]
      ring

end Causalean.Stat.Concentration.EntropyMethod
