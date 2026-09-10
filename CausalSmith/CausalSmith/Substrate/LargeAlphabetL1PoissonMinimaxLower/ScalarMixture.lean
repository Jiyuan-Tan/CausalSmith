import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Basic
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.PoissonCharlier
import Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.MaximalCoupling
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Moment-matched scalar priors and Poisson mixtures

This module isolates the approximation-theoretic scalar prior pair and the
analytic fact that matching sufficiently many moments makes the corresponding
mixed-Poisson laws close.  The statements use actual probability measures and
explicit support, moment, separation, and total-variation conditions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

private noncomputable def unitAffineNN (x : ℝ) : ℝ≥0 :=
  ⟨max 0 ((x + 1) / 2), le_max_left _ _⟩

private lemma measurable_unitAffineNN : Measurable unitAffineNN := by
  apply Measurable.subtype_mk
  change Measurable fun x : ℝ => max 0 ((x + 1) / 2)
  fun_prop

private lemma coe_unitAffineNN_of_mem {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (unitAffineNN x : ℝ) = (x + 1) / 2 := by
  change max 0 ((x + 1) / 2) = (x + 1) / 2
  rw [max_eq_right]
  linarith [hx.1]

private lemma ae_mem_unitInterval_of_mass_one (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : ν (Set.Icc (-1 : ℝ) 1) = 1) :
    ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hc : ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top ν _), hs, measure_univ]
    simp
  rw [ae_iff]
  change ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  exact hc

private lemma integrable_pow_of_unit_support (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : ν (Set.Icc (-1 : ℝ) 1) = 1) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [ae_mem_unitInterval_of_mass_one ν hs] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg x) (abs_le.2 hx)

private lemma unitAffine_map_supported (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : ν (Set.Icc (-1 : ℝ) 1) = 1) :
    (Measure.map unitAffineNN ν) (Set.Icc (0 : ℝ≥0) 1) = 1 := by
  rw [Measure.map_apply measurable_unitAffineNN measurableSet_Icc]
  apply le_antisymm
  · simpa using measure_mono
      (μ := ν) (Set.subset_univ (unitAffineNN ⁻¹' Set.Icc (0 : ℝ≥0) 1))
  · rw [← hs]
    apply measure_mono
    intro x hx
    constructor
    · exact (unitAffineNN x).2
    · apply NNReal.coe_le_coe.mp
      rw [coe_unitAffineNN_of_mem hx]
      norm_num
      linarith [hx.2]

private lemma unitAffine_moment_eq {ν0 ν1 : Measure ℝ}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    (hs0 : ν0 (Set.Icc (-1 : ℝ) 1) = 1)
    (hs1 : ν1 (Set.Icc (-1 : ℝ) 1) = 1)
    (k : ℕ) (hmom : ∀ j ≤ k, (∫ x, x ^ j ∂ν0) = ∫ x, x ^ j ∂ν1) :
    (∫ y, (y : ℝ) ^ k ∂Measure.map unitAffineNN ν0) =
      ∫ y, (y : ℝ) ^ k ∂Measure.map unitAffineNN ν1 := by
  rw [integral_map measurable_unitAffineNN.aemeasurable (by fun_prop),
    integral_map measurable_unitAffineNN.aemeasurable (by fun_prop)]
  have hae0 : (fun x : ℝ => (unitAffineNN x : ℝ) ^ k) =ᵐ[ν0]
      fun x => ((x + 1) / 2) ^ k := by
    filter_upwards [ae_mem_unitInterval_of_mass_one ν0 hs0] with x hx
    rw [coe_unitAffineNN_of_mem hx]
  have hae1 : (fun x : ℝ => (unitAffineNN x : ℝ) ^ k) =ᵐ[ν1]
      fun x => ((x + 1) / 2) ^ k := by
    filter_upwards [ae_mem_unitInterval_of_mass_one ν1 hs1] with x hx
    rw [coe_unitAffineNN_of_mem hx]
  rw [integral_congr_ae hae0, integral_congr_ae hae1]
  simp_rw [div_pow, add_pow]
  rw [integral_div, integral_div]
  congr 1
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [one_pow, mul_one]
    rw [integral_mul_const, integral_mul_const,
      hmom j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro j hj
    simpa using (integrable_pow_of_unit_support ν1 hs1 j).mul_const
      (k.choose j : ℝ)
  · intro j hj
    simpa using (integrable_pow_of_unit_support ν0 hs0 j).mul_const
      (k.choose j : ℝ)

private lemma unitAffine_abs_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : ν (Set.Icc (-1 : ℝ) 1) = 1) :
    (∫ y, |(y : ℝ) - (1 / 2 : ℝ≥0)| ∂Measure.map unitAffineNN ν) =
      (∫ x, |x| ∂ν) / 2 := by
  rw [integral_map measurable_unitAffineNN.aemeasurable (by fun_prop)]
  have hae : (fun x : ℝ => |(unitAffineNN x : ℝ) - (1 / 2 : ℝ≥0)|) =ᵐ[ν]
      fun x => |x| / 2 := by
    filter_upwards [ae_mem_unitInterval_of_mass_one ν hs] with x hx
    rw [coe_unitAffineNN_of_mem hx]
    norm_num
    rw [show (x + 1) / 2 - 1 / 2 = x / 2 by ring, abs_div]
    norm_num
  rw [integral_congr_ae hae, integral_div]

/-- The absolute-deviation expectation of a nonnegative scalar law about a
fixed center. -/
noncomputable def absMomentAbout (ν : Measure ℝ≥0) (a : ℝ≥0) : ℝ :=
  ∫ x, |(x : ℝ) - (a : ℝ)| ∂ν

/-- A scalar moment-prior pair consists of two probability laws in the same
nonnegative interval, matching through degree `K`, with the second law having
the stated absolute-moment advantage. -/
structure ScalarMomentPriorPair (K : ℕ) (a M : ℝ≥0) where
  /-- The lower-target scalar prior. -/
  ν0 : Measure ℝ≥0
  /-- The upper-target scalar prior. -/
  ν1 : Measure ℝ≥0
  /-- The lower-target prior is a probability measure. -/
  ν0_probability : IsProbabilityMeasure ν0
  /-- The upper-target prior is a probability measure. -/
  ν1_probability : IsProbabilityMeasure ν1
  /-- The lower-target prior is supported on `[a-M,a+M]`. -/
  ν0_support : ν0 (Set.Icc (a - M) (a + M)) = 1
  /-- The upper-target prior is supported on `[a-M,a+M]`. -/
  ν1_support : ν1 (Set.Icc (a - M) (a + M)) = 1
  /-- All real moments through degree `K` agree. -/
  moments_eq : ∀ k ≤ K,
    (∫ x, (x : ℝ) ^ k ∂ν0) = ∫ x, (x : ℝ) ^ k ∂ν1

/-- The target separation of a scalar moment-prior pair is the difference of
its two expected absolute deviations. -/
noncomputable def ScalarMomentPriorPair.absGap {K : ℕ} {a M : ℝ≥0}
    (W : ScalarMomentPriorPair K a M) : ℝ :=
  absMomentAbout W.ν1 a - absMomentAbout W.ν0 a

/-- Universal-order moment-matched priors for the absolute value exist: for
every degree at least two, two laws on `[0,1]` match through that degree and
have absolute-deviation expectations separated by order `1/K`.

Proof route: apply the absolute-value best-polynomial-approximation duality
substrate, symmetrize its extremal signed measure, and affinely push the two
Jordan parts from `[-1,1]` to `[0,1]`. -/
theorem exists_absMomentPriorPair :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, 2 ≤ K →
      ∃ W : ScalarMomentPriorPair K (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0),
        c / (K + 1 : ℝ) ≤ W.absGap := by
  let c : ℝ := 1 / 200
  refine ⟨c, by simp [c], ?_⟩
  intro K hK
  let N := 2 * K
  have hN : 0 < N := by omega
  have hNeven : Even N := ⟨K, by dsimp [N]; omega⟩
  let P := Classical.choice
    (exists_symmetric_momentMatched_absGap hN hNeven)
  let ν0 : Measure ℝ≥0 := Measure.map unitAffineNN P.ν₀
  let ν1 : Measure ℝ≥0 := Measure.map unitAffineNN P.ν₁
  haveI hP0 : IsProbabilityMeasure P.ν₀ := P.probability₀
  haveI hP1 : IsProbabilityMeasure P.ν₁ := P.probability₁
  have hsP0 : P.ν₀ (Set.Icc (-1 : ℝ) 1) = 1 := by
    have hc : P.ν₀ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
      simpa [IsSupportedOnUnitInterval,
        Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.unitInterval] using
          P.supported₀
    rw [← compl_compl (Set.Icc (-1 : ℝ) 1),
      measure_compl measurableSet_Icc.compl (measure_ne_top P.ν₀ _),
      hc, measure_univ]
    simp
  have hsP1 : P.ν₁ (Set.Icc (-1 : ℝ) 1) = 1 := by
    have hc : P.ν₁ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
      simpa [IsSupportedOnUnitInterval,
        Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.unitInterval] using
          P.supported₁
    rw [← compl_compl (Set.Icc (-1 : ℝ) 1),
      measure_compl measurableSet_Icc.compl (measure_ne_top P.ν₁ _),
      hc, measure_univ]
    simp
  haveI hν0 : IsProbabilityMeasure ν0 :=
    Measure.isProbabilityMeasure_map measurable_unitAffineNN.aemeasurable
  haveI hν1 : IsProbabilityMeasure ν1 :=
    Measure.isProbabilityMeasure_map measurable_unitAffineNN.aemeasurable
  let W : ScalarMomentPriorPair K (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) :=
    { ν0 := ν0
      ν1 := ν1
      ν0_probability := hν0
      ν1_probability := hν1
      ν0_support := by
        convert unitAffine_map_supported P.ν₀ hsP0 using 1 <;> norm_num [ν0]
      ν1_support := by
        convert unitAffine_map_supported P.ν₁ hsP1 using 1 <;> norm_num [ν1]
      moments_eq := by
        intro k hk
        apply unitAffine_moment_eq hsP0 hsP1 k
        intro j hj
        exact P.moments_eq j (by omega) }
  refine ⟨W, ?_⟩
  have hgap : W.absGap =
      bestUniformApproxErrorAbs N := by
    rw [ScalarMomentPriorPair.absGap]
    change absMomentAbout ν1 (1 / 2 : ℝ≥0) -
      absMomentAbout ν0 (1 / 2 : ℝ≥0) = _
    rw [absMomentAbout, absMomentAbout,
      unitAffine_abs_integral P.ν₁ hsP1,
      unitAffine_abs_integral P.ν₀ hsP0]
    linarith [P.abs_gap]
  rw [hgap]
  have hlower := bestUniformApproxErrorAbs_lower N hN
  calc
    c / (K + 1 : ℝ) ≤ (1 / 100 : ℝ) / (N : ℝ) := by
      dsimp [c, N]
      have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)
        (by positivity : (0 : ℝ) < (2 * K : ℕ))]
      norm_num
      linarith
    _ ≤ _ := hlower

/-- Mixing a scalar Poisson law over a nonnegative rate prior gives the
unconditional count law. -/
noncomputable def poissonRateMixture (ν : Measure ℝ≥0) : Measure ℕ :=
  ν.bind poissonMeasure

/-- A mixed-Poisson law is a probability measure whenever its mixing law is a
probability measure. -/
instance poissonRateMixture_isProbabilityMeasure (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (poissonRateMixture ν) := by
  apply isProbabilityMeasure_bind
  · apply Measurable.aemeasurable
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [poissonMeasure, Measure.sum_apply _ hs, Measure.smul_apply,
      Measure.dirac_apply' _ hs]
    fun_prop
  · exact Filter.Eventually.of_forall fun _ => inferInstance

/-- If two rate priors in `[a-M,a+M]` match through degree `L` and
`L+1 ≥ (2eM)²/a`, then their mixed-Poisson laws have the explicit geometric
total-variation bound from the moment expansion.

Proof route (Jiao--Han--Weissman, Lemma `mixturepoissontvbound`): write the
total variation as the sum of the absolute differences of the mixed Poisson
point masses.  After the change of variables `U = a + M X`, Taylor-expand
`exp (-(a+Mx)) * (a+Mx)^j` at zero.  Raw moment matching cancels degrees at
most `L`.  The remaining derivative sum is a Poisson expectation of a
Charlier polynomial; Cauchy--Schwarz and its factorial second moment bound it
by `(M * sqrt (k/a))^k`.  Finally use `k! ≥ (k/e)^k` and the degree hypothesis
to sum a geometric tail of ratio at most `1/2`. -/
theorem tvDist_poissonRateMixture_le_of_momentMatch
    {ν0 ν1 : Measure ℝ≥0} [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ}
    (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L,
      (∫ x, (x : ℝ) ^ k ∂ν0) = ∫ x, (x : ℝ) ^ k ∂ν1)
    (hdegree : ((2 * Real.exp 1 * (M : ℝ)) ^ 2) / (a : ℝ) ≤ (L + 1 : ℝ)) :
    Causalean.Stat.tvDist (poissonRateMixture ν0) (poissonRateMixture ν1) ≤
      2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) := by
  exact tvDist_bind_poisson_le_of_momentMatch ha hM hs0 hs1 hmom hdegree

private lemma tvDist_le_coupling_ne
    {X Ω : Type*} [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace Ω]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (γ : Measure Ω) [IsProbabilityMeasure γ]
    (f g : Ω → X) (hf : Measurable f) (hg : Measurable g)
    (hfst : γ.map f = μ) (hsnd : γ.map g = ν) :
    Causalean.Stat.tvDist μ ν ≤ γ.real {z | f z ≠ g z} := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  let S : Set Ω := f ⁻¹' A
  let T : Set Ω := g ⁻¹' A
  have hS : MeasurableSet S := hA.preimage hf
  have hT : MeasurableSet T := hA.preimage hg
  have hμ : μ.real A = γ.real S := by
    rw [← hfst, map_measureReal_apply hf hA]
  have hν : ν.real A = γ.real T := by
    rw [← hsnd, map_measureReal_apply hg hA]
  rw [hμ, hν]
  refine (abs_measureReal_sub_le_measureReal_symmDiff hS.nullMeasurableSet
    hT.nullMeasurableSet).trans ?_
  apply measureReal_mono
  · intro z hz
    simp only [Set.mem_symmDiff, Set.mem_preimage, S, T] at hz
    change f z ≠ g z
    rintro hfg
    rcases hz with ⟨hfA, hgA⟩ | ⟨hgA, hfA⟩
    · exact hgA (hfg ▸ hfA)
    · exact hfA (hfg.symm ▸ hgA)
  · exact measure_ne_top γ _

private lemma maximalCoupling_ne_mass_le
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (Causalean.Stat.maximalCoupling μ ν).real {z | z.1 ≠ z.2} ≤
      Causalean.Stat.tvDist μ ν := by
  let γ := Causalean.Stat.maximalCoupling μ ν
  let D : Set (X × X) := {z | z.1 = z.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have hdiagENN := Causalean.Stat.maximalCoupling_eq_mass_ge μ ν
  have hdiag : 1 - Causalean.Stat.tvDist μ ν ≤ γ.real D := by
    have hreal := ENNReal.toReal_mono (by simp) hdiagENN
    change 1 - Causalean.Stat.tvDist μ ν ≤ (γ D).toReal
    simpa [γ, D, ENNReal.toReal_ofReal (sub_nonneg.mpr
      (Causalean.Stat.tvDist_le_one (μ := μ) (ν := ν)))] using hreal
  have hcompl : γ.real Dᶜ = 1 - γ.real D := by
    rw [measureReal_compl hD, probReal_univ]
  have hne : {z : X × X | z.1 ≠ z.2} = Dᶜ := by
    ext z
    simp [D]
  rw [hne, hcompl]
  linarith

private theorem tvDist_pi_le_sum
    {X : Type*} [MeasurableSpace X] [MeasurableEq X] [Countable X]
    {m : ℕ} (μ ν : Fin m → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    Causalean.Stat.tvDist (Measure.pi μ) (Measure.pi ν) ≤
      ∑ i, Causalean.Stat.tvDist (μ i) (ν i) := by
  let γ : Fin m → Measure (X × X) :=
    fun i => Causalean.Stat.maximalCoupling (μ i) (ν i)
  let Γ : Measure (Fin m → X × X) := Measure.pi γ
  let left : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).1
  let right : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).2
  let E : Fin m → Set (Fin m → X × X) := fun i => {z | (z i).1 ≠ (z i).2}
  let bad : Set (Fin m → X × X) := {z | ∃ i, (z i).1 ≠ (z i).2}
  have hleft : Γ.map left = Measure.pi μ := by
    rw [show left = fun z i => Prod.fst (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_fst (μ i) (ν i)
    intro i
    exact measurable_fst.aemeasurable
  have hright : Γ.map right = Measure.pi ν := by
    rw [show right = fun z i => Prod.snd (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_snd (μ i) (ν i)
    intro i
    exact measurable_snd.aemeasurable
  have htv : Causalean.Stat.tvDist (Measure.pi μ) (Measure.pi ν) ≤ Γ.real bad := by
    have hbadLR : {z | left z ≠ right z} = bad := by
      ext z
      simp [bad, left, right, Function.ne_iff]
    rw [← hbadLR]
    apply tvDist_le_coupling_ne _ _ Γ left right
    · dsimp [left]
      fun_prop
    · dsimp [right]
      fun_prop
    · exact hleft
    · exact hright
  have hbad : bad = ⋃ i, E i := by
    ext z
    simp [bad, E]
  have hcoord (i : Fin m) :
      Γ.real (E i) ≤ Causalean.Stat.tvDist (μ i) (ν i) := by
    have hEval : Γ.map (Function.eval i) = γ i := by
      rw [Measure.pi_map_eval]
      simp
    have hmap : Γ.real (E i) = (γ i).real {z | z.1 ≠ z.2} := by
      rw [← hEval, map_measureReal_apply (measurable_pi_apply i)]
      · rfl
      · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [hmap]
    exact maximalCoupling_ne_mass_le (μ i) (ν i)
  calc
    Causalean.Stat.tvDist (Measure.pi μ) (Measure.pi ν) ≤ Γ.real bad := htv
    _ = Γ.real (⋃ i, E i) := by rw [hbad]
    _ ≤ ∑ i, Γ.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ i, Causalean.Stat.tvDist (μ i) (ν i) :=
      Finset.sum_le_sum fun i _ => hcoord i

/-- Coordinatewise total variation tensorizes subadditively for finite
products of mixed-Poisson laws. -/
theorem tvDist_pi_poissonRateMixture_le_sum {d : ℕ}
    (ν0 ν1 : Fin d → Measure ℝ≥0)
    (hν0 : ∀ i, IsProbabilityMeasure (ν0 i))
    (hν1 : ∀ i, IsProbabilityMeasure (ν1 i)) :
    Causalean.Stat.tvDist
        (Measure.pi fun i : Fin d => poissonRateMixture (ν0 i))
        (Measure.pi fun i : Fin d => poissonRateMixture (ν1 i)) ≤
      ∑ i, Causalean.Stat.tvDist
        (poissonRateMixture (ν0 i)) (poissonRateMixture (ν1 i)) := by
  letI : ∀ i, IsProbabilityMeasure (ν0 i) := hν0
  letI : ∀ i, IsProbabilityMeasure (ν1 i) := hν1
  exact tvDist_pi_le_sum (fun i => poissonRateMixture (ν0 i))
    (fun i => poissonRateMixture (ν1 i))

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
