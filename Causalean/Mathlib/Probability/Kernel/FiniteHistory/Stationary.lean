module
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Causalean.Mathlib.Probability.Kernel.FiniteHistory.Expectation

/-!
# Stationary finite-state window bounds

This module turns finite stationary mass identities and ℓ¹-contractive Markov transitions into
geometric covariance bounds for separated bounded windows, without positive atom assumptions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

namespace Causalean.Mathlib.Probability.Kernel.FiniteHistory

/-- A probability [law](hyp:ρ) on a finite measurable space, [candidate atom masses](hyp:π) that [sum to one](hyp:hπsum) and [match the law's singleton masses](hyp:hπatom), and a measurable [score](hyp:v,hv) yield [the corresponding finite weighted-sum integral](goal). -/
theorem integral_finite_eq_sum_of_singleton_masses
    {S : Type*} [Fintype S] [MeasurableSpace S]
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (π : S → ℝ)
    (hπsum : ∑ s, π s = 1)
    (hπatom : ∀ s, (ρ {s}).toReal = π s)
    (v : S → ℝ) (hv : Measurable v) :
    (∫ s, v s ∂ρ) = ∑ s, π s * v s := by
  classical
  let T (A : Set S) : Finset S := Finset.univ.filter (fun s => s ∈ A)
  have hbound (A : Set S) :
      ρ.real A ≤ ∑ s ∈ T A, π s := by
    have hset : A = ⋃ s ∈ T A, ({s} : Set S) := by
      ext s
      simp [T]
    calc
      ρ.real A = ρ.real (⋃ s ∈ T A, ({s} : Set S)) :=
        congrArg ρ.real hset
      _ ≤ ∑ s ∈ T A, ρ.real {s} :=
        measureReal_biUnion_finset_le _ _
      _ = ∑ s ∈ T A, π s := by simp [Measure.real, hπatom]
  have hevent (A : Set S) (hA : MeasurableSet A) :
      ρ.real A = ∑ s ∈ T A, π s := by
    have hc := hbound Aᶜ
    have hs : (∑ s ∈ T A, π s) + (∑ s ∈ T Aᶜ, π s) = 1 := by
      simpa only [T, Set.mem_compl_iff, Finset.sum_filter_add_sum_filter_not] using hπsum
    have hm : ρ.real A + ρ.real Aᶜ = 1 := by
      simpa [probReal_univ] using (measureReal_add_measureReal_compl (μ := ρ) hA)
    have ha := hbound A
    have hreverse : (∑ s ∈ T A, π s) ≤ ρ.real A := by
      calc
        (∑ s ∈ T A, π s) = 1 - (∑ s ∈ T Aᶜ, π s) :=
          eq_sub_of_add_eq hs
        _ ≤ 1 - ρ.real Aᶜ := sub_le_sub_left hc 1
        _ = ρ.real A := (eq_sub_of_add_eq hm).symm
    exact le_antisymm ha hreverse
  let f : SimpleFunc S ℝ := ⟨v, (fun x => hv (measurableSet_singleton x)), Set.finite_range v⟩
  have hf : (f : S → ℝ) = v := rfl
  have hi : Integrable (f : S → ℝ) ρ := f.integrable_of_isFiniteMeasure
  change (∫ s, f s ∂ρ) = ∑ s, π s * v s
  rw [SimpleFunc.integral_eq_sum f hi]
  simp only [smul_eq_mul]
  have hfiber (x : ℝ) :
      ρ.real (v ⁻¹' {x}) = ∑ s ∈ Finset.univ.filter (fun s => v s = x), π s := by
    simpa only [T, Set.mem_preimage, Set.mem_singleton_iff] using
      hevent (v ⁻¹' {x}) (hv (measurableSet_singleton x))
  simp only [hf] at *
  simp_rw [hfiber]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := f.range)
      (g := v) (f := fun s => π s * v s) (by
        intro s hs
        exact f.mem_range_self s)]
  congr 1
  ext x
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hvs : v s = x := (Finset.mem_filter.mp hs).2
  rw [hvs]

/-- [The point-mass probability vector](goal) at [a state s of a finite state space](hyp:s)
[puts mass one on s and zero on every other state](step:1). -/
def pointVector {S : Type*} [Fintype S] [DecidableEq S] (s : S) : S → ℝ :=
  fun t => if t = s then 1 else 0

/-- Let [P be a row-stochastic transition matrix](hyp:P,hP) on a finite state space with
[stationary distribution π](hyp:π,hπ), and suppose [one step of P contracts the ℓ¹ distance
between probability vectors by a factor α](hyp:alpha,hcontract) with [0 ≤ α](hyp:halpha0)
[< 1](hyp:halpha1). Then for [every starting state s](hyp:s) and [every number of steps
gap](hyp:gap), [the ℓ¹ distance between the distribution after gap steps from the point mass at s
and π is at most 2·α^gap](goal). -/
theorem markovIterate_point_stationary_bound
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (π : S → ℝ) (alpha : ℝ)
    (hP : IsStochasticMatrix P) (hπ : IsStationary P π)
    (hcontract : ContractsL1 P alpha)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (gap : ℕ) (s : S) :
    l1Distance (markovIterate P (pointVector s) gap) π ≤ 2 * alpha ^ gap := by
  have hp : IsProbabilityVector (pointVector s) := by
    constructor
    · intro t
      unfold pointVector
      split <;> norm_num
    · simp [pointVector]
  have hbase : l1Distance (pointVector s) π ≤ 2 := by
    unfold l1Distance
    calc
      (∑ t, |pointVector s t - π t|) ≤
          ∑ t, (pointVector s t + π t) := by
        apply Finset.sum_le_sum
        intro t ht
        apply abs_le.mpr
        constructor <;> have := hp.1 t <;> have := hπ.1.1 t <;> linarith
      _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hπ.1.2]; ring
  induction gap with
  | zero => simpa [markovIterate] using hbase
  | succ n ih =>
    have hn := hP.iterate_probability hp n
    calc
      l1Distance (markovIterate P (pointVector s) (n + 1)) π =
          l1Distance (markovStep (markovIterate P (pointVector s) n) P)
            (markovStep π P) := by rw [hπ.2]; rfl
      _ ≤ alpha * l1Distance (markovIterate P (pointVector s) n) π :=
        hcontract _ _ hn hπ.1
      _ ≤ alpha * (2 * alpha ^ n) := mul_le_mul_of_nonneg_left ih halpha0
      _ = 2 * alpha ^ (n + 1) := by rw [pow_succ]; ring

/-- A finite [transition matrix](hyp:P), [stationary distribution](hyp:π), [contraction coefficient](hyp:alpha), [stochasticity certificate](hyp:hP), [stationarity certificate](hyp:hπ), [ℓ¹ contraction certificate](hyp:hcontract), [nonnegative coefficient below one](hyp:halpha0,halpha1), [step gap](hyp:gap), [starting state](hyp:s), and [bounded score](hyp:v,Cv,hv) give [the geometric error bound for its Markov-row mean](goal). -/
theorem markov_row_score_bound
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (π : S → ℝ) (alpha : ℝ)
    (hP : IsStochasticMatrix P) (hπ : IsStationary P π)
    (hcontract : ContractsL1 P alpha)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (gap : ℕ) (s : S) (v : S → ℝ)
    (Cv : ℝ) (hv : ∀ t, |v t| ≤ Cv) :
    |(∑ t, markovIterate P (pointVector s) gap t * v t) -
        (∑ t, π t * v t)| ≤ 2 * Cv * alpha ^ gap := by
  have hCv : 0 ≤ Cv := le_trans (abs_nonneg _) (hv s)
  have hdist := markovIterate_point_stationary_bound P π alpha hP hπ hcontract
    halpha0 halpha1 gap s
  calc
    |(∑ t, markovIterate P (pointVector s) gap t * v t) -
      (∑ t, π t * v t)| ≤ Cv * l1Distance (markovIterate P (pointVector s) gap) π := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ t, (markovIterate P (pointVector s) gap t * v t - π t * v t)| =
              |∑ t, (markovIterate P (pointVector s) gap t - π t) * v t| := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ ≤ ∑ t, |(markovIterate P (pointVector s) gap t - π t) * v t| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ t, |markovIterate P (pointVector s) gap t - π t| * Cv := by
            apply Finset.sum_le_sum
            intro t ht
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hv t) (abs_nonneg _)
          _ = Cv * l1Distance (markovIterate P (pointVector s) gap) π := by
            rw [l1Distance, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
    _ ≤ Cv * (2 * alpha ^ gap) := mul_le_mul_of_nonneg_left hdist hCv
    _ = 2 * Cv * alpha ^ gap := by ring

/-- A finite [transition matrix](hyp:P), [stationary distribution](hyp:π), [stochasticity and stationarity certificates](hyp:hP,hπ), [gap](hyp:gap), probability [past-window law](hyp:μ), measurable [last-state map](hyp:last,hlast_meas) with [stationary singleton masses](hyp:hlast), [stationary future kernel](hyp:Q), [conditional future kernel](hyp:future), [their supplied gap-kernel representation](hyp:hfuture), [joint law](hyp:ν) satisfying [the composition-product identity](hyp:hν), and a measurable normalized [future score](hyp:g,hg,hg_bound) give [the stationary-mixture formula for its marginal mean](goal). -/
theorem stationary_future_window_mean
    {S X Y : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Matrix S S ℝ) (π : S → ℝ)
    (hP : IsStochasticMatrix P) (hπ : IsStationary P π)
    (gap : ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (last : X → S) (hlast_meas : Measurable last)
    (hlast : ∀ s, ((μ.map last) {s}).toReal = π s)
    (Q : Kernel S Y) [IsMarkovKernel Q]
    (future : Kernel X Y) [IsMarkovKernel future]
    (hfuture : ∀ (g : Y → ℝ), Measurable g →
      (∀ y, |g y| ≤ 1) → ∀ x,
      (∫ y, g y ∂future x) =
        ∑ s, markovIterate P (pointVector (last x)) gap s * (∫ y, g y ∂Q s))
    (ν : Measure (X × Y)) (hν : ν = μ ⊗ₘ future)
    (g : Y → ℝ) (hg : Measurable g) (hg_bound : ∀ y, |g y| ≤ 1) :
    (∫ z, g z.2 ∂ν) = ∑ s, π s * (∫ y, g y ∂Q s) := by
  -- The future kernel integral is measurable on `X`. Its finite fibers have
  -- masses determined by the outer singleton masses of `μ.map last`, even
  -- when the state singletons themselves are not measurable. The stationary
  -- identity then averages the finite Markov rows back to `π`.
  classical
  let ρ : Measure S := μ.map last
  have : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map hlast_meas.aemeasurable
  let q : S → ℝ := fun s => ∫ y, g y ∂Q s
  let v : S → ℝ := fun s =>
    ∑ t, markovIterate P (pointVector s) gap t * q t
  let F : X → ℝ := fun x => ∫ y, g y ∂future x
  have hF : Measurable F :=
    ((hg.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right').measurable
  have hFv (x : X) : F x = v (last x) := hfuture g hg hg_bound x
  have hbound (B : Set S) :
      μ.real (last ⁻¹' B) ≤ ∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s := by
    have hset : B = ⋃ s ∈ Finset.univ.filter (fun s => s ∈ B), ({s} : Set S) := by
      ext s
      simp
    calc
      μ.real (last ⁻¹' B) ≤ ρ.real B := by
        exact ENNReal.toReal_mono (measure_ne_top ρ B)
          (Measure.le_map_apply hlast_meas.aemeasurable B)
      _ = ρ.real (⋃ s ∈ Finset.univ.filter (fun s => s ∈ B), ({s} : Set S)) :=
        congrArg ρ.real hset
      _ ≤ ∑ s ∈ Finset.univ.filter (fun s => s ∈ B), ρ.real {s} :=
        measureReal_biUnion_finset_le _ _
      _ = ∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s := by
        simp [Measure.real, ρ, hlast]
  have hevent (B : Set S) (hB : MeasurableSet (last ⁻¹' B)) :
      μ.real (last ⁻¹' B) =
        ∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s := by
    have hc := hbound Bᶜ
    have hs : (∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s) +
        (∑ s ∈ Finset.univ.filter (fun s => s ∈ Bᶜ), π s) = 1 := by
      simpa only [Set.mem_compl_iff, Finset.sum_filter_add_sum_filter_not] using hπ.1.2
    have hm : μ.real (last ⁻¹' B) + μ.real (last ⁻¹' Bᶜ) = 1 := by
      simpa [Set.preimage_compl, probReal_univ] using
        (measureReal_add_measureReal_compl (μ := μ) hB)
    have ha := hbound B
    have hr : (∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s) ≤
        μ.real (last ⁻¹' B) := by
      calc
        (∑ s ∈ Finset.univ.filter (fun s => s ∈ B), π s) =
            1 - (∑ s ∈ Finset.univ.filter (fun s => s ∈ Bᶜ), π s) :=
          eq_sub_of_add_eq hs
        _ ≤ 1 - μ.real (last ⁻¹' Bᶜ) := by
          simpa only [Set.mem_compl_iff] using (sub_le_sub_left hc 1)
        _ = μ.real (last ⁻¹' B) := (eq_sub_of_add_eq hm).symm
    exact le_antisymm ha hr
  have hfr : (Set.range F).Finite :=
    (Set.finite_range v).subset (by
      rintro r ⟨x, rfl⟩
      exact ⟨last x, (hFv x).symm⟩)
  let sf : SimpleFunc X ℝ :=
    ⟨F, (fun r => hF (measurableSet_singleton r)), hfr⟩
  have hfi : Integrable (sf : X → ℝ) μ := sf.integrable_of_isFiniteMeasure
  have hfiber (r : ℝ) :
      μ.real (F ⁻¹' {r}) = ∑ s ∈ Finset.univ.filter (fun s => v s = r), π s := by
    have hpre : F ⁻¹' {r} = last ⁻¹' {s | v s = r} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, hFv]
    rw [hpre]
    simpa only [Set.mem_ofPred_eq] using
      hevent {s | v s = r} (by rw [← hpre]; exact hF (measurableSet_singleton r))
  have hmass : (∫ x, F x ∂μ) = ∑ s, π s * v s := by
    change (∫ x, sf x ∂μ) = _
    rw [← SimpleFunc.integral_eq_integral sf hfi]
    have hsubset : {r ∈ sf.range | r ≠ 0} ⊆ Finset.univ.image v := by
      intro r hr
      obtain ⟨x, hx⟩ := (SimpleFunc.mem_range.mp (Finset.mem_filter.mp hr).1)
      exact Finset.mem_image.mpr
        ⟨last x, Finset.mem_univ _, by simpa [sf] using (hFv x).symm.trans hx⟩
    rw [SimpleFunc.integral_eq_sum_of_subset hsubset]
    simp only [smul_eq_mul]
    simp_rw [show (sf : X → ℝ) = F from rfl, hfiber]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image v) (g := v) (f := fun s => π s * v s)
      (by intro s hs; exact Finset.mem_image_of_mem v hs)]
    congr 1
    ext r
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_filter.mp hs).2]
  have hmix : ∀ n t,
      (∑ s, π s * markovIterate P (pointVector s) n t) = π t := by
    intro n
    induction n with
    | zero =>
      intro t
      simp [markovIterate, pointVector]
    | succ n ih =>
      intro t
      simp only [markovIterate, markovStep, Matrix.vecMul_eq_sum,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ s, π s * ∑ u, markovIterate P (pointVector s) n u * P u t) =
            ∑ u, (∑ s, π s * markovIterate P (pointVector s) n u) * P u t := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          simp_rw [← mul_assoc, ← Finset.sum_mul]
        _ = ∑ u, π u * P u t := by simp_rw [ih]
        _ = π t := by
          have ht := congrFun hπ.2 t
          simpa [markovStep, Matrix.vecMul_eq_sum] using ht
  have hq : Measurable q :=
    ((hg.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right').measurable
  have hqmean := integral_finite_eq_sum_of_singleton_masses ρ π hπ.1.2
    (by simpa [ρ] using hlast) q hq
  calc
    (∫ z, g z.2 ∂ν) = ∫ x, F x ∂μ := by
      exact integral_compProd_bounded μ future ν hν _ (hg.comp measurable_snd) 1
        (fun z => hg_bound z.2)
    _ = ∑ s, π s * v s := hmass
    _ = ∑ t, π t * q t := by
      simp only [v]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      simp_rw [hmix]
    _ = ∫ s, q s ∂ρ := hqmean.symm
    _ = ∑ s, π s * (∫ y, g y ∂Q s) := hqmean

/-- Let [P be a row-stochastic transition matrix](hyp:P,hP) on a finite state space with
[stationary distribution π](hyp:π,hπ), and suppose [one step of P contracts the ℓ¹ distance
between probability vectors by a factor α](hyp:alpha,hcontract) with [0 ≤ α](hyp:halpha0)
[< 1](hyp:halpha1). Let [a past window be drawn from a probability law μ](hyp:μ) whose
[measurable last state](hyp:last,hlast_meas) [has distribution π](hyp:hlast), and let
[Q be a Markov kernel from states to future windows](hyp:Q) and [future a Markov kernel from past
to future windows](hyp:future) such that [for every past window x, the future kernel's mean of
every measurable function bounded by one equals its Q-mean averaged over the distribution reached
after gap steps](hyp:gap,hfuture) from the point mass at the last state of x. If [the joint law ν
is μ composed with the future kernel](hyp:ν,hν), [f is a measurable past score bounded in absolute
value by Cf](hyp:f,hf,Cf,hf_bound) and [g a measurable future score bounded in absolute value by
Cg](hyp:g,hg,Cg,hg_bound), then [the covariance of f and g under ν is at most 2·Cf·Cg·α^gap in
absolute value](goal). -/
theorem separated_window_covariance
    {S X Y : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Matrix S S ℝ) (π : S → ℝ) (alpha : ℝ)
    (hP : IsStochasticMatrix P) (hπ : IsStationary P π)
    (hcontract : ContractsL1 P alpha)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (gap : ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (last : X → S) (hlast_meas : Measurable last)
    (hlast : ∀ s, ((μ.map last) {s}).toReal = π s)
    (Q : Kernel S Y) [IsMarkovKernel Q]
    (future : Kernel X Y) [IsMarkovKernel future]
    (hfuture : ∀ (g : Y → ℝ), Measurable g →
      (∀ y, |g y| ≤ 1) → ∀ x,
      (∫ y, g y ∂future x) =
        ∑ s, markovIterate P (pointVector (last x)) gap s * (∫ y, g y ∂Q s))
    (ν : Measure (X × Y)) (hν : ν = μ ⊗ₘ future)
    (f : X → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hf_bound : ∀ x, |f x| ≤ Cf)
    (g : Y → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hg_bound : ∀ y, |g y| ≤ Cg) :
    |(∫ z, f z.1 * g z.2 ∂ν) -
        (∫ x, f x ∂μ) * (∫ z, g z.2 ∂ν)| ≤
      2 * Cf * Cg * alpha ^ gap := by
  -- Probability of `μ` supplies an `x : X`; Markovness of `future x` supplies
  -- a `y : Y`, so the pointwise bounds give `0 ≤ Cf` and `0 ≤ Cg`.
  -- If `Cg = 0`, then `g = 0` pointwise and the covariance vanishes.
  -- Otherwise apply `hfuture` and `stationary_future_window_mean` to
  -- `fun y => g y / Cg`, whose absolute value is at most one. Scale both
  -- identities back by `Cg`; `markov_row_score_bound` bounds the centered
  -- conditional mean pointwise with `v s = ∫ y, g y ∂Q s` and `Cv = Cg`.
  -- Finish with `covariance_compProd_of_centered_kernel_bound`, taking
  -- `D = 2 * Cg * alpha ^ gap`. No singleton measurability or positive
  -- history-atom probability is required.
  classical
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg _) (hf_bound x₀)
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure (future x₀)
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hg_bound y₀)
  by_cases hCg0 : Cg = 0
  · have hg0 : ∀ y, g y = 0 := by
      intro y
      have h := hg_bound y
      rw [hCg0] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simp [hg0, hCg0]
  have hCgpos : 0 < Cg := lt_of_le_of_ne hCg (Ne.symm hCg0)
  have hnorm_meas : Measurable (fun y => g y / Cg) := hg.div_const Cg
  have hnorm_bound : ∀ y, |g y / Cg| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hCgpos]
    exact (div_le_iff₀ hCgpos).2 (by simpa using hg_bound y)
  let v : S → ℝ := fun s => ∫ y, g y ∂Q s
  have hv : ∀ s, |v s| ≤ Cg := by
    intro s
    simpa only [v, Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := Q s) (f := g) (C := Cg)
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hg_bound y))
  have hscale (m : Measure Y) :
      Cg * (∫ y, g y / Cg ∂m) = ∫ y, g y ∂m := by
    rw [integral_div]
    exact mul_div_cancel₀ _ hCg0
  have hfuture_scaled (x : X) :
      (∫ y, g y ∂future x) =
        ∑ s, markovIterate P (pointVector (last x)) gap s * v s := by
    calc
      (∫ y, g y ∂future x) = Cg * (∫ y, g y / Cg ∂future x) :=
        (hscale (future x)).symm
      _ = Cg * ∑ s, markovIterate P (pointVector (last x)) gap s *
          (∫ y, g y / Cg ∂Q s) := by
        rw [hfuture (fun y => g y / Cg) hnorm_meas hnorm_bound x]
      _ = ∑ s, markovIterate P (pointVector (last x)) gap s * v s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [← mul_assoc, mul_comm Cg, mul_assoc, hscale (Q s)]
  have hmean : (∫ z, g z.2 ∂ν) = ∑ s, π s * v s := by
    calc
      (∫ z, g z.2 ∂ν) = Cg * (∫ z, g z.2 / Cg ∂ν) :=
        by rw [integral_div]; exact (mul_div_cancel₀ _ hCg0).symm
      _ = Cg * ∑ s, π s * (∫ y, g y / Cg ∂Q s) := by
        rw [stationary_future_window_mean P π hP hπ gap μ last hlast_meas
          hlast Q future hfuture ν hν (fun y => g y / Cg) hnorm_meas hnorm_bound]
      _ = ∑ s, π s * v s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [← mul_assoc, mul_comm Cg, mul_assoc, hscale (Q s)]
  have hkernel (x : X) :
      |(∫ y, g y ∂future x) - (∫ z, g z.2 ∂ν)| ≤
        2 * Cg * alpha ^ gap := by
    rw [hfuture_scaled x, hmean]
    exact markov_row_score_bound P π alpha hP hπ hcontract halpha0 halpha1
      gap (last x) v Cg hv
  have hD : 0 ≤ 2 * Cg * alpha ^ gap := by
    exact mul_nonneg (mul_nonneg (by norm_num) hCg) (pow_nonneg halpha0 _)
  convert covariance_compProd_of_centered_kernel_bound μ future ν hν f hf Cf hCf
    hf_bound g hg Cg hCg hg_bound (2 * Cg * alpha ^ gap) hD hkernel using 1
  ring

end Causalean.Mathlib.Probability.Kernel.FiniteHistory

