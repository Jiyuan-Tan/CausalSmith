module
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteAverage
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Martingale.Basic

/-!
# The finite sign experiment and its reveal martingale

The uniform probability law on Boolean sign vectors represents the exact
finite sign average. Mathlib's piFinset filtration reveals the first k signs.
Signed partial sums, held constant after all signs are revealed, form a real
martingale. The measure conversion, adaptedness, and zero conditional
increment are isolated before the Doob application in FiniteSigns.

Reuse leads: PMF.uniformOfFintype, Filtration.piFinset, and
martingale_of_condExp_sub_eq_zero_nat. Causalean's design-based
prefixCondExp_ae_eq_condExp is an alternative finite-conditioning bridge.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- [The signed prefix](goal) of [a coefficient vector a](hyp:a) under [a
sign vector σ](hyp:σ) at [time k between 0 and n](hyp:k) is [the signed sum
of the first k coefficients, Σ_(j < k) σ_j a_j](step:1); it is zero at time
zero and the full signed sum at time n. -/
def signedPrefix {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) (k : Fin (n + 1)) : ℝ :=
  ∑ j : Fin n, if j.val < k.val then (if σ j then (1 : ℝ) else -1) * a j else 0

/-- [The signed prefix maximum](goal) of [a coefficient vector
a](hyp:a) under [a sign vector σ](hyp:σ) is [the largest absolute signed
prefix over times 0 through n](step:1), including both the empty prefix and
the full sum. -/
def signedPrefixMax {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ⨆ k : Fin (n + 1), |signedPrefix a σ k|

/-- [The sign law](goal) for [length n](hyp:n) is [the uniform
probability law on all Boolean sign vectors of length n](step:1),
including the single empty vector when n is zero. -/
def signLaw (n : ℕ) : Measure (Fin n → Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).toMeasure

/-- [The uniform sign law](goal) of [any length n](hyp:n) is a
probability measure. -/
instance signLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (signLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Fin n → Bool)).toMeasure)

/-- [Every real function of sign vectors](hyp:H) [is integrable under the
sign law, and its integral equals its uniform sign average](goal). -/
theorem signLaw_integral {n : ℕ} (H : (Fin n → Bool) → ℝ) :
    Integrable H (signLaw n) ∧ (∫ σ, H σ ∂signLaw n) = signAverage H := by
  classical
  have hH : Integrable H (signLaw n) := Integrable.of_finite
  refine ⟨hH, ?_⟩
  rw [integral_fintype hH]
  simp only [signLaw, measureReal_def, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul, signAverage, div_eq_mul_inv]
  rw [← Finset.mul_sum, mul_comm]
  simp

/-- [The signed prefix process](goal) of [a coefficient vector a](hyp:a)
at [a natural time k](hyp:k) under [a sign vector σ](hyp:σ) is [the signed
sum Σ_(j < k) σ_j a_j of the coefficients with index below k](step:1); it
stays constant from time n onward. -/
def signedPrefixProcess {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (σ : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if j.val < k then (if σ j then (1 : ℝ) else -1) * a j else 0

/-- [At every time between 0 and n the signed prefix process agrees with
the signed prefix](goal). -/
theorem signedPrefixProcess_eq {n : ℕ} (a : Fin n → ℝ)
    (k : Fin (n + 1)) (σ : Fin n → Bool) :
    signedPrefixProcess a k σ = signedPrefix a σ k := rfl

/-- [At time n the signed prefix process equals the full signed
sum](goal). -/
theorem signedPrefixProcess_terminal {n : ℕ} (a : Fin n → ℝ) (σ : Fin n → Bool) :
    signedPrefixProcess a n σ = ∑ j, (if σ j then (1 : ℝ) else -1) * a j := by
  simp only [signedPrefixProcess, Fin.is_lt, ite_true]

/-- [The sign reveal filtration](goal) on sign vectors of [length
n](hyp:n) is the filtration whose information at time k consists exactly of
the signs with index below k. -/
def signRevealFiltration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → Bool)) where
  seq k := Filtration.piFinset (X := fun _ : Fin n => Bool)
    (Finset.univ.filter (fun j => j.val < k))
  mono' := by
    intro k l hkl
    apply (Filtration.piFinset (X := fun _ : Fin n => Bool)).mono
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, lt_of_lt_of_le hj.2 hkl⟩
  le' k := Filtration.le _ _

/-- For [any coefficient vector](hyp:a), [the signed prefix process is
adapted to the sign reveal filtration](goal). -/
theorem signedPrefixProcess_stronglyAdapted {n : ℕ} (a : Fin n → ℝ) :
    StronglyAdapted (signRevealFiltration n) (signedPrefixProcess a) := by
  classical
  intro k
  unfold signedPrefixProcess
  apply Finset.stronglyMeasurable_fun_sum
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
    let s := Finset.univ.filter (fun j : Fin n => j.val < k)
    have hmem : j ∈ s := by simp [s, hj]
    have hev : Measurable[(signRevealFiltration n) k] (fun σ : Fin n → Bool => σ j) :=
      (measurable_pi_apply (⟨j, hmem⟩ : s)).comp (comap_measurable s.restrict)
    exact ((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      hev).stronglyMeasurable.mul_const (a j)
  · simp only [hj, ite_false]
    exact stronglyMeasurable_const

/-- For [any coefficient vector](hyp:a) and [any time k](hyp:k), [the
increment of the signed prefix process from time k to k + 1 has
conditional expectation zero, almost surely under the sign law, given the
signs revealed by time k](goal), also after the terminal time. -/
theorem signedPrefixProcess_condExp_increment {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    (signLaw n)[signedPrefixProcess a (k + 1) - signedPrefixProcess a k |
      (signRevealFiltration n) k] =ᵐ[signLaw n] 0 := by
  classical
  by_cases hk : k < n
  · let i : Fin n := ⟨k, hk⟩
    let f : (Fin n → Bool) → ℝ := fun σ => (if σ i then 1 else -1) * a i
    have hinc : signedPrefixProcess a (k + 1) - signedPrefixProcess a k = f := by
      funext σ
      change (∑ j : Fin n, if j.val < k + 1 then
        (if σ j then (1 : ℝ) else -1) * a j else 0) -
        (∑ j : Fin n, if j.val < k then
        (if σ j then (1 : ℝ) else -1) * a j else 0) = f σ
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · simp [i, f]
      · intro j _ hji
        have hjk : j.val ≠ k := fun h => hji (Fin.ext h)
        by_cases hj : j.val < k
        · simp [hj, Nat.lt_succ_of_lt hj]
        · have hj' : ¬j.val < k + 1 := by omega
          simp [hj, hj']
      · simp
    rw [hinc]
    let flip : (Fin n → Bool) → (Fin n → Bool) :=
      fun σ j => if j = i then !(σ j) else σ j
    have hflip : Function.Involutive flip := by
      intro σ
      funext j
      by_cases hj : j = i <;> simp [flip, hj]
    let e := hflip.toPerm flip
    have hm := (signRevealFiltration n).le k
    apply (ae_eq_condExp_of_forall_setIntegral_eq hm
      (signLaw_integral f).1 (fun _ _ _ => integrable_zero _ _ _) ?_
      stronglyMeasurable_zero.aestronglyMeasurable).symm
    intro s hs _
    have hmem : ∀ σ, flip σ ∈ s ↔ σ ∈ s := by
      change MeasurableSet[MeasurableSpace.pi.comap
        (Finset.univ.filter (fun j : Fin n => j.val < k)).restrict] s at hs
      obtain ⟨t, _, rfl⟩ := hs
      intro σ
      have heq : (Finset.univ.filter (fun j : Fin n => j.val < k)).restrict
          (flip σ) = (Finset.univ.filter (fun j : Fin n => j.val < k)).restrict σ := by
        funext j
        have hj : j.val ≠ i := by
          intro h
          have hjlt := (Finset.mem_filter.mp j.property).2
          simp [h, i] at hjlt
        simp [Finset.restrict, flip, hj]
      change (_ ∈ t ↔ _ ∈ t)
      rw [heq]
    have hneg : ∀ σ, s.indicator f (e σ) = -s.indicator f σ := by
      intro σ
      have hf : f (flip σ) = -f σ := by
        simp only [f, flip, ite_true]
        cases σ i <;> simp
      by_cases hσ : σ ∈ s
      · change s.indicator f (flip σ) = -s.indicator f σ
        simp only [Set.indicator_of_mem hσ, Set.indicator_of_mem ((hmem σ).2 hσ)]
        exact hf
      · have hσ' : flip σ ∉ s := fun h => hσ ((hmem σ).1 h)
        simp [show e σ = flip σ from rfl, hσ, hσ']
    have hsum : ∑ σ, s.indicator f σ = 0 := by
      have he := Equiv.sum_comp e (s.indicator f)
      simp only [hneg, Finset.sum_neg_distrib] at he
      linarith
    simp only [Pi.zero_apply, integral_zero]
    rw [← integral_indicator (hm s hs),
      (signLaw_integral (s.indicator f)).2]
    simp [signAverage, hsum]
  · have hinc : signedPrefixProcess a (k + 1) - signedPrefixProcess a k = 0 := by
      funext σ
      have hj : ∀ j : Fin n, j.val < k := fun j => lt_of_lt_of_le j.is_lt (by omega)
      simp [signedPrefixProcess, hj, fun j => Nat.lt_succ_of_lt (hj j)]
    rw [hinc, condExp_zero]

/-- For [any coefficient vector](hyp:a), [the signed prefix process is a
martingale for the sign reveal filtration under the uniform sign
law](goal). -/
theorem signedPrefixProcess_martingale {n : ℕ} (a : Fin n → ℝ) :
    Martingale (signedPrefixProcess a) (signRevealFiltration n) (signLaw n) := by
  exact martingale_of_condExp_sub_eq_zero_nat
    (signedPrefixProcess_stronglyAdapted a)
    (fun k => (signLaw_integral (signedPrefixProcess a k)).1)
    (signedPrefixProcess_condExp_increment a)

end Causalean.Stat.EmpiricalProcess.Countable
