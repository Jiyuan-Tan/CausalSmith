module
public import Causalean.Stat.EmpiricalProcess.Countable.TailMoment
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# The fourth-moment Doob bridge

Mathlib's stopped-event weak maximal inequality combines with the mixed-moment
layer-cake bridge and Holder at orders 4/3 and 4 to give the final martingale
estimate with constant (4/3)^4 = 256/81.
Reference: Fabrice Baudoin, "Lecture 11. Doob's martingale maximal inequalities",
https://fabricebaudoin.blog/2012/04/10/lecture-11-doobs-martingale-maximal-inequalities/
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- If [a real process f is a submartingale for a filtration under a
probability measure μ](hyp:μ,f,hf) and [its values at every time up to a
horizon N](hyp:N) [have integrable fourth powers](hyp:h4), then [the
running maximum of f over times 0 through N is measurable and has an
integrable fourth power](goal). -/
theorem submartingale_max_fourth_legal {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Submartingale f ℱ μ) (N : ℕ)
    (h4 : ∀ k ≤ N, Integrable (fun x => f k x ^ 4) μ) :
    Measurable (fun x => ⨆ k : Fin (N + 1), f k x) ∧
      Integrable (fun x => (⨆ k : Fin (N + 1), f k x)^4) μ := by
  have hm (k : ℕ) : Measurable (f k) :=
    (hf.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl
  refine ⟨Measurable.iSup (fun k : Fin (N + 1) => hm k), ?_⟩
  exact (finite_iSup_fourth_integrable μ (fun k : Fin (N + 1) => f k)
    (fun k => (hm k).aestronglyMeasurable)
    (fun k => h4 k (Nat.le_of_lt_succ k.isLt))).2

/-- If [a real process f is a submartingale for a filtration under a
probability measure μ](hyp:μ,f,hf) and [is nonnegative everywhere](hyp:hpos),
then for [any horizon N](hyp:N) and [any positive level t](hyp:t,ht), [t
times the probability that the maximum of f over times 0 through N is at
least t is at most the integral of the terminal value f_N over that
event](goal). -/
theorem submartingale_max_tail_le {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Submartingale f ℱ μ)
    (hpos : ∀ k x, 0 ≤ f k x) (N : ℕ) (t : ℝ) (ht : 0 < t) :
    t * μ.real {x | t ≤ ⨆ k : Fin (N + 1), f k x} ≤
      ∫ x in {x | t ≤ ⨆ k : Fin (N + 1), f k x}, f N x ∂μ := by
  have hsup (x : Ω) :
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => f k x) =
        ⨆ k : Fin (N + 1), f k x := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      exact le_ciSup (Finite.bddAbove_range (fun k : Fin (N + 1) => f k x))
        (⟨k, Finset.mem_range.mp hk⟩ : Fin (N + 1))
    · apply ciSup_le
      intro k
      exact Finset.le_sup' (f := fun k => f k x) (Finset.mem_range.mpr k.isLt)
  have hw := maximal_ineq hf (show 0 ≤ f from hpos) (ε := ⟨t, ht.le⟩) N
  simp_rw [hsup] at hw
  have hreal := ENNReal.toReal_mono (by finiteness) hw
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg (hpos N))] at hreal
  change t * μ.real {x | t ≤ ⨆ k : Fin (N + 1), f k x} ≤
    ∫ x in {x | t ≤ ⨆ k : Fin (N + 1), f k x}, f N x ∂μ at hreal
  exact hreal

/-- If [a real process f is a submartingale for a filtration under a
probability measure μ](hyp:μ,f,hf), [is nonnegative everywhere](hyp:hpos),
and [has integrable fourth powers at every time up to a horizon
N](hyp:N,h4), then [the fourth power of its maximum over times 0 through N
is integrable, with expectation at most 4/3 times the expectation of the
cube of that maximum times the terminal value f_N](goal).

The proof integrates the weak Doob inequality against the cubic
layer-cake weight.
-/
theorem doob_fourth_mixed {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Submartingale f ℱ μ)
    (hpos : ∀ k x, 0 ≤ f k x) (N : ℕ)
    (h4 : ∀ k ≤ N, Integrable (fun x => f k x ^ 4) μ) :
    Integrable (fun x => (⨆ k : Fin (N + 1), f k x)^4) μ ∧
    (∫ x, (⨆ k : Fin (N + 1), f k x)^4 ∂μ) ≤
      (4 / 3 : ℝ) * ∫ x, (⨆ k : Fin (N + 1), f k x)^3 * f N x ∂μ := by
  obtain ⟨hm, hi⟩ := submartingale_max_fourth_legal μ ℱ f hf N h4
  have hmax (x : Ω) : 0 ≤ ⨆ k : Fin (N + 1), f k x :=
    (hpos 0 x).trans (le_ciSup (Finite.bddAbove_range (fun k : Fin (N + 1) => f k x))
      (0 : Fin (N + 1)))
  refine ⟨hi, weak_fourth_mixed μ _ (f N) hmax (hpos N) hm
    ((hf.stronglyMeasurable N).mono (ℱ.le N)).aestronglyMeasurable hi
    (h4 N le_rfl) ?_⟩
  exact fun t ht => submartingale_max_tail_le μ ℱ f hf hpos N t ht

/-- If [a real discrete-time process f is a martingale for a filtration
under a probability measure μ](hyp:μ,f,hf) and [has integrable fourth powers
at every time up to a horizon N](hyp:N,h4), then [the fourth power of its
maximal absolute value over times 0 through N is integrable, with
expectation at most 256/81 times the expected fourth power of the terminal
value f_N](goal). -/
theorem doob_fourth_maximal {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ) (N : ℕ)
    (h4 : ∀ k ≤ N, Integrable (fun x => f k x ^ 4) μ) :
    Integrable (fun x => (⨆ k : Fin (N + 1), |f k x|)^4) μ ∧
    (∫ x, (⨆ k : Fin (N + 1), |f k x|)^4 ∂μ) ≤
      (256 / 81 : ℝ) * ∫ x, f N x ^ 4 ∂μ := by
  have habs : Submartingale (fun k x => |f k x|) ℱ μ := by
    have heq : (fun k x => |f k x|) = f ⊔ -f := by
      ext k x
      exact abs_eq_max_neg
    rw [heq]
    exact hf.submartingale.sup hf.neg.submartingale
  have h4abs (k : ℕ) (hk : k ≤ N) : Integrable (fun x => |f k x| ^ 4) μ := by
    have heq : (fun x => |f k x| ^ 4) = (fun x => f k x ^ 4) := by
      funext x
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [heq]
    exact h4 k hk
  obtain ⟨hi, hmix⟩ := doob_fourth_mixed μ ℱ _ habs (fun k x => abs_nonneg _) N h4abs
  let A : Ω → ℝ := fun x => ⨆ k : Fin (N + 1), |f k x|
  have hA (x : Ω) : 0 ≤ A x :=
    (abs_nonneg (f 0 x)).trans
      (le_ciSup (Finite.bddAbove_range (fun k : Fin (N + 1) => |f k x|))
        (0 : Fin (N + 1)))
  have hAm : Measurable A := (submartingale_max_fourth_legal μ ℱ _ habs N h4abs).1
  have hBm : AEStronglyMeasurable (fun x => |f N x|) μ :=
    ((hf.stronglyMeasurable N).mono (ℱ.le N)).aestronglyMeasurable.norm
  obtain ⟨_, hholder⟩ := fourth_moment_holder μ A (fun x => |f N x|) hA
    (fun x => abs_nonneg _) hi (h4abs N le_rfl) hAm.aestronglyMeasurable hBm
  have hterminal : (∫ x, |f N x| ^ 4 ∂μ) = ∫ x, f N x ^ 4 ∂μ := by
    congr 1
    funext x
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [hterminal] at hholder
  refine ⟨hi, ?_⟩
  let M : ℝ := ∫ x, A x ^ 4 ∂μ
  let H : ℝ := ∫ x, A x ^ 3 * |f N x| ∂μ
  let T : ℝ := ∫ x, f N x ^ 4 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun x => by positivity
  have hH : 0 ≤ H := integral_nonneg fun x => mul_nonneg (pow_nonneg (hA x) _) (abs_nonneg _)
  have hT : 0 ≤ T := integral_nonneg fun x => by positivity
  change M ≤ (256 / 81 : ℝ) * T
  change M ≤ (4 / 3 : ℝ) * H at hmix
  change H ^ 4 ≤ M ^ 3 * T at hholder
  by_cases hzero : M = 0
  · rw [hzero]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    have hp := pow_le_pow_left₀ hM hmix 4
    have hc : M ^ 3 * M ≤ M ^ 3 * ((256 / 81 : ℝ) * T) := by
      nlinarith only [hp, hholder]
    exact le_of_mul_le_mul_left hc (pow_pos hMpos 3)

end Causalean.Stat.EmpiricalProcess.Countable
