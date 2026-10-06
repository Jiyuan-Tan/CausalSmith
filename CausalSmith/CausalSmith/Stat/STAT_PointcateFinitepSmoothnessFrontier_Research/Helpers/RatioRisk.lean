module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperVariance

/-! Integrability and deterministic safeguards for the original-record risk assembly. -/
public section
set_option linter.style.whitespace false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Products of bounded measurable functions remain in L-infinity. -/
-- @node: risk_memLp_mul
lemma risk_memLp_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun x => f x * g x) ⊤ μ := hg.mul' hf

/-- Every finite clipped numerator and histogram denominator is integrable. -/
-- @node: upper_statistics_integrable
lemma upper_statistics_integrable (κ : Params) (n : ℕ) (μ : Measure (Dataset n))
    [IsFiniteMeasure μ] : Integrable (numeratorHat κ n) μ ∧ Integrable (denominatorHat κ n) μ := by
  have hb (i : Fin n) : MemLp (fun o : Dataset n => bit (A (o i))) ⊤ μ := by
    apply MemLp.of_bound ((by unfold A; fun_prop : Measurable (fun o : Dataset n => bit (A (o i)))).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun o => by simp [bit]; split <;> norm_num)
  have ht (i : Fin n) (t : ℝ) : MemLp (fun o : Dataset n => trunc t (Y (o i))) ⊤ μ := by
    apply MemLp.of_bound ((by unfold Y; fun_prop : Measurable (fun o : Dataset n => trunc t (Y (o i)))).aestronglyMeasurable) (max t 0)
    apply Filter.Eventually.of_forall
    intro o
    rw [Real.norm_eq_abs]
    unfold trunc
    split
    · exact le_trans ‹_› (le_max_left _ _)
    · simp only [abs_zero]
      exact le_max_right t 0
  have hp (i k : Fin n) (j : ℕ) :
      MemLp (fun o : Dataset n => projKernel (upperH κ n) j (X (o i)) (X (o k))) ⊤ μ := by
    apply MemLp.of_bound ((by unfold X; fun_prop : Measurable (fun o : Dataset n => projKernel (upperH κ n) j (X (o i)) (X (o k)))).aestronglyMeasurable) |(cellLen (upperH κ n) j)⁻¹|
    apply Filter.Eventually.of_forall
    intro o
    simp only [projKernel, Real.norm_eq_abs]
    split
    · exact le_rfl
    · simpa using abs_nonneg ((cellLen (upperH κ n) j)⁻¹)
  have hband (i k : Fin n) (j : ℕ) :
      MemLp (fun o : Dataset n => bandKernel (upperH κ n) j (X (o i)) (X (o k))) ⊤ μ :=
    (hp i k j).sub (hp i k (j-1))
  have hh (i k : Fin n) : MemLp (fun o : Dataset n =>
      heavyKernel (upperH κ n) (upperJ κ n) (upperT κ n) (o i) (o k)) ⊤ μ := by
    unfold heavyKernel
    change MemLp (fun o => (bit (A (o i)) * (upperH κ n)⁻¹) * _) ⊤ μ
    apply risk_memLp_mul ((hb i).mul_const _)
    apply (risk_memLp_mul (hp i k 0) (ht k (upperT κ n 0))).add
    apply memLp_finsetSum
    intro j hj
    exact risk_memLp_mul (hband i k (j.val+1)) (ht k (upperT κ n j.succ))
  have hw (i : Fin n) : MeasurableSet {o : Dataset n | X (o i) ∈ window (upperH κ n)} :=
    measurableSet_Icc.preimage (by unfold X; fun_prop)
  constructor
  · apply MemLp.integrable (q := ⊤) (by simp)
    unfold numeratorHat
    apply MemLp.sub
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro i hi
      exact (risk_memLp_mul (hb i) (ht i (upperT κ n 0))).indicator (hw i)
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro i hi
      apply memLp_finsetSum
      intro k hk
      exact hh i k
  · apply MemLp.integrable (q := ⊤) (by simp)
    unfold denominatorHat
    apply MemLp.sub
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro i hi
      exact (hb i).indicator (hw i)
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro i hi
      apply memLp_finsetSum
      intro k hk
      exact risk_memLp_mul (risk_memLp_mul (hb i) (hb k)) (hp i k (upperJ κ n))

/-- Clipping to the target range cannot increase absolute target error. -/
-- @node: clip_error_le
lemma clip_error_le (x θ : ℝ) (hθ : θ ∈ Icc (-1/2) (1/2)) :
    |clip x - θ| ≤ |x - θ| := by
  unfold clip
  rcases le_total x (1/2) with hx | hx
  · rw [min_eq_left hx]
    rcases le_total (-1/2 : ℝ) x with hl | hl
    · rw [max_eq_right hl]
    · rw [max_eq_left hl, abs_of_nonpos (by linarith [hθ.1]),
        abs_of_nonpos (by linarith [hθ.1])]
      linarith
  · rw [min_eq_right hx, max_eq_right (by norm_num),
      abs_of_nonneg (by linarith [hθ.2]), abs_of_nonneg (by linarith [hθ.2])]
    linarith

/-- The positive ratio branch and fallback share one pointwise error majorant. -/
-- @node: safeguarded_ratio_error
lemma safeguarded_ratio_error (N D N₀ D₀ θ : ℝ) (hD : 3/16 ≤ D₀)
    (hθ : θ ∈ Icc (-1/2) (1/2)) :
    |(if 3/32 ≤ D then clip (N/D) else 0) - θ| ≤
      (32/3 : ℝ) * (|N-N₀| + |N₀-θ*D₀| + |D-D₀|) := by
  split
  next hd =>
    have hdpos : 0 < D := by linarith
    have ht : |θ| ≤ 1/2 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
    have hid : N/D-θ = ((N-N₀)+(N₀-θ*D₀)+θ*(D₀-D))/D := by
      field_simp
      ring
    have hnum : |(N-N₀)+(N₀-θ*D₀)+θ*(D₀-D)| ≤
        |N-N₀|+|N₀-θ*D₀|+(1/2)*|D-D₀| := by
      have h := abs_add_le ((N-N₀)+(N₀-θ*D₀)) (θ*(D₀-D))
      rw [abs_mul, abs_sub_comm D₀ D] at h
      have hm := mul_le_mul_of_nonneg_right ht (abs_nonneg (D-D₀))
      linarith [abs_add_le (N-N₀) (N₀-θ*D₀)]
    apply (clip_error_le (N/D) θ hθ).trans
    rw [hid, abs_div, abs_of_pos hdpos]
    apply (div_le_iff₀ hdpos).mpr
    have he : 0 ≤ |N-N₀|+|N₀-θ*D₀|+|D-D₀| := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) he, abs_nonneg (D-D₀)]
  next hd =>
    have hab : (3/32 : ℝ) ≤ |D-D₀| := by
      have := le_abs_self (D₀-D)
      rw [abs_sub_comm D₀ D] at this
      linarith
    simp only [zero_sub, abs_neg]
    have ht : |θ| ≤ 1/2 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
    nlinarith [abs_nonneg (N-N₀), abs_nonneg (N₀-θ*D₀)]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
