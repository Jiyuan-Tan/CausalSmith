module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaLegalityBasics
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.SmoothedTentSmoothness
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentIntegrals

/-! Exact squared-frame cell integrals, trapezoidal quadrature, and paired-grid centering. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The two squared frame profiles each have integral one half over a normalized cell. [This is the stated conclusion](goal). -/
-- @node: squared_frame_profile_integrals
lemma squared_frame_profile_integrals :
    (∫ t in (0:ℝ)..1, Real.cos (Real.pi*t/2)^2) = 1/2 ∧
    (∫ t in (0:ℝ)..1, Real.sin (Real.pi*t/2)^2) = 1/2 := by
  have hp : Real.pi/2 ≠ 0 := by positivity
  have he (t : ℝ) : Real.pi*t/2 = (Real.pi/2)*t := by ring
  simp_rw [he]
  constructor
  · rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x^2) hp, integral_cos_sq]
    simp only [mul_zero, mul_one, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.cos_zero, Real.sin_zero, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    ring
  · rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x^2) hp, integral_sin_sq]
    simp only [mul_zero, mul_one, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.cos_zero, Real.sin_zero, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    ring

/-- Integrating a squared-frame interpolation gives the average of its endpoint values. [This is the stated conclusion](goal). -/
-- @node: squared_frame_interpolation_integral
lemma squared_frame_interpolation_integral (g h : ℝ) :
    (∫ t in (0:ℝ)..1,
      g*Real.cos (Real.pi*t/2)^2+h*Real.sin (Real.pi*t/2)^2) = (g+h)/2 := by
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    squared_frame_profile_integrals.1, squared_frame_profile_integrals.2]
  ring

/-- The fine-cell change of variables contributes exactly its inverse-rank width. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: squared_frame_cell_integral
lemma squared_frame_cell_integral (K j : ℕ) (hK : 0 < K) (g h : ℝ) :
    (∫ x in (j:ℝ)/K..((j:ℝ)+1)/K,
      g*Real.cos (Real.pi*((K:ℝ)*x-j)/2)^2+
        h*Real.sin (Real.pi*((K:ℝ)*x-j)/2)^2) = (g+h)/(2*K) := by
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  rw [intervalIntegral.integral_comp_mul_sub
    (fun t => g*Real.cos (Real.pi*t/2)^2+h*Real.sin (Real.pi*t/2)^2) hk]
  rw [show (K:ℝ)*((j:ℝ)/K)-j = 0 by field_simp; ring,
    show (K:ℝ)*(((j:ℝ)+1)/K)-j = 1 by field_simp; ring,
    squared_frame_interpolation_integral, smul_eq_mul]
  field_simp

/-- On every fine cell the smoothed tent integrates to its endpoint trapezoid. This statement assumes [the hK condition](hyp:hK), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_cell_integral
lemma smoothedTent_cell_integral (K M j : ℕ) (hK : 0 < K) (hj : j < K)
    (σ : Fin (M / 2) → Bool) :
    (∫ x in (j:ℝ)/K..((j:ℝ)+1)/K, smoothedTent K M σ x) =
      (coarseTent M σ ((j:ℝ)/K)+coarseTent M σ (((j:ℝ)+1)/K))/(2*K) := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hle : (j:ℝ)/K ≤ ((j:ℝ)+1)/K := by apply div_le_div_of_nonneg_right _ hk.le; linarith
  calc
    _ = ∫ x in (j:ℝ)/K..((j:ℝ)+1)/K,
        coarseTent M σ ((j:ℝ)/K)*Real.cos (Real.pi*((K:ℝ)*x-j)/2)^2+
          coarseTent M σ (((j:ℝ)+1)/K)*Real.sin (Real.pi*((K:ℝ)*x-j)/2)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc ((j:ℝ)/K) (((j:ℝ)+1)/K) := by simpa [uIcc_of_le hle] using hx
      have hx0 : 0 ≤ x := le_trans (by positivity) hx'.1
      have hx1 : x ≤ 1 := hx'.2.trans (by
        apply (div_le_iff₀ hk).mpr
        have : (j:ℝ)+1 ≤ K := by exact_mod_cast hj
        linarith)
      exact smoothedTent_cell_formula K M hK σ j hj ⟨x, hx0, hx1⟩
        (by simpa [mul_comm] using (div_le_iff₀ hk).mp hx'.1)
        (by simpa [mul_comm] using (le_div_iff₀ hk).mp hx'.2)
    _ = _ := squared_frame_cell_integral K j hK _ _

/-- The squared-frame tent is continuous on the full closed design interval. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: continuousOn_smoothedTent
lemma continuousOn_smoothedTent (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M / 2) → Bool) : ContinuousOn (smoothedTent K M σ) (Icc 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : unitInterval => smoothedTent K M σ x)
  unfold smoothedTent
  fun_prop

/-- Summing the exact fine-cell integrals gives the full trapezoidal quadrature formula. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_integral_trapezoidal
lemma smoothedTent_integral_trapezoidal (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M / 2) → Bool) :
    (∫ x : unitInterval, smoothedTent K M σ x ∂design) =
      ∑ j ∈ Finset.range K,
        (coarseTent M σ ((j:ℝ)/K)+coarseTent M σ (((j:ℝ)+1)/K))/(2*K) := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hint (j : ℕ) (hj : j < K) :
      IntervalIntegrable (smoothedTent K M σ) volume ((j:ℝ)/K) (((j+1:ℕ):ℝ)/K) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_smoothedTent K M hK σ).mono
    rw [uIcc_of_le (by apply div_le_div_of_nonneg_right _ hk.le; exact_mod_cast Nat.le_succ j)]
    intro x hx
    constructor
    · exact le_trans (by positivity) hx.1
    · apply hx.2.trans
      apply (div_le_iff₀ hk).mpr
      have : ((j+1:ℕ):ℝ) ≤ K := by exact_mod_cast hj
      linarith
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j:ℝ)/K) hint
  simp only [Nat.cast_zero, zero_div, div_self hk.ne'] at hs
  rw [integral_design_eq_interval, ← hs]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_add, Nat.cast_one]
  exact smoothedTent_cell_integral K M j hK (Finset.mem_range.mp hj) σ

/-- Translating a full compact tent by an integer number of fine cells preserves its sample sum. This statement assumes [the hr condition](hyp:hr), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: tentBase_grid_sum_translate
lemma tentBase_grid_sum_translate (K r c : ℕ) (hr : 0 < r) (hc : c + r ≤ K) :
    (∑ i ∈ Finset.range (K+1), tentBase (((i:ℝ)-c)/r)) =
      ∑ t ∈ Finset.range (r+1), tentBase ((t:ℝ)/r) := by
  have hrr : (0:ℝ) < r := by exact_mod_cast hr
  have hsub : Finset.Ico c (c+r+1) ⊆ Finset.range (K+1) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  have hz (i : ℕ) (hi : i ∈ Finset.range (K+1)) (hni : i ∉ Finset.Ico c (c+r+1)) :
      tentBase (((i:ℝ)-c)/r) = 0 := by
    apply tentBase_zero_outside
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hni
    rcases hni with hi | hi
    · left
      apply div_nonpos_of_nonpos_of_nonneg _ hrr.le
      have : (i:ℝ) < c := by exact_mod_cast hi
      linarith
    · right
      apply (le_div_iff₀ hrr).mpr
      have : (c:ℝ)+(r:ℝ)+1 ≤ i := by exact_mod_cast hi
      linarith
  rw [← Finset.sum_subset hsub hz]
  symm
  apply Finset.sum_bij (fun t _ => c+t)
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_Ico]
    omega
  · intro t ht s hs he
    omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    exact ⟨i-c, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro t ht
    push_cast
    congr 1
    ring

/-- Every coarse tent has the same sample sum when the fine grid is an integer refinement. This statement assumes [the hM condition](hyp:hM), [the hr condition](hyp:hr), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: scaled_tent_grid_sum
lemma scaled_tent_grid_sum (M r m : ℕ) (hM : 0 < M) (hr : 0 < r) (hm : m < M) :
    (∑ i ∈ Finset.range (M*r+1), tentBase ((M:ℝ)*((i:ℝ)/(M*r))-m)) =
      ∑ t ∈ Finset.range (r+1), tentBase ((t:ℝ)/r) := by
  have hmr : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have he (i : ℕ) : (M:ℝ)*((i:ℝ)/(M*r))-m = ((i:ℝ)-(m*r:ℕ))/r := by
    push_cast
    field_simp
  simp_rw [he]
  apply tentBase_grid_sum_translate (M*r) r (m*r) hr
  nlinarith

/-- Adjacent opposite coarse tents cancel exactly in the full fine-grid sample sum. This statement assumes [the hM condition](hyp:hM), [the hr condition](hyp:hr), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: coarseTent_grid_sum_zero
lemma coarseTent_grid_sum_zero (M r : ℕ) (hM : 0 < M) (hr : 0 < r)
    (heven : 2 * (M / 2) = M) (σ : Fin (M / 2) → Bool) :
    (∑ i ∈ Finset.range (M*r+1), coarseTent M σ ((i:ℝ)/(M*r))) = 0 := by
  unfold coarseTent
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hidx : 2*j.val < M ∧ 2*j.val+1 < M := by omega
  have h0 := scaled_tent_grid_sum M r (2*j.val) hM hr hidx.1
  have h1 := scaled_tent_grid_sum M r (2*j.val+1) hM hr hidx.2
  push_cast at h0 h1
  rw [h0, h1, sub_self, mul_zero]

/-- Both endpoints of the paired field vanish, independently of signs and parity. [This is the stated conclusion](goal). -/
-- @node: coarseTent_endpoints_zero
lemma coarseTent_endpoints_zero (M : ℕ) (σ : Fin (M / 2) → Bool) :
    coarseTent M σ 0 = 0 ∧ coarseTent M σ 1 = 0 := by
  constructor <;> unfold coarseTent <;> apply Finset.sum_eq_zero <;> intro j _
  · have h0 := tentBase_zero_outside (-(2*(j.val:ℝ)))
      (Or.inl (by nlinarith [(Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val)]))
    have h1 := tentBase_zero_outside (-(2*(j.val:ℝ)+1))
      (Or.inl (by nlinarith [(Nat.cast_nonneg j.val : (0:ℝ) ≤ j.val)]))
    simp only [mul_zero, zero_sub, h0, h1, sub_self, mul_zero]
  · have hj : 2*j.val+2 ≤ M := by have := j.isLt; omega
    have hjr : 2*(j.val:ℝ)+2 ≤ M := by exact_mod_cast hj
    have h0 := tentBase_zero_outside ((M:ℝ)-2*j.val) (Or.inr (by linarith))
    have h1 := tentBase_zero_outside ((M:ℝ)-(2*j.val+1)) (Or.inr (by linarith))
    simp only [mul_one, h0, h1, sub_self, mul_zero]

/-- Exact cancellation of the paired grid sum centers the squared-frame interpolation. This statement assumes [the hM condition](hyp:hM), [the hr condition](hyp:hr), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_integral_zero_of_refinement
lemma smoothedTent_integral_zero_of_refinement (M r : ℕ) (hM : 0 < M) (hr : 0 < r)
    (heven : 2 * (M / 2) = M) (σ : Fin (M / 2) → Bool) :
    (∫ x : unitInterval, smoothedTent (M*r) M σ x ∂design) = 0 := by
  let K := M*r
  let g : ℕ → ℝ := fun i => coarseTent M σ ((i:ℝ)/K)
  have hK : 0 < K := Nat.mul_pos hM hr
  have hsum : (∑ i ∈ Finset.range (K+1), g i) = 0 := by
    simpa only [g, K, Nat.cast_mul] using coarseTent_grid_sum_zero M r hM hr heven σ
  have hg0 : g 0 = 0 := by
    dsimp [g]
    simpa using (coarseTent_endpoints_zero M σ).1
  have hgK : g K = 0 := by
    dsimp [g]
    rw [div_self (by exact_mod_cast (Nat.ne_of_gt hK))]
    exact (coarseTent_endpoints_zero M σ).2
  have hleft : (∑ i ∈ Finset.range K, g i) = 0 := by
    rw [Finset.sum_range_succ, hgK, add_zero] at hsum
    exact hsum
  have hright : (∑ i ∈ Finset.range K, g (i+1)) = 0 := by
    rw [Finset.sum_range_succ', hg0, add_zero] at hsum
    exact hsum
  rw [smoothedTent_integral_trapezoidal K M hK σ]
  have he : (∑ i ∈ Finset.range K, (g i+g (i+1))/(2*K)) = 0 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hleft, hright, add_zero, zero_div]
  simpa only [g, Nat.cast_add, Nat.cast_one] using he

/-- Dyadic legality ranks provide an even coarse rank and an integer fine-grid refinement. This statement assumes [the hranks condition](hyp:hranks). [This is the stated conclusion](goal). -/
-- @node: legalityRanks_refinement
lemma legalityRanks_refinement (v : Params) (K M : ℕ) (hranks : LegalityRanks v K M) :
    0 < M ∧ 2 * (M / 2) = M ∧ ∃ r : ℕ, 0 < r ∧ K = M*r := by
  have hM : 0 < M := by have := hranks.2.2.2.1; omega
  have hK : 0 < K := by have := hranks.2.2.1; omega
  obtain ⟨k, hk⟩ := hranks.1
  obtain ⟨m, hm⟩ := hranks.2.1
  have hmk : m ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hm, ← hk]
    have := hranks.2.2.1
    omega
  have hdiv : M ∣ K := by
    rw [hm, hk]
    exact Nat.pow_dvd_pow 2 hmk
  have heven : 2 * (M / 2) = M := by
    have hmpos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      have hge := hranks.2.2.2.1
      simp [hm, hm0] at hge
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    rw [hm, pow_succ]
    omega
  obtain ⟨r, hkr⟩ := hdiv
  refine ⟨hM, heven, r, ?_, hkr⟩
  by_contra h
  have hr0 : r = 0 := by omega
  simp [hkr, hr0] at hK

/-- Legal dyadic ranks give an exactly centered interpolated paired tent. This statement assumes [the hranks condition](hyp:hranks). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_integral_zero_of_legalityRanks
lemma smoothedTent_integral_zero_of_legalityRanks (v : Params) (K M : ℕ)
    (hranks : LegalityRanks v K M) (σ : Fin (M / 2) → Bool) :
    (∫ x : unitInterval, smoothedTent K M σ x ∂design) = 0 := by
  obtain ⟨hM, heven, r, hr, hkr⟩ := legalityRanks_refinement v K M hranks
  rw [hkr]
  exact smoothedTent_integral_zero_of_refinement M r hM hr heven σ

end CausalSmith.Stat.FinitepHomogeneityDensegamma
