module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.RateConsistency

/-!
# Transfer of numerical rates to value sequences

Positive uniform rate comparisons transfer consistency, parametric comparability,
and the growing-dimension elbow to risk and honest length.
-/

public section
noncomputable section
open scoped Topology
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Eventual comparison by positive constants is symmetric](goal). -/
-- @node: comparable_symm
lemma comparable_symm {f g : ℕ → ℝ} (h : Comparable f g) : Comparable g f := by
  obtain ⟨c, C, hc, hcC, he⟩ := h
  have hC : 0 < C := hc.trans_le hcC
  refine ⟨C⁻¹, c⁻¹, inv_pos.mpr hC, inv_le_inv₀ hC hc |>.mpr hcC, ?_⟩
  filter_upwards [he] with k hk
  constructor
  · exact (inv_mul_le_iff₀ hC).mpr (by simpa [mul_comm] using hk.2)
  · exact (le_inv_mul_iff₀ hc).mpr (by simpa [mul_comm] using hk.1)

/-- Assume [the stated hfg condition](hyp:hfg) and [the stated hgh condition](hyp:hgh). [Eventual comparison by positive constants is transitive](goal). -/
-- @node: comparable_trans
lemma comparable_trans {f g h : ℕ → ℝ} (hfg : Comparable f g)
    (hgh : Comparable g h) : Comparable f h := by
  obtain ⟨c, C, hc, hcC, he⟩ := hfg
  obtain ⟨a, A, ha, haA, he'⟩ := hgh
  have hC := hc.trans_le hcC
  refine ⟨c*a, C*A, mul_pos hc ha,
    mul_le_mul hcC haA ha.le hC.le, ?_⟩
  filter_upwards [he, he'] with k hk hk'
  constructor
  · calc
      (c*a)*h k ≤ c*g k := by simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hk'.1 hc.le
      _ ≤ f k := hk.1
  · exact hk.2.trans (by simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hk'.2 hC.le)

/-- Assume [the stated hf condition](hyp:hf) and [the stated hg condition](hyp:hg). [Nonnegative comparable sequences vanish together](goal). -/
-- @node: comparable_tendsto_zero_iff
lemma comparable_tendsto_zero_iff {f g : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) (h : Comparable f g) :
    Filter.Tendsto f Filter.atTop (nhds 0) ↔
      Filter.Tendsto g Filter.atTop (nhds 0) := by
  have transfer : ∀ (u v : ℕ → ℝ), (∀ k, 0 ≤ u k) → Comparable u v →
      Filter.Tendsto v Filter.atTop (nhds 0) →
      Filter.Tendsto u Filter.atTop (nhds 0) := by
    intro u v hu huv hv
    obtain ⟨c, C, hc, hcC, he⟩ := huv
    apply squeeze_zero' (Filter.Eventually.of_forall hu) (he.mono fun k hk => hk.2)
    simpa using hv.const_mul C
  exact ⟨transfer g f hg (comparable_symm h), transfer f g hf h⟩

/-- Assume [the stated hf condition](hyp:hf). [A nonnegative sequence and its square root vanish together](goal). -/
-- @node: tendsto_sqrt_zero_iff
lemma tendsto_sqrt_zero_iff (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    Filter.Tendsto (fun k => Real.sqrt (f k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto f Filter.atTop (nhds 0) := by
  constructor
  · intro h
    have hh := h.pow 2
    simpa only [Real.sq_sqrt (hf _), zero_pow (by omega : 2 ≠ 0)] using hh
  · intro h
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp h

/-- Assume [the stated hc condition](hyp:hc), [the stated hc c condition](hyp:hcC), and [the function hBounds](hyp:hBounds). [Risk and honest length inherit every numerical resource conclusion from uniform positive comparisons with the rate and its square root](goal). -/
-- @node: value_sequence_conclusions_of_bounds
lemma value_sequence_conclusions_of_bounds
    (risk length : (n d : ℕ) → ℝ → ℝ) (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hBounds : ∀ n d eps, Allowed n d eps →
      c * rho (n*eps^2) d ≤ risk n d eps ∧
      risk n d eps ≤ C * rho (n*eps^2) d ∧
      c * Real.sqrt (rho (n*eps^2) d) ≤ length n d eps ∧
      length n d eps ≤ C * Real.sqrt (rho (n*eps^2) d)) :
    ValueSequenceConclusions risk length := by
  have hC : 0 < C := hc.trans_le hcC
  have hrho : ∀ n d eps, Allowed n d eps → 0 ≤ rho (n*eps^2) d := by
    intro n d eps h
    exact (by positivity : (0 : ℝ) ≤ min 1 (1 / (n*eps^2))).trans
      (rho_elementary_comparisons n d eps h).1
  constructor
  · intro ns ds es h
    have hR : Comparable (fun k => risk (ns k) (ds k) (es k))
        (fun k => rho (ns k*(es k)^2) (ds k)) :=
      ⟨c, C, hc, hcC, Filter.Eventually.of_forall fun k =>
        ⟨(hBounds _ _ _ (h k)).1, (hBounds _ _ _ (h k)).2.1⟩⟩
    have hH : Comparable (fun k => length (ns k) (ds k) (es k))
        (fun k => Real.sqrt (rho (ns k*(es k)^2) (ds k))) :=
      ⟨c, C, hc, hcC, Filter.Eventually.of_forall fun k =>
        (hBounds _ _ _ (h k)).2.2⟩
    have hR0 : ∀ k, 0 ≤ risk (ns k) (ds k) (es k) := fun k =>
      (mul_nonneg hc.le (hrho _ _ _ (h k))).trans (hBounds _ _ _ (h k)).1
    have hH0 : ∀ k, 0 ≤ length (ns k) (ds k) (es k) := fun k =>
      (mul_nonneg hc.le (Real.sqrt_nonneg _)).trans (hBounds _ _ _ (h k)).2.2.1
    have hparam : Comparable (fun k => risk (ns k) (ds k) (es k))
        (fun k => 1/(ns k*(es k)^2)) ↔
        Comparable (fun k => rho (ns k*(es k)^2) (ds k))
          (fun k => 1/(ns k*(es k)^2)) :=
      ⟨fun hh => comparable_trans (comparable_symm hR) hh,
        fun hh => comparable_trans hR hh⟩
    refine ⟨?_, ?_, hparam.trans (rho_parametric_comparable_iff ns ds es h), ?_⟩
    · exact (comparable_tendsto_zero_iff hR0 (fun k => hrho _ _ _ (h k)) hR).trans
        (rho_consistency_iff ns ds es h)
    · exact ((comparable_tendsto_zero_iff hH0 (fun k => Real.sqrt_nonneg _) hH).trans
        (tendsto_sqrt_zero_iff _ (fun k => hrho _ _ _ (h k)))).trans
        (rho_consistency_iff ns ds es h)
    · intro ht
      exact hparam.trans (rho_parametric_iff_bounded_dimension ns ds es h ht)
  · intro a b ha hab
    obtain ⟨u, U, hu, huU, D0, hD⟩ := rho_elbow_comparison a b ha hab
    refine ⟨min (c*u) (c^2*u), max (C*U) (C^2*U),
      lt_min (mul_pos hc hu) (mul_pos (sq_pos_of_pos hc) hu),
      (min_le_left _ _).trans ((mul_le_mul hcC huU hu.le hC.le).trans
        (le_max_left _ _)), D0, ?_⟩
    intro n d eps h hd ht
    obtain ⟨hlo, hhi⟩ := hD d hd h.2.1 (n*eps^2) ht
    obtain ⟨hRlo, hRhi, hHlo, hHhi⟩ := hBounds n d eps h
    have hU : 0 < U := hu.trans_le huU
    have hslo := Real.sqrt_le_sqrt hlo
    have hshi := Real.sqrt_le_sqrt hhi
    rw [Real.sqrt_mul hu.le, Real.sqrt_sq_eq_abs] at hslo
    rw [Real.sqrt_mul hU.le, Real.sqrt_sq_eq_abs] at hshi
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        min (c*u) (c^2*u) * (Real.log (logDim d)/logDim d)^2 ≤
            (c*u) * (Real.log (logDim d)/logDim d)^2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
        _ ≤ c * rho (n*eps^2) d := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlo hc.le
        _ ≤ risk n d eps := hRlo
    · calc
        risk n d eps ≤ C * rho (n*eps^2) d := hRhi
        _ ≤ (C*U) * (Real.log (logDim d)/logDim d)^2 := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hhi hC.le
        _ ≤ max (C*U) (C^2*U) * (Real.log (logDim d)/logDim d)^2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    · have hsqrt : Real.sqrt (min (c*u) (c^2*u)) ≤ c * Real.sqrt u := by
        calc
          _ ≤ Real.sqrt (c^2*u) := Real.sqrt_le_sqrt (min_le_right _ _)
          _ = c * Real.sqrt u := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
      calc
        _ ≤ (c * Real.sqrt u) * |Real.log (logDim d)/logDim d| :=
          mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)
        _ ≤ c * Real.sqrt (rho (n*eps^2) d) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hslo hc.le
        _ ≤ length n d eps := hHlo
    · have hsqrt : C * Real.sqrt U ≤ Real.sqrt (max (C*U) (C^2*U)) := by
        calc
          _ = Real.sqrt (C^2*U) := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
          _ ≤ _ := Real.sqrt_le_sqrt (le_max_right _ _)
      calc
        length n d eps ≤ C * Real.sqrt (rho (n*eps^2) d) := hHhi
        _ ≤ (C * Real.sqrt U) * |Real.log (logDim d)/logDim d| := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hshi hC.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt (abs_nonneg _)

end CausalSmith.Stat.LdpOptvalueUniformFrontier
