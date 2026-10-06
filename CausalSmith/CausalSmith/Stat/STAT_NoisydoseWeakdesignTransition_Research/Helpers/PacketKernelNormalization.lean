module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketNormalization

/-! Quantitative endpoint normalization by counting active filtered spectral terms (P3). -/
public section
set_option linter.style.whitespace false
set_option linter.style.longLine false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory Set Filter
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The fixed exponential filter is nonnegative everywhere. [This is the stated conclusion](goal). -/
-- @node: packetFilter_nonneg
lemma packetFilter_nonneg (s : ℝ) : 0 ≤ packetFilter s := by
  unfold packetFilter
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
/-- The fixed filter is strictly positive in its active interval. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: packetFilter_pos
lemma packetFilter_pos (s : ℝ) (hs : s ∈ Ioo (9/8 : ℝ) (15/8)) :
    0 < packetFilter s := by
  rw [packetFilter, if_pos hs]
  exact Real.exp_pos _
/-- Every legal packet degree has a spectral index strictly inside the filter support. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: packetFilter_active_degree
lemma packetFilter_active_degree (m : ℕ) (hm : 4 ≤ m) :
    m + m/2 ∈ Finset.range (2*m+1) ∧ 0 < packetFilter ((m+m/2 : ℕ) / (m : ℝ)) := by
  have hlo : 9*m < 8*(m+m/2) := by omega
  have hhi : 8*(m+m/2) < 15*m := by omega
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨Finset.mem_range.mpr (by omega), packetFilter_pos _ ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hmp]
    have h : (9 : ℝ)*m < 8*(m+m/2 : ℕ) := by exact_mod_cast hlo
    push_cast at h ⊢
    linarith
  · rw [div_lt_iff₀ hmp]
    have h : (8 : ℝ)*(m+m/2 : ℕ) < 15*m := by exact_mod_cast hhi
    push_cast at h ⊢
    linarith
/-- The diagonal filtered kernel is strictly positive because one active spectral term is positive. [Under the stated conditions](hyp:hNorm,ha,hb,hm). [This is the stated conclusion](goal). -/
-- @node: filteredJacobiKernel_endpoint_pos
lemma filteredJacobiKernel_endpoint_pos (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (m : ℕ) (hm : 4 ≤ m) :
    0 < filteredJacobiKernel a b packetFilter m (-1) (-1) := by
  unfold filteredJacobiKernel
  apply Finset.sum_pos'
  · intro j hj
    have hn := (hNorm a b ha hb j).2.1
    have hnum : 0 ≤ packetFilter ((j : ℝ)/m) * stdJacobi a b j (-1) *
        stdJacobi a b j (-1) := by
      nlinarith [packetFilter_nonneg ((j : ℝ)/m), sq_nonneg (stdJacobi a b j (-1))]
    exact div_nonneg hnum hn.le
  · obtain ⟨hj, hp⟩ := packetFilter_active_degree m hm
    refine ⟨m+m/2, hj, ?_⟩
    have hn := (hNorm a b ha hb (m+m/2)).2.1
    have hsq := sq_pos_of_ne_zero (stdJacobi_neg_one_ne_zero a b ha hb (m+m/2))
    apply div_pos _ hn
    nlinarith [mul_pos hp hsq]
/-- Positivity of the endpoint packet's normalizing denominator, without an asymptotic gate. [Under the stated conditions](hyp:hNorm,hkappa,hm). [This is the stated conclusion](goal). -/
-- @node: packetKernel_endpoint_pos
lemma packetKernel_endpoint_pos (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m : ℕ) (hm : 4 ≤ m) :
    0 < packetKernel kappa m (-1) := by
  rw [packetKernel, if_pos hkappa]
  exact filteredJacobiKernel_endpoint_pos hNorm 4 ((kappa-1)/2) (by norm_num)
    (by linarith) m hm
/-- The explicit filter is bounded by one everywhere. [This is the stated conclusion](goal). -/
-- @node: packetFilter_le_one
lemma packetFilter_le_one (s : ℝ) : packetFilter s ≤ 1 := by
  unfold packetFilter
  split_ifs with hs
  · apply Real.exp_le_one_iff.mpr
    have hp : 0 < (s-9/8)*(15/8-s) := mul_pos (by linarith [hs.1]) (by linarith [hs.2])
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le
  · norm_num

/-- On the fixed counting interval the explicit filter has a degree-independent positive lower bound. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: packetFilter_counting_interval_lower
lemma packetFilter_counting_interval_lower (s : ℝ) (hs : s ∈ Icc (5/4 : ℝ) (7/4)) :
    Real.exp (-64) ≤ packetFilter s := by
  rw [packetFilter, if_pos (show s ∈ Ioo (9/8 : ℝ) (15/8) by
    constructor <;> linarith [hs.1, hs.2])]
  apply Real.exp_le_exp.mpr
  have hp : (1/64 : ℝ) ≤ (s-9/8)*(15/8-s) := by nlinarith [hs.1, hs.2]
  have hpp : 0 < (s-9/8)*(15/8-s) := by linarith
  have hdiv : 1/((s-9/8)*(15/8-s)) ≤ (64 : ℝ) :=
    (div_le_iff₀ hpp).mpr (by linarith)
  simpa only [neg_div] using neg_le_neg hdiv

/-- Endpoint normalization has the full two-sided degree order claimed in (P3). [Under the stated conditions](hyp:hNorm,hGamma,hkappa). [This is the stated conclusion](goal). -/
-- @node: packetKernel_endpoint_power_bounds
lemma packetKernel_endpoint_power_bounds (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 4 ≤ m →
      c*(m : ℝ)^(kappa+1) ≤ packetKernel kappa m (-1) ∧
      packetKernel kappa m (-1) ≤ C*(m : ℝ)^(kappa+1) := by
  obtain ⟨c, C, hc, hC, hcoef⟩ := jacobi_endpoint_spectral_power_bounds
    hNorm hGamma ((kappa-1)/2) (by linarith)
  have hexp : 2*((kappa-1)/2)+1 = kappa := by ring
  simp only [hexp] at hcoef
  let E := Real.exp (-64)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨E*c/7, 3*C*(2 : ℝ)^kappa, by positivity, by positivity, ?_⟩
  intro m hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpow : 0 ≤ (m : ℝ)^kappa := (Real.rpow_pos_of_pos hmp _).le
  have hepow : (m : ℝ)^(kappa+1) = (m : ℝ)^kappa * m := by
    rw [Real.rpow_add hmp, Real.rpow_one]
  let f : ℕ → ℝ := fun j => packetFilter ((j : ℝ)/m) *
    (stdJacobi 4 ((kappa-1)/2) j (-1))^2 / jacobiSqNorm 4 ((kappa-1)/2) j
  have hkernel : packetKernel kappa m (-1) = ∑ j ∈ Finset.range (2*m+1), f j := by
    rw [packetKernel, if_pos hkappa, filteredJacobiKernel]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    ring
  have hfnonneg (j : ℕ) : 0 ≤ f j := by
    exact div_nonneg (mul_nonneg (packetFilter_nonneg _) (sq_nonneg _))
      (hNorm 4 ((kappa-1)/2) (by norm_num) (by linarith) j).2.1.le
  have hupper (j : ℕ) (hj : j ∈ Finset.range (2*m+1)) :
      f j ≤ C*(2 : ℝ)^kappa*(m : ℝ)^kappa := by
    by_cases hz : packetFilter ((j : ℝ)/m) = 0
    · simp only [f, hz, zero_mul, zero_div]
      positivity
    · have hs : (j : ℝ)/m ∈ Ioo (9/8 : ℝ) (15/8) := by
        by_contra hn
        exact hz (by rw [packetFilter, if_neg hn])
      have hjp : 1 ≤ j := by
        have hlow := (lt_div_iff₀ hmp).mp hs.1
        by_contra hn
        have hjz : j = 0 := by omega
        simp only [hjz, Nat.cast_zero] at hlow
        nlinarith
      have hju : (j : ℝ) ≤ 2*m := by
        exact_mod_cast (show j ≤ 2*m by have := Finset.mem_range.mp hj; omega)
      have hcp := (hcoef j hjp).2
      have hrpow : (j : ℝ)^kappa ≤ (2*(m : ℝ))^kappa :=
        Real.rpow_le_rpow (by positivity) hju hkappa.le
      dsimp [f]
      calc
        _ = packetFilter ((j : ℝ)/m) *
          ((stdJacobi 4 ((kappa-1)/2) j (-1))^2 / jacobiSqNorm 4 ((kappa-1)/2) j) := by ring
        _ ≤ 1 * (C*(j : ℝ)^kappa) := mul_le_mul (packetFilter_le_one _) hcp
          (div_nonneg (sq_nonneg _)
            (hNorm 4 ((kappa-1)/2) (by norm_num) (by linarith) j).2.1.le) (by norm_num)
        _ ≤ C*(2*(m : ℝ))^kappa := by simpa using mul_le_mul_of_nonneg_left hrpow hC.le
        _ = _ := by rw [Real.mul_rpow (by norm_num) hmp.le]; ring
  have hlower (i : ℕ) (hi : i ∈ Finset.range (m/4)) :
      E*c*(m : ℝ)^kappa ≤ f (m+m/4+1+i) := by
    have hi' : i < m/4 := Finset.mem_range.mp hi
    have hindex : m ≤ m+m/4+1+i := by omega
    have hindex1 : 1 ≤ m+m/4+1+i := by omega
    have hlow : 5*m ≤ 4*(m+m/4+1+i) := by omega
    have hupp : 4*(m+m/4+1+i) ≤ 7*m := by omega
    have hs : ((m+m/4+1+i : ℕ) : ℝ)/m ∈ Icc (5/4 : ℝ) (7/4) := by
      constructor
      · rw [le_div_iff₀ hmp]
        have h : (5 : ℝ)*m ≤ 4*(m+m/4+1+i : ℕ) := by exact_mod_cast hlow
        linarith
      · rw [div_le_iff₀ hmp]
        have h : (4 : ℝ)*(m+m/4+1+i : ℕ) ≤ 7*m := by exact_mod_cast hupp
        linarith
    have hcj := (hcoef (m+m/4+1+i) hindex1).1
    have hpj : (m : ℝ)^kappa ≤ ((m+m/4+1+i : ℕ) : ℝ)^kappa :=
      Real.rpow_le_rpow hmp.le (by exact_mod_cast hindex) hkappa.le
    dsimp [f]
    calc
      _ ≤ E*(c*((m+m/4+1+i : ℕ) : ℝ)^kappa) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpj hc.le) hE.le
      _ ≤ packetFilter (((m+m/4+1+i : ℕ) : ℝ)/m) *
          ((stdJacobi 4 ((kappa-1)/2) (m+m/4+1+i) (-1))^2 /
            jacobiSqNorm 4 ((kappa-1)/2) (m+m/4+1+i)) :=
        mul_le_mul (packetFilter_counting_interval_lower _ hs) hcj (by positivity)
          (packetFilter_nonneg _)
      _ = _ := by ring
  rw [hkernel]
  constructor
  · let g : ℕ → ℕ := fun i => m+m/4+1+i
    have hginj : Function.Injective g := by intro i j hij; dsimp [g] at hij; omega
    have hsub : (Finset.range (m/4)).image g ⊆ Finset.range (2*m+1) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_range.mpr
      dsimp [g]
      have := Finset.mem_range.mp hi
      omega
    have hcount : (m : ℝ)/7 ≤ (m/4 : ℕ) := by
      have h : m ≤ 7*(m/4) := by omega
      have hreal : (m : ℝ) ≤ 7*(m/4 : ℕ) := by exact_mod_cast h
      linarith
    calc
      E*c/7*(m : ℝ)^(kappa+1) = ((m : ℝ)/7)*(E*c*(m : ℝ)^kappa) := by rw [hepow]; ring
      _ ≤ (m/4 : ℕ)*(E*c*(m : ℝ)^kappa) := mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = ∑ i ∈ Finset.range (m/4), E*c*(m : ℝ)^kappa := by simp
      _ ≤ ∑ i ∈ Finset.range (m/4), f (g i) := Finset.sum_le_sum (fun i hi => hlower i hi)
      _ = ∑ j ∈ (Finset.range (m/4)).image g, f j :=
        (Finset.sum_image (fun i hi j hj hij => hginj hij)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hn => hfnonneg j)
  · calc
      _ ≤ ∑ j ∈ Finset.range (2*m+1), C*(2 : ℝ)^kappa*(m : ℝ)^kappa :=
        Finset.sum_le_sum hupper
      _ = (2*m+1 : ℕ)*(C*(2 : ℝ)^kappa*(m : ℝ)^kappa) := by simp
      _ ≤ (3*(m : ℝ))*(C*(2 : ℝ)^kappa*(m : ℝ)^kappa) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        push_cast
        have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      _ = _ := by rw [hepow]; ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition
