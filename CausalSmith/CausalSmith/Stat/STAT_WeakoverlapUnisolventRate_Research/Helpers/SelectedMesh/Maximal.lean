module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Model
public import Causalean.Mathlib.Probability.SubGaussian.Main
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Ordered sub-Gaussian maximal inequality -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory

/-- The logarithmic correction is absorbed by a positive power on the unit interval. [For the stated inputs and conditions](hyp:β,s,hβ,hs,hs1), [the asserted conclusion holds](goal). -/
lemma scale_log_envelope_unit (β s : ℝ) (hβ : 1 ≤ β)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ β * Real.sqrt (1 + max 0 (Real.log (1 / s))) ≤ 1 := by
  have hdiv : 0 < 1 / s := by positivity
  have hlog : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by
    apply (one_le_div hs).2
    exact hs1)
  have hlogbound := Real.log_le_sub_one_of_pos hdiv
  have hsqrtarg : 0 ≤ 1 + max 0 (Real.log (1 / s)) := by positivity
  have hsqrtbound : Real.sqrt (1 + max 0 (Real.log (1 / s))) ≤ 1 / s := by
    have harg : 1 + max 0 (Real.log (1 / s)) ≤ 1 / s := by
      rw [max_eq_right hlog]
      linarith
    exact (Real.sqrt_le_sqrt harg).trans (by
      have hdiv1 : 1 ≤ 1 / s := (one_le_div hs).2 hs1
      apply (Real.sqrt_le_left hdiv.le).2
      nlinarith)
  have hpow : s ^ β ≤ s := by
    simpa using (Real.rpow_le_rpow_of_exponent_ge hs hs1 hβ : s ^ β ≤ s ^ (1 : ℝ))
  calc
    s ^ β * Real.sqrt (1 + max 0 (Real.log (1 / s))) ≤ s * (1 / s) := by
      gcongr
    _ = 1 := by field_simp

/-- A fixed upper scale gives a uniform bound for the oracle logarithmic factor. [For the stated inputs and conditions](hyp:β,s,K,hβ,hs,hsK), [the asserted conclusion holds](goal). -/
lemma scale_log_envelope_bounded (β s K : ℝ) (hβ : 1 ≤ β)
    (hs : 0 < s) (hsK : s ≤ K) :
    s ^ β * Real.sqrt (1 + max 0 (Real.log (1 / s))) ≤ max 1 (K ^ β) := by
  by_cases hs1 : s ≤ 1
  · exact (scale_log_envelope_unit β s hβ hs hs1).trans (le_max_left _ _)
  · have hlog : Real.log (1 / s) ≤ 0 := Real.log_nonpos
      (by positivity) ((div_le_one hs).2 (le_of_lt (lt_of_not_ge hs1)))
    have hsβ : s ^ β ≤ K ^ β := Real.rpow_le_rpow hs.le hsK (by linarith)
    rw [max_eq_left hlog]
    simpa using hsβ.trans (le_max_right 1 (K ^ β))

/-- Convert a selected-width bound into the oracle-rate logarithmic envelope. [For the stated inputs and conditions](hyp:β,h,o,K,hβ,hh,ho,hbound), [the asserted conclusion holds](goal). -/
lemma selectedMesh_oracle_log_bound (β h o K : ℝ)
    (hβ : 1 ≤ β) (hh : 0 < h) (ho : 0 < o)
    (hbound : h ≤ K * o) :
    h ^ β * Real.sqrt (1 + max 0 (Real.log (o / h))) ≤
      max 1 (K ^ β) * o ^ β := by
  have hr : 0 < h / o := div_pos hh ho
  have hrK : h / o ≤ K := (div_le_iff₀ ho).2 (by simpa [mul_comm] using hbound)
  have hlog : o / h = 1 / (h / o) := by
    field_simp
  have hpow : h ^ β = (h / o) ^ β * o ^ β := by
    rw [← Real.mul_rpow hr.le ho.le]
    congr 1
    field_simp
  rw [hpow, hlog]
  have hscale := scale_log_envelope_bounded β (h / o) K hβ hr hrK
  calc
    (h / o) ^ β * o ^ β * Real.sqrt (1 + max 0 (Real.log (1 / (h / o)))) =
        ((h / o) ^ β * Real.sqrt (1 + max 0 (Real.log (1 / (h / o))))) * o ^ β := by ring
    _ ≤ max 1 (K ^ β) * o ^ β :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg ho.le _)

/-- The final deterministic term in the selected-mesh envelope. [For the stated inputs and conditions](hyp:d,n,β,γ,h,K,hn,hβ,hh,hbound), [the asserted conclusion holds](goal). -/
lemma selectedMesh_oracle_rate_log_bound (d n : ℕ) (β γ h K : ℝ)
    (hn : 0 < n) (hβ : 1 ≤ β) (hh : 0 < h)
    (hbound : h ≤ K * oracleMesh d n β γ) :
    h ^ β * Real.sqrt
        (1 + max 0 (Real.log (oracleMesh d n β γ / h))) ≤
      max 1 (K ^ β) * oracleRate d n β γ := by
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  simpa only [oracleRate] using
    selectedMesh_oracle_log_bound β h (oracleMesh d n β γ) K hβ hh ho hbound

/-- The stochastic coefficient scale is the oracle mesh raised to the
smoothness plus half the effective dimension. [For the stated inputs and conditions](hyp:d,n,β,γ,hn,hden), [the asserted conclusion holds](goal). -/
lemma oracleMesh_stochastic_scale (d n : ℕ) (β γ : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + effectiveDimension d γ) :
    (n : ℝ) ^ (-(1 : ℝ) / 2) =
      (oracleMesh d n β γ) ^ (β + effectiveDimension d γ / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [oracleMesh, ← Real.rpow_mul hn'.le]
  congr 1
  field_simp

/-- Dividing the stochastic scale by the bias scale leaves only the ratio
between oracle and selected mesh widths. [For the stated inputs and conditions](hyp:d,n,β,γ,h,hn,hden,hh), [the asserted conclusion holds](goal). -/
lemma selectedMesh_stochastic_bias_ratio (d n : ℕ) (β γ h : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + effectiveDimension d γ)
    (hh : 0 < h) :
    ((n : ℝ) ^ (-(1 : ℝ) / 2) *
      h ^ (-(effectiveDimension d γ) / 2)) / h ^ β =
      (oracleMesh d n β γ / h) ^
        (β + effectiveDimension d γ / 2) := by
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [oracleMesh_stochastic_scale d n β γ hn hden]
  rw [Real.div_rpow ho.le hh.le]
  rw [Real.rpow_add ho, Real.rpow_add hh]
  rw [show -(effectiveDimension d γ) / 2 =
    -(effectiveDimension d γ / 2) by ring, Real.rpow_neg hh.le]
  field_simp

/-- A positive power in the maximal bound changes only the constant in its
logarithmic factor. [For the stated inputs and conditions](hyp:o,h,p,ho,hh,hp), [the asserted conclusion holds](goal). -/
lemma selectedMesh_maximal_log_scale (o h p : ℝ)
    (ho : 0 < o) (hh : 0 < h) (hp : 0 ≤ p) :
    1 + max 0 (Real.log ((o / h) ^ p)) ≤
      max 1 p * (1 + max 0 (Real.log (o / h))) := by
  rw [Real.log_rpow (div_pos ho hh)]
  by_cases hl : 0 ≤ Real.log (o / h)
  · rw [max_eq_right hl, max_eq_right (mul_nonneg hp hl)]
    have hmax : 1 ≤ max 1 p := le_max_left _ _
    have hpmax : p ≤ max 1 p := le_max_right _ _
    nlinarith
  · have hl' : Real.log (o / h) ≤ 0 := le_of_lt (lt_of_not_ge hl)
    rw [max_eq_left hl', max_eq_left (mul_nonpos_of_nonneg_of_nonpos hp hl')]
    simpa only [add_zero, mul_one] using (le_max_left 1 p)

/-- A mass rank at least the ordered position gives the ordered variance proxy. [For the stated inputs and conditions](hyp:a,b,α,r,k,hb,hα,hr), [the asserted conclusion holds](goal). -/
lemma selectedMesh_rank_proxy_to_ordered (a b α r : ℝ) (k : ℕ)
    (hb : 0 ≤ b) (hα : 0 < α)
    (hr : (k + 1 : ℝ) ≤ r) :
    min a (b * r ^ (-α)) ≤
      min a (b * (k + 1 : ℝ) ^ (-α)) := by
  have hk : 0 < (k + 1 : ℝ) := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le hk hr
  have hpow : (k + 1 : ℝ) ^ α ≤ r ^ α :=
    Real.rpow_le_rpow hk.le hr hα.le
  have hinv : r ^ (-α) ≤ (k + 1 : ℝ) ^ (-α) := by
    rw [Real.rpow_neg hrpos.le, Real.rpow_neg hk.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hrpos α) (Real.rpow_pos_of_pos hk α)).2 hpow
  exact min_le_min_left a (mul_le_mul_of_nonneg_left hinv hb)

/-- A uniform lower bound on the mass coefficient absorbs its reciprocal
inside the two competing variance scales. [For the stated inputs and conditions](hyp:A,x,y,κ,c,hA,hx,hy,hκ,hc), [the asserted conclusion holds](goal). -/
lemma selectedMesh_uniform_min_proxy (A x y κ c : ℝ)
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hy : 0 < y)
    (hκ : 0 < κ) (hc : κ ≤ c) :
    A * min x (5 / (c * y)) ≤
      (A * max 1 (5 / κ)) * min x y⁻¹ := by
  have hcpos : 0 < c := hκ.trans_le hc
  let M := max 1 (5 / κ)
  have hM : 1 ≤ M := le_max_left _ _
  have hMκ : 5 / κ ≤ M := le_max_right _ _
  have hdiv : 5 / (c * y) ≤ M * y⁻¹ := by
    rw [show M * y⁻¹ = M / y by ring]
    apply (div_le_div_iff₀ (mul_pos hcpos hy) hy).2
    have h : 5 ≤ M * c := by
      have h' : 5 ≤ M * κ := (div_le_iff₀ hκ).mp hMκ
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (le_trans (by norm_num : (0 : ℝ) ≤ 1) hM)]
    nlinarith
  have hmin : min x (5 / (c * y)) ≤ M * min x y⁻¹ := by
    by_cases hxy : x ≤ y⁻¹
    · rw [min_eq_left hxy]
      exact (min_le_left _ _).trans (by nlinarith)
    · have hyx : y⁻¹ ≤ x := le_of_lt (lt_of_not_ge hxy)
      rw [min_eq_right hyx]
      exact (min_le_right _ _).trans hdiv
  calc
    A * min x (5 / (c * y)) ≤ A * (M * min x y⁻¹) :=
      mul_le_mul_of_nonneg_left hmin hA
    _ = (A * M) * min x y⁻¹ := by ring

/-- Normalize the ordered inverse-count proxy after bounding its mass
coefficient uniformly on the adaptation interval. [For the stated inputs and conditions](hyp:A,x,n,h,r,κ,c,D,α,hA,hx,hn,hh,hr,hκ,hc), [the asserted conclusion holds](goal). -/
lemma selectedMesh_uniform_ordered_proxy
    (A x n h r κ c D α : ℝ)
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hn : 0 < n) (hh : 0 < h)
    (hr : 0 < r) (hκ : 0 < κ) (hc : κ ≤ c) :
    A * min x (5 / (n * c * h ^ D * r ^ α)) ≤
      (A * max 1 (5 / κ)) *
        min x (n⁻¹ * h ^ (-D) * r ^ (-α)) := by
  have hy : 0 < n * h ^ D * r ^ α := by positivity
  have hproxy := selectedMesh_uniform_min_proxy A x
    (n * h ^ D * r ^ α) κ c hA hx hy hκ hc
  have hden : n * c * h ^ D * r ^ α = c * (n * h ^ D * r ^ α) := by ring
  rw [← hden] at hproxy
  simpa only [mul_inv_rev, Real.rpow_neg hh.le, Real.rpow_neg hr.le,
    mul_assoc, mul_comm, mul_left_comm] using hproxy

/-- The raw selected-mesh variance proxy has one constant for every ordered
cube, including ties in the cube masses. [For the stated inputs and conditions](hyp:A,x,n,h,r,κ,c,D,α,k,hA,hx,hn,hh,hr,hκ,hc,hα,hrank), [the asserted conclusion holds](goal). -/
lemma selectedMesh_uniform_ranked_raw_proxy
    (A x n h r κ c D α : ℝ) (k : ℕ)
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hn : 0 < n) (hh : 0 < h)
    (hr : 0 < r) (hκ : 0 < κ) (hc : κ ≤ c)
    (hα : 0 < α) (hrank : (k + 1 : ℝ) ≤ r) :
    A * min x (5 / (n * c * h ^ D * r ^ α)) ≤
      (A * max 1 (5 / κ)) *
        min x (n⁻¹ * h ^ (-D) * (k + 1 : ℝ) ^ (-α)) := by
  have hnormalized := selectedMesh_uniform_ordered_proxy
    A x n h r κ c D α hA hx hn hh hr hκ hc
  have hordered := selectedMesh_rank_proxy_to_ordered x
    (n⁻¹ * h ^ (-D)) α r k (by positivity) hα hrank
  exact hnormalized.trans
    (mul_le_mul_of_nonneg_left hordered
      (mul_nonneg hA (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 (5 / κ)))))

/-- Convert a raw mass-rank MGF estimate into the common ordered proxy used
by the scalar maximal inequality. [For the stated inputs and conditions](hyp:Ω,μ,Z,A,x,n,h,r,κ,c,D,α,k,t,hA,hx,hn,hh,hr,hκ,hc,hα,hrank,hmgf), [the asserted conclusion holds](goal). -/
lemma selectedMesh_uniform_ranked_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ)
    (A x n h r κ c D α : ℝ) (k : ℕ) (t : ℝ)
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hn : 0 < n) (hh : 0 < h)
    (hr : 0 < r) (hκ : 0 < κ) (hc : κ ≤ c)
    (hα : 0 < α) (hrank : (k + 1 : ℝ) ≤ r)
    (hmgf : mgf Z μ t ≤
      Real.exp (A * min x (5 / (n * c * h ^ D * r ^ α)) * t ^ 2 / 2)) :
    mgf Z μ t ≤ Real.exp
      ((A * max 1 (5 / κ)) *
        min x (n⁻¹ * h ^ (-D) * (k + 1 : ℝ) ^ (-α)) * t ^ 2 / 2) := by
  exact hmgf.trans (Real.exp_le_exp.mpr (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
    exact selectedMesh_uniform_ranked_raw_proxy
      A x n h r κ c D α k hA hx hn hh hr hκ hc hα hrank))

/-- One maximal constant works over a fixed compact exponent interval. [For the stated inputs and conditions](hyp:αmin,αmax,hαmin,hαmax), [the asserted conclusion holds](goal). -/
lemma orderedSubGaussianMaximal_uniform (αmin αmax : ℝ)
    (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ), α ∈ Set.Icc αmin αmax →
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) (Z : Fin N → Ω → ℝ) (a b : ℝ),
        0 < a → 0 < b →
        (∀ k : Fin N, ∀ t : ℝ,
          Integrable (fun ω => Real.exp (t * Z k ω)) μ) →
        (∀ k : Fin N, ∀ t : ℝ,
          mgf (Z k) μ t ≤ Real.exp
            (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
        ∫ ω, sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) ∂μ ≤
          K * a * Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨Kmin, hKmin, hmax⟩ :=
    Causalean.Mathlib.Probability.SubGaussian.orderedSubGaussianMaximal αmin hαmin
  let R : ℝ := αmax / αmin
  have hR : 1 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ hαmin).2 (by nlinarith)
  refine ⟨Kmin * Real.sqrt R, mul_pos hKmin (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hR)), ?_⟩
  intro α hα Ω _ μ _ N Z a b ha hb hmgf hbound
  have hαpos : 0 < α := lt_of_lt_of_le hαmin hα.1
  have hproxy : ∀ k : Fin N, ∀ t : ℝ,
      mgf (Z k) μ t ≤ Real.exp
        (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-αmin)) * t ^ 2 / 2) := by
    intro k t
    calc
      mgf (Z k) μ t ≤ Real.exp
          (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2) := hbound k t
      _ ≤ Real.exp
          (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-αmin)) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
        apply min_le_min_left
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
        apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast Nat.le_add_left 1 k.val
        · linarith [hα.1]
  have hbase := hmax μ N Z a b ha hb hmgf hproxy
  have hrpos : 0 < b / a := div_pos hb ha
  have hscale :
      1 + max 0 (Real.log ((b / a) ^ (2 / αmin))) ≤
        R * (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
    rw [Real.log_rpow hrpos, Real.log_rpow hrpos]
    by_cases ht : 0 ≤ Real.log (b / a)
    · have hamin : 0 ≤ 2 / αmin * Real.log (b / a) :=
        mul_nonneg (div_nonneg (by norm_num) (le_of_lt hαmin)) ht
      have haα : 0 ≤ 2 / α * Real.log (b / a) :=
        mul_nonneg (div_nonneg (by norm_num) (le_of_lt hαpos)) ht
      rw [max_eq_right hamin, max_eq_right haα]
      dsimp [R]
      have hαle : α ≤ αmax := hα.2
      apply (mul_le_mul_iff_of_pos_left hαmin).mp
      have hαne : α ≠ 0 := ne_of_gt hαpos
      have hminne : αmin ≠ 0 := ne_of_gt hαmin
      have hprod := mul_nonneg (sub_nonneg.mpr hαle) ht
      field_simp
      nlinarith
    · have ht' : Real.log (b / a) ≤ 0 := le_of_lt (lt_of_not_ge ht)
      have hamin : 2 / αmin * Real.log (b / a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (by norm_num) (le_of_lt hαmin)) ht'
      have haα : 2 / α * Real.log (b / a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (by norm_num) (le_of_lt hαpos)) ht'
      rw [max_eq_left hamin, max_eq_left haα]
      nlinarith [hR]
  have hsqrt :
      Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / αmin)))) ≤
        Real.sqrt R * Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
    rw [← Real.sqrt_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hR))]
    exact Real.sqrt_le_sqrt hscale
  calc
    ∫ ω, sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) ∂μ ≤
        Kmin * a * Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / αmin)))) := hbase
    _ ≤ (Kmin * Real.sqrt R) * a *
          Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (le_of_lt hKmin) (le_of_lt ha))]

/-- The maximum of the coefficient sup norms is bounded by the sum of the
coordinatewise maxima. This lets a scalar maximal inequality handle the
finite monomial index without changing its logarithmic scale. [For the stated inputs and conditions](hyp:κ,ι,f), [the asserted conclusion holds](goal). -/
lemma selectedMesh_maxNorm_le_sum_maxAbs {κ ι : Type*}
    [Finite κ] [Nonempty κ] [Fintype ι] (f : κ → ι → ℝ) :
    sSup ((fun k : κ => ‖f k‖) '' Set.univ) ≤
      ∑ a : ι, sSup ((fun k : κ => |f k a|) '' Set.univ) := by
  classical
  apply csSup_le
  · exact ⟨‖f (Classical.choice inferInstance)‖, ⟨_, Set.mem_univ _, rfl⟩⟩
  · rintro x ⟨k, -, rfl⟩
    have hb (a : ι) : BddAbove ((fun k : κ => |f k a|) '' Set.univ) :=
      by simpa only [Set.image_univ] using
        (Set.finite_range (fun k : κ => |f k a|)).bddAbove
    have hn (a : ι) : 0 ≤ sSup ((fun k : κ => |f k a|) '' Set.univ) :=
      (abs_nonneg _).trans (le_csSup (hb a) ⟨k, Set.mem_univ _, rfl⟩)
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a ha => hn a)).2
    intro a
    calc
      ‖f k a‖ = |f k a| := Real.norm_eq_abs _
      _ ≤ sSup ((fun k : κ => |f k a|) '' Set.univ) :=
        le_csSup (hb a) ⟨k, Set.mem_univ _, rfl⟩
      _ ≤ ∑ b : ι, sSup ((fun k : κ => |f k b|) '' Set.univ) :=
        Finset.single_le_sum (fun b hb => hn b) (Finset.mem_univ a)

/-- Integrate the finite-coordinate reduction once the scalar maxima are
integrable, as they are under the conditional sub-Gaussian bounds. [For the stated inputs and conditions](hyp:Ω,κ,ι,μ,f,hwhole,hcoord), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integral_maxNorm_le_sum_maxAbs
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Finite κ] [Nonempty κ]
    [Fintype ι] (μ : Measure Ω) (f : Ω → κ → ι → ℝ)
    (hwhole : Integrable (fun ξ =>
      sSup ((fun k : κ => ‖f ξ k‖) '' Set.univ)) μ)
    (hcoord : ∀ a : ι, Integrable (fun ξ =>
      sSup ((fun k : κ => |f ξ k a|) '' Set.univ)) μ) :
    (∫ ξ, sSup ((fun k : κ => ‖f ξ k‖) '' Set.univ) ∂μ) ≤
      ∑ a : ι, ∫ ξ, sSup ((fun k : κ => |f ξ k a|) '' Set.univ) ∂μ := by
  have hsum : Integrable (fun ξ =>
      ∑ a : ι, sSup ((fun k : κ => |f ξ k a|) '' Set.univ)) μ :=
    integrable_finsetSum _ (fun a ha => hcoord a)
  calc
    (∫ ξ, sSup ((fun k : κ => ‖f ξ k‖) '' Set.univ) ∂μ) ≤
        ∫ ξ, ∑ a : ι, sSup ((fun k : κ => |f ξ k a|) '' Set.univ) ∂μ :=
      integral_mono hwhole hsum (fun ξ => selectedMesh_maxNorm_le_sum_maxAbs (f ξ))
    _ = _ := integral_finsetSum _ (fun a ha => hcoord a)

/-- Exponential moments on both sides make a scalar coefficient integrable. [For the stated inputs and conditions](hyp:Ω,μ,Z,hpos,hneg), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integrable_of_exp_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ)
    (hpos : Integrable (fun ω => Real.exp (Z ω)) μ)
    (hneg : Integrable (fun ω => Real.exp (-Z ω)) μ) :
    Integrable Z μ := by
  have h := ProbabilityTheory.integrable_pow_abs_mul_exp_of_integrable_exp_mul
    (X := Z) (v := 0) (t := 1) (by norm_num)
    (by simpa using hpos) (by simpa using hneg) 1
  have hm : AEStronglyMeasurable Z μ :=
    (ProbabilityTheory.aemeasurable_of_integrable_exp_mul
      (X := Z) (u := 1) (v := -1) (by norm_num)
      (by simpa using hpos) (by simpa using hneg)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, pow_one, zero_mul, Real.exp_zero, mul_one] using h

/-- The maximum of finitely many integrable scalar absolute values is integrable. [For the stated inputs and conditions](hyp:Ω,κ,μ,Z,hZ,s,hs), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integrable_finset_maxAbs
    {Ω κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : κ → Ω → ℝ)
    (hZ : ∀ k, Integrable (Z k) μ)
    (s : Finset κ) (hs : s.Nonempty) :
    Integrable (fun ω => s.sup' hs (fun k => |Z k ω|)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert k s hk ih =>
    by_cases hs' : s.Nonempty
    · have h := (hZ k).abs.sup (ih hs')
      convert h using 1
      funext ω
      simp only [Finset.sup'_insert hs', Pi.sup_apply]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using (hZ k).abs

/-- An integrable finite family has an integrable maximum absolute value. [For the stated inputs and conditions](hyp:Ω,κ,μ,Z,hZ), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integrable_maxAbs
    {Ω κ : Type*} [MeasurableSpace Ω] [Finite κ] [Nonempty κ]
    (μ : Measure Ω) (Z : κ → Ω → ℝ)
    (hZ : ∀ k, Integrable (Z k) μ) :
    Integrable (fun ω => sSup ((fun k : κ => |Z k ω|) '' Set.univ)) μ := by
  classical
  letI := Fintype.ofFinite κ
  have h := selectedMesh_integrable_finset_maxAbs μ Z hZ
    Finset.univ Finset.univ_nonempty
  convert h using 1
  funext ω
  simpa using (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty
    (fun k => |Z k ω|)).symm

/-- Finite scalar maxima are integrable when all coordinates have two-sided
exponential moments. [For the stated inputs and conditions](hyp:Ω,κ,μ,Z,hexp), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integrable_maxAbs_of_exp_moments
    {Ω κ : Type*} [MeasurableSpace Ω] [Finite κ] [Nonempty κ]
    (μ : Measure Ω) (Z : κ → Ω → ℝ)
    (hexp : ∀ k, ∀ t : ℝ,
      Integrable (fun ω => Real.exp (t * Z k ω)) μ) :
    Integrable (fun ω => sSup ((fun k : κ => |Z k ω|) '' Set.univ)) μ := by
  have hZ (k : κ) : Integrable (Z k) μ :=
    selectedMesh_integrable_of_exp_moments μ (Z k)
      (by simpa using hexp k 1) (by simpa using hexp k (-1))
  exact selectedMesh_integrable_maxAbs μ Z hZ

/-- Coordinate exponential moments give the integrability conditions for a
finite maximum of coefficient sup norms. [For the stated inputs and conditions](hyp:Ω,κ,ι,μ,Z,hexp), [the asserted conclusion holds](goal). -/
lemma selectedMesh_integrable_vector_max_of_exp_moments
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Finite κ] [Nonempty κ]
    [Fintype ι] (μ : Measure Ω) (Z : κ → Ω → ι → ℝ)
    (hexp : ∀ k i t,
      Integrable (fun ω => Real.exp (t * Z k ω i)) μ) :
    Integrable (fun ω => sSup ((fun k : κ => ‖Z k ω‖) '' Set.univ)) μ ∧
    ∀ i : ι, Integrable (fun ω =>
      sSup ((fun k : κ => |Z k ω i|) '' Set.univ)) μ := by
  have hZ (k : κ) (i : ι) : Integrable (fun ω => Z k ω i) μ :=
    selectedMesh_integrable_of_exp_moments μ (fun ω => Z k ω i)
      (by simpa using hexp k i 1) (by simpa using hexp k i (-1))
  have hcoord (i : ι) : Integrable (fun ω =>
      sSup ((fun k : κ => |Z k ω i|) '' Set.univ)) μ :=
    selectedMesh_integrable_maxAbs μ (fun k ω => Z k ω i) (fun k => hZ k i)
  have hnorm (k : κ) : Integrable (fun ω => ‖Z k ω‖) μ := by
    apply Integrable.norm
    exact (integrable_pi_iff).2 (hZ k)
  have hwhole := selectedMesh_integrable_maxAbs μ
    (fun k ω => ‖Z k ω‖) hnorm
  refine ⟨?_, hcoord⟩
  simpa only [abs_norm] using hwhole

/-- Apply the scalar ordered maximal theorem to every coefficient coordinate,
then sum over the fixed finite monomial index. [For the stated inputs and conditions](hyp:αmin,αmax,hαmin,hαmax), [the asserted conclusion holds](goal). -/
lemma orderedSubGaussianMaximal_vector_uniform
    (αmin αmax : ℝ) (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ), α ∈ Set.Icc αmin αmax →
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) [Nonempty (Fin N)] (Z : Fin N → Ω → ι → ℝ)
        (a b : ℝ), 0 < a → 0 < b →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          Integrable (fun ω => Real.exp (t * Z k ω i)) μ) →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          mgf (fun ω => Z k ω i) μ t ≤ Real.exp
            (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
        Integrable (fun ω =>
          sSup ((fun k : Fin N => ‖Z k ω‖) '' Set.univ)) μ →
        (∀ i : ι, Integrable (fun ω =>
          sSup ((fun k : Fin N => |Z k ω i|) '' Set.univ)) μ) →
        (∫ ω, sSup ((fun k : Fin N => ‖Z k ω‖) '' Set.univ) ∂μ) ≤
          (Fintype.card ι : ℝ) * K * a *
            Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨K, hK, hmax⟩ :=
    orderedSubGaussianMaximal_uniform αmin αmax hαmin hαmax
  refine ⟨K, hK, ?_⟩
  intro α hα Ω ι _ _ μ _ N _ Z a b ha hb hint hmgf hwhole hcoord
  calc
    (∫ ω, sSup ((fun k : Fin N => ‖Z k ω‖) '' Set.univ) ∂μ) ≤
        ∑ i : ι, ∫ ω, sSup ((fun k : Fin N => |Z k ω i|) '' Set.univ) ∂μ :=
      selectedMesh_integral_maxNorm_le_sum_maxAbs μ
        (fun ω k i => Z k ω i) hwhole hcoord
    _ ≤ ∑ _i : ι, K * a *
          Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
      apply Finset.sum_le_sum
      intro i _
      exact hmax α hα μ N (fun k ω => Z k ω i) a b ha hb
        (fun k t => hint k i t) (fun k t => hmgf k i t)
    _ = (Fintype.card ι : ℝ) * K * a *
          Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
      simp [mul_assoc]

/-- The uniform vector maximal inequality with its integrability hypotheses
deduced from the coordinate exponential moments. [For the stated inputs and conditions](hyp:αmin,αmax,hαmin,hαmax), [the asserted conclusion holds](goal). -/
lemma orderedSubGaussianMaximal_vector_uniform_of_exp
    (αmin αmax : ℝ) (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ), α ∈ Set.Icc αmin αmax →
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) [Nonempty (Fin N)] (Z : Fin N → Ω → ι → ℝ)
        (a b : ℝ), 0 < a → 0 < b →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          Integrable (fun ω => Real.exp (t * Z k ω i)) μ) →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          mgf (fun ω => Z k ω i) μ t ≤ Real.exp
            (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
        (∫ ω, sSup ((fun k : Fin N => ‖Z k ω‖) '' Set.univ) ∂μ) ≤
          (Fintype.card ι : ℝ) * K * a *
            Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨K, hK, hmax⟩ :=
    orderedSubGaussianMaximal_vector_uniform αmin αmax hαmin hαmax
  refine ⟨K, hK, ?_⟩
  intro α hα Ω ι _ _ μ _ N _ Z a b ha hb hexp hmgf
  obtain ⟨hwhole, hcoord⟩ :=
    selectedMesh_integrable_vector_max_of_exp_moments μ Z hexp
  exact hmax α hα μ N Z a b ha hb hexp hmgf hwhole hcoord

/-- Reindex the vector maximal inequality by a mass-ordered enumeration of a
finite cube family. The maximum over cubes is unchanged by the enumeration. [For the stated inputs and conditions](hyp:αmin,αmax,hαmin,hαmax), [the asserted conclusion holds](goal). -/
lemma orderedSubGaussianMaximal_vector_equiv_uniform_of_exp
    (αmin αmax : ℝ) (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ), α ∈ Set.Icc αmin αmax →
      ∀ {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) [Nonempty (Fin N)]
        (σ : Fin N ≃ κ) (Z : κ → Ω → ι → ℝ)
        (a b : ℝ), 0 < a → 0 < b →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          Integrable (fun ω => Real.exp (t * Z (σ k) ω i)) μ) →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          mgf (fun ω => Z (σ k) ω i) μ t ≤ Real.exp
            (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
        (∫ ω, sSup ((fun k : κ => ‖Z k ω‖) '' Set.univ) ∂μ) ≤
          (Fintype.card ι : ℝ) * K * a *
            Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨K, hK, hmax⟩ :=
    orderedSubGaussianMaximal_vector_uniform_of_exp αmin αmax hαmin hαmax
  refine ⟨K, hK, ?_⟩
  intro α hα Ω κ ι _ _ μ _ N _ σ Z a b ha hb hexp hmgf
  have hreindex (ω : Ω) :
      sSup ((fun k : κ => ‖Z k ω‖) '' Set.univ) =
        sSup ((fun k : Fin N => ‖Z (σ k) ω‖) '' Set.univ) := by
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨σ.symm k, by simp⟩
    · rintro ⟨k, rfl⟩
      exact ⟨σ k, rfl⟩
  simp only [hreindex]
  exact hmax α hα μ N (fun k ω => Z (σ k) ω) a b ha hb hexp hmgf

/-- The weak-overlap rank exponent stays in a fixed positive interval when
the overlap exponent ranges over a compact interval. [For the stated inputs and conditions](hyp:γmin,γmax,γ,hmin,hlo,hhi), [the asserted conclusion holds](goal). -/
lemma selectedMesh_rank_exponent_mem_interval
    (γmin γmax γ : ℝ) (hmin : 1 < γmin)
    (hlo : γmin ≤ γ) (hhi : γ ≤ γmax) :
    1 / (γmax - 1) ≤ 1 / (γ - 1) ∧
      1 / (γ - 1) ≤ 1 / (γmin - 1) := by
  have hdenmin : 0 < γmin - 1 := by linarith
  have hden : 0 < γ - 1 := by linarith
  have hdenmax : 0 < γmax - 1 := by linarith
  constructor
  · apply (div_le_div_iff₀ hdenmax hden).2
    nlinarith
  · apply (div_le_div_iff₀ hden hdenmin).2
    nlinarith
end CausalSmith.Stat.WeakOverlap
