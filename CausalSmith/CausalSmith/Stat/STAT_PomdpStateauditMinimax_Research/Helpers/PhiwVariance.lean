module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwOverlapCarrier
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CappedRisk
public import Mathlib.Probability.Moments.Variance

/-! # Finite covariance assembly for state-audited PHIW. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory Filter

lemma sum_pow_image_le_range {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Nat) (n : Nat) (r : ℝ)
    (hr : 0 ≤ r) (hf : ∀ i ∈ s, f i < n) (hinj : Set.InjOn f ↑s) :
    ∑ i ∈ s, r ^ f i ≤ ∑ j ∈ Finset.range n, r ^ j := by
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hf i hi)
  · intro j _ _
    positivity

private lemma geom_partial_le_pow_div {L : ℝ} (hL : 1 < L) (d : Nat) :
    ∑ j ∈ Finset.range d, L ^ j ≤ L ^ d / (L - 1) := by
  rw [geom_sum_eq (ne_of_gt hL)]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hL)).2
  have hp : 1 ≤ L ^ d := one_le_pow₀ hL.le
  linarith

lemma geom_partial_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : Nat) :
    ∑ j ∈ Finset.range n, a ^ j ≤ 1 / (1 - a) := by
  calc
    _ ≤ ∑' j : Nat, a ^ j := by
      apply Summable.sum_le_tsum
      · intro j _; positivity
      · exact summable_geometric_of_norm_lt_one
          (by simpa [Real.norm_eq_abs, abs_of_nonneg ha0])
    _ = _ := by rw [tsum_geometric_of_lt_one ha0 ha1]; ring

lemma sum_abs_symmetric_eq_diag_add_two_upper
    {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ι → ℝ) (hsymm : ∀ i j, |f i j| = |f j i|) :
    ∑ i ∈ s, ∑ j ∈ s, |f i j| =
      ∑ i ∈ s, |f i i| + 2 * ∑ i ∈ s, ∑ j ∈ s.filter (i < ·), |f i j| := by
  have hsplit (i : ι) (hi : i ∈ s) :
      ∑ j ∈ s, |f i j| = |f i i| +
        ∑ j ∈ s.filter (fun j => j < i), |f i j| +
          ∑ j ∈ s.filter (fun j => i < j), |f i j| := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun j => j < i)]
    simp only [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun j => i ≤ j)
      (fun j => i = j)]
    simp only [Finset.filter_filter, and_imp]
    have heq : s.filter (fun j => i ≤ j ∧ i = j) = {i} := by
      ext j
      constructor
      · intro hj
        obtain ⟨_, _, hji⟩ := Finset.mem_filter.mp hj
        simpa using hji.symm
      · intro hj
        have hji : j = i := by simpa using hj
        subst j
        exact Finset.mem_filter.mpr ⟨hi, le_rfl, rfl⟩
    have hgt : s.filter (fun j => i ≤ j ∧ ¬i = j) =
        s.filter (fun j => i < j) := by
      ext j
      simp [lt_iff_le_and_ne]
    rw [heq, hgt]
    simp
    ring
  rw [Finset.sum_congr rfl (fun i hi => hsplit i hi), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hpast :
      ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), |f i j| =
        ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), |f i j| := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i < j
    · simp [h, hsymm]
    · simp [h]
  rw [hpast]
  ring

lemma sum_abs_covariance_windowScore_future_le
    {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (t : Fin T) (hdepth : depth ≤ t.val) :
    ∑ u ∈ (Finset.univ.filter (fun u : Fin T => depth ≤ u.val)).filter (fun u => t < u),
      |covariance
        (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
        (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
      2 * policyFactor zeta ^ (depth + 1) / (policyFactor zeta - 1) +
        2 * policyFactor zeta ^ (depth + 1) / (1 - mixingAlpha t0) := by
  let I := Finset.univ.filter (fun u : Fin T => depth ≤ u.val)
  let U := I.filter (fun u => t < u)
  let A := U.filter (fun u => u.val - t.val ≤ depth)
  let D := U.filter (fun u => depth + 1 ≤ u.val - t.val)
  have hpart : U = A ∪ D := by
    ext u
    simp only [U, A, D, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      by_cases hlag : u.val - t.val ≤ depth
      · exact Or.inl ⟨hu, hlag⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (hu | hu) <;> exact hu.1
  have hdisj : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro u huA huD
    simp only [A, D, Finset.mem_filter] at huA huD
    omega
  rw [show (Finset.univ.filter (fun u : Fin T => depth ≤ u.val)).filter
    (fun u => t < u) = U by rfl, hpart, Finset.sum_union hdisj]
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hM.zeta_pos
  have hA :
      ∑ u ∈ A, |covariance
        (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
        (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
        2 * policyFactor zeta ^ (depth + 1) / (policyFactor zeta - 1) := by
    calc
      _ ≤ ∑ u ∈ A, 2 * policyFactor zeta ^
          (depth + 1 - (u.val - t.val)) := by
        apply Finset.sum_le_sum
        intro u hu
        have huA : u ∈ U ∧ u.val - t.val ≤ depth := by
          simpa only [A, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huA.1
        exact abs_covariance_windowScore_le_overlap M hM t u hdepth
          (by omega) (by omega) huA.2
      _ = 2 * policyFactor zeta * ∑ u ∈ A,
          policyFactor zeta ^ (depth - (u.val - t.val)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have huA : u ∈ U ∧ u.val - t.val ≤ depth := by
          simpa only [A, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huA.1
        rw [show depth + 1 - (u.val - t.val) =
          (depth - (u.val - t.val)) + 1 by omega, pow_succ]
        ring
      _ ≤ 2 * policyFactor zeta * ∑ j ∈ Finset.range depth,
          policyFactor zeta ^ j := by
        gcongr
        apply sum_pow_image_le_range A (fun u => depth - (u.val - t.val)) depth
          (policyFactor zeta) (zero_le_one.trans hL.le)
        · intro u hu
          have huA : u ∈ U ∧ u.val - t.val ≤ depth := by
            simpa only [A, Finset.mem_filter] using hu
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huA.1
          omega
        · intro u hu v hv huv
          apply Fin.ext
          have huA : u ∈ U ∧ u.val - t.val ≤ depth := Finset.mem_filter.mp hu
          have hvA : v ∈ U ∧ v.val - t.val ≤ depth := Finset.mem_filter.mp hv
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huA.1
          have hvU : v ∈ I ∧ t < v := by
            simpa only [U, Finset.mem_filter] using hvA.1
          simp only at huv
          omega
      _ ≤ 2 * policyFactor zeta *
          (policyFactor zeta ^ depth / (policyFactor zeta - 1)) := by
        gcongr
        exact geom_partial_le_pow_div hL depth
      _ = _ := by rw [pow_succ]; ring
  have ha0 : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have ha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hD :
      ∑ u ∈ D, |covariance
        (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
        (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
        2 * policyFactor zeta ^ (depth + 1) / (1 - mixingAlpha t0) := by
    calc
      _ ≤ ∑ u ∈ D, 2 * policyFactor zeta ^ (depth + 1) *
          mixingAlpha t0 ^ (u.val - t.val - depth - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        have huD : u ∈ U ∧ depth + 1 ≤ u.val - t.val := by
          simpa only [D, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huD.1
        have hh := abs_covariance_windowScore_le_disjoint M hM hnX hnH t u
          hdepth (by omega) huD.2
        nlinarith
      _ = 2 * policyFactor zeta ^ (depth + 1) *
          ∑ u ∈ D, mixingAlpha t0 ^ (u.val - t.val - depth - 1) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * policyFactor zeta ^ (depth + 1) *
          ∑ j ∈ Finset.range T, mixingAlpha t0 ^ j := by
        gcongr
        apply sum_pow_image_le_range D (fun u => u.val - t.val - depth - 1) T
          (mixingAlpha t0) ha0
        · intro u hu; omega
        · intro u hu v hv huv
          apply Fin.ext
          have huD : u ∈ U ∧ depth + 1 ≤ u.val - t.val := Finset.mem_filter.mp hu
          have hvD : v ∈ U ∧ depth + 1 ≤ v.val - t.val := Finset.mem_filter.mp hv
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huD.1
          have hvU : v ∈ I ∧ t < v := by
            simpa only [U, Finset.mem_filter] using hvD.1
          simp only at huv
          omega
      _ ≤ 2 * policyFactor zeta ^ (depth + 1) * (1 / (1 - mixingAlpha t0)) := by
        gcongr
        exact geom_partial_le_inv ha0 ha1 T
      _ = _ := by ring
  linarith

lemma variance_fullPathPhiwRaw_le
    {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (hT : 1 ≤ T) (M : PomdpModel T nX nH k)
    (hM : HuWagerClass t0 zeta M) (hnX : 1 ≤ nX) (hnH : 1 ≤ nH)
    (hdepth : depth ≤ T / 2) :
    variance (fullPathPhiwRaw depth M) M.law ≤
      (2 / (T : ℝ)) *
        (policyFactor zeta ^ (depth + 1) *
          (1 + 4 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0))) := by
  let I := Finset.univ.filter (fun t : Fin T => depth ≤ t.val)
  let L := policyFactor zeta
  let a := mixingAlpha t0
  let B := L ^ (depth + 1) * (1 + 4 / (L - 1) + 4 / (1 - a))
  have hL : 1 < L := by
    dsimp [L, policyFactor]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hM.zeta_pos
  have ha0 : 0 ≤ a := by dsimp [a, mixingAlpha]; positivity
  have ha1 : a < 1 := by
    dsimp [a, mixingAlpha]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hI : I = Finset.Ici ⟨depth, by omega⟩ := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  have hIcard : I.card = T - depth := by rw [hI, Fin.card_Ici]
  have hNpos : 0 < T - depth := by omega
  have hNhalf : (T : ℝ) / 2 ≤ (T - depth : Nat) := by
    have hn : T ≤ 2 * (T - depth) := by omega
    have hnr : (T : ℝ) ≤ 2 * (T - depth : Nat) := by exact_mod_cast hn
    nlinarith
  let S : Fin T → FullPath T nX nH k → ℝ := fun t w =>
    windowScore M ⟨t.val - depth, by omega⟩ t w
  have hSmem (t : Fin T) (ht : t ∈ I) : MemLp (S t) 2 M.law := by
    have hdt : depth ≤ t.val := by
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    have hh := observed_phiwScore_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap t hdt
    apply (memLp_congr_ae ?_).2 hh
    filter_upwards with w
    exact (phiwScore_observedRecord_eq_windowScore M t hdt w).symm
  have hsumVar : variance (fun w => ∑ t ∈ I, S t w) M.law ≤
      (T - depth : Nat) * B := by
    rw [variance_fun_sum']
    · calc
        _ ≤ ∑ t ∈ I, ∑ u ∈ I, |covariance (S t) (S u) M.law| := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact le_abs_self _
        _ = ∑ t ∈ I, |covariance (S t) (S t) M.law| +
            2 * ∑ t ∈ I, ∑ u ∈ I.filter (fun u => t < u),
              |covariance (S t) (S u) M.law| := by
          apply sum_abs_symmetric_eq_diag_add_two_upper
          intro t u
          rw [covariance_comm]
        _ ≤ I.card * L ^ (depth + 1) +
            2 * (I.card * (2 * L ^ (depth + 1) / (L - 1) +
              2 * L ^ (depth + 1) / (1 - a))) := by
          gcongr
          · calc
              _ ≤ ∑ _t ∈ I, L ^ (depth + 1) := by
                apply Finset.sum_le_sum
                intro t ht
                have hdt : depth ≤ t.val := by
                  simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using ht
                have hsquare := integral_windowScore_sq_le M hM.pomdp
                  hM.randomization hM.moment hM.overlap hM.start
                  ⟨t.val - depth, by omega⟩ t (Nat.sub_le _ _)
                have hmem := hSmem t ht
                rw [covariance_self hmem.1.aemeasurable,
                  abs_of_nonneg (variance_nonneg _ _),
                  variance_eq_sub hmem]
                exact (sub_le_self _ (sq_nonneg _)).trans (by
                  simpa [S, L, Nat.sub_sub_self hdt] using hsquare)
              _ = _ := by simp
          · calc
              _ ≤ ∑ _t ∈ I, (2 * L ^ (depth + 1) / (L - 1) +
                    2 * L ^ (depth + 1) / (1 - a)) := by
                apply Finset.sum_le_sum
                intro t ht
                simpa only [I, S, L, a] using
                  sum_abs_covariance_windowScore_future_le M hM hnX hnH t
                    (by simpa only [I, Finset.mem_filter, Finset.mem_univ,
                      true_and] using ht)
              _ = _ := by simp; ring
        _ = (T - depth : Nat) * B := by
          rw [hIcard]
          dsimp [B]
          push_cast
          ring
    · exact hSmem
  have hraw : fullPathPhiwRaw depth M = fun w =>
      (((T - depth : Nat) : ℝ)⁻¹) * ∑ t ∈ I, S t w := by
    funext w
    unfold fullPathPhiwRaw
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hdt : depth ≤ t.val := by
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    exact phiwScore_observedRecord_eq_windowScore M t hdt w
  rw [hraw, variance_const_mul]
  calc
    ((T - depth : Nat) : ℝ)⁻¹ ^ 2 *
        variance (fun w => ∑ t ∈ I, S t w) M.law ≤
      ((T - depth : Nat) : ℝ)⁻¹ ^ 2 * ((T - depth : Nat) * B) := by
        gcongr
    _ = B / (T - depth : Nat) := by
      have hn : ((T - depth : Nat) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hNpos)
      field_simp
    _ ≤ (2 / (T : ℝ)) * B := by
      have hTr : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
      have hNr : 0 < ((T - depth : Nat) : ℝ) := by exact_mod_cast hNpos
      apply (div_le_iff₀ hNr).2
      rw [show 2 / (T : ℝ) * B * (T - depth : Nat) =
        (2 * B * (T - depth : Nat)) / (T : ℝ) by ring]
      apply (le_div_iff₀ hTr).2
      nlinarith
    _ = _ := by rfl

lemma clipUnit_sq_sub_le {u theta : ℝ} (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    (clipUnit u - theta) ^ 2 ≤ (u - theta) ^ 2 := by
  rcases htheta with ⟨htheta_lower, htheta_upper⟩
  by_cases hu_lower : u < -1
  · rw [clipUnit, min_eq_right (by linarith), max_eq_left (le_of_lt hu_lower)]
    nlinarith
  by_cases hu_upper : 1 < u
  · rw [clipUnit, min_eq_left (le_of_lt hu_upper), max_eq_right (by norm_num)]
    nlinarith
  rw [clipUnit, min_eq_right (by linarith), max_eq_right (by linarith)]

lemma sqRisk_clipUnit_le_variance_add_bias_sq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {X : Omega → ℝ} {theta : ℝ}
    (hXmeas : Measurable X) (hX : MemLp X 2 mu)
    (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    Causalean.Stat.sqRisk mu (fun omega => clipUnit (X omega)) theta ≤
      variance X mu + (∫ omega, X omega ∂mu - theta) ^ 2 := by
  have hdiff : MemLp (fun omega => X omega - theta) 2 mu := by
    change MemLp (X - fun _ => theta) 2 mu
    exact hX.sub (memLp_const theta)
  have hdiffInt : Integrable (fun omega => (X omega - theta) ^ 2) mu := by
    simpa only [Pi.pow_apply] using hdiff.integrable_sq
  have hclipInt : Integrable (fun omega => (clipUnit (X omega) - theta) ^ 2) mu := by
    apply hdiffInt.mono'
    · unfold clipUnit
      fun_prop
    · filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact clipUnit_sq_sub_le htheta
  have hriskRaw :
      (∫ omega, (X omega - theta) ^ 2 ∂mu) =
        variance X mu + (∫ omega, X omega ∂mu - theta) ^ 2 := by
    rw [variance_eq_sub hX]
    have hXint : Integrable X mu := hX.integrable one_le_two
    have hXsq : Integrable (fun omega => X omega ^ 2) mu := hX.integrable_sq
    calc
      _ = ∫ omega, (X omega ^ 2 - 2 * theta * X omega + theta ^ 2) ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        ring
      _ = (∫ omega, X omega ^ 2 ∂mu) -
          2 * theta * (∫ omega, X omega ∂mu) + theta ^ 2 := by
        (integral_linearity; simp)
      _ = ((∫ omega, (X ^ 2) omega ∂mu) - (∫ omega, X omega ∂mu) ^ 2) +
          (∫ omega, X omega ∂mu - theta) ^ 2 := by
        simp only [Pi.pow_apply]
        ring
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ omega, (X omega - theta) ^ 2 ∂mu :=
      integral_mono hclipInt hdiffInt (fun omega => clipUnit_sq_sub_le htheta)
    _ = _ := hriskRaw

lemma fullPathPhiw_clipped_risk_le
    {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (hT : 1 ≤ T) (M : PomdpModel T nX nH k)
    (hM : HuWagerClass t0 zeta M) (hnX : 1 ≤ nX) (hnH : 1 ≤ nH)
    (hdepth : depth ≤ T / 2) :
    Causalean.Stat.sqRisk M.law (fun w => clipUnit (fullPathPhiwRaw depth M w))
        (targetValue M) ≤
      4 * mixingAlpha t0 ^ (2 * depth) +
      (2 / (T : ℝ)) * (policyFactor zeta ^ (depth + 1) *
        (1 + 4 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0))) := by
  have hrawMeas : Measurable (fullPathPhiwRaw depth M) := by
    unfold fullPathPhiwRaw phiwScore observedRecord obsProj currentState actionAt rewardAt
    fun_prop
  have hrawLp : MemLp (fullPathPhiwRaw depth M) 2 M.law := by
    unfold fullPathPhiwRaw
    apply MemLp.const_mul
    apply memLp_finsetSum
    intro t ht
    exact observed_phiwScore_memLp_two M hM.pomdp hM.randomization hM.moment
      hM.overlap t (Finset.mem_filter.mp ht).2
  have hrisk := sqRisk_clipUnit_le_variance_add_bias_sq M.law hrawMeas hrawLp
    (targetValue_mem_unit_hw hM)
  have hvar := variance_fullPathPhiwRaw_le hT M hM hnX hnH hdepth
  have hbias := fullPathPhiwRaw_bias_le M hM hnX hnH hT hdepth
  have hbiasSq :
      (∫ w, fullPathPhiwRaw depth M w ∂M.law - targetValue M) ^ 2 ≤
        4 * mixingAlpha t0 ^ (2 * depth) := by
    have ha0 : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg
      (∫ w, fullPathPhiwRaw depth M w ∂M.law - targetValue M))
      (by positivity : 0 ≤ 2 * mixingAlpha t0 ^ depth)).2 hbias
    rw [sq_abs] at hsquare
    calc
      _ ≤ (2 * mixingAlpha t0 ^ depth) ^ 2 := hsquare
      _ = _ := by
        rw [show mixingAlpha t0 ^ (2 * depth) =
          (mixingAlpha t0 ^ depth) ^ 2 by rw [← pow_mul]; congr 1; omega]
        ring
  exact hrisk.trans (add_le_add hvar hbiasSq) |>.trans_eq (by ring)

lemma observedPhiwEstimator_comp_obsProj {T nX nH k : Nat}
    (t0 zeta : ℝ) (M : PomdpModel T nX nH k) (w : FullPath T nX nH k) :
    observedPhiwEstimator (nH := nH) t0 zeta M.b M.e (obsProj w) =
      clipUnit (fullPathPhiwRaw (historyDepth T t0 zeta) M w) := by
  rfl

lemma sqRisk_observed_phiw_eq_fullPath {T nX nH k : Nat}
    (t0 zeta theta : ℝ) (M : PomdpModel T nX nH k) :
    Causalean.Stat.sqRisk (obsLaw M)
        (observedPhiwEstimator (nH := nH) t0 zeta M.b M.e) theta =
      Causalean.Stat.sqRisk M.law
        (fun w => clipUnit (fullPathPhiwRaw (historyDepth T t0 zeta) M w)) theta := by
  have hobs : Measurable (obsProj : FullPath T nX nH k → ObsPath T nX k) := by
    unfold obsProj currentState actionAt rewardAt
    fun_prop
  have hmap := Causalean.Stat.sqRisk_map_affinePullback
    (law := M.law) (phi := obsProj) (a := (1 : ℝ)) (b := 0) (theta := theta)
    (targetEst := observedPhiwEstimator (nH := nH) t0 zeta M.b M.e)
    one_ne_zero hobs (measurable_observedPhiwEstimator t0 zeta M.b M.e)
  simp only [one_pow, one_mul, add_zero] at hmap
  have hpull : Causalean.Stat.affinePullbackEstimator obsProj 1 0
      (observedPhiwEstimator (T := T) (nH := nH) t0 zeta M.b M.e) =
      fun w => clipUnit (fullPathPhiwRaw (historyDepth T t0 zeta) M w) := by
    funext w
    unfold Causalean.Stat.affinePullbackEstimator
    rw [observedPhiwEstimator_comp_obsProj]
    ring
  rw [hpull] at hmap
  simpa [obsLaw] using hmap.symm

lemma historyDepth_rate {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c : ℝ, 0 < c ∧ ∃ TStar : Nat, ∀ T ≥ TStar,
      mixingAlpha t0 ^ (2 * historyDepth T t0 zeta) +
        (policyFactor zeta ^ (historyDepth T t0 zeta + 1)) / (T : ℝ) ≤
      c * (T : ℝ) ^ (-rateExponent t0 zeta) := by
  let D : ℝ := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by
    simp [mixingAlpha]
  have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
  have hlogInvAlpha : Real.log (1 / mixingAlpha t0) = 1 / t0 := by
    rw [Real.log_div (by norm_num) (ne_of_gt halpha0), Real.log_one, hlogalpha]
    ring
  have hD : D = 2 / t0 + zeta := by
    dsimp [D]
    rw [hlogInvAlpha, hlogL]
    ring
  have hDpos : 0 < D := by rw [hD]; positivity
  have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
    rw [rateExponent, hD]
    field_simp
  have heventReal : ∀ᶠ x : ℝ in atTop, |Real.log x| ≤ (D / 2) * |x| := by
    have h := Real.isLittleO_log_id_atTop.bound (show 0 < D / 2 by positivity)
    simpa [Real.norm_eq_abs] using h
  have heventNat : ∀ᶠ T : Nat in atTop,
      |Real.log (T : ℝ)| ≤ (D / 2) * |(T : ℝ)| :=
    tendsto_natCast_atTop_atTop.eventually heventReal
  rw [eventually_atTop] at heventNat
  obtain ⟨T0, hT0⟩ := heventNat
  let c : ℝ := Real.exp (2 / t0) + Real.exp zeta
  refine ⟨c, by dsimp [c]; positivity, max T0 1, ?_⟩
  intro T hT
  have hlogbound := hT0 T ((le_max_left T0 1).trans hT)
  have hT1 : 1 ≤ T := (le_max_right T0 1).trans hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  have hlog0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
  have hx0 : 0 ≤ Real.log (T : ℝ) / D := div_nonneg hlog0 hDpos.le
  have hxle : Real.log (T : ℝ) / D ≤ (T : ℝ) / 2 := by
    rw [abs_of_nonneg hlog0, abs_of_nonneg hTpos.le] at hlogbound
    apply (div_le_iff₀ hDpos).2
    nlinarith
  let k : Nat := ⌊Real.log (T : ℝ) / D⌋₊
  have hkT : k ≤ T / 2 := by
    apply Nat.le_div_iff_mul_le (by norm_num : 0 < 2) |>.2
    rw [Nat.mul_comm]
    apply_mod_cast (show (2 : ℝ) * k ≤ T from ?_)
    have hkx : (k : ℝ) ≤ Real.log (T : ℝ) / D := Nat.floor_le hx0
    nlinarith
  have hdepth : historyDepth T t0 zeta = k := by
    unfold historyDepth
    rw [show 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta) = D by rfl]
    rw [Int.floor_toNat]
    exact Nat.min_eq_right hkT
  have hk_lower : Real.log (T : ℝ) / D - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
  have hk_upper : (k : ℝ) ≤ Real.log (T : ℝ) / D := Nat.floor_le hx0
  have hbarg : ((2 * k : Nat) : ℝ) * (-(1 / t0)) ≤
      2 / t0 + Real.log (T : ℝ) * (-rateExponent t0 zeta) := by
    have hm := mul_le_mul_of_nonpos_left (le_of_lt hk_lower)
      (neg_nonpos.mpr (by positivity : 0 ≤ 2 / t0))
    rw [hbeta]
    push_cast
    calc
      2 * (k : ℝ) * (-(1 / t0)) = (-(2 / t0)) * (k : ℝ) := by ring
      _ ≤ (-(2 / t0)) * (Real.log (T : ℝ) / D - 1) := hm
      _ = 2 / t0 + Real.log (T : ℝ) * (-(2 / t0 / D)) := by ring
  have hbias : mixingAlpha t0 ^ (2 * k) ≤
      Real.exp (2 / t0) * (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [← Real.exp_log halpha0, ← Real.exp_nat_mul, hlogalpha,
      Real.rpow_def_of_pos hTpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hbarg
  have hvarg : (((k + 1 : Nat) : ℝ) * zeta - Real.log (T : ℝ)) ≤
      zeta + Real.log (T : ℝ) * (-rateExponent t0 zeta) := by
    have hm := mul_le_mul_of_nonneg_right hk_upper hzeta.le
    rw [hbeta]
    push_cast
    calc
      ((k : ℝ) + 1) * zeta - Real.log (T : ℝ) ≤
          (Real.log (T : ℝ) / D + 1) * zeta - Real.log (T : ℝ) := by
        nlinarith
      _ = zeta + Real.log (T : ℝ) * (-(2 / t0 / D)) := by
        rw [hD]
        field_simp <;> ring
  have hvar : policyFactor zeta ^ (k + 1) / (T : ℝ) ≤
      Real.exp zeta * (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [policyFactor, ← Real.exp_nat_mul, div_eq_mul_inv,
      show (T : ℝ)⁻¹ = Real.exp (-Real.log (T : ℝ)) by
        rw [Real.exp_neg, Real.exp_log hTpos],
      ← Real.exp_add, Real.rpow_def_of_pos hTpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hvarg
  rw [hdepth]
  calc
    mixingAlpha t0 ^ (2 * k) + policyFactor zeta ^ (k + 1) / (T : ℝ) ≤
        Real.exp (2 / t0) * (T : ℝ) ^ (-rateExponent t0 zeta) +
          Real.exp zeta * (T : ℝ) ^ (-rateExponent t0 zeta) := add_le_add hbias hvar
    _ = c * (T : ℝ) ^ (-rateExponent t0 zeta) := by simp [c]; ring

lemma audited_phiw_eventual_rate {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ A : ℝ, 0 < A ∧ ∃ TStar : Nat, ∀ T ≥ TStar,
      ∀ (eta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : HWIndex T t0 zeta,
      Causalean.Stat.sqRisk (auditedLaw eta i.raw)
          (phiwEstimator t0 zeta i.raw.b i.raw.e) (targetValue i.raw) ≤
        A * (T : ℝ) ^ (-rateExponent t0 zeta) := by
  obtain ⟨c, hc, TStar, hrate⟩ := historyDepth_rate ht0 hzeta
  let C := 1 + 4 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)
  let K := 4 + 2 * C
  let A := K * c
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hzeta
  have halpha : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A, mul_pos hK hc, max TStar 1, ?_⟩
  intro T hT eta heta i
  have hT1 : 1 ≤ T := (le_max_right TStar 1).trans hT
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  let depth := historyDepth T t0 zeta
  have hdepth : depth ≤ T / 2 := by
    unfold depth historyDepth
    exact Nat.min_le_left _ _
  have hfull := fullPathPhiw_clipped_risk_le hT1 i.raw i.mem i.nX_pos i.nH_pos hdepth
  have hobs := sqRisk_observed_phiw_eq_fullPath t0 zeta (targetValue i.raw) i.raw
  have haud := sqRisk_audited_phiw_eq_observed i.raw eta heta t0 zeta (targetValue i.raw)
  rw [haud, hobs]
  have hr := hrate T ((le_max_left TStar 1).trans hT)
  have hb0 : 0 ≤ mixingAlpha t0 ^ (2 * depth) := by
    apply pow_nonneg
    unfold mixingAlpha
    positivity
  have hb0' : 0 ≤ mixingAlpha t0 ^ (depth * 2) := by
    apply pow_nonneg
    unfold mixingAlpha
    positivity
  have hv0 : 0 ≤ policyFactor zeta ^ (depth + 1) / (T : ℝ) :=
    div_nonneg (pow_nonneg (by unfold policyFactor; positivity) _) hTr.le
  have hv0' : 0 ≤ (T : ℝ)⁻¹ * policyFactor zeta * policyFactor zeta ^ depth := by
    positivity
  calc
    _ ≤ 4 * mixingAlpha t0 ^ (2 * depth) +
        (2 / (T : ℝ)) * (policyFactor zeta ^ (depth + 1) * C) := by
      simpa [depth, C] using hfull
    _ ≤ K * (mixingAlpha t0 ^ (2 * depth) +
        policyFactor zeta ^ (depth + 1) / (T : ℝ)) := by
      dsimp [K]
      ring_nf
      nlinarith [mul_nonneg hC.le hb0', hv0']
    _ ≤ K * (c * (T : ℝ) ^ (-rateExponent t0 zeta)) :=
      mul_le_mul_of_nonneg_left hr hK.le
    _ = A * (T : ℝ) ^ (-rateExponent t0 zeta) := by dsimp [A]; ring

noncomputable def phiwAuditedEstimator (T : Nat) (t0 zeta : ℝ) :
    AuditedEstimator T :=
  ⟨fun nX nH k b e => phiwEstimator (nH := nH) t0 zeta b e, by
    constructor
    · intro nX nH k b e
      unfold phiwEstimator phiwScore clipUnit
      fun_prop
    · intro nX nH k b e w
      unfold phiwEstimator clipUnit
      constructor
      · exact le_max_left _ _
      · apply max_le (by norm_num)
        exact min_le_left _ _⟩

lemma audited_phiw_rate {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : Nat), 1 ≤ T →
      ∀ (eta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : HWIndex T t0 zeta,
      Causalean.Stat.sqRisk (auditedLaw eta i.raw)
          (phiwEstimator t0 zeta i.raw.b i.raw.e) (targetValue i.raw) ≤
        A * (T : ℝ) ^ (-rateExponent t0 zeta) := by
  obtain ⟨Ae, hAe, S, hevent⟩ := audited_phiw_eventual_rate ht0 hzeta
  let beta := rateExponent t0 zeta
  let A := max Ae (4 * (S : ℝ) ^ beta)
  have hbeta : 0 < beta := by
    dsimp [beta, rateExponent]
    positivity
  refine ⟨A, lt_of_lt_of_le hAe (le_max_left _ _), ?_⟩
  intro T hT eta heta i
  by_cases hlarge : S ≤ T
  · exact (hevent T hlarge eta heta i).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg T) _))
  · have hTS : T ≤ S := by omega
    have hTr : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
    have hSr : 0 ≤ (S : ℝ) := Nat.cast_nonneg S
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg T)
      (show (T : ℝ) ≤ (S : ℝ) by exact_mod_cast hTS) hbeta.le
    have hinv : 0 ≤ (T : ℝ) ^ (-beta) := Real.rpow_nonneg hTr.le _
    have hmul := mul_le_mul_of_nonneg_right hp hinv
    have hone : (T : ℝ) ^ beta * (T : ℝ) ^ (-beta) = 1 := by
      rw [← Real.rpow_add hTr]
      simp
    rw [hone] at hmul
    have hfour : 4 ≤ (4 * (S : ℝ) ^ beta) * (T : ℝ) ^ (-beta) := by
      nlinarith
    have hrisk : Causalean.Stat.sqRisk (auditedLaw eta i.raw)
        (phiwEstimator t0 zeta i.raw.b i.raw.e) (targetValue i.raw) ≤ 4 := by
      simpa [auditedRisk, phiwAuditedEstimator] using
        auditedRisk_le_four heta (phiwAuditedEstimator T t0 zeta) i
    calc
      _ ≤ 4 := hrisk
      _ ≤ (4 * (S : ℝ) ^ beta) * (T : ℝ) ^ (-beta) := hfour
      _ ≤ A * (T : ℝ) ^ (-beta) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hinv
      _ = _ := by rfl

lemma auditedMinimaxRisk_upper_rate {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : Nat), 1 ≤ T →
      ∀ (eta : ℝ), eta ∈ Set.Icc (0 : ℝ) 1 →
      auditedMinimaxRisk T t0 zeta eta ≤
        A * (T : ℝ) ^ (-rateExponent t0 zeta) ∧
      (∀ i : HWIndex T t0 zeta,
        Causalean.Stat.sqRisk (auditedLaw eta i.raw)
          (phiwEstimator t0 zeta i.raw.b i.raw.e) (targetValue i.raw) ≤
            A * (T : ℝ) ^ (-rateExponent t0 zeta)) := by
  obtain ⟨A, hA, hphiw⟩ := audited_phiw_rate ht0 hzeta
  refine ⟨A, hA, ?_⟩
  intro T hT eta heta
  have hi := hphiw T hT eta heta
  constructor
  · unfold auditedMinimaxRisk
    calc
      Causalean.Stat.minimaxValueReal
          (auditedRisk (T := T) (t0 := t0) (zeta := zeta) eta) ≤
        Causalean.Stat.worstCaseRiskReal
          (auditedRisk (T := T) (t0 := t0) (zeta := zeta) eta)
          (phiwAuditedEstimator T t0 zeta) :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
          (fun est i => auditedRisk_nonneg est i) _
      _ ≤ A * (T : ℝ) ^ (-rateExponent t0 zeta) := by
        by_cases hidx : Nonempty (HWIndex T t0 zeta)
        · letI := hidx
          apply Causalean.Stat.worstCaseRisk_le
          intro i
          simpa [auditedRisk, phiwAuditedEstimator] using hi i
        · letI : IsEmpty (HWIndex T t0 zeta) := not_nonempty_iff.mp hidx
          rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
          exact mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg T) _)
  · exact hi


end CausalSmith.Stat.PomdpStateauditMinimax
