module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwFutureEndpoint
public import Mathlib.Probability.Moments.Variance

set_option linter.style.longLine false

/-! # Finite covariance sum for partial-history weighting -/

public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

private lemma sum_pow_image_le_range {ι : Type*} [DecidableEq ι]
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

private lemma geom_partial_le_pow_div {L : ℝ} (hL : 1 < L) (k : Nat) :
    ∑ j ∈ Finset.range k, L ^ j ≤ L ^ k / (L - 1) := by
  rw [geom_sum_eq (ne_of_gt hL)]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hL)).2
  have hp : 1 ≤ L ^ k := one_le_pow₀ hL.le
  linarith

private lemma geom_partial_le_inv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (n : Nat) :
    ∑ j ∈ Finset.range n, a ^ j ≤ 1 / (1 - a) := by
  calc
    ∑ j ∈ Finset.range n, a ^ j ≤ ∑' j : Nat, a ^ j := by
      apply Summable.sum_le_tsum
      · intro j _
        positivity
      · exact summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg ha0])
    _ = 1 / (1 - a) := by rw [tsum_geometric_of_lt_one ha0 ha1]; ring

private lemma sum_abs_symmetric_eq_diag_add_two_upper
    {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ι → ℝ) (hsymm : ∀ i j, |f i j| = |f j i|) :
    ∑ i ∈ s, ∑ j ∈ s, |f i j| =
      ∑ i ∈ s, |f i i| + 2 * ∑ i ∈ s, ∑ j ∈ s.filter (i < ·), |f i j| := by
  have hsplit (i : ι) (hi : i ∈ s) :
      ∑ j ∈ s, |f i j| = |f i i| +
        ∑ j ∈ s.filter (fun j ↦ j < i), |f i j| +
          ∑ j ∈ s.filter (fun j ↦ i < j), |f i j| := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun j ↦ j < i)]
    simp only [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun j ↦ i ≤ j) (fun j ↦ i = j)]
    simp only [Finset.filter_filter, and_imp]
    have heq : s.filter (fun j ↦ i ≤ j ∧ i = j) = {i} := by
      ext j
      constructor
      · intro hj
        obtain ⟨_, _, hji⟩ := Finset.mem_filter.mp hj
        simpa using hji.symm
      · intro hj
        have hji : j = i := by simpa using hj
        subst j
        exact Finset.mem_filter.mpr ⟨hi, le_rfl, rfl⟩
    have hgt : s.filter (fun j ↦ i ≤ j ∧ ¬i = j) = s.filter (fun j ↦ i < j) := by
      ext j
      simp [lt_iff_le_and_ne]
    rw [heq, hgt]
    simp
    ring
  rw [Finset.sum_congr rfl (fun i hi ↦ hsplit i hi), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hpast :
      ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ j < i), |f i j| =
        ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i < j), |f i j| := by
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

/-- For [a latent-overlap POMDP experiment](hyp:hM), [a time point](hyp:t)
[at or after the truncation depth](hyp:htk), [the sum of absolute covariances with
all later retained scores is bounded by the overlap and mixing tails](goal). -/
lemma sum_abs_covariance_future_le {T nX nH k : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (t : Fin T) (htk : k ≤ t.val) :
    ∑ u ∈ (Finset.univ.filter (fun u : Fin T ↦ k ≤ u.val)).filter (fun u ↦ t < u),
        |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M)| ≤
      2 * policyFactor zeta ^ (k + 1) / (policyFactor zeta - 1) +
        2 / (1 - mixingAlpha t0) := by
  let I := Finset.univ.filter (fun u : Fin T ↦ k ≤ u.val)
  let U := I.filter (fun u ↦ t < u)
  let A := U.filter (fun u ↦ u.val - t.val ≤ k)
  let D := U.filter (fun u ↦ k + 1 ≤ u.val - t.val)
  have hpart : U = A ∪ D := by
    ext u
    simp only [U, A, D, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      by_cases hlag : u.val - t.val ≤ k
      · exact Or.inl ⟨hu, hlag⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (hu | hu) <;> exact hu.1
  have hdisj : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro u huA huD
    simp only [A, D, Finset.mem_filter] at huA huD
    omega
  rw [show (Finset.univ.filter (fun u : Fin T ↦ k ≤ u.val)).filter (fun u ↦ t < u) = U by rfl,
    hpart, Finset.sum_union hdisj]
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hM.zeta_pos
  have hA :
      ∑ u ∈ A,
          |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M)| ≤
        2 * policyFactor zeta ^ (k + 1) / (policyFactor zeta - 1) := by
    calc
      _ ≤ ∑ u ∈ A, 2 * policyFactor zeta ^ (k + 1 - (u.val - t.val)) := by
        apply Finset.sum_le_sum
        intro u hu
        have huA : u ∈ U ∧ u.val - t.val ≤ k := by
          simpa only [A, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huA.1
        have htu := huU.2
        have hlag := huA.2
        apply abs_covariance_phiwScore_le_overlapDecay hM.sequential_ignorability
          hM.policy_overlap hL.le hM.pomdp_kernel hM.bounded_reward t u htk
          (by omega) (by omega) hlag
      _ = 2 * policyFactor zeta * ∑ u ∈ A, policyFactor zeta ^ (k - (u.val - t.val)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have huA : u ∈ U ∧ u.val - t.val ≤ k := by
          simpa only [A, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huA.1
        have htu := huU.2
        have hlag := huA.2
        rw [show k + 1 - (u.val - t.val) = (k - (u.val - t.val)) + 1 by omega,
          pow_succ]
        ring
      _ ≤ 2 * policyFactor zeta * ∑ j ∈ Finset.range k, policyFactor zeta ^ j := by
        gcongr
        apply sum_pow_image_le_range A (fun u ↦ k - (u.val - t.val)) k
          (policyFactor zeta) (zero_le_one.trans hL.le)
        · intro u hu
          have huA : u ∈ U ∧ u.val - t.val ≤ k := by
            simpa only [A, Finset.mem_filter] using hu
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huA.1
          have htu := huU.2
          have hlag := huA.2
          omega
        · intro u hu v hv huv
          apply Fin.ext
          have huA : u ∈ U ∧ u.val - t.val ≤ k := by
            exact Finset.mem_filter.mp (show u ∈ A from hu)
          have hvA : v ∈ U ∧ v.val - t.val ≤ k := by
            exact Finset.mem_filter.mp (show v ∈ A from hv)
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huA.1
          have hvU : v ∈ I ∧ t < v := by
            simpa only [U, Finset.mem_filter] using hvA.1
          have htu := huU.2
          have htv := hvU.2
          have hlu := huA.2
          have hlv := hvA.2
          simp only at huv
          omega
      _ ≤ 2 * policyFactor zeta * (policyFactor zeta ^ k / (policyFactor zeta - 1)) := by
        gcongr
        exact geom_partial_le_pow_div hL k
      _ = 2 * policyFactor zeta ^ (k + 1) / (policyFactor zeta - 1) := by
        rw [pow_succ]
        ring
  have ha0 : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have ha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hD :
      ∑ u ∈ D,
          |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M)| ≤
        2 / (1 - mixingAlpha t0) := by
    calc
      _ ≤ ∑ u ∈ D, 2 * mixingAlpha t0 ^ (u.val - t.val - k - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        have huD : u ∈ U ∧ k + 1 ≤ u.val - t.val := by
          simpa only [D, Finset.mem_filter] using hu
        have huU : u ∈ I ∧ t < u := by
          simpa only [U, Finset.mem_filter] using huD.1
        have htu := huU.2
        have hlag := huD.2
        apply abs_covariance_phiwScore_le_disjoint_sharp hM t u htk (by omega) hlag
      _ = 2 * ∑ u ∈ D, mixingAlpha t0 ^ (u.val - t.val - k - 1) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ∑ j ∈ Finset.range T, mixingAlpha t0 ^ j := by
        gcongr
        apply sum_pow_image_le_range D (fun u ↦ u.val - t.val - k - 1) T
          (mixingAlpha t0) ha0
        · intro u hu
          omega
        · intro u hu v hv huv
          apply Fin.ext
          have huD : u ∈ U ∧ k + 1 ≤ u.val - t.val := by
            exact Finset.mem_filter.mp (show u ∈ D from hu)
          have hvD : v ∈ U ∧ k + 1 ≤ v.val - t.val := by
            exact Finset.mem_filter.mp (show v ∈ D from hv)
          have huU : u ∈ I ∧ t < u := by
            simpa only [U, Finset.mem_filter] using huD.1
          have hvU : v ∈ I ∧ t < v := by
            simpa only [U, Finset.mem_filter] using hvD.1
          have htu := huU.2
          have htv := hvU.2
          have hlu := huD.2
          have hlv := hvD.2
          simp only at huv
          omega
      _ ≤ 2 * (1 / (1 - mixingAlpha t0)) := by
        gcongr
        exact geom_partial_le_inv ha0 ha1 T
      _ = 2 / (1 - mixingAlpha t0) := by ring
  linarith

/-- The exact finite covariance assembly for the raw partial-history estimator. [the h T condition](hyp:hT); and [the h M condition](hyp:hM); and [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma variance_phiwRaw_le {T nX nH k : Nat} {t0 zeta C : ℝ}
    (hT : 1 ≤ T) (M : RawPomdpExperiment T nX nH)
    (hM : LatentOverlapClass t0 zeta C M) (hk : k ≤ T / 2) :
    variance (phiwRaw k M.b M.e) (obsLaw M) ≤
      (2 / (T : ℝ)) *
        (policyFactor zeta ^ (k + 1) * (1 + 4 / (policyFactor zeta - 1)) +
          4 / (1 - mixingAlpha t0)) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  let I := Finset.univ.filter (fun t : Fin T ↦ k ≤ t.val)
  let L := policyFactor zeta
  let a := mixingAlpha t0
  let B := L ^ (k + 1) * (1 + 4 / (L - 1)) + 4 / (1 - a)
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
    have hLm : 0 < L - 1 := sub_pos.mpr hL
    have ham : 0 < 1 - a := sub_pos.mpr ha1
    positivity
  have hI : I = Finset.Ici ⟨k, by omega⟩ := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  have hIcard : I.card = T - k := by
    rw [hI, Fin.card_Ici]
  have hNpos : 0 < T - k := by omega
  have hNhalf : (T : ℝ) / 2 ≤ (T - k : Nat) := by
    have hn : T ≤ 2 * (T - k) := by omega
    have hnr : (T : ℝ) ≤ 2 * (T - k : Nat) := by exact_mod_cast hn
    nlinarith
  have hsumVar :
      variance (fun w ↦ ∑ t ∈ I, phiwScore k M.b M.e w t) (obsLaw M) ≤
        (T - k : Nat) * B := by
    rw [variance_fun_sum']
    · calc
        ∑ t ∈ I, ∑ u ∈ I,
              covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M) ≤
            ∑ t ∈ I, ∑ u ∈ I,
              |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u)
                (obsLaw M)| := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact le_abs_self _
        _ = ∑ t ∈ I,
              |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · t)
                (obsLaw M)| +
            2 * ∑ t ∈ I, ∑ u ∈ I.filter (fun u ↦ t < u),
              |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u)
                (obsLaw M)| := by
          apply sum_abs_symmetric_eq_diag_add_two_upper
          intro t u
          rw [covariance_comm]
        _ ≤ I.card * L ^ (k + 1) +
            2 * (I.card * (2 * L ^ (k + 1) / (L - 1) + 2 / (1 - a))) := by
          gcongr
          · calc
              _ ≤ ∑ _t ∈ I, L ^ (k + 1) := by
                apply Finset.sum_le_sum
                intro t ht
                have hscore : MemLp (phiwScore k M.b M.e · t) 2 (obsLaw M) :=
                  phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL.le
                    hM.bounded_reward 2 t
                rw [covariance_self (phiwScore_measurable M.b M.e t).aemeasurable,
                  abs_of_nonneg (variance_nonneg _ _), variance_eq_sub hscore]
                exact (sub_le_self _ (sq_nonneg _)).trans
                  (integral_sq_phiwScore_le hM.sequential_ignorability hM.policy_overlap hL.le
                    hM.pomdp_kernel hM.bounded_reward t (by
                      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using ht))
              _ = _ := by simp
          · calc
              _ ≤ ∑ _t ∈ I, (2 * L ^ (k + 1) / (L - 1) + 2 / (1 - a)) := by
                apply Finset.sum_le_sum
                intro t ht
                simpa only [I, L, a] using sum_abs_covariance_future_le hM t (by
                  simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using ht)
              _ = _ := by simp; ring
        _ = (T - k : Nat) * B := by
          rw [hIcard]
          dsimp [B]
          push_cast
          ring
    · intro t ht
      exact phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL.le
        hM.bounded_reward 2 t
  unfold phiwRaw
  change variance (fun w ↦ ((T - k : Nat) : ℝ)⁻¹ *
    ∑ t ∈ I, phiwScore k M.b M.e w t) (obsLaw M) ≤ _
  rw [variance_const_mul]
  calc
    ((T - k : Nat) : ℝ)⁻¹ ^ 2 *
        variance (fun w ↦ ∑ t ∈ I, phiwScore k M.b M.e w t) (obsLaw M) ≤
      ((T - k : Nat) : ℝ)⁻¹ ^ 2 * ((T - k : Nat) * B) := by
        gcongr
    _ = B / (T - k : Nat) := by
      have hn : ((T - k : Nat) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
      field_simp
    _ ≤ (2 / (T : ℝ)) * B := by
      have hTr : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
      have hNr : 0 < ((T - k : Nat) : ℝ) := by exact_mod_cast hNpos
      apply (div_le_iff₀ hNr).2
      rw [show 2 / (T : ℝ) * B * (T - k : Nat) =
        (2 * B * (T - k : Nat)) / (T : ℝ) by ring]
      apply (le_div_iff₀ hTr).2
      nlinarith
    _ = _ := by rfl

end CausalSmith.Stat.PomdpLatentOverlapMinimax
