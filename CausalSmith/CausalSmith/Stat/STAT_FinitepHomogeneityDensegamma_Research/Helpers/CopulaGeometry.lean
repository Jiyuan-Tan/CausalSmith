module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaSeparation
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.SmoothedTentSmoothness
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentIntegrals

/-! Interpolation error and geometric lower second moment for the copula paired tent. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The opposite adjacent tents have Lipschitz constant two, including their common zero. [This is the stated conclusion](goal). -/
-- @node: opposite_tents_abs_sub_le
lemma opposite_tents_abs_sub_le (x y : ℝ) :
    |(tentBase x-tentBase (x-1))-(tentBase y-tentBase (y-1))| ≤ 2*|x-y| := by
  have hleft (t : ℝ) (ht : t ≤ 1) : tentBase (t-1) = 0 :=
    tentBase_zero_outside _ (Or.inl (by linarith))
  have hright (t : ℝ) (ht : 1 ≤ t) : tentBase t = 0 :=
    tentBase_zero_outside _ (Or.inr ht)
  have hcross (x y : ℝ) (hx : x ≤ 1) (hy : 1 ≤ y) :
      |(tentBase x-tentBase (x-1))-(tentBase y-tentBase (y-1))| ≤ 2*|x-y| := by
    rw [hleft x hx, hright y hy]
    have h0 := tentBase_abs_sub_le x 1
    have h1 := tentBase_abs_sub_le (y-1) 0
    simp only [show tentBase 1 = 0 by norm_num [tentBase],
      show tentBase 0 = 0 by norm_num [tentBase], sub_zero] at h0 h1
    rw [abs_of_nonpos (by linarith : x-1 ≤ 0)] at h0
    rw [abs_of_nonneg (by linarith : 0 ≤ y-1)] at h1
    rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
    have hr := abs_add_le (tentBase x) (tentBase (y-1))
    simp only [sub_zero, zero_sub, sub_neg_eq_add] at *
    linarith
  by_cases hx : x ≤ 1
  · by_cases hy : y ≤ 1
    · rw [hleft x hx, hleft y hy, sub_zero, sub_zero]
      exact tentBase_abs_sub_le x y
    · exact hcross x y hx (le_of_not_ge hy)
  · by_cases hy : y ≤ 1
    · rw [abs_sub_comm (tentBase x-tentBase (x-1)), abs_sub_comm x]
      exact hcross y x hy (le_of_not_ge hx)
    · rw [hright x (le_of_not_ge hx), hright y (le_of_not_ge hy)]
      simpa only [zero_sub, neg_sub_neg, abs_sub_comm, sub_sub_sub_cancel_right] using
        tentBase_abs_sub_le (x-1) (y-1)

/-- A signed paired coarse bump has the sharp rank-scaled Lipschitz constant. [This is the stated conclusion](goal). -/
-- @node: paired_bump_abs_sub_le_two
lemma paired_bump_abs_sub_le_two (M : ℕ) (σ : Fin (M/2) → Bool)
    (j : Fin (M/2)) (x y : ℝ) :
    |signVal (σ j)*(tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)))-
      signVal (σ j)*(tentBase ((M:ℝ)*y-2*j.val)-tentBase ((M:ℝ)*y-(2*j.val+1)))| ≤
      2*(M:ℝ)*|x-y| := by
  have hs : |signVal (σ j)| = 1 := by cases σ j <;> norm_num [signVal]
  rw [← mul_sub, abs_mul, hs, one_mul]
  have hb := opposite_tents_abs_sub_le ((M:ℝ)*x-2*j.val) ((M:ℝ)*y-2*j.val)
  rw [show (M:ℝ)*x-2*j.val-1 = (M:ℝ)*x-(2*j.val+1) by ring,
    show (M:ℝ)*y-2*j.val-1 = (M:ℝ)*y-(2*j.val+1) by ring,
    show (M:ℝ)*x-2*j.val-((M:ℝ)*y-2*j.val) = (M:ℝ)*(x-y) by ring,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ M)] at hb
  simpa only [mul_assoc] using hb

/-- Disjoint support keeps the Lipschitz bound independent of the number of pairs. [This is the stated conclusion](goal). -/
-- @node: coarseTent_abs_sub_le_four
lemma coarseTent_abs_sub_le_four (M : ℕ) (σ : Fin (M/2) → Bool) (x y : ℝ) :
    |coarseTent M σ x-coarseTent M σ y| ≤ 4*(M:ℝ)*|x-y| := by
  classical
  let f := fun (z : ℝ) (j : Fin (M/2)) => signVal (σ j)*
    (tentBase ((M:ℝ)*z-2*j.val)-tentBase ((M:ℝ)*z-(2*j.val+1)))
  let S := fun z => Finset.univ.filter (fun j => f z j ≠ 0)
  have hc (z : ℝ) : (S z).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    have hj' : f z j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hk' : f z k ≠ 0 := (Finset.mem_filter.mp hk).2
    apply paired_bump_unique M z j k
    · intro h; apply hj'; simp [f, h]
    · intro h; apply hk'; simp [f, h]
  have hs : (S x ∪ S y).card ≤ 2 :=
    (Finset.card_union_le _ _).trans (by linarith [hc x, hc y])
  have he : coarseTent M σ x-coarseTent M σ y =
      ∑ j ∈ S x ∪ S y, (f x j-f y j) := by
    unfold coarseTent
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hx : f x j = 0 := by
      by_contra h
      exact hj (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hy : f y j = 0 := by
      by_contra h
      exact hj (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    change f x j-f y j = 0
    rw [hx, hy, sub_self]
  rw [he]
  calc
    _ ≤ ∑ j ∈ S x ∪ S y, |f x j-f y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S x ∪ S y, 2*(M:ℝ)*|x-y| := by
      apply Finset.sum_le_sum
      intro j _
      exact paired_bump_abs_sub_le_two M σ j x y
    _ = ((S x ∪ S y).card:ℝ)*(2*(M:ℝ)*|x-y|) := by simp
    _ ≤ 2*(2*(M:ℝ)*|x-y|) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
      positivity
    _ = _ := by ring


/-- Convex squared-frame interpolation differs from the coarse tent by at most four mesh widths. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_uniform_approximation
lemma smoothedTent_uniform_approximation (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (x : unitInterval) :
    |smoothedTent K M σ x-coarseTent M σ x| ≤ 4*(M:ℝ)/K := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have he : smoothedTent K M σ x-coarseTent M σ x =
      ∑ i : Fin (K+1), (coarseTent M σ ((i:ℝ)/K)-coarseTent M σ x)*frameCoord K i x^2 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, frame_partition K hK x, mul_one]
    rfl
  rw [he]
  calc
    _ ≤ ∑ i : Fin (K+1), |(coarseTent M σ ((i:ℝ)/K)-coarseTent M σ x)*frameCoord K i x^2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (K+1), (4*(M:ℝ)/K)*frameCoord K i x^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hz : frameCoord K i x = 0
      · simp [hz]
      have hd := (frameCoord_nonzero_distance K hK i x hz).le
      have hdist : |(i:ℝ)/K-(x:ℝ)| ≤ 1/(K:ℝ) := by
        apply (le_div_iff₀ hk).mpr
        have heq : |(i:ℝ)/(K:ℝ)-(x:ℝ)| * (K:ℝ) = |(K:ℝ)*(x:ℝ)-(i:ℝ)| := by
          calc
            _ = |((i:ℝ)/(K:ℝ)-(x:ℝ))*(K:ℝ)| := by rw [abs_mul, abs_of_pos hk]
            _ = |(i:ℝ)-(K:ℝ)*(x:ℝ)| := by congr 1; field_simp
            _ = _ := abs_sub_comm _ _
        rwa [heq]
      rw [abs_mul, abs_of_nonneg (sq_nonneg (frameCoord K i x))]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ 4*(M:ℝ)*|((i:ℝ)/K)-(x:ℝ)| := coarseTent_abs_sub_le_four M σ _ _
        _ ≤ 4*(M:ℝ)*(1/K) := mul_le_mul_of_nonneg_left hdist (by positivity)
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum, frame_partition K hK x, mul_one]

/-- Fine rank at least sixteen times coarse rank makes the interpolation error at most one quarter. This statement assumes [the hK condition](hyp:hK), [the hKM condition](hyp:hKM). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_error_le_quarter
lemma smoothedTent_error_le_quarter (K M : ℕ) (hK : 0 < K) (hKM : 16*M ≤ K)
    (σ : Fin (M/2) → Bool) (x : unitInterval) :
    |smoothedTent K M σ x-coarseTent M σ x| ≤ 1/4 := by
  apply (smoothedTent_uniform_approximation K M hK σ x).trans
  apply (div_le_iff₀ (by exact_mod_cast hK : (0:ℝ) < K)).mpr
  have h : (16:ℝ)*M ≤ K := by exact_mod_cast hKM
  linarith

/-- The exact coarse-tent second moment and the mesh error force a positive interpolated second moment. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hKM condition](hyp:hKM). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_second_moment_lower
lemma smoothedTent_second_moment_lower (K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (heven : 2*(M/2) = M) (hKM : 16*M ≤ K) (σ : Fin (M/2) → Bool) :
    (1:ℝ)/16 ≤ ∫ x : unitInterval, (smoothedTent K M σ x)^2 ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hs : Integrable (fun x : unitInterval => (smoothedTent K M σ x)^2) design := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  have hb : (∫ x : unitInterval, (coarseTent M σ x)^2 ∂design) ≤
      ∫ x : unitInterval, 2*(smoothedTent K M σ x)^2+(1:ℝ)/8 ∂design := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((hs.const_mul 2).add (integrable_const _))
    apply Filter.Eventually.of_forall
    intro x
    change (coarseTent M σ x)^2 ≤ 2*(smoothedTent K M σ x)^2+(1:ℝ)/8
    have he := smoothedTent_error_le_quarter K M hK hKM σ x
    have he2 : (smoothedTent K M σ x-coarseTent M σ x)^2 ≤ (1:ℝ)/16 := by
      have hh := abs_le.mp he
      nlinarith
    nlinarith [sq_nonneg (smoothedTent K M σ x +
      (smoothedTent K M σ x-coarseTent M σ x))]
  rw [(coarseTent_design_moments M hM heven σ).2,
    integral_add (hs.const_mul 2) (integrable_const _), integral_const_mul] at hb
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hb
  linarith

/-- A nontrivial dyadic coarse rank is even, so the paired field has its full second moment. This statement assumes [the hranks condition](hyp:hranks). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_second_moment_lower_of_legalityRanks
lemma smoothedTent_second_moment_lower_of_legalityRanks (v : Params) (K M : ℕ)
    (hranks : LegalityRanks v K M) (σ : Fin (M/2) → Bool) :
    (1:ℝ)/16 ≤ ∫ x : unitInterval, (smoothedTent K M σ x)^2 ∂design := by
  have hM : 0 < M := by have := hranks.2.2.2.1; omega
  have hK : 0 < K := by have := hranks.2.2.1; omega
  have heven : 2*(M/2) = M := by
    obtain ⟨m, hm⟩ := hranks.2.1
    have hmpos : 0 < m := by
      by_contra hh
      have hmzero : m = 0 := by omega
      have hge := hranks.2.2.2.1
      simp [hm, hmzero] at hge
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    rw [hm, pow_succ]
    omega
  exact smoothedTent_second_moment_lower K M hK hM heven hranks.2.2.1 σ

end CausalSmith.Stat.FinitepHomogeneityDensegamma
