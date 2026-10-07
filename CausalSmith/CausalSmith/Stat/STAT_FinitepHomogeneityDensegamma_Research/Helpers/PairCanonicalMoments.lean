module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairSampleMoments
public import Mathlib.Probability.Moments.Covariance

/-! Canonical pair cross moments and their cancellation at shared sample indices. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Three distinct coordinates have the independent three-record law. This statement assumes [the hij condition](hyp:hij), [the hik condition](hyp:hik), [the hjk condition](hyp:hjk). [This is the stated conclusion](goal). -/
-- @node: pair_triple_measurePreserving
lemma pair_triple_measurePreserving (P : Measure Ω) [IsProbabilityMeasure P]
    {s : ℕ} (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun data : Fin s → Ω => (data i, (data j, data k)))
      (Measure.pi fun _ : Fin s => P) (P.prod (P.prod P)) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin s => P)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun_prodMk
      (fun i => measurable_pi_apply i) j k i hij.symm hik.symm
  refine ⟨by fun_prop, ?_⟩
  have hm := hind.symm.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin s => P) i).map_eq,
    (pair_sample_measurePreserving P j k hjk).map_eq] using hm

/-- Shared-index canonical products vanish after integrating the two other records. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: canonical_shared_integral_zero
lemma canonical_shared_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    (∫ z : Ω × (Ω × Ω), canonicalProjection P g z.1 z.2.1 *
      canonicalProjection P g z.1 z.2.2 ∂P.prod (P.prod P)) = 0 := by
  have hk := canonicalProjection_memLp P g hg hL2
  have hm1 := (MeasurePreserving.id P).prod (measurePreserving_fst (μ := P) (ν := P))
  have hm2 := (MeasurePreserving.id P).prod (measurePreserving_snd (μ := P) (ν := P))
  have hi := (hk.comp_measurePreserving hm1).integrable_mul (hk.comp_measurePreserving hm2)
  change Integrable (fun z : Ω × (Ω × Ω) => canonicalProjection P g z.1 z.2.1 *
    canonicalProjection P g z.1 z.2.2) (P.prod (P.prod P)) at hi
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [canonicalProjection_integral_zero P g hg hL2] with x hx
      rw [integral_prod_mul, hx, zero_mul]
    _ = 0 := by simp

/-- Sample canonical kernels sharing exactly one record are orthogonal. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij), [the hik condition](hyp:hik), [the hjk condition](hyp:hjk). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_shared_zero
lemma canonical_sample_shared_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ data : Fin s → Ω, canonicalProjection P g (data i) (data j) *
      canonicalProjection P g (data i) (data k) ∂Measure.pi (fun _ : Fin s => P)) = 0 := by
  have hm := pair_triple_measurePreserving P i j k hij hik hjk
  have hmeas := canonicalProjection_measurable P g hg
  have hfun : Measurable (fun z : Ω × (Ω × Ω) =>
      canonicalProjection P g z.1 z.2.1 * canonicalProjection P g z.1 z.2.2) :=
    (hmeas.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hmeas.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hzero := canonical_shared_integral_zero P g hg hL2
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hfun.aestronglyMeasurable] at hzero
  exact hzero

/-- A singleton term and a canonical kernel have zero cross moment at every sample index. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm), [the hjk condition](hyp:hjk). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_singleton_zero
lemma canonical_sample_singleton_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (f : Ω → ℝ) (hf : MemLp f 2 P) (hfm : Measurable f)
    {s : ℕ} (i j k : Fin s) (hjk : j ≠ k) :
    (∫ data : Fin s → Ω, f (data i) * canonicalProjection P g (data j) (data k)
      ∂Measure.pi (fun _ : Fin s => P)) = 0 := by
  have hkm := canonicalProjection_measurable P g hg
  by_cases hij : i = j
  · subst j
    have hm := pair_sample_measurePreserving P i k hjk
    have hmfun : Measurable (fun z : Ω × Ω => f z.1 * canonicalProjection P g z.1 z.2) :=
      (hfm.comp measurable_fst).mul hkm
    have hzero := canonicalProjection_orthogonal_first P g hg hL2 f hf
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hmfun.aestronglyMeasurable] at hzero
    exact hzero
  by_cases hik : i = k
  · subst k
    have hm := pair_sample_measurePreserving P j i hjk
    have hmfun : Measurable (fun z : Ω × Ω => f z.2 * canonicalProjection P g z.1 z.2) :=
      (hfm.comp measurable_snd).mul hkm
    have hzero := canonicalProjection_orthogonal_second P g hg hsym hL2 f hf
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hmfun.aestronglyMeasurable] at hzero
    exact hzero
  · have hm := pair_triple_measurePreserving P i j k hij hik hjk
    have hmfun : Measurable (fun z : Ω × (Ω × Ω) => f z.1 *
        canonicalProjection P g z.2.1 z.2.2) :=
      (hfm.comp measurable_fst).mul (hkm.comp measurable_snd)
    have hzero : (∫ z : Ω × (Ω × Ω), f z.1 * canonicalProjection P g z.2.1 z.2.2
        ∂P.prod (P.prod P)) = 0 := by
      rw [integral_prod_mul (f := f) (g := fun z : Ω × Ω => canonicalProjection P g z.1 z.2)]
      change (∫ x, f x ∂P) * pairMean P (canonicalProjection P g) = 0
      rw [canonicalProjection_pairMean_zero P g hg hL2, mul_zero]
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hmfun.aestronglyMeasurable] at hzero
    exact hzero

/-- Every distinct-coordinate canonical term has zero mean. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_mean_zero
lemma canonical_sample_mean_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    (∫ data : Fin s → Ω, canonicalProjection P g (data i) (data j)
      ∂Measure.pi (fun _ : Fin s => P)) = 0 := by
  have hm := pair_sample_measurePreserving P i j hij
  have hzero := canonicalProjection_pairMean_zero P g hg hL2
  unfold pairMean at hzero
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable
    (canonicalProjection_measurable P g hg).aestronglyMeasurable] at hzero
  exact hzero

/-- The variance of one sampled canonical pair is its two-record energy. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_variance
lemma canonical_sample_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    variance (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j))
      (Measure.pi fun _ : Fin s => P) =
      ∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P := by
  have hk := canonicalProjection_memLp P g hg hL2
  rw [variance_eq_sub (pair_sample_memLp P _ hk i j hij),
    canonical_sample_mean_zero P g hg hL2 i j hij]
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  exact Causalean.Stat.UStatistic.LocalizedVariance.integral_two_coordinates_integrable
    P hij (fun x y => canonicalProjection P g x y^2)
    ((canonicalProjection_measurable P g hg).pow_const 2)

/-- Disjoint sample pairs are independent, hence their canonical covariance vanishes. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij), [the hkl condition](hyp:hkl), [the hik condition](hyp:hik), [the hil condition](hyp:hil), [the hjk condition](hyp:hjk), [the hjl condition](hyp:hjl). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_disjoint_covariance
lemma canonical_sample_disjoint_covariance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j k l : Fin s) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    covariance (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j))
      (fun data => canonicalProjection P g (data k) (data l))
      (Measure.pi fun _ : Fin s => P) = 0 := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin s => P)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun_prodMk_prodMk
      (fun i => measurable_pi_apply i) i j k l hik hil hjk hjl
  have hkm := canonicalProjection_measurable P g hg
  exact (hind.comp hkm hkm).covariance_eq_zero
    (pair_sample_memLp P _ (canonicalProjection_memLp P g hg hL2) i j hij)
    (pair_sample_memLp P _ (canonicalProjection_memLp P g hg hL2) k l hkl)

/-- Canonical pair covariance is nonzero only for the same unordered pair. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij), [the hkl condition](hyp:hkl). [This is the stated conclusion](goal). -/
-- @node: canonical_sample_covariance
lemma canonical_sample_covariance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j k l : Fin s) (hij : i ≠ j) (hkl : k ≠ l) :
    covariance (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j))
      (fun data => canonicalProjection P g (data k) (data l))
      (Measure.pi fun _ : Fin s => P) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then
        ∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P else 0 := by
  have hk := canonicalProjection_memLp P g hg hL2
  have hm := (pair_sample_memLp P _ hk i j hij).aemeasurable
  by_cases heq : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  · rw [if_pos heq]
    have hfun : (fun data : Fin s → Ω => canonicalProjection P g (data k) (data l)) =
        (fun data => canonicalProjection P g (data i) (data j)) := by
      funext data
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact canonicalProjection_symmetric P g hsym _ _
    rw [hfun, covariance_self hm]
    exact canonical_sample_variance P g hg hL2 i j hij
  rw [if_neg heq]
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by intro h; exact heq (Or.inl ⟨rfl, h⟩)
    rw [covariance_eq_sub (pair_sample_memLp P _ hk i j hij)
      (pair_sample_memLp P _ hk i l hkl), canonical_sample_mean_zero P g hg hL2 i j hij]
    simp only [zero_mul, sub_zero, Pi.mul_apply]
    exact canonical_sample_shared_zero P g hg hL2 i j l hij hkl hjl
  by_cases hil : i = l
  · subst l
    have hjk : j ≠ k := by intro h; exact heq (Or.inr ⟨rfl, h⟩)
    have hswap : (fun data : Fin s → Ω => canonicalProjection P g (data k) (data i)) =
        (fun data => canonicalProjection P g (data i) (data k)) :=
      funext (fun data => canonicalProjection_symmetric P g hsym _ _)
    rw [hswap, covariance_eq_sub (pair_sample_memLp P _ hk i j hij)
      (pair_sample_memLp P _ hk i k hik), canonical_sample_mean_zero P g hg hL2 i j hij]
    simp only [zero_mul, sub_zero, Pi.mul_apply]
    exact canonical_sample_shared_zero P g hg hL2 i j k hij hik hjk
  by_cases hjk : j = k
  · subst k
    have hswap : (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j)) =
        (fun data => canonicalProjection P g (data j) (data i)) :=
      funext (fun data => canonicalProjection_symmetric P g hsym _ _)
    rw [hswap, covariance_eq_sub (pair_sample_memLp P _ hk j i hij.symm)
      (pair_sample_memLp P _ hk j l hkl), canonical_sample_mean_zero P g hg hL2 j i hij.symm]
    simp only [zero_mul, sub_zero, Pi.mul_apply]
    exact canonical_sample_shared_zero P g hg hL2 j i l hij.symm hkl hil
  by_cases hjl : j = l
  · subst l
    have hswap1 : (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j)) =
        (fun data => canonicalProjection P g (data j) (data i)) :=
      funext (fun data => canonicalProjection_symmetric P g hsym _ _)
    have hswap2 : (fun data : Fin s → Ω => canonicalProjection P g (data k) (data j)) =
        (fun data => canonicalProjection P g (data j) (data k)) :=
      funext (fun data => canonicalProjection_symmetric P g hsym _ _)
    rw [hswap1, hswap2, covariance_eq_sub (pair_sample_memLp P _ hk j i hij.symm)
      (pair_sample_memLp P _ hk j k hjk), canonical_sample_mean_zero P g hg hL2 j i hij.symm]
    simp only [zero_mul, sub_zero, Pi.mul_apply]
    exact canonical_sample_shared_zero P g hg hL2 j i k hij.symm hjk hik
  exact canonical_sample_disjoint_covariance P g hg hL2 i j k l hij hkl hik hil hjk hjl

/-- Each ordered pair has exactly two ordered partners with the same unordered indices. This statement assumes [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: canonical_pair_collision_count
lemma canonical_pair_collision_count {s : ℕ} (i j : Fin s) (hij : i ≠ j) (E : ℝ) :
    (∑ k : Fin s, ∑ l ∈ Finset.univ.erase k,
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then E else 0) = 2*E := by
  classical
  have hinner (k : Fin s) : (∑ l ∈ Finset.univ.erase k,
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then E else 0) =
      if k = i then E else if k = j then E else 0 := by
    by_cases hki : k = i
    · subst k
      simp [hij, hij.symm, eq_comm]
    by_cases hkj : k = j
    · subst k
      simp [hij, hij.symm, eq_comm]
    · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]
  simp_rw [hinner]
  have hfilter : (Finset.univ.filter (fun k : Fin s => i = k)) = {i} := by
    ext k
    simp [eq_comm]
  simp [Finset.sum_ite, hij, hij.symm, eq_comm, hfilter]
  ring

/-- Exact pair counting gives the canonical average its two-over-s(s−1) variance. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: canonicalPairAverage_variance
lemma canonicalPairAverage_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (s : ℕ) (hs : 2 ≤ s) :
    variance (orderedPairAverage s (canonicalProjection P g)) (Measure.pi fun _ : Fin s => P) =
      2/((s:ℝ)*((s:ℝ)-1)) *
        (∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P) := by
  classical
  let E := ∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P
  have hk := canonicalProjection_memLp P g hg hL2
  have hp (i j : Fin s) (hj : j ∈ (Finset.univ : Finset (Fin s)).erase i) :=
    pair_sample_memLp P _ hk i j (Finset.mem_erase.mp hj).1.symm
  have hsum (i : Fin s) : MemLp (fun data : Fin s → Ω =>
      ∑ j ∈ Finset.univ.erase i, canonicalProjection P g (data i) (data j)) 2
        (Measure.pi fun _ : Fin s => P) := memLp_finsetSum _ (hp i)
  unfold orderedPairAverage
  rw [variance_const_mul, variance_fun_sum hsum]
  have hexpand (i k : Fin s) := covariance_fun_sum_fun_sum' (hp i) (hp k)
  simp_rw [hexpand]
  have hrow (i : Fin s) :
      (∑ k : Fin s, ∑ j ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase k,
        covariance (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j))
          (fun data => canonicalProjection P g (data k) (data l)) (Measure.pi fun _ : Fin s => P)) =
      ((s : ℝ)-1)*(2*E) := by
    rw [Finset.sum_comm]
    have hinner (j : Fin s) (hj : j ∈ (Finset.univ : Finset (Fin s)).erase i) :
        (∑ k : Fin s, ∑ l ∈ Finset.univ.erase k,
          covariance (fun data : Fin s → Ω => canonicalProjection P g (data i) (data j))
            (fun data => canonicalProjection P g (data k) (data l)) (Measure.pi fun _ : Fin s => P)) = 2*E := by
      have hij := (Finset.mem_erase.mp hj).1.symm
      calc
        _ = ∑ k : Fin s, ∑ l ∈ Finset.univ.erase k,
            if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then E else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l hl
          exact canonical_sample_covariance P g hg hsym hL2 i j k l hij
            (Finset.mem_erase.mp hl).1.symm
        _ = 2*E := canonical_pair_collision_count i j hij E
    rw [Finset.sum_congr rfl hinner]
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ s)]
  simp_rw [hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsn : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : (s : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  dsimp [E]
  field_simp

/-- Summing singleton terms preserves their orthogonality to the canonical pair average. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: canonicalPairAverage_singleton_covariance
lemma canonicalPairAverage_singleton_covariance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (f : Ω → ℝ) (hf : MemLp f 2 P) (hfm : Measurable f) (s : ℕ) :
    covariance (fun data : Fin s → Ω => ∑ i : Fin s, f (data i))
      (orderedPairAverage s (canonicalProjection P g)) (Measure.pi fun _ : Fin s => P) = 0 := by
  have hk := canonicalProjection_memLp P g hg hL2
  have hp (j k : Fin s) (hk' : k ∈ (Finset.univ : Finset (Fin s)).erase j) :=
    pair_sample_memLp P _ hk j k (Finset.mem_erase.mp hk').1.symm
  have hf' (i : Fin s) : MemLp (fun data : Fin s → Ω => f (data i)) 2
      (Measure.pi fun _ : Fin s => P) :=
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin s => P) i)
  have hsum (j : Fin s) : MemLp (fun data : Fin s → Ω =>
      ∑ k ∈ Finset.univ.erase j, canonicalProjection P g (data j) (data k)) 2
        (Measure.pi fun _ : Fin s => P) := memLp_finsetSum _ (hp j)
  unfold orderedPairAverage
  rw [covariance_const_mul_right,
    covariance_fun_sum_left hf' (memLp_finsetSum _ (fun j _ => hsum j))]
  have hzero (i : Fin s) : covariance (fun data : Fin s → Ω => f (data i))
      (fun data => ∑ j : Fin s, ∑ k ∈ Finset.univ.erase j,
        canonicalProjection P g (data j) (data k)) (Measure.pi fun _ : Fin s => P) = 0 := by
    rw [covariance_fun_sum_right hsum (hf' i)]
    apply Finset.sum_eq_zero
    intro j _
    rw [covariance_fun_sum_right' (hp j) (hf' i)]
    apply Finset.sum_eq_zero
    intro k hk'
    have hjk := (Finset.mem_erase.mp hk').1.symm
    rw [covariance_eq_sub (hf' i) (hp j k hk'),
      canonical_sample_mean_zero P g hg hL2 j k hjk]
    simp only [mul_zero, sub_zero, Pi.mul_apply]
    exact canonical_sample_singleton_zero P g hg hsym hL2 f hf hfm i j k hjk
  simp_rw [hzero]
  simp

end CausalSmith.Stat.FinitepHomogeneityDensegamma



