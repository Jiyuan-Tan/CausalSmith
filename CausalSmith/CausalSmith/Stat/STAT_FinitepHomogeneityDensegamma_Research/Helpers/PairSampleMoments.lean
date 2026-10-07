module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairProjections

/-! Exact sample-level means, integrability, and linear Hoeffding variance. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Distinct sample coordinates have the independent two-record law. This statement assumes [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: pair_sample_measurePreserving
lemma pair_sample_measurePreserving (P : Measure Ω) [IsProbabilityMeasure P]
    {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    MeasurePreserving (fun data : Fin s → Ω => (data i, data j))
      (Measure.pi fun _ : Fin s => P) (P.prod P) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin s => P)
    (X := fun _ : Fin s => id) (fun _ => aemeasurable_id)).indepFun hij
  refine ⟨by fun_prop, ?_⟩
  simpa only [(measurePreserving_eval (fun _ : Fin s => P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin s => P) j).map_eq] using
    hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable

/-- Finite second moments of a pair kernel transport to distinct sample coordinates. This statement assumes [the hL2 condition](hyp:hL2), [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: pair_sample_memLp
lemma pair_sample_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    MemLp (fun data : Fin s → Ω => g (data i) (data j)) 2
      (Measure.pi fun _ : Fin s => P) :=
  hL2.comp_measurePreserving (pair_sample_measurePreserving P i j hij)

/-- Finite ordered pair averaging preserves square integrability. This statement assumes [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: orderedPairAverage_memLp
lemma orderedPairAverage_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (s : ℕ) : MemLp (orderedPairAverage s g) 2 (Measure.pi fun _ : Fin s => P) := by
  unfold orderedPairAverage
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j hj
  exact pair_sample_memLp P g hL2 i j (Finset.mem_erase.mp hj).1.symm

/-- The normalization cancels the exact number of ordered distinct pairs. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: orderedPairAverage_integral
lemma orderedPairAverage_integral (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (s : ℕ) (hs : 2 ≤ s) :
    (∫ data, orderedPairAverage s g data ∂Measure.pi (fun _ : Fin s => P)) =
      pairMean P g := by
  have hi (i j : Fin s) (hj : j ∈ (Finset.univ : Finset (Fin s)).erase i) :
      Integrable (fun data : Fin s → Ω => g (data i) (data j))
        (Measure.pi fun _ : Fin s => P) :=
    (pair_sample_memLp P g hL2 i j (Finset.mem_erase.mp hj).1.symm).integrable (by norm_num)
  have hm (i j : Fin s) (hj : j ∈ (Finset.univ : Finset (Fin s)).erase i) :
      (∫ data : Fin s → Ω, g (data i) (data j) ∂Measure.pi (fun _ : Fin s => P)) =
        pairMean P g := by
    exact Causalean.Stat.UStatistic.LocalizedVariance.integral_two_coordinates_integrable
      P (Finset.mem_erase.mp hj).1.symm g hg
  have hsn : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : (s : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  unfold orderedPairAverage
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j hj => hi _ j hj)]
    have hsum (i : Fin s) :
        (∑ j ∈ Finset.univ.erase i,
          ∫ data : Fin s → Ω, g (data i) (data j) ∂Measure.pi (fun _ : Fin s => P)) =
          ((s : ℝ)-1)*pairMean P g := by
      rw [Finset.sum_congr rfl (fun j hj => hm i j hj)]
      simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ s)]
    simp_rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact integrable_finsetSum _ (fun j hj => hi i j hj)

/-- The canonical residual is measurable because its conditional mean is a measurable integral. This statement assumes [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_measurable
@[fun_prop] lemma canonicalProjection_measurable (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2)) :
    Measurable (fun z : Ω × Ω => canonicalProjection P g z.1 z.2) := by
  have hm : Measurable (fun x => ∫ y, g x y ∂P) :=
    hg.stronglyMeasurable.integral_prod_right.measurable
  unfold canonicalProjection singletonProjection
  exact ((hg.sub measurable_const).sub
    ((hm.comp measurable_fst).sub measurable_const)).sub
      ((hm.comp measurable_snd).sub measurable_const)

/-- The canonical residual's two-record mean vanishes. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_pairMean_zero
lemma canonicalProjection_pairMean_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    pairMean P (canonicalProjection P g) = 0 := by
  simpa only [pairMean, one_mul] using
    canonicalProjection_orthogonal_first P g hg hL2 (fun _ => 1) (memLp_const 1)

/-- The canonical ordered-pair average is square integrable and exactly centered. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: canonicalPairAverage_centered
lemma canonicalPairAverage_centered (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (s : ℕ) (hs : 2 ≤ s) :
    MemLp (orderedPairAverage s (canonicalProjection P g)) 2 (Measure.pi fun _ : Fin s => P) ∧
      (∫ data, orderedPairAverage s (canonicalProjection P g) data
        ∂Measure.pi (fun _ : Fin s => P)) = 0 := by
  refine ⟨orderedPairAverage_memLp P _ (canonicalProjection_memLp P g hg hL2) s, ?_⟩
  rw [orderedPairAverage_integral P _ (canonicalProjection_measurable P g hg)
    (canonicalProjection_memLp P g hg hL2) s hs,
    canonicalProjection_pairMean_zero P g hg hL2]

/-- The ordered sum of singleton terms counts each record exactly s minus one times. [This is the stated conclusion](goal). -/
-- @node: pair_singleton_sum
lemma pair_singleton_sum (s : ℕ) (f : Fin s → ℝ) :
    (∑ i : Fin s, ∑ j ∈ Finset.univ.erase i, (f i+f j)) =
      2*((s : ℝ)-1)*∑ i : Fin s, f i := by
  simp only [Finset.sum_add_distrib]
  have hswap := score_pair_sum_swap (Finset.univ : Finset (Fin s)) (fun i _j => f i)
  rw [hswap]
  have h (i : Fin s) : (∑ _j ∈ Finset.univ.erase i, f i) = ((s : ℝ)-1)*f i := by
    have hs : 1 ≤ s := by have := i.isLt; omega
    simp [Finset.card_erase_of_mem, Nat.cast_sub hs]
  simp_rw [h]
  rw [← Finset.mul_sum]
  ring

/-- The pair average splits into its mean, linear projection, and canonical average. This statement assumes [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: orderedPairAverage_hoeffding_decomposition
lemma orderedPairAverage_hoeffding_decomposition (P : Measure Ω)
    (g : Ω → Ω → ℝ) (s : ℕ) (hs : 2 ≤ s) (data : Fin s → Ω) :
    orderedPairAverage s g data = pairMean P g+
      2/(s : ℝ)*(∑ i : Fin s, singletonProjection P g (data i))+
      orderedPairAverage s (canonicalProjection P g) data := by
  have he (i j : Fin s) : g (data i) (data j) = pairMean P g+
      (singletonProjection P g (data i)+singletonProjection P g (data j))+
      canonicalProjection P g (data i) (data j) := by
    unfold canonicalProjection
    ring
  have hsn : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : (s : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hconst : (∑ i : Fin s, ∑ _j ∈ Finset.univ.erase i, pairMean P g) =
      (s : ℝ)*((s : ℝ)-1)*pairMean P g := by
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ s)]
    ring
  unfold orderedPairAverage
  simp_rw [he, Finset.sum_add_distrib]
  have hsingle := pair_singleton_sum s (fun i => singletonProjection P g (data i))
  simp only [Finset.sum_add_distrib] at hsingle
  rw [hconst, hsingle]
  field_simp

/-- The singleton projection's variance equals its centered second moment. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: singletonProjection_variance
lemma singletonProjection_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    variance (singletonProjection P g) P = ∫ x, singletonProjection P g x^2 ∂P := by
  rw [variance_eq_sub (singletonProjection_memLp P g hg hL2),
    singletonProjection_integral_zero P g hg hL2]
  simp

/-- Independence gives the precise four-over-s variance factor for the linear part. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hs condition](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: pair_linear_variance
lemma pair_linear_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (s : ℕ) (hs : 0 < s) :
    variance (fun data : Fin s → Ω => 2/(s : ℝ)*∑ i : Fin s,
      singletonProjection P g (data i)) (Measure.pi fun _ : Fin s => P) =
      4/(s : ℝ)*variance (singletonProjection P g) P := by
  rw [variance_const_mul]
  have he : variance (fun data : Fin s → Ω => ∑ i : Fin s,
      singletonProjection P g (data i)) (Measure.pi fun _ : Fin s => P) =
      (s : ℝ)*variance (singletonProjection P g) P := by
    have hv := variance_sum_pi (μ := fun _ : Fin s => P)
      (X := fun _ => singletonProjection P g)
      (fun _ => singletonProjection_memLp P g hg hL2)
    convert hv using 1
    · congr 1
      funext data
      simp only [Finset.sum_apply]
    · simp
  rw [he]
  have hsn : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
