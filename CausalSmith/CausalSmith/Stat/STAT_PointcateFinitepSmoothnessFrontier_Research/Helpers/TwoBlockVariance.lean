module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoBlockLegs
/-! Exact bipartite degenerate variance and the assembled two-block certificate. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable {Ω : Type*} [MeasurableSpace Ω]
/-- Integrating an input record absent from the other kernel kills the product by conditional centering. -/
-- @node: twoBlock_unused_coordinate_product
lemma twoBlock_unused_coordinate_product {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (t i s k : Fin n) (hti : t ≠ i) (hts : t ≠ s) (htk : t ≠ k)
    (K L : Ω → Ω → ℝ)
    (hp : Integrable (fun o : Fin n → Ω => K (o t) (o i) * L (o s) (o k))
      (Measure.pi (fun _ => P)))
    (hcol : ∀ᵐ y ∂P, (∫ x, K x y ∂P) = 0) :
    (∫ o : Fin n → Ω, K (o t) (o i) * L (o s) (o k)
      ∂Measure.pi (fun _ => P)) = 0 := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ n =>
    obtain ⟨i', hi'⟩ : ∃ j : Fin n, t.succAbove j = i := by
      change i ∈ Set.range t.succAbove
      simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using hti.symm
    obtain ⟨s', hs'⟩ : ∃ j : Fin n, t.succAbove j = s := by
      change s ∈ Set.range t.succAbove
      simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using hts.symm
    obtain ⟨k', hk'⟩ : ∃ j : Fin n, t.succAbove j = k := by
      change k ∈ Set.range t.succAbove
      simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using htk.symm
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) t
    have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => P) t).symm
    have hpi := hm.integrable_comp_of_integrable hp
    have he : (fun z : Ω × (Fin n → Ω) => K ((e.symm z) t) ((e.symm z) i) *
        L ((e.symm z) s) ((e.symm z) k)) =
        (fun z => K z.1 (z.2 i') * L (z.2 s') (z.2 k')) := by
      funext z
      subst i s k
      simp [e]
    calc
      _ = ∫ z : Ω × (Fin n → Ω), K ((e.symm z) t) ((e.symm z) i) *
          L ((e.symm z) s) ((e.symm z) k) ∂P.prod (Measure.pi (fun _ => P)) := by
        rw [← hm.map_eq]
        exact (integral_map hm.measurable.aemeasurable
          (hm.map_eq.symm ▸ hp.aestronglyMeasurable))
      _ = ∫ o : Fin n → Ω, ∫ x, K x (o i') * L (o s') (o k') ∂P
          ∂Measure.pi (fun _ => P) := by
        rw [he]
        exact integral_prod_symm _ (he ▸ hpi)
      _ = 0 := by
        have hz := (measurePreserving_eval (fun _ : Fin n => P) i').quasiMeasurePreserving.ae hcol
        apply integral_eq_zero_of_ae
        filter_upwards [hz] with o ho
        simp only [integral_mul_const, ho, zero_mul, Pi.zero_apply]


/-- Distinct bipartite kernel entries have zero product mean, even when they share a record. -/
-- @node: twoBlock_kernel_pair_product
lemma twoBlock_kernel_pair_product {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY)
    (t i s k : Fin n) (ht : t ∈ BT) (hi : i ∈ BY) (hs : s ∈ BT) (hk : k ∈ BY)
    (K : Ω → Ω → ℝ) (hK : MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (P.prod P))
    (hrow : ∀ᵐ x ∂P, (∫ y, K x y ∂P) = 0)
    (hcol : ∀ᵐ y ∂P, (∫ x, K x y ∂P) = 0) :
    Integrable (fun o : Fin n → Ω => K (o t) (o i) * K (o s) (o k)) (Measure.pi (fun _ => P)) ∧
    (∫ o : Fin n → Ω, K (o t) (o i) * K (o s) (o k) ∂Measure.pi (fun _ => P)) =
      if t = s ∧ i = k then ∫ x, ∫ y, (K x y)^2 ∂P ∂P else 0 := by
  have hcross (a : Fin n) (ha : a ∈ BT) (b : Fin n) (hb : b ∈ BY) : a ≠ b :=
    fun he => Finset.disjoint_left.mp hdis ha (he ▸ hb)
  have hm := twoBlock_pair_measurePreserving P t i (hcross t ht i hi)
  have hn := twoBlock_pair_measurePreserving P s k (hcross s hs k hk)
  have hp := (hK.comp_measurePreserving hm).integrable_mul (hK.comp_measurePreserving hn)
  refine ⟨hp, ?_⟩
  by_cases hts : t = s
  · subst s
    by_cases hik : i = k
    · subst k
      rw [if_pos ⟨rfl, rfl⟩]
      simp_rw [← sq]
      calc
        _ = ∫ z : Ω × Ω, (K z.1 z.2)^2 ∂P.prod P := by
          rw [← hm.map_eq]
          exact (integral_map hm.measurable.aemeasurable
            (hm.map_eq.symm ▸ hK.integrable_sq.aestronglyMeasurable)).symm
        _ = _ := integral_prod _ hK.integrable_sq
    · rw [if_neg (by simpa using hik)]
      exact twoBlock_unused_coordinate_product P i t t k (hcross t ht i hi).symm
        (hcross t ht i hi).symm hik (fun x y => K y x) K hp hrow
  · rw [if_neg (by simp [hts])]
    exact twoBlock_unused_coordinate_product P t i s k (hcross t ht i hi)
      hts (hcross t ht k hk) K K hp hcol

/-- Expanding the double sum leaves exactly one squared-kernel moment per index pair. -/
-- @node: twoBlock_kernel_sum_second_moment
lemma twoBlock_kernel_sum_second_moment {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY)
    (K : Ω → Ω → ℝ) (hK : MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (P.prod P))
    (hrow : ∀ᵐ x ∂P, (∫ y, K x y ∂P) = 0)
    (hcol : ∀ᵐ y ∂P, (∫ x, K x y ∂P) = 0) :
    (∫ o : Fin n → Ω, (∑ t ∈ BT, ∑ i ∈ BY, K (o t) (o i))^2
      ∂Measure.pi (fun _ => P)) =
      (BT.card : ℝ) * (BY.card : ℝ) * (∫ x, ∫ y, (K x y)^2 ∂P ∂P) := by
  have hp (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY)
      (s : Fin n) (hs : s ∈ BT) (k : Fin n) (hk : k ∈ BY) :=
    twoBlock_kernel_pair_product P BT BY hdis t i s k ht hi hs hk K hK hrow hcol
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun t ht => integrable_finsetSum BY (fun i hi =>
    integrable_finsetSum BT (fun s hs => integrable_finsetSum BY (fun k hk =>
      (hp t ht i hi s hs k hk).1))))]
  have he (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :
      (∫ o : Fin n → Ω, ∑ s ∈ BT, ∑ k ∈ BY, K (o t) (o i) * K (o s) (o k)
        ∂Measure.pi (fun _ => P)) = ∫ x, ∫ y, (K x y)^2 ∂P ∂P := by
    rw [integral_finsetSum _ (fun s hs => integrable_finsetSum BY
      (fun k hk => (hp t ht i hi s hs k hk).1))]
    calc
      _ = ∑ s ∈ BT, ∑ k ∈ BY, if t = s ∧ i = k then
          ∫ x, ∫ y, (K x y)^2 ∂P ∂P else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [integral_finsetSum _ (fun k hk => (hp t ht i hi s hs k hk).1)]
        exact Finset.sum_congr rfl (fun k hk => (hp t ht i hi s hs k hk).2)
      _ = _ := by simp [ite_and, Finset.sum_ite_eq, ht, hi]
  have hout (t : Fin n) (ht : t ∈ BT) :
      (∫ o : Fin n → Ω, ∑ i ∈ BY, ∑ s ∈ BT, ∑ k ∈ BY,
        K (o t) (o i) * K (o s) (o k) ∂Measure.pi (fun _ => P)) =
        (BY.card : ℝ) * (∫ x, ∫ y, (K x y)^2 ∂P ∂P) := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum BT (fun s hs =>
      integrable_finsetSum BY (fun k hk => (hp t ht i hi s hs k hk).1)))]
    rw [Finset.sum_congr rfl (he t ht)]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hout]
  simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, pow_two]


/-- The degenerate bipartite average has exact variance equal to kernel energy divided by both block sizes. -/
-- @node: twoBlock_degenerate_variance
lemma twoBlock_degenerate_variance {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (hT : BT.Nonempty) (hY : BY.Nonempty)
    (B : Ω → Ω → ℝ) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    variance (degenerateTerm P BT BY B) (Measure.pi (fun _ => P)) =
      (∫ x, ∫ y, (centeredKernel P B x y)^2 ∂P ∂P) / ((BT.card : ℝ) * BY.card) := by
  have hm := (twoBlock_leg_moments P BT BY hdis (fun _ => 0) B (memLp_const 0) hB).2.2
  have hk := twoBlock_centered_kernel_moments P B hB
  have hc := centeredKernel_conditional_means P B hB
  have hs := twoBlock_kernel_sum_second_moment P BT BY hdis _ hk.1 hc.1 hc.2
  have hTc : (BT.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  have hYc : (BY.card : ℝ) ≠ 0 := by exact_mod_cast hY.card_pos.ne'
  rw [variance_eq_sub hm.1, hm.2]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply, degenerateTerm, mul_pow, neg_sq]
  rw [integral_const_mul, hs]
  field_simp
-- @node: lem:two-block-linear-bilinear-variance
/-- The bipartite Hoeffding decomposition has three orthogonal components, exact degenerate
variance, centering contraction, and an absolute-deviation bound by their standard deviations. -/
lemma two_block_linear_bilinear_variance (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (expLaw : ExperimentFamilyOf Ω) (hiid : IIDSampling expLaw)
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (hcover : BT ∪ BY = Finset.univ)
    (hT : BT.Nonempty) (hY : BY.Nonempty) (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
  let sampleLaw := (expLaw n P).map Prod.fst
  let V := twoBlockStatistic BT BY F B
  let VT := treatmentTerm P BT B
  let VY := outcomeTerm P BY F B
  let VC := degenerateTerm P BT BY B
  (∫ o, V o ∂sampleLaw) = (∫ o, F o ∂P) - (∫ o, ∫ z, B o z ∂P ∂P) ∧
  (∀ o, V o - (∫ z, V z ∂sampleLaw) = VT o + VY o + VC o) ∧
  (∫ o, VT o * VY o ∂sampleLaw) = 0 ∧
  (∫ o, VT o * VC o ∂sampleLaw) = 0 ∧
  (∫ o, VY o * VC o ∂sampleLaw) = 0 ∧
  ProbabilityTheory.variance VC sampleLaw =
    (∫ o, ∫ z, (centeredKernel P B o z)^2 ∂P ∂P) / ((BT.card : ℝ) * BY.card) ∧
  (∫ o, ∫ z, (centeredKernel P B o z)^2 ∂P ∂P) ≤ (∫ o, ∫ z, (B o z)^2 ∂P ∂P) ∧
  (∫ o, |V o - (∫ z, V z ∂sampleLaw)| ∂sampleLaw) ≤
    Real.sqrt (ProbabilityTheory.variance VT sampleLaw) + Real.sqrt (ProbabilityTheory.variance VY sampleLaw) +
      Real.sqrt (ProbabilityTheory.variance VC sampleLaw) := by
  dsimp only
  have hn : 2 ≤ n := by
    obtain ⟨t, ht⟩ := hT
    obtain ⟨i, hi⟩ := hY
    have hti : t ≠ i := fun he => Finset.disjoint_left.mp hdis ht (he ▸ hi)
    by_contra hsmall
    have he : t = i := Fin.ext (by omega)
    exact hti he
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hsample : (expLaw n P).map Prod.fst = Measure.pi (fun _ : Fin n => P) := by
    rw [hiid n hn P inferInstance, Measure.map_fst_prod]
    simp
  have hmean : (∫ o, twoBlockStatistic BT BY F B o ∂(expLaw n P).map Prod.fst) =
      (∫ o, F o ∂P) - (∫ o, ∫ z, B o z ∂P ∂P) := by
    rw [hsample]
    exact twoBlock_expectation P BT BY hdis hT hY F B hF hB
  have hremaining :
      (∫ o, treatmentTerm P BT B o * outcomeTerm P BY F B o ∂(expLaw n P).map Prod.fst) = 0 ∧
      (∫ o, treatmentTerm P BT B o * degenerateTerm P BT BY B o ∂(expLaw n P).map Prod.fst) = 0 ∧
      (∫ o, outcomeTerm P BY F B o * degenerateTerm P BT BY B o ∂(expLaw n P).map Prod.fst) = 0 ∧
      ProbabilityTheory.variance (degenerateTerm P BT BY B) ((expLaw n P).map Prod.fst) =
        (∫ o, ∫ z, (centeredKernel P B o z)^2 ∂P ∂P) / ((BT.card : ℝ) * BY.card) ∧
      (∫ o, ∫ z, (centeredKernel P B o z)^2 ∂P ∂P) ≤ (∫ o, ∫ z, (B o z)^2 ∂P ∂P) ∧
      (∫ o, |twoBlockStatistic BT BY F B o -
          (∫ z, twoBlockStatistic BT BY F B z ∂(expLaw n P).map Prod.fst)|
          ∂(expLaw n P).map Prod.fst) ≤
        Real.sqrt (ProbabilityTheory.variance (treatmentTerm P BT B) ((expLaw n P).map Prod.fst)) +
        Real.sqrt (ProbabilityTheory.variance (outcomeTerm P BY F B) ((expLaw n P).map Prod.fst)) +
        Real.sqrt (ProbabilityTheory.variance (degenerateTerm P BT BY B) ((expLaw n P).map Prod.fst)) := by
    refine ⟨?_, ?_⟩
    · rw [hsample]
      exact twoBlock_single_legs_orthogonal P BT BY hdis F B hF hB
    · have hcontraction := centeredKernel_energy_contraction P B hB
      have horth := twoBlock_degenerate_legs_orthogonal P BT BY hdis F B hF hB
      -- The pair-product calculation supplies the exact sample variance.
      have hopen :
          ProbabilityTheory.variance (degenerateTerm P BT BY B) ((expLaw n P).map Prod.fst) =
            (∫ o, ∫ z, (centeredKernel P B o z)^2 ∂P ∂P) / ((BT.card : ℝ) * BY.card) := by
        rw [hsample]
        exact twoBlock_degenerate_variance P BT BY hdis hT hY B hB
      have hdev := twoBlock_deviation_bound P BT BY hdis hT hY F B hF hB
      refine ⟨?_, ?_, hopen, hcontraction, ?_⟩
      · rw [hsample]
        exact horth.1
      · rw [hsample]
        exact horth.2
      · rw [hmean, hsample]
        exact hdev
  refine ⟨hmean, ?_, hremaining⟩
  intro o
  rw [hmean]
  exact twoBlock_population_decomposition P BT BY hT hY F B hF hB o

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
