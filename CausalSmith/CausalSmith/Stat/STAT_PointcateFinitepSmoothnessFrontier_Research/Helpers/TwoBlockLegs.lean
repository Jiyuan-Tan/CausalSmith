module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Centering
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration

/-! Finite-moment point-CATE frontier: Helpers/TwoBlockLegs. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


variable {Ω : Type*} [MeasurableSpace Ω]
/-- The raw asymmetric linear-minus-bilinear statistic on the two blocks. -/
def twoBlockStatistic {n : ℕ} (BT BY : Finset (Fin n)) (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (o : Fin n → Ω) : ℝ :=
  (BY.card : ℝ)⁻¹ * (∑ i ∈ BY, F (o i)) -
  ((BT.card : ℝ) * BY.card)⁻¹ * (∑ t ∈ BT, ∑ i ∈ BY, B (o t) (o i))
/-- The centered treatment-leg average. -/
def treatmentTerm {n : ℕ} (P : Measure Ω) (BT : Finset (Fin n)) (B : Ω → Ω → ℝ) (o : Fin n → Ω) : ℝ :=
  -(BT.card : ℝ)⁻¹ * ∑ t ∈ BT, ((∫ z, B (o t) z ∂P) - ∫ v, ∫ w, B v w ∂P ∂P)
/-- The centered outcome-leg average. -/
def outcomeTerm {n : ℕ} (P : Measure Ω) (BY : Finset (Fin n)) (F : Ω → ℝ) (B : Ω → Ω → ℝ) (o : Fin n → Ω) : ℝ :=
  (BY.card : ℝ)⁻¹ * ∑ i ∈ BY, (F (o i) - (∫ v, B v (o i) ∂P) - ∫ z, F z - (∫ v, B v z ∂P) ∂P)
/-- The product-law-degenerate double-sum term. -/
def degenerateTerm {n : ℕ} (P : Measure Ω) (BT BY : Finset (Fin n)) (B : Ω → Ω → ℝ) (o : Fin n → Ω) : ℝ :=
  -((BT.card : ℝ) * BY.card)⁻¹ * ∑ t ∈ BT, ∑ i ∈ BY, centeredKernel P B (o t) (o i)
/-- Expanding the product-law centering counts each single-leg value once per
record in the opposite block. -/
-- @node: centeredKernel_block_sum
lemma centeredKernel_block_sum {n : ℕ} (P : Measure Ω) (BT BY : Finset (Fin n))
    (B : Ω → Ω → ℝ) (o : Fin n → Ω) :
    (∑ t ∈ BT, ∑ i ∈ BY, centeredKernel P B (o t) (o i)) =
      (∑ t ∈ BT, ∑ i ∈ BY, B (o t) (o i)) -
      (BT.card : ℝ) * (∑ i ∈ BY, ∫ v, B v (o i) ∂P) -
      (BY.card : ℝ) * (∑ t ∈ BT, ∫ z, B (o t) z ∂P) +
      (BT.card : ℝ) * (BY.card : ℝ) * (∫ v, ∫ w, B v w ∂P ∂P) := by
  simp only [centeredKernel, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The mean of the outcome leg is the linear mean minus the product-kernel mean,
with the latter written in treatment-first order by Fubini. -/
-- @node: outcome_leg_mean
lemma outcome_leg_mean (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ z, F z - (∫ v, B v z ∂P) ∂P) =
      (∫ z, F z ∂P) - (∫ v, ∫ w, B v w ∂P ∂P) := by
  have hBi := hB.integrable (by norm_num)
  rw [integral_sub (hF.integrable (by norm_num)) hBi.integral_prod_right]
  rw [← integral_integral_swap hBi]

/-- Subtracting the population mean gives the three-leg decomposition by counting
block repetitions; no probabilistic independence is needed for this algebraic step. -/
-- @node: twoBlock_population_decomposition
lemma twoBlock_population_decomposition {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hT : BT.Nonempty) (hY : BY.Nonempty)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P))
    (o : Fin n → Ω) :
    twoBlockStatistic BT BY F B o - ((∫ z, F z ∂P) - (∫ v, ∫ w, B v w ∂P ∂P)) =
      treatmentTerm P BT B o + outcomeTerm P BY F B o + degenerateTerm P BT BY B o := by
  have hTc : (BT.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  have hYc : (BY.card : ℝ) ≠ 0 := by exact_mod_cast hY.card_pos.ne'
  rw [twoBlockStatistic, treatmentTerm, outcomeTerm, degenerateTerm,
    centeredKernel_block_sum, outcome_leg_mean P F B hF hB]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  <;> ring

/-- Distinct sample coordinates have the original product law. -/
-- @node: twoBlock_pair_measurePreserving
lemma twoBlock_pair_measurePreserving {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (t i : Fin n) (hti : t ≠ i) :
    MeasurePreserving (fun o : Fin n → Ω => (o t, o i))
      (Measure.pi (fun _ : Fin n => P)) (P.prod P) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin n => P)
    (X := fun _ => @id Ω) (fun _ => measurable_id.aemeasurable)).indepFun hti
  simp only [id_eq] at hind
  refine ⟨by fun_prop, ?_⟩
  rw [hind.map_prod_eq_prod_map_map
    (measurable_pi_apply t).aemeasurable (measurable_pi_apply i).aemeasurable]
  rw [(measurePreserving_eval (fun _ : Fin n => P) t).map_eq,
    (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]

/-- Averaging over disjoint blocks preserves the linear and bilinear population means. -/
-- @node: twoBlock_expectation
lemma twoBlock_expectation {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (hT : BT.Nonempty) (hY : BY.Nonempty)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ o, twoBlockStatistic BT BY F B o ∂Measure.pi (fun _ : Fin n => P)) =
      (∫ z, F z ∂P) - (∫ v, ∫ w, B v w ∂P ∂P) := by
  have hFi := hF.integrable (by norm_num)
  have hBi := hB.integrable (by norm_num)
  have hcoord (i : Fin n) : Integrable (fun o : Fin n → Ω => F (o i))
      (Measure.pi (fun _ : Fin n => P)) :=
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hFi
  have hpair (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :=
    twoBlock_pair_measurePreserving P t i (fun he =>
      Finset.disjoint_left.mp hdis ht (he ▸ hi))
  have hkernel (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :
      Integrable (fun o : Fin n → Ω => B (o t) (o i)) (Measure.pi (fun _ : Fin n => P)) :=
    (hpair t ht i hi).integrable_comp_of_integrable hBi
  have hlinear (i : Fin n) :
      (∫ o : Fin n → Ω, F (o i) ∂Measure.pi (fun _ : Fin n => P)) = ∫ z, F z ∂P := by
    have hm := measurePreserving_eval (fun _ : Fin n => P) i
    have he := (integral_map hm.measurable.aemeasurable
      (hm.map_eq.symm ▸ hFi.aestronglyMeasurable)).symm
    simpa only [hm.map_eq] using he
  have hbilinear (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :
      (∫ o : Fin n → Ω, B (o t) (o i) ∂Measure.pi (fun _ : Fin n => P)) =
        ∫ v, ∫ w, B v w ∂P ∂P := by
    have hm := hpair t ht i hi
    calc
      _ = ∫ z : Ω × Ω, B z.1 z.2 ∂P.prod P := by
        rw [← hm.map_eq]
        exact (integral_map hm.measurable.aemeasurable
          (hm.map_eq.symm ▸ hBi.aestronglyMeasurable)).symm
      _ = _ := integral_prod _ hBi
  have hTc : (BT.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  have hYc : (BY.card : ℝ) ≠ 0 := by exact_mod_cast hY.card_pos.ne'
  unfold twoBlockStatistic
  rw [integral_sub
    ((integrable_finsetSum BY (fun i _ => hcoord i)).const_mul _)
    ((integrable_finsetSum BT (fun t ht =>
      integrable_finsetSum BY (fun i hi => hkernel t ht i hi))).const_mul _)]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun i _ => hcoord i),
    integral_finsetSum _ (fun t ht => integrable_finsetSum BY (fun i hi => hkernel t ht i hi))]
  simp_rw [hlinear]
  have hd : (∑ t ∈ BT, ∫ o : Fin n → Ω, ∑ i ∈ BY, B (o t) (o i)
      ∂Measure.pi (fun _ : Fin n => P)) =
      (BT.card : ℝ) * (BY.card : ℝ) * (∫ v, ∫ w, B v w ∂P ∂P) := by
    calc
      _ = ∑ t ∈ BT, ∑ i ∈ BY, ∫ o : Fin n → Ω, B (o t) (o i)
          ∂Measure.pi (fun _ : Fin n => P) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact integral_finsetSum _ (fun i hi => hkernel t ht i hi)
      _ = _ := by
        rw [Finset.sum_congr rfl (fun t ht =>
          Finset.sum_congr rfl (fun i hi => hbilinear t ht i hi))]
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  rw [hd]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Products of integrable functions of distinct iid records are integrable and
have the product of their population means. -/
-- @node: twoBlock_coordinate_product
lemma twoBlock_coordinate_product {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (t i : Fin n) (hti : t ≠ i) (f g : Ω → ℝ)
    (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun o : Fin n → Ω => f (o t) * g (o i)) (Measure.pi (fun _ => P)) ∧
    (∫ o : Fin n → Ω, f (o t) * g (o i) ∂Measure.pi (fun _ => P)) =
      (∫ x, f x ∂P) * (∫ x, g x ∂P) := by
  have hm := twoBlock_pair_measurePreserving P t i hti
  have hp := hf.mul_prod hg
  refine ⟨hm.integrable_comp_of_integrable hp, ?_⟩
  calc
    _ = ∫ z : Ω × Ω, f z.1 * g z.2 ∂P.prod P := by
      rw [← hm.map_eq]
      exact (integral_map hm.measurable.aemeasurable
        (hm.map_eq.symm ▸ hp.aestronglyMeasurable)).symm
    _ = _ := integral_prod_mul f g

/-- Centered integrable coordinate sums over disjoint blocks have zero inner product. -/
-- @node: twoBlock_centered_sums_orthogonal
lemma twoBlock_centered_sums_orthogonal {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (f g : Ω → ℝ)
    (hf : Integrable f P) (hg : Integrable g P) (hf0 : (∫ x, f x ∂P) = 0) :
    (∫ o : Fin n → Ω, (∑ t ∈ BT, f (o t)) * (∑ i ∈ BY, g (o i))
      ∂Measure.pi (fun _ => P)) = 0 := by
  have hp (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :=
    twoBlock_coordinate_product P t i
      (fun he => Finset.disjoint_left.mp hdis ht (he ▸ hi)) f g hf hg
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun t ht =>
    integrable_finsetSum BY (fun i hi => (hp t ht i hi).1))]
  have hz (t : Fin n) (ht : t ∈ BT) :
      (∫ o : Fin n → Ω, ∑ i ∈ BY, f (o t) * g (o i)
        ∂Measure.pi (fun _ => P)) = 0 := by
    rw [integral_finsetSum _ (fun i hi => (hp t ht i hi).1)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [(hp t ht i hi).2, hf0, zero_mul]
  exact Finset.sum_eq_zero hz

/-- The two single-block Hoeffding legs are orthogonal by independence of the
blocks and zero mean of the treatment projection. -/
-- @node: twoBlock_single_legs_orthogonal
lemma twoBlock_single_legs_orthogonal {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ o, treatmentTerm P BT B o * outcomeTerm P BY F B o
      ∂Measure.pi (fun _ : Fin n => P)) = 0 := by
  have hBi := hB.integrable (by norm_num)
  have hf : Integrable (fun x => (∫ z, B x z ∂P) - ∫ v, ∫ w, B v w ∂P ∂P) P :=
    hBi.integral_prod_left.sub (integrable_const _)
  have hg : Integrable (fun x => F x - (∫ v, B v x ∂P) -
      ∫ z, F z - (∫ v, B v z ∂P) ∂P) P :=
    ((hF.integrable (by norm_num)).sub hBi.integral_prod_right).sub (integrable_const _)
  have hf0 : (∫ x, (∫ z, B x z ∂P) - ∫ v, ∫ w, B v w ∂P ∂P ∂P) = 0 := by
    rw [integral_sub hBi.integral_prod_left (integrable_const _)]
    simp
  have hz := twoBlock_centered_sums_orthogonal P BT BY hdis _ _ hf hg hf0
  simp only [treatmentTerm, outcomeTerm]
  simp_rw [show ∀ a b c d : ℝ, (a*b)*(c*d) = (a*c)*(b*d) by intros; ring]
  rw [integral_const_mul, hz, mul_zero]

/-- Both conditional projections of an L² kernel remain in L², so its
product-law centering is square integrable and has zero product mean. -/
-- @node: twoBlock_centered_kernel_moments
lemma twoBlock_centered_kernel_moments (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Ω → ℝ)
    (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    MemLp (fun z : Ω × Ω => centeredKernel P B z.1 z.2) 2 (P.prod P) ∧
      (∫ z : Ω × Ω, centeredKernel P B z.1 z.2 ∂P.prod P) = 0 := by
  have hr := centeredKernel_row_mean_memLp P B hB
  have hswap : MemLp (fun z : Ω × Ω => B z.2 z.1) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hc := centeredKernel_row_mean_memLp P (fun x y => B y x) hswap
  have hcol := hc.comp_snd P
  have hrow := hr.comp_fst P
  have hmem := ((hB.sub hcol).sub hrow).add
    (memLp_const (∫ v, ∫ w, B v w ∂P ∂P))
  refine ⟨hmem, ?_⟩
  have hBi := hB.integrable (by norm_num)
  change (∫ z : Ω × Ω, B z.1 z.2 - (∫ v, B v z.2 ∂P) -
    (∫ v, B z.1 v ∂P) + ∫ v, ∫ w, B v w ∂P ∂P ∂P.prod P) = 0
  have hi1 : Integrable (fun z : Ω × Ω => B z.1 z.2 - ∫ v, B v z.2 ∂P)
      (P.prod P) := hBi.sub (hcol.integrable (by norm_num))
  have hi2 : Integrable (fun z : Ω × Ω => B z.1 z.2 - (∫ v, B v z.2 ∂P) -
      ∫ v, B z.1 v ∂P) (P.prod P) := hi1.sub (hrow.integrable (by norm_num))
  rw [integral_add hi2 (integrable_const _),
    integral_sub hi1 (hrow.integrable (by norm_num)),
    integral_sub hBi (hcol.integrable (by norm_num))]
  rw [integral_prod _ hBi, integral_prod _ (hcol.integrable (by norm_num)),
    integral_prod _ (hrow.integrable (by norm_num))]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, one_mul, mul_one]
  rw [← integral_integral_swap hBi]
  ring

/-- A centered kernel is orthogonal to a square-integrable function of either
of its input records, including the shared-record cases. -/
-- @node: twoBlock_kernel_single_record_product
lemma twoBlock_kernel_single_record_product {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (t i r : Fin n) (hti : t ≠ i) (f : Ω → ℝ) (K : Ω → Ω → ℝ)
    (hf : MemLp f 2 P) (hK : MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (P.prod P))
    (hrow : ∀ᵐ x ∂P, (∫ y, K x y ∂P) = 0)
    (hcol : ∀ᵐ y ∂P, (∫ x, K x y ∂P) = 0) :
    Integrable (fun o : Fin n → Ω => f (o r) * K (o t) (o i)) (Measure.pi (fun _ => P)) ∧
      (∫ o : Fin n → Ω, f (o r) * K (o t) (o i) ∂Measure.pi (fun _ => P)) = 0 := by
  have hm := twoBlock_pair_measurePreserving P t i hti
  have hk := hK.comp_measurePreserving hm
  have hfr := hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) r)
  refine ⟨hfr.integrable_mul hk, ?_⟩
  by_cases hrt : r = t
  · subst r
    have hp : Integrable (fun z : Ω × Ω => f z.1 * K z.1 z.2) (P.prod P) :=
      (hf.comp_fst P).integrable_mul hK
    calc
      _ = ∫ z : Ω × Ω, f z.1 * K z.1 z.2 ∂P.prod P := by
        rw [← hm.map_eq]
        exact (integral_map hm.measurable.aemeasurable
          (hm.map_eq.symm ▸ hp.aestronglyMeasurable)).symm
      _ = ∫ x, f x * (∫ y, K x y ∂P) ∂P := by
        rw [integral_prod _ hp]
        simp only [integral_const_mul]
      _ = 0 := by
        have he : (fun x => f x * ∫ y, K x y ∂P) =ᵐ[P] fun _ => 0 := by
          filter_upwards [hrow] with x hx
          rw [hx, mul_zero]
        rw [integral_congr_ae he, integral_zero]
  · by_cases hri : r = i
    · subst r
      have hp : Integrable (fun z : Ω × Ω => f z.2 * K z.1 z.2) (P.prod P) :=
        (hf.comp_snd P).integrable_mul hK
      calc
        _ = ∫ z : Ω × Ω, f z.2 * K z.1 z.2 ∂P.prod P := by
          rw [← hm.map_eq]
          exact (integral_map hm.measurable.aemeasurable
            (hm.map_eq.symm ▸ hp.aestronglyMeasurable)).symm
        _ = ∫ y, f y * (∫ x, K x y ∂P) ∂P := by
          rw [integral_prod_symm _ hp]
          simp only [integral_const_mul]
        _ = 0 := by
          have he : (fun y => f y * ∫ x, K x y ∂P) =ᵐ[P] fun _ => 0 := by
            filter_upwards [hcol] with y hy
            rw [hy, mul_zero]
          rw [integral_congr_ae he, integral_zero]
    · have hind := (iIndepFun_pi (μ := fun _ : Fin n => P)
        (X := fun _ => @id Ω) (fun _ => measurable_id.aemeasurable)).indepFun_prodMk
          (fun j => measurable_pi_apply j) t i r (Ne.symm hrt) (Ne.symm hri)
      simp only [id_eq] at hind
      have hind' := hind.comp₀ hm.measurable.aemeasurable
        (measurable_pi_apply r).aemeasurable
        (hm.map_eq.symm ▸ hK.aestronglyMeasurable.aemeasurable)
        ((measurePreserving_eval (fun _ : Fin n => P) r).map_eq.symm ▸
          hf.aestronglyMeasurable.aemeasurable)
      have hz : (∫ o : Fin n → Ω, K (o t) (o i) ∂Measure.pi (fun _ => P)) = 0 := by
        calc
          _ = ∫ z : Ω × Ω, K z.1 z.2 ∂P.prod P := by
            rw [← hm.map_eq]
            exact (integral_map hm.measurable.aemeasurable
              (hm.map_eq.symm ▸ hK.aestronglyMeasurable)).symm
          _ = ∫ x, ∫ y, K x y ∂P ∂P := integral_prod _ (hK.integrable (by norm_num))
          _ = 0 := by rw [integral_congr_ae hrow, integral_zero]
      have he := hind'.symm.integral_mul_eq_mul_integral
        hfr.aestronglyMeasurable hk.aestronglyMeasurable
      simpa only [Function.comp_def, Pi.mul_apply, hz, mul_zero] using he

/-- Expanding the two sums reduces their covariance to single-record versus
centered-kernel products, whose conditional means vanish. -/
-- @node: twoBlock_sum_kernel_orthogonal
lemma twoBlock_sum_kernel_orthogonal {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (S BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (f : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hf : MemLp f 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ o : Fin n → Ω, (∑ r ∈ S, f (o r)) *
      (∑ t ∈ BT, ∑ i ∈ BY, centeredKernel P B (o t) (o i))
      ∂Measure.pi (fun _ => P)) = 0 := by
  have hk := twoBlock_centered_kernel_moments P B hB
  have hc := centeredKernel_conditional_means P B hB
  have hp (r : Fin n) (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :=
    twoBlock_kernel_single_record_product P t i r
      (fun he => Finset.disjoint_left.mp hdis ht (he ▸ hi)) f _ hf hk.1 hc.1 hc.2
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum BT (fun t ht =>
    integrable_finsetSum BY (fun i hi => (hp r t ht i hi).1)))]
  apply Finset.sum_eq_zero
  intro r hr
  rw [integral_finsetSum _ (fun t ht => integrable_finsetSum BY
    (fun i hi => (hp r t ht i hi).1))]
  apply Finset.sum_eq_zero
  intro t ht
  rw [integral_finsetSum _ (fun i hi => (hp r t ht i hi).1)]
  exact Finset.sum_eq_zero (fun i hi => (hp r t ht i hi).2)

/-- Each single-block Hoeffding leg is orthogonal to the degenerate double
sum, including every summand that shares a sample coordinate. -/
-- @node: twoBlock_degenerate_legs_orthogonal
lemma twoBlock_degenerate_legs_orthogonal {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ o : Fin n → Ω, treatmentTerm P BT B o * degenerateTerm P BT BY B o
      ∂Measure.pi (fun _ => P)) = 0 ∧
    (∫ o : Fin n → Ω, outcomeTerm P BY F B o * degenerateTerm P BT BY B o
      ∂Measure.pi (fun _ => P)) = 0 := by
  have hr := centeredKernel_row_mean_memLp P B hB
  have hswap : MemLp (fun z : Ω × Ω => B z.2 z.1) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hc := centeredKernel_row_mean_memLp P (fun x y => B y x) hswap
  have ht := hr.sub (memLp_const (∫ v, ∫ w, B v w ∂P ∂P))
  have hy := (hF.sub hc).sub (memLp_const (∫ z, F z - (∫ v, B v z ∂P) ∂P))
  have hzT := twoBlock_sum_kernel_orthogonal P BT BT BY hdis _ B ht hB
  have hzY := twoBlock_sum_kernel_orthogonal P BY BT BY hdis _ B hy hB
  simp only [Pi.sub_apply] at hzT hzY
  constructor
  · simp only [treatmentTerm, degenerateTerm]
    simp_rw [show ∀ a b c d : ℝ, (a*b)*(c*d) = (a*c)*(b*d) by intros; ring]
    rw [integral_const_mul, hzT, mul_zero]
  · simp only [outcomeTerm, degenerateTerm]
    simp_rw [show ∀ a b c d : ℝ, (a*b)*(c*d) = (a*c)*(b*d) by intros; ring]
    rw [integral_const_mul, hzY, mul_zero]

/-- A square-integrable centered single-record function stays centered after
any finite coordinate average. -/
-- @node: twoBlock_centered_coordinate_sum
lemma twoBlock_centered_coordinate_sum {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Finset (Fin n)) (f : Ω → ℝ) (c : ℝ) (hf : MemLp f 2 P)
    (hf0 : (∫ x, f x ∂P) = 0) :
    MemLp (fun o : Fin n → Ω => c * ∑ i ∈ S, f (o i)) 2 (Measure.pi (fun _ => P)) ∧
      (∫ o : Fin n → Ω, c * ∑ i ∈ S, f (o i) ∂Measure.pi (fun _ => P)) = 0 := by
  have hm (i : Fin n) := measurePreserving_eval (fun _ : Fin n => P) i
  have hi (i : Fin n) : MemLp (fun o : Fin n → Ω => f (o i)) 2
      (Measure.pi (fun _ => P)) := hf.comp_measurePreserving (hm i)
  refine ⟨(memLp_finsetSum S (fun i _ => hi i)).const_mul c, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hi i).integrable (by norm_num))]
  have hz (i : Fin n) : (∫ o : Fin n → Ω, f (o i) ∂Measure.pi (fun _ => P)) = 0 := by
    have he := (integral_map (hm i).measurable.aemeasurable
      ((hm i).map_eq.symm ▸ hf.aestronglyMeasurable)).symm
    simpa only [(hm i).map_eq, hf0] using he
  simp_rw [hz]
  simp

/-- Each of the three Hoeffding legs is square integrable and centered. This
uses only coordinate laws, not covariance or the exact variance calculation. -/
-- @node: twoBlock_leg_moments
lemma twoBlock_leg_moments {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (MemLp (treatmentTerm P BT B) 2 (Measure.pi (fun _ => P)) ∧
      (∫ o, treatmentTerm P BT B o ∂Measure.pi (fun _ => P)) = 0) ∧
    (MemLp (outcomeTerm P BY F B) 2 (Measure.pi (fun _ => P)) ∧
      (∫ o, outcomeTerm P BY F B o ∂Measure.pi (fun _ => P)) = 0) ∧
    (MemLp (degenerateTerm P BT BY B) 2 (Measure.pi (fun _ => P)) ∧
      (∫ o, degenerateTerm P BT BY B o ∂Measure.pi (fun _ => P)) = 0) := by
  have hr := centeredKernel_row_mean_memLp P B hB
  have hswap : MemLp (fun z : Ω × Ω => B z.2 z.1) 2 (P.prod P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hc := centeredKernel_row_mean_memLp P (fun x y => B y x) hswap
  have ht := hr.sub (memLp_const (∫ v, ∫ w, B v w ∂P ∂P))
  have hy := (hF.sub hc).sub (memLp_const (∫ z, F z - (∫ v, B v z ∂P) ∂P))
  have ht0 : (∫ x, (∫ z, B x z ∂P) - ∫ v, ∫ w, B v w ∂P ∂P ∂P) = 0 := by
    rw [integral_sub (hr.integrable (by norm_num)) (integrable_const _)]
    simp
  have hy0 : (∫ x, F x - (∫ v, B v x ∂P) -
      ∫ z, F z - (∫ v, B v z ∂P) ∂P ∂P) = 0 := by
    change (∫ x, (F - fun x => ∫ v, B v x ∂P) x -
      ∫ z, F z - (∫ v, B v z ∂P) ∂P ∂P) = 0
    rw [integral_sub ((hF.sub hc).integrable (by norm_num)) (integrable_const _)]
    simp
  refine ⟨twoBlock_centered_coordinate_sum P BT _ _ ht ht0,
    twoBlock_centered_coordinate_sum P BY _ _ hy hy0, ?_⟩
  have hk := twoBlock_centered_kernel_moments P B hB
  have hm (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :=
    twoBlock_pair_measurePreserving P t i
      (fun he => Finset.disjoint_left.mp hdis ht (he ▸ hi))
  have hp (t : Fin n) (ht : t ∈ BT) (i : Fin n) (hi : i ∈ BY) :
      MemLp (fun o : Fin n → Ω => centeredKernel P B (o t) (o i)) 2
        (Measure.pi (fun _ => P)) := hk.1.comp_measurePreserving (hm t ht i hi)
  refine ⟨(memLp_finsetSum BT (fun t ht => memLp_finsetSum BY
    (fun i hi => hp t ht i hi))).const_mul _, ?_⟩
  unfold degenerateTerm
  rw [integral_const_mul, integral_finsetSum _ (fun t ht =>
    (memLp_finsetSum BY (fun i hi => hp t ht i hi)).integrable (by norm_num))]
  have hz (t : Fin n) (ht : t ∈ BT) :
      (∫ o : Fin n → Ω, ∑ i ∈ BY, centeredKernel P B (o t) (o i)
        ∂Measure.pi (fun _ => P)) = 0 := by
    rw [integral_finsetSum _ (fun i hi => (hp t ht i hi).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro i hi
    have he := (integral_map (hm t ht i hi).measurable.aemeasurable
      ((hm t ht i hi).map_eq.symm ▸ hk.1.aestronglyMeasurable)).symm
    simpa only [(hm t ht i hi).map_eq, hk.2] using he
  rw [Finset.sum_eq_zero hz, mul_zero]

/-- Cauchy–Schwarz bounds the first absolute moment of a centered L² variable
by its standard deviation. -/
-- @node: twoBlock_abs_le_standard_deviation
lemma twoBlock_abs_le_standard_deviation (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) (hf0 : (∫ x, f x ∂P) = 0) :
    (∫ x, |f x| ∂P) ≤ Real.sqrt (variance f P) := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (show Real.HolderConjugate 2 2 by constructor <;> norm_num)
    (f := f) (g := fun _ : Ω => (1 : ℝ)) (by simpa using hf) (memLp_const _)
  rw [Real.sqrt_eq_rpow]
  simpa [Real.norm_eq_abs, Real.rpow_two,
    variance_eq_sub hf, hf0] using hcs

/-- The triangle inequality followed by Cauchy–Schwarz on each centered leg
bounds the mean absolute deviation by the sum of the three standard deviations. -/
-- @node: twoBlock_deviation_bound
lemma twoBlock_deviation_bound {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (BT BY : Finset (Fin n)) (hdis : Disjoint BT BY) (hT : BT.Nonempty) (hY : BY.Nonempty)
    (F : Ω → ℝ) (B : Ω → Ω → ℝ)
    (hF : MemLp F 2 P) (hB : MemLp (fun z : Ω × Ω => B z.1 z.2) 2 (P.prod P)) :
    (∫ o : Fin n → Ω, |twoBlockStatistic BT BY F B o -
      ((∫ z, F z ∂P) - (∫ v, ∫ w, B v w ∂P ∂P))| ∂Measure.pi (fun _ => P)) ≤
      Real.sqrt (variance (treatmentTerm P BT B) (Measure.pi (fun _ => P))) +
      Real.sqrt (variance (outcomeTerm P BY F B) (Measure.pi (fun _ => P))) +
      Real.sqrt (variance (degenerateTerm P BT BY B) (Measure.pi (fun _ => P))) := by
  have hm := twoBlock_leg_moments P BT BY hdis F B hF hB
  have ht := (hm.1.1.integrable (by norm_num)).abs
  have hy := (hm.2.1.1.integrable (by norm_num)).abs
  have hc := (hm.2.2.1.integrable (by norm_num)).abs
  calc
    _ = ∫ o : Fin n → Ω,
        |treatmentTerm P BT B o + outcomeTerm P BY F B o + degenerateTerm P BT BY B o|
        ∂Measure.pi (fun _ => P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun o => congrArg abs
        (twoBlock_population_decomposition P BT BY hT hY F B hF hB o))
    _ ≤ ∫ o : Fin n → Ω,
        |treatmentTerm P BT B o| + |outcomeTerm P BY F B o| + |degenerateTerm P BT BY B o|
        ∂Measure.pi (fun _ => P) := by
      apply integral_mono ((((hm.1.1.add hm.2.1.1).add hm.2.2.1).integrable (by norm_num)).abs)
        ((ht.add hy).add hc)
      intro o
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (∫ o, |treatmentTerm P BT B o| ∂Measure.pi (fun _ => P)) +
        (∫ o, |outcomeTerm P BY F B o| ∂Measure.pi (fun _ => P)) +
        (∫ o, |degenerateTerm P BT BY B o| ∂Measure.pi (fun _ => P)) := by
      have hty : Integrable (fun o : Fin n → Ω =>
          |treatmentTerm P BT B o| + |outcomeTerm P BY F B o|)
          (Measure.pi (fun _ => P)) := ht.add hy
      rw [integral_add hty hc, integral_add ht hy]
    _ ≤ _ := add_le_add
      (add_le_add (twoBlock_abs_le_standard_deviation _ _ hm.1.1 hm.1.2)
        (twoBlock_abs_le_standard_deviation _ _ hm.2.1.1 hm.2.1.2))
      (twoBlock_abs_le_standard_deviation _ _ hm.2.2.1 hm.2.2.2)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
