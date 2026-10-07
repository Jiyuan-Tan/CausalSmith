module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CapacityAlphabetPadding
public import Causalean.Stat.Minimax.ChiSquaredFinite
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSqOverlap

/-! A two-cell parametric lower bound inside the capacity-active paired family. -/

public section
namespace CausalSmith.Stat.DiscreteBudgetvalueCurve
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private noncomputable def singletonSimplex : ProbabilitySimplex 1 :=
  ⟨fun _ => 1, by simp⟩

private noncomputable def singletonContrast (t : ℝ) (ht : t ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8)) :
    PairedContrasts 1 := ⟨fun _ => t, fun _ => ht⟩

private lemma obsLaw_real_jointMass {d : ℕ} (P : DiscreteLaw d) (z : Obs d) :
    (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw P).real {z} =
      jointMass P z.1 z.2.1 z.2.2 := by
  rw [Measure.real]
  unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton z)]
  rfl

private lemma pairedOne_obs_real (t : ℝ) (ht : t ∈ Set.Icc (-1/8 : ℝ) (1/8))
    (z : Obs 2) :
    (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
      (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))).real {z} =
      jointMass (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))
        z.1 z.2.1 z.2.2 := by
  exact obsLaw_real_jointMass _ z

private lemma pairedOne_joint_zero (t : ℝ) (ht : t ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8))
    (a y : Bool) :
    jointMass (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))
        (0 : Fin 2) a y =
      (1 / 4 : ℝ) * bernoulliMass (if a then 1 / 2 + t else 1 / 4) y := by
  simpa [singletonSimplex, singletonContrast, finProdFinEquiv] using
    pairedLaw_observedAtom singletonSimplex (singletonContrast t ht) (0 : Fin 1) false a y

private lemma pairedOne_joint_one (t : ℝ) (ht : t ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8))
    (a y : Bool) :
    jointMass (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))
        (1 : Fin 2) a y =
      (1 / 4 : ℝ) * bernoulliMass (if a then 1 / 2 - t else 1 / 4) y := by
  convert pairedLaw_observedAtom singletonSimplex (singletonContrast t ht)
    (0 : Fin 1) true a y using 1 <;>
      simp [singletonSimplex, singletonContrast, finProdFinEquiv] <;> ring

private lemma pairedOne_chiSq (t : ℝ) (ht : t ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8)) :
    Causalean.Stat.chiSqDiv
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
        (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht))))
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
        (observedMarginal (pairedLaw singletonSimplex
          (singletonContrast 0 (by norm_num))))) = 2 * t ^ 2 := by
  let Pt := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
        (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))
  let P0 := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
        (observedMarginal (pairedLaw singletonSimplex
          (singletonContrast 0 (by norm_num))))
  have hpos (z : Obs 2) : P0 {z} ≠ 0 := by
    have hp : 0 < P0.real {z} := by
      rw [pairedOne_obs_real]
      rcases z with ⟨j, a, y⟩
      fin_cases j <;> fin_cases a <;> fin_cases y <;>
        norm_num [pairedOne_joint_zero, pairedOne_joint_one, bernoulliMass]
    intro hz
    rw [Measure.real, hz] at hp
    simp at hp
  have hac : Pt ≪ P0 :=
    Causalean.Estimation.MinimaxATE.absolutelyContinuous_of_singleton_pos Pt P0 hpos
  have hs := Causalean.Stat.finite_one_add_chiSqDiv Pt P0 hac
  rw [show (∑ z : Obs 2, (Pt.real {z}) ^ 2 / P0.real {z}) = 1 + 2 * t ^ 2 by
    dsimp [Pt, P0]
    simp only [obsLaw_real_jointMass]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, pairedOne_joint_zero,
      pairedOne_joint_one, bernoulliMass]
    ring] at hs
  linarith

private lemma pairedOne_product_tv_le_half {n : ℕ} (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8))
    (htsq : 2 * (n : ℝ) * t ^ 2 ≤ Real.log 2) :
    Causalean.Stat.tvDist
      (productLaw (observedMarginal (pairedLaw singletonSimplex
        (singletonContrast 0 (by norm_num)))) n)
      (productLaw (observedMarginal (pairedLaw singletonSimplex
        (singletonContrast t ht))) n) ≤ 1 / 2 := by
  let P0 := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
    (observedMarginal (pairedLaw singletonSimplex (singletonContrast 0 (by norm_num))))
  let Pt := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
    (observedMarginal (pairedLaw singletonSimplex (singletonContrast t ht)))
  have hpos (z : Obs 2) : P0 {z} ≠ 0 := by
    have hp : 0 < P0.real {z} := by
      rw [obsLaw_real_jointMass]
      rcases z with ⟨j, a, y⟩
      fin_cases j <;> fin_cases a <;> fin_cases y <;>
        norm_num [pairedOne_joint_zero, pairedOne_joint_one, bernoulliMass]
    intro hz
    rw [Measure.real, hz] at hp
    simp at hp
  have hac : Pt ≪ P0 :=
    Causalean.Estimation.MinimaxATE.absolutelyContinuous_of_singleton_pos Pt P0 hpos
  have htensor := Causalean.Stat.one_add_chiSqDiv_pi_iid Pt P0 hac n
  have hsingle : Causalean.Stat.chiSqDiv Pt P0 = 2 * t ^ 2 :=
    pairedOne_chiSq t ht
  have hx0 : 0 ≤ 2 * t ^ 2 := by positivity
  have hpow : (1 + 2 * t ^ 2) ^ n ≤ Real.exp ((n : ℝ) * (2 * t ^ 2)) := by
    calc
      _ ≤ (Real.exp (2 * t ^ 2)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * t ^ 2)]) n
      _ = _ := by rw [← Real.exp_nat_mul]
  have hexp : Real.exp ((n : ℝ) * (2 * t ^ 2)) ≤ 2 := by
    calc
      Real.exp ((n : ℝ) * (2 * t ^ 2)) ≤ Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.2
        calc
          (n : ℝ) * (2 * t ^ 2) = 2 * n * t ^ 2 := by ring
          _ ≤ Real.log 2 := htsq
      _ = 2 := Real.exp_log (by norm_num)
  have hchi : Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => Pt)) (Measure.pi (fun _ : Fin n => P0)) ≤ 1 := by
    rw [hsingle] at htensor
    linarith
  have hacP : Measure.pi (fun _ : Fin n => Pt) ≪ Measure.pi (fun _ : Fin n => P0) :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      Pt P0 hac n
  rw [Causalean.Stat.tvDist_symm]
  change Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Pt))
      (Measure.pi (fun _ : Fin n => P0)) ≤ 1 / 2
  calc
    _ ≤ (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv
        (Measure.pi (fun _ : Fin n => Pt)) (Measure.pi (fun _ : Fin n => P0))) :=
      Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ _ hacP Integrable.of_finite
    _ ≤ (1 / 2) * Real.sqrt 1 := by gcongr
    _ = 1 / 2 := by norm_num

/-- On every alphabet containing two cells, a binary paired submodel gives a
uniform parametric capacity-active lower bound. With [the specified inputs and conditions](hyp:n,d,hn,hd,epsilon,he,he',mu,hmu,T), [the stated relationship holds](goal). -/
-- @node: small_capacity_lower_padded
lemma small_capacity_lower_padded {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (mu : PotentialLaw d → Measure (Fin n → Obs d))
    (hmu : ∀ Q, IidSampling (observedMarginal Q) (mu Q))
    (T : {f : (Fin n → Obs d) → ℝ // Measurable f}) :
    ∃ Q : PotentialLaw d, Q ∈ capacityHardClass d epsilon ∧
      1 / (4096 * (n : ℝ)) ≤
        Causalean.Stat.sqRisk (mu Q) T.1 (budgetValue Q (1 / 2)) := by
  let t : ℝ := 1 / (8 * Real.sqrt n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht8 : t ≤ 1 / 8 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 8 * Real.sqrt (n : ℝ))).2
    nlinarith
  have ht : t ∈ Set.Icc (-1/8 : ℝ) (1/8) := ⟨by linarith, ht8⟩
  have htsq : t ^ 2 = 1 / (64 * (n : ℝ)) := by
    dsimp [t]
    rw [div_pow, mul_pow, Real.sq_sqrt hnR.le]
    ring
  let Q0 : PotentialLaw 2 := pairedLaw singletonSimplex
    (singletonContrast 0 (by norm_num))
  let Qt : PotentialLaw 2 := pairedLaw singletonSimplex (singletonContrast t ht)
  have hQ0 : Q0 ∈ capacityHardClass 2 epsilon := by
    have hc := pairedLaw_completion singletonSimplex (singletonContrast 0 (by norm_num))
    obtain ⟨hm, heff, hbind, _, hvone, _⟩ :=
      (paired_capacity_identity 1 (by omega) epsilon he he').1 Q0
        ⟨singletonSimplex, singletonContrast 0 (by norm_num), hc⟩
        singletonSimplex (singletonContrast 0 (by norm_num)) hc
    exact ⟨hm, hvone, heff, hbind⟩
  have hQt : Qt ∈ capacityHardClass 2 epsilon := by
    have hc := pairedLaw_completion singletonSimplex (singletonContrast t ht)
    obtain ⟨hm, heff, hbind, _, hvone, _⟩ :=
      (paired_capacity_identity 1 (by omega) epsilon he he').1 Qt
        ⟨singletonSimplex, singletonContrast t ht, hc⟩
        singletonSimplex (singletonContrast t ht) hc
    exact ⟨hm, hvone, heff, hbind⟩
  have hv0 : budgetValue Q0 (1 / 2) = 3 / 8 := by
    have hb := (pairedCompletion_bindingValue Q0 singletonSimplex
      (singletonContrast 0 (by norm_num)) (pairedLaw_completion _ _)
      epsilon he he' (by omega)).2.1
    simpa [singletonSimplex, singletonContrast] using hb
  have hvt : budgetValue Qt (1 / 2) = 3 / 8 + t / 2 := by
    have hb := (pairedCompletion_bindingValue Qt singletonSimplex
      (singletonContrast t ht) (pairedLaw_completion _ _)
      epsilon he he' (by omega)).2.1
    convert hb using 1 <;>
      simp [singletonSimplex, singletonContrast, abs_of_nonneg ht0] <;> ring
  let Q0d := padPotentialLaw hd Q0
  let Qtd := padPotentialLaw hd Qt
  let Td : (Fin n → Obs 2) → ℝ := fun z => T.1 (fun i => padCausalObs hd (z i))
  have htv : Causalean.Stat.tvDist
      (productLaw (observedMarginal Q0) n) (productLaw (observedMarginal Qt) n) ≤ 1 / 2 := by
    apply pairedOne_product_tv_le_half hn t ht
    rw [htsq]
    have hlog : (1 / 32 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have hsep : 2 * (t / 4) ≤
      |budgetValue Q0 (1 / 2) - budgetValue Qt (1 / 2)| := by
    rw [hv0, hvt]
    rw [show (3 / 8 : ℝ) - (3 / 8 + t / 2) = -(t / 2) by ring,
      abs_neg, abs_of_nonneg (div_nonneg ht0 (by norm_num))]
    ring_nf
    exact le_rfl
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := productLaw (observedMarginal Q0) n)
    (P₁ := productLaw (observedMarginal Qt) n) (est := Td)
    (θ₀ := budgetValue Q0 (1 / 2)) (θ₁ := budgetValue Qt (1 / 2))
    (s := t / 4) (c := (1 / 2 : ℝ)) (measurable_of_finite _) hsep htv
  have hrisk (Q : PotentialLaw 2) :
      (t / 4) ^ 2 * (productLaw (observedMarginal Q) n).real
        {z | t / 4 ≤ |Td z - budgetValue Q (1 / 2)|} ≤
        Causalean.Stat.sqRisk (productLaw (observedMarginal Q) n) Td
          (budgetValue Q (1 / 2)) := by
    unfold Causalean.Stat.sqRisk
    have hm := mul_meas_ge_le_integral_of_nonneg
      (μ := productLaw (observedMarginal Q) n)
      (f := fun z => (Td z - budgetValue Q (1 / 2)) ^ 2)
      (ae_of_all _ (fun z => sq_nonneg _)) Integrable.of_finite ((t / 4) ^ 2)
    have hevent : {z | t / 4 ≤ |Td z - budgetValue Q (1 / 2)|} =
        {z | (t / 4) ^ 2 ≤ (Td z - budgetValue Q (1 / 2)) ^ 2} := by
      ext z
      simpa [sq_abs] using (sq_le_sq₀ (by positivity : 0 ≤ t / 4)
        (abs_nonneg (Td z - budgetValue Q (1 / 2)))).symm
    rw [hevent]
    exact hm
  have hmax : 1 / (4096 * (n : ℝ)) ≤ max
      (Causalean.Stat.sqRisk (productLaw (observedMarginal Q0) n) Td (budgetValue Q0 (1/2)))
      (Causalean.Stat.sqRisk (productLaw (observedMarginal Qt) n) Td (budgetValue Qt (1/2))) := by
    have hp : (1 / 4 : ℝ) ≤ max
        ((productLaw (observedMarginal Q0) n).real
          {z | t / 4 ≤ |Td z - budgetValue Q0 (1/2)|})
        ((productLaw (observedMarginal Qt) n).real
          {z | t / 4 ≤ |Td z - budgetValue Qt (1/2)|}) := by
      norm_num at hprob ⊢
      exact hprob
    calc
      1 / (4096 * (n : ℝ)) = (t / 4) ^ 2 * (1 / 4) := by
        rw [show (t / 4) ^ 2 * (1 / 4) = t ^ 2 / 64 by ring, htsq]
        field_simp
        norm_num
      _ ≤ (t / 4) ^ 2 * max _ _ := by gcongr
      _ = max ((t / 4) ^ 2 * _) ((t / 4) ^ 2 * _) := by
        rw [mul_max_of_nonneg _ _ (sq_nonneg (t / 4))]
      _ ≤ _ := max_le_max (hrisk Q0) (hrisk Qt)
  rcases le_max_iff.mp hmax with hcase | hcase
  · refine ⟨Q0d, padPotentialLaw_capacityHardClass (by omega) hd hQ0, ?_⟩
    rw [hmu Q0d]
    exact hcase.trans_eq (sqRisk_padPotentialLaw hd Q0 T.1 T.2)
  · refine ⟨Qtd, padPotentialLaw_capacityHardClass (by omega) hd hQt, ?_⟩
    rw [hmu Qtd]
    exact hcase.trans_eq (sqRisk_padPotentialLaw hd Qt T.1 T.2)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
