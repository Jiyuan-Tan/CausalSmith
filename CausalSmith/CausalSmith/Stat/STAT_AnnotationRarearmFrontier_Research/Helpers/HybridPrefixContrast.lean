module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPrefixRisk

/-!
Square integrability and clipped contrast risk for the independent three-pool hybrid prefixes.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal

/-- [Under the stated hypotheses](hyp:hmeas,hZ,hJ,hK,hind), Independent Poisson counts give a square-integrable hybrid arm sum at every tuning.  This gives [the stated result](goal). -/
-- @node: hybrid_count_arm_memLp
lemma hybrid_count_arm_memLp {d : Nat} (L k0 : Nat) (B u tp t : Real)
    (P : DiscreteLaw d) (a : Bool) {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (Z J K : Bool → Fin d → Om → Nat)
    (hmeas : ∀ b j, Measurable (Z b j) ∧ Measurable (J b j) ∧ Measurable (K b j))
    (hZ : ∀ b j, mu.map (Z b j) = poissonMeasure (Real.toNNReal (u * markedMass P j b)))
    (hJ : ∀ b j, mu.map (J b j) = poissonMeasure (Real.toNNReal (tp * armMass P j b)))
    (hK : ∀ b j, mu.map (K b j) = poissonMeasure (Real.toNNReal (t * armMass P j b)))
    (hind : iIndepFun (fun i : Fin 3 × Bool × Fin d =>
      if i.1 = 0 then Z i.2.1 i.2.2 else if i.1 = 1 then J i.2.1 i.2.2
      else K i.2.1 i.2.2) mu) :
    MemLp (fun om => ∑ j, hybridCellValue L B k0 u t
      (Z a j om) (J a j om) (K a j om) (K (!a) j om)) 2 mu := by
  classical
  let X : Fin 4 × Fin d → Om → Nat := fun i =>
    if i.1 = 0 then J a i.2 else if i.1 = 1 then Z a i.2
    else if i.1 = 2 then K a i.2 else K (!a) i.2
  have hX (i) : Measurable (X i) := by
    dsimp [X]
    split_ifs <;> first
    | exact (hmeas a i.2).1
    | exact (hmeas a i.2).2.1
    | exact (hmeas a i.2).2.2
    | exact (hmeas (!a) i.2).2.2
  let idx : Fin 4 × Fin d → Fin 3 × Bool × Fin d := fun i =>
    if i.1 = 0 then (1,a,i.2) else if i.1 = 1 then (0,a,i.2)
    else if i.1 = 2 then (2,a,i.2) else (2,!a,i.2)
  have hinj : Function.Injective idx := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ h
    fin_cases i <;> fin_cases i' <;> simp [idx] at h ⊢ <;>
      exact h
  have hi : iIndepFun X mu := by
    have hh := hind.precomp hinj
    have hfun : (fun i : Fin 4 × Fin d =>
        if (idx i).1 = 0 then Z (idx i).2.1 (idx i).2.2
        else if (idx i).1 = 1 then J (idx i).2.1 (idx i).2.2
        else K (idx i).2.1 (idx i).2.2) = X := by
      funext ⟨i,j⟩
      fin_cases i <;> simp [idx, X]
    rw [hfun] at hh
    exact hh
  have hlaw := hybrid_four_count_product_law mu X hX hi
  simp only [X, Fin.reduceEq, if_true, if_false] at hlaw
  simp_rw [hJ, hZ, hK] at hlaw
  let nu := fun j => (poissonMeasure (Real.toNNReal (tp * armMass P j a))).prod
    (cellPoissonLaw u t (markedMass P j a) (armMass P j a) (armMass P j (!a)))
  let V := fun z : Nat × (Nat × Nat × Nat) =>
    hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2
  let (j : Fin d) : IsProbabilityMeasure (nu j) := by
    dsimp [nu, cellPoissonLaw]; infer_instance
  have hcell (j : Fin d) : MemLp V 2 (nu j) :=
    hybrid_pilot_cell_memLp L k0 B u tp t (markedMass P j a)
      (armMass P j a) (armMass P j (!a))
  have hsum : MemLp (fun z => ∑ j, V (z j)) 2 (Measure.pi nu) := by
    apply memLp_finsetSum
    intro j _
    exact (hcell j).comp_measurePreserving (measurePreserving_eval nu j)
  have hmap : Measurable (fun om j => (J a j om, Z a j om, K a j om, K (!a) j om)) := by
    apply measurable_pi_lambda
    intro j
    exact (hmeas a j).2.1.prodMk ((hmeas a j).1.prodMk
      ((hmeas a j).2.2.prodMk (hmeas (!a) j).2.2))
  have hlaw' : mu.map (fun om j => (J a j om, Z a j om, K a j om, K (!a) j om)) =
      Measure.pi nu := hlaw
  exact hsum.comp_measurePreserving ⟨hmap, hlaw'⟩

/-- [Under the stated inputs and conditions](hyp:d,P,B,a,L,k0,u,tp,t), Each ordered-prefix hybrid arm has finite second moment, including zero intensities.  This gives [the stated result](goal).-/
-- @node: hybrid_ordered_arm_memLp
lemma hybrid_ordered_arm_memLp {d : Nat} (P : DiscreteLaw d) (L k0 : Nat)
    (B : Real) (u tp t : NNReal) (a : Bool) :
    MemLp (hybridOrderedArmStatistic L B k0 u t a) 2
      (hybridPoissonPrefixLaw P u tp t) := by
  let Z := fun b j s => hybridPrefixCounts (d := d) s (Sum.inl (j,b,true))
  let J := fun b j s => hybridPrefixCounts (d := d) s (Sum.inr (Sum.inl (j,b)))
  let K := fun b j s => hybridPrefixCounts (d := d) s (Sum.inr (Sum.inr (j,b)))
  have hm (b j) : Measurable (Z b j) ∧ Measurable (J b j) ∧ Measurable (K b j) := by
    constructor
    · exact (measurable_pi_apply _).comp (hybridPrefixCounts_measurable d)
    · constructor <;> exact (measurable_pi_apply _).comp (hybridPrefixCounts_measurable d)
  have hZ (b j) : (hybridPoissonPrefixLaw P u tp t).map (Z b j) =
      poissonMeasure (Real.toNNReal ((u : Real) * markedMass P j b)) := by
    simpa only [Real.toNNReal_mul u.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_success_count_law P u tp t j b
  have hJ (b j) : (hybridPoissonPrefixLaw P u tp t).map (J b j) =
      poissonMeasure (Real.toNNReal ((tp : Real) * armMass P j b)) := by
    simpa only [Real.toNNReal_mul tp.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_pilot_count_law P u tp t j b
  have hK (b j) : (hybridPoissonPrefixLaw P u tp t).map (K b j) =
      poissonMeasure (Real.toNNReal ((t : Real) * armMass P j b)) := by
    simpa only [Real.toNNReal_mul t.coe_nonneg, Real.toNNReal_coe] using
      hybrid_prefix_factorial_count_law P u tp t j b
  have hi : iIndepFun (fun i : Fin 3 × Bool × Fin d =>
      if i.1 = 0 then Z i.2.1 i.2.2 else if i.1 = 1 then J i.2.1 i.2.2
      else K i.2.1 i.2.2) (hybridPoissonPrefixLaw P u tp t) := by
    convert hybrid_prefix_arm_counts_independent P u tp t using 1
    funext i s
    dsimp [Z,J,K]
    split_ifs <;> rfl
  exact hybrid_count_arm_memLp L k0 B u tp t P a
    (hybridPoissonPrefixLaw P u tp t) Z J K hm hZ hJ hK hi

/-- [Under the stated inputs and conditions](hyp:d,tun,s), The ordered clipped statistic is exactly the difference of the two hybrid arm sums.  This gives [the stated result](goal).-/
-- @node: hybrid_ordered_statistic_eq_contrast
lemma hybrid_ordered_statistic_eq_contrast {d : Nat} (tun : HybridTuning)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) :
    hybridOrderedPrefixStatistic tun s = max (-1) (min 1
      (hybridOrderedArmStatistic tun.L tun.B tun.k0 tun.u tun.t true s -
        hybridOrderedArmStatistic tun.L tun.B tun.k0 tun.u tun.t false s)) := by
  simp only [hybridOrderedPrefixStatistic, hybridOrderedArmStatistic,
    hybridPrefixCounts, Sum.elim_inl, Sum.elim_inr, Bool.not_true, Bool.not_false,
    Finset.sum_sub_distrib]

/-- Under the stated inputs and conditions, Squared-difference and clipping bounds aggregate the two arm risks without arm independence.  This gives [the stated result](goal). -/
-- @node: hybrid_ordered_prefix_contrast_risk
lemma hybrid_ordered_prefix_contrast_risk :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d)
      (u tp t : NNReal),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 → Real.exp 4096 ≤ (n : Real) * eps →
      ModelClass d eps P → (n : Real) / 32 ≤ (u : Real) →
      ((n : Real) + m) / 64 ≤ (tp : Real) →
      ((n : Real) + m) / 64 ≤ (t : Real) →
      1 / 3 ≤ (t : Real) / tp → (t : Real) / tp ≤ 3 →
      let L := Nat.floor (Real.log ((n : Real) * eps) / 1024)
      let B : Real := 2 ^ 20 * L / min (tp : Real) t
      let k0 := Nat.floor ((tp : Real) * B / 4)
      let H := fun a => hybridOrderedArmStatistic (d := d) L B k0 u t a
      Causalean.Stat.sqRisk (hybridPoissonPrefixLaw P u tp t)
        (fun s => max (-1) (min 1 (H true s - H false s))) (ateFunctional P) ≤
        C * (1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps * L)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := hybrid_ordered_prefix_arm_risk
  refine ⟨4 * C, by positivity, ?_⟩
  intro n m d eps P u tp t hn hd heps heps4 hS hP hu htp ht hlo hhi
  dsimp only
  let L := Nat.floor (Real.log ((n : Real) * eps) / 1024)
  let B : Real := 2 ^ 20 * L / min (tp : Real) t
  let k0 := Nat.floor ((tp : Real) * B / 4)
  let H := fun a => hybridOrderedArmStatistic (d := d) L B k0 u t a
  let psi := fun a => ∑ j : Fin d, cellMass P j * outcomeMean P a j
  let mu := hybridPoissonPrefixLaw P u tp t
  have hLp (a) : MemLp (H a) 2 mu := hybrid_ordered_arm_memLp P L k0 B u tp t a
  have hint (a) : Integrable (fun s => (H a s - psi a) ^ 2) mu :=
    ((hLp a).sub (memLp_const (psi a))).integrable_sq
  have hcontrast : Integrable (fun s => (H true s - H false s - ateFunctional P) ^ 2) mu :=
    (((hLp true).sub (hLp false)).sub (memLp_const (ateFunctional P))).integrable_sq
  have htau : ateFunctional P = psi true - psi false := by
    simp only [ateFunctional, psi, Finset.sum_sub_distrib, mul_sub]
  have hMSE (a) : (∫ s, (H a s - psi a) ^ 2 ∂mu) ≤
      C * (1 / ((n : Real) * eps) +
        ((d : Real) / (((n : Real) + m) * eps * L)) ^ 2) :=
    hbound n m d eps P a u tp t hn hd heps heps4 hS hP hu htp ht hlo hhi
  change (∫ s, (max (-1) (min 1 (H true s - H false s)) - ateFunctional P) ^ 2 ∂mu) ≤ _
  calc
    _ ≤ ∫ s, (H true s - H false s - ateFunctional P) ^ 2 ∂mu :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        hcontrast (Filter.Eventually.of_forall (fun s =>
          knownMarginal_clip_loss _ _ (ateFunctional_mem_Icc P)))
    _ ≤ ∫ s, (2 * (H true s - psi true) ^ 2 + 2 * (H false s - psi false) ^ 2) ∂mu := by
      apply integral_mono hcontrast ((hint true).const_mul 2 |>.add ((hint false).const_mul 2))
      intro s
      change (H true s - H false s - ateFunctional P) ^ 2 ≤
        2 * (H true s - psi true) ^ 2 + 2 * (H false s - psi false) ^ 2
      rw [htau]
      nlinarith [sq_nonneg ((H true s - psi true) + (H false s - psi false))]
    _ = 2 * (∫ s, (H true s - psi true) ^ 2 ∂mu) +
        2 * (∫ s, (H false s - psi false) ^ 2 ∂mu) := by
      rw [integral_add ((hint true).const_mul 2) ((hint false).const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith [hMSE true, hMSE false]

/-- The clipped ordered hybrid statistic is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: hybridOrderedPrefixStatistic_measurable
lemma hybridOrderedPrefixStatistic_measurable (d : Nat) (tun : HybridTuning) :
    Measurable (hybridOrderedPrefixStatistic (d := d) tun) := by
  let F : (Obs d ⊕ (AuxObs d ⊕ AuxObs d) → Nat) → Real := fun z =>
    max (-1) (min 1 (∑ j : Fin d,
      (hybridCellValue tun.L tun.B tun.k0 tun.u tun.t
        (z (Sum.inl (j,true,true))) (z (Sum.inr (Sum.inl (j,true))))
        (z (Sum.inr (Sum.inr (j,true)))) (z (Sum.inr (Sum.inr (j,false)))) -
      hybridCellValue tun.L tun.B tun.k0 tun.u tun.t
        (z (Sum.inl (j,false,true))) (z (Sum.inr (Sum.inl (j,false))))
        (z (Sum.inr (Sum.inr (j,false)))) (z (Sum.inr (Sum.inr (j,true)))))))
  have h := (measurable_of_countable F).comp (hybridPrefixCounts_measurable d)
  change Measurable (fun s => F (hybridPrefixCounts s)) at h
  unfold hybridOrderedPrefixStatistic
  simpa only [F, hybridPrefixCounts,
    Sum.elim_inl, Sum.elim_inr] using h

/-- [Under the stated inputs and conditions](hyp:d,tun,s), Clipping keeps every ordered hybrid output in the target interval.  This gives [the stated result](goal).-/
-- @node: hybridOrderedPrefixStatistic_mem_Icc
lemma hybridOrderedPrefixStatistic_mem_Icc {d : Nat} (tun : HybridTuning)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) :
    hybridOrderedPrefixStatistic tun s ∈ Set.Icc (-1) 1 := by
  rw [hybrid_ordered_statistic_eq_contrast]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

end CausalSmith.Stat.AnnotationRarearmFrontier
