module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.KnownMarginalUpper

/-!
Squared-risk assembly for the inverse-count Poisson baseline and numerical pool bounds.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated hypotheses](hyp:hu,hmeas,hZ,hK,hW,hind), Independent Poisson cell statistics have a square-integrable arm sum.  This gives [the stated result](goal). -/
-- @node: baseline_poisson_arm_memLp
lemma baseline_poisson_arm_memLp {d : Nat} (P : DiscreteLaw d) (a : Bool)
    (u t : NNReal) (hu : 0 < u) {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (Z K W : Fin d → Om → Nat)
    (hmeas : ∀ j, Measurable (Z j) ∧ Measurable (K j) ∧ Measurable (W j))
    (hZ : ∀ j, mu.map (Z j) = poissonMeasure (u * Real.toNNReal (markedMass P j a)))
    (hK : ∀ j, mu.map (K j) = poissonMeasure (t * Real.toNNReal (armMass P j a)))
    (hW : ∀ j, mu.map (W j) = poissonMeasure (t * Real.toNNReal (armMass P j (!a))))
    (hind : iIndepFun
      (fun i : Fin 3 × Fin d => if i.1 = 0 then Z i.2 else if i.1 = 1 then K i.2 else W i.2) mu) :
    MemLp (fun om => ∑ j, (Z j om : Real) / (u : Real) *
      (1 + (W j om : Real) / ((K j om : Real) + 1))) 2 mu := by
  apply memLp_finsetSum
  intro j _
  let X : Fin 3 → Om → Nat :=
    fun i => if i = 0 then Z j else if i = 1 then K j else W j
  let lam : Fin 3 → NNReal :=
    fun i => if i = 0 then u * Real.toNNReal (markedMass P j a)
      else if i = 1 then t * Real.toNNReal (armMass P j a)
      else t * Real.toNNReal (armMass P j (!a))
  have hx (i) : Measurable (X i) := by
    dsimp [X]
    split_ifs <;> first
    | exact (hmeas j).1
    | exact (hmeas j).2.1
    | exact (hmeas j).2.2
  have hl (i) : mu.map (X i) = poissonMeasure (lam i) := by
    dsimp [X, lam]
    split_ifs <;> first | exact hZ j | exact hK j | exact hW j
  have hind' : iIndepFun X mu :=
    hind.precomp (g := fun i : Fin 3 => (i, j))
      (fun i i' h => (Prod.mk.inj h).1)
  have h := inverse_count_poisson_cell_variance mu X lam u hx hl hind'
  have hq : 0 ≤ markedMass P j a := jointMass_nonneg P j a true
  have hu' : (u : Real) ≠ 0 := (NNReal.coe_pos.mpr hu).ne'
  have hscale : (u : Real) * markedMass P j a / (u : Real) ^ 2 =
      markedMass P j a / (u : Real) := by
    field_simp
  simpa [X, lam, NNReal.coe_mul,
    Real.coe_toNNReal _ hq,
    Real.coe_toNNReal _ (armMass_nonneg P j a),
    Real.coe_toNNReal _ (armMass_nonneg P j (!a)),
    mul_div_cancel_left₀ _ hu', hscale] using h.1

/-- [Under the stated inputs and conditions](hyp:Om,mu,H,hH,theta), Squared loss around any constant is variance plus squared bias.  This gives [the stated result](goal).-/
-- @node: baseline_mse_eq_variance_add_bias
lemma baseline_mse_eq_variance_add_bias {Om : Type} [MeasurableSpace Om]
    {mu : Measure Om} [IsProbabilityMeasure mu] {H : Om → Real}
    (hH : MemLp H 2 mu) (theta : Real) :
    (∫ om, (H om - theta) ^ 2 ∂mu) =
      variance H mu + ((∫ om, H om ∂mu) - theta) ^ 2 := by
  have hshift := hH.sub (memLp_const theta)
  have hv := variance_eq_sub hshift
  change variance (fun om => H om - theta) mu =
    (∫ om, (H om - theta) ^ 2 ∂mu) - (∫ om, H om - theta ∂mu) ^ 2 at hv
  rw [variance_sub_const hH.aestronglyMeasurable theta] at hv
  have hm : (∫ om, H om - theta ∂mu) = (∫ om, H om ∂mu) - theta := by
    rw [integral_sub (hH.integrable (by norm_num)) (integrable_const theta)]
    simp
  rw [hm] at hv
  linarith

/-- Under the stated inputs and conditions, The proved arm bias and variance bounds imply the uncapped squared-risk bound.  This gives [the stated result](goal). -/
-- @node: baseline_poisson_arm_mse
lemma baseline_poisson_arm_mse :
    ∃ C : Real, 0 < C ∧
    ∀ (d : Nat) (eps : Real) (P : DiscreteLaw d) (a : Bool) (u t : NNReal)
      (Om : Type) [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
      (Z K W : Fin d → Om → Nat),
      2 ≤ d → 0 < eps → eps ≤ 1 / 4 → ModelClass d eps P → 0 < u → 0 < t →
      (∀ j, Measurable (Z j) ∧ Measurable (K j) ∧ Measurable (W j)) →
      (∀ j, mu.map (Z j) = poissonMeasure (u * Real.toNNReal (markedMass P j a))) →
      (∀ j, mu.map (K j) = poissonMeasure (t * Real.toNNReal (armMass P j a))) →
      (∀ j, mu.map (W j) = poissonMeasure (t * Real.toNNReal (armMass P j (!a)))) →
      ProbabilityTheory.iIndepFun
        (fun i : Fin 3 × Fin d => if i.1 = 0 then Z i.2 else if i.1 = 1 then K i.2 else W i.2) mu →
      let Hs : Om → Real := fun om => ∑ j : Fin d,
        (Z j om : Real) / (u : Real) * (1 + (W j om : Real) / ((K j om : Real) + 1))
      let psi : Real := ∑ j : Fin d, cellMass P j * outcomeMean P a j
      (∫ om, (Hs om - psi) ^ 2 ∂mu) ≤
        C * (1 / ((u : Real) * eps) + 1 / ((t : Real) * eps)) +
          ((d : Real) / (Real.exp 1 * (t : Real) * eps)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := inverse_count_arm_risk
  refine ⟨C, hC, ?_⟩
  intro d eps P a u t Om _ mu _ Z K W hd heps heps' hP hu ht hmeas hZ hK hW hind
  dsimp only
  have hLp := baseline_poisson_arm_memLp P a u t hu mu Z K W hmeas hZ hK hW hind
  obtain ⟨hbias, hvar⟩ :=
    hbound d eps P a u t Om mu Z K W hd heps heps' hP hu ht hmeas hZ hK hW hind
  rw [baseline_mse_eq_variance_add_bias hLp]
  apply add_le_add hvar
  have hb := hbias.trans (min_le_right _ _)
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [sq_abs] using hs

/-- Under the stated inputs and conditions, The clipped Poisson contrast has risk at most four times the arm envelope;
independence between the two arms is unnecessary.  This gives [the stated result](goal). -/
-- @node: baseline_poisson_contrast_risk
lemma baseline_poisson_contrast_risk :
    ∃ C : Real, 0 < C ∧
    ∀ (d : Nat) (eps : Real) (P : DiscreteLaw d) (u t : NNReal)
      (Om : Type) [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
      (Z K : Bool → Fin d → Om → Nat),
      2 ≤ d → 0 < eps → eps ≤ 1 / 4 → ModelClass d eps P → 0 < u → 0 < t →
      (∀ a j, Measurable (Z a j) ∧ Measurable (K a j)) →
      (∀ a j, mu.map (Z a j) = poissonMeasure (u * Real.toNNReal (markedMass P j a))) →
      (∀ a j, mu.map (K a j) = poissonMeasure (t * Real.toNNReal (armMass P j a))) →
      (∀ a, iIndepFun
        (fun i : Fin 3 × Fin d => if i.1 = 0 then Z a i.2
          else if i.1 = 1 then K a i.2 else K (!a) i.2) mu) →
      let H : Bool → Om → Real := fun a om => ∑ j : Fin d,
        (Z a j om : Real) / (u : Real) *
          (1 + (K (!a) j om : Real) / ((K a j om : Real) + 1))
      (∫ om, (max (-1) (min 1 (H true om - H false om)) - ateFunctional P) ^ 2 ∂mu) ≤
        C * (1 / ((u : Real) * eps) + 1 / ((t : Real) * eps)) +
          4 * ((d : Real) / (Real.exp 1 * (t : Real) * eps)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := baseline_poisson_arm_mse
  refine ⟨4 * C, by positivity, ?_⟩
  intro d eps P u t Om _ mu _ Z K hd heps heps' hP hu ht hmeas hZ hK hind
  let H : Bool → Om → Real := fun a om => ∑ j : Fin d,
    (Z a j om : Real) / (u : Real) *
      (1 + (K (!a) j om : Real) / ((K a j om : Real) + 1))
  let psi : Bool → Real := fun a => ∑ j : Fin d, cellMass P j * outcomeMean P a j
  have hmeas' (a j) : Measurable (Z a j) ∧ Measurable (K a j) ∧
      Measurable (K (!a) j) := ⟨(hmeas a j).1, (hmeas a j).2, (hmeas (!a) j).2⟩
  have hLp (a) : MemLp (H a) 2 mu :=
    baseline_poisson_arm_memLp P a u t hu mu (Z a) (K a) (K (!a))
      (hmeas' a) (hZ a) (hK a) (hK (!a)) (hind a)
  have hMSE (a) : (∫ om, (H a om - psi a) ^ 2 ∂mu) ≤
      C * (1 / ((u : Real) * eps) + 1 / ((t : Real) * eps)) +
        ((d : Real) / (Real.exp 1 * (t : Real) * eps)) ^ 2 :=
    hbound d eps P a u t Om mu (Z a) (K a) (K (!a)) hd heps heps' hP hu ht
      (hmeas' a) (hZ a) (hK a) (hK (!a)) (hind a)
  have htau : ateFunctional P = psi true - psi false := by
    simp only [ateFunctional, psi, Finset.sum_sub_distrib, mul_sub]
  have hint (a) : Integrable (fun om => (H a om - psi a) ^ 2) mu :=
    ((hLp a).sub (memLp_const (psi a))).integrable_sq
  have hcontrast : Integrable (fun om =>
      (H true om - H false om - ateFunctional P) ^ 2) mu :=
    (((hLp true).sub (hLp false)).sub (memLp_const (ateFunctional P))).integrable_sq
  change (∫ om, (max (-1) (min 1 (H true om - H false om)) - ateFunctional P) ^ 2 ∂mu) ≤ _
  calc
    _ ≤ ∫ om, (H true om - H false om - ateFunctional P) ^ 2 ∂mu :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        hcontrast (Filter.Eventually.of_forall (fun om =>
          knownMarginal_clip_loss _ _ (ateFunctional_mem_Icc P)))
    _ ≤ ∫ om, (2 * (H true om - psi true) ^ 2 +
        2 * (H false om - psi false) ^ 2) ∂mu := by
      apply integral_mono hcontrast ((hint true).const_mul 2 |>.add ((hint false).const_mul 2))
      intro om
      change (H true om - H false om - ateFunctional P) ^ 2 ≤
        2 * (H true om - psi true) ^ 2 + 2 * (H false om - psi false) ^ 2
      rw [htau]
      nlinarith [sq_nonneg ((H true om - psi true) + (H false om - psi false))]
    _ = 2 * (∫ om, (H true om - psi true) ^ 2 ∂mu) +
        2 * (∫ om, (H false om - psi false) ^ 2 ∂mu) := by
      rw [integral_add ((hint true).const_mul 2) ((hint false).const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith [hMSE true, hMSE false]

/-- [Under the stated inputs and conditions](hyp:hn,n,m), The baseline's two disjoint pools have the lower sizes required by the roadmap.  This gives [the stated result](goal).-/
-- @node: baseline_pool_sizes
lemma baseline_pool_sizes (n m : Nat) (hn : 6 ≤ n) :
    (n : Real) / 3 ≤ (n / 2 : Nat) ∧
      ((n : Real) + m) / 2 ≤ (n - n / 2 + m : Nat) := by
  have hh : n ≤ 3 * (n / 2) := by omega
  have hg : n + m ≤ 2 * (n - n / 2 + m) := by omega
  have hh' : (n : Real) ≤ 3 * (n / 2 : Nat) := by exact_mod_cast hh
  have hg' : (n : Real) + m ≤ 2 * (n - n / 2 + m : Nat) := by exact_mod_cast hg
  constructor <;> linarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,heps',n,m), Zero on overflow adds at most two inverse label scales.  This gives [the stated result](goal).-/
-- @node: baseline_pool_overflow_bound
lemma baseline_pool_overflow_bound (n m : Nat) (eps : Real)
    (hn : 6 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    Real.exp (-(n / 2 : Nat)) + Real.exp (-(n - n / 2 + m : Nat)) ≤
      2 / ((n : Real) * eps) := by
  obtain ⟨hh, hg⟩ := baseline_pool_sizes n m hn
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < (n : Real) * eps := mul_pos hn0 heps
  have htail : Real.exp (-(n / 2 : Nat)) + Real.exp (-(n - n / 2 + m : Nat)) ≤
      2 * Real.exp (-(n : Real) / 3) := by
    have h1 := Real.exp_le_exp.mpr (show -(n / 2 : Nat) ≤ -(n : Real) / 3 by linarith)
    have h2 := Real.exp_le_exp.mpr
      (show -(n - n / 2 + m : Nat) ≤ -(n : Real) / 3 by
        linarith [Nat.cast_nonneg (α := Real) m])
    linarith
  have hx := Real.mul_exp_neg_le_exp_neg_one ((n : Real) / 3)
  rw [← neg_div] at hx
  have he : Real.exp (-1 : Real) ≤ 1 := by
    exact (Real.exp_le_exp.mpr (by norm_num : (-1 : Real) ≤ 0)).trans_eq Real.exp_zero
  have hprod : (n : Real) * eps * (2 * Real.exp (-(n : Real) / 3)) ≤ 2 := by
    have hne : (n : Real) * eps ≤ (n : Real) / 4 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hne (Real.exp_pos (-(n : Real) / 3)).le
    nlinarith
  exact htail.trans ((le_div_iff₀ hS).2 (by nlinarith [hprod]))

/-- [Under the stated inputs and conditions](hyp:hn,heps,heps',hC,d,n,m,eps,C), Substituting the pool intensities and absorbing overflow gives a numerical public-rate bound.  This gives [the stated result](goal).-/
-- @node: baseline_pool_rate_bound
lemma baseline_pool_rate_bound (n m d : Nat) (eps C : Real)
    (hn : 6 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) (hC : 0 < C) :
    C * (1 / (((n / 2 : Nat) : Real) / 8 * eps) +
        1 / (((n - n / 2 + m : Nat) : Real) / 8 * eps)) +
      4 * ((d : Real) / (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps)) ^ 2 +
      (Real.exp (-(n / 2 : Nat)) + Real.exp (-(n - n / 2 + m : Nat))) ≤
    (40 * C + 1026) * (1 / ((n : Real) * eps) +
      ((d : Real) / (((n : Real) + m) * eps)) ^ 2) := by
  obtain ⟨hh, hg⟩ := baseline_pool_sizes n m hn
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < (n : Real) * eps := mul_pos hn0 heps
  have hN : 0 < ((n : Real) + m) * eps := by positivity
  have hh0 : (0 : Real) < (n / 2 : Nat) := by linarith
  have hg0 : (0 : Real) < (n - n / 2 + m : Nat) := by
    linarith [Nat.cast_nonneg (α := Real) m]
  have hu : 0 < ((n / 2 : Nat) : Real) / 8 * eps := by positivity
  have ht : 0 < ((n - n / 2 + m : Nat) : Real) / 8 * eps := by positivity
  have hU : 1 / (((n / 2 : Nat) : Real) / 8 * eps) ≤ 24 / ((n : Real) * eps) := by
    apply (div_le_div_iff₀ hu hS).2
    nlinarith
  have hT : 1 / (((n - n / 2 + m : Nat) : Real) / 8 * eps) ≤
      16 / ((n : Real) * eps) := by
    apply (div_le_div_iff₀ ht hS).2
    nlinarith [Nat.cast_nonneg (α := Real) m]
  have he : 1 ≤ Real.exp (1 : Real) := by
    exact Real.exp_zero.symm.trans_le (Real.exp_le_exp.mpr (by norm_num : (0 : Real) ≤ 1))
  have hden : ((n : Real) + m) * eps ≤
      16 * (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps) := by
    have hm := mul_le_mul_of_nonneg_right he ht.le
    nlinarith
  have hratio : (d : Real) / (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps) ≤
      16 * ((d : Real) / (((n : Real) + m) * eps)) := by
    calc
      _ = (16 * (d : Real)) /
          (16 * (Real.exp 1 * ((n - n / 2 + m : Nat) : Real) / 8 * eps)) := by ring
      _ ≤ (16 * (d : Real)) / (((n : Real) + m) * eps) :=
        div_le_div_of_nonneg_left (by positivity) hN hden
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (by positivity) hratio 2
  have hov := baseline_pool_overflow_bound n m eps hn heps heps'
  have hvar := mul_le_mul_of_nonneg_left (add_le_add hU hT) hC.le
  have hi : 0 ≤ 1 / ((n : Real) * eps) := by positivity
  have hs : 0 ≤ ((d : Real) / (((n : Real) + m) * eps)) ^ 2 := sq_nonneg _
  have hCs := mul_nonneg hC.le hs
  simp only [div_eq_mul_inv] at hvar hov hsq hi hs hCs ⊢
  nlinarith

end CausalSmith.Stat.AnnotationRarearmFrontier
