module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Basic
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountProductMoments
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountVarianceAlgebra
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PoissonInverseMoments
public import Causalean.Stat.Concentration.Poisson.ConditionalProduct
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Probability.Independence.Integration

/-!
Overlap-uniform inverse-count arm bias and variance under independent Poisson counts.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- [Under the stated inputs and conditions](hyp:d,P,eps,hP,j,a), Both arms inherit the occupied-cell overlap floor, including zero-mass cells.  This gives [the stated result](goal).-/
-- @node: armMass_ge_overlap_cellMass
lemma armMass_ge_overlap_cellMass {d : Nat} (P : DiscreteLaw d) (eps : Real)
    (hP : ModelClass d eps P) (j : Fin d) (a : Bool) :
    eps * cellMass P j ≤ armMass P j a := by
  have hsum : cellMass P j = armMass P j true + armMass P j false := by
    simp [cellMass, armMass]
  by_cases hz : cellMass P j = 0
  · simpa [hz] using armMass_nonneg P j a
  · have hp : 0 < cellMass P j := lt_of_le_of_ne (cellMass_nonneg P j) (Ne.symm hz)
    have he := hP.overlap j hp
    simp only [propensity, if_neg hz] at he
    have h1 := (le_div_iff₀ hp).mp he.1
    have h0 := (div_le_iff₀ hp).mp he.2
    cases a
    · nlinarith
    · exact h1

/-- [Under the stated inputs and conditions](hyp:ht,heps,p,t,eps), The exponential missing-cell envelope has the sharp reciprocal-intensity bound.  This gives [the stated result](goal).-/
-- @node: inverse_count_exp_envelope
lemma inverse_count_exp_envelope (p t eps : Real) (ht : 0 < t) (heps : 0 < eps) :
    p * Real.exp (-(t * eps * p)) ≤ 1 / (Real.exp 1 * t * eps) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t * eps * p)
  apply (le_div_iff₀ (by positivity : 0 < Real.exp 1 * t * eps)).2
  have hscaled := mul_le_mul_of_nonneg_right h (Real.exp_pos 1).le
  rw [Real.exp_neg 1, inv_mul_cancel₀ (ne_of_gt (Real.exp_pos 1))] at hscaled
  nlinarith

/-- [Under the stated inputs and conditions](hyp:d,P,ht,heps,t,eps), The sum of exponential missing-cell masses is capped by one and by the cell budget.  This gives [the stated result](goal).-/
-- @node: inverse_count_missing_mass_bound
lemma inverse_count_missing_mass_bound {d : Nat} (P : DiscreteLaw d) (t eps : Real)
    (ht : 0 < t) (heps : 0 < eps) :
    (∑ j, cellMass P j * Real.exp (-(t * eps * cellMass P j))) ≤
      min 1 ((d : Real) / (Real.exp 1 * t * eps)) := by
  apply le_min
  · calc
      (∑ j, cellMass P j * Real.exp (-(t * eps * cellMass P j))) ≤
          ∑ j, cellMass P j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_of_le_one_right (cellMass_nonneg P j)
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg (mul_nonneg ht.le heps.le) (cellMass_nonneg P j)))
      _ = 1 := sum_cellMass P
  · calc
      (∑ j, cellMass P j * Real.exp (-(t * eps * cellMass P j))) ≤
          ∑ _j : Fin d, 1 / (Real.exp 1 * t * eps) := by
        exact Finset.sum_le_sum (fun j _ => inverse_count_exp_envelope _ _ _ ht heps)
      _ = (d : Real) / (Real.exp 1 * t * eps) := by simp [div_eq_mul_inv]

/-- [Under the stated inputs and conditions](hyp:d,P,a,ht,heps,hP,t,eps), The explicit inverse-count bias obeys the overlap-uniform bound without excluding null cells.  This gives [the stated result](goal).-/
-- @node: inverse_count_bias_bound
lemma inverse_count_bias_bound {d : Nat} (P : DiscreteLaw d) (a : Bool) (t eps : Real)
    (ht : 0 < t) (heps : 0 < eps) (hP : ModelClass d eps P) :
    |∑ j, armMass P j (!a) * outcomeMean P a j * Real.exp (-(t * armMass P j a))| ≤
      min 1 ((d : Real) / (Real.exp 1 * t * eps)) := by
  have hnonneg : 0 ≤ ∑ j, armMass P j (!a) * outcomeMean P a j *
      Real.exp (-(t * armMass P j a)) := by
    exact Finset.sum_nonneg (fun j _ => mul_nonneg
      (mul_nonneg (armMass_nonneg P j (!a)) (outcomeMean_mem_Icc P a j).1)
      (Real.exp_pos _).le)
  rw [abs_of_nonneg hnonneg]
  apply le_trans _ (inverse_count_missing_mass_bound P t eps ht heps)
  apply Finset.sum_le_sum
  intro j _
  have hv : armMass P j (!a) ≤ cellMass P j := by
    have hsum : cellMass P j = armMass P j true + armMass P j false := by
      simp [cellMass, armMass]
    cases a <;> simp only [Bool.not_false, Bool.not_true] <;>
      linarith [armMass_nonneg P j false, armMass_nonneg P j true]
  have hfactor : armMass P j (!a) * outcomeMean P a j ≤ cellMass P j :=
    (mul_le_of_le_one_right (armMass_nonneg P j (!a)) (outcomeMean_mem_Icc P a j).2).trans hv
  apply mul_le_mul hfactor _ (Real.exp_pos _).le (cellMass_nonneg P j)
  apply Real.exp_le_exp.mpr
  have hs := mul_le_mul_of_nonneg_left (armMass_ge_overlap_cellMass P eps hP j a) ht.le
  nlinarith

/-- [Under the stated inputs and conditions](hyp:d,P,a,j,t,ht), The Poisson reciprocal first-moment formula gives target minus missing-cell bias.  This gives [the stated result](goal).-/
-- @node: inverse_count_cell_mean_identity
lemma inverse_count_cell_mean_identity {d : Nat} (P : DiscreteLaw d) (a : Bool)
    (j : Fin d) (t : Real) (ht : 0 < t) :
    markedMass P j a * (1 + t * armMass P j (!a) *
      (if t * armMass P j a = 0 then 1 else
        (1 - Real.exp (-(t * armMass P j a))) / (t * armMass P j a))) =
      cellMass P j * outcomeMean P a j -
        armMass P j (!a) * outcomeMean P a j * Real.exp (-(t * armMass P j a)) := by
  have hsum : cellMass P j = armMass P j a + armMass P j (!a) := by
    cases a <;> simp [cellMass, armMass, add_comm]
  by_cases hs : armMass P j a = 0
  · have hq : markedMass P j a = 0 := by
      have hmass : armMass P j a = jointMass P j a true + jointMass P j a false := by
        simp [armMass]
      dsimp only [markedMass]
      linarith [jointMass_nonneg P j a true, jointMass_nonneg P j a false]
    simp [hs, hq, outcomeMean]
  · rw [if_neg (mul_ne_zero ht.ne' hs), hsum]
    dsimp only [outcomeMean]
    field_simp
    ring

/-- [Under the stated inputs and conditions](hyp:d,P,a,ht,heps,hP,t,eps), Summed cell means satisfy the claimed capped bias bound once the Poisson means are read back.  This gives [the stated result](goal).-/
-- @node: inverse_count_mean_bias_bound
lemma inverse_count_mean_bias_bound {d : Nat} (P : DiscreteLaw d) (a : Bool) (t eps : Real)
    (ht : 0 < t) (heps : 0 < eps) (hP : ModelClass d eps P) :
    |(∑ j, markedMass P j a * (1 + t * armMass P j (!a) *
      (if t * armMass P j a = 0 then 1 else
        (1 - Real.exp (-(t * armMass P j a))) / (t * armMass P j a)))) -
      (∑ j, cellMass P j * outcomeMean P a j)| ≤
      min 1 ((d : Real) / (Real.exp 1 * t * eps)) := by
  simp_rw [inverse_count_cell_mean_identity P a _ t ht]
  rw [Finset.sum_sub_distrib, sub_sub_cancel_left, abs_neg]
  exact inverse_count_bias_bound P a t eps ht heps hP

/-- [Under the stated hypotheses](hyp:hX,hlaw), Pull back Poisson integrability and the exact count mean along a measurable count.  This gives [the stated result](goal). -/
-- @node: inverse_count_count_moment
lemma inverse_count_count_moment {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (X : Om → Nat) (lam : NNReal)
    (hX : Measurable X) (hlaw : mu.map X = poissonMeasure lam) :
    Integrable (fun om => (X om : Real)) mu ∧
      (∫ om, (X om : Real) ∂mu) = (lam : Real) := by
  have hi := (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two lam).integrable
    (by norm_num)
  have hi' : Integrable (fun k : Nat => (k : Real)) (mu.map X) := hlaw.symm ▸ hi
  refine ⟨hi'.comp_measurable hX, ?_⟩
  rw [← integral_map hX.aemeasurable (by fun_prop), hlaw]
  exact Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment lam

/-- [Under the stated inputs and conditions](hyp:Om,mu,X,lam,u,hX,hlaw,hind), Independent Poisson factors give the exact inverse-count cell mean and integrability.  This gives [the stated result](goal).-/
-- @node: inverse_count_poisson_cell_mean
lemma inverse_count_poisson_cell_mean {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (X : Fin 3 → Om → Nat)
    (lam : Fin 3 → NNReal) (u : Real)
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, mu.map (X i) = poissonMeasure (lam i))
    (hind : iIndepFun X mu) :
    Integrable (fun om => (X 0 om : Real) / u *
      (1 + (X 2 om : Real) / ((X 1 om : Real) + 1))) mu ∧
    (∫ om, (X 0 om : Real) / u *
      (1 + (X 2 om : Real) / ((X 1 om : Real) + 1)) ∂mu) =
      (lam 0 : Real) / u * (1 + (lam 2 : Real) *
        (if (lam 1 : Real) = 0 then 1 else
          (1 - Real.exp (-(lam 1 : Real))) / (lam 1 : Real))) := by
  let f : Fin 3 → Nat → Real := fun i k =>
    if i = 1 then ((k : Real) + 1)⁻¹ else (k : Real)
  let V : Fin 3 → Om → Real := fun i om => f i (X i om)
  have hm (i) : Measurable (V i) := by
    dsimp [V, f]
    split_ifs <;> fun_prop
  have hi (i) : Integrable (V i) mu := by
    fin_cases i
    · simpa [V, f] using (inverse_count_count_moment mu (X 0) (lam 0) (hX 0) (hlaw 0)).1
    · have hg := (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two
        (lam 1)).integrable (by norm_num)
      have hg' : Integrable (fun k : Nat => ((k : Real) + 1)⁻¹) (mu.map (X 1)) := by
        simpa only [hlaw 1, Nat.cast_add, Nat.cast_one] using hg
      simpa [V, f, Function.comp_def] using hg'.comp_measurable (hX 1)
    · simpa [V, f] using (inverse_count_count_moment mu (X 2) (lam 2) (hX 2) (hlaw 2)).1
  have hv : iIndepFun V mu := hind.comp f (fun _ => measurable_of_countable _)
  have h01 : IndepFun (V 0) (V 1) mu := hv.indepFun (by decide)
  have hi01 := h01.integrable_mul (hi 0) (hi 1)
  have hpair : IndepFun (V 0 * V 1) (V 2) mu := hv.indepFun_mul_left (fun i => hm i) 0 1 2
    (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide)
  have h012 := hpair.integrable_mul hi01 (hi 2)
  have heq : (fun om => (X 0 om : Real) / u *
      (1 + (X 2 om : Real) / ((X 1 om : Real) + 1))) =
      (fun om => V 0 om / u + (V 0 om * V 1 om * V 2 om) / u) := by
    funext om
    simp [V, f, div_eq_mul_inv]
    ring
  rw [heq]
  refine ⟨((hi 0).div_const u).add (h012.div_const u), ?_⟩
  have hmean0 := (inverse_count_count_moment mu (X 0) (lam 0) (hX 0) (hlaw 0)).2
  have hmean2 := (inverse_count_count_moment mu (X 2) (lam 2) (hX 2) (hlaw 2)).2
  have hmean1 : (∫ om, V 1 om ∂mu) =
      (if (lam 1 : Real) = 0 then 1 else
        (1 - Real.exp (-(lam 1 : Real))) / (lam 1 : Real)) := by
    dsimp [V, f]
    rw [← integral_map (f := fun k : Nat => ((k : Real) + 1)⁻¹)
      (hX 1).aemeasurable (by fun_prop), hlaw 1]
    exact (poisson_inverse_moments (lam 1)).1
  have hp' : (∫ om, V 0 om * V 1 om * V 2 om ∂mu) =
      (∫ om, V 0 om ∂mu) * (∫ om, V 1 om ∂mu) * (∫ om, V 2 om ∂mu) := by
    change (∫ om, ((V 0 * V 1) * V 2) om ∂mu) = _
    rw [hpair.integral_mul_eq_mul_integral hi01.aestronglyMeasurable (hi 2).aestronglyMeasurable,
      h01.integral_mul_eq_mul_integral (hi 0).aestronglyMeasurable (hi 1).aestronglyMeasurable]
  have hdiv0 := (hi 0).div_const u
  have hdiv012 : Integrable (fun om => V 0 om * V 1 om * V 2 om / u) mu :=
    h012.div_const u
  integral_linearity
  rw [hp', hmean1]
  simp only [V, f, if_false, show (0 : Fin 3) ≠ 1 by decide,
    show (2 : Fin 3) ≠ 1 by decide] at *
  rw [hmean0, hmean2]
  ring

/-- [Under the stated hypotheses](hyp:hu,hmeas,hZ,hK,hW,hind), Reading back all independent Poisson cell means gives the arm expectation, including null cells.  This gives [the stated result](goal). -/
-- @node: inverse_count_poisson_arm_mean
lemma inverse_count_poisson_arm_mean {d : Nat} (P : DiscreteLaw d) (a : Bool)
    (u t : NNReal) (hu : 0 < u) {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (Z K W : Fin d → Om → Nat)
    (hmeas : ∀ j, Measurable (Z j) ∧ Measurable (K j) ∧ Measurable (W j))
    (hZ : ∀ j, mu.map (Z j) = poissonMeasure (u * Real.toNNReal (markedMass P j a)))
    (hK : ∀ j, mu.map (K j) = poissonMeasure (t * Real.toNNReal (armMass P j a)))
    (hW : ∀ j, mu.map (W j) = poissonMeasure (t * Real.toNNReal (armMass P j (!a))))
    (hind : iIndepFun
      (fun i : Fin 3 × Fin d => if i.1 = 0 then Z i.2 else if i.1 = 1 then K i.2 else W i.2) mu) :
    Integrable (fun om => ∑ j, (Z j om : Real) / (u : Real) *
      (1 + (W j om : Real) / ((K j om : Real) + 1))) mu ∧
    (∫ om, ∑ j, (Z j om : Real) / (u : Real) *
      (1 + (W j om : Real) / ((K j om : Real) + 1)) ∂mu) =
      ∑ j, markedMass P j a * (1 + (t : Real) * armMass P j (!a) *
        (if (t : Real) * armMass P j a = 0 then 1 else
          (1 - Real.exp (-((t : Real) * armMass P j a))) / ((t : Real) * armMass P j a))) := by
  have hcell (j : Fin d) :
      Integrable (fun om => (Z j om : Real) / (u : Real) *
        (1 + (W j om : Real) / ((K j om : Real) + 1))) mu ∧
      (∫ om, (Z j om : Real) / (u : Real) *
        (1 + (W j om : Real) / ((K j om : Real) + 1)) ∂mu) =
        markedMass P j a * (1 + (t : Real) * armMass P j (!a) *
          (if (t : Real) * armMass P j a = 0 then 1 else
            (1 - Real.exp (-((t : Real) * armMass P j a))) / ((t : Real) * armMass P j a))) := by
    let X : Fin 3 → Om → Nat := fun i => if i = 0 then Z j else if i = 1 then K j else W j
    let lam : Fin 3 → NNReal := fun i => if i = 0 then u * Real.toNNReal (markedMass P j a)
      else if i = 1 then t * Real.toNNReal (armMass P j a)
      else t * Real.toNNReal (armMass P j (!a))
    have hx (i) : Measurable (X i) := by
      dsimp [X]
      split_ifs <;> first | exact (hmeas j).1 | exact (hmeas j).2.1 | exact (hmeas j).2.2
    have hl (i) : mu.map (X i) = poissonMeasure (lam i) := by
      dsimp [X, lam]
      split_ifs <;> first | exact hZ j | exact hK j | exact hW j
    have hind' : iIndepFun X mu :=
      hind.precomp (g := fun i : Fin 3 => (i, j))
        (fun i i' h => (Prod.mk.inj h).1)
    have h := inverse_count_poisson_cell_mean mu X lam u hx hl hind'
    have hq : 0 ≤ markedMass P j a := jointMass_nonneg P j a true
    have hu' : (u : Real) ≠ 0 := (NNReal.coe_pos.mpr hu).ne'
    simpa [X, lam, NNReal.coe_mul, Real.coe_toNNReal _ hq,
      Real.coe_toNNReal _ (armMass_nonneg P j a),
      Real.coe_toNNReal _ (armMass_nonneg P j (!a)), mul_div_cancel_left₀ _ hu'] using h
  refine ⟨integrable_finset_sum _ (fun j _ => (hcell j).1), ?_⟩
  have hi (j : Fin d) : Integrable (fun om => (Z j om : Real) / (u : Real) *
      (1 + (W j om : Real) / ((K j om : Real) + 1))) mu := (hcell j).1
  integral_linearity
  exact Finset.sum_congr rfl (fun j _ => (hcell j).2)

/-- [Under the stated inputs and conditions](hyp:d,P,a,hu,ht,heps,hP,u,t,eps), Summing the numerical Poisson cell envelopes gives a universal arm envelope.  This gives [the stated result](goal).-/
-- @node: inverse_count_arm_variance_envelope
lemma inverse_count_arm_variance_envelope {d : Nat} (P : DiscreteLaw d) (a : Bool)
    (u t eps : Real) (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (hP : ModelClass d eps P) :
    (∑ j : Fin d,
      (markedMass P j a / u * (2 + 2 * (2 ^ 16 : Real) *
        ((t * armMass P j (!a)) ^ 2 + t * armMass P j (!a)) /
          (1 + t * armMass P j a) ^ 2) +
      markedMass P j a ^ 2 * (2 ^ 16 : Real) *
        (t * armMass P j (!a) / (1 + t * armMass P j a) ^ 2 +
          (t * armMass P j (!a)) ^ 2 * (t * armMass P j a) /
            (1 + t * armMass P j a) ^ 4))) ≤
      2 ^ 20 * (1 / (u * eps) + 1 / (t * eps)) := by
  have hcell (j : Fin d) := inverse_count_cell_variance_envelope
    (armMass P j a) (armMass P j (!a)) (markedMass P j a) u t eps (2 ^ 16)
    (armMass_nonneg P j a) (armMass_nonneg P j (!a)) (jointMass_nonneg P j a true)
    (show markedMass P j a ≤ armMass P j a by
      simp only [markedMass, armMass, Fintype.sum_bool]
      linarith [jointMass_nonneg P j a false]) hu ht heps (by positivity)
    (by
      have hsum : armMass P j a + armMass P j (!a) = cellMass P j := by
        cases a <;> simp [cellMass, armMass, add_comm]
      rw [hsum]
      exact armMass_ge_overlap_cellMass P eps hP j a)
  calc
    _ ≤ ∑ j : Fin d, (2 + 4 * (2 ^ 16 : Real)) *
        (armMass P j a + armMass P j (!a)) * (1 / (u * eps) + 1 / (t * eps)) :=
      Finset.sum_le_sum (fun j _ => hcell j)
    _ = (2 + 4 * (2 ^ 16 : Real)) * (1 / (u * eps) + 1 / (t * eps)) := by
      have hmass : ∑ j : Fin d, (armMass P j a + armMass P j (!a)) = 1 := by
        convert sum_cellMass P using 1
        apply Finset.sum_congr rfl
        intro j _
        cases a <;> simp [cellMass, armMass, add_comm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hmass, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

-- @node: lem:inverse-count-arm-risk
/-- Under the stated inputs and conditions, Independent Poisson count families yield the overlap-explicit arm bias and variance
guarantee. This gives [the stated conclusion](goal). -/
lemma inverse_count_arm_risk :
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
      |(∫ om, Hs om ∂mu) - psi| ≤ min 1 ((d : Real) / (Real.exp 1 * (t : Real) * eps)) ∧
      ProbabilityTheory.variance Hs mu ≤ C * (1 / ((u : Real) * eps) + 1 / ((t : Real) * eps)) :=
  by
    refine ⟨2 ^ 20, by norm_num, ?_⟩
    intro d eps P a u t Om _ mu _ Z K W hd heps heps' hP hu ht hmeas hZ hK hW hind
    dsimp only
    constructor
    · rw [(inverse_count_poisson_arm_mean P a u t hu mu Z K W hmeas hZ hK hW hind).2]
      exact inverse_count_mean_bias_bound P a t eps (NNReal.coe_pos.mpr ht) heps hP
    · have hvariance :
          ProbabilityTheory.variance (fun om => ∑ j : Fin d,
            (Z j om : Real) / (u : Real) *
              (1 + (W j om : Real) / ((K j om : Real) + 1))) mu ≤
          ∑ j : Fin d,
            (markedMass P j a / (u : Real) * (2 + 2 * (2 ^ 16 : Real) *
              (((t : Real) * armMass P j (!a)) ^ 2 +
                (t : Real) * armMass P j (!a)) /
                (1 + (t : Real) * armMass P j a) ^ 2) +
            markedMass P j a ^ 2 * (2 ^ 16 : Real) *
              ((t : Real) * armMass P j (!a) / (1 + (t : Real) * armMass P j a) ^ 2 +
                ((t : Real) * armMass P j (!a)) ^ 2 * ((t : Real) * armMass P j a) /
                  (1 + (t : Real) * armMass P j a) ^ 4)) := by
        let H : Fin d → Om → Real := fun j om =>
          (Z j om : Real) / (u : Real) *
            (1 + (W j om : Real) / ((K j om : Real) + 1))
        have hcell (j : Fin d) : MemLp (H j) 2 mu ∧ variance (H j) mu ≤
            markedMass P j a / (u : Real) * (2 + 2 * (2 ^ 16 : Real) *
              (((t : Real) * armMass P j (!a)) ^ 2 +
                (t : Real) * armMass P j (!a)) / (1 + (t : Real) * armMass P j a) ^ 2) +
            markedMass P j a ^ 2 * (2 ^ 16 : Real) *
              ((t : Real) * armMass P j (!a) / (1 + (t : Real) * armMass P j a) ^ 2 +
                ((t : Real) * armMass P j (!a)) ^ 2 * ((t : Real) * armMass P j a) /
                  (1 + (t : Real) * armMass P j a) ^ 4) := by
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
          simpa [X, lam, H, NNReal.coe_mul,
            Real.coe_toNNReal _ hq,
            Real.coe_toNNReal _ (armMass_nonneg P j a),
            Real.coe_toNNReal _ (armMass_nonneg P j (!a)),
            mul_div_cancel_left₀ _ hu', hscale] using h
        have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin d)))
            (fun j k => IndepFun (H j) (H k) mu) := by
          intro j _ k _ hjk
          let X : Fin 3 × Fin d → Om → Nat := fun i =>
            if i.1 = 0 then Z i.2 else if i.1 = 1 then K i.2 else W i.2
          have hx (i) : Measurable (X i) := by
            dsimp [X]
            split_ifs <;> first
            | exact (hmeas i.2).1
            | exact (hmeas i.2).2.1
            | exact (hmeas i.2).2.2
          simpa [X, H] using inverse_count_cell_blocks_independent mu X hx hind u j k hjk
        have hsum := IndepFun.variance_sum
          (s := Finset.univ) (X := H) (fun j _ => (hcell j).1) hpair
        change variance (fun om => ∑ j, H j om) mu ≤ _
        have hsum' : variance (fun om => ∑ j, H j om) mu = ∑ j, variance (H j) mu := by
          simpa only [← Finset.sum_fn] using hsum
        rw [hsum']
        exact Finset.sum_le_sum (fun j _ => (hcell j).2)
      exact hvariance.trans (inverse_count_arm_variance_envelope P a u t eps
        (NNReal.coe_pos.mpr hu) (NNReal.coe_pos.mpr ht) heps hP)

end CausalSmith.Stat.AnnotationRarearmFrontier
