module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FiniteLaw

/-!
Explicit diagnostic pair sharing its treatment-covariate marginal.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- The arbitrary real diagnostic amplitude is [positive and at most one eighth](goal).
@realizes \delta(arbitrary Real amplitude in (0,1/8]) -/
def LabelFloorAmplitude (delta : Real) : Prop := -- @realizes \delta(Real carrier; 0 < delta ≤ 1/8)
  0 < delta ∧ delta ≤ 1 / 8 -- @realizes \delta(amplitude in (0,1/8])

/--
[The displayed two-cell law, with total fallback outside legal scalar ranges](goal).
-/
noncomputable def labelFloorLaw (d : Nat) (eps delta : Real) (sign : Bool)
    (hd : 2 ≤ d) (_hdelta : LabelFloorAmplitude delta) : DiscreteLaw d :=
  let mass : Obs d → Real := fun z =>
    if z.1.val < 2 then (1 / 2) * bernoulliMass eps z.2.1 *
      bernoulliMass (if z.2.1 then 1 / 2 + (if sign then delta else -delta) else 1 / 2) z.2.2
    else 0
  ⟨normalizedPMF mass (PMF.pure (⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1 : 0 < 2)
    hd⟩, false, false))⟩
/-- The fixed endpoint [one eighth is a legal diagnostic amplitude](goal). -/
lemma labelFloorAmplitude_eighth : LabelFloorAmplitude (1 / 8) := by
  norm_num [LabelFloorAmplitude]

/-- [Under the stated inputs and conditions](hyp:S), The displayed scale choice [is a legal diagnostic amplitude for every scale](goal). -/
lemma labelFloorAmplitude_scaled (S : Real) :
    LabelFloorAmplitude (1 / (16 * Real.sqrt (max 1 S))) := by
  have hmax : (1 : Real) ≤ max 1 S := le_max_left _ _
  have hsqrt : (1 : Real) ≤ Real.sqrt (max 1 S) := by
    have h := Real.sqrt_le_sqrt hmax
    simpa only [Real.sqrt_one] using h
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 16 * Real.sqrt (max 1 S))).mpr
    nlinarith

/-- [Under the stated inputs and conditions](hyp:d,hd,r), Summing a constant over the two occupied covariates gives twice that constant.  This gives [the stated result](goal).-/
-- @node: labelFloor_sum_two_cells
lemma labelFloor_sum_two_cells (d : Nat) (hd : 2 ≤ d) (r : Real) :
    (∑ j : Fin d, if j.val < 2 then r else 0) = 2 * r := by
  let j0 : Fin d := ⟨0, by omega⟩
  let j1 : Fin d := ⟨1, by omega⟩
  have hsplit (j : Fin d) :
      (if j.val < 2 then r else 0) =
        (if j = j0 then r else 0) + (if j = j1 then r else 0) := by
    by_cases h0 : j = j0
    · subst j
      simp [j0, j1]
    · by_cases h1 : j = j1
      · subst j
        simp [j0, j1]
      · have hv0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
        have hv : ¬j.val < 2 := by omega
        simp [hv, h0, h1]
  simp_rw [hsplit]
  simp [Finset.sum_add_distrib, two_mul]

/-- [Under the stated inputs and conditions](hyp:heps,heps',hdelta,eps,delta,sign,a,y), The diagnostic table has nonnegative entries throughout the legal parameter range.  This gives [the stated result](goal).-/
-- @node: labelFloor_mass_nonneg
lemma labelFloor_mass_nonneg (eps delta : Real) (sign a y : Bool)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) (hdelta : LabelFloorAmplitude delta) :
    0 ≤ (1 / 2 : Real) * bernoulliMass eps a *
      bernoulliMass (if a then 1 / 2 + (if sign then delta else -delta) else 1 / 2) y := by
  rcases hdelta with ⟨hd, hd'⟩
  apply mul_nonneg
  · apply mul_nonneg (by norm_num)
    cases a <;> dsimp [bernoulliMass] <;> linarith
  · cases sign <;> cases a <;> cases y <;> dsimp [bernoulliMass] <;> linarith

/-- [Under the stated inputs and conditions](hyp:d,hd,sign,eps,delta), The displayed diagnostic table already has total mass one.  This gives [the stated result](goal).-/
-- @node: labelFloor_mass_sum
lemma labelFloor_mass_sum (d : Nat) (hd : 2 ≤ d) (eps delta : Real) (sign : Bool) :
    (∑ z : Obs d, if z.1.val < 2 then (1 / 2 : Real) * bernoulliMass eps z.2.1 *
      bernoulliMass (if z.2.1 then 1 / 2 + (if sign then delta else -delta) else 1 / 2) z.2.2
      else 0) = 1 := by
  simp only [Fintype.sum_prod_type]
  have hcell (j : Fin d) :
      (∑ a : Bool, ∑ y : Bool, if j.val < 2 then (1 / 2 : Real) * bernoulliMass eps a *
        bernoulliMass (if a then 1 / 2 + (if sign then delta else -delta) else 1 / 2) y
        else 0) = if j.val < 2 then 1 / 2 else 0 := by
    by_cases hj : j.val < 2
    · simp [hj, bernoulliMass, Fintype.sum_bool]
      ring
    · simp [hj]
  simp_rw [hcell]
  rw [labelFloor_sum_two_cells d hd]
  norm_num

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',j,eps,delta,a,y), Reading back a diagnostic atom gives exactly its specified table entry.  This gives [the stated result](goal).-/
-- @node: labelFloor_jointMass
lemma labelFloor_jointMass (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (j : Fin d) (a y : Bool) :
    jointMass (labelFloorLaw d eps delta sign hd hdelta) j a y =
      if j.val < 2 then (1 / 2 : Real) * bernoulliMass eps a *
        bernoulliMass (if a then 1 / 2 + (if sign then delta else -delta) else 1 / 2) y
      else 0 := by
  apply normalizedPMF_toReal
  · intro z
    by_cases hz : z.1.val < 2
    · simp only [if_pos hz]
      exact labelFloor_mass_nonneg eps delta sign _ _ heps heps' hdelta
    · simp only [if_neg hz, le_refl]
  · exact labelFloor_mass_sum d hd eps delta sign

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',j,a,eps,delta), Summing out the outcome leaves a diagnostic arm mass independent of the sign.  This gives [the stated result](goal).-/
-- @node: labelFloor_armMass
lemma labelFloor_armMass (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (j : Fin d) (a : Bool) :
    armMass (labelFloorLaw d eps delta sign hd hdelta) j a =
      if j.val < 2 then (1 / 2 : Real) * bernoulliMass eps a else 0 := by
  simp only [armMass, labelFloor_jointMass d eps delta sign hd hdelta heps heps',
    Fintype.sum_bool]
  by_cases hj : j.val < 2
  · cases a <;> simp [hj, bernoulliMass] <;> ring
  · simp [hj]

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',j,eps,delta), Each occupied diagnostic covariate has mass one half, and all other cells are null.  This gives [the stated result](goal).-/
-- @node: labelFloor_cellMass
lemma labelFloor_cellMass (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (j : Fin d) :
    cellMass (labelFloorLaw d eps delta sign hd hdelta) j =
      if j.val < 2 then (1 / 2 : Real) else 0 := by
  change (∑ a : Bool, armMass _ j a) = _
  simp only [labelFloor_armMass d eps delta sign hd hdelta heps heps', Fintype.sum_bool]
  by_cases hj : j.val < 2
  · simp [hj, bernoulliMass]
    ring
  · simp [hj]

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',j,hj,eps,delta), The occupied diagnostic propensities equal the public overlap floor.  This gives [the stated result](goal).-/
-- @node: labelFloor_propensity
lemma labelFloor_propensity (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (j : Fin d) (hj : j.val < 2) :
    propensity (labelFloorLaw d eps delta sign hd hdelta) j = eps := by
  simp [propensity, labelFloor_cellMass d eps delta sign hd hdelta heps heps',
    labelFloor_armMass d eps delta sign hd hdelta heps heps', hj, bernoulliMass]
  ring

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',eps,delta), Both signs of the diagnostic pair belong to the public model class.  This gives [the stated result](goal).-/
-- @node: labelFloor_model
lemma labelFloor_model (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ModelClass d eps (labelFloorLaw d eps delta sign hd hdelta) := by
  constructor
  intro j hp
  have hj : j.val < 2 := by
    by_contra h
    rw [labelFloor_cellMass d eps delta sign hd hdelta heps heps', if_neg h] at hp
    exact (lt_irrefl 0) hp
  rw [labelFloor_propensity d eps delta sign hd hdelta heps heps' j hj]
  exact ⟨le_rfl, by linarith⟩

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',j,hj,a,eps,delta), Diagnostic conditional means match the specified control and treated Bernoulli means.  This gives [the stated result](goal).-/
-- @node: labelFloor_outcomeMean
lemma labelFloor_outcomeMean (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (j : Fin d) (hj : j.val < 2) (a : Bool) :
    outcomeMean (labelFloorLaw d eps delta sign hd hdelta) a j =
      if a then 1 / 2 + (if sign then delta else -delta) else 1 / 2 := by
  simp only [outcomeMean, markedMass,
    labelFloor_jointMass d eps delta sign hd hdelta heps heps',
    labelFloor_armMass d eps delta sign hd hdelta heps heps', if_pos hj,
    bernoulliMass, ite_true]
  have heps0 : eps ≠ 0 := heps.ne'
  have heps1 : 1 - eps ≠ 0 := by linarith
  cases a <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;>
    field_simp <;> ring

/-- [Under the stated inputs and conditions](hyp:d,sign,hd,hdelta,heps,heps',eps,delta), Summing the two occupied-cell contrasts yields the signed diagnostic amplitude.  This gives [the stated result](goal).-/
-- @node: labelFloor_target
lemma labelFloor_target (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ateFunctional (labelFloorLaw d eps delta sign hd hdelta) =
      if sign then delta else -delta := by
  unfold ateFunctional
  have hterm (j : Fin d) : cellMass (labelFloorLaw d eps delta sign hd hdelta) j *
      (outcomeMean (labelFloorLaw d eps delta sign hd hdelta) true j -
        outcomeMean (labelFloorLaw d eps delta sign hd hdelta) false j) =
      if j.val < 2 then (1 / 2 : Real) * (if sign then delta else -delta) else 0 := by
    by_cases hj : j.val < 2
    · rw [labelFloor_cellMass d eps delta sign hd hdelta heps heps', if_pos hj,
        labelFloor_outcomeMean d eps delta sign hd hdelta heps heps' j hj true,
        labelFloor_outcomeMean d eps delta sign hd hdelta heps heps' j hj false, if_pos hj]
      simp
    · rw [labelFloor_cellMass d eps delta sign hd hdelta heps heps', if_neg hj]
      simp [hj]
  simp_rw [hterm]
  rw [labelFloor_sum_two_cells d hd]
  ring

/-- [Under the stated inputs and conditions](hyp:d,P,j,a), The real mass of a projected treatment-covariate atom is its arm-cell mass.  This gives [the stated result](goal).-/
-- @node: auxMarginal_toReal_armMass
lemma auxMarginal_toReal_armMass {d : Nat} (P : DiscreteLaw d) (j : Fin d) (a : Bool) :
    (auxMarginal P (j, a)).toReal = armMass P j a := by
  have hm : auxMarginal P (j, a) = ∑ y : Bool, P.pmf (j, a, y) := by
    rw [auxMarginal, PMF.map_apply, tsum_fintype]
    cases a <;> simp [Fintype.sum_prod_type, Prod.mk.injEq, Finset.sum_add_distrib]
  rw [hm, ENNReal.toReal_sum (fun y _ => P.pmf.apply_ne_top _)]
  rfl

/-- [Under the stated inputs and conditions](hyp:d,hd,hdelta,heps,heps',eps,delta), The positive and negative diagnostic laws have exactly the same auxiliary PMF.  This gives [the stated result](goal).-/
-- @node: labelFloor_auxMarginal
lemma labelFloor_auxMarginal (d : Nat) (eps delta : Real) (hd : 2 ≤ d)
    (hdelta : LabelFloorAmplitude delta) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    auxMarginal (labelFloorLaw d eps delta true hd hdelta) =
      auxMarginal (labelFloorLaw d eps delta false hd hdelta) := by
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff'
    ((auxMarginal _).apply_ne_top z) ((auxMarginal _).apply_ne_top z)).mp
  rcases z with ⟨j, a⟩
  rw [auxMarginal_toReal_armMass, auxMarginal_toReal_armMass,
    labelFloor_armMass d eps delta true hd hdelta heps heps',
    labelFloor_armMass d eps delta false hd hdelta heps heps']

/--
[Finite natural-log divergence sums population mass times the log probability ratio](goal).
-/
noncomputable def finiteKL {d : Nat} (P Q : DiscreteLaw d) : Real :=
  ∑ z : Obs d, (P.pmf z).toReal * Real.log ((P.pmf z).toReal / (Q.pmf z).toReal)

/-- [Under the stated inputs and conditions](hyp:d,eps,hd,heps,heps'), At amplitude one eighth the diagnostic one-record KL has its exact stated value.  This gives [the stated result](goal).-/
-- @node: labelFloor_KL_eighth
lemma labelFloor_KL_eighth (d : Nat) (eps : Real) (hd : 2 ≤ d)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    finiteKL (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth)
      (labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth) =
      eps * Real.log (5 / 3) / 4 := by
  have heps0 : eps ≠ 0 := heps.ne'
  have heps1 : 1 - eps ≠ 0 := by linarith
  have hlog : Real.log (3 / 5 : Real) = -Real.log (5 / 3 : Real) := by
    rw [show (3 / 5 : Real) = (5 / 3)⁻¹ by norm_num, Real.log_inv]
  unfold finiteKL
  change (∑ z : Obs d,
    jointMass (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth)
      z.1 z.2.1 z.2.2 * Real.log
        (jointMass (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth)
          z.1 z.2.1 z.2.2 /
         jointMass (labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth)
          z.1 z.2.1 z.2.2)) = _
  simp only [Fintype.sum_prod_type]
  have hcell (j : Fin d) :
      (∑ a : Bool, ∑ y : Bool,
        jointMass (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth) j a y *
          Real.log (jointMass (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth)
            j a y / jointMass (labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth)
            j a y)) =
      if j.val < 2 then eps * Real.log (5 / 3) / 8 else 0 := by
    simp only [labelFloor_jointMass d eps (1 / 8) true hd labelFloorAmplitude_eighth heps heps',
      labelFloor_jointMass d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps',
      Fintype.sum_bool]
    by_cases hj : j.val < 2
    · simp [hj, bernoulliMass]
      rw [mul_div_mul_left _ _ (mul_ne_zero (by norm_num : (2 : Real)⁻¹ ≠ 0) heps0),
        mul_div_mul_left _ _ (mul_ne_zero (by norm_num : (2 : Real)⁻¹ ≠ 0) heps0)]
      norm_num
      rw [hlog]
      ring
    · simp [hj]
  simp_rw [hcell]
  rw [labelFloor_sum_two_cells d hd]
  ring

end CausalSmith.Stat.AnnotationRarearmFrontier
