module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FiniteLaw

/-!
Existence and universal ATE identification for compatible finite potential laws.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Independent conditional Bernoulli completion followed by the factual outcome](goal).
-/
noncomputable def independentExtension {d : Nat} (P : DiscreteLaw d) : PotentialLaw d :=
  let mass : FullObs d → Real := fun z =>
    cellMass P z.1 * bernoulliMass (propensity P z.1) z.2.1 *
      bernoulliMass (outcomeMean P false z.1) z.2.2.2.1 *
      bernoulliMass (outcomeMean P true z.1) z.2.2.2.2 *
      (if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then 1 else 0)
  ⟨normalizedPMF mass (P.pmf.map (fun z => (z.1, z.2.1, z.2.2, false, false)))⟩
/-- [Under the stated inputs and conditions](hyp:d,P,j), The propensity is a probability even on the stipulated null cells.  This gives [the stated result](goal).-/
-- @node: propensity_mem_Icc
lemma propensity_mem_Icc {d : Nat} (P : DiscreteLaw d) (j : Fin d) :
    propensity P j ∈ Set.Icc (0 : Real) 1 := by
  by_cases hz : cellMass P j = 0
  · norm_num [propensity, hz]
  · have hp : 0 < cellMass P j := lt_of_le_of_ne (cellMass_nonneg P j) (Ne.symm hz)
    have hle : armMass P j true ≤ cellMass P j := by
      have hsum : cellMass P j = armMass P j true + armMass P j false := by
        simp [cellMass, armMass]
      linarith [armMass_nonneg P j false]
    simp only [propensity, if_neg hz, Set.mem_Icc]
    exact ⟨div_nonneg (armMass_nonneg P j true) hp.le, (div_le_one hp).mpr hle⟩

/-- [Under the stated inputs and conditions](hyp:r,hr,b), Each Bernoulli factor is nonnegative, including boundary probabilities.  This gives [the stated result](goal).-/
-- @node: bernoulliMass_nonneg
lemma bernoulliMass_nonneg (r : Real) (hr : r ∈ Set.Icc (0 : Real) 1) (b : Bool) :
    0 ≤ bernoulliMass r b := by
  cases b <;> simp [bernoulliMass, hr.1, sub_nonneg.mpr hr.2]

/-- [The factual-outcome indicator leaves a unit mass over all binary coordinates. ](goal)-/
-- @node: completion_binary_mass_sum
lemma completion_binary_mass_sum (e r0 r1 : Real) :
    (∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      bernoulliMass e a * bernoulliMass r0 y0 * bernoulliMass r1 y1 *
        (if y = (if a then y1 else y0) then 1 else 0)) = 1 := by
  simp [bernoulliMass]
  ring

/-- [Under the stated inputs and conditions](hyp:d,P), The independent completion table is normalized before applying the PMF constructor.  This gives [the stated result](goal).-/
-- @node: independentExtension_mass_sum
lemma independentExtension_mass_sum {d : Nat} (P : DiscreteLaw d) :
    (∑ z : FullObs d,
      cellMass P z.1 * bernoulliMass (propensity P z.1) z.2.1 *
        bernoulliMass (outcomeMean P false z.1) z.2.2.2.1 *
        bernoulliMass (outcomeMean P true z.1) z.2.2.2.2 *
        (if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then 1 else 0)) = 1 := by
  simp only [Fintype.sum_prod_type]
  have hcell (j : Fin d) :
      (∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        cellMass P j * bernoulliMass (propensity P j) a *
          bernoulliMass (outcomeMean P false j) y0 *
          bernoulliMass (outcomeMean P true j) y1 *
          (if y = (if a then y1 else y0) then 1 else 0)) = cellMass P j := by
    calc
      _ = cellMass P j * (∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
          bernoulliMass (propensity P j) a * bernoulliMass (outcomeMean P false j) y0 *
            bernoulliMass (outcomeMean P true j) y1 *
            (if y = (if a then y1 else y0) then 1 else 0)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = cellMass P j := by rw [completion_binary_mass_sum, mul_one]
  simp_rw [hcell]
  exact sum_cellMass P

/-- [Under the stated inputs and conditions](hyp:d,P,z), Normalization preserves the explicit completion table on every full atom.  This gives [the stated result](goal).-/
-- @node: independentExtension_fullMass
lemma independentExtension_fullMass {d : Nat} (P : DiscreteLaw d) (z : FullObs d) :
    fullMass (independentExtension P) z =
      cellMass P z.1 * bernoulliMass (propensity P z.1) z.2.1 *
        bernoulliMass (outcomeMean P false z.1) z.2.2.2.1 *
        bernoulliMass (outcomeMean P true z.1) z.2.2.2.2 *
        (if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then 1 else 0) := by
  apply normalizedPMF_toReal
  · intro w
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg (cellMass_nonneg P w.1)
        (bernoulliMass_nonneg _ (propensity_mem_Icc P w.1) _))
        (bernoulliMass_nonneg _ (outcomeMean_mem_Icc P false w.1) _))
        (bernoulliMass_nonneg _ (outcomeMean_mem_Icc P true w.1) _)
    · positivity
  · exact independentExtension_mass_sum P

/-- [Under the stated inputs and conditions](hyp:d,P), The completion assigns zero probability to every inconsistent factual outcome.  This gives [the stated result](goal).-/
-- @node: independentExtension_consistency
lemma independentExtension_consistency {d : Nat} (P : DiscreteLaw d) :
    Consistency (independentExtension P) := by
  intro z hz
  rw [independentExtension_fullMass, if_neg hz, mul_zero]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y0,y1), Summing the factual outcome gives the product conditional Bernoulli table.  This gives [the stated result](goal).-/
-- @node: independentExtension_poAtom
lemma independentExtension_poAtom {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a y0 y1 : Bool) :
    poAtom (independentExtension P) j a y0 y1 =
      cellMass P j * bernoulliMass (propensity P j) a *
        bernoulliMass (outcomeMean P false j) y0 *
        bernoulliMass (outcomeMean P true j) y1 := by
  simp only [poAtom, independentExtension_fullMass, Fintype.sum_bool]
  cases a <;> cases y0 <;> cases y1 <;> simp

/-- [Under the stated inputs and conditions](hyp:d,P), The potential-outcome pair and treatment factor conditionally on each covariate cell.  This gives [the stated result](goal).-/
-- @node: independentExtension_exchangeability
lemma independentExtension_exchangeability {d : Nat} (P : DiscreteLaw d) :
    ConditionalExchangeability (independentExtension P) := by
  intro j a y0 y1
  simp only [independentExtension_poAtom, Fintype.sum_bool]
  cases a <;> cases y0 <;> cases y1 <;> simp [bernoulliMass] <;> ring

/-- [Under the stated inputs and conditions](hyp:d,P,j,a), The propensity weights reconstruct both arm masses, including null cells.  This gives [the stated result](goal).-/
-- @node: cellMass_mul_bernoulli_propensity
lemma cellMass_mul_bernoulli_propensity {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a : Bool) :
    cellMass P j * bernoulliMass (propensity P j) a = armMass P j a := by
  have hsum : cellMass P j = armMass P j true + armMass P j false := by
    simp [cellMass, armMass]
  by_cases hz : cellMass P j = 0
  · have ha : armMass P j a = 0 := by
      cases a <;> linarith [armMass_nonneg P j true, armMass_nonneg P j false]
    simp [hz, ha]
  · cases a <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, propensity,
      if_neg hz]
    · field_simp
      linarith
    · field_simp

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y), The binary regression reconstructs the two outcome atom masses, including null arms.  This gives [the stated result](goal).-/
-- @node: armMass_mul_bernoulli_outcomeMean
lemma armMass_mul_bernoulli_outcomeMean {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a y : Bool) :
    armMass P j a * bernoulliMass (outcomeMean P a j) y = jointMass P j a y := by
  have hsum : armMass P j a = jointMass P j a true + jointMass P j a false := by
    simp [armMass]
  by_cases hz : armMass P j a = 0
  · have hy : jointMass P j a y = 0 := by
      cases y <;> linarith [jointMass_nonneg P j a true, jointMass_nonneg P j a false]
    simp [hz, hy]
  · cases y <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte, outcomeMean,
      markedMass]
    · field_simp
      linarith
    · field_simp

/-- [Under the stated inputs and conditions](hyp:d,H,j,a,y), Mapping a full law to its observed coordinates sums out both potential outcomes.  This gives [the stated result](goal).-/
-- @node: observedMarginal_jointMass
lemma observedMarginal_jointMass {d : Nat} (H : PotentialLaw d)
    (j : Fin d) (a y : Bool) :
    jointMass (observedMarginal H) j a y =
      ∑ y0 : Bool, ∑ y1 : Bool, fullMass H (j, a, y, y0, y1) := by
  have hm : (H.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))) (j, a, y) =
      ∑ y0 : Bool, ∑ y1 : Bool, H.pmf (j, a, y, y0, y1) := by
    rw [PMF.map_apply, tsum_fintype]
    cases a <;> cases y <;>
      simp [Fintype.sum_prod_type, Prod.mk.injEq, Finset.sum_add_distrib]
  simp only [jointMass, observedMarginal, hm, fullMass]
  rw [ENNReal.toReal_sum (fun y0 _ => by
    exact ENNReal.sum_ne_top.mpr (fun y1 _ => H.pmf.apply_ne_top _))]
  congr 1
  funext y0
  exact ENNReal.toReal_sum (fun y1 _ => H.pmf.apply_ne_top _)

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y), The completion reproduces every original complete-record mass exactly.  This gives [the stated result](goal).-/
-- @node: independentExtension_jointMass
lemma independentExtension_jointMass {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a y : Bool) :
    jointMass (observedMarginal (independentExtension P)) j a y = jointMass P j a y := by
  rw [observedMarginal_jointMass]
  simp only [independentExtension_fullMass, Fintype.sum_bool]
  have hbinary :
      (∑ y0 : Bool, ∑ y1 : Bool,
        cellMass P j * bernoulliMass (propensity P j) a *
          bernoulliMass (outcomeMean P false j) y0 *
          bernoulliMass (outcomeMean P true j) y1 *
          (if y = (if a then y1 else y0) then 1 else 0)) =
        cellMass P j * bernoulliMass (propensity P j) a *
          bernoulliMass (outcomeMean P a j) y := by
    cases a <;> cases y <;> simp [bernoulliMass] <;> ring
  simp only [Fintype.sum_bool] at hbinary
  rw [hbinary, cellMass_mul_bernoulli_propensity, armMass_mul_bernoulli_outcomeMean]

/-- [Under the stated inputs and conditions](hyp:d,P), The independent potential-outcome completion extends exactly the supplied observed law.  This gives [the stated result](goal).-/
-- @node: independentExtension_observedMarginal
lemma independentExtension_observedMarginal {d : Nat} (P : DiscreteLaw d) :
    observedMarginal (independentExtension P) = P := by
  have hpmf : (observedMarginal (independentExtension P)).pmf = P.pmf := by
    apply DFunLike.ext
    intro z
    rcases z with ⟨j, a, y⟩
    apply (ENNReal.toReal_eq_toReal_iff'
      ((observedMarginal (independentExtension P)).pmf.apply_ne_top _)
      (P.pmf.apply_ne_top _)).mp
    exact independentExtension_jointMass P j a y
  exact congrArg DiscreteLaw.mk hpmf

/-- Success mass of one potential outcome in a fixed covariate cell. -/
-- @node: potentialSuccessMass
noncomputable def potentialSuccessMass {d : Nat} (H : PotentialLaw d)
    (j : Fin d) (a : Bool) : Real :=
  ∑ a' : Bool, ∑ y0 : Bool, ∑ y1 : Bool, poAtom H j a' y0 y1 *
    (if (if a then y1 else y0) then 1 else 0)

/-- [Under the stated inputs and conditions](hyp:d,H,j,a,y0,y1), Potential-outcome marginal atom masses are nonnegative.  This gives [the stated result](goal).-/
-- @node: poAtom_nonneg
lemma poAtom_nonneg {d : Nat} (H : PotentialLaw d) (j : Fin d) (a y0 y1 : Bool) :
    0 ≤ poAtom H j a y0 y1 :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

/-- [Under the stated inputs and conditions](hyp:d,H,j), The full potential-outcome table and observed law have identical covariate masses.  This gives [the stated result](goal).-/
-- @node: observedMarginal_cellMass
lemma observedMarginal_cellMass {d : Nat} (H : PotentialLaw d) (j : Fin d) :
    cellMass (observedMarginal H) j =
      ∑ a : Bool, ∑ y0 : Bool, ∑ y1 : Bool, poAtom H j a y0 y1 := by
  simp only [cellMass, observedMarginal_jointMass, poAtom, Fintype.sum_bool]
  ring

/-- [Under the stated inputs and conditions](hyp:d,H,j,a), The full potential-outcome table and observed law have identical arm masses.  This gives [the stated result](goal).-/
-- @node: observedMarginal_armMass
lemma observedMarginal_armMass {d : Nat} (H : PotentialLaw d) (j : Fin d) (a : Bool) :
    armMass (observedMarginal H) j a =
      ∑ y0 : Bool, ∑ y1 : Bool, poAtom H j a y0 y1 := by
  simp only [armMass, observedMarginal_jointMass, poAtom, Fintype.sum_bool]
  ring

/-- [Under the stated inputs and conditions](hyp:d,H,hC,j,a), Consistency identifies factual success mass with selected potential success mass in each arm.  This gives [the stated result](goal).-/
-- @node: consistent_markedMass
lemma consistent_markedMass {d : Nat} (H : PotentialLaw d) (hC : Consistency H)
    (j : Fin d) (a : Bool) :
    markedMass (observedMarginal H) j a =
      ∑ y0 : Bool, ∑ y1 : Bool, poAtom H j a y0 y1 *
        (if (if a then y1 else y0) then 1 else 0) := by
  have hzero (a y0 y1 : Bool) :
      fullMass H (j, a, !(if a then y1 else y0), y0, y1) = 0 := by
    apply hC
    cases a <;> cases y0 <;> cases y1 <;> simp
  have hzfff := hzero false false false
  have hzfft := hzero false false true
  have hzftf := hzero false true false
  have hzftt := hzero false true true
  have hztff := hzero true false false
  have hztft := hzero true false true
  have hzttf := hzero true true false
  have hzttt := hzero true true true
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
    at hzfff hzfft hzftf hzftt hztff hztft hzttf hzttt
  cases a <;> simp [markedMass, observedMarginal_jointMass, poAtom,
    hzfff, hzfft, hzftf, hzftt, hztff, hztft, hzttf, hzttt]

/-- [Under the stated inputs and conditions](hyp:d,H,j,a), Each potential success mass is bounded by its covariate mass.  This gives [the stated result](goal).-/
-- @node: potentialSuccessMass_bounds
lemma potentialSuccessMass_bounds {d : Nat} (H : PotentialLaw d) (j : Fin d) (a : Bool) :
    0 ≤ potentialSuccessMass H j a ∧
      potentialSuccessMass H j a ≤ cellMass (observedMarginal H) j := by
  constructor
  · exact Finset.sum_nonneg (fun a' _ => Finset.sum_nonneg (fun y0 _ =>
      Finset.sum_nonneg (fun y1 _ => mul_nonneg (poAtom_nonneg H j a' y0 y1)
        (by positivity))))
  · rw [observedMarginal_cellMass]
    apply Finset.sum_le_sum
    intro a' _
    apply Finset.sum_le_sum
    intro y0 _
    apply Finset.sum_le_sum
    intro y1 _
    apply mul_le_of_le_one_right (poAtom_nonneg H j a' y0 y1)
    cases a <;> cases y0 <;> cases y1 <;> norm_num

/-- [Under the stated inputs and conditions](hyp:d,H,hC,hE,j,a), Summing conditional exchangeability over a potential success event gives
its identifying equation.  This gives [the stated result](goal).-/
-- @node: compatible_success_identity
lemma compatible_success_identity {d : Nat} (H : PotentialLaw d)
    (hC : Consistency H) (hE : ConditionalExchangeability H) (j : Fin d) (a : Bool) :
    markedMass (observedMarginal H) j a * cellMass (observedMarginal H) j =
      armMass (observedMarginal H) j a * potentialSuccessMass H j a := by
  rw [consistent_markedMass H hC, observedMarginal_cellMass, observedMarginal_armMass]
  simp only [potentialSuccessMass, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ y0 : Bool, ∑ y1 : Bool,
        (poAtom H j a y0 y1 *
          (∑ a' : Bool, ∑ y0' : Bool, ∑ y1' : Bool, poAtom H j a' y0' y1')) *
          (if (if a then y1 else y0) then 1 else 0) := by
      simp only [Fintype.sum_bool]
      ring
    _ = ∑ y0 : Bool, ∑ y1 : Bool,
        ((∑ y0' : Bool, ∑ y1' : Bool, poAtom H j a y0' y1') *
          (∑ a' : Bool, poAtom H j a' y0 y1)) *
          (if (if a then y1 else y0) then 1 else 0) := by
      simp_rw [hE j a]
    _ = _ := by
      simp only [Fintype.sum_bool]
      ring

/-- [Under the stated inputs and conditions](hyp:d,P,eps,heps,hP,H,hm,hC,hE,j,a), Overlap identifies each potential success mass without restricting the unseen coupling.  This gives [the stated result](goal).-/
-- @node: compatible_cell_mean
lemma compatible_cell_mean {d : Nat} (P : DiscreteLaw d) (eps : Real)
    (heps : 0 < eps) (hP : ModelClass d eps P) (H : PotentialLaw d)
    (hm : observedMarginal H = P) (hC : Consistency H)
    (hE : ConditionalExchangeability H) (j : Fin d) (a : Bool) :
    potentialSuccessMass H j a = cellMass P j * outcomeMean P a j := by
  have hid := compatible_success_identity H hC hE j a
  rw [hm] at hid
  by_cases hz : cellMass P j = 0
  · have hb := potentialSuccessMass_bounds H j a
    rw [hm, hz] at hb
    have hzero : potentialSuccessMass H j a = 0 := le_antisymm hb.2 hb.1
    simp [hz, hzero]
  · have hp : 0 < cellMass P j := lt_of_le_of_ne (cellMass_nonneg P j) (Ne.symm hz)
    have he := hP.overlap j hp
    have hs : 0 < armMass P j a := by
      rw [← cellMass_mul_bernoulli_propensity]
      apply mul_pos hp
      cases a
      · simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte]
        linarith [he.2]
      · simp only [bernoulliMass, ↓reduceIte]
        exact lt_of_lt_of_le heps he.1
    dsimp only [outcomeMean]
    field_simp
    nlinarith [hid]

/-- [Under the stated inputs and conditions](hyp:d,H), Finite expectation of the contrast equals the difference of the two potential success masses.  This gives [the stated result](goal).-/
-- @node: poContrast_eq_sum_potentialSuccessMass
lemma poContrast_eq_sum_potentialSuccessMass {d : Nat} (H : PotentialLaw d) :
    poContrast H = ∑ j : Fin d,
      (potentialSuccessMass H j true - potentialSuccessMass H j false) := by
  simp only [poContrast, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [potentialSuccessMass, poAtom]
  ring

/-- [Under the stated inputs and conditions](hyp:d,P,eps,heps,hP,H,hm,hC,hE), Every compatible extension identifies the same observable ATE under occupied-cell overlap.  This gives [the stated result](goal).-/
-- @node: compatible_poContrast
lemma compatible_poContrast {d : Nat} (P : DiscreteLaw d) (eps : Real)
    (heps : 0 < eps) (hP : ModelClass d eps P) (H : PotentialLaw d)
    (hm : observedMarginal H = P) (hC : Consistency H)
    (hE : ConditionalExchangeability H) : poContrast H = ateFunctional P := by
  rw [poContrast_eq_sum_potentialSuccessMass]
  apply Finset.sum_congr rfl
  intro j _
  rw [compatible_cell_mean P eps heps hP H hm hC hE j true,
    compatible_cell_mean P eps heps hP H hm hC hE j false]
  ring

-- @node: lem:causal-realization
/-- For an observed law with [at least two covariate cells](hyp:hd), [positive overlap](hyp:heps), [overlap at most one quarter](hyp:heps'), and [membership in the model class](hyp:hP), [the independent potential-outcome extension realizes the observed law, and every compatible exchangeable extension has the stated causal contrast](goal). -/
lemma causal_realization (d : Nat) (eps : Real) (P : DiscreteLaw d)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) (hP : ModelClass d eps P) :
    (observedMarginal (independentExtension P) = P ∧ Consistency (independentExtension P) ∧
      ConditionalExchangeability (independentExtension P)) ∧
    ∀ H : PotentialLaw d, observedMarginal H = P → Consistency H →
      -- @realizes H(compatible extension of the specified observed law P)
      ConditionalExchangeability H → poContrast H = ateFunctional P := by
  refine ⟨⟨independentExtension_observedMarginal P, independentExtension_consistency P,
    independentExtension_exchangeability P⟩, ?_⟩
  intro H hm hC hE
  exact compatible_poContrast P eps heps hP H hm hC hE

end CausalSmith.Stat.AnnotationRarearmFrontier
