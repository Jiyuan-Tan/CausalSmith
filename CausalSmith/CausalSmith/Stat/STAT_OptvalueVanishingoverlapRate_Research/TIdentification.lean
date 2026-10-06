module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.ArmwiseExtension
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Identification and completion of finite observed laws
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators ENNReal

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedClass_factorization {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (_hP : ObservedClass ε P) :
    ∀ x a,
      jointMass P x a true =
        cellMass P x * (if a then propensity P x else 1 - propensity P x) *
          outcomeMean P a x ∧
      jointMass P x a false =
        cellMass P x * (if a then propensity P x else 1 - propensity P x) *
          (1 - outcomeMean P a x) := by
  intro x a
  have hq (a y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have harm (a : Bool) :
      armMass P a x = jointMass P x a false + jointMass P x a true := by
    simp [armMass]
    ring
  have hcell : cellMass P x = armMass P false x + armMass P true x := by
    simp [cellMass, armMass]
    ring
  have hnonneg (a : Bool) : 0 ≤ armMass P a x := by
    rw [harm]
    exact add_nonneg (hq a false) (hq a true)
  have hmean (a : Bool) :
      armMass P a x * outcomeMean P a x = jointMass P x a true := by
    by_cases ha : armMass P a x = 0
    · have hzero : jointMass P x a true = 0 := by
        have h := harm a
        rw [ha] at h
        linarith [hq a false, hq a true]
      simp [ha, hzero]
    · rw [outcomeMean]
      field_simp [ha]
  have hfail (a : Bool) :
      armMass P a x * (1 - outcomeMean P a x) = jointMass P x a false := by
    rw [mul_sub, mul_one, hmean, harm]
    ring
  have hpropTrue : cellMass P x * propensity P x = armMass P true x := by
    by_cases hp : cellMass P x = 0
    · have ht : armMass P true x = 0 := by
        rw [hcell] at hp
        linarith [hnonneg false, hnonneg true]
      simp [hp, ht]
    · rw [propensity]
      field_simp [hp]
  have hpropFalse : cellMass P x * (1 - propensity P x) = armMass P false x := by
    rw [mul_sub, mul_one, hpropTrue, hcell]
    ring
  cases a with
  | false =>
      constructor
      · simpa [hpropFalse] using (hmean false).symm
      · simpa [hpropFalse] using (hfail false).symm
  | true =>
      constructor
      · simpa [hpropTrue] using (hmean true).symm
      · simpa [hpropTrue] using (hfail true).symm

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP), the [stated conclusion](goal) holds. -/
lemma armwiseExtension_cellVector {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) :
    armwiseExtensionFormula ε (cellVector P x) =
      cellMass P x * max (outcomeMean P false x) (outcomeMean P true x) := by
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have harm (a : Bool) : armMassVecFormula (cellVector P x) a = armMass P a x := by
    cases a <;> simp [armMassVecFormula, cellVector, armMass, cellIdx] <;> ring
  have hcoord (a : Bool) : (cellVector P x) (cellIdx a true) = jointMass P x a true := by
    cases a <;> simp [cellVector, cellIdx]
  have hpnonneg : 0 ≤ cellMass P x := by
    unfold cellMass
    exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun y _ => ENNReal.toReal_nonneg))
  by_cases hp : cellMass P x = 0
  · have hzero (a y : Bool) : jointMass P x a y = 0 := by
      have hq (b z : Bool) : 0 ≤ jointMass P x b z := ENNReal.toReal_nonneg
      simp [cellMass] at hp
      rcases a with _ | _ <;> rcases y with _ | _ <;>
        linarith [hq false false, hq false true, hq true false, hq true true]
    have hv : cellVector P x = 0 := by
      funext j
      fin_cases j <;> simp [cellVector, hzero]
    simp [hv, hp, armwiseExtensionFormula]
  · have hppos : 0 < cellMass P x := lt_of_le_of_ne hpnonneg (Ne.symm hp)
    obtain ⟨hlo, hhi⟩ := hP.overlap x hppos
    have htrue : ε * cellMass P x ≤ armMass P true x := by
      exact (le_div_iff₀ hppos).mp (by simpa [propensity] using hlo)
    have hfalse : ε * cellMass P x ≤ armMass P false x := by
      have hs : cellMass P x = armMass P false x + armMass P true x := by
        simp [cellMass, armMass]
        ring
      have ht : armMass P true x ≤ (1 - ε) * cellMass P x := by
        rw [propensity, div_le_iff₀ hppos] at hhi
        nlinarith
      nlinarith
    have hterm (a : Bool) :
        totalMassVecFormula (cellVector P x) * (cellVector P x) (cellIdx a true) /
          anchoredDenomFormula ε (cellVector P x) a =
        cellMass P x * outcomeMean P a x := by
      have ha : ε * cellMass P x ≤ armMass P a x := by
        cases a <;> assumption
      have ha_pos : 0 < armMass P a x := lt_of_lt_of_le (mul_pos hε hppos) ha
      rw [anchoredDenomFormula, hmass, harm, max_eq_left ha, hcoord, outcomeMean]
      ring
    have hv : cellVector P x ≠ 0 := by
      intro hz
      rw [hz] at hmass
      simp [totalMassVecFormula, armMassVecFormula] at hmass
      exact hp hmass.symm
    rw [armwiseExtensionFormula, if_neg hv, hterm false, hterm true]
    exact (mul_max_of_nonneg _ _ (le_of_lt hppos)).symm

-- @node: completionBernoulliMass
/-- For the displayed parameters, completionBernoulliMass is the object specified by this definition. For [the displayed parameters](hyp:p,y), [completionBernoulliMass](goal) is the defined object. -/
def completionBernoulliMass (p : ℝ) (y : Bool) : ℝ := if y then p else 1 - p

-- @node: completionFullMass
/-- For the displayed parameters, completionFullMass is the object specified by this definition. For [the displayed parameters](hyp:P,z), [completionFullMass](goal) is the defined object. -/
noncomputable def completionFullMass {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) : ℝ :=
  if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then
    jointMass P z.1 z.2.1 z.2.2.1 *
      completionBernoulliMass (outcomeMean P (!z.2.1) z.1)
        (if z.2.1 then z.2.2.2.1 else z.2.2.2.2)
  else 0

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma outcomeMean_mem_unitInterval {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) :
    outcomeMean P a x ∈ Set.Icc (0 : ℝ) 1 := by
  have hnum : 0 ≤ jointMass P x a true := ENNReal.toReal_nonneg
  have hden : 0 ≤ armMass P a x := by
    exact Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have hle : jointMass P x a true ≤ armMass P a x := by
    simp [armMass]
    exact ENNReal.toReal_nonneg
  exact ⟨div_nonneg hnum hden, div_le_one_of_le₀ hle hden⟩

-- @node: completionFullMass_nonneg_sum
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma completionFullMass_nonneg_sum {d : ℕ} (P : DiscreteLaw d) :
    (∀ z, 0 ≤ completionFullMass P z) ∧
      ∑ z : FullObs d, ENNReal.ofReal (completionFullMass P z) = 1 := by
  classical
  have hnonneg : ∀ z, 0 ≤ completionFullMass P z := by
    rintro ⟨x, a, y, y0, y1⟩
    have hm0 := outcomeMean_mem_unitInterval P (!a) x
    cases a <;> simp at hm0 ⊢ <;>
      simp [completionFullMass, completionBernoulliMass] <;>
      split_ifs
    all_goals
      first
      | exact le_rfl
      | apply mul_nonneg ENNReal.toReal_nonneg
        linarith [hm0.1, hm0.2]
  refine ⟨hnonneg, ?_⟩
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _hz => hnonneg z)]
  have hsum : ∑ z : FullObs d, completionFullMass P z =
      ∑ z : Obs d, jointMass P z.1 z.2.1 z.2.2 := by
    simp [Fintype.sum_prod_type, completionFullMass, completionBernoulliMass]
    ring_nf
  rw [hsum]
  simpa [jointMass] using
    (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm

-- @node: bernoulliCompletion
/-- For the displayed parameters, bernoulliCompletion is the object specified by this definition. For [the displayed parameters](hyp:P), [bernoulliCompletion](goal) is the defined object. -/
noncomputable def bernoulliCompletion {d : ℕ} (P : DiscreteLaw d) : PotentialLaw d :=
  ⟨PMF.ofFintype (fun z => ENNReal.ofReal (completionFullMass P z))
    (completionFullMass_nonneg_sum P).2⟩

-- @node: bernoulliCompletion_fullMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_fullMass {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) :
    fullMass (bernoulliCompletion P) z = completionFullMass P z := by
  rw [fullMass, bernoulliCompletion, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact (completionFullMass_nonneg_sum P).1 z

-- @node: bernoulliCompletion_pmf_toReal
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_pmf_toReal {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) :
    ((bernoulliCompletion P).pmf z).toReal = completionFullMass P z :=
  bernoulliCompletion_fullMass P z

-- @node: bernoulliCompletion_consistency
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_consistency {d : ℕ} (P : DiscreteLaw d) :
    Consistency (bernoulliCompletion P) := by
  intro z hz
  rw [bernoulliCompletion, PMF.ofFintype_apply, completionFullMass, if_neg hz]
  simp

-- @node: bernoulliCompletion_poAtom
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_poAtom {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a y0 y1 : Bool) :
    poAtom (bernoulliCompletion P) x a y0 y1 =
      jointMass P x a (if a then y1 else y0) *
        completionBernoulliMass (outcomeMean P (!a) x) (if a then y0 else y1) := by
  simp [poAtom, bernoulliCompletion_fullMass, completionFullMass]

-- @node: bernoulliCompletion_poAtom_factorization
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP), the [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_poAtom_factorization {d : ℕ} {ε : ℝ}
    (P : DiscreteLaw d) (hP : ObservedClass ε P)
    (x : Fin d) (a y0 y1 : Bool) :
    poAtom (bernoulliCompletion P) x a y0 y1 =
      cellMass P x * completionBernoulliMass (propensity P x) a *
        completionBernoulliMass (outcomeMean P false x) y0 *
          completionBernoulliMass (outcomeMean P true x) y1 := by
  have hf := observedClass_factorization ε P hP x false
  have ht := observedClass_factorization ε P hP x true
  fin_cases a <;> fin_cases y0 <;> fin_cases y1 <;>
    simp only [bernoulliCompletion_poAtom, completionBernoulliMass,
      Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.false_eq_true] at hf ht ⊢
  all_goals
    first | rw [ht.1] | rw [ht.2] | rw [hf.1] | rw [hf.2]
  all_goals ring

-- @node: bernoulliCompletion_observedMarginal
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_observedMarginal {d : ℕ} (P : DiscreteLaw d) :
    observedMarginal (bernoulliCompletion P) = P := by
  cases P with
  | mk pmf =>
    change ⟨_⟩ = (⟨pmf⟩ : DiscreteLaw d)
    congr 1
    apply PMF.ext
    rintro ⟨x, a, y⟩
    rw [← ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    change (PMF.map _ (bernoulliCompletion ⟨pmf⟩).pmf (x, a, y)).toReal = _
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq (fun z => by
      split
      · exact PMF.apply_ne_top _ _
      · simp), tsum_fintype]
    have hsum (f : FullObs d → ℝ) :
        ∑ z : FullObs d, f z =
          ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
            f (x, a, y, y0, y1) := by
      simp [Fintype.sum_prod_type]
    rw [hsum]
    simp only [apply_ite, ENNReal.toReal_zero]
    simp only [bernoulliCompletion_pmf_toReal]
    simp [completionFullMass, completionBernoulliMass]
    ring_nf
    fin_cases a <;> fin_cases y <;> simp [jointMass]

-- @node: poCellMass_eq_sum_poAtom
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poCellMass_eq_sum_poAtom {d : ℕ} (Q : PotentialLaw d) (x : Fin d) :
    poCellMass Q x = ∑ a : Bool, ∑ y0 : Bool, ∑ y1 : Bool, poAtom Q x a y0 y1 := by
  simp [poCellMass, poAtom, Fintype.sum_bool]
  ring

-- @node: poTreatMass_eq_sum_poAtom
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poTreatMass_eq_sum_poAtom {d : ℕ} (Q : PotentialLaw d) (x : Fin d) (a : Bool) :
    poTreatMass Q x a = ∑ y0 : Bool, ∑ y1 : Bool, poAtom Q x a y0 y1 := by
  simp [poTreatMass, poAtom, Fintype.sum_bool]
  ring

-- @node: bernoulliCompletion_exchangeability
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP), the [stated conclusion](goal) holds. -/
lemma bernoulliCompletion_exchangeability {d : ℕ} {ε : ℝ}
    (P : DiscreteLaw d) (hP : ObservedClass ε P) :
    ConditionalExchangeability (bernoulliCompletion P) := by
  intro x r a ya
  rw [poCellMass_eq_sum_poAtom, poTreatMass_eq_sum_poAtom]
  fin_cases r <;> fin_cases a <;> fin_cases ya <;>
    simp [poArmAtom, poPotentialMass,
      bernoulliCompletion_poAtom_factorization P hP,
      completionBernoulliMass] <;> ring

-- @node: observedMarginal_jointMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedMarginal_jointMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) (a y : Bool) :
    jointMass (observedMarginal Q) x a y =
      ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (x, a, y, y0, y1) := by
  classical
  have hmap : (observedMarginal Q).pmf (x, a, y) =
      ∑ y0 : Bool, ∑ y1 : Bool, Q.pmf (x, a, y, y0, y1) := by
    change (Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))) (x, a, y) = _
    rw [PMF.map_apply, tsum_fintype]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · fin_cases a <;> fin_cases y <;>
        simp [Fintype.sum_prod_type]
    · intro b _hb hbx
      simp [Ne.symm hbx]
    · simp
  rw [jointMass, hmap]
  simp [fullMass, ENNReal.toReal_add, PMF.apply_ne_top]

-- @node: observedMarginal_cellMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedMarginal_cellMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) :
    cellMass (observedMarginal Q) x = poCellMass Q x := by
  simp [cellMass, poCellMass, observedMarginal_jointMass]

-- @node: consistent_observed_selected_atom
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma consistent_observed_selected_atom {d : ℕ} (Q : PotentialLaw d)
    (h : Consistency Q) (x : Fin d) (r : Fin 2) (y : Bool) :
    jointMass (observedMarginal Q) x (r = 1) y =
      poArmAtom Q x r (r = 1) y := by
  have hs : ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) →
      fullMass Q z = 0 := by
    intro z hz
    simp [fullMass, h z hz]
  fin_cases r <;> fin_cases y <;>
    simp [observedMarginal_jointMass, poArmAtom, poAtom, hs]

-- @node: poTreatMass_eq_observed_armMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poTreatMass_eq_observed_armMass {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (a : Bool) :
    poTreatMass Q x a = armMass (observedMarginal Q) a x := by
  simp [poTreatMass, armMass, observedMarginal_jointMass, Fintype.sum_bool]

-- @node: poRegression_eq_poArmAtom_ratio
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poRegression_eq_poArmAtom_ratio {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (r : Fin 2) :
    poRegression Q r x =
      (∑ arm : Bool, poArmAtom Q x r arm true) / poCellMass Q x := by
  fin_cases r <;>
    simp [poRegression, poCellMass, poArmAtom, poAtom] <;>
    ring

-- @node: consistent_observed_armMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma consistent_observed_armMass {d : ℕ} (Q : PotentialLaw d) (h : Consistency Q)
    (x : Fin d) (r : Fin 2) :
    armMass (observedMarginal Q) (r = 1) x =
      ∑ y : Bool, poArmAtom Q x r (r = 1) y := by
  simp [armMass, consistent_observed_selected_atom Q h x r]

-- @node: poArmAtom_total_eq_cellMass
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poArmAtom_total_eq_cellMass {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (r : Fin 2) :
    (∑ a : Bool, ∑ y : Bool, poArmAtom Q x r a y) = poCellMass Q x := by
  fin_cases r <;>
    simp [poCellMass, poArmAtom, poAtom] <;>
    ring

-- @node: poRegression_eq_outcomeMean_of_pos
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hcons,hexch,hcell,harm), the [stated conclusion](goal) holds. -/
lemma poRegression_eq_outcomeMean_of_pos {d : ℕ} (Q : PotentialLaw d)
    (hcons : Consistency Q) (hexch : ConditionalExchangeability Q)
    (x : Fin d) (r : Fin 2)
    (hcell : 0 < cellMass (observedMarginal Q) x)
    (harm : 0 < armMass (observedMarginal Q) (r = 1) x) :
    poRegression Q r x = outcomeMean (observedMarginal Q) (r = 1) x := by
  have heq := hexch x r (r = 1) true
  rw [poTreatMass_eq_observed_armMass, ← observedMarginal_cellMass] at heq
  change poArmAtom Q x r (r = 1) true * cellMass (observedMarginal Q) x =
    armMass (observedMarginal Q) (r = 1) x *
      (∑ arm : Bool, poArmAtom Q x r arm true) at heq
  rw [consistent_observed_armMass Q hcons] at heq
  rw [consistent_observed_armMass Q hcons] at harm
  rw [poRegression_eq_poArmAtom_ratio, outcomeMean,
    consistent_observed_selected_atom Q hcons,
    consistent_observed_armMass Q hcons,
    ← observedMarginal_cellMass]
  field_simp [ne_of_gt hcell, ne_of_gt harm]
  nlinarith

-- @node: prop:identification
/-- [Every admissible observed law has a compatible potential-outcome completion, the oracle value of every admissible causal law equals the value identified from its observed marginal, and each covariate cell's armwise extension equals its mass times the larger conditional outcome mean](goal). -/
theorem identification :
    (∀ (d : ℕ) (ε : ℝ) (P : DiscreteLaw d),
      2 ≤ d → 0 < ε → ε ≤ 1 / 2 → ObservedClass ε P →
        ∃ Q : PotentialLaw d, CausalClass ε Q ∧ observedMarginal Q = P) ∧
    (∀ (d : ℕ) (ε : ℝ) (Q : PotentialLaw d),
      2 ≤ d → 0 < ε → ε ≤ 1 / 2 → CausalClass ε Q →
        oracleValue Q = observedValue (observedMarginal Q)) ∧
    (∀ (d : ℕ) (ε : ℝ) (P : DiscreteLaw d),
      2 ≤ d → 0 < ε → ε ≤ 1 / 2 → ObservedClass ε P →
      ∀ x : Fin d, armwiseExtension ε (cellVector P x) (cellVector_nonnegative P x) =
        cellMass P x * max (outcomeMean P false x) (outcomeMean P true x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d ε P _hd _hε _hεhalf hP
    refine ⟨bernoulliCompletion P, ?_, bernoulliCompletion_observedMarginal P⟩
    exact ⟨bernoulliCompletion_consistency P,
      bernoulliCompletion_exchangeability P hP,
      by simpa [bernoulliCompletion_observedMarginal P] using hP.overlap⟩
  · intro d ε Q _hd hε _hεhalf hQ
    rw [oracleValue, observedValue]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [← observedMarginal_cellMass]
    by_cases hx : cellMass (observedMarginal Q) x = 0
    · simp [hx]
    · have hnonneg : 0 ≤ cellMass (observedMarginal Q) x := by
        unfold cellMass jointMass
        positivity
      have hxpos : 0 < cellMass (observedMarginal Q) x :=
        lt_of_le_of_ne hnonneg (Ne.symm hx)
      obtain ⟨hlo, hhi⟩ := hQ.overlap x hxpos
      have ht : 0 < armMass (observedMarginal Q) true x := by
        have he : 0 < ε * cellMass (observedMarginal Q) x := mul_pos hε hxpos
        exact lt_of_lt_of_le he ((le_div_iff₀ hxpos).mp (by
          simpa [propensity] using hlo))
      have hsum : cellMass (observedMarginal Q) x =
          armMass (observedMarginal Q) false x +
            armMass (observedMarginal Q) true x := by
        simp [cellMass, armMass]
        ring
      have hf : 0 < armMass (observedMarginal Q) false x := by
        rw [propensity, div_le_iff₀ hxpos] at hhi
        nlinarith [mul_pos hε hxpos]
      rw [poRegression_eq_outcomeMean_of_pos Q hQ.consistency hQ.exchangeability
          x 0 hxpos (by simpa using hf),
        poRegression_eq_outcomeMean_of_pos Q hQ.consistency hQ.exchangeability
          x 1 hxpos (by simpa using ht)]
      rfl
  · intro d ε P _hd hε _hεhalf hP x
    exact armwiseExtension_cellVector ε P hε hP x

end CausalSmith.Stat.OptvalueVanishingoverlapRate
