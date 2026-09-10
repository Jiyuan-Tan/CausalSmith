import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.GlobalLipschitz

/-! Identification, global extension bounds, and equivalence of observed and causal experiments. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

-- @node: completionBernoulliMass
/-- For [the specified success probability, binary value](hyp:p,y), the [completion Bernoulli mass assigns probability p to success and one minus p to failure](goal). -/
def completionBernoulliMass (p : ℝ) (y : Bool) : ℝ := if y then p else 1 - p

-- @node: completionFullMass
/-- For [the specified discrete law, data point or sample](hyp:P,z), the [completion full-data mass equals the observed joint mass times the counterfactual Bernoulli mass when consistency holds, and zero otherwise](goal). -/
noncomputable def completionFullMass {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) : ℝ :=
  if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then
    jointMass P z.1 z.2.1 z.2.2.1 *
      completionBernoulliMass (outcomeMean P (!z.2.1) z.1)
        (if z.2.1 then z.2.2.2.1 else z.2.2.2.2)
  else 0

-- @node: jointMass_nonneg
/-- [the stated joint mass nonnegativity relation holds](goal). -/
lemma jointMass_nonneg {d : ℕ} (P : DiscreteLaw d) (x : Fin d) (a y : Bool) :
    0 ≤ jointMass P x a y := ENNReal.toReal_nonneg

-- @node: cellMass_nonneg
/-- [the stated cell mass nonnegativity relation holds](goal). -/
lemma cellMass_nonneg {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    0 ≤ cellMass P x := by
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => jointMass_nonneg P x a y

-- @node: outcomeMean_mem_unitInterval
/-- [the stated outcome mean mem unit interval relation holds](goal). -/
lemma outcomeMean_mem_unitInterval {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) :
    outcomeMean P a x ∈ Set.Icc (0 : ℝ) 1 := by
  have hnum := jointMass_nonneg P x a true
  have hden : 0 ≤ armMass P a x := by
    exact Finset.sum_nonneg fun y _ => jointMass_nonneg P x a y
  have hle : jointMass P x a true ≤ armMass P a x := by
    simp [armMass]
    exact jointMass_nonneg P x a false
  exact ⟨div_nonneg hnum hden, div_le_one_of_le₀ hle hden⟩

-- @node: completionFullMass_nonneg_sum
/-- [the completion masses are nonnegative and their extended-real sum is one](goal). -/
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
      | apply mul_nonneg (jointMass_nonneg P x _ y)
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
/-- For [the specified discrete law](hyp:P), the [Bernoulli completion is the potential-outcome law obtained from the completion masses](goal). -/
noncomputable def bernoulliCompletion {d : ℕ} (P : DiscreteLaw d) : PotentialLaw d :=
  ⟨PMF.ofFintype (fun z => ENNReal.ofReal (completionFullMass P z))
    (completionFullMass_nonneg_sum P).2⟩

-- @node: vectorMass_cellVector_optimal
/-- [the total mass of a cell vector equals the observed cell mass](goal). -/
lemma vectorMass_cellVector_optimal {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    vectorMass (cellVector P x) = cellMass P x := by
  simp [vectorMass, vectorArmMass, cellVector, cellMass, finTwoEquiv]
  ring

-- @node: vectorArmMass_cellVector_optimal
/-- [the arm mass of a cell vector equals the observed arm mass](goal). -/
lemma vectorArmMass_cellVector_optimal {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (a : Fin 2) :
    vectorArmMass (cellVector P x) a = armMass P (finTwoEquiv a) x := by
  rcases a with ⟨a, ha⟩
  interval_cases a <;>
    simp [vectorArmMass, cellVector, armMass, finTwoEquiv] <;> ring

-- @node: cellVector_mem_overlapCone_optimal
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [every observed cell vector belongs to the overlap cone](goal). -/
lemma cellVector_mem_overlapCone_optimal {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) (x : Fin d) :
    cellVector P x ∈ overlapCone epsilon := by
  refine ⟨fun j => jointMass_nonneg P x (finTwoEquiv j.1) (finTwoEquiv j.2), ?_, ?_⟩
  · rw [vectorMass_cellVector_optimal, vectorArmMass_cellVector_optimal]
    by_cases hp : 0 < cellMass P x
    · exact (le_div_iff₀ hp).mp (hP.overlap x hp).1
    · have hp0 : cellMass P x = 0 := le_antisymm (le_of_not_gt hp) (cellMass_nonneg P x)
      have ha : 0 ≤ armMass P true x := by
        exact Finset.sum_nonneg fun y _ => jointMass_nonneg P x true y
      have hle : armMass P true x ≤ cellMass P x := by
        simp [armMass, cellMass]
        nlinarith [jointMass_nonneg P x false false, jointMass_nonneg P x false true]
      have ha0 : armMass P true x = 0 := le_antisymm (hle.trans_eq hp0) ha
      simpa [hp0, ha0, finTwoEquiv]
  · rw [vectorMass_cellVector_optimal, vectorArmMass_cellVector_optimal]
    by_cases hp : 0 < cellMass P x
    · exact (div_le_iff₀ hp).mp (hP.overlap x hp).2
    · have hp0 : cellMass P x = 0 := le_antisymm (le_of_not_gt hp) (cellMass_nonneg P x)
      have ha : 0 ≤ armMass P true x := by
        exact Finset.sum_nonneg fun y _ => jointMass_nonneg P x true y
      have hle : armMass P true x ≤ cellMass P x := by
        simp [armMass, cellMass]
        nlinarith [jointMass_nonneg P x false false, jointMass_nonneg P x false true]
      have ha0 : armMass P true x = 0 := le_antisymm (hle.trans_eq hp0) ha
      simpa [hp0, ha0, finTwoEquiv]

-- @node: armCellValue_cellVector
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the arm value of a cell vector equals cell mass times the corresponding outcome mean](goal). -/
lemma armCellValue_cellVector {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) (x : Fin d) (a : Fin 2) :
    armCellValue epsilon a (cellVector P x) =
      cellMass P x * outcomeMean P (finTwoEquiv a) x := by
  have hcone := cellVector_mem_overlapCone_optimal P hP x
  have hmass := vectorMass_cellVector_optimal P x
  have harm := vectorArmMass_cellVector_optimal P x a
  by_cases hp : cellMass P x = 0
  · have ha_nonneg : 0 ≤ armMass P (finTwoEquiv a) x := by
      exact Finset.sum_nonneg fun y _ => jointMass_nonneg P x (finTwoEquiv a) y
    have ha_le : armMass P (finTwoEquiv a) x ≤ cellMass P x := by
      rcases a with ⟨a, ha⟩
      interval_cases a <;> simp [armMass, cellMass, finTwoEquiv] <;>
        nlinarith [jointMass_nonneg P x false false, jointMass_nonneg P x false true,
          jointMass_nonneg P x true false, jointMass_nonneg P x true true]
    have ha0 : armMass P (finTwoEquiv a) x = 0 :=
      le_antisymm (ha_le.trans_eq hp) ha_nonneg
    simp [armCellValue, hmass, hp]
  · have hp_pos : 0 < cellMass P x := lt_of_le_of_ne (cellMass_nonneg P x) (Ne.symm hp)
    have hden : epsilon * cellMass P x ≤ armMass P (finTwoEquiv a) x := by
      have ht : epsilon * cellMass P x ≤ armMass P true x := by
        simpa [vectorMass_cellVector_optimal, vectorArmMass_cellVector_optimal,
          finTwoEquiv] using hcone.2.1
      have hf : epsilon * cellMass P x ≤ armMass P false x := by
        have hsum : cellMass P x = armMass P false x + armMass P true x := by
          simp [cellMass, armMass]
          ring
        have hu : armMass P true x ≤ (1 - epsilon) * cellMass P x := by
          simpa [vectorMass_cellVector_optimal, vectorArmMass_cellVector_optimal,
            finTwoEquiv] using hcone.2.2
        nlinarith
      fin_cases a
      · simpa [finTwoEquiv] using hf
      · simpa [finTwoEquiv] using ht
    rw [armCellValue, if_neg (by simpa [hmass] using hp), hmass, harm,
      max_eq_left hden]
    unfold outcomeMean
    have hzEq : cellVector P x (a, 1) = jointMass P x (finTwoEquiv a) true := by
      rcases a with ⟨a, ha⟩
      interval_cases a <;> simp [cellVector, finTwoEquiv]
    rw [hzEq]
    ring

-- @node: globalCellValue_cellVector
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the global cell value equals cell mass times the larger of the two outcome means](goal). -/
lemma globalCellValue_cellVector {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) (x : Fin d) :
    globalCellValue epsilon (cellVector P x) =
      cellMass P x * max (outcomeMean P false x) (outcomeMean P true x) := by
  rw [globalCellValue, armCellValue_cellVector P hP x 0,
    armCellValue_cellVector P hP x 1]
  change max (cellMass P x * outcomeMean P false x)
      (cellMass P x * outcomeMean P true x) = _
  by_cases hle : outcomeMean P false x ≤ outcomeMean P true x
  · rw [max_eq_right hle, max_eq_right
      (mul_le_mul_of_nonneg_left hle (cellMass_nonneg P x))]
  · have hle' := le_of_not_ge hle
    rw [max_eq_left hle', max_eq_left
      (mul_le_mul_of_nonneg_left hle' (cellMass_nonneg P x))]

-- @node: bernoulliCompletion_fullMass
/-- [each full-data atom of the Bernoulli completion has its prescribed completion mass](goal). -/
@[simp] lemma bernoulliCompletion_fullMass {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) :
    fullMass (bernoulliCompletion P) z = completionFullMass P z := by
  rw [fullMass, bernoulliCompletion, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact (completionFullMass_nonneg_sum P).1 z

-- @node: bernoulliCompletion_pmf_toReal
/-- [the real-valued atom probability of the Bernoulli completion equals its completion mass](goal). -/
@[simp] lemma bernoulliCompletion_pmf_toReal {d : ℕ} (P : DiscreteLaw d) (z : FullObs d) :
    ((bernoulliCompletion P).pmf z).toReal = completionFullMass P z :=
  bernoulliCompletion_fullMass P z

-- @node: completionFullMass_ofReal_toReal
/-- [converting a completion mass to an extended nonnegative real and back leaves it unchanged](goal). -/
@[simp] lemma completionFullMass_ofReal_toReal {d : ℕ} (P : DiscreteLaw d)
    (z : FullObs d) :
    (ENNReal.ofReal (completionFullMass P z)).toReal = completionFullMass P z :=
  ENNReal.toReal_ofReal ((completionFullMass_nonneg_sum P).1 z)

-- @node: bernoulliCompletion_consistency
/-- [the Bernoulli completion satisfies consistency](goal). -/
lemma bernoulliCompletion_consistency {d : ℕ} (P : DiscreteLaw d) :
    Consistency (bernoulliCompletion P) := by
  intro z hz
  rw [bernoulliCompletion_fullMass, completionFullMass, if_neg hz]

-- @node: bernoulliCompletion_poAtom
/-- [each potential-outcome atom of the Bernoulli completion factors into the observed joint mass and the missing-outcome Bernoulli mass](goal). -/
lemma bernoulliCompletion_poAtom {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a y0 y1 : Bool) :
    poAtom (bernoulliCompletion P) x a y0 y1 =
      jointMass P x a (if a then y1 else y0) *
        completionBernoulliMass (outcomeMean P (!a) x) (if a then y0 else y1) := by
  simp [poAtom, bernoulliCompletion_fullMass, completionFullMass]

-- @node: bernoulliCompletion_poAtom_factorization
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [each potential-outcome atom factors into cell mass, treatment propensity, and the two Bernoulli outcome masses](goal). -/
lemma bernoulliCompletion_poAtom_factorization {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P)
    (x : Fin d) (a y0 y1 : Bool) :
    poAtom (bernoulliCompletion P) x a y0 y1 =
      cellMass P x * completionBernoulliMass (propensity P x) a *
        completionBernoulliMass (outcomeMean P false x) y0 *
          completionBernoulliMass (outcomeMean P true x) y1 := by
  have hf := observedModelClass_factorization P hP x false
  have ht := observedModelClass_factorization P hP x true
  fin_cases a <;> fin_cases y0 <;> fin_cases y1 <;>
    simp only [bernoulliCompletion_poAtom, completionBernoulliMass,
      Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.false_eq_true] at hf ht ⊢
  all_goals
    first | rw [ht.1] | rw [ht.2] | rw [hf.1] | rw [hf.2]
  all_goals ring

-- @node: bernoulliCompletion_exchangeability
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the Bernoulli completion satisfies conditional exchangeability](goal). -/
lemma bernoulliCompletion_exchangeability {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    ConditionalExchangeability (bernoulliCompletion P) := by
  intro x r a ya
  fin_cases r <;> fin_cases a <;> fin_cases ya <;>
    simp [poArmAtom, bernoulliCompletion_poAtom_factorization P hP,
      completionBernoulliMass] <;> ring

-- @node: bernoulliCompletion_joint_independence
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [treatment is conditionally independent of the pair of potential outcomes given the covariate](goal). -/
lemma bernoulliCompletion_joint_independence {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    ∀ x a y0 y1,
      poAtom (bernoulliCompletion P) x a y0 y1 *
          (∑ a' : Bool, ∑ u0 : Bool, ∑ u1 : Bool,
            poAtom (bernoulliCompletion P) x a' u0 u1) =
        (∑ a' : Bool, poAtom (bernoulliCompletion P) x a' y0 y1) *
          (∑ u0 : Bool, ∑ u1 : Bool,
            poAtom (bernoulliCompletion P) x a u0 u1) := by
  intro x a y0 y1
  fin_cases a <;> fin_cases y0 <;> fin_cases y1 <;>
    simp [bernoulliCompletion_poAtom_factorization P hP,
      completionBernoulliMass] <;> ring

-- @node: bernoulliCompletion_potential_independence
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the two potential outcomes are conditionally independent given the covariate](goal). -/
lemma bernoulliCompletion_potential_independence {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    ∀ x y0 y1,
      (∑ a : Bool, poAtom (bernoulliCompletion P) x a y0 y1) *
          (∑ a : Bool, ∑ u0 : Bool, ∑ u1 : Bool,
            poAtom (bernoulliCompletion P) x a u0 u1) =
        (∑ a : Bool, ∑ u1 : Bool,
          poAtom (bernoulliCompletion P) x a y0 u1) *
          (∑ a : Bool, ∑ u0 : Bool,
            poAtom (bernoulliCompletion P) x a u0 y1) := by
  intro x y0 y1
  fin_cases y0 <;> fin_cases y1 <;>
    simp [bernoulliCompletion_poAtom_factorization P hP,
      completionBernoulliMass] <;> ring

-- @node: bernoulliCompletion_observedMarginal
/-- [the observed marginal of the Bernoulli completion recovers the original observed law](goal). -/
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
    simp only [apply_ite, ENNReal.toReal_zero, bernoulliCompletion_pmf_toReal]
    simp [completionFullMass, completionBernoulliMass]
    ring_nf
    fin_cases a <;> fin_cases y <;> simp [jointMass]

/-- The particular completion used for observed-margin surjectivity: potential outcomes
are conditionally independent Bernoulli variables, treatment is independent of their
joint vector given `X`, and the observed outcome is selected by treatment. -/
def BernoulliCompletionConstruction {d : ℕ} (P : DiscreteLaw d) (Q : PotentialLaw d) : Prop :=
  observedMarginal Q = P ∧ Consistency Q ∧ ConditionalExchangeability Q ∧
  (∀ x a y0 y1,
    poAtom Q x a y0 y1 *
        (∑ a' : Bool, ∑ u0 : Bool, ∑ u1 : Bool, poAtom Q x a' u0 u1) =
      (∑ a' : Bool, poAtom Q x a' y0 y1) *
        (∑ u0 : Bool, ∑ u1 : Bool, poAtom Q x a u0 u1)) ∧
  (∀ x y0 y1,
    (∑ a : Bool, poAtom Q x a y0 y1) *
        (∑ a : Bool, ∑ u0 : Bool, ∑ u1 : Bool, poAtom Q x a u0 u1) =
      (∑ a : Bool, ∑ u1 : Bool, poAtom Q x a y0 u1) *
      (∑ a : Bool, ∑ u0 : Bool, poAtom Q x a u0 y1))

-- @node: bernoulliCompletion_construction
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the Bernoulli completion supplies a valid completion of the observed law](goal). -/
lemma bernoulliCompletion_construction {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    BernoulliCompletionConstruction P (bernoulliCompletion P) := by
  exact ⟨bernoulliCompletion_observedMarginal P,
    bernoulliCompletion_consistency P,
    bernoulliCompletion_exchangeability P hP,
    bernoulliCompletion_joint_independence P hP,
    bernoulliCompletion_potential_independence P hP⟩

-- @node: bernoulliCompletion_mem_class
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the Bernoulli completion belongs to the causal completion class](goal). -/
lemma bernoulliCompletion_mem_class {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    CausalCompletionClass epsilon (bernoulliCompletion P) := by
  refine ⟨hP.d_ge_two, hP.epsilon_pos, hP.epsilon_lt_half,
    bernoulliCompletion_consistency P, bernoulliCompletion_exchangeability P hP, ?_⟩
  simpa [bernoulliCompletion_observedMarginal P] using hP.overlap

-- @node: identification_and_extension_raw
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the observed law satisfies the stated model restrictions](hyp:hP), then [the Bernoulli construction extends every admissible observed law to a causal model with the identified optimal value](goal). -/
theorem identification_and_extension_raw {d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hP : ObservedModelClass epsilon P) :
    (∀ x, cellVector P x ∈ overlapCone epsilon) ∧
    observedOptimalValue P hP = ∑ x, globalCellValue epsilon (cellVector P x) ∧
    (∀ u : Cell → ℝ, (∀ j, 0 ≤ u j) →
      0 ≤ globalCellValue epsilon u ∧ globalCellValue epsilon u ≤ vectorMass u) ∧
    (∀ u v : Cell → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ v j) →
      |globalCellValue epsilon u - globalCellValue epsilon v| ≤
        (1 + epsilon⁻¹) * l1CellDistance u v) ∧
    (∃ Q : PotentialLaw d,
      CausalCompletionClass epsilon Q ∧ BernoulliCompletionConstruction P Q) ∧
    (∀ Q : PotentialLaw d, CausalCompletionClass epsilon Q →
      ObservedModelClass epsilon (observedMarginal Q)) := by
  refine ⟨fun x => cellVector_mem_overlapCone_optimal P hP x, ?_, ?_, ?_, ?_, ?_⟩
  · rw [observedOptimalValue, observedOptimalValueRaw]
    apply Finset.sum_congr rfl
    intro x _hx
    exact (globalCellValue_cellVector P hP x).symm
  · exact fun u hu => globalCellValue_bounds hepsilon.1 u hu
  · exact fun u v hu hv => globalCellValue_lipschitz hepsilon.1 u v hu hv
  · exact ⟨bernoulliCompletion P, bernoulliCompletion_mem_class P hP,
      bernoulliCompletion_construction P hP⟩
  · intro Q hQ
    exact hQ.observedModel

-- @node: prop:identification-and-extension
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the observed law satisfies the stated model restrictions](hyp:hP), then [the observed optimal-value functional is identified and every admissible observed law has a causal completion with the same oracle value](goal). -/
theorem identification_and_extension {d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hP : ObservedModelClass epsilon P) :
    (∀ x, cellVector P x ∈ overlapCone epsilon) ∧
    observedOptimalValue P hP = ∑ x,
      globalCellValueNonnegative epsilon
        ⟨cellVector P x, (cellVector_mem_overlapCone_optimal P hP x).1⟩ ∧
    (∀ u : NonnegativeCellVector,
      0 ≤ globalCellValueNonnegative epsilon u ∧
        globalCellValueNonnegative epsilon u ≤ vectorMass u.1) ∧
    (∀ u v : NonnegativeCellVector,
      |globalCellValueNonnegative epsilon u - globalCellValueNonnegative epsilon v| ≤
        (1 + epsilon⁻¹) * l1CellDistance u.1 v.1) ∧
    (∃ Q : PotentialLaw d,
      CausalCompletionClass epsilon Q ∧ BernoulliCompletionConstruction P Q) ∧
    (∀ Q : PotentialLaw d, CausalCompletionClass epsilon Q →
      ObservedModelClass epsilon (observedMarginal Q)) := by
  rcases identification_and_extension_raw P hd hepsilon hP with
    ⟨hcone, hvalue, hbounds, hlipschitz, hcompletion, hconverse⟩
  refine ⟨hcone, ?_, ?_, ?_, hcompletion, hconverse⟩
  · simpa [globalCellValueNonnegative] using hvalue
  · intro u
    simpa [globalCellValueNonnegative] using hbounds u.1 u.2
  · intro u v
    simpa [globalCellValueNonnegative] using hlipschitz u.1 v.1 u.2 v.2

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
