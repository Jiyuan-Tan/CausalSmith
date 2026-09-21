module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic

/-! Explicit finite control-zero laws used by the common-marginal prior. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open scoped ENNReal BigOperators
/-- [the stated conditions](hyp:hq,hfinite) establishes [the stated conclusion](goal). -/

lemma measurable_comp_of_finite_range {alpha beta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    [MeasurableSingletonClass beta] {q : alpha → beta}
    (hq : Measurable q) (hfinite : (Set.range q).Finite) (f : beta → gamma) :
    Measurable (f ∘ q) := by
  intro s _
  let t := f ⁻¹' s ∩ Set.range q
  have ht : t.Finite := hfinite.subset (Set.inter_subset_right)
  have htmeas : MeasurableSet t := ht.measurableSet
  have hpre := hq htmeas
  convert hpre using 1
  ext x
  simp [t]
/-- [the stated conditions](hyp:hd) defines [the specified object](goal). -/

def commonMarginalReservoir {d : Nat} (hd : 1 ≤ d) : Fin d := ⟨0, hd⟩
/-- [the stated conditions](hyp:hkd,i) defines [the specified object](goal). -/

def commonMarginalRareCell {k d : Nat} (hkd : k + 1 ≤ d) (i : Fin k) : Fin d :=
  ⟨i.val + 1, lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) hkd⟩
/-- [the stated conditions](hyp:hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalRareCell_injective {k d : Nat} (hkd : k + 1 ≤ d) :
    Function.Injective (commonMarginalRareCell hkd) := by
  intro i j hij
  apply Fin.ext
  simpa [commonMarginalRareCell] using congrArg Fin.val hij
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalReservoir_ne_rareCell {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (i : Fin k) :
    commonMarginalReservoir hd ≠ commonMarginalRareCell hkd i := by
  intro h
  have := congrArg Fin.val h
  simp [commonMarginalReservoir, commonMarginalRareCell] at this
/-- [the stated conditions](hyp:hd,hkd,reservoirMass,w,x) defines [the specified object](goal). -/

noncomputable def commonMarginalRawMass {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (w : Fin k → Real) (x : Fin d) : Real :=
  (if x = commonMarginalReservoir hd then reservoirMass else 0) +
    ∑ i, if x = commonMarginalRareCell hkd i then w i else 0
/-- [the stated conditions](hyp:hd,hkd,eps,a,w,x) defines [the specified object](goal). -/

noncomputable def commonMarginalPropensity {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (eps a : Real) (w : Fin k → Real) (x : Fin d) : Real :=
  if x = commonMarginalReservoir hd then 1 / 2
  else
    let p := commonMarginalRawMass hd hkd 0 w x
    if p = 0 then 1 / 2 else eps * (p + a) / p
/-- [the stated conditions](hyp:hd,hkd,sign,branch,w,x) defines [the specified object](goal). -/

noncomputable def commonMarginalOutcomeMean {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (sign : Real → Real) (branch : Bool)
    (w : Fin k → Real) (x : Fin d) : Real :=
  ∑ i, if x = commonMarginalRareCell hkd i ∧ w i ≠ 0 then
    (1 + (if branch then sign (w i) else -sign (w i))) / 2 else 0
/-- [the stated conditions](hyp:s,p) defines [the specified object](goal). -/

noncomputable def commonMarginalClampSign (s : Real → Real) (p : Real) : Real :=
  max (-1) (min 1 (s p))
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma commonMarginalClampSign_mem (s : Real → Real) (p : Real) :
    commonMarginalClampSign s p ∈ Set.Icc (-1 : Real) 1 := by
  constructor <;> simp [commonMarginalClampSign]
/-- [the stated conditions](hyp:hp) establishes [the stated conclusion](goal). -/

lemma commonMarginalClampSign_eq {s : Real → Real} {p : Real}
    (hp : s p ∈ Set.Icc (-1 : Real) 1) :
    commonMarginalClampSign s p = s p := by
  simp [commonMarginalClampSign, hp.1, hp.2]
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_reservoir {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (w : Fin k → Real) :
    commonMarginalRawMass hd hkd reservoirMass w (commonMarginalReservoir hd) =
      reservoirMass := by
  simp [commonMarginalRawMass, commonMarginalReservoir_ne_rareCell]
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_rare {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (w : Fin k → Real) (i : Fin k) :
    commonMarginalRawMass hd hkd reservoirMass w (commonMarginalRareCell hkd i) = w i := by
  rw [commonMarginalRawMass]
  simp only [if_neg (commonMarginalReservoir_ne_rareCell hd hkd i).symm, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [(commonMarginalRareCell_injective hkd).ne hji |>.symm]
  · simp
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalPropensity_reservoir {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (eps a : Real) (w : Fin k → Real) :
    commonMarginalPropensity hd hkd eps a w (commonMarginalReservoir hd) = 1 / 2 := by
  simp [commonMarginalPropensity]
/-- [the stated conditions](hyp:hd,hkd,hi) establishes [the stated conclusion](goal). -/

lemma commonMarginalPropensity_rare {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (eps a : Real) (w : Fin k → Real) (i : Fin k)
    (hi : w i ≠ 0) :
    commonMarginalPropensity hd hkd eps a w (commonMarginalRareCell hkd i) =
      eps * (w i + a) / w i := by
  rw [commonMarginalPropensity]
  simp only [if_neg (commonMarginalReservoir_ne_rareCell hd hkd i).symm]
  rw [commonMarginalRawMass_rare hd hkd 0 w i, if_neg hi]
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalOutcomeMean_reservoir {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (sign : Real → Real) (branch : Bool) (w : Fin k → Real) :
    commonMarginalOutcomeMean hd hkd sign branch w (commonMarginalReservoir hd) = 0 := by
  simp [commonMarginalOutcomeMean, commonMarginalReservoir_ne_rareCell]
/-- [the stated conditions](hyp:hd,hkd,hi) establishes [the stated conclusion](goal). -/

lemma commonMarginalOutcomeMean_rare {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (sign : Real → Real) (branch : Bool)
    (w : Fin k → Real) (i : Fin k) (hi : w i ≠ 0) :
    commonMarginalOutcomeMean hd hkd sign branch w (commonMarginalRareCell hkd i) =
      (1 + (if branch then sign (w i) else -sign (w i))) / 2 := by
  rw [commonMarginalOutcomeMean, Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hne := (commonMarginalRareCell_injective hkd).ne hji
    simp [hne.symm]
  · simp
/-- [the stated conditions](hyp:hd,hkd,hsign) establishes [the stated conclusion](goal). -/

lemma commonMarginalOutcomeMean_mem {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (sign : Real → Real)
    (hsign : ∀ p, sign p ∈ Set.Icc (-1 : Real) 1) (branch : Bool)
    (w : Fin k → Real) (x : Fin d) :
    commonMarginalOutcomeMean hd hkd sign branch w x ∈ Set.Icc (0 : Real) 1 := by
  by_cases hx : ∃ i, x = commonMarginalRareCell hkd i ∧ w i ≠ 0
  · obtain ⟨i, hxi, hi⟩ := hx
    rw [hxi, commonMarginalOutcomeMean_rare hd hkd sign branch w i hi]
    cases branch <;> simp only [Bool.false_eq_true, if_false, if_true]
    · constructor <;> linarith [(hsign (w i)).1, (hsign (w i)).2]
    · constructor <;> linarith [(hsign (w i)).1, (hsign (w i)).2]
  · simp only [commonMarginalOutcomeMean]
    have hzero : (∑ i, if x = commonMarginalRareCell hkd i ∧ w i ≠ 0 then
        (1 + (if branch then sign (w i) else -sign (w i))) / 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (fun hi => hx ⟨i, hi⟩)]
    rw [hzero]
    exact ⟨le_rfl, zero_le_one⟩
/-- [the stated conditions](hyp:hd,hkd,hx,hxi) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_unused {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (w : Fin k → Real) (x : Fin d)
    (hx : x ≠ commonMarginalReservoir hd)
    (hxi : ∀ i, x ≠ commonMarginalRareCell hkd i) :
    commonMarginalRawMass hd hkd reservoirMass w x = 0 := by
  simp [commonMarginalRawMass, hx, hxi]
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_sum {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (w : Fin k → Real) :
    ∑ x, commonMarginalRawMass hd hkd reservoirMass w x =
      reservoirMass + ∑ i, w i := by
  simp_rw [commonMarginalRawMass]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply congrArg (fun z => reservoirMass + z)
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq']
  simp
/-- [the stated conditions](hyp:hd,hkd,hr,hw) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_nonneg {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) {reservoirMass : Real} {w : Fin k → Real}
    (hr : 0 ≤ reservoirMass) (hw : ∀ i, 0 ≤ w i) (x : Fin d) :
    0 ≤ commonMarginalRawMass hd hkd reservoirMass w x := by
  unfold commonMarginalRawMass
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hw i
    · exact le_rfl
/-- [the stated conditions](hyp:hd,hkd) establishes [the stated conclusion](goal). -/

lemma commonMarginalRawMass_mul_outcome_sum {k d : Nat} (hd : 1 ≤ d)
    (hkd : k + 1 ≤ d) (reservoirMass : Real) (sign : Real → Real)
    (branch : Bool) (w : Fin k → Real) :
    ∑ x, commonMarginalRawMass hd hkd reservoirMass w x *
        commonMarginalOutcomeMean hd hkd sign branch w x =
      ∑ i, w i * (1 + (if branch then sign (w i) else -sign (w i))) / 2 := by
  simp_rw [commonMarginalOutcomeMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : w i = 0
  · simp [hi]
  · rw [Finset.sum_eq_single (commonMarginalRareCell hkd i)]
    · rw [if_pos ⟨rfl, hi⟩, commonMarginalRawMass_rare]
      ring
    · intro x _ hxi
      simp [hxi]
    · simp
/-- [the stated conditions](hyp:p,e,mu,z) defines [the specified object](goal). -/

noncomputable def finiteControlZeroAtom {d : Nat}
    (p e mu : Fin d → Real) (z : Obs d) : Real :=
  if z.2.1 then
    if z.2.2 then p z.1 * e z.1 * mu z.1
    else p z.1 * e z.1 * (1 - mu z.1)
  else if z.2.2 then 0 else p z.1 * (1 - e z.1)
/-- [the stated conditions](hyp:hp,he,hmu) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroAtom_nonneg {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1) (z : Obs d) :
    0 ≤ finiteControlZeroAtom p e mu z := by
  unfold finiteControlZeroAtom
  split_ifs <;> try positivity
  · exact mul_nonneg (mul_nonneg (hp _).1 (he _).1) (hmu _).1
  · exact mul_nonneg (mul_nonneg (hp _).1 (he _).1) (sub_nonneg.mpr (hmu _).2)
  · exact mul_nonneg (hp _).1 (sub_nonneg.mpr (he _).2)
/-- [the stated conditions](hyp:hp) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroAtom_sum {d : Nat}
    (p e mu : Fin d → Real) (hp : ∑ x, p x = 1) :
    ∑ z : Obs d, finiteControlZeroAtom p e mu z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, finiteControlZeroAtom,
    Bool.false_eq_true, if_false, if_true]
  calc
    ∑ x, (p x * e x * mu x + p x * e x * (1 - mu x) +
        (0 + p x * (1 - e x))) = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 1 := hp
/-- [the stated conditions](hyp:p,e,mu,hp,he,hmu,hsum) defines [the specified object](goal). -/

noncomputable def finiteControlZeroLaw {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) : DiscreteLaw d where
  pmf := PMF.ofFintype
    (fun z => ENNReal.ofReal (finiteControlZeroAtom p e mu z)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => finiteControlZeroAtom_nonneg p e mu hp he hmu z),
        finiteControlZeroAtom_sum p e mu hsum]
      simp
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_jointMass {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) (arm y : Bool) :
    jointMass (finiteControlZeroLaw p e mu hp he hmu hsum) x arm y =
      finiteControlZeroAtom p e mu (x, arm, y) := by
  unfold jointMass finiteControlZeroLaw
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact finiteControlZeroAtom_nonneg p e mu hp he hmu (x, arm, y)
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_cellMass {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) :
    cellMass (finiteControlZeroLaw p e mu hp he hmu hsum) x = p x := by
  unfold cellMass
  simp only [Fintype.sum_bool,
    finiteControlZeroLaw_jointMass p e mu hp he hmu hsum,
    finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
  ring
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_armMass {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) :
    armMass (finiteControlZeroLaw p e mu hp he hmu hsum) x true = p x * e x := by
  unfold armMass
  simp only [Fintype.sum_bool,
    finiteControlZeroLaw_jointMass p e mu hp he hmu hsum,
    finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
  ring
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_armMass_false {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) :
    armMass (finiteControlZeroLaw p e mu hp he hmu hsum) x false =
      p x * (1 - e x) := by
  unfold armMass
  simp only [Fintype.sum_bool,
    finiteControlZeroLaw_jointMass p e mu hp he hmu hsum,
    finiteControlZeroAtom, Bool.false_eq_true, if_false, if_true]
  ring
/-- [the stated conditions](hyp:hp,he,hmu,hsum,hx) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_propensity {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) (hx : 0 < p x) :
    propensity (finiteControlZeroLaw p e mu hp he hmu hsum) x = e x := by
  rw [propensity, finiteControlZeroLaw_cellMass p e mu hp he hmu hsum,
    finiteControlZeroLaw_armMass p e mu hp he hmu hsum]
  field_simp [ne_of_gt hx]
/-- [the stated conditions](hyp:hp,he,hmu,hsum,hx) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_outcomeMean_true {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) (hx : 0 < p x * e x) :
    outcomeMean (finiteControlZeroLaw p e mu hp he hmu hsum) true x = mu x := by
  rw [outcomeMean, finiteControlZeroLaw_armMass p e mu hp he hmu hsum,
    finiteControlZeroLaw_jointMass]
  simp only [finiteControlZeroAtom, if_true]
  exact mul_div_cancel_left₀ (mu x) (ne_of_gt hx)
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_outcomeMean_false {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (x : Fin d) :
    outcomeMean (finiteControlZeroLaw p e mu hp he hmu hsum) false x = 0 := by
  rw [outcomeMean, finiteControlZeroLaw_jointMass]
  simp [finiteControlZeroAtom]
/-- [the stated conditions](hyp:hp,he,hmu,hsum) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_auxTable {d : Nat}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) :
    auxTableOf (finiteControlZeroLaw p e mu hp he hmu hsum) = fun z =>
      if z.2 then p z.1 * e z.1 else p z.1 * (1 - e z.1) := by
  funext z
  cases z with
  | mk x arm =>
    cases arm
    · unfold auxTableOf armMass
      simp [finiteControlZeroLaw_jointMass, finiteControlZeroAtom]
    · simp [auxTableOf, finiteControlZeroLaw_armMass]
/-- [the stated conditions](hyp:hp,he,hmu,hsum,hd,heps,hepsHalf,hoverlap) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_model {d : Nat} {eps : Real}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (hd : 2 ≤ d) (heps : 0 < eps)
    (hepsHalf : eps < 1 / 2)
    (hoverlap : ∀ x, 0 < p x → eps ≤ e x ∧ e x ≤ 1 - eps) :
    ModelClass d eps (finiteControlZeroLaw p e mu hp he hmu hsum) := by
  refine ⟨hd, heps, hepsHalf, ?_⟩
  intro x hx
  rw [finiteControlZeroLaw_cellMass p e mu hp he hmu hsum] at hx
  rw [finiteControlZeroLaw_propensity p e mu hp he hmu hsum x hx]
  exact hoverlap x hx
/-- [the stated conditions](hyp:hp,he,hmu,hsum,heps,hoverlap) establishes [the stated conclusion](goal). -/

lemma finiteControlZeroLaw_ate {d : Nat} {eps : Real}
    (p e mu : Fin d → Real)
    (hp : ∀ x, p x ∈ Set.Icc (0 : Real) 1)
    (he : ∀ x, e x ∈ Set.Icc (0 : Real) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : Real) 1)
    (hsum : ∑ x, p x = 1) (heps : 0 < eps)
    (hoverlap : ∀ x, 0 < p x → eps ≤ e x) :
    ateFunctional (finiteControlZeroLaw p e mu hp he hmu hsum) = ∑ x, p x * mu x := by
  unfold ateFunctional
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteControlZeroLaw_cellMass p e mu hp he hmu hsum,
    finiteControlZeroLaw_outcomeMean_false p e mu hp he hmu hsum]
  by_cases hx : p x = 0
  · simp [hx]
  · have hpx : 0 < p x := lt_of_le_of_ne (hp x).1 (Ne.symm hx)
    have hex : 0 < e x := heps.trans_le (hoverlap x hpx)
    rw [finiteControlZeroLaw_outcomeMean_true p e mu hp he hmu hsum x
      (mul_pos hpx hex)]
    ring

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
