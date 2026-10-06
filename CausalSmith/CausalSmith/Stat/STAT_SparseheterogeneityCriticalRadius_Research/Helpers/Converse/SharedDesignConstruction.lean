module
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineRealLaw

/-! Finite-law construction used by the shared-design converse. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SharedDesignConstruction

abbrev BinLaw := CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.BinLaw
abbrev RealLaw := CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.RealLaw
abbrev BinObs := CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.BinObs

open CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
open CausalSmith.Stat.DiscreteAteMinimaxLoggap

-- @node: sharedDesignBinaryAtom
/-- The atom weights for a finite binary law with prescribed cell masses,
propensities, and armwise success probabilities. -/
noncomputable def sharedDesignBinaryAtom {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ) (z : BinObs d) : ℝ :=
  p z.1 * (if z.2.1 then pi z.1 else 1 - pi z.1) *
    (if z.2.2 then mu z.2.1 z.1 else 1 - mu z.2.1 z.1)

-- @node: sharedDesignBinaryAtom_nonneg
/-- Unit-interval parameters give nonnegative finite atom weights. -/
lemma sharedDesignBinaryAtom_nonneg {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1) (z : BinObs d) :
    0 ≤ sharedDesignBinaryAtom p pi mu z := by
  rcases hp z.1 with ⟨hp0, hp1⟩
  rcases hpi z.1 with ⟨hpi0, hpi1⟩
  rcases hmu z.2.1 z.1 with ⟨hmu0, hmu1⟩
  unfold sharedDesignBinaryAtom
  split_ifs <;> positivity

-- @node: sharedDesignBinaryAtom_sum
/-- If the cell masses sum to one, the finite atom weights sum to one. -/
lemma sharedDesignBinaryAtom_sum {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ) (hp_sum : ∑ k, p k = 1) :
    ∑ z : BinObs d, sharedDesignBinaryAtom p pi mu z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sharedDesignBinaryAtom,
    Bool.false_eq_true, if_false, if_true]
  rw [show (∑ k, (p k * pi k * mu true k + p k * pi k * (1 - mu true k) +
      (p k * (1 - pi k) * mu false k +
        p k * (1 - pi k) * (1 - mu false k)))) = ∑ k, p k by
    apply Finset.sum_congr rfl
    intro k _
    ring]
  exact hp_sum

-- @node: sharedDesignBinaryLaw
/-- The finite binary law with the prescribed cell, treatment, and outcome
parameters. -/
noncomputable def sharedDesignBinaryLaw {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) : BinLaw d where
  pmf := PMF.ofFintype
    (fun z => ENNReal.ofReal (sharedDesignBinaryAtom p pi mu z)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => sharedDesignBinaryAtom_nonneg p pi mu hp hpi hmu z),
        sharedDesignBinaryAtom_sum p pi mu hp_sum]
      simp

-- @node: sharedDesignBinaryLaw_jointMass
/-- The constructed binary law has the declared atom weights. -/
lemma sharedDesignBinaryLaw_jointMass {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (k : Fin d) (a y : Bool) :
    jointMass (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum) k a y =
      sharedDesignBinaryAtom p pi mu (k, a, y) := by
  unfold jointMass sharedDesignBinaryLaw
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact sharedDesignBinaryAtom_nonneg p pi mu hp hpi hmu (k, a, y)

-- @node: sharedDesignBinaryLaw_cellMass
/-- The constructed binary law has the declared cell masses. -/
lemma sharedDesignBinaryLaw_cellMass {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (k : Fin d) :
    cellMass (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum) k = p k := by
  unfold cellMass
  simp only [Fintype.sum_bool,
    sharedDesignBinaryLaw_jointMass p pi mu hp hpi hmu hp_sum,
    sharedDesignBinaryAtom, Bool.false_eq_true, if_false, if_true]
  ring

-- @node: sharedDesignBinaryLaw_propensity
/-- On a positive-mass cell, the constructed binary law has the declared
propensity. -/
lemma sharedDesignBinaryLaw_propensity {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (k : Fin d) (hk : 0 < p k) :
    propensity (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum) k = pi k := by
  unfold propensity armMass
  rw [sharedDesignBinaryLaw_cellMass p pi mu hp hpi hmu hp_sum]
  simp only [Fintype.sum_bool,
    sharedDesignBinaryLaw_jointMass p pi mu hp hpi hmu hp_sum,
    sharedDesignBinaryAtom, if_true, Bool.false_eq_true, if_false]
  field_simp [ne_of_gt hk]
  ring

-- @node: sharedDesignBinaryLaw_outcomeMean
/-- On a positive-mass cell with an interior propensity, each arm of the
constructed binary law has its declared success probability. -/
lemma sharedDesignBinaryLaw_outcomeMean {d : ℕ} (p pi : Fin d → ℝ)
    (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (a : Bool) (k : Fin d) (hk : 0 < p k)
    (hpi0 : 0 < pi k) (hpi1 : pi k < 1) :
    outcomeMean (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum) a k = mu a k := by
  unfold outcomeMean armMass
  simp only [Fintype.sum_bool,
    sharedDesignBinaryLaw_jointMass p pi mu hp hpi hmu hp_sum,
    sharedDesignBinaryAtom, Bool.false_eq_true, if_false, if_true]
  cases a
  · field_simp [ne_of_gt hk, ne_of_gt (sub_pos.mpr hpi1)]
    ring
  · field_simp [ne_of_gt hk, ne_of_gt hpi0]
    ring

-- @node: prescribedOutcomeLaw
/-- The affine two-point outcome law with a prescribed binary success
probability. -/
noncomputable def prescribedOutcomeLaw (M q : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - q) • Measure.dirac (-(M / 2)) +
    ENNReal.ofReal q • Measure.dirac (M / 2)

-- @node: prescribedOutcomeLaw_probability
/-- A unit-interval success probability gives a probability outcome law. -/
lemma prescribedOutcomeLaw_probability {M q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (prescribedOutcomeLaw M q) := by
  rw [isProbabilityMeasure_iff, prescribedOutcomeLaw, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  simp only [measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hq.2) hq.1]
  norm_num

-- @node: prescribedOutcomeLaw_mean
/-- The mean of the prescribed affine two-point law is `M * (q - 1/2)`. -/
lemma prescribedOutcomeLaw_mean {M q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫ y, y ∂prescribedOutcomeLaw M q = M * (q - 1 / 2) := by
  rw [prescribedOutcomeLaw, integral_add_measure, integral_smul_measure,
    integral_smul_measure]
  · simp [ENNReal.toReal_ofReal hq.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2)]
    ring
  · exact Integrable.smul_measure
      (integrable_dirac (f := fun y : ℝ => y) (a := -(M / 2))
        (by simp [enorm]; exact ENNReal.div_lt_top ENNReal.coe_ne_top (by norm_num)))
      (by simp)
  · exact Integrable.smul_measure
      (integrable_dirac (f := fun y : ℝ => y) (a := M / 2)
        (by simp [enorm]; exact ENNReal.div_lt_top ENNReal.coe_ne_top (by norm_num)))
      (by simp)

-- @node: prescribedFiniteRealLaw
/-- A real-outcome law with prescribed finite design and conditional means,
including the declarations on zero-mass cells. -/
noncomputable def prescribedFiniteRealLaw {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) : RealLaw d := by
  let Q := sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum
  let R := affineBinaryRealLaw M Q
  exact
    { R with
      propensity := pi
      outcomeLaw := fun a k => prescribedOutcomeLaw M (mu a k)
      outcomeMean := fun a k => M * (mu a k - 1 / 2)
      propensity_range := hpi
      outcome_isProbability := fun a k => prescribedOutcomeLaw_probability (hmu a k)
      arm_outcome_factorization := by
        intro a k s hs
        change (cellMass Q k * (if a then pi k else 1 - pi k)) *
            realMass (prescribedOutcomeLaw M (mu a k)) s =
          realMass ((Q.pmf.map (affineObserved M)).toMeasure)
            {o | o.x = k ∧ o.a = a ∧ o.y ∈ s}
        rw [sharedDesignBinaryLaw_cellMass p pi mu hp hpi hmu hp_sum]
        rw [realMass_affineObserved_event M Q k a s hs]
        rw [prescribedOutcomeLaw, realMass, Measure.add_apply,
          Measure.smul_apply, Measure.smul_apply]
        simp only [Fintype.sum_bool, Q,
          sharedDesignBinaryLaw_jointMass p pi mu hp hpi hmu hp_sum,
          sharedDesignBinaryAtom, Set.indicator]
        simp at ⊢
        have hpos_iff : M * (1 - (1 : ℝ) / 2) ∈ s ↔ M / 2 ∈ s := by
          constructor <;> intro h <;> convert h using 1 <;> ring
        have hneg_iff : M * (0 - (1 : ℝ) / 2) ∈ s ↔ -(M / 2) ∈ s := by
          constructor <;> intro h <;> convert h using 1 <;> ring
        by_cases hnsource : M * (0 - (1 : ℝ) / 2) ∈ s
        · have hneg := hneg_iff.mp hnsource
          by_cases hpsource : M * (1 - (1 : ℝ) / 2) ∈ s
          · have hpos := hpos_iff.mp hpsource
            cases a <;> simp [hneg, hpos, hnsource, hpsource,
              ENNReal.toReal_add, ENNReal.toReal_ofReal, (hmu false k).1,
              (hmu false k).2, (hmu true k).1, (hmu true k).2] <;>
              split_ifs <;> simp_all <;> ring
          · have hpos : M / 2 ∉ s := fun h => hpsource (hpos_iff.mpr h)
            cases a <;> simp [hneg, hpos, hnsource, hpsource,
              ENNReal.toReal_add, ENNReal.toReal_ofReal, (hmu false k).1,
              (hmu false k).2, (hmu true k).1, (hmu true k).2] <;>
              split_ifs <;> simp_all <;> ring
        · have hneg : -(M / 2) ∉ s := fun h => hnsource (hneg_iff.mpr h)
          by_cases hpsource : M * (1 - (1 : ℝ) / 2) ∈ s
          · have hpos := hpos_iff.mp hpsource
            cases a <;> simp [hneg, hpos, hnsource, hpsource,
              ENNReal.toReal_add, ENNReal.toReal_ofReal, (hmu false k).1,
              (hmu false k).2, (hmu true k).1, (hmu true k).2] <;>
              split_ifs <;> simp_all <;> ring
          · have hpos : M / 2 ∉ s := fun h => hpsource (hpos_iff.mpr h)
            cases a <;> simp [hneg, hpos, hnsource, hpsource,
              ENNReal.toReal_add, ENNReal.toReal_ofReal, (hmu false k).1,
              (hmu false k).2, (hmu true k).1, (hmu true k).2] <;>
              split_ifs <;> simp_all <;> ring
      outcomeMean_eq := fun a k => (prescribedOutcomeLaw_mean (hmu a k)).symm }

-- @node: prescribedFiniteRealLaw_cellMass
/-- The prescribed finite real law retains every declared cell mass. -/
lemma prescribedFiniteRealLaw_cellMass {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (k : Fin d) :
    (prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum).cellMass k = p k := by
  simp only [prescribedFiniteRealLaw]
  change cellMass (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum) k = p k
  exact sharedDesignBinaryLaw_cellMass p pi mu hp hpi hmu hp_sum k

-- @node: prescribedFiniteRealLaw_support
/-- Both conditional outcome laws of the prescribed finite law are supported on
the two affine endpoints. -/
lemma prescribedFiniteRealLaw_support {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) (a : Bool) (k : Fin d) :
    (prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum).outcomeLaw a k
      (({-(M / 2), M / 2} : Set ℝ)ᶜ) = 0 := by
  simp only [prescribedFiniteRealLaw]
  change prescribedOutcomeLaw M (mu a k) (({-(M / 2), M / 2} : Set ℝ)ᶜ) = 0
  rw [prescribedOutcomeLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

-- @node: prescribedFiniteRealLaw_fullSupport
/-- The full-data law of the prescribed construction has both potential outcomes
at the two affine endpoints. -/
lemma prescribedFiniteRealLaw_fullSupport {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) :
    (prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum).fullLaw
      {z | z.y0 ∉ ({-(M / 2), M / 2} : Set ℝ) ∨
        z.y1 ∉ ({-(M / 2), M / 2} : Set ℝ)} = 0 := by
  let Q := sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum
  simp only [prescribedFiniteRealLaw]
  change ((PMF.map (BinaryFullObs.affine M (fun k => k))
    (binaryIndependentFullPMF Q)).toMeasure) _ = 0
  rw [← PMF.toMeasure_map _ _ (by fun_prop)]
  have hset : MeasurableSet
      {z : CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.FullObs d |
        z.y0 ∉ ({-(M / 2), M / 2} : Set ℝ) ∨
        z.y1 ∉ ({-(M / 2), M / 2} : Set ℝ)} := by
    exact (((measurableSet_singleton (-(M / 2))).union
      (measurableSet_singleton (M / 2))).compl.preimage measurable_full_y0).union
      (((measurableSet_singleton (-(M / 2))).union
        (measurableSet_singleton (M / 2))).compl.preimage measurable_full_y1)
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) hset]
  have hempty : (BinaryFullObs.affine M (fun k => k)) ⁻¹'
      {z : CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.FullObs d |
        z.y0 ∉ ({-(M / 2), M / 2} : Set ℝ) ∨
        z.y1 ∉ ({-(M / 2), M / 2} : Set ℝ)} = ∅ := by
    ext z
    constructor
    · intro hz
      have hscale (b : Bool) :
          M * ((if b then 1 else 0) - 1 / 2) ∈
            ({-(M / 2), M / 2} : Set ℝ) := by
        cases b
        · left
          simp
          ring
        · right
          simp
          ring
      rcases z with ⟨x, a, b0, b1⟩
      change (M * ((if b0 then 1 else 0) - 1 / 2) ∉
          ({-(M / 2), M / 2} : Set ℝ) ∨
        M * ((if b1 then 1 else 0) - 1 / 2) ∉
          ({-(M / 2), M / 2} : Set ℝ)) at hz
      exact hz.elim (fun h => h (hscale b0)) (fun h => h (hscale b1))
    · intro hz
      simp at hz
  rw [hempty]
  simp

-- @node: prescribedFiniteRealLaw_consistency
/-- The prescribed finite real law is consistent. -/
lemma prescribedFiniteRealLaw_consistency {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) :
    DiscreteAteHeterogeneityFrontier.Consistency
      (prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum) := by
  simp only [prescribedFiniteRealLaw]
  exact affineBinaryRealLaw_consistency M
    (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum)

-- @node: prescribedFiniteRealLaw_exchangeability
/-- The prescribed finite real law is conditionally exchangeable. -/
lemma prescribedFiniteRealLaw_exchangeability {d : ℕ} (M : ℝ)
    (p pi : Fin d → ℝ) (mu : Bool → Fin d → ℝ)
    (hp : ∀ k, p k ∈ Icc (0 : ℝ) 1)
    (hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1)
    (hpi0 : ∀ k, 0 < pi k) (hpi1 : ∀ k, pi k < 1)
    (hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1)
    (hp_sum : ∑ k, p k = 1) :
    DiscreteAteHeterogeneityFrontier.ConditionalExchangeability
      (prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum) := by
  simp only [prescribedFiniteRealLaw]
  exact affineBinaryRealLaw_exchangeability M
    (sharedDesignBinaryLaw p pi mu hp hpi hmu hp_sum)

end SharedDesignConstruction

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
