module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightWeightBound

/-! Exact heavy-cell population weight and its exponential bias bound. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- Equation (19), exposed as a reusable exact population-weight identity. -/
lemma heavyAuditWeight_eq {n : ℕ} (P : Law n) (k : Fin n) :
    heavyAuditWeight n P k =
      P.cellMass k *
        (1 - P.propensity k *
            Real.exp (-blockMean n * armMass P false k) -
          (1 - P.propensity k) *
            Real.exp (-blockMean n * armMass P true k)) := by
  rfl

/-- Exact heavy-weight bias decomposition. -/
lemma cellMass_sub_heavyAuditWeight {n : ℕ} (P : Law n) (k : Fin n) :
    P.cellMass k - heavyAuditWeight n P k =
      P.cellMass k *
        (P.propensity k * Real.exp (-blockMean n * armMass P false k) +
          (1 - P.propensity k) *
            Real.exp (-blockMean n * armMass P true k)) := by
  rw [heavyAuditWeight_eq]
  ring

/-- Equation (24), including zero-mass cells. -/
lemma heavyAuditWeight_bias_bound {n : ℕ} (P : Law n) (k : Fin n)
    (hn : 0 < n) (hoverlap : FixedOverlap P) :
    0 ≤ P.cellMass k - heavyAuditWeight n P k ∧
      P.cellMass k - heavyAuditWeight n P k ≤
        P.cellMass k * Real.exp (-blockMean n * P.cellMass k / 4) := by
  have hp0 : 0 ≤ P.cellMass k := (P.cellMass_range k).1
  have hpi0 : 0 ≤ P.propensity k := (P.propensity_range k).1
  have hpi1 : P.propensity k ≤ 1 := (P.propensity_range k).2
  rw [cellMass_sub_heavyAuditWeight]
  constructor
  · positivity
  · by_cases hp : P.cellMass k = 0
    · simp [hp]
    · have hp' : 0 < P.cellMass k := lt_of_le_of_ne hp0 (Ne.symm hp)
      obtain ⟨hquarter, hthreequarter⟩ := hoverlap k hp'
      have hm : 0 < blockMean n := by
        simp only [blockMean, postPilotSize, pilotSize]
        have : 0 < n - n / 2 := by omega
        positivity
      have hs0 : P.cellMass k / 4 ≤ armMass P false k := by
        simp only [armMass, Bool.false_eq_true, ↓reduceIte]
        nlinarith
      have hs1 : P.cellMass k / 4 ≤ armMass P true k := by
        simp only [armMass, ↓reduceIte]
        nlinarith
      have he0 : Real.exp (-blockMean n * armMass P false k) ≤
          Real.exp (-blockMean n * P.cellMass k / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have he1 : Real.exp (-blockMean n * armMass P true k) ≤
          Real.exp (-blockMean n * P.cellMass k / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hmix :
          P.propensity k * Real.exp (-blockMean n * armMass P false k) +
              (1 - P.propensity k) *
                Real.exp (-blockMean n * armMass P true k) ≤
            Real.exp (-blockMean n * P.cellMass k / 4) := by
        calc
          _ ≤ P.propensity k * Real.exp (-blockMean n * P.cellMass k / 4) +
              (1 - P.propensity k) *
                Real.exp (-blockMean n * P.cellMass k / 4) := by gcongr
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_left hmix hp0

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
