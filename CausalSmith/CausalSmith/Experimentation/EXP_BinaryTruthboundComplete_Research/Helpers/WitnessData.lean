import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BooleanMobius
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-! Exact rational data for the six-coordinate, three-assignment witness. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Observation sets of the three witness assignments. -/
def witnessO (z : Fin 3) : Finset (Fin 6) :=
  match z.1 with
  | 0 => {1, 3, 5}
  | 1 => {3, 4}
  | _ => {0, 1, 2, 5}

/-- Score vectors of the three witness assignments. -/
def witnessV (z : Fin 3) (i : Fin 6) : ℝ :=
  match z.1, i.1 with
  | 0, 1 => -2 | 0, 3 => -1 | 0, 5 => 3
  | 1, 3 => 1 | 1, 4 => -1
  | 2, 0 => -2 | 2, 1 => -1 | 2, 2 => 2 | 2, 5 => 1
  | _, _ => 0

/-- The concrete six-coordinate, three-atom finite experiment. -/
-- @env: S4
noncomputable def witnessExperiment : Setup where
  K := 6
  Omega := Fin 3
  fintypeOmega := inferInstance
  design := {
    p := fun _ => (1 : ℝ) / 3
    p_nonneg := by
      intro z
      norm_num
    p_sum := by
      norm_num [Fin.sum_univ_succ] }
  support_pos := by
    intro z
    norm_num
  O := witnessO
  v := witnessV
  -- @realizes \mathfrak E_\star(K=6, three atoms, displayed O_z and v_z)

/-- Witness centered schedule. -/
noncomputable def witnessK_eq : witnessExperiment.K = 6 := rfl

/-- Coerce a concrete six-coordinate index into the witness setup's coordinate type. -/
noncomputable def wcoord (i : Fin 6) : Fin witnessExperiment.K := Fin.cast witnessK_eq.symm i

/-- For [a binary schedule in the witness experiment](hyp:θ), [the centered six-coordinate witness vector](goal) records each bit after mapping it to minus one or one. -/
noncomputable def witnessX (θ : Theta witnessExperiment) : Fin 6 → ℝ := fun i => centeredCoord θ (wcoord i)
  -- @realizes x(centered schedule in {-1,1}^6)

/-- The nine-term centered quadratic appearing in every witness certificate. -/
def witnessP (x : Fin 6 → ℝ) : ℝ :=
  3*x 0*x 1 - 35*x 0*x 2 + 3*x 0*x 5 - 3*x 1*x 2 + 24*x 1*x 3 -
  45*x 1*x 5 - 3*x 2*x 5 - 12*x 3*x 4 - 36*x 3*x 5
  -- @realizes P(displayed centered quadratic polynomial)

/-- The unrestricted quartic primal certificate. -/
noncomputable def bStar (θ : Theta witnessExperiment) : ℝ :=
  (107 + witnessP (witnessX θ) -
    3 * witnessX θ 0 * witnessX θ 1 * witnessX θ 2 * witnessX θ 5) / 72
  -- @realizes b^\star((107+P-3*x0*x1*x2*x5)/72)

/-- The degree-two primal certificate. -/
-- @node: p3
noncomputable def rStar (θ : Theta witnessExperiment) : ℝ :=
  (110 + witnessP (witnessX θ)) / 72
  -- @realizes r^\star((110+P)/72)

/-- Read an observed bit, returning zero only outside the observation set. -/
def localBit (E : Setup) (z : E.Omega) (y : E.O z → Fin 2) (i : Fin E.K) : ℕ :=
  if h : i ∈ E.O z then (y ⟨i, h⟩ : ℕ) else 0

/-- Lexicographic index of a witness assignment-local binary schedule. -/
noncomputable def witnessLocalIndex (z : Fin 3) (y : witnessExperiment.O z → Fin 2) : ℕ :=
  match z.1 with
  | 0 => 4 * localBit witnessExperiment z y (wcoord 1) +
    2 * localBit witnessExperiment z y (wcoord 3) + localBit witnessExperiment z y (wcoord 5)
  | 1 => 2 * localBit witnessExperiment z y (wcoord 3) + localBit witnessExperiment z y (wcoord 4)
  | _ => 8 * localBit witnessExperiment z y (wcoord 0) +
    4 * localBit witnessExperiment z y (wcoord 1) +
    2 * localBit witnessExperiment z y (wcoord 2) + localBit witnessExperiment z y (wcoord 5)

/-- The displayed rational table entries, by assignment and lexicographic row. -/
noncomputable def hStarValue (z n : ℕ) : ℝ :=
  match z, n with
  | 0, 0 => 0 | 0, 1 => 5 | 0, 2 => 1 | 0, 3 => 0
  | 0, 4 => 0 | 0, 5 => 1 | 0, 6 => 5 | 0, 7 => 0
  | 1, 0 => 0 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 11/3 | 2, 3 => 14/3
  | 2, 4 => 2 | 2, 5 => 0 | 2, 6 => 14/3 | 2, 7 => 8/3
  | 2, 8 => 8/3 | 2, 9 => 14/3 | 2, 10 => 0 | 2, 11 => 2
  | 2, 12 => 14/3 | 2, 13 => 11/3 | 2, 14 => 2 | 2, 15 => 0
  | _, _ => 0

/-- Nonnegative rational assignment tables implementing `bStar`. -/
noncomputable def hStar : AssignmentRule witnessExperiment := fun z y =>
  hStarValue z.1 (witnessLocalIndex z y)
  -- @realizes h_z^\star(displayed 8, 4, and 16 rational table entries)

/-- Binary code of a six-coordinate schedule, left-to-right as displayed in the paper. -/
noncomputable def witnessCode (θ : Theta witnessExperiment) : ℕ :=
  ∑ i, (θ i : ℕ) * 2 ^ (5 - i.1)

/-- Uniform law on the displayed sixteen schedules. -/
noncomputable def muStar (θ : Theta witnessExperiment) : ℝ :=
  if witnessCode θ ∈ ([0,7,11,14,19,20,28,31,32,39,43,44,48,53,56,59] : List ℕ) then 1/16 else 0
  -- @realizes \mu^\star(uniform mass on the listed sixteen schedules)

/-- Uniform law on the displayed eight schedules. -/
noncomputable def nuStar (θ : Theta witnessExperiment) : ℝ :=
  if witnessCode θ ∈ ([3,10,16,31,36,47,49,60] : List ℕ) then 1/8 else 0
  -- @realizes \nu^\star(uniform mass on the listed eight schedules)

/-- Uniform objective weights on the witness cube. -/
noncomputable def witnessQ : Theta witnessExperiment → ℝ := fun _ => 1 / 64

/-- [Every nonzero score coordinate in the concrete witness is observed](goal). -/
lemma witnessObservableScore : ObservableScore witnessExperiment := by
  classical
  change ∀ (z : Fin 3) (i : Fin 6), witnessV z i ≠ 0 → i ∈ witnessO z
  intro z i h
  fin_cases z <;> fin_cases i <;> simp_all [witnessV, witnessO]

/-- [The uniform objective weights on the witness cube are strictly positive and sum to one](goal). -/
lemma witnessQ_fullSupport : FullSupportWeight witnessExperiment witnessQ := by
  constructor
  · intro θ
    norm_num [witnessQ]
  · norm_num [witnessQ, witnessExperiment, Fin.sum_univ_succ]

/-- [The full-support witness objective](goal) consists of the uniform cube weights together with their positivity and normalization certificate. -/
noncomputable def witnessObjective : FullSupportObjective witnessExperiment :=
  ⟨witnessQ, witnessQ_fullSupport⟩

/-- The entire six-coordinate witness, including every displayed primal, implementation, and dual
certificate rather than only its underlying finite design. -/
structure WitnessExperimentData where
  experiment : Setup
  objective : FullSupportObjective experiment
  scoreVariance : ScoreVarianceData experiment
  quadraticPolynomial : (Fin 6 → ℝ) → ℝ
  unrestrictedOptimizer : Theta experiment → ℝ
  quadraticOptimizer : Theta experiment → ℝ
  implementationTables : AssignmentRule experiment
  allDegreeDual : Theta experiment → ℝ
  degreeThreeDual : Theta experiment → ℝ

-- @node: def:witness-experiment
/-- [The complete witness-data bundle](goal) uses [the concrete finite experiment](step:1), [its uniform full-support objective](step:2), [its design variance and observability certificate](step:3), [the displayed quadratic polynomial](step:4), [the unrestricted optimizer](step:5), [the quadratic optimizer](step:6), [the implementing assignment tables](step:7), [the all-degree dual law](step:8), and [the degree-three dual law](step:9). -/
noncomputable def witnessSetup : WitnessExperimentData where
  experiment := witnessExperiment
  objective := witnessObjective
  scoreVariance := designVarianceFn witnessExperiment witnessObservableScore
  quadraticPolynomial := witnessP
  unrestrictedOptimizer := bStar
  quadraticOptimizer := rStar
  implementationTables := hStar
  allDegreeDual := muStar
  degreeThreeDual := nuStar
  -- @realizes \mathfrak E_\star(full experiment and displayed P, b-star, r-star, h-star, mu-star, nu-star tables)

end CausalSmith.Experimentation.BinaryTruthbound
