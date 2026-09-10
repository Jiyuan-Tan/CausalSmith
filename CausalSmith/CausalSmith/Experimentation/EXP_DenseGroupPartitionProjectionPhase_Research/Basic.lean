import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.FinitePopulationMoments
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.Real.Sqrt

/-!
# Dense random-group experiments: finite-population slice

This file defines the deterministic composition-indexed potential-outcome schedule,
the uniform fixed-cardinality slice, and its group-level moments.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @env: S1
variable (n M : ℕ) -- @realizes n(population size ℕ) @realizes M(common group size ℕ)

/-- The labeled finite population. -/
abbrev Population (n : ℕ) := Fin n -- @realizes \mathcal U_n(carrier Fin n)

/-- The fixed-cardinality slice of candidate groups. -/
abbrev Omega (n M : ℕ) := {A : Finset (Fin n) // A.card = M}
  -- @realizes \Omega_{n,M}(M-subsets of the labeled population)

/-- The two treatment arms. -/
abbrev Arm := Bool -- @realizes \mathcal Z(two-arm carrier)

/-- A deterministic potential-outcome schedule, defined only for units belonging to the group. -/
abbrev PotentialOutcome (n M : ℕ) :=
  (A : Omega n M) → {i : Fin n // i ∈ A.1} → Arm → ℝ
  -- @realizes Y_{i,n}(z,A)(composition-indexed real schedule)

/-- The uniform design on the `M`-slice. -/
noncomputable def slice (hM : M ≤ n) : FiniteDesign (Omega n M) :=
  completeRandomization M (by simpa using hM)
  -- @realizes \mathbb E_n(uniform slice law)

/-- Uniform-slice inner product. -/
noncomputable def sliceInner (hM : M ≤ n) (f g : Omega n M → ℝ) : ℝ :=
  (slice n M hM).E (fun A => f A * g A)
  -- @realizes \langle\cdot,\cdot\rangle_n(uniform expectation of product)

/-- Squared uniform-slice norm. -/
noncomputable def sliceNormSq (hM : M ≤ n) (f : Omega n M → ℝ) : ℝ :=
  sliceInner n M hM f f
  -- @realizes \|\cdot\|_n(squared slice norm)

/-- Uniform-slice norm. -/
noncomputable def sliceNorm (hM : M ≤ n) (f : Omega n M → ℝ) : ℝ :=
  Real.sqrt (sliceNormSq n M hM f)

-- @node: def:group-table
/-- The arm-specific mean outcome of a candidate group. -/
noncomputable def armTable (Y : PotentialOutcome n M) (z : Arm) (A : Omega n M) : ℝ :=
  (∑ i ∈ A.1.attach, Y A i z) / (M : ℝ)
  -- @realizes h_{z,n}(group mean formula)

/-- The centered arm table. -/
noncomputable def armTableCentered (hM : M ≤ n) (Y : PotentialOutcome n M)
    (z : Arm) (A : Omega n M) : ℝ :=
  armTable n M Y z A - (slice n M hM).E (armTable n M Y z)
  -- @realizes h_{z,n}^{\circ}(arm table minus slice mean)

/-- The uniform-slice arm variance. -/
noncomputable def armVar (hM : M ≤ n) (Y : PotentialOutcome n M) (z : Arm) : ℝ :=
  (slice n M hM).Var (armTable n M Y z)
  -- @realizes V_{z,n}(uniform-slice variance)

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
