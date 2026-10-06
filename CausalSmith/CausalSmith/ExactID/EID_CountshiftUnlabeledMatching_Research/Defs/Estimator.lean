module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Fiber
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Robust factorial moments and noisy target certificates. -/

@[expose] public section

open MeasureTheory Real

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @env: S3
variable {p M n : ℕ}

/-- Odd number of median-of-means blocks. -/
noncomputable def momBlocks (η : ℝ) : ℕ :=
  2 * ⌈(8 * Real.log (2 / η) - 1) / 2⌉₊ + 1

/-- Mean of a disjoint block; unused remainder observations are discarded. -/
noncomputable def blockMean (k : ℕ) (Y : Fin n → ℝ) (s : Fin k) : ℝ :=
  let block := Finset.univ.filter (fun r : Fin n =>
    r.val / (n / k) = s.val ∧ r.val < k * (n / k))
  (∑ r ∈ block, Y r) / block.card

/-- Median of the block means. -/
noncomputable def medianOfMeans (k : ℕ) (Y : Fin n → ℝ) : ℝ :=
  sInf {x : ℝ | (k + 1) / 2 ≤
    (Finset.univ.filter (fun s : Fin k => blockMean k Y s ≤ x)).card}

/-- Clipped log factorial estimator. @realizes \widehat\mu_m(clipped robust moments) -/
noncomputable def muHat (ℓ : ℝ)
    (δ : {x : ℝ // 0 < x ∧ x < 1 / 2}) -- @realizes \delta(0<δ<1/2)
    (U W : Fin (p + 1) → Fin n → Fin p → ℝ)
    (m : Fin (p + 1)) (j : Fin p) : ℝ :=
  let k := momBlocks ((δ : ℝ) / (2 * p * (p + 1)))
  2 * Real.log (max (ℓ / 2) (medianOfMeans k (fun r => U m r j))) -
    (1 / 2 : ℝ) * Real.log
      (max (ℓ ^ 2 / 2) (medianOfMeans k (fun r => W m r j)))

/-- Shift estimator from offset-adjusted factorial counts. -/
-- @node: def:robust-moment-estimator
noncomputable def robustShiftEstimator (ℓ : ℝ)
    (δ : {x : ℝ // 0 < x ∧ x < 1 / 2}) -- @realizes \delta(estimator domain)
    (S : Fin (p + 1) → Fin n → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Fin p → ℕ)
    (m : Fin p) (j : Fin p) : ℝ :=
  let U : Fin (p + 1) → Fin n → Fin p → ℝ :=
    fun e r i => firstFactorial (X e r) (S e r) i
  let W : Fin (p + 1) → Fin n → Fin p → ℝ :=
    fun e r i => secondFactorial (X e r) (S e r) i
  muHat ℓ δ U W m.succ j - muHat ℓ δ U W 0 j
  -- @realizes \widehat d_m(estimated mean difference)

/-- Simultaneous deviation radius. @realizes \epsilon_n(universal-constant radius) -/
noncomputable def epsN (C : ℝ) (p n : ℕ) (v ℓ δ : ℝ) : ℝ :=
  -- @realizes C(universal deviation constant)
  C * Real.sqrt (v * Real.log (4 * p * (p + 1) / δ) / n) *
    (ℓ⁻¹ + ℓ⁻¹ ^ 2)

/-- Variance envelope for the unit-offset Gaussian permutation submodel.
@realizes v_0(a)(explicit moment envelope) -/
noncomputable def v0 (a : ℝ) : ℝ :=
  max (Real.exp (a + 1 / 2) + (Real.exp 1 - 1) * Real.exp (2 * a + 1))
    (4 * Real.exp (3 * a + 9 / 2) + 2 * Real.exp (2 * a + 2) +
      Real.exp (4 * a + 8) - Real.exp (4 * a + 4))

/-- A noisy support edge. @realizes \widehat G_{\epsilon}(|dhat|>ε) -/
def noisyGraph (dhat : Fin p → Fin p → ℝ)
    (ε : {x : ℝ // 0 ≤ x}) -- @realizes \epsilon(nonnegative graph radius)
    (m i : Fin p) : Prop := (ε : ℝ) < |dhat m i|

/-- Return the unique perfect matching, or abstain. -/
-- @node: def:one-sided-certificate
noncomputable def oneSidedCertificate (dhat : Fin p → Fin p → ℝ)
    (ε : {x : ℝ // 0 < x}) : -- @realizes \epsilon(positive certificate radius)
    Option (Equiv.Perm (Fin p)) := by
  classical
  exact if h : ∃! σ : Equiv.Perm (Fin p),
      ∀ m, noisyGraph dhat ⟨ε.val, le_of_lt ε.property⟩ m (σ m)
    then some (Classical.choose h.exists)
    else none
  -- @realizes \widehat t_{\epsilon}(unique matching or abstain)

/-- Thresholded recovered support. -/
noncomputable def recoveredSupport (dhat : Fin M → Fin p → ℝ)
    (β : ℝ) (m : Fin M) : Finset (Fin p) :=
  Finset.univ.filter (fun i => β / 2 < |dhat m i|)

/-- All recovered supports are nonempty and the distinct support family is feasible. -/
noncomputable def recoveredCompatible (dhat : Fin M → Fin p → ℝ)
    (β : ℝ) : Prop :=
  (∀ m, recoveredSupport dhat β m ≠ ∅) ∧
  peelsAll (fun g : {s : Finset (Fin p) //
    s ∈ Finset.univ.image (recoveredSupport dhat β)} => g.val)

/-- Group equal recovered supports and peel the distinct groups. -/
-- @node: def:noisy-incomplete-handle
noncomputable def noisyIncompleteHandle (dhat : Fin M → Fin p → ℝ)
    (_ε β : ℝ) : Fin M → Finset (Fin p) := by
  classical
  let T : Finset (Finset (Fin p)) := Finset.univ.image (recoveredSupport dhat β)
  let G := {s : Finset (Fin p) // s ∈ T}
  let S : G → Finset (Fin p) := Subtype.val
  let group : Fin M → G := fun m =>
    ⟨recoveredSupport dhat β m,
      Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩⟩
  exact if recoveredCompatible dhat β
    then fun m => frozenPeeling S (group m)
    else fun _ => Finset.univ

/-- The support grouping and maintained-incidence peeling algorithm, paired with
its count of coordinate comparisons and elementary incidence operations. -/
noncomputable def costedNoisyIncompleteHandle (dhat : Fin M → Fin p → ℝ)
    (_ε β : ℝ) : (Fin M → Finset (Fin p)) × ℕ := by
  classical
  let T : Finset (Finset (Fin p)) := Finset.univ.image (recoveredSupport dhat β)
  let G := {s : Finset (Fin p) // s ∈ T}
  let S : G → Finset (Fin p) := Subtype.val
  let group : Fin M → G := fun m =>
    ⟨recoveredSupport dhat β m,
      Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩⟩
  let base := incidencePeelRun S none
  let total := M * M * p + base.cost +
    ∑ g : G, (costedFrozenPeeling S g).2
  exact if (∀ m, recoveredSupport dhat β m ≠ ∅) ∧ base.remaining = ∅ then
    (fun m => (costedFrozenPeeling S (group m)).1, total)
  else (fun _ => Finset.univ, total)

/-- Delay of the batch enumerator: preprocessing precedes its first output;
each later stored marginal set takes one output operation. -/
noncomputable def noisyIncompleteDelay (dhat : Fin M → Fin p → ℝ)
    (ε β : ℝ) (m : Fin M) : ℕ :=
  if m.val = 0 then (costedNoisyIncompleteHandle dhat ε β).2 + 1 else 1

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
