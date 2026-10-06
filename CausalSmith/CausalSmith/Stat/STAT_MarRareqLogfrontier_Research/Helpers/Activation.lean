module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Explicit finite activated laws and the two prior-mixture experiments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @env: S3
variable (n d : ℕ) (q : ℝ)
/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def lowerDegree (n : ℕ) (q : ℝ) : ℕ :=
  Nat.ceil (logScale n q) -- @realizes \(K\)(ceiling ell)
/-- For [the specified inputs and assumptions](hyp:n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def lowerEndpoint (n : ℕ) (q : ℝ) : ℝ :=
  (lowerDegree n q : ℝ) ^ 2 -- @realizes \(H\)(K squared)
/-- Given [the specified inputs and assumptions](hyp:n,q,hq,hslice), [the stated mathematical conclusion holds](goal). -/
-- @node: lower_activation_probability_le_one
lemma lower_activation_probability_le_one (n : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hslice : RareArrivalSlice n q) :
    q * lowerEndpoint n q ≤ 1 := by
  have hN : 0 ≤ effectiveSize n q := by
    unfold effectiveSize
    positivity
  have hlog : 1 ≤ logScale n q := by
    unfold logScale
    have harg : Real.exp 1 ≤ Real.exp 1 + effectiveSize n q := by linarith
    have hpos : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
    have := Real.log_le_log hpos harg
    simpa using this
  have hceil : (lowerDegree n q : ℝ) ≤ 2 * logScale n q := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ logScale n q by linarith)
    unfold lowerDegree
    exact le_of_lt (lt_of_lt_of_le h (by linarith))
  have hdegree : 0 ≤ (lowerDegree n q : ℝ) := by positivity
  have hsq : lowerEndpoint n q ≤ 4 * (logScale n q) ^ 2 := by
    unfold lowerEndpoint
    nlinarith [sq_nonneg ((lowerDegree n q : ℝ) - 2 * logScale n q)]
  have hslice' : q * (logScale n q) ^ 2 ≤ 1 / 64 := hslice
  nlinarith

/-- For [the specified inputs and assumptions](hyp:η,n,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def rareMass (η : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  η / (effectiveSize n q * logScale n q)
  -- @realizes \(b_0\)(positive nominal eta divided by N ell; assigned to a rare cell only when J is positive)

/-- For [the specified inputs and assumptions](hyp:η,n,d,q), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def rareCount (η : ℝ) (n d : ℕ) (q : ℝ) : ℕ :=
  min (d - 1) (Nat.floor ((2 * rareMass η n q)⁻¹))
  -- @realizes \(J\)(number of rare cells)

/-- For [the specified inputs and assumptions](hyp:H,prior), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def FiniteReciprocalPrior (H : ℝ) (prior : Measure ℝ) : Prop :=
  IsProbabilityMeasure prior ∧
    ∃ support : Finset ℝ,
      prior (support : Set ℝ) = 1 ∧
      ∀ z ∈ support, 1 ≤ z ∧ z ≤ H

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def baselineMass (η : ℝ) (n d : ℕ) (q : ℝ) (x : Fin d) : ℝ :=
  if x.val < rareCount η n d q then rareMass η n q
  else if x.val = rareCount η n d q then 1 - rareCount η n d q * rareMass η n q
  else 0

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def lowerCellZ (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ)
    (x : Fin d) : ℝ :=
  if x.val < rareCount η n d q then z x else lowerEndpoint n q

/-- For [the specified inputs and assumptions](hyp:p,b), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def bernWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- For [the specified inputs and assumptions](hyp:d,x,a,y₁,arrival), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def lowerFullRecord {d : ℕ} (x : Fin d) (a y₁ arrival : Bool) : FullRecord d :=
  ⟨x, a, false, false, false, y₁, arrival⟩

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,_hz), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def activatedLaw (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ)
    (_hz : ∀ x, z x ∈ Set.Icc (1 : ℝ) (lowerEndpoint n q))
      -- @realizes \(Z\)(latent reciprocal variable in [1,H])
    :
    Measure (FullRecord d) :=
  ∑ x : Fin d, ∑ a : Bool, ∑ y₁ : Bool, ∑ arrival : Bool,
    ENNReal.ofReal (baselineMass η n d q x / 2 *
      bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y₁ *
      bernWeight (q * lowerCellZ η n d q z x) arrival) •
      Measure.dirac (lowerFullRecord x a y₁ arrival)

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,arrival,one), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def augmentedOutcomeWeight (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag arrival one : Bool) : ℝ :=
  if !flag then if !arrival && !one then 1 else 0
  else if one then
    if arrival && a && x.val < rareCount η n d q then 1 / lowerEndpoint n q else 0
  else if arrival then
    if a && x.val < rareCount η n d q then (z x - 1) / lowerEndpoint n q
    else lowerCellZ η n d q z x / lowerEndpoint n q
  else 1 - lowerCellZ η n d q z x / lowerEndpoint n q

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,_hz), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def augmentedOneRecord (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ)
    (_hz : ∀ x, z x ∈ Set.Icc (1 : ℝ) (lowerEndpoint n q))
      -- @realizes \(Z\)(latent reciprocal variable in [1,H])
    :
    Measure (Bool × ObsRecord d) :=
  ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool, ∑ arrival : Bool, ∑ one : Bool,
    ENNReal.ofReal (baselineMass η n d q x / 2 *
      bernWeight (q * lowerEndpoint n q) flag *
      augmentedOutcomeWeight η n d q z x a flag arrival one) •
        Measure.dirac (flag, ⟨x, a, false, arrival, one⟩)
  -- @realizes \(\mathsf B_{\mathrm{act}}\)(revealed parameter-independent flag)

/-- For [the specified inputs and assumptions](hyp:η,_hη,n,d,q,_hn,_hd,_hq_pos,_hq_le_one,_hregime,prior0,prior1,_hprior0,_hprior1,_hmoments,_hseparation), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: def:activation-lower-handle
noncomputable def activationHandle
    (η : ℝ) -- @realizes \(\eta\)(universal constant selected before n,d,q)
    (_hη : 0 < η) -- @realizes \(\eta\)(positive universal constant)
                  -- @realizes \(b_0\)(activation-scope positive numerator)
    (n d : ℕ) (q : ℝ)
    (_hn : 1 ≤ n) -- @realizes \(b_0\)(activation-scope positive sample size)
    (_hd : 1 ≤ d)
    (_hq_pos : 0 < q) -- @realizes \(b_0\)(activation-scope positive arrival floor)
    (_hq_le_one : q ≤ 1)
    (_hregime : RareArrivalSlice n q)
    (prior0 : Measure ℝ) -- @realizes \(\Pi_0\)(first prior carrier)
    (prior1 : Measure ℝ) -- @realizes \(\Pi_1\)(second prior carrier)
    (_hprior0 : FiniteReciprocalPrior (lowerEndpoint n q) prior0)
      -- @realizes \(\Pi_0\)(finite probability supported on [1,H])
    (_hprior1 : FiniteReciprocalPrior (lowerEndpoint n q) prior1)
      -- @realizes \(\Pi_1\)(finite probability supported on [1,H])
    (_hmoments : ∀ v : ℕ, v ≤ lowerDegree n q →
      (∫ z, z ^ v ∂prior0) = ∫ z, z ^ v ∂prior1)
    (_hseparation : 1 / 12 ≤
      |(∫ z, z⁻¹ ∂prior1) - (∫ z, z⁻¹ ∂prior0)|) :
    Measure (Fin n → Bool × ObsRecord d) × Measure (Fin n → Bool × ObsRecord d) :=
  ((Measure.pi (fun _ : Fin d => prior0)).bind
      (fun z => if hz : ∀ x, z x ∈ Set.Icc (1 : ℝ) (lowerEndpoint n q) then
        Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz) else 0),
   (Measure.pi (fun _ : Fin d => prior1)).bind
      (fun z => if hz : ∀ x, z x ∈ Set.Icc (1 : ℝ) (lowerEndpoint n q) then
        Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz) else 0))
  -- @realizes \(\mathfrak H_{\mathrm{act}}\)(activated fuzzy pair)

end CausalSmith.Stat.MarRareqLogfrontier
