module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Basic
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Concrete partial matchings and the balanced schedule prior

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

-- @env: S4
variable (n m : ℕ)
/-- A finite partial injective map from recipients to donors. -/
abbrev Matching (m : ℕ) : Type :=
  {φ : Fin m → Option (Fin m) // ∀ i i' j, φ i = some j → φ i' = some j → i = i'}
-- @realizes Match(all legal partial injective recipient-to-donor maps)
/-- The finite family has its inherited subtype enumeration. -/
instance (m : ℕ) : Fintype (Matching m) := Fintype.ofFinite _
/-- The matching family has the discrete measurable structure. -/
instance (m : ℕ) : MeasurableSpace (Matching m) := ⊤
/-- The edges of a matching, stored in donor-recipient order. -/
def Matching.edges {m : ℕ} (M : Matching m) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => M.1 e.2 = some e.1) -- @realizes M(legal edge set on donor and recipient indices)
/-- The matching size. -/
def Matching.size {m : ℕ} (M : Matching m) : ℕ := M.edges.card -- @realizes K(number of matching arrows)
/-- The dilute activity. -/
def activity (m : ℕ) : ℝ := 1/(4*m) -- @realizes lambda(activity formula 1/(4m); positivity under 1≤m via activity_pos)
/-- The finite unnormalized matching weight. -/
def matchingWeight (m : ℕ) (M : Matching m) : ℝ := activity m ^ M.size
/-- The normalizing partition sum. -/
def matchingPartition (m : ℕ) : ℝ := ∑ M : Matching m, matchingWeight m M
/-- The normalized matching prior mass. -/
def matchingPriorMass (m : ℕ) (M : Matching m) : ℝ := matchingWeight m M / matchingPartition m
/-- The dilute prior is a normalized finite Dirac mixture. -/
def matchingPrior (m : ℕ) : Measure (Matching m) :=
  ∑ M : Matching m, ENNReal.ofReal (matchingPriorMass m M) • Measure.dirac M
-- @realizes Pi(normalized λ^|M| law on all partial matchings)
/-- The matched-count threshold. -/
def kZero (m : ℕ) : ℕ := m/64 -- @realizes kzero(floor(m/64))
/-- Given [the stated assumptions](hyp:hfit), [A donor label fits inside the full population.](goal) -/
-- @node: donor_lt
lemma donor_lt (hfit : 2*m ≤ n) (j : Fin m) : j.val < n := by
  have hj := j.isLt
  omega
/-- Given [the stated assumptions](hyp:hfit), [A recipient label fits inside the full population.](goal) -/
-- @node: recipient_lt
lemma recipient_lt (hfit : 2*m ≤ n) (i : Fin m) : m+i.val < n := by
  have hi := i.isLt
  omega
/-- Embed the first m paper labels as donors. -/
def donorOf (hfit : 2*m ≤ n) (j : Fin m) : Fin n := ⟨j.val, donor_lt n m hfit j⟩ -- @realizes Dset(image in Fin n has paper labels {1,...,m} under v↦v.val+1)
-- @realizes j(donor index)
/-- Embed the next m paper labels as recipients. -/
def recipientOf (hfit : 2*m ≤ n) (i : Fin m) : Fin n := ⟨m+i.val, recipient_lt n m hfit i⟩ -- @realizes Cset(image in Fin n has paper labels {m+1,...,2m} under v↦v.val+1)
-- @realizes i(recipient index)
/-- A candidate matching's concrete population graph. -/
def matchingEdge (hfit : 2*m ≤ n) (M : Matching m) (j i : Fin n) : Prop :=
  ∃ c a : Fin m, i = recipientOf n m hfit c ∧ j = donorOf n m hfit a ∧ M.1 c = some a
/-- Given [the stated assumptions](hyp:hfit), [Bipartite matching graphs have no diagonal arrows.](goal) -/
-- @node: matchingEdge_irrefl
lemma matchingEdge_irrefl (hfit : 2*m ≤ n) (M : Matching m) :
    ∀ i, ¬ matchingEdge n m hfit M i i := by
  rintro i ⟨c, a, hic, hia, _⟩
  have hv := congrArg Fin.val (hic.symm.trans hia)
  change m + c.val = a.val at hv
  have ha := a.isLt
  omega
/-- A graph-only schedule with zero responses, used to acquire the matching graph. -/
def matchingGraphSchedule (hfit : 2*m ≤ n) (M : Matching m) : Schedule (Fin n) where
  edge := matchingEdge n m hfit M
  decEdge := Classical.decRel _
  irrefl := matchingEdge_irrefl n m hfit M
  a := fun _ => 0
  t := fun _ => 0
  b := fun _ _ => 0
/-- Matching, independent recipient baselines, and independent fair signs. -/
abbrev PriorParam (m : ℕ) : Type := Matching m × (Fin m → ℝ) × (Fin m → Bool)
/-- The inherited compact baseline density. -/
abbrev baselineDensity (y : ℝ) : ℝ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y
-- @realizes f(4 cos²(2πy) on |y|≤1/4, zero elsewhere)
-- @realizes y(real scalar density argument)
/-- The baseline and fair signs are independently drawn before the experiment. -/
def balancedParamLaw (m : ℕ) : Measure (PriorParam m) :=
  (matchingPrior m).prod ((Measure.pi (fun _ : Fin m =>
    volume.withDensity (fun y => ENNReal.ofReal (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y)))).prod
    (Measure.pi (fun _ : Fin m => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2))))
/-- Concrete balanced affine responses: matched recipients share their donor's causal sign,
unmatched recipients receive an independent fair constant shift. -/
def balancedSchedule (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ) (ξ : PriorParam m) : Schedule (Fin n) where
  edge := matchingEdge n m hfit ξ.1
  decEdge := Classical.decRel _
  irrefl := matchingEdge_irrefl n m hfit ξ.1
  a := fun i => ∑ c : Fin m, if i = recipientOf n m hfit c then
    if ξ.1.1 c = none then ξ.2.1 c + δ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (ξ.2.2 c)
    else ξ.2.1 c - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * δ else 0
  t := fun _ => 0
  b := fun _ _ => 2 * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * δ
-- @realizes sigma(Bool-coded causal sign, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ ∈ {-1,1})
/-- The supported schedule prior, realized by its parameter law and concrete schedule map. -/
-- @node: def:balanced-prior
def balancedPrior (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ) :
    Measure (PriorParam m) × (PriorParam m → Schedule (Fin n)) :=
  (balancedParamLaw m, balancedSchedule n m hfit σ δ)
-- @realizes Pisign(law of the explicitly constructed pre-experiment affine schedules)
/-- Given [the stated assumptions](hyp:hfit), [A candidate donor-recipient arrow is off diagonal.](goal) -/
-- @node: candidate_ne
lemma candidate_ne (hfit : 2*m ≤ n) (e : Fin m × Fin m) :
    donorOf n m hfit e.1 ≠ recipientOf n m hfit e.2 := by
  intro heq
  have hv := congrArg Fin.val heq
  change e.1.val = m + e.2.val at hv
  have ha := e.1.isLt
  omega
/-- The full acquired-graph coordinate for a candidate arrow. -/
def candidateArrow (hfit : 2*m ≤ n) (e : Fin m × Fin m) : OffDiag (Fin n) :=
  ⟨(donorOf n m hfit e.1, recipientOf n m hfit e.2), candidate_ne n m hfit e⟩
/-- Matching supersets are enumerated inside the finite legal family. -/
def supersets (F : Matching m) : Finset (Matching m) :=
  Finset.univ.filter (fun M => F.edges ⊆ M.edges)

/-- [A partial injective matching has at most one arrow per recipient.](goal) -/
-- @node: matching_size_le
lemma matching_size_le (m : ℕ) (M : Matching m) : M.size ≤ m := by
  have hinj : Set.InjOn Prod.snd (M.edges : Set (Fin m × Fin m)) := by
    intro e he e' he' h
    have heq : M.1 e.2 = some e.1 := (Finset.mem_filter.mp he).2
    have heq' : M.1 e'.2 = some e'.1 := (Finset.mem_filter.mp he').2
    have ha : e.1 = e'.1 := Option.some.inj (heq.symm.trans (h ▸ heq'))
    exact Prod.ext ha h
  simpa [Matching.size] using
    (Finset.card_le_card_of_injOn (f := Prod.snd)
      (s := M.edges) (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj)
-- @realizes K(derived size range {0,...,m})
/-- Given [the stated assumptions](hyp:hm), [Positive matching size gives positive activity.
@realizes lambda(positive activity under the admitted premise 1≤m)](goal) -/
-- @node: activity_pos
lemma activity_pos (m : ℕ) (hm : 1 ≤ m) : 0 < activity m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold activity
  positivity
/-- [The explicit finite normalization defines a probability prior.](goal) -/
-- @node: matchingPrior_probability
lemma matchingPrior_probability (m : ℕ) : IsProbabilityMeasure (matchingPrior m) := by
  have hw (M : Matching m) : 0 ≤ matchingWeight m M := by
    unfold matchingWeight activity
    positivity
  let empty : Matching m := ⟨fun _ => none, by simp⟩
  have hempty : matchingWeight m empty = 1 := by
    simp [matchingWeight, Matching.size, Matching.edges, empty]
  have hpart : 0 < matchingPartition m := by
    have hle := Finset.single_le_sum (fun M _ => hw M) (Finset.mem_univ empty)
    rw [hempty] at hle
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle
  have hmass (M : Matching m) : 0 ≤ matchingPriorMass m M :=
    div_nonneg (hw M) hpart.le
  have hsum : (∑ M : Matching m, matchingPriorMass m M) = 1 := by
    simp only [matchingPriorMass, ← Finset.sum_div]
    exact div_self (ne_of_gt hpart)
  constructor
  simp only [matchingPrior, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun M _ => hmass M), hsum]
  norm_num
-- @realizes Pi(probability law on the finite legal matching family)

end CausalSmith.Experimentation.NoisygraphTtePrecision
