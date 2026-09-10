import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.FiniteSupport
import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight

/-! A policy-restricted four-mask forward/reverse monotone-deque scan. -/

open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

structure ScanEntry where
  policyIndex : ℕ
  regret : ℝ
  comparatorIndex : ℕ
  directionForward : Bool
  activeMask : Fin 4
  allocationCoefficient : Bool → Bool → ℝ

def maskContains (mask : Fin 4) (r : Bool) : Bool :=
  Nat.testBit mask.val (if r then 1 else 0)

def maskCoefficient (z w : ℝ) (mask : Fin 4) (r : Bool) : ℝ :=
  if maskContains mask r then -w else z

def maskWindow (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (mask : Fin 4) (j i : ℕ) : Prop :=
  i ≤ j ∧ ∀ r : Bool,
    if maskContains mask r then d r ≤ A r j - A r i
    else A r j - A r i ≤ d r

def entersWindow (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (mask : Fin 4) (j i : ℕ) : Prop :=
  i ≤ j ∧ ∀ r : Bool, maskContains mask r = true → d r ≤ A r j - A r i

def staysInWindow (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (mask : Fin 4) (j i : ℕ) : Prop :=
  ∀ r : Bool, maskContains mask r = false → A r j - A r i ≤ d r

def maskObjective (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (z w : ℝ) (mask : Fin 4) (j i : ℕ) : ℝ :=
  (∑ r : Bool, maskCoefficient z w mask r * A r j) +
    (z + w) * ∑ r : Bool, if maskContains mask r then d r else 0 -
    ∑ r : Bool, maskCoefficient z w mask r * A r i

def dequeScore (A : Bool → ℕ → ℝ) (z w : ℝ)
    (mask : Fin 4) (i : ℕ) : ℝ :=
  -∑ r : Bool, maskCoefficient z w mask r * A r i

def pushMonotone (score : ℕ → ℝ) (q : List ℕ) (i : ℕ) : List ℕ :=
  ((q.reverse.dropWhile fun k => score k ≤ score i).reverse).append [i]

def monotoneDeque (score : ℕ → ℝ) (xs : List ℕ) : List ℕ :=
  xs.foldl (pushMonotone score) []

structure MaskScanState where
  pending : List ℕ
  deque : List ℕ

noncomputable def advanceMaskState (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (z w : ℝ) (mask : Fin 4) (j : ℕ) (state : MaskScanState) : MaskScanState := by
  classical
  let entered := state.pending.takeWhile (fun i => decide (entersWindow A d mask j i))
  let pending := state.pending.drop entered.length
  let queued := entered.foldl (pushMonotone (dequeScore A z w mask)) state.deque
  let deque := queued.dropWhile (fun i => decide (¬ staysInWindow A d mask j i))
  exact { pending := pending, deque := deque }

def endpointCoefficient (q d p : Bool → ℝ) (complement : Bool)
    (r inside : Bool) : ℝ :=
  let allocated := min (d r) (p r)
  let base := if inside then
      if p r = 0 then 0 else allocated / p r
    else if q r - p r = 0 then 0 else (d r - allocated) / (q r - p r)
  if complement then 1 - base else base

structure ScanCandidate where
  mask : Fin 4
  comparatorIndex : ℕ
  objective : ℝ
  coefficient : Bool → Bool → ℝ

def candidateFromState (A : Bool → ℕ → ℝ) (q d : Bool → ℝ)
    (z w : ℝ) (complement : Bool) (j : ℕ) (mask : Fin 4)
    (state : MaskScanState) : Option ScanCandidate :=
  match state.deque with
  | [] => none
  | i :: _ =>
      let p := fun r => A r j - A r i
      some
        { mask := mask
          comparatorIndex := i
          objective := maskObjective A d z w mask j i
          coefficient := endpointCoefficient q d p complement }

def betterCandidate (x y : ScanCandidate) : ScanCandidate :=
  if x.objective ≤ y.objective then y else x

def bestCandidate (j : ℕ) (xs : List ScanCandidate) : ScanCandidate :=
  xs.foldl betterCandidate
    { mask := 0, comparatorIndex := j, objective := 0,
      coefficient := fun _ _ => 0 }

structure DirectionScanState where
  masks : Fin 4 → MaskScanState
  outputRev : List ScanEntry
  operations : ℕ
  peakMemory : ℕ

def directionStep (A : Bool → ℕ → ℝ) (q d : Bool → ℝ)
    (z w : ℝ) (forward : Bool) (j : ℕ)
    (state : DirectionScanState) : DirectionScanState :=
  let next := fun mask => advanceMaskState A d z w mask j (state.masks mask)
  let candidates := (List.ofFn fun mask : Fin 4 =>
    candidateFromState A q d z w (!forward) j mask (next mask)).filterMap id
  let best := bestCandidate j candidates
  let entry : ScanEntry :=
    { policyIndex := j
      regret := max 0 best.objective
      comparatorIndex := best.comparatorIndex
      directionForward := forward
      activeMask := best.mask
      allocationCoefficient := best.coefficient }
  let stepOps := 5 + (∑ mask : Fin 4,
    (let entered := (state.masks mask).pending.length - (next mask).pending.length
     entered + ((state.masks mask).deque.length + entered - (next mask).deque.length) + 1))
  let currentMemory := state.outputRev.length + 1 +
    (∑ mask : Fin 4, ((next mask).pending.length + (next mask).deque.length))
  { masks := next
    outputRev := entry :: state.outputRev
    operations := state.operations + stepOps
    peakMemory := max state.peakMemory currentMemory }

def runDirection (A : Bool → ℕ → ℝ) (q d : Bool → ℝ)
    (z w : ℝ) (K : List ℕ) (forward : Bool) : DirectionScanState :=
  let initial : DirectionScanState :=
    { masks := fun _ => { pending := K, deque := [] }
      outputRev := []
      operations := 0
      peakMemory := 4 * K.length }
  K.foldl (fun state j => directionStep A q d z w forward j state) initial

def reversePrefixes (m : ℕ) (A : Bool → ℕ → ℝ) : Bool → ℕ → ℝ :=
  fun r j => A r m - A r (m - j)

structure ScanResult where
  entries : List ScanEntry
  operations : ℕ
  peakMemory : ℕ

/-- Validated output of sorting, tie aggregation, prefix formation, and policy
deduplication.  The scan consumes this object, so ordered nonempty represented
indices, prefix-mass identities, and cutoff representatives are enforced before
the deque kernel starts. -/
structure ScanInput (M : ImperfectReferenceModel) where
  m : ℕ
  atom : Bool → Fin m → ℝ -- @realizes \(w_{rj}\)(aggregated cell masses)
  prefixes : Bool → ℕ → ℝ -- @realizes \(A_r(j)\)(validated prefix masses)
  a : Bool → ℝ
  q : Bool → ℝ
  b : ℝ
  c : ℝ
  indices : List ℕ -- @realizes \(K_{\mathcal T}\)(ordered represented indices)
  representative : ℕ → EReal
  inducedIndex : EReal → ℕ
  indices_nonempty : indices ≠ []
  indices_nodup : indices.Nodup
  indices_ordered : indices.Pairwise (· < ·)
  indices_bounded : ∀ j ∈ indices, j ≤ m
  atom_mem_Icc : ∀ r k, atom r k ∈ Set.Icc (0 : ℝ) 1
    -- @realizes \(w_{rj}\)(per-cell probability range [0,1])
  prefix_zero : ∀ r, prefixes r 0 = 0
  prefix_sum : ∀ r j, j ≤ m →
    prefixes r j = ∑ k : Fin m, if (k : ℕ) < j then atom r k else 0
  prefix_monotone : ∀ r, Monotone (prefixes r)
  prefix_mem_Icc : ∀ r j, j ≤ m → prefixes r j ∈ Set.Icc (0 : ℝ) 1
    -- @realizes \(A_r(j)\)(probability-prefix range [0,1])
  prefix_terminal : ∀ r, prefixes r m = q r
  allocation_feasible : ∀ r, 0 ≤ a r ∧ a r ≤ q r
  representative_mem : ∀ j ∈ indices, representative j ∈ M.T
  representative_index : ∀ j ∈ indices, inducedIndex (representative j) = j
  exhaustive : ∀ t ∈ M.T, inducedIndex t ∈ indices

-- @node: def:linear-scan
def scan {M : ImperfectReferenceModel} (input : ScanInput M) : ScanResult :=
  let forward := runDirection input.prefixes input.q input.a input.b input.c
    input.indices true
  let Kreverse := input.indices.reverse.map (fun j => input.m - j)
  let reverse := runDirection (reversePrefixes input.m input.prefixes) input.q
    (fun r => input.q r - input.a r) input.c input.b Kreverse false
  let forwardEntries := forward.outputRev.reverse
  let reverseEntries := reverse.outputRev.map fun e =>
    { policyIndex := input.m - e.policyIndex
      regret := e.regret
      comparatorIndex := input.m - e.comparatorIndex
      directionForward := e.directionForward
      activeMask := e.activeMask
      allocationCoefficient := e.allocationCoefficient }
  { entries := List.zipWith
      (fun x y => if x.regret ≤ y.regret then y else x) forwardEntries reverseEntries
    operations := forward.operations + reverse.operations + input.indices.length
    peakMemory := max forward.peakMemory reverse.peakMemory }
  -- @realizes \(\mathsf{Scan}\)(validated four-mask forward/reverse deque scan)

lemma monotoneDeque_head_max (score : ℕ → ℝ) (xs : List ℕ)
    (i : ℕ) (hi : i ∈ xs) :
    score i ≤ score ((monotoneDeque score xs).headD i) := by
  have headD_eq_of_ne_nil_of_prefix {l q : List ℕ} {d : ℕ}
      (hl : l ≠ []) (hp : l <+: q) : l.headD d = q.headD d := by
    rcases l with _ | ⟨a, l⟩
    · contradiction
    rcases q with _ | ⟨b, q⟩
    · simp at hp
    have heq := List.prefix_iff_eq_append.mp hp
    simpa using congrArg List.head? heq
  have headD_append_of_ne_nil (l t : List ℕ) (d : ℕ)
      (hl : l ≠ []) : (l ++ t).headD d = l.headD d := by
    cases l <;> simp_all
  have push_mem (q : List ℕ) (j x : ℕ)
      (hx : x ∈ pushMonotone score q j) : x ∈ q ∨ x = j := by
    have hx' : x ∈
        (q.reverse.dropWhile (fun k => score k ≤ score j)).reverse ∨ x = j := by
      simpa [pushMonotone] using hx
    rcases hx' with hx' | hxj
    · left
      have hxrev : x ∈ q.reverse :=
        (List.dropWhile_suffix _).sublist.subset (by simpa using hx')
      simpa using hxrev
    · exact Or.inr hxj
  have push_ne_nil (q : List ℕ) (j : ℕ) :
      pushMonotone score q j ≠ [] := by
    simp [pushMonotone]
  have push_head_max (q : List ℕ) (j x d : ℕ)
      (hqne : q ≠ []) (hq : ∀ k ∈ q, score k ≤ score (q.headD d))
      (hx : score x ≤ score (q.headD d) ∨ x = j) :
      score x ≤ score ((pushMonotone score q j).headD d) := by
    cases q with
    | nil => contradiction
    | cons a q =>
      have hqa : ∀ k ∈ a :: q, score k ≤ score a := by simpa using hq
      by_cases haj : score a ≤ score j
      · have hdrop :
            (a :: q).reverse.dropWhile (fun k => score k ≤ score j) = [] := by
          rw [List.dropWhile_eq_nil_iff]
          intro k hk
          simp only [decide_eq_true_eq]
          exact (hqa k (by simpa [or_comm] using hk)).trans haj
        have hhead : (pushMonotone score (a :: q) j).headD d = j := by
          change (((a :: q).reverse.dropWhile (fun k => score k ≤ score j)).reverse ++
            [j]).headD d = j
          rw [hdrop]
          simp
        rw [hhead]
        rcases hx with hx | rfl
        · exact hx.trans haj
        · exact le_rfl
      · have hdropne :
            (a :: q).reverse.dropWhile (fun k => score k ≤ score j) ≠ [] := by
          intro h
          have hall := List.dropWhile_eq_nil_iff.mp h
          have ha := hall a (by simp)
          exact haj (by simpa using ha)
        have hpref :
            (a :: q).rdropWhile (fun k => score k ≤ score j) <+: (a :: q) :=
          List.rdropWhile_prefix _ _
        have hrdropne :
            (a :: q).rdropWhile (fun k => score k ≤ score j) ≠ [] := by
          simpa [List.rdropWhile] using hdropne
        have hfirst :
            ((a :: q).rdropWhile (fun k => score k ≤ score j)).headD d = a := by
          calc
            _ = (a :: q).headD d :=
              headD_eq_of_ne_nil_of_prefix hrdropne hpref
            _ = a := by simp
        have hhead : (pushMonotone score (a :: q) j).headD d = a := by
          change (((a :: q).rdropWhile (fun k => score k ≤ score j)) ++ [j]).headD d = a
          rw [headD_append_of_ne_nil _ _ _ hrdropne, hfirst]
        rw [hhead]
        rcases hx with hx | rfl
        · simpa using hx
        · exact le_of_not_ge haj
  have invariant (ys : List ℕ) (d : ℕ) :
      (∀ k ∈ monotoneDeque score ys, k ∈ ys) ∧
      (ys ≠ [] → monotoneDeque score ys ≠ []) ∧
      ∀ k ∈ ys, score k ≤ score ((monotoneDeque score ys).headD d) := by
    induction ys using List.reverseRecOn with
    | nil => simp [monotoneDeque]
    | append_singleton ys j ih =>
      have hstep : monotoneDeque score (ys ++ [j]) =
          pushMonotone score (monotoneDeque score ys) j := by
        simp [monotoneDeque]
      rw [hstep]
      constructor
      · intro k hk
        rcases push_mem _ _ _ hk with hk | rfl
        · exact List.mem_append_left _ (ih.1 k hk)
        · simp
      constructor
      · exact fun _ => push_ne_nil _ _
      · intro k hk
        by_cases hys : ys = []
        · have : k = j := by simpa [hys] using hk
          subst k
          subst ys
          simp [monotoneDeque, pushMonotone]
        · apply push_head_max (monotoneDeque score ys) j k d
          · exact ih.2.1 hys
          · intro x hx
            exact ih.2.2 x (ih.1 x hx)
          · rcases List.mem_append.mp hk with hk | hk
            · exact Or.inl (ih.2.2 k hk)
            · exact Or.inr (by simpa using hk)
  exact (invariant xs i).2.2 i hi

noncomputable def admissibleIndices (A : Bool → ℕ → ℝ) (d : Bool → ℝ)
    (mask : Fin 4) (j k : ℕ) : List ℕ := by
  classical
  exact (List.range (k + 1)).filter (fun i => maskWindow A d mask j i)

lemma maskWindow_endpoints_monotone (A : Bool → ℕ → ℝ)
    (hA : ∀ r, Monotone (A r)) (d : Bool → ℝ) (mask : Fin 4) :
    ∀ {j k}, j ≤ k →
      (admissibleIndices A d mask j k).length ≤ k + 1 := by
  intro j k _
  classical
  unfold admissibleIndices
  simpa using List.length_filter_le
    (fun i => decide (maskWindow A d mask j i)) (List.range (k + 1))

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
