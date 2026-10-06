module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Projection
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines

/-! # Fixed-budget represented upper intervals

One retained rank pair drives both exact coordinates and the literal rational
expression tree. Ideal real endpoints and their evaluated enclosures are separate.
-/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Exact interval intersection; an empty intersection is reported. -/
def boxIntersection (I J : RatInterval) : Option RatInterval :=
  if h : max I.lo J.lo ≤ min I.hi J.hi then some ⟨max I.lo J.lo, min I.hi J.hi, h⟩ else none
/-- A successful intersection is contained in its second input interval. Under the stated assumptions. [The stated hypotheses](hyp:h) hold, and [the stated conclusion follows](goal). -/
-- @node: boxIntersection_subinterval_right
lemma boxIntersection_subinterval_right (I J B : RatInterval)
    (h : boxIntersection I J = some B) : B.Subinterval J := by
  unfold boxIntersection at h
  split at h
  · cases h
    exact ⟨le_max_right _ _, min_le_right _ _⟩
  · cases h

/-- [Exact minimum range. -/
def boxMin (I J : RatInterval) : RatInterval := rationalBox (min I.lo J.lo) (min I.hi J.hi)
/-- Exact maximum range. -/
def boxMax (I J : RatInterval) : RatInterval := rationalBox (max I.lo J.lo) (max I.hi J.hi)
/-- Domain-checked division. -/
def boxDiv (I J : RatInterval) : Option RatInterval :=
  if h : J.hi < 0 ∨ 0 < J.lo then some (I.div J h) else none
/-- Full public effect box. -/
def fullEffectBox : RatInterval := rationalBox (-1/2) (1/2)
/-- Public rank budget, computed with integer comparisons. -/
def qRank (n : ℕ) : ℕ := 7 + 3 * Nat.clog 2 n -- @realizes q_{\mathrm{rank}}(fixed rank precision)
/-- Public endpoint budget. -/
def qEnd (n kC kS : ℕ) : ℕ :=
  44 + Nat.clog 2 (n + 1) + 4 * Nat.clog 2 (max kC kS + 1) -- @realizes q_{\mathrm{end}}(fixed endpoint precision)
/-- Literal engine rank-target enclosures. -/
def rankBoxes (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) : Option (RatInterval × RatInterval) := do
  let q := qRank n
  let a ← boxIntersection (N.alphaName n α β q) (rationalBox 0 1)
  let b ← boxIntersection (N.betaName n α β q) (rationalBox 0 (1/4))
  let c ← boxDiv (RatInterval.point 2)
    ((RatInterval.point 2).mul a |>.add ((RatInterval.point 2).mul b) |>.add (RatInterval.point 1))
  let d ← boxDiv (RatInterval.point 2) (((RatInterval.point 4).mul b).add (RatInterval.point 1))
  return (E.powBox q n c, E.powBox q n d)
-- @node: def:resolutions
/-- Ceiling of each upper enclosure endpoint, fixed before sampling. -/
def resolutions (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) : ℕ × ℕ :=
  match rankBoxes E N n α β with
  | some (c,s) => ((⌈c.hi⌉ : ℤ).toNat, (⌈s.hi⌉ : ℤ).toNat)
  | none => (1,1)
  -- @realizes k_C(engine and public-name selected numerator rank) @realizes k_S(engine and public-name selected denominator rank)
/-- Exact covariance coordinate statistic at the retained rank. -/
def cHat (n kC : ℕ) (o : Fin n → Record) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, treatment (o i) * outcome (o i) -
    projectionStatistic n kC treatment outcome o -- @realizes \widehat C(exact projected sample covariance)
/-- Exact denominator statistic at the retained rank. -/
def sHat (n kS : ℕ) (o : Fin n → Record) : ℝ :=
  projectionStatistic n kS (fun o => treatment o * (1 - outcome o))
    (fun o => (1 - treatment o) * outcome o) o -- @realizes \widehat S(exact projected sample denominator)
-- @node: def:coordinate-estimates
/-- Both statistics use exactly the previously selected rank pair. -/
def coordinateEstimates (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) : ℝ × ℝ :=
  let k := resolutions E N n α β
  (cHat n k.1 o, sHat n k.2 o)
/-- Public variance radius. -/
def varianceRadius (n k : ℕ) : ℝ := 10 / n + 4 * k / ((n : ℝ) * ((n : ℝ) - 1))
/-- Clipping as literal maximum and minimum. -/
def clip (l u v : ℝ) : ℝ := max l (min u v)
/-- Joint odds inversion with the public effect clipping. -/
def inversion (c d : ℝ) : ℝ :=
  Real.log (clip (Real.exp (-1/2)) (Real.exp (1/2)) (1 + c / d))
/-- The ideal exact-real endpoint expressions. -/
def idealEndpoints (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) : ℝ × ℝ :=
  let k := resolutions E N n α β
  let c := cHat n k.1 o
  let s := sHat n k.2 o
  let bC := 8 * (k.1 : ℝ) ^ (-(α+β)) + Real.sqrt (20 * varianceRadius n k.1)
  let bS := 25 * (k.2 : ℝ) ^ (-2*β) + Real.sqrt (20 * varianceRadius n k.2)
  let sm := clip denominatorFloor 1 (s-bS)
  let sp := clip denominatorFloor 1 (s+bS)
  (min (inversion (c-bC) sm) (inversion (c-bC) sp),
   max (inversion (c+bC) sm) (inversion (c+bC) sp))
/-- Finite expression syntax with matching real and rational-box semantics. -/
inductive BoxExpr where
  | constant : ℚ → BoxExpr
  | input : ℕ → BoxExpr
  | pi : BoxExpr
  | add : BoxExpr → BoxExpr → BoxExpr
  | sub : BoxExpr → BoxExpr → BoxExpr
  | mul : BoxExpr → BoxExpr → BoxExpr
  | div : BoxExpr → BoxExpr → BoxExpr
  | min : BoxExpr → BoxExpr → BoxExpr
  | max : BoxExpr → BoxExpr → BoxExpr
  | exp : BoxExpr → BoxExpr
  | cos : BoxExpr → BoxExpr
  | log : BoxExpr → BoxExpr
  | sqrt : BoxExpr → BoxExpr
  | power : ℕ → BoxExpr → BoxExpr
/-- Exact-real semantics. -/
def BoxExpr.real : BoxExpr → List ℝ → ℝ
  | .constant c, _ => c
  | .input i, xs => xs[i]?.getD 0
  | .pi, _ => Real.pi
  | .add a b, xs => a.real xs + b.real xs
  | .sub a b, xs => a.real xs - b.real xs
  | .mul a b, xs => a.real xs * b.real xs
  | .div a b, xs => a.real xs / b.real xs
  | .min a b, xs => Min.min (a.real xs) (b.real xs)
  | .max a b, xs => Max.max (a.real xs) (b.real xs)
  | .exp a, xs => Real.exp (a.real xs)
  | .cos a, xs => Real.cos (a.real xs)
  | .log a, xs => Real.log (a.real xs)
  | .sqrt a, xs => Real.sqrt (a.real xs)
  | .power b a, xs => (b : ℝ) ^ a.real xs
/-- Literal structural box evaluation with the supplied engine and one precision. -/
def BoxExpr.eval (E : ArithmeticEngine) (q : ℕ) : BoxExpr → List RatInterval → Option RatInterval
  | .constant c, _ => some (RatInterval.point c)
  | .input i, xs => xs[i]?
  | .pi, _ => some (E.piBox q)
  | .add a b, xs => return (← a.eval E q xs).add (← b.eval E q xs)
  | .sub a b, xs => return (← a.eval E q xs).sub (← b.eval E q xs)
  | .mul a b, xs => return (← a.eval E q xs).mul (← b.eval E q xs)
  | .div a b, xs => do boxDiv (← a.eval E q xs) (← b.eval E q xs)
  | .min a b, xs => return boxMin (← a.eval E q xs) (← b.eval E q xs)
  | .max a b, xs => return boxMax (← a.eval E q xs) (← b.eval E q xs)
  | .exp a, xs => return E.expBox q (← a.eval E q xs)
  | .cos a, xs => return E.cosBox q (← a.eval E q xs)
  | .log a, xs => do
      let I ← a.eval E q xs
      if 0 < I.lo then return E.logBox q I else none
  | .sqrt a, xs => do
      let I ← a.eval E q xs
      if 0 ≤ I.lo then return E.sqrtBox q I else none
  | .power b a, xs => do
      let I ← a.eval E q xs
      if 1 ≤ b ∧ -3 ≤ I.lo ∧ I.hi ≤ 3 then return E.powBox q b I else none
/-- A literal finite expression sum. -/
def expressionSum (xs : List BoxExpr) : BoxExpr := xs.foldr BoxExpr.add (.constant 0)
/-- Cosine basis expression at input covariate i. -/
def basisExpression (j i : ℕ) : BoxExpr :=
  if j = 0 then .constant 1 else
    .mul (.sqrt (.constant 2)) (.cos (.mul (.mul .pi (.constant j)) (.input (2+i))))
/-- Projection kernel expression. -/
def kernelExpression (k i j : ℕ) : BoxExpr :=
  expressionSum ((List.range k).map fun l => .mul (basisExpression l i) (basisExpression l j))
/-- The full original-record statistic as a finite expression. -/
def statisticExpression (n k : ℕ) (W V : Fin n → ℚ) : BoxExpr :=
  .mul (.constant (1 / ((n : ℚ) * ((n : ℚ)-1))))
    (expressionSum ((Finset.univ : Finset (Fin n × Fin n)).toList.filter (fun ij => ij.1 ≠ ij.2) |>.map
      fun ij => .mul (kernelExpression k ij.1.val ij.2.val) (.constant (W ij.1 * V ij.2))))
/-- Literal numerator and denominator expressions using exact binary labels. -/
def coordinateExpressions (n kC kS : ℕ) (o : Fin n → Record) : BoxExpr × BoxExpr :=
  let A : Fin n → ℚ := fun i => if (o i).2.1 then 1 else 0
  let Y : Fin n → ℚ := fun i => if (o i).2.2 then 1 else 0
  (.sub (.constant ((n : ℚ)⁻¹ * ∑ i, A i * Y i)) (statisticExpression n kC A Y),
    statisticExpression n kS (fun i => A i * (1-Y i)) (fun i => (1-A i)*Y i))
/-- Literal joint-inversion expression. -/
def inversionExpression (c d : BoxExpr) : BoxExpr :=
  .log (.max (.exp (.constant (-1/2)))
    (.min (.exp (.constant (1/2))) (.add (.constant 1) (.div c d))))
/-- The displayed finite expression tree, retaining the rank-step integers. -/
def endpointExpressions (n kC kS : ℕ) (o : Fin n → Record) : BoxExpr × BoxExpr :=
  let cs := coordinateExpressions n kC kS o
  let bC := BoxExpr.add (.mul (.constant 8) (.power kC (.sub (.constant 0) (.add (.input 0) (.input 1)))))
    (.sqrt (.constant (20 * (10/(n : ℚ)+4*kC/((n : ℚ)*((n : ℚ)-1))))))
  let bS := BoxExpr.add (.mul (.constant 25) (.power kS (.mul (.constant (-2)) (.input 1))))
    (.sqrt (.constant (20 * (10/(n : ℚ)+4*kS/((n : ℚ)*((n : ℚ)-1))))))
  let sm := BoxExpr.max (.constant (1/512)) (.min (.constant 1) (.sub cs.2 bS))
  let sp := BoxExpr.max (.constant (1/512)) (.min (.constant 1) (.add cs.2 bS))
  (.min (inversionExpression (.sub cs.1 bC) sm) (inversionExpression (.sub cs.1 bC) sp),
   .max (inversionExpression (.add cs.1 bC) sm) (inversionExpression (.add cs.1 bC) sp))
/-- Endpoint-step inputs are queried once at the public endpoint precision.
The supplied boxes enter the expression tree directly, without domain narrowing. -/
def endpointInputs (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) (q : ℕ) : Option (List RatInterval) :=
  some (N.alphaName n α β q :: N.betaName n α β q ::
    (List.finRange n).map (fun i => N.covariateName n α β o i q))
/-- Literal endpoint enclosures. -/
def endpointBoxes (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) : Option (RatInterval × RatInterval) := do
  let k := resolutions E N n α β
  let q := qEnd n k.1 k.2
  let xs ← endpointInputs N n α β o q
  let lr := endpointExpressions n k.1 k.2 o
  return (← lr.1.eval E q xs, ← lr.2.eval E q xs)
/-- Outward rational endpoints, with full-box totalization on invalid inputs. -/
def upperRawBox (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) : RatInterval :=
  if n < 2 then fullEffectBox else
    match rankBoxes E N n α β, endpointBoxes E N n α β o with
    | some _, some (L,R) =>
      match boxIntersection (rationalBox L.lo R.hi) fullEffectBox with
      | some I => I
      | none => fullEffectBox
    | _, _ => fullEffectBox
/-- The final intersection or full-box fallback keeps both endpoints in the effect box. [the stated conclusion](goal) holds. -/
-- @node: upperRawBox_subinterval
lemma upperRawBox_subinterval (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ)
    (α β : ℝ) (o : Fin n → Record) :
    (upperRawBox E N n α β o).Subinterval fullEffectBox := by
  unfold upperRawBox
  split
  · exact RatInterval.subinterval_refl _
  · split
    · split
      · exact boxIntersection_subinterval_right _ _ _ ‹_›
      · exact RatInterval.subinterval_refl _
    · exact RatInterval.subinterval_refl _

/-- The totalized rational output always defines a nonempty closed effect interval. [the stated conclusion](goal) holds. -/
-- @node: upperRawBox_valid
lemma upperRawBox_valid (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) :
  IntervalDataValid ((upperRawBox E N n α β o).lo, (upperRawBox E N n α β o).hi, true, true) := by
  have hBounds := upperRawBox_subinterval E N n α β o
  have hlo : (fullEffectBox.lo : ℝ) ≤ (upperRawBox E N n α β o).lo := by
    exact_mod_cast hBounds.1
  have hhi : ((upperRawBox E N n α β o).hi : ℝ) ≤ fullEffectBox.hi := by
    exact_mod_cast hBounds.2
  norm_num [fullEffectBox, rationalBox] at hlo hhi
  have hOrder : ((upperRawBox E N n α β o).lo : ℝ) ≤
      (upperRawBox E N n α β o).hi := by
    exact_mod_cast (upperRawBox E N n α β o).lo_le_hi
  dsimp [IntervalDataValid]
  refine ⟨?_, ?_, ?_⟩
  · exact hlo
  · exact hhi
  · rcases lt_or_eq_of_le hOrder with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, rfl, rfl⟩
/-- Closed interval carrier for the literal rational output. -/
def upperOutput (E : ArithmeticEngine) (N : NamingPolicy) (n : ℕ) (α β : ℝ) (o : Fin n → Record) : EffectInterval :=
  ⟨((upperRawBox E N n α β o).lo, (upperRawBox E N n α β o).hi, true, true), upperRawBox_valid E N n α β o⟩
/-- A finite response code determines every subsequent rational computation. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hlabels,hnames). -/
-- @node: upperRawBox_response_congr
lemma upperRawBox_response_congr (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (α β : ℝ) (o o' : Fin n → Record)
    (hlabels : ∀ i, (o i).2 = (o' i).2)
    (hnames : ∀ i, N.covariateName n α β o i
        (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) =
      N.covariateName n α β o' i
        (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2)) :
    upperRawBox E N n α β o = upperRawBox E N n α β o' := by
  have hinputs : endpointInputs N n α β o
      (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) =
      endpointInputs N n α β o'
      (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) := by
    unfold endpointInputs
    simp_rw [hnames]
  have hexprs : endpointExpressions n (resolutions E N n α β).1
      (resolutions E N n α β).2 o =
      endpointExpressions n (resolutions E N n α β).1
      (resolutions E N n α β).2 o' := by
    unfold endpointExpressions coordinateExpressions
    simp_rw [hlabels]
  unfold upperRawBox endpointBoxes
  dsimp only
  rw [hinputs, hexprs]

/-- Any union of fibers of a measurable countable response code is measurable. Under the stated assumptions. [The stated hypotheses](hyp:hcode,houtput) hold, and [the stated conclusion follows](goal). -/
-- @node: countable_response_preimage
lemma countable_response_preimage {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    {code : A → B} {output : A → C} (hcode : Measurable code)
    (houtput : ∀ a a', code a = code a' → output a = output a') (s : Set C) :
    MeasurableSet (output ⁻¹' s) := by
  have hfibers : output ⁻¹' s =
      ⋃ b ∈ {b | ∃ a, code a = b ∧ output a ∈ s}, code ⁻¹' {b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro ha
      exact ⟨code a, ⟨a, rfl, ha⟩, rfl⟩
    · rintro ⟨b, ⟨a', ha', hs⟩, ha⟩
      rw [houtput a a' (ha.trans ha'.symm)]
      exact hs
  rw [hfibers]
  exact MeasurableSet.biUnion (Set.to_countable _) fun b _ =>
    hcode (measurableSet_singleton b)

/-- [Borelness follows from finite rational computations and the Borel supplied policy.](goal) Under [the stated assumptions](hyp:hN). -/
-- @node: upperOutput_regular
lemma upperOutput_regular (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (α β : ℝ) :
  Measurable (fun ω : Experiment n => upperOutput E N n α β ω.1) ∧
  (∀ t : ℝ, MeasurableSet {ω : Experiment n | t ∈ intervalSet (upperOutput E N n α β ω.1)}) ∧
  Measurable (fun ω : Experiment n => intervalLength (upperOutput E N n α β ω.1)) := by
  let q := qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2
  let code : Experiment n → Fin n → (Bool × Bool) × (ℚ × ℚ) := fun ω i =>
    ((ω.1 i).2, (N.covariateName n α β ω.1 i q).lo,
      (N.covariateName n α β ω.1 i q).hi)
  have hcode : Measurable code := by
    apply measurable_pi_lambda
    intro i
    have hlabels : Measurable (fun ω : Experiment n => (ω.1 i).2) := by
      fun_prop
    have hnames : Measurable (fun ω : Experiment n =>
        ((N.covariateName n α β ω.1 i q).lo,
          (N.covariateName n α β ω.1 i q).hi)) := by
      exact (hN.2.2.2 n i q).comp ((measurable_const (a := (α, β))).prodMk measurable_fst)
    exact hlabels.prodMk hnames
  have houtput : ∀ ω ω' : Experiment n, code ω = code ω' →
      upperOutput E N n α β ω.1 = upperOutput E N n α β ω'.1 := by
    intro ω ω' heq
    have hi (i : Fin n) := congrFun heq i
    have hraw : upperRawBox E N n α β ω.1 = upperRawBox E N n α β ω'.1 := by
      apply upperRawBox_response_congr
      · intro i
        exact congrArg Prod.fst (hi i)
      · intro i
        apply RatInterval.ext
        · exact congrArg (fun v => v.2.1) (hi i)
        · exact congrArg (fun v => v.2.2) (hi i)
    apply Subtype.ext
    simp only [upperOutput, hraw]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact countable_response_preimage hcode houtput s
  · intro t
    exact countable_response_preimage hcode houtput {B | t ∈ intervalSet B}
  · intro s hs
    exact countable_response_preimage hcode
      (fun ω ω' h => congrArg intervalLength (houtput ω ω' h)) s
/-- The literal represented algorithm, with no radius or nuisance input. -/
def upperInterval (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (α β : ℝ) : Procedure n where
  output := fun ω => upperOutput E N n α β ω.1 -- @realizes I^{\mathrm{up}}(literal radius-independent rational output)
  borel := (upperOutput_regular E N hN n α β).1
  coverage_measurable := (upperOutput_regular E N hN n α β).2.1
  length_measurable := (upperOutput_regular E N hN n α β).2.2
-- @node: def:upper-handle
/-- Canonical upper handle for the literal fixed-budget represented procedure. -/
def upperHandle (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β : ℝ) : Procedure n :=
  upperInterval E N hN n α β
/-- Sharp profile candidate, defined independently of the engine and policy. -/
def rate : ℕ → ℝ → ℝ → ℝ → ℝ := diagnosticEnvelope -- @realizes \rho(diagnostic profile)
-- @node: def:frontier-handle
/-- The rate and the actual supplied-engine interval family. -/
def frontierHandle (E : ArithmeticEngine) (N : NamingPolicy) (hN : N.Admissible) :
    (ℕ → ℝ → ℝ → ℝ → ℝ) × ((n : ℕ) → ℝ → ℝ → Procedure n) :=
  (rate, upperInterval E N hN) -- @realizes I^\star(supplied-engine upper interval)
end CausalSmith.Stat.LogoddsLowsmoothFrontier
