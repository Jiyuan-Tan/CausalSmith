module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Experiment
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Projection

/-!
# Estimator

Two-channel point-CATE annotation frontier: Estimator
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


variable {d n m : ℕ}
/-- Given [the specified input D](hyp:D), [treatment records](goal) is the corresponding construction. -/
def treatmentRecords (D : Dataset d n m) : Fin (n+m) → Cov d × Bool :=
  Fin.addCases (fun i => ((D.1 i).1, (D.1 i).2.1)) D.2 -- @realizes DT(concatenated records) @realizes XT(first coordinate) @realizes AT(second coordinate) @realizes i(treatment index)
/-- Given [the specified input n](hyp:n), [outcome count](goal) is the corresponding construction. -/
def outcomeCount (n : ℕ) : ℕ := n/2 -- @realizes ell(outcome-role count)
/-- Given [the specified input n](hyp:n), [the specified input m](hyp:m), [treatment count](goal) is the corresponding construction. -/
def treatmentCount (n m : ℕ) : ℕ := n+m-n/2 -- @realizes t(treatment-role count)
-- @node: def:roles
/-- Given [the specified input n](hyp:n), [the specified input m](hyp:m), [role split](goal) is the corresponding construction. -/
def roleSplit (n m : ℕ) : Finset (Fin n) × Finset (Fin (n+m)) :=
  (Finset.univ.filter (fun j => j.val < n/2), -- @realizes IL(outcome indices) @realizes j(outcome index)
   Finset.univ.filter (fun i => n/2 ≤ i.val)) -- @realizes IT(treatment indices)
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input x](hyp:x), [eta hat](goal) is the corresponding construction. -/
def etaHat (D : Dataset d n m) (h : ℝ) (J : ℕ) (x : Cov d) : ℝ :=
  if x ∈ locCube d h then (outcomeCount n : ℝ)⁻¹ *
    ∑ j ∈ (roleSplit n m).1, locWeight h (D.1 j).1 * fineKernel d h J x (D.1 j).1 * bit (D.1 j).2.2
  else 0 -- @realizes etahat(observed outcome projection)
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [r hat](goal) is the corresponding construction. -/
def rHat (D : Dataset d n m) (h : ℝ) (J : ℕ) (u : PolyIdx d) : ℝ :=
  (outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1,
    locWeight h (D.1 j).1 * coarseBasis h (D.1 j).1 u * bit (D.1 j).2.1 * bit (D.1 j).2.2 -
  (treatmentCount n m : ℝ)⁻¹ * ∑ i ∈ (roleSplit n m).2,
    locWeight h (treatmentRecords D i).1 * coarseBasis h (treatmentRecords D i).1 u *
      bit (treatmentRecords D i).2 * etaHat D h J (treatmentRecords D i).1 -- @realizes Rhat(rectangular moment vector)
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the specified input v](hyp:v), [q raw](goal) is the corresponding construction. -/
def qRaw (D : Dataset d n m) (h : ℝ) (J : ℕ) (u v : PolyIdx d) : ℝ :=
  (outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1,
    locWeight h (D.1 j).1 * coarseBasis h (D.1 j).1 u * coarseBasis h (D.1 j).1 v * bit (D.1 j).2.1 -
  ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
    ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
      locWeight h (treatmentRecords D i).1 * locWeight h (D.1 j).1 *
      coarseBasis h (treatmentRecords D i).1 u * coarseBasis h (D.1 j).1 v *
      bit (treatmentRecords D i).2 * bit (D.1 j).2.1 * fineKernel d h J (treatmentRecords D i).1 (D.1 j).1 -- @realizes Qraw(raw rectangular matrix)
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [q hat](goal) is the corresponding construction. -/
def qHat (D : Dataset d n m) (h : ℝ) (J : ℕ) : Matrix (PolyIdx d) (PolyIdx d) ℝ :=
  fun u v => (qRaw D h J u v + qRaw D h J v u)/2 -- @realizes Qhat(symmetrized matrix)
-- @node: def:moments
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [rect moments](goal) is the corresponding construction. -/
def rectMoments (D : Dataset d n m) (h : ℝ) (J : ℕ) :
    (PolyIdx d → ℝ) × Matrix (PolyIdx d) (PolyIdx d) ℝ := (rHat D h J, qHat D h J)
/-- Given [the specified input P](hyp:P), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [q pop](goal) is the corresponding construction. -/
def qPop (P : PrimitiveLaw d) (n m : ℕ) (h : ℝ) (J : ℕ) : Matrix (PolyIdx d) (PolyIdx d) ℝ :=
  fun u v => ∫ w, qHat w.1 h J u v ∂experiment P n m -- @realizes Q(population expectation)
/-- Given [the specified input P](hyp:P), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [r bar](goal) is the corresponding construction. -/
def rBar (P : PrimitiveLaw d) (n m : ℕ) (h : ℝ) (J : ℕ) (u : PolyIdx d) : ℝ :=
  ∫ w, rHat w.1 h J u ∂experiment P n m
/-- Given [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the r hat rectangular conclusion](goal) holds. -/
lemma rHat_rectangular (D : Dataset d n m) (h : ℝ) (J : ℕ) (u : PolyIdx d) :
    rHat D h J u = (outcomeCount n : ℝ)⁻¹ * ∑ j ∈ (roleSplit n m).1,
      locWeight h (D.1 j).1 * coarseBasis h (D.1 j).1 u * bit (D.1 j).2.1 * bit (D.1 j).2.2 -
    ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
      ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
        locWeight h (treatmentRecords D i).1 * locWeight h (D.1 j).1 *
        coarseBasis h (treatmentRecords D i).1 u * bit (treatmentRecords D i).2 *
        fineKernel d h J (treatmentRecords D i).1 (D.1 j).1 * bit (D.1 j).2.2 := by
  unfold rHat
  congr 1
  rw [mul_inv_rev]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : (treatmentRecords D i).1 ∈ locCube d h
  · simp only [etaHat, if_pos hx]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp [etaHat, hx, locWeight]


/-- Given [the specified input Q](hyp:Q), [lambda min](goal) is the corresponding construction. -/
def lambdaMin (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ) : ℝ :=
  sInf {c | ∃ v : PolyIdx d → ℝ, (∑ u, v u^2) = 1 ∧ c = ∑ u, v u * (Q.mulVec v) u}
/-- [Clipping to the effect range](goal): [a real number x](hyp:x) is truncated to the interval from −1 to 1, the range of a difference of two probabilities. -/
def clip (x : ℝ) : ℝ := max (-1) (min 1 x)
/-- [The Gram guard level](goal) for [the overlap level eps](hyp:eps): half of eps·(1 − eps), the smallest value of e·(1 − e) when the propensity e lies between eps and 1 − eps. -/
def gramGuard (eps : ℝ) : ℝ := eps * (1 - eps) / 2

/-- For [an overlap level eps](hyp:eps) that is [positive](hyp:heps) and [below one](hyp:heps1), [the Gram guard level is positive](goal). -/
lemma gramGuard_pos {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) : 0 < gramGuard eps := by
  unfold gramGuard
  have : 0 < 1 - eps := by linarith
  positivity

/-- Under [the public parameter domain](hyp:hdom), [the Gram guard level is positive](goal) for [the overlap level eps](hyp:eps). -/
lemma PublicDomain.gramGuard_pos {d : ℕ} {alpha beta gamma L eps : ℝ}
    (hdom : PublicDomain d alpha beta gamma L eps) : 0 < gramGuard eps :=
  CausalSmith.Stat.TwosamplePointcateAnnotationFrontier.gramGuard_pos hdom.2.2.2.2.2.2.2.2.1 (by linarith [hdom.2.2.2.2.2.2.2.2.2])

-- @node: def:estimator
/-- Given [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input D](hyp:D), [t hat](goal) is the corresponding construction: the clipped local-polynomial estimate when the smallest Rayleigh quotient of the empirical Gram matrix is at least the Gram guard level of eps, and zero otherwise. -/
def tHat (eps h : ℝ) (J : ℕ) (D : Dataset d n m) : ℝ :=
  if gramGuard eps ≤ lambdaMin (qHat D h J) then
    clip (∑ u, r0 d h u * ((qHat D h J)⁻¹.mulVec (rHat D h J)) u)
  else 0 -- @realizes That(clipped eigenvalue-guarded decision)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [h star](goal) is the corresponding construction. -/
def hStar (d : ℕ) (alpha beta gamma : ℝ) (n m : ℕ) : ℝ :=
  (1/2) * max ((n:ℝ)^(-(1/(2*gamma+d))))
    (((n:ℝ)*((n:ℝ)+m))^(-(1/bigDelta d alpha beta gamma))) -- @realizes hstar(tuned bandwidth)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [j star](goal) is the corresponding construction. -/
def jStar (d : ℕ) (alpha beta gamma : ℝ) (n m : ℕ) : ℕ :=
  Nat.ceil ((hStar d alpha beta gamma n m)^(-(max 0 (gamma/(alpha+beta)-1)))) -- @realizes Jstar(tuned grid)
-- @node: def:tuning
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the overlap level eps](hyp:eps), [t up](goal) is the corresponding construction. -/
def tUp (d : ℕ) (alpha beta gamma eps : ℝ) (n m : ℕ) (D : Dataset d n m) : ℝ :=
  tHat eps (hStar d alpha beta gamma n m) (jStar d alpha beta gamma n m) D -- @realizes Tup(tuned upper decision)
-- @node: def:sharp-decision
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [the overlap level eps](hyp:eps), [sharp decision](goal) is the corresponding construction. -/
def sharpDecision (d : ℕ) (alpha beta gamma eps : ℝ) (n m : ℕ) (w : Sample d n m) : ℝ :=
  tUp d alpha beta gamma eps n m w.1 -- @realizes Tstar(total data-only decision)
-- @node: def:frontier-handle
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the overlap level eps](hyp:eps), [frontier handle](goal) is the corresponding construction. -/
def frontierHandle (d : ℕ) (alpha beta gamma eps : ℝ) (n m : ℕ) : ℝ × (Sample d n m → ℝ) :=
  (sharpRate d alpha beta gamma n m, sharpDecision d alpha beta gamma eps n m) -- @realizes frontierHandle(rate-decision program)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
