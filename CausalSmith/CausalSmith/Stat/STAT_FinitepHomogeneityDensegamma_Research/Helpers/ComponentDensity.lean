module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentAugmentation

/-! Finite-moment homogeneity testing: Helpers/ComponentDensity. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Use the histogram interval index, assigning the right endpoint to the last interval. This statement assumes [the K parameter](hyp:K), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def fineIndex (K : ℕ) (x : unitInterval) : ℕ := min (K-1) (Nat.floor ((K:ℝ)*(x:ℝ)))
/-- Neighbouring occupied fine intervals join through an undisclosed coefficient. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the aug parameter](hyp:aug), [the i parameter](hyp:i), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def componentEdge (n K M : ℕ) (aug : Augmentation n K) (i j : Fin n) : Prop :=
  fineIndex M (aug.1 i) = fineIndex M (aug.1 j) ∧
  (fineIndex K (aug.1 i) = fineIndex K (aug.1 j) ∨
    ((fineIndex K (aug.1 i)+1=fineIndex K (aug.1 j) ∨ fineIndex K (aug.1 j)+1=fineIndex K (aug.1 i)) ∧
      max (fineIndex K (aug.1 i)) (fineIndex K (aug.1 j))*M % K ≠ 0))
/-- A component contains all observations connected by occupied neighbouring fine intervals sharing an undisclosed coefficient. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the aug parameter](hyp:aug), [the i parameter](hyp:i). [This is the stated defined object](goal). -/
def componentOf (n K M : ℕ) (aug : Augmentation n K) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen (componentEdge n K M aug) i j)
/-- Collect distinct observation components of the complete augmented design. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def components (n K M : ℕ) (aug : Augmentation n K) : Finset (Finset (Fin n)) :=
  Finset.univ.image (componentOf n K M aug)
/-- The component is contained within one coarse-sign pair. This statement assumes [the M parameter](hyp:M), [the aug parameter](hyp:aug), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
def pairIndex {n K : ℕ} (M : ℕ) (aug : Augmentation n K) (C : Finset (Fin n)) : ℕ :=
  C.sup (fun i => fineIndex M (aug.1 i)/2)
/-- Average the complete finite-label likelihood over undisclosed coefficient pairs with a fixed coarse sign. This statement assumes [the ν parameter](hyp:ν), [the sign parameter](hyp:sign), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def componentDensity (ν sign : Bool) (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ pairs : CoefficientPairs K,
    conditionalPairWeight ν K M (fun _ => sign) aug.2.2 pairs *
    ∏ i ∈ C, labelDensity ν K M a u ((fun _ => sign),pairs) (aug.1 i) (aug.2.1 i) (labels i)
/-- The null component density averages the uncoupled coefficient law. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
def nullComponent (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) : Labels n → ℝ :=
  componentDensity false false n K M a u aug C
/-- The intermediate component density averages both values of its undisclosed coarse sign. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def averageComponent (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentDensity true true n K M a u aug C labels+componentDensity true false n K M a u aug C labels)/2
/-- The even discrepancy subtracts the actual null density from the sign-averaged component density. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def evenDiscrepancy (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  averageComponent n K M a u aug C labels-nullComponent n K M a u aug C labels
/-- The odd discrepancy is half the difference of the two coarse-sign component densities. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def oddDiscrepancy (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentDensity true true n K M a u aug C labels-componentDensity true false n K M a u aug C labels)/2
/-- Average squared even discrepancy divided by the actual null component density over every fair label. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
def componentEvenActivity (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) : ℝ :=
  (4:ℝ)^(-(n:ℤ))*∑ labels : Labels n, evenDiscrepancy n K M a u aug C labels^2/nullComponent n K M a u aug C labels
/-- Average squared odd discrepancy divided by the intermediate component density over every fair label. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
def componentOddActivity (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) : ℝ :=
  (4:ℝ)^(-(n:ℤ))*∑ labels : Labels n, oddDiscrepancy n K M a u aug C labels^2/averageComponent n K M a u aug C labels
/-- Multiply the normalized independent sign-averaged component densities. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def intermediateDensity (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (labels : Labels n) : ℝ :=
  ∏ C ∈ components n K M aug, averageComponent n K M a u aug C labels
/-- Multiply the actual independent null component densities. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def nullConditionalDensity (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (labels : Labels n) : ℝ :=
  ∏ C ∈ components n K M aug, nullComponent n K M a u aug C labels
/-- Average all complete label likelihoods over both undisclosed coefficients and coarse signs. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def alternativeConditionalDensity (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) (labels : Labels n) : ℝ :=
  (2:ℝ)^(-(M/2:ℤ))*∑ σ : Fin (M/2) → Bool,
    ∑ pairs : CoefficientPairs K, conditionalPairWeight true K M σ aug.2.2 pairs *
      ∏ i : Fin n, labelDensity true K M a u (σ,pairs) (aug.1 i) (aug.2.1 i) (labels i)
/-- The explicit intermediate law is the fair-label measure of the product component density. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def intermediateConditionalLaw (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) : Measure (Labels n) := fairLabelMeasure n (intermediateDensity n K M a u aug)
/-- The null conditional law retains the full actual null-mixture denominator. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def nullConditionalLaw (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) : Measure (Labels n) := fairLabelMeasure n (nullConditionalDensity n K M a u aug)
/-- The alternative conditional law integrates every latent coefficient and coarse sign. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def alternativeConditionalLaw (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) : Measure (Labels n) := fairLabelMeasure n (alternativeConditionalDensity n K M a u aug)
/-- The first conditional activity is the sum of component even chi-square activities. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def activityA (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) : ℝ :=
  ∑ C ∈ components n K M aug, componentEvenActivity n K M a u aug C
/-- The second conditional activity pairs distinct odd components sharing a coarse sign, with no diagonal terms. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug). [This is the stated defined object](goal). -/
def activityB (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K) : ℝ :=
  (∑ C ∈ components n K M aug, ∑ C' ∈ components n K M aug,
    if C ≠ C' ∧ pairIndex M aug C = pairIndex M aug C' then
      componentOddActivity n K M a u aug C*componentOddActivity n K M a u aug C' else 0)/2

end CausalSmith.Stat.FinitepHomogeneityDensegamma
