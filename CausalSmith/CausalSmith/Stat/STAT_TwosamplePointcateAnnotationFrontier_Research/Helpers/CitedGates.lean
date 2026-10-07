module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.Hellinger
public import Causalean.Stat.Minimax.AbsoluteFuzzyTesting

/-!
# Helpers/CitedGates

Two-channel point-CATE annotation frontier: Helpers/CitedGates
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


-- @node: lem:published-fuzzy-testing
/-- Kennedy, Balakrishnan, Robins and Wasserman (2024), Section 3, Lemma 1,
absolute-loss specialization; citation handle cite:kennedybalakrishnanrobinswasserman2024-lemma1.
Source: https://arxiv.org/html/2203.00837v4#Thmlemma1.
This follows from the sharp absolute fuzzy-testing bound, applied to the two
kernel ranges inside the ambient model.  [the published fuzzy testing conclusion](goal) holds. -/
lemma PublishedFuzzyTesting :
  ∀ (Ω Z : Type) [MeasurableSpace Ω] [MeasurableSpace Z]
    (ω : Measure Z) [IsProbabilityMeasure ω] (B C : Kernel Z Ω)
    [IsMarkovKernel B] [IsMarkovKernel C] (v0 : ℕ), 1 ≤ v0 →
    ∀ (Model : Set (Measure Ω)), (∀ z, B z ∈ Model) → (∀ z, C z ∈ Model) →
    ∀ (Ψ : Measure Ω → ℝ) (s0 u0 : ℝ), 0 < s0 → 0 ≤ u0 → u0 < 2 →
    (∀ z z', s0 ≤ Ψ (B z) - Ψ (C z')) →
    hellingerSq (ω.bind (fun z => Measure.pi (fun _ : Fin v0 => B z)))
      (ω.bind (fun z => Measure.pi (fun _ : Fin v0 => C z))) ≤ u0 →
    ∀ (est : (Fin v0 → Ω) → ℝ), Measurable est →
      ENNReal.ofReal ((s0/4)*(1-Real.sqrt (u0*(1-u0/4)))) ≤
        ⨆ (P : Measure Ω) (_ : P ∈ Model),
          ∫⁻ w, ENNReal.ofReal |est w - Ψ P| ∂Measure.pi (fun _ : Fin v0 => P) := by
  intro Ω Z _ _ ω _ B C _ _ v0 _ Model hB hC Ψ s0 u0 hs hu hu2 hsep hhell est hest
  let M : Set (Measure Ω) := Set.range B ∪ Set.range C
  have hM : ∀ P ∈ M, IsProbabilityMeasure P := by
    intro P hP
    rcases hP with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;> infer_instance
  have htest := Causalean.Stat.Minimax.absolute_fuzzy_testing_lower_bound_iid
    v0 ω B C M Ψ
    (fun z => Set.mem_union_left _ ⟨z, rfl⟩)
    (fun z => Set.mem_union_right _ ⟨z, rfl⟩)
    hs hu hu2 hsep hhell hest
  apply htest.trans
  apply iSup_le
  intro P
  have hP : P.1 ∈ Model := by
    rcases P.2 with ⟨z, hz⟩ | ⟨z, hz⟩
    · rw [← hz]
      exact hB z
    · rw [← hz]
      exact hC z
  exact le_iSup_of_le P.1 (le_iSup_of_le hP le_rfl)

/-- The numerical rate and smoothness split displayed in the published point-CATE benchmark.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [kbrw benchmark rate](goal) is the corresponding construction. -/
def kbrwBenchmarkRate (d : ℕ) (alpha beta gamma : ℝ) (n : ℕ) : ℝ :=
  if (alpha+beta)/2 < ((d:ℝ)/4)/(1+(d:ℝ)/(2*gamma)) then
    (n:ℝ)^(-(1/(1+(d:ℝ)/(2*gamma)+(d:ℝ)/(4*((alpha+beta)/2)))))
  else (n:ℝ)^(-(1/(2+(d:ℝ)/gamma)))

/-- Kennedy, Balakrishnan, Robins and Wasserman (2024), Section 3, Theorem 1:
only the numerical exponents and smoothness cutoff at nuisance-average smoothness.
Citation handle cite:kennedybalakrishnanrobinswasserman2024-theorem1;
source https://arxiv.org/html/2203.00837v4#Thmtheorem1.
This disclosed logical input asserts no source-model risk guarantee or minimax transfer.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [published cate benchmark](goal) is the corresponding construction. -/
def PublishedCateBenchmark (d : ℕ) (alpha beta gamma : ℝ) : Sort 0 :=
  1 ≤ d → 0 < alpha → 0 < beta → 1 ≤ gamma →
    (1/(1+(d:ℝ)/(2*gamma)+(d:ℝ)/(4*((alpha+beta)/2))) =
      2*gamma/(2*gamma+(d:ℝ)+gamma*(d:ℝ)/(alpha+beta))) ∧
    (1/(2+(d:ℝ)/gamma) = gamma/(2*gamma+(d:ℝ))) ∧
    ((alpha+beta)/2 < ((d:ℝ)/4)/(1+(d:ℝ)/(2*gamma)) ↔
      alpha+beta < gamma*(d:ℝ)/(2*gamma+(d:ℝ))) ∧
    (∀ n : ℕ, 2 ≤ n → kbrwBenchmarkRate d alpha beta gamma n =
      max ((n:ℝ)^(-(gamma/(2*gamma+(d:ℝ)))))
        ((n:ℝ)^(-(2*gamma/(2*gamma+(d:ℝ)+gamma*(d:ℝ)/(alpha+beta))))))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
