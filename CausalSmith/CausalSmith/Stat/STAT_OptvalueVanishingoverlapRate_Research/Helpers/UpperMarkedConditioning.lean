module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullMarked
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Averaging fixed-pilot bounds in the implemented experiment

The actual pilot and evaluation vectors are independent. Their joint law
and Fubini decomposition justify freezing the pilot in roadmap (26)–(28),
then averaging the resulting cell loss bounds.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal


-- @node: markedPoissonCellCounts
/-- The four actual counts of a cell with a specified pilot/evaluation mark.
For the displayed parameters, markedPoissonCellCounts is the object specified by this definition. -/
def markedPoissonCellCounts {d : ℕ} (a : Bool) (x : Fin d)
    (s : FiniteSample (Obs d × Bool)) : Fin 4 → ℕ :=
  markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) a x
/-- Either actual count vector is measurable. The [stated conclusion](goal) holds. -/
-- @node: markedPoissonCellCounts_measurable
@[fun_prop]
lemma markedPoissonCellCounts_measurable {d : ℕ} (a : Bool) (x : Fin d) :
    Measurable (markedPoissonCellCounts a x) := by
  exact measurable_pi_lambda _ (fun j => markedPoissonCount_measurable d a x j)

-- @node: markedPoissonCellCounts_pilot_indep_evaluation
/-- The pilot and evaluation vectors of the same cell depend on disjoint marked atoms, so freezing the entire pilot preserves the evaluation law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_pilot_indep_evaluation {d : ℕ}
    (P : DiscreteLaw d) (n : ℕ) (x : Fin d) :
    IndepFun (markedPoissonCellCounts true x) (markedPoissonCellCounts false x)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  classical
  let atoms (a : Bool) : Finset (Obs d × Bool) :=
    Finset.univ.filter (fun z => z.1.1 = x ∧ z.2 = a)
  let atom (a : Bool) (j : Fin 4) : atoms a :=
    ⟨((x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)), a), by simp [atoms]⟩
  let F (a : Bool) (v : atoms a → ℕ) : Fin 4 → ℕ := fun j => v (atom a j)
  have heq (a : Bool) : markedPoissonCellCounts a x =
      F a ∘ (fun s z => markedPoissonHistogram s (z : Obs d × Bool)) := by
    funext s j
    exact markedCount_eq_markedPoissonHistogram s a x j
  have hdis : Disjoint (atoms true) (atoms false) := by
    apply Finset.disjoint_left.2
    intro z ht hf
    simp only [atoms, Finset.mem_filter, Finset.mem_univ, true_and] at ht hf
    exact Bool.noConfusion (ht.2.symm.trans hf.2)
  rw [heq true, heq false]
  exact ((markedPoissonHistogram_iIndepFun P n).indepFun_finset
    (atoms true) (atoms false) hdis (fun z =>
      (measurable_pi_apply z).comp (markedPoissonHistogram_measurable d))).comp
    (Measurable.of_discrete (f := F true)) (Measurable.of_discrete (f := F false))


-- @node: markedPoissonCellCounts_hasLaw
/-- The law of either actual cell vector is the same fourfold Poisson product. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_hasLaw {d : ℕ} (P : DiscreteLaw d)
    (n : ℕ) (a : Bool) (x : Fin d) :
    HasLaw (markedPoissonCellCounts a x)
      (Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
        (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal)))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  apply iIndepFun.hasLaw_pi (fun j => markedCount_poisson_hasLaw P n a x j)
  cases a
  · exact markedPoissonEvaluation_iIndepFun P n x
  · exact markedPoissonPilot_iIndepFun P n x


-- @node: markedPoissonCellCounts_pair_hasLaw
/-- The joint law needed to average the fixed-pilot clipping bounds is a product, with no conditional-law assumption left to discharge. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_pair_hasLaw {d : ℕ} (P : DiscreteLaw d)
    (n : ℕ) (x : Fin d) :
    let ν := Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
      (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
    HasLaw (fun s => (markedPoissonCellCounts true x s,
      markedPoissonCellCounts false x s)) (ν.prod ν)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  exact (markedPoissonCellCounts_pilot_indep_evaluation P n x).hasLaw_prod
    (markedPoissonCellCounts_hasLaw P n true x)
    (markedPoissonCellCounts_hasLaw P n false x)


-- @node: markedPoissonCellCounts_integral_freeze_pilot
/-- Integrating any integrable function of the actual two count vectors is exactly averaging its fixed-pilot evaluation integral against the pilot law. This applies to the good-pilot first and squared losses in (28). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_integral_freeze_pilot {d : ℕ}
    (P : DiscreteLaw d) (n : ℕ) (x : Fin d)
    (f : (Fin 4 → ℕ) × (Fin 4 → ℕ) → ℝ)
    (hf : Integrable (fun s => f (markedPoissonCellCounts true x s,
      markedPoissonCellCounts false x s))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    let ν := Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
      (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
    (∫ s, f (markedPoissonCellCounts true x s, markedPoissonCellCounts false x s) ∂μ) =
      ∫ v, ∫ s, f (v, markedPoissonCellCounts false x s) ∂μ ∂ν := by
  dsimp only
  let ν := Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
    (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
  have hpair := markedPoissonCellCounts_pair_hasLaw P n x
  have hmeas : StronglyMeasurable f := (Measurable.of_discrete).stronglyMeasurable
  have hprod : Integrable f (ν.prod ν) := by
    rw [← hpair.map_eq]
    exact (integrable_map_measure hmeas.aestronglyMeasurable hpair.aemeasurable).2 hf
  calc
    _ = ∫ v, f v ∂(ν.prod ν) := hpair.integral_comp hmeas.aestronglyMeasurable
    _ = ∫ v, ∫ w, f (v, w) ∂ν ∂ν := integral_prod f hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with v
      exact ((markedPoissonCellCounts_hasLaw P n false x).integral_comp
        (Measurable.of_discrete.stronglyMeasurable.aestronglyMeasurable)).symm


-- @node: markedPoissonCellCounts_integral_le_of_fixedPilot
/-- A nonnegative fixed-pilot loss bound averages to the corresponding bound for the actual marked experiment. Integrability of the pilot envelope is transported by its proved count law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf,hg,hfnonneg,hfixed), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_integral_le_of_fixedPilot {d : ℕ}
    (P : DiscreteLaw d) (n : ℕ) (x : Fin d)
    (f : (Fin 4 → ℕ) × (Fin 4 → ℕ) → ℝ) (g : (Fin 4 → ℕ) → ℝ)
    (hf : Integrable (fun s => f (markedPoissonCellCounts true x s,
      markedPoissonCellCounts false x s))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)))
    (hg : Integrable (fun s => g (markedPoissonCellCounts true x s))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)))
    (hfnonneg : ∀ v, 0 ≤ f v)
    (hfixed : ∀ v, (∫ s, f (v, markedPoissonCellCounts false x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) ≤ g v) :
    (∫ s, f (markedPoissonCellCounts true x s, markedPoissonCellCounts false x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) ≤
    ∫ s, g (markedPoissonCellCounts true x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4) := by
  let ν := Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
    (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
  have hlaw := markedPoissonCellCounts_hasLaw P n true x
  have hgm : StronglyMeasurable g := Measurable.of_discrete.stronglyMeasurable
  have hgi : Integrable g ν := by
    dsimp only [ν]
    rw [← hlaw.map_eq]
    exact (integrable_map_measure hgm.aestronglyMeasurable hlaw.aemeasurable).2 hg
  rw [markedPoissonCellCounts_integral_freeze_pilot P n x f hf]
  calc
    _ ≤ ∫ v, g v ∂ν := integral_mono_of_nonneg
      (ae_of_all ν (fun v => integral_nonneg (fun s => hfnonneg _)))
      hgi (ae_of_all ν hfixed)
    _ = _ := (hlaw.integral_comp hgm.aestronglyMeasurable).symm


-- @node: markedPoissonCellCounts_abs_integral_le_of_fixedPilot
/-- A fixed-pilot absolute bias bound averages to the corresponding bound for the actual marked experiment. Integrability of the pilot envelope is transported by its proved count law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf,hg,hfixed), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellCounts_abs_integral_le_of_fixedPilot {d : ℕ}
    (P : DiscreteLaw d) (n : ℕ) (x : Fin d)
    (f : (Fin 4 → ℕ) × (Fin 4 → ℕ) → ℝ) (g : (Fin 4 → ℕ) → ℝ)
    (hf : Integrable (fun s => f (markedPoissonCellCounts true x s,
      markedPoissonCellCounts false x s))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)))
    (hg : Integrable (fun s => g (markedPoissonCellCounts true x s))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)))
    (hfixed : ∀ v, |∫ s, f (v, markedPoissonCellCounts false x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)| ≤ g v) :
    |∫ s, f (markedPoissonCellCounts true x s, markedPoissonCellCounts false x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)| ≤
    ∫ s, g (markedPoissonCellCounts true x s)
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4) := by
  let ν := Measure.pi (fun j : Fin 4 => poissonMeasure (((n : ℝ≥0) / 8) *
    (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
  have hlaw := markedPoissonCellCounts_hasLaw P n true x
  have hgm : StronglyMeasurable g := Measurable.of_discrete.stronglyMeasurable
  have hgi : Integrable g ν := by
    dsimp only [ν]
    rw [← hlaw.map_eq]
    exact (integrable_map_measure hgm.aestronglyMeasurable hlaw.aemeasurable).2 hg
  rw [markedPoissonCellCounts_integral_freeze_pilot P n x f hf]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ v, g v ∂ν := integral_mono_of_nonneg
      (ae_of_all ν (fun v => abs_nonneg _)) hgi (ae_of_all ν hfixed)
    _ = _ := (hlaw.integral_comp hgm.aestronglyMeasurable).symm

end CausalSmith.Stat.OptvalueVanishingoverlapRate
