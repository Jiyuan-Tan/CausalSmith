module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDisclosure
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.FrameBounds
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! Exact transport from marked fair labels to the six original-record categories. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Summing the unused outcome sign in a zero-mark record recovers its treatment-only category mass. This identity retains both zero-outcome treatment categories. [This is the stated conclusion](goal). -/
-- @node: zero_mark_label_mass
lemma zero_mark_label_mass (ξ ε : ℝ) (t : Bool) :
    (∑ h : Bool, ENNReal.ofReal ((1-ε)/4*(1+signVal t*ξ))) =
      ENNReal.ofReal ((1-ε)/2*(1+signVal t*ξ)) := by
  simp only [Fintype.sum_bool]
  rw [← two_mul, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- The independent mark flag and fair treatment/outcome labels push forward to exactly the normalized six-category table, with the unused sign summed out in zero marks. [This is the stated conclusion](goal). -/
-- @node: marked_label_record_measure
lemma marked_label_record_measure (ξ υ ζ ε L : ℝ) (x : unitInterval) :
    (∑ label : Bool × Bool,
      ENNReal.ofReal (ε/4*(1+signVal label.1*ξ+signVal label.2*υ+
        signVal label.1*signVal label.2*ζ)) •
          Measure.dirac (x,label.1,signVal label.2*L)) +
    (∑ label : Bool × Bool,
      ENNReal.ofReal ((1-ε)/4*(1+signVal label.1*ξ)) •
          Measure.dirac (x,label.1,(0:ℝ))) =
    ∑ cat : Category, ENNReal.ofReal (markedTable ξ υ ζ ε cat) •
      Measure.dirac (x,cat.1,markValue L cat.2) := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [← Finset.sum_smul, zero_mark_label_mass, Fintype.sum_option,
    markedTable, markValue]
  exact add_comm _ _

/-- A valid support draw uses the literal table law, so its original sampling measure does not enter the fallback branch of the observed-law constructor. [This is the stated conclusion](goal). -/
-- @node: copulaLaw_measure_eq_tableLaw
lemma copulaLaw_measure_eq_tableLaw (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) (idx : CopulaIndex K M) :
    (copulaLaw ν v K M a u ε L idx).P =
      tableLaw (copulaXi K M a idx) (copulaUpsilon K M u idx)
        (copulaZeta ν K M a u idx) ε L := by
  have ht := copula_table_valid n K M a u ε L h ν idx
  simp only [copulaLaw, tableObservedLaw, dif_pos ht]

/-- The original support measure is the uniform-design mixture of the marked-label record measures, including all six categories. [This is the stated conclusion](goal). -/
-- @node: copulaLaw_measure_eq_label_bind
lemma copulaLaw_measure_eq_label_bind (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) (idx : CopulaIndex K M) :
    (copulaLaw ν v K M a u ε L idx).P = design.bind (fun x =>
      (∑ label : Bool × Bool, ENNReal.ofReal (ε/4*labelDensity ν K M a u idx x true label) •
        Measure.dirac (x,label.1,signVal label.2*L)) +
      (∑ label : Bool × Bool, ENNReal.ofReal ((1-ε)/4*labelDensity ν K M a u idx x false label) •
        Measure.dirac (x,label.1,(0:ℝ)))) := by
  rw [copulaLaw_measure_eq_tableLaw ν v n K M a u ε L h idx]
  unfold tableLaw
  congr 1
  funext x
  exact (marked_label_record_measure _ _ _ ε L x).symm

/-- Enumeration through the finite prior preserves the original weights and full iid sampling laws exactly. No probability or model-membership premise is needed for reindexing. [This is the stated conclusion](goal). -/
-- @node: copulaMixture_eq_index_sum
lemma copulaMixture_eq_index_sum (ν : Bool) (n : ℕ) (v : Params) (K M : ℕ)
    (a u ε L : ℝ) :
    copulaMixture ν n v K M a u ε L =
      ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
        Measure.pi (fun _ : Fin n => (copulaLaw ν v K M a u ε L idx).P) := by
  unfold copulaMixture copulaPrior priorMixture priorWeight priorLaw finitePriorOf
  exact Fintype.sum_equiv (Fintype.equivFin (CopulaIndex K M)).symm _ _ (fun _ => rfl)

/-- Each conditional six-category record measure is a probability measure.  [the parameters and conditions in the statement](hyp:L,h,x), [the asserted mathematical result holds](goal). -/
-- @node: table_record_fibre_probability
lemma table_record_fibre_probability (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (x : unitInterval) :
    IsProbabilityMeasure (∑ cat : Category,
      ENNReal.ofReal (markedTable (ξ x) (υ x) (ζ x) ε cat) •
        Measure.dirac (x,cat.1,markValue L cat.2)) := by
  constructor
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun cat _ => h.2.2.2.2.2.2 x cat)]
  have hsum : (∑ cat : Category, markedTable (ξ x) (υ x) (ζ x) ε cat) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [markedTable_row_sum]
    simp [Fintype.sum_bool, signVal]
    ring
  rw [hsum, ENNReal.ofReal_one]

/-- The full iid support law is obtained by first drawing the iid uniform design and then independently drawing each of its six-category record fibres. [This is the stated conclusion](goal). -/
-- @node: copula_iid_table_bind
lemma copula_iid_table_bind (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) (idx : CopulaIndex K M) :
    Measure.pi (fun _ : Fin n => (copulaLaw ν v K M a u ε L idx).P) =
      (Measure.pi (fun _ : Fin n => design)).bind (fun xs =>
        Measure.pi (fun i : Fin n => ∑ cat : Category,
          ENNReal.ofReal (markedTable (copulaXi K M a idx (xs i))
            (copulaUpsilon K M u idx (xs i)) (copulaZeta ν K M a u idx (xs i)) ε cat) •
              Measure.dirac (xs i,cat.1,markValue L cat.2))) := by
  have ht := copula_table_valid n K M a u ε L h ν idx
  let κ : Kernel unitInterval Record := ⟨fun x => ∑ cat : Category,
    ENNReal.ofReal (markedTable (copulaXi K M a idx x)
      (copulaUpsilon K M u idx x) (copulaZeta ν K M a u idx x) ε cat) •
        Measure.dirac (x,cat.1,markValue L cat.2), by
    apply Finset.measurable_sum
    intro cat _
    have hξ := ht.1.measurable
    have hυ := ht.2.1.measurable
    have hζ := ht.2.2.1.measurable
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    have hd : Measurable (fun x : unitInterval =>
        Measure.dirac (x,cat.1,markValue L cat.2) s) :=
      (Measure.measurable_coe hs).comp (by fun_prop)
    rcases cat with ⟨t, mark⟩
    cases mark <;> simp only [markedTable] <;> fun_prop⟩
  let : IsMarkovKernel κ := ⟨fun x => table_record_fibre_probability _ _ _ ε L ht x⟩
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hcomp : κ ∘ₘ design = (copulaLaw ν v K M a u ε L idx).P := by
    rw [copulaLaw_measure_eq_tableLaw ν v n K M a u ε L h idx]
    rfl
  rw [← hcomp, ← Causalean.Stat.finProductKernel_comp_pi]
  change (Measure.pi (fun _ : Fin n => design)).bind _ = _
  congr 1
  funext xs
  exact Causalean.Stat.finProductKernel_apply n κ xs

/-- The same iid transport written with the marked fair-label fibres explicitly preserves both treatment labels even when the outcome mark is zero. [This is the stated conclusion](goal). -/
-- @node: copula_iid_label_bind
lemma copula_iid_label_bind (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) (idx : CopulaIndex K M) :
    Measure.pi (fun _ : Fin n => (copulaLaw ν v K M a u ε L idx).P) =
      (Measure.pi (fun _ : Fin n => design)).bind (fun xs =>
        Measure.pi (fun i : Fin n =>
          (∑ label : Bool × Bool, ENNReal.ofReal (ε/4*labelDensity ν K M a u idx (xs i) true label) •
            Measure.dirac (xs i,label.1,signVal label.2*L)) +
          (∑ label : Bool × Bool, ENNReal.ofReal ((1-ε)/4*labelDensity ν K M a u idx (xs i) false label) •
            Measure.dirac (xs i,label.1,(0:ℝ))))) := by
  rw [copula_iid_table_bind ν v n K M a u ε L h idx]
  congr 1
  funext xs
  congr 1
  funext i
  exact (marked_label_record_measure _ _ _ ε L (xs i)).symm

/-- Finite products of atomic fibres enumerate all joint labels, with the product of their actual category weights. The proof identifies every measurable rectangle. This statement assumes [the w condition](hyp:w). [This is the stated conclusion](goal). -/
-- @node: record_pi_finite_atomic
lemma record_pi_finite_atomic {ι J Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    [MeasurableSpace Ω] (w : ι → J → ℝ≥0∞) (f : ι → J → Ω)
    [∀ i, SigmaFinite (∑ j : J, w i j • Measure.dirac (f i j))] :
    Measure.pi (fun i => ∑ j : J, w i j • Measure.dirac (f i j)) =
      ∑ labels : ι → J, (∏ i, w i (labels i)) •
        Measure.dirac (fun i => f i (labels i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  simp only [Set.indicator_apply, Pi.one_apply]
  apply Finset.sum_congr rfl
  intro labels _
  by_cases hmem : ∀ i, f i (labels i) ∈ s i
  · simp [Set.mem_pi, hmem]
  · obtain ⟨i, hi⟩ := not_forall.mp hmem
    simp only [Set.mem_pi, Set.mem_univ, forall_const] at *
    rw [if_neg (by simpa using hmem), mul_zero]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Keeping a redundant outcome sign in zero marks gives an eight-label fibre whose pushforward is the literal six-category record fibre. [This is the stated conclusion](goal). -/
-- @node: copula_flag_label_fibre
lemma copula_flag_label_fibre (ν : Bool) (K M : ℕ) (a u ε L : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) :
    (∑ tag : Bool × (Bool × Bool),
      ENNReal.ofReal ((if tag.1 then ε/4 else (1-ε)/4) *
        labelDensity ν K M a u idx x tag.1 tag.2) •
          Measure.dirac (x,tag.2.1,if tag.1 then signVal tag.2.2*L else 0)) =
    ∑ cat : Category, ENNReal.ofReal (markedTable (copulaXi K M a idx x)
      (copulaUpsilon K M u idx x) (copulaZeta ν K M a u idx x) ε cat) •
        Measure.dirac (x,cat.1,markValue L cat.2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simpa only [Bool.false_eq_true, ↓reduceIte, labelDensity] using
    marked_label_record_measure (copulaXi K M a idx x) (copulaUpsilon K M u idx x)
      (copulaZeta ν K M a u idx x) ε L x

/-- Every fixed support draw has the exact full-sample marked-label enumeration conditional on the iid design. No record categories or occupied cells are discarded. [This is the stated conclusion](goal). -/
-- @node: copula_iid_flag_label_bind
lemma copula_iid_flag_label_bind (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) (idx : CopulaIndex K M) :
    Measure.pi (fun _ : Fin n => (copulaLaw ν v K M a u ε L idx).P) =
      (Measure.pi (fun _ : Fin n => design)).bind (fun xs =>
        ∑ tags : Fin n → Bool × (Bool × Bool),
          (∏ i : Fin n, ENNReal.ofReal ((if (tags i).1 then ε/4 else (1-ε)/4) *
            labelDensity ν K M a u idx (xs i) (tags i).1 (tags i).2)) •
          Measure.dirac (fun i => (xs i,(tags i).2.1,
            if (tags i).1 then signVal (tags i).2.2*L else 0))) := by
  rw [copula_iid_table_bind ν v n K M a u ε L h idx]
  congr 1
  funext xs
  have ht := copula_table_valid n K M a u ε L h ν idx
  let w (i : Fin n) (tag : Bool × (Bool × Bool)) : ℝ≥0∞ :=
    ENNReal.ofReal ((if tag.1 then ε/4 else (1-ε)/4) *
      labelDensity ν K M a u idx (xs i) tag.1 tag.2)
  let f (i : Fin n) (tag : Bool × (Bool × Bool)) : Record :=
    (xs i,tag.2.1,if tag.1 then signVal tag.2.2*L else 0)
  have hf (i : Fin n) : (∑ tag, w i tag • Measure.dirac (f i tag)) =
      ∑ cat : Category, ENNReal.ofReal (markedTable (copulaXi K M a idx (xs i))
        (copulaUpsilon K M u idx (xs i)) (copulaZeta ν K M a u idx (xs i)) ε cat) •
          Measure.dirac (xs i,cat.1,markValue L cat.2) :=
    copula_flag_label_fibre ν K M a u ε L idx (xs i)
  let : ∀ i, IsProbabilityMeasure (∑ tag, w i tag • Measure.dirac (f i tag)) :=
    fun i => by rw [hf]; exact table_record_fibre_probability _ _ _ ε L ht (xs i)
  rw [← record_pi_finite_atomic w f]
  congr 1
  funext i
  exact (hf i).symm

/-- The original copula mixture is the exact finite prior average of the full marked-label sample transports, with the coarse signs retained inside each support draw. [This is the stated conclusion](goal). -/
-- @node: copulaMixture_eq_flag_label_bind
lemma copulaMixture_eq_flag_label_bind (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) :
    copulaMixture ν n v K M a u ε L =
      ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
        (Measure.pi (fun _ : Fin n => design)).bind (fun xs =>
          ∑ tags : Fin n → Bool × (Bool × Bool),
            (∏ i : Fin n, ENNReal.ofReal ((if (tags i).1 then ε/4 else (1-ε)/4) *
              labelDensity ν K M a u idx (xs i) (tags i).1 (tags i).2)) •
            Measure.dirac (fun i => (xs i,(tags i).2.1,
              if (tags i).1 then signVal (tags i).2.2*L else 0))) := by
  rw [copulaMixture_eq_index_sum]
  simp_rw [copula_iid_flag_label_bind ν v n K M a u ε L h]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
