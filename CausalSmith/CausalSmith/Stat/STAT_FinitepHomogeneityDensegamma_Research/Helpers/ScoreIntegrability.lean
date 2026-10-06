module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreLedger
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments

/-! Bounded clipped score primitives and integrability of both public ledger branches. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A crude finite rank bound suffices for integrability, including rank zero. [This is the stated conclusion](goal). -/
-- @node: featureMap_norm_bound
lemma featureMap_norm_bound (J : ℕ) (x : unitInterval) :
    ‖featureMap J x‖ ≤ Real.sqrt ((J : ℝ)*J) := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : Fin J, (J : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [featureMap, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
      split_ifs <;> simp [Real.sq_sqrt (Nat.cast_nonneg J)]
    _ = _ := by simp

/-- Composing histogram features with any measurable location map gives bounded features. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: featureMap_memLp_top
lemma featureMap_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (x : Ω → unitInterval) (hx : Measurable x) :
    MemLp (fun o => featureMap J (x o)) ∞ μ := by
  apply memLp_top_of_bound ((measurable_featureMap J).comp hx).aestronglyMeasurable
    (Real.sqrt ((J : ℝ)*J))
  exact ae_of_all _ (fun o => featureMap_norm_bound J (x o))

/-- Histogram kernels have a finite uniform bound, even at rank zero. This statement assumes [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: projKernel_memLp_top
lemma projKernel_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (x z : Ω → unitInterval) (hx : Measurable x) (hz : Measurable z) :
    MemLp (fun o => projKernel J (x o) (z o)) ∞ μ := by
  apply memLp_top_of_bound (by unfold projKernel; fun_prop) ((J : ℝ)*J)
  apply ae_of_all
  intro o
  calc
    ‖projKernel J (x o) (z o)‖ ≤ ‖featureMap J (x o)‖*‖featureMap J (z o)‖ := norm_inner_le_norm _ _
    _ ≤ Real.sqrt ((J : ℝ)*J)*Real.sqrt ((J : ℝ)*J) := by
      gcongr <;> exact featureMap_norm_bound J _
    _ = _ := Real.mul_self_sqrt (by positivity)

/-- Dyadic difference kernels inherit boundedness from their two histogram kernels. This statement assumes [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: diffKernel_memLp_top
lemma diffKernel_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (x z : Ω → unitInterval) (hx : Measurable x) (hz : Measurable z) :
    MemLp (fun o => diffKernel J (x o) (z o)) ∞ μ :=
  (projKernel_memLp_top μ (2*J) x z hx hz).sub (projKernel_memLp_top μ J x z hx hz)

/-- A treatment label is a bounded measurable scalar on any dataset space. This statement assumes [the ho condition](hyp:ho). [This is the stated conclusion](goal). -/
-- @node: treatment_memLp_top
lemma treatment_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (o : Ω → Record) (ho : Measurable o) : MemLp (fun d => treatment (o d)) ∞ μ := by
  have ht : Measurable treatment := by
    unfold treatment A
    exact (measurable_of_countable (fun a : Bool => if a then (1 : ℝ) else 0)).comp
      (measurable_fst.comp measurable_snd)
  apply memLp_top_of_bound ((ht.comp ho).aestronglyMeasurable) 1
  apply ae_of_all
  intro d
  change ‖(if A (o d) then (1 : ℝ) else 0)‖ ≤ 1
  split <;> norm_num

/-- Every real clipping level produces a uniformly bounded outcome mark. This statement assumes [the ho condition](hyp:ho). [This is the stated conclusion](goal). -/
-- @node: clippedOutcome_memLp_top
lemma clippedOutcome_memLp_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℝ) (o : Ω → Record) (ho : Measurable o) :
    MemLp (fun d => clipY T (Y (o d))) ∞ μ := by
  apply memLp_top_of_bound (by unfold clipY Y; fun_prop) |T|
  apply ae_of_all
  intro d
  rw [Real.norm_eq_abs]
  by_cases hT : 0 ≤ T
  · simpa [abs_of_nonneg hT] using clipY_abs_le T (Y (o d)) hT
  · have ht : T ≤ -T := by linarith
    have hm : min (Y (o d)) T ≤ -T := (min_le_right _ _).trans ht
    simp only [clipY, max_eq_left hm, abs_neg]
    exact le_rfl

/-- Finite block averages of clipped single-record features are bounded in every sample. [This is the stated conclusion](goal). -/
-- @node: hScore_memLp_top
lemma hScore_memLp_top (n J : ℕ) (b : Bool) (T c : ℝ) (μ : Measure (Dataset n)) :
    MemLp (hScore n b J T c) ∞ μ := by
  have hx (i : Fin n) : Measurable (fun d : Dataset n => X (d i)) := by unfold X; fun_prop
  have ho (i : Fin n) : Measurable (fun d : Dataset n => d i) := by fun_prop
  have hi : MemLp (hIntercept n b J T) ∞ μ := by
    unfold hIntercept
    split
    · exact memLp_top_const 0
    · change MemLp ((_ : ℝ) • (fun data : Dataset n => (_ : Vec J))) ∞ μ
      apply MemLp.const_smul
      apply memLp_finsetSum
      intro i _
      exact (featureMap_memLp_top μ J _ (hx i)).smul
        ((clippedOutcome_memLp_top μ T _ (ho i)).mul (r := ∞) (treatment_memLp_top μ _ (ho i)))
  have ht : MemLp (hTreatment n b J) ∞ μ := by
    unfold hTreatment
    split
    · exact memLp_top_const 0
    · change MemLp ((_ : ℝ) • (fun data : Dataset n => (_ : Vec J))) ∞ μ
      apply MemLp.const_smul
      apply memLp_finsetSum
      intro i _
      exact (featureMap_memLp_top μ J _ (hx i)).smul (treatment_memLp_top μ _ (ho i))
  exact hi.sub (ht.const_smul c)

/-- Any bounded measurable correction kernel gives a bounded clipped ordered-pair score. This statement assumes [the hG condition](hyp:hG). [This is the stated conclusion](goal). -/
-- @node: uScore_memLp_top
lemma uScore_memLp_top (n J : ℕ) (b : Bool) (G : unitInterval → unitInterval → ℝ)
    (T c : ℝ) (μ : Measure (Dataset n))
    (hG : ∀ i j : Fin n, MemLp (fun d : Dataset n => G (X (d i)) (X (d j))) ∞ μ) :
    MemLp (uScore n b J G T c) ∞ μ := by
  have hx (i : Fin n) : Measurable (fun d : Dataset n => X (d i)) := by unfold X; fun_prop
  have ho (i : Fin n) : Measurable (fun d : Dataset n => d i) := by fun_prop
  have hi : MemLp (uIntercept n b J G T) ∞ μ := by
    unfold uIntercept
    split
    · exact memLp_top_const 0
    · change MemLp ((_ : ℝ) • (fun data : Dataset n => (_ : Vec J))) ∞ μ
      apply MemLp.const_smul
      apply memLp_finsetSum
      intro i _
      apply memLp_finsetSum
      intro j _
      exact (featureMap_memLp_top μ J _ (hx i)).smul
        ((clippedOutcome_memLp_top μ T _ (ho j)).mul (r := ∞)
          ((hG i j).mul (r := ∞) (treatment_memLp_top μ _ (ho i))))
  have ht : MemLp (uTreatment n b J G) ∞ μ := by
    unfold uTreatment
    split
    · exact memLp_top_const 0
    · change MemLp ((_ : ℝ) • (fun data : Dataset n => (_ : Vec J))) ∞ μ
      apply MemLp.const_smul
      apply memLp_finsetSum
      intro i _
      apply memLp_finsetSum
      intro j _
      exact (featureMap_memLp_top μ J _ (hx i)).smul
        ((treatment_memLp_top μ _ (ho j)).mul (r := ∞)
          ((hG i j).mul (r := ∞) (treatment_memLp_top μ _ (ho i))))
  exact hi.sub (ht.const_smul c)

/-- All finite dyadic corrections remain bounded after their level-specific clipping. [This is the stated conclusion](goal). -/
-- @node: multiresScore_memLp_top
lemma multiresScore_memLp_top (n J L : ℕ) (b : Bool) (T0 : ℝ) (T : Fin L → ℝ)
    (c : ℝ) (μ : Measure (Dataset n)) : MemLp (multiresScore n b J L T0 T c) ∞ μ := by
  have hx (i : Fin n) : Measurable (fun d : Dataset n => X (d i)) := by unfold X; fun_prop
  unfold multiresScore
  apply MemLp.sub
  · exact (hScore_memLp_top n J b T0 c μ).sub
      (uScore_memLp_top n J b (projKernel J) T0 c μ
        (fun i j => projKernel_memLp_top μ J _ _ (hx i) (hx j)))
  · apply memLp_finsetSum
    intro j _
    exact uScore_memLp_top n J b (diffKernel (2^j.val*J)) (T j) c μ
      (fun i k => diffKernel_memLp_top μ _ _ _ (hx i) (hx k))

/-- Every public ledger branch is bounded, with no model or sample-size premise. [This is the stated conclusion](goal). -/
-- @node: ledgerScore_memLp_top
lemma ledgerScore_memLp_top (n : ℕ) (v : Params) (b : Bool) (c : ℝ)
    (μ : Measure (Dataset n)) : MemLp (ledgerScore n v b c) ∞ μ := by
  have hx (i : Fin n) : Measurable (fun d : Dataset n => X (d i)) := by unfold X; fun_prop
  unfold ledgerScore
  split
  · exact memLp_top_const 0
  · split
    · exact (hScore_memLp_top n _ b _ c μ).sub
        (uScore_memLp_top n _ b (projKernel (ledgerK n v)) _ c μ
          (fun i j => projKernel_memLp_top μ _ _ _ (hx i) (hx j)))
    · exact multiresScore_memLp_top n _ _ b _ _ c μ

/-- On a finite sampling measure the total public score belongs to every finite-moment space. This statement assumes [the p condition](hyp:p). [This is the stated conclusion](goal). -/
-- @node: ledgerScore_memLp
lemma ledgerScore_memLp (n : ℕ) (v : Params) (b : Bool) (c : ℝ)
    (μ : Measure (Dataset n)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (ledgerScore n v b c) p μ :=
  (ledgerScore_memLp_top n v b c μ).mono_exponent le_top

/-- In particular the original-record mean is a genuine Bochner integral in every branch. [This is the stated conclusion](goal). -/
-- @node: integrable_ledgerScore
lemma integrable_ledgerScore (n : ℕ) (v : Params) (b : Bool) (c : ℝ)
    (law : ObservedLaw) : Integrable (ledgerScore n v b c) (Measure.pi fun _ : Fin n => law.P) :=
  (memLp_one_iff_integrable).mp (ledgerScore_memLp n v b c _ 1)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
