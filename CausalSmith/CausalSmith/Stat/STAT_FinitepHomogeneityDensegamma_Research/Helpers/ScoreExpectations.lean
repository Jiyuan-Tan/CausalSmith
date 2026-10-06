module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairSampleMoments
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreIntegrability
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Exact block averaging and arm integration for the clipped score means. -/
@[expose] public section
set_option maxHeartbeats 800000
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Both deterministic evaluation blocks contain precisely the public block size. [This is the stated conclusion](goal). -/
-- @node: evalBlock_card
lemma evalBlock_card (n : ℕ) (b : Bool) : (evalBlock n b).card = blockSize n := by
  classical
  have hhalf : 2*blockSize n ≤ n := by unfold blockSize; omega
  rw [← Finset.card_range (blockSize n)]
  cases b
  · apply Finset.card_bij (fun (i : Fin n) _ => i.val) (t := Finset.range (blockSize n))
    · intro i hi
      simpa [evalBlock] using hi
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      have hj' : j < blockSize n := Finset.mem_range.mp hj
      refine ⟨⟨j, by omega⟩, ?_, rfl⟩
      simp [evalBlock, hj']
  · apply Finset.card_bij (fun (i : Fin n) _ => i.val-blockSize n) (t := Finset.range (blockSize n))
    · intro i hi
      have hh : blockSize n ≤ i.val ∧ i.val < 2*blockSize n := by simpa [evalBlock] using hi
      simp only [Finset.mem_range]
      omega
    · intro i hi j hj hij
      have hi' : blockSize n ≤ i.val := (show blockSize n ≤ i.val ∧ i.val < 2*blockSize n by simpa [evalBlock] using hi).1
      have hj' : blockSize n ≤ j.val := (show blockSize n ≤ j.val ∧ j.val < 2*blockSize n by simpa [evalBlock] using hj).1
      apply Fin.ext
      omega
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      refine ⟨⟨blockSize n+j, by omega⟩, ?_, by simp⟩
      simp only [evalBlock, Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte]
      omega

/-- A bounded single-record vector integrates identically at every iid coordinate. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: score_single_coordinate_integral
lemma score_single_coordinate_integral {n J : ℕ} (law : ObservedLaw)
    (f : Record → Vec J) (hf : Measurable f) (i : Fin n) :
    (∫ data : Dataset n, f (data i) ∂Measure.pi (fun _ : Fin n => law.P)) = ∫ o, f o ∂law.P := by
  have hp := measurePreserving_eval (fun _ : Fin n => law.P) i
  have he := integral_map hp.measurable.aemeasurable (hf.aestronglyMeasurable (μ := (Measure.pi fun _ : Fin n => law.P).map (fun data => data i)))
  simpa only [hp.map_eq] using he.symm

/-- The normalized finite single-record block average has its population mean. This statement assumes [the hn condition](hyp:hn), [the hf condition](hyp:hf), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: score_block_integral
lemma score_block_integral {J : ℕ} (n : ℕ) (b : Bool) (hn : 4 ≤ n) (law : ObservedLaw)
    (f : Record → Vec J) (hf : Measurable f) (hi : Integrable f law.P) :
    (∫ data : Dataset n, (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b, f (data i)
      ∂Measure.pi (fun _ : Fin n => law.P)) = ∫ o, f o ∂law.P := by
  have his (i : Fin n) : Integrable (fun data : Dataset n => f (data i))
      (Measure.pi fun _ : Fin n => law.P) :=
    (measurePreserving_eval (fun _ : Fin n => law.P) i).integrable_comp_of_integrable hi
  rw [integral_smul, integral_finsetSum _ (fun i _ => his i)]
  simp_rw [score_single_coordinate_integral law f hf]
  rw [Finset.sum_const, evalBlock_card, ← Nat.cast_smul_eq_nsmul ℝ]
  have hs : (blockSize n:ℝ) ≠ 0 := by
    have : 0 < blockSize n := by unfold blockSize; omega
    exact_mod_cast this.ne'
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- Distinct iid coordinates integrate a measurable vector pair by its product law. This statement assumes [the hg condition](hyp:hg), [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: score_pair_coordinate_integral
lemma score_pair_coordinate_integral {n J : ℕ} (law : ObservedLaw)
    (g : Record → Record → Vec J) (hg : Measurable (fun z : Record × Record => g z.1 z.2))
    (i j : Fin n) (hij : i ≠ j) :
    (∫ data : Dataset n, g (data i) (data j) ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ z : Record × Record, g z.1 z.2 ∂law.P.prod law.P := by
  have hp := pair_sample_measurePreserving law.P i j hij
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable).symm

/-- Exact ordered-pair counting cancels the public correction normalization. This statement assumes [the hn condition](hyp:hn), [the hg condition](hyp:hg), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: score_pair_block_integral
lemma score_pair_block_integral {J : ℕ} (n : ℕ) (b : Bool) (hn : 4 ≤ n) (law : ObservedLaw)
    (g : Record → Record → Vec J) (hg : Measurable (fun z : Record × Record => g z.1 z.2))
    (hi : Integrable (fun z : Record × Record => g z.1 z.2) (law.P.prod law.P)) :
    (∫ data : Dataset n, ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
      ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, g (data i) (data j)
      ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ z : Record × Record, g z.1 z.2 ∂law.P.prod law.P := by
  have his (i j : Fin n) (hj : j ∈ (evalBlock n b).erase i) :
      Integrable (fun data : Dataset n => g (data i) (data j)) (Measure.pi fun _ : Fin n => law.P) :=
    (pair_sample_measurePreserving law.P i j (Finset.mem_erase.mp hj).1.symm).integrable_comp_of_integrable hi
  rw [integral_smul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j hj => his i j hj))]
  simp_rw [integral_finsetSum _ (fun j hj => his _ j hj)]
  have he (i : Fin n) (hi : i ∈ evalBlock n b) :
      (∑ j ∈ (evalBlock n b).erase i,
        ∫ data : Dataset n, g (data i) (data j) ∂Measure.pi (fun _ : Fin n => law.P)) =
      ((blockSize n:ℝ)-1) • (∫ z : Record × Record, g z.1 z.2 ∂law.P.prod law.P) := by
    rw [Finset.sum_congr rfl (fun j hj => score_pair_coordinate_integral law g hg i j (Finset.mem_erase.mp hj).1.symm)]
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, evalBlock_card]
    simp only [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_sub (by unfold blockSize; omega : 1 ≤ blockSize n), Nat.cast_one]
  rw [Finset.sum_congr rfl he, Finset.sum_const, evalBlock_card, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have hs : 2 ≤ blockSize n := by unfold blockSize; omega
  have hs0 : (blockSize n:ℝ) ≠ 0 := by exact_mod_cast (by omega : blockSize n ≠ 0)
  have hs1 : (blockSize n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ blockSize n := by exact_mod_cast hs
    linarith
  rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 hs1), one_smul]

/-- The binary treatment encoding is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_treatment
@[fun_prop] lemma measurable_treatment : Measurable treatment := by
  unfold treatment A
  exact (measurable_of_countable (fun a : Bool => if a then (1:ℝ) else 0)).comp
    (measurable_fst.comp measurable_snd)

/-- Clipped single-record averaging integrates by the original treated feature kernel. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: hScore_mean_record
lemma hScore_mean_record (n J : ℕ) (b : Bool) (hn : 4 ≤ n) (law : ObservedLaw)
    (T c : ℝ) :
    (∫ data, hScore n b J T c data ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ o, (treatment o*(clipY T (Y o)-c)) • featureMap J (X o) ∂law.P := by
  have he : hScore n b J T c = fun data =>
      (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
        (treatment (data i)*(clipY T (Y (data i))-c)) • featureMap J (X (data i)) := by
    funext data
    simp only [hScore, hIntercept, hTreatment, if_neg (by omega : ¬n<4)]
    rw [smul_comm c, ← smul_sub, Finset.smul_sum, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    module
  rw [he]
  apply score_block_integral (J := J) n b hn law (fun o => (treatment o*(clipY T (Y o)-c)) • featureMap J (X o))
  · exact (measurable_treatment.mul ((show Measurable (fun o : Record => clipY T (Y o)) from
      (by unfold clipY Y; fun_prop)).sub measurable_const)).smul
        ((measurable_featureMap J).comp measurable_fst)
  · have hf := featureMap_memLp_top law.P J X (by unfold X; fun_prop)
    have ht := treatment_memLp_top law.P id measurable_id
    have hy := clippedOutcome_memLp_top law.P T id measurable_id
    convert (hf.smul (r := ∞) (ht.mul (r := ∞) (hy.sub (memLp_top_const c)))).integrable (by norm_num) using 1
    · rfl
    · funext o
      dsimp
      congr 1
      ring

/-- Clipped ordered-pair averaging integrates against two independent original records. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: uScore_mean_record
lemma uScore_mean_record (n J K : ℕ) (b : Bool) (hn : 4 ≤ n) (law : ObservedLaw)
    (T c : ℝ) :
    (∫ data, uScore n b J (projKernel K) T c data ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ z : Record × Record,
        (treatment z.1*projKernel K (X z.1) (X z.2)*(clipY T (Y z.2)-c*treatment z.2)) •
          featureMap J (X z.1) ∂law.P.prod law.P := by
  have he : uScore n b J (projKernel K) T c = fun data =>
      ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
        ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
          (treatment (data i)*projKernel K (X (data i)) (X (data j))*
            (clipY T (Y (data j))-c*treatment (data j))) • featureMap J (X (data i)) := by
    funext data
    simp only [uScore, uIntercept, uTreatment, if_neg (by omega : ¬n<4)]
    rw [smul_comm c, ← smul_sub, Finset.smul_sum, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    module
  rw [he]
  apply score_pair_block_integral (J := J) n b hn law (fun o z =>
    (treatment o*projKernel K (X o) (X z)*(clipY T (Y z)-c*treatment z)) • featureMap J (X o))
  · exact (((measurable_treatment.comp measurable_fst).mul
      ((measurable_projKernel K).comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))).mul
        ((show Measurable (fun z : Record × Record => clipY T (Y z.2)) from
          (by unfold clipY Y; fun_prop)).sub
            (measurable_const.mul (measurable_treatment.comp measurable_snd)))).smul
              ((measurable_featureMap J).comp (measurable_fst.comp measurable_fst))
  · let μ := law.P.prod law.P
    have hf := featureMap_memLp_top μ J (fun z : Record × Record => X z.1) (by unfold X; fun_prop)
    have hg := projKernel_memLp_top μ K (fun z : Record × Record => X z.1)
      (fun z => X z.2) (by unfold X; fun_prop) (by unfold X; fun_prop)
    have ht1 := treatment_memLp_top μ Prod.fst measurable_fst
    have ht2 := treatment_memLp_top μ Prod.snd measurable_snd
    have hy := clippedOutcome_memLp_top μ T Prod.snd measurable_snd
    convert (hf.smul (r := ∞) ((ht1.mul (r := ∞) hg).mul (r := ∞)
      (hy.sub (ht2.const_mul c)))).integrable (by norm_num) using 1
    · rfl
    · funext o
      dsimp
      congr 1
      ring

/-- The original-record law integrates a bounded vector by its two conditional arms. This statement assumes [the hu condition](hyp:hu), [the hf condition](hyp:hf), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: original_record_integral_arms
lemma original_record_integral_arms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (law : ObservedLaw) (hu : UniformDesign law)
    (f : Record → E) (hf : Measurable f) (C : ℝ) (hb : ∀ o, ‖f o‖ ≤ C) :
    (∫ o, f o ∂law.P) = ∫ x,
      law.e x • (∫ y, f (x,true,y) ∂law.Q true x)+
        (1-law.e x) • (∫ y, f (x,false,y) ∂law.Q false x) ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable law.Q) :=
    recordKernel_markov _ _ _ law.e_range law.markov
  have he : law.P = design ⊗ₘ recordKernel law.e law.e.continuous.measurable law.Q := by
    rw [law.record_version, show law.P.map X = design from hu]
  have hi : Integrable f law.P :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hb)
  rw [he, Measure.integral_compProd (he ▸ hi)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hiy (a : Bool) : Integrable (fun y => f (x,a,y)) (law.Q a x) :=
    (integrable_const C).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ (fun y => hb (x,a,y)))
  have hip (a : Bool) : Integrable (fun r : Bool × ℝ => f (x,r))
      ((Measure.dirac a).prod (law.Q a x)) := by
    rw [Measure.dirac_prod]
    exact (integrable_map_measure (hf.comp (by fun_prop)).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).mpr (hiy a)
  change (∫ r : Bool × ℝ, f (x,r) ∂recordMeasure law.e law.Q x) = _
  rw [recordMeasure, integral_add_measure (hip true |>.smul_measure ENNReal.ofReal_ne_top)
    (hip false |>.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (law.e_range x).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (law.e_range x).2),
    Measure.dirac_prod, Measure.dirac_prod,
    integral_map (f := fun r : Bool × ℝ => f (x,r)) measurable_prodMk_left.aemeasurable
      (hf.comp measurable_prodMk_left).aestronglyMeasurable,
    integral_map (f := fun r : Bool × ℝ => f (x,r)) measurable_prodMk_left.aemeasurable
      (hf.comp measurable_prodMk_left).aestronglyMeasurable]

/-- A bounded original mark times a bounded covariate vector integrates by its conditional arm mean. This statement assumes [the hu condition](hyp:hu), [the hq condition](hyp:hq), [the hCq condition](hyp:hCq), [the hbq condition](hyp:hbq), [the hg condition](hyp:hg), [the hCg condition](hyp:hCg), [the hbg condition](hyp:hbg). [This is the stated conclusion](goal). -/
-- @node: original_record_weighted_integral
lemma original_record_weighted_integral {J : ℕ} (law : ObservedLaw) (hu : UniformDesign law)
    (q : Record → ℝ) (hq : Measurable q) (Cq : ℝ) (hCq : 0 ≤ Cq) (hbq : ∀ o, |q o| ≤ Cq)
    (g : unitInterval → Vec J) (hg : Measurable g) (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hbg : ∀ x, ‖g x‖ ≤ Cg) :
    (∫ o, q o • g (X o) ∂law.P) = ∫ x,
      (law.e x*(∫ y, q (x,true,y) ∂law.Q true x)+
        (1-law.e x)*(∫ y, q (x,false,y) ∂law.Q false x)) • g x ∂design := by
  rw [original_record_integral_arms law hu (fun o => q o • g (X o))
    (hq.smul (hg.comp measurable_fst)) (Cq*Cg) (fun o => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hbq o) (hbg (X o)) (norm_nonneg _) hCq)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [X, integral_smul_const, smul_smul, ← add_smul]

/-- The treatment mark is bounded by one. [This is the stated conclusion](goal). -/
-- @node: treatment_abs_le_one
lemma treatment_abs_le_one (o : Record) : |treatment o| ≤ 1 := by
  unfold treatment
  split <;> norm_num

/-- The clipped treated centered outcome is bounded uniformly over original records. [This is the stated conclusion](goal). -/
-- @node: treated_clipped_mark_bound
lemma treated_clipped_mark_bound (T c : ℝ) (o : Record) :
    |treatment o*(clipY T (Y o)-c)| ≤ |T|+|c| := by
  have hy : |clipY T (Y o)| ≤ |T| := by
    by_cases hT : 0 ≤ T
    · simpa [abs_of_nonneg hT] using clipY_abs_le T (Y o) hT
    · have ht : min (Y o) T ≤ -T := (min_le_right _ _).trans (by linarith)
      simp [clipY, max_eq_left ht]
  rw [abs_mul]
  exact (mul_le_mul (treatment_abs_le_one o) ((abs_sub (clipY T (Y o)) c).trans (add_le_add hy (le_refl |c|)))
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The affine clipped outcome mark has the same deterministic bound. [This is the stated conclusion](goal). -/
-- @node: clipped_mark_bound
lemma clipped_mark_bound (T c : ℝ) (o : Record) :
    |clipY T (Y o)-c*treatment o| ≤ |T|+|c| := by
  have hy : |clipY T (Y o)| ≤ |T| := by
    by_cases hT : 0 ≤ T
    · simpa [abs_of_nonneg hT] using clipY_abs_le T (Y o) hT
    · have ht : min (Y o) T ≤ -T := (min_le_right _ _).trans (by linarith)
      simp [clipY, max_eq_left ht]
  calc
    _ ≤ |clipY T (Y o)|+|c*treatment o| := abs_sub _ _
    _ ≤ |T|+|c| := by
      rw [abs_mul]
      exact add_le_add hy (by simpa using mul_le_mul_of_nonneg_left (treatment_abs_le_one o) (abs_nonneg c))

/-- Integrating a treatment-weighted clipped feature gives its treated conditional mean. This statement assumes [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: treated_clipped_feature_integral
lemma treated_clipped_feature_integral (law : ObservedLaw) (hu : UniformDesign law)
    (J : ℕ) (T c : ℝ) :
    (∫ o, (treatment o*(clipY T (Y o)-c)) • featureMap J (X o) ∂law.P) =
      ∫ x, (law.e x*((∫ y, clipY T y ∂law.Q true x)-c)) • featureMap J x ∂design := by
  rw [original_record_weighted_integral (J := J) law hu (fun o => treatment o*(clipY T (Y o)-c))
    (measurable_treatment.mul ((show Measurable (fun o : Record => clipY T (Y o)) from
      (by unfold clipY Y; fun_prop)).sub measurable_const))
    (|T|+|c|) (by positivity) (treated_clipped_mark_bound T c)
    (featureMap J) (measurable_featureMap J) (Real.sqrt ((J:ℝ)*J)) (by positivity)
    (featureMap_norm_bound J)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hi : Integrable (fun y => clipY T y) (law.Q true x) :=
    (clippedOutcome_memLp_top (law.Q true x) T (fun y => (x,true,y)) (by fun_prop)).integrable (by norm_num)
  simp only [treatment, A, Y, Bool.false_eq_true, ↓reduceIte, one_mul, zero_mul,
    integral_zero, mul_zero, add_zero]
  rw [integral_sub hi (integrable_const c)]
  simp

/-- The conditional original-record mean of a bounded scalar mark retains both treatment arms. This statement assumes [the law parameter](hyp:law), [the q parameter](hyp:q), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
-- @node: recordMarkMean
def recordMarkMean (law : ObservedLaw) (q : Record → ℝ) (x : unitInterval) : ℝ :=
  law.e x*(∫ y, q (x,true,y) ∂law.Q true x)+
    (1-law.e x)*(∫ y, q (x,false,y) ∂law.Q false x)

/-- Conditional arm integration of a Borel scalar mark is Borel measurable. This statement assumes [the hq condition](hyp:hq). [This is the stated conclusion](goal). -/
-- @node: measurable_recordMarkMean
@[fun_prop] lemma measurable_recordMarkMean (law : ObservedLaw) (q : Record → ℝ)
    (hq : Measurable q) : Measurable (recordMarkMean law q) := by
  have ha (a : Bool) : Measurable (fun x => ∫ y, q (x,a,y) ∂law.Q a x) :=
    (show Measurable (fun z : unitInterval × ℝ => q (z.1,a,z.2)) from
      hq.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).stronglyMeasurable.integral_kernel_prod_right'.measurable
  exact (law.e.continuous.measurable.mul (ha true)).add
    ((measurable_const.sub law.e.continuous.measurable).mul (ha false))

/-- Conditional mark averaging preserves its deterministic absolute bound. This statement assumes [the hq condition](hyp:hq), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: recordMarkMean_bound
lemma recordMarkMean_bound (law : ObservedLaw) (q : Record → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ o, |q o| ≤ C) (x : unitInterval) :
    |recordMarkMean law q x| ≤ C := by
  have ha (a : Bool) : |∫ y, q (x,a,y) ∂law.Q a x| ≤ C := by
    calc
      _ ≤ ∫ y, |q (x,a,y)| ∂law.Q a x := abs_integral_le_integral_abs
      _ ≤ ∫ _y, C ∂law.Q a x := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) (integrable_const C)
        exact ae_of_all _ (fun y => hb (x,a,y))
      _ = C := by simp
  unfold recordMarkMean
  calc
    _ ≤ |law.e x*(∫ y, q (x,true,y) ∂law.Q true x)|+
        |(1-law.e x)*(∫ y, q (x,false,y) ∂law.Q false x)| := abs_add_le _ _
    _ ≤ law.e x*C+(1-law.e x)*C := by
      rw [abs_mul, abs_mul, abs_of_nonneg (law.e_range x).1,
        abs_of_nonneg (sub_nonneg.mpr (law.e_range x).2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (ha true) (law.e_range x).1)
        (mul_le_mul_of_nonneg_left (ha false) (sub_nonneg.mpr (law.e_range x).2))
    _ = C := by ring

/-- The conditional mean of the treatment encoding is the propensity. [This is the stated conclusion](goal). -/
-- @node: recordMarkMean_treatment
lemma recordMarkMean_treatment (law : ObservedLaw) : recordMarkMean law treatment = law.e := by
  funext x
  simp [recordMarkMean, treatment, A]

/-- A bounded scalar mark times the histogram row integrates to its projected conditional mean. This statement assumes [the hu condition](hyp:hu), [the hK condition](hyp:hK), [the hq condition](hyp:hq), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: record_histogram_mark_integral
lemma record_histogram_mark_integral (law : ObservedLaw) (hu : UniformDesign law)
    (K : ℕ) (hK : 0 < K) (x : unitInterval) (q : Record → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ o, |q o| ≤ C) :
    (∫ o, projKernel K x (X o)*q o ∂law.P) = projOp K (recordMarkMean law q) x := by
  rw [original_record_integral_arms law hu (fun o => projKernel K x (X o)*q o)
    (by exact ((measurable_projKernel K).comp (measurable_const.prodMk measurable_fst)).mul hq)
    ((K:ℝ)*C) (fun o => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (histogram_kernel_bounds K hK x (X o)).2 (hb o) (abs_nonneg _) (by positivity))]
  simp only [integral_const_mul, smul_eq_mul, projOp, recordMarkMean]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only [X]
  simp only [integral_const_mul]
  ring

/-- Histogram projection of a Borel function is Borel measurable. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: measurable_projOp
@[fun_prop] lemma measurable_projOp (K : ℕ) (f : unitInterval → ℝ) (hf : Measurable f) :
    Measurable (projOp K f) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  unfold projOp
  exact (show Measurable (fun z : unitInterval × unitInterval => projKernel K z.1 z.2*f z.2) from
    (measurable_projKernel K).mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable

/-- A bounded input gives a finite deterministic bound on every histogram projection row. This statement assumes [the hK condition](hyp:hK), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: projOp_bound_of_bound
lemma projOp_bound_of_bound (K : ℕ) (hK : 0 < K) (f : unitInterval → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (x : unitInterval) :
    |projOp K f x| ≤ (K:ℝ)*C := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  unfold projOp
  calc
    _ ≤ ∫ z, |projKernel K x z*f z| ∂design := abs_integral_le_integral_abs
    _ ≤ ∫ _z, (K:ℝ)*C ∂design := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (integrable_const _)
      exact ae_of_all _ (fun z => by
        dsimp only
        rw [abs_mul]
        exact mul_le_mul (histogram_kernel_bounds K hK x z).2 (hb z) (abs_nonneg _) (by positivity))
    _ = _ := by simp

/-- Independent record correction pairs integrate to the propensity times a projected conditional mark. This statement assumes [the hu condition](hyp:hu), [the hK condition](hyp:hK), [the hq condition](hyp:hq), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: treated_pair_histogram_integral
lemma treated_pair_histogram_integral (law : ObservedLaw) (hu : UniformDesign law)
    (J K : ℕ) (hK : 0 < K) (q : Record → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ o, |q o| ≤ C) :
    (∫ z : Record × Record,
      (treatment z.1*projKernel K (X z.1) (X z.2)*q z.2) • featureMap J (X z.1) ∂law.P.prod law.P) =
      ∫ x, (law.e x*projOp K (recordMarkMean law q) x) • featureMap J x ∂design := by
  let f := recordMarkMean law q
  have hfm : Measurable f := measurable_recordMarkMean law q hq
  have hfb : ∀ x, |f x| ≤ C := recordMarkMean_bound law q hq C hC hb
  have hpm : Measurable (projOp K f) := measurable_projOp K f hfm
  have hpb : ∀ x, |projOp K f x| ≤ (K:ℝ)*C := projOp_bound_of_bound K hK f C hC hfb
  have hm : Measurable (fun z : Record × Record =>
      (treatment z.1*projKernel K (X z.1) (X z.2)*q z.2) • featureMap J (X z.1)) :=
    (((measurable_treatment.comp measurable_fst).mul
      ((measurable_projKernel K).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))).mul (hq.comp measurable_snd)).smul
          ((measurable_featureMap J).comp (measurable_fst.comp measurable_fst))
  have hi : Integrable (fun z : Record × Record =>
      (treatment z.1*projKernel K (X z.1) (X z.2)*q z.2) • featureMap J (X z.1)) (law.P.prod law.P) := by
    apply (integrable_const ((K:ℝ)*C*Real.sqrt ((J:ℝ)*J))).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      _ ≤ (1*(K:ℝ)*C)*Real.sqrt ((J:ℝ)*J) := by
        gcongr
        · exact treatment_abs_le_one z.1
        · exact (histogram_kernel_bounds K hK (X z.1) (X z.2)).2
        · exact hb z.2
        · exact featureMap_norm_bound J (X z.1)
      _ = _ := by ring
  rw [integral_prod _ hi]
  simp_rw [integral_smul_const, mul_assoc, integral_const_mul,
    record_histogram_mark_integral law hu K hK _ q hq C hC hb]
  simp only [← smul_smul]
  rw [original_record_weighted_integral (J := J) law hu treatment measurable_treatment 1
    (by norm_num) treatment_abs_le_one (fun x => projOp K f x • featureMap J x)
    (hpm.smul (measurable_featureMap J)) ((K:ℝ)*C*Real.sqrt ((J:ℝ)*J)) (by positivity)
    (fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hpb x) (featureMap_norm_bound J x) (norm_nonneg _) (by positivity))]
  change (∫ x, recordMarkMean law treatment x • (projOp K f x • featureMap J x) ∂design) = _
  simp only [recordMarkMean_treatment, smul_smul, f]

/-- A histogram feature vector is constant on each of its cells. This statement assumes [the hJ condition](hyp:hJ), [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: histogram_feature_eq_on_cell
lemma histogram_feature_eq_on_cell (J : ℕ) (hJ : 0 < J) (j : Fin J)
    (x z : unitInterval) (hx : x ∈ cell J j) (hz : z ∈ cell J j) :
    featureMap J x = featureMap J z := by
  obtain ⟨jx, hjx, hux⟩ := histogram_cell_unique J hJ x
  obtain ⟨jz, hjz, huz⟩ := histogram_cell_unique J hJ z
  have he (i : Fin J) : x ∈ cell J i ↔ z ∈ cell J i := by
    constructor
    · intro hi
      have : i=j := (hux i hi).trans (hux j hx).symm
      simpa [this] using hz
    · intro hi
      have : i=j := (huz i hi).trans (huz j hz).symm
      simpa [this] using hx
  ext i
  by_cases hi : x ∈ cell J i
  · simp [featureMap, hi, (he i).mp hi]
  · have hzi : z ∉ cell J i := fun hz => hi ((he i).mpr hz)
    simp [featureMap, hi, hzi]

/-- A refining histogram kernel can move the coarse feature between its two arguments. This statement assumes [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: histogram_feature_kernel_commute
lemma histogram_feature_kernel_commute (J K : ℕ) (hJ : 0 < J) (hK : 0 < K)
    (hJK : J ∣ K) (x z : unitInterval) :
    projKernel K x z • featureMap J x = projKernel K z x • featureMap J z := by
  obtain ⟨m, rfl⟩ := hJK
  have hm : 0 < m := by nlinarith
  obtain ⟨k, hx, _⟩ := histogram_cell_unique (J*m) hK x
  rw [← (histogram_kernel_bounds (J*m) hK x z).1,
    histogram_kernel_row (J*m) hK x k hx z]
  by_cases hz : z ∈ cell (J*m) k
  · obtain ⟨j, hj⟩ := histogram_cell_refinement J m hJ hm k
    simp only [if_pos hz]
    rw [histogram_feature_eq_on_cell J hJ j x z (hj hx) (hj hz)]
  · simp [hz]

/-- Refining histogram projection is self-adjoint even with a coarse feature vector weight. This statement assumes [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the he condition](hyp:he), [the hf condition](hyp:hf), [the hCe condition](hyp:hCe), [the hCf condition](hyp:hCf), [the hbe condition](hyp:hbe), [the hbf condition](hyp:hbf). [This is the stated conclusion](goal). -/
-- @node: histogram_feature_selfAdjoint
lemma histogram_feature_selfAdjoint (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K)
    (e f : unitInterval → ℝ) (he : Measurable e) (hf : Measurable f)
    (Ce Cf : ℝ) (hCe : 0 ≤ Ce) (hCf : 0 ≤ Cf)
    (hbe : ∀ x, |e x| ≤ Ce) (hbf : ∀ x, |f x| ≤ Cf) :
    (∫ x, (e x*projOp K f x) • featureMap J x ∂design) =
      ∫ x, (projOp K e x*f x) • featureMap J x ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hi : Integrable (fun z : unitInterval × unitInterval =>
      (e z.1*projKernel K z.1 z.2*f z.2) • featureMap J z.1) (design.prod design) := by
    apply (integrable_const (Ce*(K:ℝ)*Cf*Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
    apply ae_of_all
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    gcongr
    · exact hbe z.1
    · exact (histogram_kernel_bounds K hK z.1 z.2).2
    · exact hbf z.2
    · exact featureMap_norm_bound J z.1
  calc
    _ = ∫ x, ∫ z, (e x*projKernel K x z*f z) • featureMap J x ∂design ∂design := by
      simp only [integral_smul_const, mul_assoc, integral_const_mul, projOp]
    _ = ∫ z, ∫ x, (e x*projKernel K x z*f z) • featureMap J x ∂design ∂design := integral_integral_swap hi
    _ = ∫ z, ∫ x, (projKernel K z x*e x*f z) • featureMap J z ∂design ∂design := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      apply integral_congr_ae
      apply ae_of_all
      intro x
      calc
        _ = (e x*f z) • (projKernel K x z • featureMap J x) := by module
        _ = (e x*f z) • (projKernel K z x • featureMap J z) := by
          rw [histogram_feature_kernel_commute J K hJ hK hJK]
        _ = _ := by module
    _ = _ := by simp only [integral_smul_const, integral_mul_const, projOp]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
