module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MixtureDensity
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.TreeSeries

/-! # Unconditional marked information
Reorder the original records into covariates and spins, integrate the conditional
component bound, and apply the labeled-root tree series. -/

@[expose] public section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Regroup four blocks by exchanging the middle two.  Given [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input D](hyp:D), [regroup four equiv](goal) is the corresponding construction. -/
def regroupFourEquiv (A B C D : Type*) [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) where
  toEquiv := Equiv.prodProdProdComm A B C D
  measurable_toFun := by
    change Measurable (fun x : (A × B) × (C × D) => ((x.1.1,x.2.1),(x.1.2,x.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : (A × C) × (B × D) => ((x.1.1,x.2.1),(x.1.2,x.2.2)))
    fun_prop

/-- Given [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input D](hyp:D), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input c](hyp:c), [the specified input d](hyp:d), [the regroup four measure preserving conclusion](goal) holds. -/
lemma regroupFour_measurePreserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] [IsFiniteMeasure d] :
    MeasurePreserving (regroupFourEquiv A B C D) ((a.prod b).prod (c.prod d))
      ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod ((measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id a).prod (Measure.measurePreserving_swap (μ:=b) (ν:=c) |>.prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := (measurePreserving_prodAssoc a c (b.prod d)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Covariate arrays split at the labeled sample size.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [covariate concat equiv](goal) is the corresponding construction. -/
def covariateConcatEquiv (d n m : ℕ) :
    ((Fin n → Cov d) × (Fin m → Cov d)) ≃ᵐ (Fin (n+m) → Cov d) where
  toFun x := Fin.addCases x.1 x.2
  invFun x := (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))
  left_inv x := by simp
  right_inv x := by funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  measurable_toFun := by
    change Measurable (fun x : (Fin n → Cov d) × (Fin m → Cov d) => fun i : Fin (n+m) => (Fin.addCases x.1 x.2 i : Cov d))
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin (n+m) → Cov d =>
      (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j)))
    fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the covariate concat measure preserving conclusion](goal) holds. -/
lemma covariateConcat_measurePreserving (d n m : ℕ) :
    MeasurePreserving (covariateConcatEquiv d n m)
      ((Measure.pi (fun _ : Fin n => uniformLaw d)).prod (Measure.pi (fun _ : Fin m => uniformLaw d)))
      (Measure.pi (fun _ : Fin (n+m) => uniformLaw d)) := by
  letI := uniformLaw_probability d
  refine ⟨(covariateConcatEquiv d n m).measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (covariateConcatEquiv d n m).measurable (MeasurableSet.univ_pi hs)]
  rw [show (covariateConcatEquiv d n m) ⁻¹' (univ.pi s) =
      (univ.pi (fun i : Fin n => s (Fin.castAdd m i))) ×ˢ
        (univ.pi (fun j : Fin m => s (Fin.natAdd n j))) by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    change (∀ i, Fin.addCases x.1 x.2 i ∈ s i) ↔ _
    constructor
    · intro h; exact ⟨fun i => by simpa using h (Fin.castAdd m i), fun j => by simpa using h (Fin.natAdd n j)⟩
    · rintro ⟨h1,h2⟩ i; refine Fin.addCases ?_ ?_ i <;> intro j
      · simpa using h1 j
      · simpa using h2 j]
  rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

/-- A measurable reordering separates all covariates from all observed spins.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [dataset split equiv](goal) is the corresponding construction. -/
def datasetSplitEquiv (d n m : ℕ) : Dataset d n m ≃ᵐ ((Fin (n+m) → Cov d) × RecordSpins n m) :=
  ((MeasurableEquiv.arrowProdEquivProdArrow (Cov d) (Bool × Bool) (Fin n)).prodCongr
    (MeasurableEquiv.arrowProdEquivProdArrow (Cov d) Bool (Fin m))).trans
    ((regroupFourEquiv (Fin n → Cov d) (Fin n → Bool × Bool) (Fin m → Cov d) (Fin m → Bool)).trans
      ((covariateConcatEquiv d n m).prodCongr (MeasurableEquiv.refl _)))

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the dataset split apply conclusion](goal) holds. -/
lemma datasetSplit_apply {d n m : ℕ} (D : Dataset d n m) :
    datasetSplitEquiv d n m D = (datasetCovariates D, datasetSpins D) := rfl

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the dataset split measure preserving conclusion](goal) holds. -/
lemma datasetSplit_measurePreserving (d n m : ℕ) :
    MeasurePreserving (datasetSplitEquiv d n m) (fairDataset d n m)
      ((Measure.pi (fun _ : Fin (n+m) => uniformLaw d)).prod
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod
          (Measure.pi (fun _ : Fin m => bern (1/2))))) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  have hl := measurePreserving_arrowProdEquivProdArrow (Cov d) (Bool × Bool) (Fin n)
    (fun _ => uniformLaw d) (fun _ => fairObserved)
  have ha := measurePreserving_arrowProdEquivProdArrow (Cov d) Bool (Fin m)
    (fun _ => uniformLaw d) (fun _ => bern (1/2))
  exact ((covariateConcat_measurePreserving d n m).prod (MeasurePreserving.id _)).comp
    ((regroupFour_measurePreserving _ _ _ _).comp (hl.prod ha))

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the fair dataset probability conclusion](goal) holds. -/
lemma fairDataset_probability (d n m : ℕ) : IsProbabilityMeasure (fairDataset d n m) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  unfold fairDataset
  infer_instance

set_option maxHeartbeats 800000 in
/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input s](hyp:s), [the marked mixed density bounds conclusion](goal) holds. -/
lemma marked_mixedDensity_bounds (d n m : ℕ) (h delta a b : ℝ) (theta : Bool)
    (x : Fin (n+m) → Cov d) (s : RecordSpins n m) :
    0 ≤ mixedDensity (markedHandle d h delta a b) theta x s ∧
    mixedDensity (markedHandle d h delta a b) theta x s ≤ (4:ℝ)^(n+m) := by
  have hrec (sigma : SignArray d h delta) (i : Fin (n+m)) :
      0 ≤ recordLikelihood (markedLaw h delta a b theta sigma) x s i ∧
      recordLikelihood (markedLaw h delta a b theta sigma) x s i ≤ 4 := by
    obtain ⟨hl, ha⟩ := independent_likelihood_bounds d (markedPropensity h delta a sigma)
      (markedMean h delta a b theta false sigma) (markedMean h delta a b theta true sigma)
      (measurable_markedPropensity h delta a sigma)
      (measurable_markedMean h delta a b theta false sigma)
      (measurable_markedMean h delta a b theta true sigma)
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [recordLikelihood, Fin.addCases_left]
      exact hl (x (Fin.castAdd m j), s.1 j)
    · intro j
      simp only [recordLikelihood, Fin.addCases_right]
      exact ⟨(ha (x (Fin.natAdd n j), s.2 j)).1,
        (ha (x (Fin.natAdd n j), s.2 j)).2.trans (by norm_num)⟩
  obtain ⟨hw, hsum⟩ := marked_prior_mass d h delta theta
  constructor
  · apply Finset.sum_nonneg
    intro sigma _
    exact mul_nonneg (hw sigma) (Finset.prod_nonneg (fun i _ => (hrec sigma i).1))
  · calc
      _ ≤ ∑ sigma : SignArray d h delta, markedWeight h delta theta sigma * (4:ℝ)^(n+m) := by
        apply Finset.sum_le_sum
        intro sigma _
        apply mul_le_mul_of_nonneg_left _ (hw sigma)
        calc
          _ ≤ ∏ _i : Fin (n+m), (4:ℝ) := Finset.prod_le_prod
            (fun i _ => (hrec sigma i).1) (fun i _ => (hrec sigma i).2)
          _ = _ := by simp
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the measurable mixed density conclusion](goal) holds. -/
@[fun_prop] lemma measurable_mixedDensity (d n m : ℕ) (H : MarkedPriors d) (theta : Bool) :
    Measurable (fun z : (Fin (n+m) → Cov d) × RecordSpins n m => mixedDensity H theta z.1 z.2) := by
  have h := (measurable_datasetDensity (n:=n) (m:=m) H theta).comp (datasetSplitEquiv d n m).symm.measurable
  convert h using 1
  funext z
  have hz := datasetSplit_apply ((datasetSplitEquiv d n m).symm z)
  rw [(datasetSplitEquiv d n m).apply_symm_apply] at hz
  simpa only [datasetDensity, Function.comp_apply] using
    congrArg (fun z => mixedDensity H theta z.1 z.2) hz

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked dataset density integrable conclusion](goal) holds. -/
lemma marked_datasetDensity_integrable (d n m : ℕ) (h delta a b : ℝ) (theta : Bool) :
    Integrable (datasetDensity (n:=n) (m:=m) (markedHandle d h delta a b) theta) (fairDataset d n m) := by
  letI := fairDataset_probability d n m
  apply (integrable_const ((4:ℝ)^(n+m))).mono' (measurable_datasetDensity _ _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro D
  have hb := marked_mixedDensity_bounds d n m h delta a b theta (datasetCovariates D) (datasetSpins D)
  change ‖mixedDensity (markedHandle d h delta a b) theta (datasetCovariates D) (datasetSpins D)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked mixture finite conclusion](goal) holds. -/
lemma markedMixture_finite (d n m : ℕ) (h delta a b : ℝ) (theta : Bool) :
    IsFiniteMeasure (markedMixture (markedHandle d h delta a b) theta n m) := by
  rw [markedMixture_density]
  exact isFiniteMeasure_withDensity_ofReal (marked_datasetDensity_integrable d n m h delta a b theta).hasFiniteIntegral

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked sqrt difference integrable conclusion](goal) holds. -/
lemma marked_sqrt_difference_integrable (d n m : ℕ) (h delta a b : ℝ) :
    Integrable (fun z : (Fin (n+m) → Cov d) × RecordSpins n m =>
      (Real.sqrt (mixedDensity (markedHandle d h delta a b) true z.1 z.2) -
        Real.sqrt (mixedDensity (markedHandle d h delta a b) false z.1 z.2))^2)
      ((Measure.pi (fun _ : Fin (n+m) => uniformLaw d)).prod
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod (Measure.pi (fun _ : Fin m => bern (1/2))))) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  apply (integrable_const (4*(4:ℝ)^(n+m))).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨hf0,hf⟩ := marked_mixedDensity_bounds d n m h delta a b true z.1 z.2
  obtain ⟨hg0,hg⟩ := marked_mixedDensity_bounds d n m h delta a b false z.1 z.2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hfs := Real.sq_sqrt hf0
  have hgs := Real.sq_sqrt hg0
  nlinarith [sq_nonneg (Real.sqrt (mixedDensity (markedHandle d h delta a b) true z.1 z.2) +
    Real.sqrt (mixedDensity (markedHandle d h delta a b) false z.1 z.2))]

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked mixture hellinger eq integral conclusion](goal) holds. -/
lemma markedMixture_hellinger_eq_integral (d n m : ℕ) (h delta a b : ℝ) :
    hellingerSq (markedMixture (markedHandle d h delta a b) true n m)
      (markedMixture (markedHandle d h delta a b) false n m) =
    ∫ x : Fin (n+m) → Cov d, Causalean.Stat.hellingerSqDensity
      ((Measure.pi (fun _ : Fin n => fairObserved)).prod (Measure.pi (fun _ : Fin m => bern (1/2))))
      (mixedDensity (markedHandle d h delta a b) true x)
      (mixedDensity (markedHandle d h delta a b) false x)
      ∂Measure.pi (fun _ : Fin (n+m) => uniformLaw d) := by
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  letI := fairDataset_probability d n m
  letI := markedMixture_finite d n m h delta a b true
  letI := markedMixture_finite d n m h delta a b false
  rw [hellingerSq_real_density _ _ (fairDataset d n m) _ _
    (measurable_datasetDensity _ _) (measurable_datasetDensity _ _)
    (datasetDensity_nonneg _ _ (marked_prior_mass d h delta true).1)
    (datasetDensity_nonneg _ _ (marked_prior_mass d h delta false).1)
    (markedMixture_density d n m h delta a b true)
    (markedMixture_density d n m h delta a b false)]
  unfold Causalean.Stat.hellingerSqDensity
  have hsplit := (datasetSplit_measurePreserving d n m).integral_comp
    (datasetSplitEquiv d n m).measurableEmbedding
    (fun z => (Real.sqrt (mixedDensity (markedHandle d h delta a b) true z.1 z.2) -
      Real.sqrt (mixedDensity (markedHandle d h delta a b) false z.1 z.2))^2)
  change (∫ D, (Real.sqrt (datasetDensity (markedHandle d h delta a b) true D) -
    Real.sqrt (datasetDensity (markedHandle d h delta a b) false D))^2 ∂fairDataset d n m) = _
  rw [show (fun D => (Real.sqrt (datasetDensity (markedHandle d h delta a b) true D) -
    Real.sqrt (datasetDensity (markedHandle d h delta a b) false D))^2) =
    (fun D => (Real.sqrt (mixedDensity (markedHandle d h delta a b) true (datasetSplitEquiv d n m D).1
      (datasetSplitEquiv d n m D).2) - Real.sqrt (mixedDensity (markedHandle d h delta a b) false
        (datasetSplitEquiv d n m D).1 (datasetSplitEquiv d n m D).2))^2) by rfl,
    hsplit, integral_prod _ (marked_sqrt_difference_integrable d n m h delta a b)]
/-- Given [the specified input N](hyp:N), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the sum sizes le shifted range conclusion](goal) holds. -/
lemma sum_sizes_le_shifted_range (N : ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (∑ p ∈ Finset.Icc 2 N, f p) ≤ ∑ j ∈ Finset.range N, f (j+2) := by
  classical
  have hi : Set.InjOn (fun p : ℕ => p-2) (Finset.Icc 2 N) := by
    intro p hp q hq he
    have hp := Finset.mem_Icc.mp hp
    have hq := Finset.mem_Icc.mp hq
    dsimp only at he
    omega
  have heq : (∑ p ∈ Finset.Icc 2 N, f p) =
      ∑ j ∈ (Finset.Icc 2 N).image (fun p => p-2), f (j+2) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    have hp := Finset.mem_Icc.mp hp
    omega
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have hp := Finset.mem_Icc.mp hp
    rw [Finset.mem_range]
    omega
  · intro j _ _; exact hf _

/-- Integrating MC32 and the labeled-root count series proves MC37 for the original records.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked information bound conclusion](goal) holds. -/
lemma marked_information_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c c0 C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < c0 ∧ 0 < C ∧
      ∀ (n m : ℕ) (h delta a b : ℝ),
        2 ≤ n → 0 < delta → delta ≤ h → h ≤ 1/2 →
        0 < a → a ≤ c*delta^alpha → 0 < b → b ≤ c*delta^beta →
        a*b ≤ c*h^gamma → ((n:ℝ)+m)*delta^d ≤ c0 →
        hellingerSq (markedMixture (markedHandle d h delta a b) true n m)
          (markedMixture (markedHandle d h delta a b) false n m) ≤
          C*(n:ℝ)*((n:ℝ)+m)*h^d*delta^d*a^2*b^2 := by
  obtain ⟨c,K,hc,hc1,hK,hcond⟩ := marked_conditional_hellinger_count_bound d alpha beta gamma L eps hdom
  obtain ⟨c0,C,hc0,hC,hseries⟩ := labeled_component_series_bound d (9/2) (by norm_num)
  refine ⟨c,c0,K*C,hc,hc1,hc0,mul_pos hK hC,?_⟩
  intro n m h delta a b hn hd hdh hh ha hac hb hbc hab hocc
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  let ν := Measure.pi (fun _ : Fin (n+m) => uniformLaw d)
  let μ := (Measure.pi (fun _ : Fin n => fairObserved)).prod (Measure.pi (fun _ : Fin m => bern (1/2)))
  let H := markedHandle d h delta a b
  let count := fun (p : ℕ) (x : Fin (n+m) → Cov d) =>
    ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
      (componentVertices h delta x c).card = p ∧
      ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ)
  have hci (p : ℕ) (hp : 2 ≤ p) : Integrable (count p) ν := labeled_record_count_integrable d n m h delta p hp
  have hsumI : Integrable (fun x => K*a^2*b^2 *
      ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 * count p x) ν := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro p hp
    exact (hci p (Finset.mem_Icc.mp hp).1).const_mul _
  have hhi : Integrable (fun x => Causalean.Stat.hellingerSqDensity μ
      (mixedDensity H true x) (mixedDensity H false x)) ν :=
    (marked_sqrt_difference_integrable d n m h delta a b).integral_prod_left
  have hx : ∀ᵐ x ∂ν, ∀ i, x i ∈ cube d := by
    apply ae_all_iff.mpr
    intro i
    have hi := measurePreserving_eval (fun _ : Fin (n+m) => uniformLaw d) i
    exact hi.quasiMeasurePreserving.ae (by
      unfold uniformLaw
      exact ae_restrict_mem (measurable_cube d))
  have hbound : (∫ x, Causalean.Stat.hellingerSqDensity μ
      (mixedDensity H true x) (mixedDensity H false x) ∂ν) ≤
      K*a^2*b^2 * ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 * (∫ x, count p x ∂ν) := by
    calc
      _ ≤ ∫ x, K*a^2*b^2 * ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 * count p x ∂ν := by
        apply integral_mono_ae hhi hsumI
        filter_upwards [hx] with x hx
        exact hcond h delta a b hd hdh hh ha hac hb hbc hab n m x hx
      _ = _ := by
        rw [integral_const_mul, integral_finsetSum (f := fun p x => (9/2:ℝ)^p*(p:ℝ)^4 * count p x)
          (Finset.Icc 2 (n+m)) (fun p hp => (hci p (Finset.mem_Icc.mp hp).1).const_mul _)]
        simp only [integral_const_mul]
  rw [markedMixture_hellinger_eq_integral]
  change (∫ x, Causalean.Stat.hellingerSqDensity μ (mixedDensity H true x) (mixedDensity H false x) ∂ν) ≤ _
  calc
    _ ≤ K*a^2*b^2 * ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 * (∫ x, count p x ∂ν) := hbound
    _ ≤ K*a^2*b^2 * ∑ j ∈ Finset.range (n+m), (9/2:ℝ)^(j+2)*((j+2:ℕ):ℝ)^4 *
        (∫ x, count (j+2) x ∂ν) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_sizes_le_shifted_range (n+m) _ (fun p => by
        apply mul_nonneg (by positivity)
        apply integral_nonneg
        intro x
        exact Nat.cast_nonneg _)
    _ ≤ K*a^2*b^2 * (C*(n:ℝ)*((n:ℝ)+m)*h^d*delta^d) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hseries n m h delta (hd.trans_le hdh) hh hd hdh hocc
    _ = _ := by ring
end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
