module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerComponentBounds
public import Mathlib.Probability.Independence.Integration

/-! Normalized component likelihoods and affinity factorization over disjoint record blocks. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Measurable functions depending on disjoint finite coordinate blocks have factored integrals. -/
-- @node: integral_disjoint_coordinate_blocks
lemma integral_disjoint_coordinate_blocks
    {ι η α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq η]
    [MeasurableSpace α] [Inhabited α] (μ : ι → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset η) (A : η → Finset ι)
    (F : η → (ι → α) → ℝ) (hd : Set.PairwiseDisjoint (S : Set η) A)
    (hm : ∀ k ∈ S, Measurable (F k))
    (hf : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → F k v = F k w) :
    (∫ z, ∏ k ∈ S, F k z ∂Measure.pi μ) =
      ∏ k ∈ S, ∫ z, F k z ∂Measure.pi μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih =>
    have hdS : Set.PairwiseDisjoint (S : Set η) A := fun i hi j hj hij =>
      hd (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    let B := S.biUnion A
    have hdis : Disjoint (A k) B := by
      apply Finset.disjoint_left.mpr
      intro i hik hiB
      obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp hiB
      exact Finset.disjoint_left.mp
        (hd (Finset.mem_insert_self k S) (Finset.mem_insert_of_mem hl)
          (by intro he; subst l; exact hk hl)) hik hil
    let extend (T : Finset ι) (z : T → α) : ι → α :=
      fun i => if hi : i ∈ T then z ⟨i, hi⟩ else default
    have heM (T : Finset ι) : Measurable (extend T) := by
      apply measurable_pi_lambda
      intro i
      dsimp only [extend]
      split_ifs <;> fun_prop
    have he (T : Finset ι) (z : ι → α) (i : ι) (hi : i ∈ T) :
        extend T (fun j => z j) i = z i := by simp [extend, hi]
    let G := fun z : B → α => ∏ l ∈ S, F l (extend B z)
    have hGM : Measurable G := by
      apply Finset.measurable_prod
      intro l hl
      exact (hm l (Finset.mem_insert_of_mem hl)).comp (heM B)
    have hleft (z : ι → α) : F k (extend (A k) (fun i => z i)) = F k z := by
      apply hf k (Finset.mem_insert_self k S)
      exact fun i hi => he _ z i hi
    have hright (z : ι → α) : G (fun i => z i) = ∏ l ∈ S, F l z := by
      apply Finset.prod_congr rfl
      intro l hl
      apply hf l (Finset.mem_insert_of_mem hl)
      intro i hi
      exact he B z i (Finset.mem_biUnion.mpr ⟨l, hl, hi⟩)
    have hi := (iIndepFun_pi (μ := μ) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun_finset (A k) B hdis
        (fun i => measurable_pi_apply i)
    have hiF := hi.comp ((hm k (Finset.mem_insert_self k S)).comp (heM (A k))) hGM
    have hiF' : IndepFun (F k) (fun z => ∏ l ∈ S, F l z) (Measure.pi μ) := by
      simpa only [Function.comp_def, id_eq, hleft, hright] using hiF
    have hmul := hiF'.integral_fun_mul_eq_mul_integral
      (hm k (Finset.mem_insert_self k S)).aestronglyMeasurable
      (Finset.measurable_prod S (fun l hl => hm l
        (Finset.mem_insert_of_mem hl))).aestronglyMeasurable
    simp only [Finset.prod_insert hk]
    rw [hmul, ih hdS (fun l hl => hm l (Finset.mem_insert_of_mem hl))
      (fun l hl => hf l (Finset.mem_insert_of_mem hl))]

variable (κ : Params) (n : ℕ)

/-- Reference responses lie on the displayed three atoms almost surely. -/
-- @node: reference_marks_finite_support
lemma reference_marks_finite_support (hκ : κ.Valid) (hn : 2 ≤ n) :
    ∀ᵐ z ∂referenceMarks κ n,
      z ∈ (Set.univ : Set Bool) ×ˢ {lowerAmplitude κ n, -lowerAmplitude κ n, 0} := by
  have hsupp : ∀ᵐ y ∂(ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (lowerAmplitude κ n) +
      ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (-lowerAmplitude κ n) +
      ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0),
      y ∈ ({lowerAmplitude κ n, -lowerAmplitude κ n, 0} : Set ℝ) := by
    rw [ae_add_measure_iff, ae_add_measure_iff]
    refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
      Measure.ae_smul_measure ?_ _⟩ <;> simp
  unfold referenceMarks
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  exact Filter.Eventually.of_forall (fun _ => hsupp.mono (fun _ hy => ⟨mem_univ _, hy⟩))

/-- Every real function is integrable on a finite product of the finite reference mark laws. -/
-- @node: reference_marks_pi_integrable
lemma reference_marks_pi_integrable (hκ : κ.Valid) (hn : 2 ≤ n)
    {ι : Type*} [Fintype ι] (f : (ι → Bool × ℝ) → ℝ) :
    Integrable f (Measure.pi (fun _ : ι => referenceMarks κ n)) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  let T : Set (Bool × ℝ) := Set.univ ×ˢ {lowerAmplitude κ n, -lowerAmplitude κ n, 0}
  have hT : T.Finite := Set.toFinite _ |>.prod (by simp)
  have ha : ∀ᵐ z ∂Measure.pi (fun _ : ι => referenceMarks κ n), z ∈ Set.pi Set.univ (fun _ => T) := by
    have hi (i : ι) : ∀ᵐ z ∂Measure.pi (fun _ : ι => referenceMarks κ n), z i ∈ T :=
      (measurePreserving_eval (fun _ : ι => referenceMarks κ n) i).quasiMeasurePreserving.ae
        (reference_marks_finite_support κ n hκ hn)
    filter_upwards [ae_all_iff.mpr hi] with z hz
    exact fun i _ => hz i
  have hfin : (Set.pi Set.univ (fun _ : ι => T)).Finite :=
    Set.Finite.pi (fun _ => hT)
  have hint : IntegrableOn f (Set.pi Set.univ (fun _ : ι => T))
      (Measure.pi (fun _ : ι => referenceMarks κ n)) := IntegrableOn.of_finite hfin
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hint

/-- Arbitrary mark functions have the explicit six-atom reference integral. -/
-- @node: reference_marks_integral
lemma reference_marks_integral (hκ : κ.Valid) (hn : 2 ≤ n) (f : Bool × ℝ → ℝ) :
    (∫ z, f z ∂referenceMarks κ n) =
      lowerP0 * ((lowerRare κ n/2)*f (true, lowerAmplitude κ n) +
        (lowerRare κ n/2)*f (true, -lowerAmplitude κ n) + (1-lowerRare κ n)*f (true, 0)) +
      (1-lowerP0) * ((lowerRare κ n/2)*f (false, lowerAmplitude κ n) +
        (lowerRare κ n/2)*f (false, -lowerAmplitude κ n) + (1-lowerRare κ n)*f (false, 0)) := by
  have hr := (lower_rare_scale κ n hκ hn).2.1
  have hr0 : 0 ≤ lowerRare κ n := by
    unfold lowerRare
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (lower_rare_scale κ n hκ hn).1.le _)
  have hi (a : ℝ) (w : ℝ) (b : Bool) :
      Integrable (fun y => f (b,y)) (ENNReal.ofReal w • Measure.dirac a) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have href : Integrable f (referenceMarks κ n) := by
    have hfin : ((Set.univ : Set Bool) ×ˢ
        {lowerAmplitude κ n, -lowerAmplitude κ n, 0}).Finite := Set.toFinite _ |>.prod (by simp)
    have hf : IntegrableOn f _ (referenceMarks κ n) := IntegrableOn.of_finite hfin
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
      (reference_marks_finite_support κ n hκ hn)] at hf
  unfold referenceMarks at href ⊢
  rw [integral_prod _ href]
  have inner (b : Bool) :
      (∫ y, f (b,y) ∂(ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (lowerAmplitude κ n) +
        ENNReal.ofReal (lowerRare κ n/2) • Measure.dirac (-lowerAmplitude κ n) +
        ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0)) =
      (lowerRare κ n/2)*f (b, lowerAmplitude κ n) +
        (lowerRare κ n/2)*f (b, -lowerAmplitude κ n) + (1-lowerRare κ n)*f (b, 0) := by
    rw [integral_add_measure ((hi _ _ b).add_measure (hi _ _ b)) (hi _ _ b),
      integral_add_measure (hi _ _ b) (hi _ _ b)]
    simp [integral_smul_measure, ENNReal.toReal_ofReal (by positivity : 0 ≤ lowerRare κ n/2),
      ENNReal.toReal_ofReal (sub_nonneg.mpr hr)]
  simp_rw [inner]
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  norm_num [integral_smul_measure, lowerP0]

/-- A fixed latent sign gives a normalized one-record conditional mark likelihood. -/
-- @node: lower_density_integral_one
lemma lower_density_integral_one (hκ : κ.Valid) (hn : 2 ≤ n)
    (s t : ℝ) (v : Signs κ n) (x : unitInterval) :
    (∫ z, lowerDensity κ n s t v x z ∂referenceMarks κ n) = 1 := by
  rw [reference_marks_integral κ n hκ hn]
  simp only [lowerDensity, markU, markV, lowerP0, Bool.false_eq_true, ↓reduceIte,
    neg_div, zero_div, mul_zero, zero_mul, add_zero]
  ring

/-- Averaged likelihoods on arbitrary record subsets retain their unit mass. -/
-- @node: subset_density_integral_one
lemma subset_density_integral_one (hκ : κ.Valid) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (x : Fin n → unitInterval) (s t : ℝ) :
    (∫ z, subsetDensity κ n S x s t z
      ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1 := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hc : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold subsetDensity
  rw [integral_const_mul, integral_finsetSum _
    (fun v _ => reference_marks_pi_integrable κ n hκ hn _)]
  have hp (v : Signs κ n) :
      (∫ z, ∏ i ∈ S, lowerDensity κ n s t v (x i) (z i)
        ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1 := by
    have he (z : Fin n → Bool × ℝ) :
        (∏ i ∈ S, lowerDensity κ n s t v (x i) (z i)) =
        ∏ i, if i ∈ S then lowerDensity κ n s t v (x i) (z i) else 1 := by
      simp [Finset.prod_ite_mem]
    simp_rw [he]
    change (∫ z, ∏ i, (fun y : Bool × ℝ =>
      if i ∈ S then lowerDensity κ n s t v (x i) y else 1) (z i)
      ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => referenceMarks κ n)
      (fun i (y : Bool × ℝ) => if i ∈ S then lowerDensity κ n s t v (x i) y else 1)]
    apply Finset.prod_eq_one
    intro i _
    split_ifs
    · exact lower_density_integral_one κ n hκ hn s t v (x i)
    · simp
  simp [hp, hc]

/-- Subset likelihoods are nonnegative on the reference support throughout the amplitude rectangle. -/
-- @node: subset_density_nonneg_ae
lemma subset_density_nonneg_ae (hκ : κ.Valid) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (x : Fin n → unitInterval) (s t : ℝ)
    (hs : |s| ≤ lowerA κ n) (ht : |t| ≤ lowerB κ n) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n),
      0 ≤ subsetDensity κ n S x s t z := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hz (i : Fin n) : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n),
      |t*markV κ n (z i).2| ≤ 1/4 :=
    (measurePreserving_eval (fun _ : Fin n => referenceMarks κ n) i).quasiMeasurePreserving.ae
      (reference_markV_scaled_bound κ n hκ hn t ht)
  filter_upwards [ae_all_iff.mpr hz] with z hz
  unfold subsetDensity
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro v _
  apply Finset.prod_nonneg
  intro i _
  exact (by norm_num : (0 : ℝ) ≤ 1/2).trans
    (lower_density_half_le κ n (by omega) s t
      (hs.trans (lower_scale_small κ n hκ hn).2.1.2) v (x i) (z i) (hz i))

/-- On the finite reference product, almost-everywhere densities obey the usual affinity identity. -/
-- @node: reference_hellinger_affinity_identity
lemma reference_hellinger_affinity_identity (hκ : κ.Valid) (hn : 2 ≤ n)
    (f g : (Fin n → Bool × ℝ) → ℝ)
    (hf0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ f z)
    (hg0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ g z)
    (hf1 : (∫ z, f z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1)
    (hg1 : (∫ z, g z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n)) f g =
      2*(1-Causalean.Stat.densityAffinity (Measure.pi (fun _ : Fin n => referenceMarks κ n)) f g) := by
  unfold Causalean.Stat.hellingerSqDensity Causalean.Stat.densityAffinity
  have he : (fun z => (Real.sqrt (f z)-Real.sqrt (g z))^2) =ᵐ[
      Measure.pi (fun _ : Fin n => referenceMarks κ n)]
      (fun z => f z+g z-2*Real.sqrt (f z*g z)) := by
    filter_upwards [hf0, hg0] with z hf hg
    rw [Real.sqrt_mul hf]
    nlinarith [Real.sq_sqrt hf, Real.sq_sqrt hg]
  rw [integral_congr_ae he, integral_sub
    (reference_marks_pi_integrable κ n hκ hn _) (reference_marks_pi_integrable κ n hκ hn _),
    integral_add (reference_marks_pi_integrable κ n hκ hn _)
      (reference_marks_pi_integrable κ n hκ hn _), integral_const_mul, hf1, hg1]
  ring

/-- Normalized reference densities have affinity in the unit interval. -/
-- @node: reference_affinity_bounds
lemma reference_affinity_bounds (hκ : κ.Valid) (hn : 2 ≤ n)
    (f g : (Fin n → Bool × ℝ) → ℝ)
    (hf0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ f z)
    (hg0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ g z)
    (hf1 : (∫ z, f z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1)
    (hg1 : (∫ z, g z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1) :
    0 ≤ Causalean.Stat.densityAffinity (Measure.pi (fun _ : Fin n => referenceMarks κ n)) f g ∧
      Causalean.Stat.densityAffinity (Measure.pi (fun _ : Fin n => referenceMarks κ n)) f g ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => Real.sqrt_nonneg _)
  · have hH : 0 ≤ Causalean.Stat.hellingerSqDensity
        (Measure.pi (fun _ : Fin n => referenceMarks κ n)) f g :=
      integral_nonneg (fun _ => sq_nonneg _)
    rw [reference_hellinger_affinity_identity κ n hκ hn f g hf0 hg0 hf1 hg1] at hH
    linarith

/-- Affinity multiplies across disjoint record blocks, including blocks with internal sign sharing. -/
-- @node: reference_affinity_disjoint_blocks
lemma reference_affinity_disjoint_blocks (hκ : κ.Valid) (hn : 2 ≤ n)
    {η : Type*} [DecidableEq η] (S : Finset η) (A : η → Finset (Fin n))
    (f g : η → (Fin n → Bool × ℝ) → ℝ)
    (hd : Set.PairwiseDisjoint (S : Set η) A)
    (hfm : ∀ k ∈ S, Measurable (f k)) (hgm : ∀ k ∈ S, Measurable (g k))
    (hfd : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → f k v = f k w)
    (hgd : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → g k v = g k w)
    (hf0 : ∀ k ∈ S, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ f k z)
    (hg0 : ∀ k ∈ S, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ g k z) :
    Causalean.Stat.densityAffinity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (fun z => ∏ k ∈ S, f k z) (fun z => ∏ k ∈ S, g k z) =
      ∏ k ∈ S, Causalean.Stat.densityAffinity
        (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  unfold Causalean.Stat.densityAffinity
  have he : (fun z => Real.sqrt ((∏ k ∈ S, f k z)*(∏ k ∈ S, g k z))) =ᵐ[
      Measure.pi (fun _ : Fin n => referenceMarks κ n)]
      (fun z => ∏ k ∈ S, Real.sqrt (f k z*g k z)) := by
    have hfa : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), ∀ k ∈ S, 0 ≤ f k z :=
      (ae_ball_iff S.finite_toSet.countable).mpr hf0
    have hga : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), ∀ k ∈ S, 0 ≤ g k z :=
      (ae_ball_iff S.finite_toSet.countable).mpr hg0
    filter_upwards [hfa, hga] with z hf hg
    rw [← Finset.prod_mul_distrib]
    exact Real.sqrt_prod _ (fun k hk => mul_nonneg (hf k hk) (hg k hk))
  rw [integral_congr_ae he]
  apply integral_disjoint_coordinate_blocks _ S A _ hd
  · intro k hk
    exact ((hfm k hk).mul (hgm k hk)).sqrt
  · intro k hk v w ha
    rw [hfd k hk v w ha, hgd k hk v w ha]

/-- Tensorized normalized component likelihoods have Hellinger loss at most the sum of block losses. -/
-- @node: reference_hellinger_disjoint_blocks_le_sum
lemma reference_hellinger_disjoint_blocks_le_sum (hκ : κ.Valid) (hn : 2 ≤ n)
    {η : Type*} [DecidableEq η] (S : Finset η) (A : η → Finset (Fin n))
    (f g : η → (Fin n → Bool × ℝ) → ℝ)
    (hd : Set.PairwiseDisjoint (S : Set η) A)
    (hfm : ∀ k ∈ S, Measurable (f k)) (hgm : ∀ k ∈ S, Measurable (g k))
    (hfd : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → f k v = f k w)
    (hgd : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → g k v = g k w)
    (hf0 : ∀ k ∈ S, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ f k z)
    (hg0 : ∀ k ∈ S, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ g k z)
    (hf1 : ∀ k ∈ S, (∫ z, f k z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1)
    (hg1 : ∀ k ∈ S, (∫ z, g k z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1) :
    Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => referenceMarks κ n))
      (fun z => ∏ k ∈ S, f k z) (fun z => ∏ k ∈ S, g k z) ≤
      ∑ k ∈ S, Causalean.Stat.hellingerSqDensity
        (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k) := by
  classical
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hp0 (F : η → (Fin n → Bool × ℝ) → ℝ)
      (hF : ∀ k ∈ S, ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ F k z) :
      ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n), 0 ≤ ∏ k ∈ S, F k z := by
    filter_upwards [(ae_ball_iff S.finite_toSet.countable).mpr hF] with z hz
    exact Finset.prod_nonneg hz
  have hp1 (F : η → (Fin n → Bool × ℝ) → ℝ)
      (hM : ∀ k ∈ S, Measurable (F k))
      (hD : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → F k v = F k w)
      (h1 : ∀ k ∈ S, (∫ z, F k z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1) :
      (∫ z, ∏ k ∈ S, F k z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n)) = 1 := by
    rw [integral_disjoint_coordinate_blocks _ S A F hd hM hD]
    exact Finset.prod_eq_one h1
  rw [reference_hellinger_affinity_identity κ n hκ hn _ _ (hp0 f hf0) (hp0 g hg0)
    (hp1 f hfm hfd hf1) (hp1 g hgm hgd hg1),
    reference_affinity_disjoint_blocks κ n hκ hn S A f g hd hfm hgm hfd hgd hf0 hg0]
  have ha (k : S) := reference_affinity_bounds κ n hκ hn (f k) (g k)
    (hf0 k k.property) (hg0 k k.property) (hf1 k k.property) (hg1 k k.property)
  have hu := Causalean.Stat.one_sub_prod_le_sum
    (fun k : S => Causalean.Stat.densityAffinity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k))
    (fun k => (ha k).1) (fun k => (ha k).2)
  rw [S.prod_coe_sort (fun k => Causalean.Stat.densityAffinity
    (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k)),
    S.sum_coe_sort (fun k => 1-Causalean.Stat.densityAffinity
      (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k))] at hu
  calc
    _ ≤ 2*(∑ k ∈ S, (1-Causalean.Stat.densityAffinity
        (Measure.pi (fun _ : Fin n => referenceMarks κ n)) (f k) (g k))) := by linarith
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact (reference_hellinger_affinity_identity κ n hκ hn _ _
        (hf0 k hk) (hg0 k hk) (hf1 k hk) (hg1 k hk)).symm

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
