module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainSquareIntegrability
public import Mathlib.Probability.Independence.Basic

/-! Integral transport and observable role-mean assembly for equation (21).
The clipped histogram statistics have finite range, so their integrability requires no
additional premise on the observed law or trained realization. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A measurable statistic with finite range is integrable under any finite measure. -/
-- @node: integrable_of_measurable_finite_range
lemma integrable_of_measurable_finite_range {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → E) (hm : Measurable f) (hf : (Set.range f).Finite) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.isBounded.exists_norm_le
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC _ ⟨x, rfl⟩))

/-- Selecting any one evaluation record preserves the observed law. -/
-- @node: eval_record_measurePreserving
lemma eval_record_measurePreserving (P : ObsLaw) (m : ℕ) (r : Fin 12) (i : Fin m) :
    MeasurePreserving (fun eval : EvalData m => eval r i) (evalLaw P m) P.law := by
  exact (measurePreserving_eval (fun _ : Fin m => P.law) i).comp
    (measurePreserving_eval (fun _ : Fin 12 => Measure.pi (fun _ : Fin m => P.law)) r)

/-- Integrating a statistic of one evaluation record gives its observed-law mean. -/
-- @node: integral_eval_record
lemma integral_eval_record {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (P : ObsLaw) (m : ℕ) (r : Fin 12) (i : Fin m)
    (f : Omega → E) (hf : AEStronglyMeasurable f P.law) :
    (∫ eval, f (eval r i) ∂evalLaw P m) = ∫ o, f o ∂P.law := by
  have hp := eval_record_measurePreserving P m r i
  have h := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hf)
  rw [hp.map_eq] at h
  exact h.symm

/-- The clipped outcome coefficient residual is integrable for every observed law. -/
-- @node: integrable_Vres
lemma integrable_Vres (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J : ℕ) (a : Bool) : Integrable (Vres train mx my J a) P.law := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  exact integrable_of_measurable_finite_range P.law _ (by fun_prop)
    (finite_range_Vres train mx my J a)

/-- First-role averages are integrable conditional on any trained realization. -/
-- @node: integrable_Uone
lemma integrable_Uone (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J : ℕ) (b : Fin 2) (a : Bool) :
    Integrable (fun eval => Uone train mx my J eval b a) (evalLaw P m) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  exact integrable_of_measurable_finite_range (evalLaw P m) _ (by fun_prop)
    (finite_range_Uone train mx my J b a)

/-- Second-role corrections are integrable at every finite collection of ranks. -/
-- @node: integrable_Utwo
lemma integrable_Utwo (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my L T J : ℕ) (kt : ℕ → ℕ) (b : Fin 2) (a : Bool) :
    Integrable (fun eval => Utwo train mx my L T J kt eval b a) (evalLaw P m) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  exact integrable_of_measurable_finite_range (evalLaw P m) _ (by fun_prop)
    (finite_range_Utwo train mx my L T J kt b a)

/-- Third-role corrections are integrable at every finite correction rank. -/
-- @node: integrable_Uthree
lemma integrable_Uthree (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J q : ℕ) (b : Fin 2) (a : Bool) :
    Integrable (fun eval => Uthree train mx my J q eval b a) (evalLaw P m) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  exact integrable_of_measurable_finite_range (evalLaw P m) _ (by fun_prop)
    (finite_range_Uthree train mx my J q b a)

/-- The positive-size first-role average has exactly the outcome residual's mean. -/
-- @node: integral_Uone_eq_integral_Vres
lemma integral_Uone_eq_integral_Vres (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my J : ℕ) (b : Fin 2) (a : Bool) :
    (∫ eval, Uone train mx my J eval b a ∂evalLaw P m) =
      ∫ o, Vres train mx my J a o ∂P.law := by
  have hv := integrable_Vres P train mx my J a
  have hi (i : Fin m) : Integrable
      (fun eval : EvalData m => Vres train mx my J a (eval (chainRole b 0) i))
      (evalLaw P m) :=
    (eval_record_measurePreserving P m (chainRole b 0) i).integrable_comp_of_integrable hv
  simp only [Uone]
  rw [integral_smul, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_eval_record P m (chainRole b 0) _ _ hv.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

/-- Linearity isolates the three observable role expectations in the signed contrast mean. -/
-- @node: contrastMean_role_decomposition
lemma contrastMean_role_decomposition (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    contrastMean P train mx my L T J q kt =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        ((∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
          (∫ eval, Uone train mx my J eval 0 a ∂evalLaw P m) -
          (∫ eval, Utwo train mx my L T J kt eval 0 a ∂evalLaw P m) +
          (∫ eval, Uthree train mx my J q eval 0 a ∂evalLaw P m)) := by
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  unfold contrastMean coefficientChain
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul]
    have h1 := integrable_Uone P train mx my J 0 a
    have h2 := integrable_Utwo P train mx my L T J kt 0 a
    have h3 := integrable_Uthree P train mx my J q 0 a
    integral_linearity
    simp
  · intro a _
    exact (((integrable_const _).add (integrable_Uone P train mx my J 0 a)).sub
      (integrable_Utwo P train mx my L T J kt 0 a)).add
        (integrable_Uthree P train mx my J q 0 a) |>.smul (if a then (1 : ℝ) else -1)

/-- For positive role size, the first-role term in the contrast mean is the single-record mean. -/
-- @node: contrastMean_first_role_identity
lemma contrastMean_first_role_identity (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    contrastMean P train mx my L T J q kt =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        ((∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
          (∫ o, Vres train mx my J a o ∂P.law) -
          (∫ eval, Utwo train mx my L T J kt eval 0 a ∂evalLaw P m) +
          (∫ eval, Uthree train mx my J q eval 0 a ∂evalLaw P m)) := by
  rw [contrastMean_role_decomposition]
  simp_rw [integral_Uone_eq_integral_Vres P hm train mx my J]

/-- Records from distinct evaluation roles have the independent observed product law. -/
-- @node: eval_record_pair_measurePreserving
lemma eval_record_pair_measurePreserving (P : ObsLaw) (m : ℕ)
    (r s : Fin 12) (hrs : r ≠ s) (i j : Fin m) :
    MeasurePreserving (fun eval : EvalData m => (eval r i, eval s j))
      (evalLaw P m) (P.law.prod P.law) := by
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hind : iIndepFun (fun r : Fin 12 => fun eval : EvalData m => eval r)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hp := (hind.indepFun hrs).comp (measurable_pi_apply i) (measurable_pi_apply j)
  refine ⟨by fun_prop, ?_⟩
  have hmap := hp.map_prod_eq_prod_map_map
    (eval_record_measurePreserving P m r i).aemeasurable
    (eval_record_measurePreserving P m s j).aemeasurable
  simpa only [(eval_record_measurePreserving P m r i).map_eq,
    (eval_record_measurePreserving P m s j).map_eq] using hmap

/-- A two-record statistic in separate roles integrates against the observed product law. -/
-- @node: integral_eval_record_pair
lemma integral_eval_record_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (P : ObsLaw) (m : ℕ) (r s : Fin 12) (hrs : r ≠ s)
    (i j : Fin m) (f : Omega × Omega → E)
    (hf : AEStronglyMeasurable f (P.law.prod P.law)) :
    (∫ eval, f (eval r i, eval s j) ∂evalLaw P m) =
      ∫ o, f o ∂P.law.prod P.law := by
  have hp := eval_record_pair_measurePreserving P m r s hrs i j
  have h := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hf)
  rw [hp.map_eq] at h
  exact h.symm

/-- Normalization cancels the number of ordered pairs in a positive-size cross-role average. -/
-- @node: integral_cross_role_pair_average
lemma integral_cross_role_pair_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (r s : Fin 12) (hrs : r ≠ s) (f : Omega × Omega → E)
    (hf : Integrable f (P.law.prod P.law)) :
    (∫ eval, (m : ℝ) ^ (-2 : ℤ) •
      ∑ i : Fin m, ∑ j : Fin m, f (eval r i, eval s j) ∂evalLaw P m) =
      ∫ o, f o ∂P.law.prod P.law := by
  have hi (i j : Fin m) : Integrable
      (fun eval : EvalData m => f (eval r i, eval s j)) (evalLaw P m) :=
    (eval_record_pair_measurePreserving P m r s hrs i j).integrable_comp_of_integrable hf
  rw [integral_smul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j),
    integral_eval_record_pair P m r s hrs _ _ f hf.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscale : (m : ℝ) ^ (-2 : ℤ) * ((m : ℝ) * (m : ℝ)) = 1 := by
    simp only [zpow_neg, zpow_ofNat, pow_two]
    field_simp
  rw [hscale, one_smul]

/-- Band projections preserve finite sums of coefficient vectors. -/
-- @node: Qband_finsetSum
lemma Qband_finsetSum {ι : Type*} (L J t : ℕ) (S : Finset ι) (f : ι → Hj J) :
    Qband L J t (∑ i ∈ S, f i) = ∑ i ∈ S, Qband L J t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa only [zero_smul] using Qband_smul L J t 0 (0 : Hj J)
  | @insert i S hi ih => simp only [Finset.sum_insert hi, Qband_add, ih]

/-- Projected second-role kernels are integrable because their factors have finite range. -/
-- @node: integrable_projected_second_role_kernel
lemma integrable_projected_second_role_kernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L J t k : ℕ) (a : Bool) :
    Integrable (fun o : Omega × Omega => Qband L J t
      ((Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2)) •
        Vres train mx my J a o.2)) (P.law.prod P.law) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
  apply chain_finite_range_comp (g := Qband L J t)
  apply chain_finite_range_binary (op := fun r v => r • v)
  · apply chain_finite_range_binary (op := (· * ·))
    · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.fst
    · exact chain_finite_range_precomp (finite_range_covariateKernel k)
        (fun o : Omega × Omega => (X o.1, X o.2))
  · exact chain_finite_range_precomp (finite_range_Vres train mx my J a) Prod.snd

/-- The multiband second-role expectation is the sum of independent two-observation kernel means. -/
-- @node: integral_Utwo_eq_sum_product_integral
lemma integral_Utwo_eq_sum_product_integral (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my L T J : ℕ) (kt : ℕ → ℕ)
    (b : Fin 2) (a : Bool) :
    (∫ eval, Utwo train mx my L T J kt eval b a ∂evalLaw P m) =
      ∑ t ∈ Finset.range (T + 1), ∫ o : Omega × Omega, Qband L J t
        ((Rres train mx a o.1 * covariateKernel (kt t) (X o.1) (X o.2)) •
          Vres train mx my J a o.2) ∂P.law.prod P.law := by
  have hrs : chainRole b 1 ≠ chainRole b 2 := by
    fin_cases b <;> decide
  let F (t : ℕ) (o : Omega × Omega) : Hj J := Qband L J t
    ((Rres train mx a o.1 * covariateKernel (kt t) (X o.1) (X o.2)) •
      Vres train mx my J a o.2)
  have hi (t : ℕ) : Integrable (F t) (P.law.prod P.law) :=
    integrable_projected_second_role_kernel P train mx my L J t (kt t) a
  let A (t : ℕ) (eval : EvalData m) : Hj J :=
    (m : ℝ) ^ (-2 : ℤ) • ∑ i : Fin m, ∑ j : Fin m,
      F t (eval (chainRole b 1) i, eval (chainRole b 2) j)
  have hij (t : ℕ) (i j : Fin m) : Integrable
      (fun eval : EvalData m => F t (eval (chainRole b 1) i, eval (chainRole b 2) j))
      (evalLaw P m) :=
    (eval_record_pair_measurePreserving P m _ _ hrs i j).integrable_comp_of_integrable (hi t)
  have ht (t : ℕ) : Integrable (A t) (evalLaw P m) :=
    (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hij t i j))).smul ((m : ℝ) ^ (-2 : ℤ))
  have heq (eval : EvalData m) : Utwo train mx my L T J kt eval b a =
      ∑ t ∈ Finset.range (T + 1), A t eval := by
    simp only [Utwo, Qband_finsetSum]
    rw [Finset.smul_sum]
  simp_rw [heq]
  change (∫ eval, ∑ t ∈ Finset.range (T + 1), A t eval ∂evalLaw P m) =
    ∑ t ∈ Finset.range (T + 1), ∫ o, F t o ∂P.law.prod P.law
  rw [integral_finsetSum (Finset.range (T + 1)) (fun t _ => ht t)]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_cross_role_pair_average P hm _ _ hrs (F t) (hi t)

/-- At positive role size, the first two mean corrections are single and pair integrals. -/
-- @node: contrastMean_second_role_identity
lemma contrastMean_second_role_identity (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    contrastMean P train mx my L T J q kt =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        ((∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
          (∫ o, Vres train mx my J a o ∂P.law) -
          (∑ t ∈ Finset.range (T + 1), ∫ o : Omega × Omega, Qband L J t
            ((Rres train mx a o.1 * covariateKernel (kt t) (X o.1) (X o.2)) •
              Vres train mx my J a o.2) ∂P.law.prod P.law) +
          (∫ eval, Uthree train mx my J q eval 0 a ∂evalLaw P m)) := by
  rw [contrastMean_first_role_identity P hm]
  simp_rw [integral_Utwo_eq_sum_product_integral P hm train mx my L T J kt]

/-- Three records in distinct evaluation roles have the independent observed triple law. -/
-- @node: eval_record_triple_measurePreserving
lemma eval_record_triple_measurePreserving (P : ObsLaw) (m : ℕ)
    (r s t : Fin 12) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (i j k : Fin m) :
    MeasurePreserving (fun eval : EvalData m => ((eval r i, eval s j), eval t k))
      (evalLaw P m) ((P.law.prod P.law).prod P.law) := by
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hind : iIndepFun (fun r : Fin 12 => fun eval : EvalData m => eval r)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hp := (hind.indepFun_prodMk (fun _ => by fun_prop) r s t hrt hst).comp
    (show Measurable (fun o : (Fin m → Omega) × (Fin m → Omega) =>
      (o.1 i, o.2 j)) by fun_prop) (measurable_pi_apply k)
  refine ⟨by fun_prop, ?_⟩
  have hmap := hp.map_prod_eq_prod_map_map
    (eval_record_pair_measurePreserving P m r s hrs i j).aemeasurable
    (eval_record_measurePreserving P m t k).aemeasurable
  simpa only [(eval_record_pair_measurePreserving P m r s hrs i j).map_eq,
    (eval_record_measurePreserving P m t k).map_eq] using hmap

/-- A three-record statistic from separate roles integrates against the observed triple law. -/
-- @node: integral_eval_record_triple
lemma integral_eval_record_triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (P : ObsLaw) (m : ℕ) (r s t : Fin 12)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (i j k : Fin m)
    (f : (Omega × Omega) × Omega → E)
    (hf : AEStronglyMeasurable f ((P.law.prod P.law).prod P.law)) :
    (∫ eval, f ((eval r i, eval s j), eval t k) ∂evalLaw P m) =
      ∫ o, f o ∂(P.law.prod P.law).prod P.law := by
  have hp := eval_record_triple_measurePreserving P m r s t hrs hrt hst i j k
  have h := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hf)
  rw [hp.map_eq] at h
  exact h.symm

/-- Normalization cancels all ordered triples in a positive-size cross-role average. -/
-- @node: integral_cross_role_triple_average
lemma integral_cross_role_triple_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (r s t : Fin 12) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (f : (Omega × Omega) × Omega → E)
    (hf : Integrable f ((P.law.prod P.law).prod P.law)) :
    (∫ eval, (m : ℝ) ^ (-3 : ℤ) •
      ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
        f ((eval r i, eval s j), eval t k) ∂evalLaw P m) =
      ∫ o, f o ∂(P.law.prod P.law).prod P.law := by
  have hi (i j k : Fin m) : Integrable
      (fun eval : EvalData m => f ((eval r i, eval s j), eval t k)) (evalLaw P m) :=
    (eval_record_triple_measurePreserving P m r s t hrs hrt hst i j k).integrable_comp_of_integrable hf
  rw [integral_smul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi _ j k)),
    integral_finsetSum _ (fun k _ => hi _ _ k),
    integral_eval_record_triple P m r s t hrs hrt hst _ _ _ f hf.aestronglyMeasurable]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscale : (m : ℝ) ^ (-3 : ℤ) * ((m : ℝ) * ((m : ℝ) * (m : ℝ))) = 1 := by
    simp only [zpow_neg, zpow_ofNat, pow_succ, pow_two]
    field_simp
  rw [hscale, one_smul]

/-- Third-role kernels are integrable because every clipped histogram factor has finite range. -/
-- @node: integrable_third_role_kernel
lemma integrable_third_role_kernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) :
    Integrable (fun o : (Omega × Omega) × Omega =>
      (Rres train mx a o.1.1 * covariateKernel q (X o.1.1) (X o.1.2) *
        Rres train mx a o.1.2 * covariateKernel q (X o.1.2) (X o.2)) •
        Vres train mx my J a o.2) ((P.law.prod P.law).prod P.law) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
  apply chain_finite_range_binary (op := fun r v => r • v)
  · apply chain_finite_range_binary (op := (· * ·))
    · apply chain_finite_range_binary (op := (· * ·))
      · apply chain_finite_range_binary (op := (· * ·))
        · exact chain_finite_range_precomp (finite_range_Rres train mx a) (fun o : (Omega × Omega) × Omega => o.1.1)
        · exact chain_finite_range_precomp (finite_range_covariateKernel q)
            (fun o : (Omega × Omega) × Omega => (X o.1.1, X o.1.2))
      · exact chain_finite_range_precomp (finite_range_Rres train mx a) (fun o : (Omega × Omega) × Omega => o.1.2)
    · exact chain_finite_range_precomp (finite_range_covariateKernel q)
        (fun o : (Omega × Omega) × Omega => (X o.1.2, X o.2))
  · exact chain_finite_range_precomp (finite_range_Vres train mx my J a) Prod.snd

/-- The third-role expectation is exactly its independent three-observation kernel mean. -/
-- @node: integral_Uthree_eq_triple_product_integral
lemma integral_Uthree_eq_triple_product_integral (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my J q : ℕ) (b : Fin 2) (a : Bool) :
    (∫ eval, Uthree train mx my J q eval b a ∂evalLaw P m) =
      ∫ o : (Omega × Omega) × Omega,
        (Rres train mx a o.1.1 * covariateKernel q (X o.1.1) (X o.1.2) *
          Rres train mx a o.1.2 * covariateKernel q (X o.1.2) (X o.2)) •
          Vres train mx my J a o.2 ∂(P.law.prod P.law).prod P.law := by
  have hrs : chainRole b 3 ≠ chainRole b 4 := by fin_cases b <;> decide
  have hrt : chainRole b 3 ≠ chainRole b 5 := by fin_cases b <;> decide
  have hst : chainRole b 4 ≠ chainRole b 5 := by fin_cases b <;> decide
  unfold Uthree
  exact integral_cross_role_triple_average P hm _ _ _ hrs hrt hst
    (fun o : (Omega × Omega) × Omega =>
      (Rres train mx a o.1.1 * covariateKernel q (X o.1.1) (X o.1.2) *
        Rres train mx a o.1.2 * covariateKernel q (X o.1.2) (X o.2)) •
        Vres train mx my J a o.2)
    (integrable_third_role_kernel P train mx my J q a)

/-- All three observable role expectations in the contrast mean reduce to product-law integrals. -/
-- @node: contrastMean_product_law_identity
lemma contrastMean_product_law_identity (P : ObsLaw) {m : ℕ} (hm : 0 < m)
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    contrastMean P train mx my L T J q kt =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        ((∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
          (∫ o, Vres train mx my J a o ∂P.law) -
          (∑ t ∈ Finset.range (T + 1), ∫ o : Omega × Omega, Qband L J t
            ((Rres train mx a o.1 * covariateKernel (kt t) (X o.1) (X o.2)) •
              Vres train mx my J a o.2) ∂P.law.prod P.law) +
          (∫ o : (Omega × Omega) × Omega,
            (Rres train mx a o.1.1 * covariateKernel q (X o.1.1) (X o.1.2) *
              Rres train mx a o.1.2 * covariateKernel q (X o.1.2) (X o.2)) •
              Vres train mx my J a o.2 ∂(P.law.prod P.law).prod P.law)) := by
  rw [contrastMean_second_role_identity P hm]
  simp_rw [integral_Uthree_eq_triple_product_integral P hm train mx my J q]

end CausalSmith.Stat.DensityEffectRoughNull
