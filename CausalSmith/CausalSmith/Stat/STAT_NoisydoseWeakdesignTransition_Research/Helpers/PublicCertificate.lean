module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.CertificateMoments
public import Mathlib.Probability.Moments.Variance

/-! Helpers — PublicCertificate -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Flooring at half the public lower bound cannot increase denominator error. [Under the stated conditions](hyp:hb,hD). [This is the stated conclusion](goal). -/
-- @node: denominator_floor_error
lemma denominator_floor_error (b D d : ℝ) (hb : 0 < b) (hD : b ≤ D) :
    0 < max d (b/2) ∧ |max d (b/2) - D| ≤ |d-D| := by
  refine ⟨lt_of_lt_of_le (by linarith) (le_max_right _ _), ?_⟩
  have hfloor : b/2 ≤ D := by linarith
  simpa only [max_eq_left hfloor] using abs_max_sub_max_le_abs d D (b/2)

/-- Clipping to the public mean range contracts distance to any mean in that range. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hm). -/
-- @node: public_mean_clip_error
lemma public_mean_clip_error (z m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1) :
    |max 0 (min 1 z) - m| ≤ |z-m| := by
  have h := Set.abs_projIcc_sub_projIcc (c := z) (d := m)
    (zero_le_one : (0 : ℝ) ≤ 1)
  simpa only [Set.coe_projIcc, min_eq_right hm.2, max_eq_right hm.1] using h

/-- The public floor and mean-range projection give the deterministic ratio stability bound. [Under the stated conditions](hyp:hb,hD,hm). [This is the stated conclusion](goal). -/
-- @node: clipped_ratio_error
lemma clipped_ratio_error (b D M d u : ℝ) (hb : 0 < b) (hD : b ≤ D)
    (hm : M/D ∈ Icc (0 : ℝ) 1) :
    |max 0 (min 1 (u / max d (b/2))) - M/D| ≤
      (2/b) * (|u-M| + |d-D|) := by
  obtain ⟨hdpos, hderr⟩ := denominator_floor_error b D d hb hD
  have hDpos : 0 < D := hb.trans_le hD
  have hmabs : |M/D| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hm.1])]
    linarith [hm.2]
  have hid : u / max d (b/2) - M/D =
      ((u-M) + (M/D)*(D-max d (b/2))) / max d (b/2) := by
    field_simp
    <;> ring
  apply (public_mean_clip_error _ _ hm).trans
  rw [hid, abs_div, abs_of_pos hdpos]
  have hnum : |(u-M) + (M/D)*(D-max d (b/2))| ≤ |u-M| + |d-D| := by
    calc
      _ ≤ |u-M| + |(M/D)*(D-max d (b/2))| := abs_add_le _ _
      _ = |u-M| + |M/D| * |max d (b/2)-D| := by rw [abs_mul, abs_sub_comm D]
      _ ≤ |u-M| + 1 * |d-D| := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (|u-M| + |d-D|) / max d (b/2) := div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ (|u-M| + |d-D|) / (b/2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (le_max_right _ _)
    _ = _ := by field_simp

/-- The actual stratum estimator obeys the deterministic public ratio error bound. [Under the stated conditions](hyp:hb,hD,hm). [This is the stated conclusion](goal). -/
-- @node: muhat_error_le
lemma muhat_error_le (K : ClassConstants) (kappa : ℝ) (n : ℕ) (q : WeightPair)
    (data : Fin n → Obs) (x : Bool) (D M : ℝ)
    (hb : 0 < bq K kappa q.q) (hD : bq K kappa q.q ≤ D)
    (hm : M/D ∈ Icc (0 : ℝ) 1) :
    |muhat K kappa n data x q - M/D| ≤
      (2 / bq K kappa q.q) * (|Mhat n data x q-M| + |Dhat n data x q-D|) := by
  exact clipped_ratio_error _ _ _ _ _ hb hD hm

/-- Each modulo-three block contains at least the quotient of the sample size by three. [Under the stated conditions](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: splitBlock_card_lower
lemma splitBlock_card_lower (n r : ℕ) (hr : r < 3) :
    n/3 ≤ (splitBlock n r).card := by
  let f : Fin (n/3) → Fin n := fun j => ⟨3*j.val+r, by
    have hj := j.isLt
    omega⟩
  have hmap : Set.MapsTo f (Finset.univ : Finset (Fin (n/3))) (splitBlock n r) := by
    intro j hj
    simp only [Finset.mem_coe, splitBlock, Finset.mem_filter, Finset.mem_univ, true_and]
    change (3*j.val+r) % 3 = r
    omega
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin (n/3))) := by
    intro i hi j hj hij
    have heq := congrArg Fin.val hij
    dsimp [f] at heq
    apply Fin.ext
    omega
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card_of_injOn f hmap hinj

/-- For at least three records every split block has at least one fifth of the records. [Under the stated conditions](hyp:hn,hr). [This is the stated conclusion](goal). -/
-- @node: splitBlock_card_fifth
lemma splitBlock_card_fifth (n r : ℕ) (hn : 3 ≤ n) (hr : r < 3) :
    n ≤ 5 * (splitBlock n r).card := by
  have hcard := splitBlock_card_lower n r hr
  omega

/-- The declared estimator's three blocks are all nonempty for sample size at least three. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: blocksNonempty_of_three_le
lemma blocksNonempty_of_three_le (n : ℕ) (hn : 3 ≤ n) : blocksNonempty n := by
  intro r hr
  apply Finset.card_pos.mp
  have hcard := splitBlock_card_lower n r hr
  omega

/-- Each empirical stratum frequency is nonnegative. [This is the stated conclusion](goal). -/
-- @node: phat_nonneg
lemma phat_nonneg (n : ℕ) (data : Fin n → Obs) (x : Bool) :
    0 ≤ phat n data x := by
  unfold phat
  positivity

/-- Frequencies in the first nonempty block sum to one over the two strata. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: phat_sum_eq_one
lemma phat_sum_eq_one (n : ℕ) (hn : 3 ≤ n) (data : Fin n → Obs) :
    (∑ x : Bool, phat n data x) = 1 := by
  have hc : (splitBlock n 0).card ≠ 0 := by
    have h := splitBlock_card_lower n 0 (by omega)
    omega
  have hcR : ((splitBlock n 0).card : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [phat, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hs (i : Fin n) : (∑ x : Bool, if (data i).1 = x then (1 : ℝ) else 0) = 1 := by
    cases h : (data i).1 <;> simp [h]
  simp only [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact div_self hcR

/-- The estimator error splits into a convexly weighted mean error and the stratum-frequency error. [Under the stated conditions](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: weightEstimator_error_decomposition
lemma weightEstimator_error_decomposition (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (n : ℕ) (data : Fin n → Obs) (q : WeightPair) :
    |weightEstimator K kappa n q data - causalTarget E P| ≤
      (∑ x : Bool, phat n data x * |muhat K kappa n data x q - condPotMean E P x a0|) +
      |∑ x : Bool, (phat n data x - strataProb P x) * condPotMean E P x a0| := by
  rw [causalTarget_eq_stratum_sum E P hP.strataPos hP.boundedPO]
  have hid : weightEstimator K kappa n q data -
      (∑ x : Bool, strataProb P x * condPotMean E P x a0) =
      (∑ x : Bool, phat n data x * (muhat K kappa n data x q - condPotMean E P x a0)) +
      (∑ x : Bool, (phat n data x - strataProb P x) * condPotMean E P x a0) := by
    simp only [weightEstimator, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  rw [abs_mul, abs_of_nonneg (phat_nonneg n data x)]

/-- The positive latent weighted mean remains in the public outcome interval. [Under the stated conditions](hyp:hP,hq,hlaw,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: localizedRatio_mem_Icc
lemma localizedRatio_mem_Icc (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (x : Bool) (q : WeightPair)
    (hq : PairAdmissible kappa sigma q) (hlaw : LawAdmissible sigma P q) :
    localizedRatio sigma P x q ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨g, hg, hglaw, hgenv⟩ := hP.weakDesign
  let H := fun t => projectedMean E P (a0+t) x
  let f := fun t => g x t * q.q t
  let ν := volume.restrict (Icc (-1/2 : ℝ) (1/2))
  have hf : Integrable f ν := latent_weight_integrable kappa q.q (g x)
    hq.1 (hg x) hq.2.2.1 hq.2.2.2.1 (hgenv x)
  have hfn : 0 ≤ᵐ[ν] f := by
    filter_upwards [hgenv x, ae_restrict_mem measurableSet_Icc] with t ht hs
    exact mul_nonneg ((mul_nonneg K.clo_pos.le
      (Real.rpow_nonneg (abs_nonneg _) _)).trans ht.1) (hq.2.2.1 t hs)
  have hH : Measurable H := (projectedMean_measurable E P beta
    (hbeta.1) hP.holderMean).comp
      (show Measurable (fun t : ℝ => (a0+t,x)) by fun_prop)
  have hfi : Integrable (fun t => f t * H t) ν := by
    apply hf.mul_bdd (c := 1) hH.aestronglyMeasurable
    filter_upwards [] with t
    have ht := projectedMean_mem_Icc E P hP.meanRange (a0+t) x
    simpa [H, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hLpos : 0 < ∫ t, f t ∂ν := lt_of_lt_of_le (by
    have := hq.2.2.2.2.1
    have := K.clo_pos
    positivity) (latent_weight_lower kappa q.q (g x) hq.1 (hg x)
      hq.2.2.1 hq.2.2.2.1 (hgenv x))
  have heq : localizedRatio sigma P x q = (∫ t, f t * H t ∂ν) / (∫ t, f t ∂ν) := by
    unfold localizedRatio
    rw [populationD_eq_latent E beta kappa sigma P hP x q hq hlaw g hg hglaw hgenv,
      populationM_eq_latent E beta kappa sigma hbeta hkappa hsigma P hP x q hq hlaw
        g hg hglaw hgenv]
    have hp := strataProb_pos P hP.strataPos x
    have hi : (fun t => g x t * (projectedMean E P (a0+t) x * q.q t)) =
        (fun t => f t * H t) := by funext t; dsimp [f, H]; ring
    rw [hi]
    change (strataProb P x * (∫ t, f t * H t ∂ν)) /
      (strataProb P x * (∫ t, f t ∂ν)) = _
    field_simp
  rw [heq]
  constructor
  · apply (le_div_iff₀ hLpos).mpr
    rw [← integral_const_mul]
    apply integral_mono_ae (hf.const_mul _) hfi
    filter_upwards [hfn] with t ht
    have hr := hP.meanRange x _ (Set.projIcc 0 1 zero_le_one (a0+t)).property
    change projectedMean E P (a0+t) x ∈ Icc (0 : ℝ) 1 at hr
    dsimp [H]
    change 0 ≤ f t at ht
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr.1 ht
  · apply (div_le_iff₀ hLpos).mpr
    rw [← integral_const_mul]
    apply integral_mono_ae hfi (hf.const_mul _)
    filter_upwards [hfn] with t ht
    have hr := hP.meanRange x _ (Set.projIcc 0 1 zero_le_one (a0+t)).property
    change projectedMean E P (a0+t) x ∈ Icc (0 : ℝ) 1 at hr
    dsimp [H]
    change 0 ≤ f t at ht
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr.2 ht

/-- Distinct modulo-three blocks are disjoint. [Under the stated conditions](hyp:hrs). [This is the stated conclusion](goal). -/
-- @node: splitBlock_disjoint
lemma splitBlock_disjoint (n r s : ℕ) (hrs : r ≠ s) :
    Disjoint (splitBlock n r) (splitBlock n s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [splitBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hrs (hi.symm.trans hj)

/-- The first-block frequency factors from the absolute error of any other block average. [Under the stated conditions](hyp:hr,f,hf,hp,hA). [This is the stated conclusion](goal). -/
-- @node: phat_block_error_factorization
lemma phat_block_error_factorization (sigma : ℝ) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (n r : ℕ) (hr : r ≠ 0) (x : Bool)
    (f : Obs → ℝ) (hf : Measurable f) (m : ℝ)
    (hp : Integrable (fun data => phat n data x) (experiment n sigma P))
    (hA : Integrable (fun data : Fin n → Obs =>
      |(∑ i ∈ splitBlock n r, f (data i)) / (splitBlock n r).card - m|)
      (experiment n sigma P)) :
    let A := fun data : Fin n → Obs =>
      |(∑ i ∈ splitBlock n r, f (data i)) / (splitBlock n r).card - m|
    Integrable (fun data => phat n data x * A data) (experiment n sigma P) ∧
    (∫ data, phat n data x * A data ∂experiment n sigma P) =
      (∫ data, phat n data x ∂experiment n sigma P) *
      (∫ data, A data ∂experiment n sigma P) := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have h := iid_disjoint_block_averages_indep (obsLaw sigma P) n
    (splitBlock n 0) (splitBlock n r) (splitBlock_disjoint n 0 r hr.symm)
    (fun o : Obs => if o.1 = x then (1 : ℝ) else 0) f
    (Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      measurable_const measurable_const) hf
  have hi := h.comp measurable_id (show Measurable (fun z : ℝ => |z-m|) by fun_prop)
  change IndepFun (fun data => phat n data x)
    (fun data : Fin n → Obs =>
      |(∑ i ∈ splitBlock n r, f (data i)) / (splitBlock n r).card - m|)
    (experiment n sigma P) at hi
  exact ⟨hi.integrable_mul hp hA,
    hi.integral_fun_mul_eq_mul_integral hp.aestronglyMeasurable hA.aestronglyMeasurable⟩

/-- The balanced split converts each moment standard deviation to the public sample-size scale. [Under the stated conditions](hyp:hn,hr,hV). [This is the stated conclusion](goal). -/
-- @node: split_standard_deviation_le
lemma split_standard_deviation_le (n r : ℕ) (hn : 3 ≤ n) (hr : r < 3)
    (V : ℝ) (hV : 0 ≤ V) :
    Real.sqrt (V / (splitBlock n r).card) ≤ 3 * Real.sqrt (V / n) ∧
    Real.sqrt ((1/4 : ℝ) / (splitBlock n r).card) ≤ Real.sqrt (3 / n) := by
  have hN : 0 < ((splitBlock n r).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (blocksNonempty_of_three_le n hn r hr)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hcard : (n : ℝ) ≤ 5 * (splitBlock n r).card := by
    exact_mod_cast splitBlock_card_fifth n r hn hr
  have hv : V / (splitBlock n r).card ≤ 9 * (V/n) := by
    rw [show 9 * (V/(n : ℝ)) = (9*V)/(n : ℝ) by ring]
    apply (div_le_div_iff₀ hN hnR).mpr
    nlinarith
  have hv' : (1/4 : ℝ) / (splitBlock n r).card ≤ 3 / n := by
    apply (div_le_div_iff₀ hN hnR).mpr
    linarith
  refine ⟨?_, Real.sqrt_le_sqrt hv'⟩
  have hs1 := Real.sq_sqrt (div_nonneg hV hN.le)
  have hs2 := Real.sq_sqrt (div_nonneg hV hnR.le)
  have hp1 := Real.sqrt_nonneg (V / (splitBlock n r).card)
  have hp2 := Real.sqrt_nonneg (V / n)
  nlinarith

/-- The split, floor-clipped and projected ratio has the public finite-sample absolute-risk certificate. [Under the stated conditions](hyp:hn,hP,hq,hlaw,hV,hbeta,hkappa,hsigma,hiid). [This is the stated conclusion](goal). -/
-- @node: lem:public-error-certificate
lemma public_error_certificate (E : PathSpace S) (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (n : ℕ) (hn : 3 ≤ n) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (hiid : IIDSampling n sigma P (experiment n sigma P))
    (q : WeightPair) (hq : PairAdmissible kappa sigma q)
    (hlaw : LawAdmissible sigma P q) (hV : VqENN kappa sigma q.ell < ⊤) :
    (∫ data, |weightEstimator K kappa n q data - causalTarget E P| ∂experiment n sigma P) ≤
      Aq K beta kappa n sigma q := by
  have hell := hq.2.1
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  haveI : IsProbabilityMeasure (experiment n sigma P) := by unfold experiment; infer_instance
  let Q := experiment n sigma P
  let B := Bq K beta kappa q.q
  let b := bq K kappa q.q
  let v := pubVq K kappa sigma q.ell
  let eD := fun (x : Bool) data => |Dhat n data x q - populationD sigma P x q|
  let eM := fun (x : Bool) data => |Mhat n data x q - populationM sigma P x q|
  let ep := fun (x : Bool) data => |phat n data x - strataProb P x|
  have hb : 0 < b := by dsimp [b, bq]; exact mul_pos (mul_pos K.pmin_pos K.clo_pos) hq.2.2.2.2.1
  have hblocks := blocksNonempty_of_three_le n hn
  have hDm (x : Bool) := Dhat_population_moments E beta kappa sigma P hP n
    (hblocks 1 (by omega)) x q hell hV
  have hMm (x : Bool) := Mhat_population_moments E beta kappa sigma P hP n
    (hblocks 2 (by omega)) x q hell hV
  have hpm (x : Bool) := phat_population_moments sigma P n (hblocks 0 (by omega)) x
  have hDi (x : Bool) : Integrable (eD x) Q :=
    ((hDm x).1.integrable (by norm_num)).sub (integrable_const _) |>.abs
  have hMi (x : Bool) : Integrable (eM x) Q :=
    ((hMm x).1.integrable (by norm_num)).sub (integrable_const _) |>.abs
  have hpi (x : Bool) : Integrable (ep x) Q :=
    ((hpm x).1.integrable (by norm_num)).sub (integrable_const _) |>.abs
  have hDF (x : Bool) : Integrable (fun data => phat n data x * eD x data) Q ∧
      (∫ data, phat n data x * eD x data ∂Q) = strataProb P x * ∫ data, eD x data ∂Q := by
    have hf : Measurable (fun o : Obs => if o.1 = x then q.ell (o.2.1-a0) else 0) :=
      Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) (by fun_prop) measurable_const
    obtain ⟨hi, he⟩ := phat_block_error_factorization sigma P n 1 (by omega) x _ hf
      (populationD sigma P x q) ((hpm x).1.integrable (by norm_num)) (hDi x)
    refine ⟨hi, ?_⟩
    simpa only [eD, eM, Dhat, Mhat, Q, (hpm x).2.1] using he
  have hMF (x : Bool) : Integrable (fun data => phat n data x * eM x data) Q ∧
      (∫ data, phat n data x * eM x data ∂Q) = strataProb P x * ∫ data, eM x data ∂Q := by
    have hf : Measurable (fun o : Obs => if o.1 = x then o.2.2*q.ell (o.2.1-a0) else 0) :=
      Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) (by fun_prop) measurable_const
    obtain ⟨hi, he⟩ := phat_block_error_factorization sigma P n 2 (by omega) x _ hf
      (populationM sigma P x q) ((hpm x).1.integrable (by norm_num)) (hMi x)
    refine ⟨hi, ?_⟩
    simpa only [eD, eM, Dhat, Mhat, Q, (hpm x).2.1] using he
  have hdev (x : Bool) :
      (∫ data, eD x data ∂Q) ≤ 3 * Real.sqrt (v/n) ∧
      (∫ data, eM x data ∂Q) ≤ 3 * Real.sqrt (v/n) := by
    have he := inverse_moments_expected_abs_error E beta kappa sigma P hP n
      (hblocks 1 (by omega)) (hblocks 2 (by omega)) x q hell hV
    exact ⟨he.1.trans (split_standard_deviation_le n 1 hn (by omega) v ENNReal.toReal_nonneg).1,
      he.2.trans (split_standard_deviation_le n 2 hn (by omega) v ENNReal.toReal_nonneg).1⟩
  have hpdev (x : Bool) : (∫ data, ep x data ∂Q) ≤ Real.sqrt (3/n) := by
    have he := expected_abs_deviation_le_sqrt_variance Q _ (hpm x).1
    rw [(hpm x).2.1] at he
    exact he.trans ((Real.sqrt_le_sqrt (hpm x).2.2).trans
      (split_standard_deviation_le n 0 hn (by omega) v ENNReal.toReal_nonneg).2)
  have hpoint (data : Fin n → Obs) :
      |weightEstimator K kappa n q data - causalTarget E P| ≤
      B + (2/b) * (∑ x : Bool, (phat n data x * eM x data + phat n data x * eD x data)) +
        ∑ x : Bool, ep x data := by
    have he := weightEstimator_error_decomposition E beta kappa sigma P hP n data q
    apply he.trans
    apply add_le_add
    · have hratio (x : Bool) :
          |muhat K kappa n data x q - condPotMean E P x a0| ≤
          B + (2/b) * (eM x data + eD x data) := by
        obtain ⟨hDpos, hD, hbias⟩ := positive_ratio E beta kappa sigma hbeta hkappa hsigma P hP q hq hlaw x
        have hrange := localizedRatio_mem_Icc E beta kappa sigma hbeta hkappa hsigma P hP x q hq hlaw
        have hr := muhat_error_le K kappa n q data x _ _ hb hD hrange
        have ht := abs_sub_le (muhat K kappa n data x q) (localizedRatio sigma P x q)
          (condPotMean E P x a0)
        exact ht.trans (by dsimp [localizedRatio] at *; dsimp [eM, eD, B, b]; linarith)
      calc
        _ ≤ ∑ x : Bool, phat n data x * (B + (2/b)*(eM x data + eD x data)) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hratio x) (phat_nonneg n data x)
        _ = B + (2/b) * (∑ x : Bool, (phat n data x * eM x data + phat n data x * eD x data)) := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, phat_sum_eq_one n hn data, one_mul]
          simp only [Finset.mul_sum]
          apply congrArg (fun z => B+z)
          congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    · apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro x hx
      have hrange := hP.meanRange x a0 (by norm_num [a0])
      have habs : |condPotMean E P x a0| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [hrange.1])]; linarith [hrange.2]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left habs (abs_nonneg _)).trans_eq (mul_one _)
  have htermI (x : Bool) : Integrable (fun data =>
      phat n data x * eM x data + phat n data x * eD x data) Q :=
    (hMF x).1.add (hDF x).1
  have hsumI : Integrable (fun data =>
      ∑ x : Bool, (phat n data x * eM x data + phat n data x * eD x data)) Q :=
    integrable_finsetSum _ (fun x _ => htermI x)
  have hepI : Integrable (fun data => ∑ x : Bool, ep x data) Q :=
    integrable_finsetSum _ (fun x _ => hpi x)
  have hscaledI : Integrable (fun data => (2/b) *
      ∑ x : Bool, (phat n data x * eM x data + phat n data x * eD x data)) Q :=
    hsumI.const_mul (2/b)
  have hbaseI : Integrable (fun data => B + (2/b) *
      ∑ x : Bool, (phat n data x * eM x data + phat n data x * eD x data)) Q :=
    (integrable_const B).add hscaledI
  have hbound := integral_mono_of_nonneg (ae_of_all Q (fun data => abs_nonneg _))
    (hbaseI.add hepI) (ae_of_all Q hpoint)
  simp only [Pi.add_apply] at hbound
  rw [integral_add hbaseI hepI,
    integral_add (integrable_const B) hscaledI, integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_finsetSum _ (fun x _ => htermI x),
    integral_finsetSum _ (fun x _ => hpi x)] at hbound
  have hsum : (∑ x : Bool, ∫ data, (phat n data x * eM x data + phat n data x * eD x data) ∂Q) ≤
      6 * Real.sqrt (v/n) := by
    have hpart (x : Bool) : (∫ data, (phat n data x * eM x data + phat n data x * eD x data) ∂Q) ≤
        strataProb P x * (6 * Real.sqrt (v/n)) := by
      rw [integral_add (hMF x).1 (hDF x).1, (hMF x).2, (hDF x).2, ← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [(hdev x).1, (hdev x).2])
        (strataProb_pos P hP.strataPos x).le
    have hs : (∑ x : Bool, strataProb P x) = 1 := by
      have h := phat_sum_eq_one n hn
      have hi : (∫ data, ∑ x : Bool, phat n data x ∂Q) = 1 := by
        simp only [h, integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [integral_finsetSum _ (fun x _ => (hpm x).1.integrable (by norm_num))] at hi
      simpa only [(hpm _).2.1] using hi
    calc
      _ ≤ ∑ x : Bool, strataProb P x * (6 * Real.sqrt (v/n)) := Finset.sum_le_sum (fun x _ => hpart x)
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  have hfreq : (∑ x : Bool, ∫ data, ep x data ∂Q) ≤ 2 * Real.sqrt (3/n) := by
    calc
      _ ≤ ∑ x : Bool, Real.sqrt (3/n) := Finset.sum_le_sum (fun x _ => hpdev x)
      _ = _ := by simp
  apply hbound.trans
  change _ ≤ B + 12/b * Real.sqrt (v/n) + 2 * Real.sqrt (3/n)
  have hcoeff : 0 ≤ 2/b := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum hcoeff
  have heq : (2/b) * (6 * Real.sqrt (v/n)) = 12/b * Real.sqrt (v/n) := by ring
  rw [heq] at hh
  linarith

end CausalSmith.Stat.NoisydoseWeakdesignTransition
