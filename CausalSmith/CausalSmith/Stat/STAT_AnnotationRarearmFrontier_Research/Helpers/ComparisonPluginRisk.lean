module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ComparisonReplacement
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-!
Bounded-loss transport from a supplied marginal table to its proof-only replacement
population, and the auxiliary plug-in rule used for experiment comparison.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs), The replacement complete-record law is at most half the marginal L¹ error away in TV.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_tv
lemma comparisonReplacementLaw_tv {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1) :
    Causalean.Stat.tvDist (obsLaw P) (obsLaw (comparisonReplacementLaw P v)) ≤
      (1 / 2 : Real) * ∑ z : AuxObs d, |auxTable P z - v z| := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure (obsLaw (comparisonReplacementLaw P v)) := by
    unfold obsLaw; infer_instance
  have h := Causalean.Stat.tvDist_le_half_tsum_singleton_abs
    (obsLaw P) (obsLaw (comparisonReplacementLaw P v))
  simp only [tsum_fintype, measureReal_def, obsLaw] at h
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  exact h.trans_eq (congrArg ((1 / 2 : Real) * ·)
    (comparisonReplacementLaw_l1 P v hv hs))

/-- [Under the stated inputs and conditions](hyp:hh,ht,ht',h,t,t'), Squared loss on the action and target intervals is four-Lipschitz in the target.  This gives [the stated result](goal).-/
-- @node: comparison_squared_loss_target_error
lemma comparison_squared_loss_target_error (h t t' : Real)
    (hh : h ∈ Set.Icc (-1) 1) (ht : t ∈ Set.Icc (-1) 1)
    (ht' : t' ∈ Set.Icc (-1) 1) :
    |(h - t) ^ 2 - (h - t') ^ 2| ≤ 4 * |t - t'| := by
  have hb : |2 * h - t - t'| ≤ 4 := abs_le.mpr
    ⟨by linarith [hh.1, ht.2, ht'.2], by linarith [hh.2, ht.1, ht'.1]⟩
  calc
    _ = |t - t'| * |2 * h - t - t'| := by
      rw [← abs_mul, ← abs_neg]
      congr 1
      ring
    _ ≤ |t - t'| * 4 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- Risk of a supplied-table rule when the supplied table need not equal the true one. -/
-- @node: comparisonFixedTableRisk
noncomputable def comparisonFixedTableRisk {n d : Nat} (K : KnownRule n d)
    (P : DiscreteLaw d) (v : AuxTable d) : Real :=
  ∫ z : (Fin n → Obs d) × Real,
    (K.1 (z.1, v, z.2) - ateFunctional P) ^ 2
      ∂((labeledProductLaw P n).prod seedLaw)

/-- Under the stated inputs and conditions, Bounded measurable supplied-table losses are integrable at any population and target.  This gives [the stated result](goal). -/
-- @node: comparisonFixedTableLoss_integrable
lemma comparisonFixedTableLoss_integrable {n d : Nat} (K : KnownRule n d)
    (P : DiscreteLaw d) (v : AuxTable d) (t : Real) :
    Integrable (fun z : (Fin n → Obs d) × Real => (K.1 (z.1, v, z.2) - t) ^ 2)
      ((labeledProductLaw P n).prod seedLaw) := by
  let : IsProbabilityMeasure (labeledProductLaw P n) := by
    unfold labeledProductLaw obsLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have hK := K.2.1
  apply Causalean.Stat.mse_integrable_of_estimator_bound (M := 1)
    ((labeledProductLaw P n).prod seedLaw)
    (fun z : (Fin n → Obs d) × Real => K.1 (z.1, v, z.2)) (by fun_prop) (by norm_num)
  exact fun z => K.2.2 _

/-- [Under the stated inputs and conditions](hyp:K,P,v,eps,heps,hv,hs,hlegal,n,d), For a fixed legal table, product-TV and target transport cost at most
`(2n + 4)` times its marginal L¹ error.  This gives [the stated result](goal).-/
-- @node: comparisonFixedTableRisk_transport
lemma comparisonFixedTableRisk_transport {n d : Nat} (K : KnownRule n d)
    (P : DiscreteLaw d) (v : AuxTable d) (eps : Real) (heps : 0 < eps)
    (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (hlegal : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true) ∧
      v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    comparisonFixedTableRisk K P v ≤
      knownRuleRisk K.1 (comparisonReplacementLaw P v) +
        (2 * (n : Real) + 4) * ∑ z : AuxObs d, |auxTable P z - v z| := by
  let Q := comparisonReplacementLaw P v
  let D := ∑ z : AuxObs d, |auxTable P z - v z|
  let mu := (labeledProductLaw P n).prod seedLaw
  let nu := (labeledProductLaw Q n).prod seedLaw
  let f := fun z : (Fin n → Obs d) × Real => (K.1 (z.1, v, z.2) - ateFunctional P) ^ 2
  let g := fun z : (Fin n → Obs d) × Real => (K.1 (z.1, v, z.2) - ateFunctional Q) ^ 2
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure (obsLaw Q) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure (labeledProductLaw P n) := by
    unfold labeledProductLaw; infer_instance
  let : IsProbabilityMeasure (labeledProductLaw Q n) := by
    unfold labeledProductLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have htv : Causalean.Stat.tvDist mu nu ≤ (n : Real) * ((1 / 2) * D) := by
    rw [labelFloor_tv_common_product]
    exact (Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le n _ _).trans
      (mul_le_mul_of_nonneg_left (comparisonReplacementLaw_tv P v hv hs)
        (Nat.cast_nonneg n))
  have hK := K.2.1
  have hf : Measurable f := by fun_prop
  have hrange : ∀ z, f z ∈ Set.Icc (0 : Real) (0 + 4) := by
    intro z
    have hb := K.2.2 (z.1, v, z.2)
    have ht := ateFunctional_mem_Icc P
    refine ⟨sq_nonneg _, ?_⟩
    dsimp [f]
    nlinarith [hb.1, hb.2, ht.1, ht.2]
  have hdist := Causalean.Stat.tvDist_integral_range mu nu f hf 0 4 (by norm_num) hrange
  have hfirst : (∫ z, f z ∂mu) ≤ (∫ z, f z ∂nu) + 2 * n * D := by
    have h := (le_abs_self ((∫ z, f z ∂mu) - ∫ z, f z ∂nu)).trans hdist
    have hb := mul_le_mul_of_nonneg_right htv (by norm_num : (0 : Real) ≤ 4)
    nlinarith
  have htarget := comparisonReplacementLaw_target_error P v eps heps hv hs hlegal
  have hsecond : (∫ z, f z ∂nu) ≤ (∫ z, g z ∂nu) + 4 * D := by
    calc
      _ ≤ ∫ z, (g z + 4 * D) ∂nu := by
        apply integral_mono (comparisonFixedTableLoss_integrable K Q v _)
          ((comparisonFixedTableLoss_integrable K Q v _).add (integrable_const _))
        intro z
        have h := (le_abs_self ((K.1 (z.1, v, z.2) - ateFunctional P) ^ 2 -
          (K.1 (z.1, v, z.2) - ateFunctional Q) ^ 2)).trans
          (comparison_squared_loss_target_error _ _ _ (K.2.2 _)
            (ateFunctional_mem_Icc P) (ateFunctional_mem_Icc Q))
        dsimp [f, g]
        linarith
      _ = _ := by rw [integral_add (comparisonFixedTableLoss_integrable K Q v _)
        (integrable_const _), integral_const]; simp [nu, g]
  have hg : (∫ z, g z ∂nu) = knownRuleRisk K.1 Q := by
    simp only [knownRuleRisk, Q, comparisonReplacementLaw_auxTable P v hv hs]
    rfl
  change (∫ z, f z ∂mu) ≤ _
  rw [← hg]
  dsimp only [D] at hfirst hsecond ⊢
  linarith

/-- Plug a legal auxiliary empirical table into any supplied-table rule. -/
-- @node: comparisonPluginRule
noncomputable def comparisonPluginRule {n m d : Nat} (K : KnownRule n d)
    (eps : Real) (hm : 0 < m) (z : Sample n m d × Real) : Real :=
  K.1 (z.1.1, comparisonEmpiricalTable eps hm z.1.2, z.2)

/-- [Under the stated hypotheses](hyp:hm), the plug-in is jointly Borel in both channels and the seed. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: comparisonPluginRule_measurable
lemma comparisonPluginRule_measurable {n m d : Nat} (K : KnownRule n d)
    (eps : Real) (hm : 0 < m) : Measurable (comparisonPluginRule K eps hm) := by
  have hK := K.2.1
  unfold comparisonPluginRule
  fun_prop

/-- [Under the stated inputs and conditions](hyp:K,eps,hm,z,n,m,d), The supplied-table rule's range bound also bounds its empirical plug-in.  This gives [the stated result](goal).-/
-- @node: comparisonPluginRule_mem_Icc
lemma comparisonPluginRule_mem_Icc {n m d : Nat} (K : KnownRule n d)
    (eps : Real) (hm : 0 < m) (z : Sample n m d × Real) :
    comparisonPluginRule K eps hm z ∈ Set.Icc (-1) 1 := K.2.2 _

/-- [Under the stated inputs and conditions](hyp:K,eps,hm,P,n,m,d), Product sampling expresses plug-in risk as the auxiliary average of fixed-table risks.  This gives [the stated result](goal).-/
-- @node: comparisonPluginRule_risk_eq
lemma comparisonPluginRule_risk_eq {n m d : Nat} (K : KnownRule n d)
    (eps : Real) (hm : 0 < m) (P : DiscreteLaw d) :
    ruleRisk (comparisonPluginRule K eps hm) P =
      ∫ V, comparisonFixedTableRisk K P (comparisonEmpiricalTable eps hm V)
        ∂auxProductLaw P m := by
  let : IsProbabilityMeasure (labeledProductLaw P n) := by
    unfold labeledProductLaw obsLaw; infer_instance
  let : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have hfull : Integrable (fun z =>
      (comparisonPluginRule K eps hm z - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod seedLaw) :=
    Causalean.Stat.mse_integrable_of_estimator_bound (M := 1) _ _
      (comparisonPluginRule_measurable K eps hm) (by norm_num)
      (comparisonPluginRule_mem_Icc K eps hm)
  unfold ruleRisk comparisonFixedTableRisk
  rw [integral_prod _ hfull]
  change (∫ LV, ∫ u, (comparisonPluginRule K eps hm (LV, u) - ateFunctional P) ^ 2
      ∂seedLaw ∂((labeledProductLaw P n).prod (auxProductLaw P m))) = _
  rw [integral_prod_symm _ hfull.integral_prod_left]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun V => by
    dsimp only
    rw [integral_prod _ (comparisonFixedTableLoss_integrable K P _ _)]
    rfl

/-- Under the stated inputs and conditions, Every supplied-table rule has uniformly bounded squared risk, so its supremum is finite.  This gives [the stated result](goal). -/
-- @node: comparisonKnownRuleRisk_bddAbove
lemma comparisonKnownRuleRisk_bddAbove {n d : Nat} (K : KnownRule n d) (eps : Real) :
    BddAbove (Set.range (fun P : ClassLaw d eps => knownRuleRisk K.1 P.1)) := by
  refine ⟨4, ?_⟩
  rintro _ ⟨P, rfl⟩
  let : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
    unfold labeledProductLaw obsLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  exact labelFloor_bounded_mse ((labeledProductLaw P.1 n).prod seedLaw)
    (fun z : (Fin n → Obs d) × Real => K.1 (z.1, auxTable P.1, z.2))
    (fun z => K.2.2 _) _ (ateFunctional_mem_Icc P.1)

/-- [Under the stated inputs and conditions](hyp:K,eps,hm,hd,heps,heps',P,n,d,m), Conditional transport and the expected empirical L¹ bound give the plug-in risk guarantee.  This gives [the stated result](goal).-/
-- @node: comparisonPluginRule_risk_le
lemma comparisonPluginRule_risk_le {n m d : Nat} (K : KnownRule n d)
    (eps : Real) (hm : 0 < m) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (P : ClassLaw d eps) :
    ruleRisk (comparisonPluginRule K eps hm) P.1 ≤
      (⨆ Q : ClassLaw d eps, knownRuleRisk K.1 Q.1) +
        6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m) := by
  let : IsProbabilityMeasure (auxProductLaw P.1 m) := by
    unfold auxProductLaw; infer_instance
  let W := ⨆ Q : ClassLaw d eps, knownRuleRisk K.1 Q.1
  let D := fun V : Fin m → AuxObs d => ∑ z : AuxObs d,
    |auxTable P.1 z - comparisonEmpiricalTable eps hm V z|
  have hcond (V : Fin m → AuxObs d) :
      comparisonFixedTableRisk K P.1 (comparisonEmpiricalTable eps hm V) ≤
        W + (2 * (n : Real) + 4) * D V := by
    obtain ⟨hv, hs⟩ := comparisonEmpiricalTable_probability eps hm hd heps.le (by linarith) V
    have hlegal := comparisonEmpiricalTable_overlap eps hm heps.le (by linarith) V
    let Q : ClassLaw d eps := ⟨comparisonReplacementLaw P.1
      (comparisonEmpiricalTable eps hm V),
      comparisonReplacementLaw_model P.1 _ eps hv hs hlegal⟩
    exact (comparisonFixedTableRisk_transport K P.1 _ eps heps hv hs hlegal).trans
      (add_le_add (le_ciSup (comparisonKnownRuleRisk_bddAbove K eps) Q) le_rfl)
  have hmean : (∫ V, D V ∂auxProductLaw P.1 m) ≤
      3 * Real.sqrt (2 * (d : Real) / m) := by
    simpa only [D, abs_sub_comm] using
      comparisonEmpiricalTable_expected_l1 eps hm heps.le (by linarith) P.1 P.2
  rw [comparisonPluginRule_risk_eq]
  calc
    _ ≤ ∫ V, (W + (2 * (n : Real) + 4) * D V) ∂auxProductLaw P.1 m :=
      integral_mono Integrable.of_finite Integrable.of_finite hcond
    _ = W + (2 * (n : Real) + 4) * (∫ V, D V ∂auxProductLaw P.1 m) := by
      rw [integral_add (integrable_const _) (Integrable.of_finite.const_mul _),
        integral_const_mul, integral_const]
      simp
    _ ≤ W + (2 * (n : Real) + 4) * (3 * Real.sqrt (2 * (d : Real) / m)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean
        (by positivity : 0 ≤ 2 * (n : Real) + 4))
    _ = _ := by dsimp only [W]; ring

/-- [Under the stated inputs and conditions](hyp:eps,hm,hd,heps,heps',n,d,m), Taking rule infima after the plug-in construction gives the numerical experiment bound.  This gives [the stated result](goal).-/
-- @node: comparison_minimax_le_known_add
lemma comparison_minimax_le_known_add (n m d : Nat) (eps : Real)
    (hm : 1 ≤ m) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    minimaxRisk n m d eps ≤ knownMarginalRisk n d eps +
      6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m) := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  let : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let K0 : KnownRule n d := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  let : Nonempty (KnownRule n d) := ⟨K0⟩
  let err := 6 * ((n : Real) + 2) * Real.sqrt (2 * (d : Real) / m)
  have hinf : minimaxRisk n m d eps - err ≤ knownMarginalRisk n d eps := by
    unfold knownMarginalRisk
    apply le_ciInf
    intro K
    let T : Rule n m d := ⟨comparisonPluginRule K eps (by omega),
      comparisonPluginRule_measurable K eps _, comparisonPluginRule_mem_Icc K eps _⟩
    have hmin : minimaxRisk n m d eps ≤ worstRisk T.1 eps :=
      Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
        (fun T P => integral_nonneg (fun z => sq_nonneg _)) T
    have hworst : worstRisk T.1 eps ≤
        (⨆ Q : ClassLaw d eps, knownRuleRisk K.1 Q.1) + err := by
      apply ciSup_le
      intro P
      exact comparisonPluginRule_risk_le K eps _ hd heps heps' P
    exact sub_le_iff_le_add.mpr (hmin.trans hworst)
  exact sub_le_iff_le_add.mp hinf

end CausalSmith.Stat.AnnotationRarearmFrontier
