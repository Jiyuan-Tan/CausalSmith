import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Decision rules and finite-sample risks used in upper and lower bounds. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

structure LawEstimator (k dx dz n : ℕ) (radius : ℝ) where
  eval : (Fin n → Obs dx dz) → AtomicLaw.LawModulo k radius
    -- @realizes \(\widetilde\nu_n\)(generic law estimator)
  measurable : Measurable eval

/-- Probability-simplex constraint for labelled weight vectors. -/
def InSimplex {k : ℕ} (p : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

structure WeightEstimator (k dx dz n : ℕ) where
  eval : (Fin n → Obs dx dz) → (Fin k → ℝ) -- @realizes \(\widetilde p_n\)(generic weight estimator)
  measurable : Measurable eval
  simplex : ∀ sample, InSimplex (eval sample)

/-- Ordered masses are a Borel function of the labelled atomic coordinates. -/
-- @node: orderedMasses_measurable
lemma orderedMasses_measurable {k : ℕ} {radius : ℝ} :
    Measurable (@orderedMasses k radius) := by
  have hcoord : Measurable (fun ν : AtomicLaw k radius => (ν.weight, ν.atom)) :=
    comap_measurable _
  have hw (i : Fin k) : Measurable (fun ν : AtomicLaw k radius => ν.weight i) :=
    (measurable_pi_apply i).comp measurable_fst |>.comp hcoord
  have ha (i : Fin k) : Measurable (fun ν : AtomicLaw k radius => ν.atom i) :=
    (measurable_pi_apply i).comp measurable_snd |>.comp hcoord
  unfold orderedMasses
  apply Measurable.ite
  · apply MeasurableSet.inter
    · change MeasurableSet ({a : AtomicLaw k radius | ∀ i, 0 < a.weight i} : Set _)
      rw [show ({a : AtomicLaw k radius | ∀ i, 0 < a.weight i} : Set _) =
          ⋂ i, {a | 0 < a.weight i} by ext; simp]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (hw i)
    · change MeasurableSet
        {ν : AtomicLaw k radius | ∀ i j, ν.atom i = ν.atom j → i = j}
      rw [show {ν : AtomicLaw k radius | ∀ i j, ν.atom i = ν.atom j → i = j} =
          ⋂ i, ⋂ j, {ν | i = j ∨ ν.atom i ≠ ν.atom j} by
        ext ν
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i j
          by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr fun he => hij (h i j he)
        · intro h i j he
          rcases h i j with hij | hne
          · exact hij
          · exact False.elim (hne he)]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.union (MeasurableSet.const _) <|
          (measurableSet_eq_fun (ha i) (ha j)).compl
  · apply measurable_pi_lambda
    intro j
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · rw [show {ν : AtomicLaw k radius |
            (Finset.univ.filter fun l => ν.atom l < ν.atom i).card = j.val} =
          ⋃ s : Finset (Fin k), if s.card = j.val then
            (⋂ l ∈ s, {ν | ν.atom l < ν.atom i}) ∩
              (⋂ l ∉ s, {ν | ¬ ν.atom l < ν.atom i}) else ∅ by
          ext ν
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_ite_empty_right,
            Set.mem_inter_iff, Set.mem_iInter]
          constructor
          · intro h
            refine ⟨Finset.univ.filter fun l => ν.atom l < ν.atom i, h, ?_, ?_⟩
            · intro l hl; exact (Finset.mem_filter.mp hl).2
            · intro l hl hlt
              exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
          · rintro ⟨s, hs, hin, hout⟩
            have heq : Finset.univ.filter (fun l => ν.atom l < ν.atom i) = s := by
              ext l
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro hl
                by_contra hls
                exact hout l hls hl
              · exact hin l
            rw [heq, hs]]
      apply MeasurableSet.iUnion
      intro s
      split_ifs
      · apply MeasurableSet.inter
        · exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
            measurableSet_lt (ha l) (ha i)
        · exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
            (measurableSet_lt (ha l) (ha i)).compl
      · exact MeasurableSet.empty
    · exact hw i
    · fun_prop
  · fun_prop

/-- Ordered masses of a valid nonempty atomic law form a probability-simplex vector. -/
-- @node: orderedMasses_inSimplex
lemma orderedMasses_inSimplex {k : ℕ} {radius : ℝ} (hk : 0 < k)
    (ν : AtomicLaw k radius) (hν : AtomicLaw.Valid ν) : InSimplex (orderedMasses ν) := by
  classical
  unfold InSimplex orderedMasses
  split_ifs with h
  · constructor
    · intro j
      exact Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact hν.1 i
        · exact le_rfl
    · rw [Finset.sum_comm]
      calc
        (∑ i : Fin k, ∑ j : Fin k,
            if (Finset.univ.filter fun l => ν.atom l < ν.atom i).card = j.val
            then ν.weight i else 0) = ∑ i : Fin k, ν.weight i := by
          apply Finset.sum_congr rfl
          intro i hi
          let r := (Finset.univ.filter fun l => ν.atom l < ν.atom i).card
          have hsub : (Finset.univ.filter fun l => ν.atom l < ν.atom i) ⊂
              (Finset.univ : Finset (Fin k)) := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨Finset.filter_subset _ _, ?_⟩
            intro heq
            have hi' : i ∈ Finset.univ.filter (fun l => ν.atom l < ν.atom i) := by
              rw [heq]
              exact Finset.mem_univ i
            exact (lt_irrefl _) (Finset.mem_filter.mp hi').2
          have hr : r < k := by
            calc
              r < (Finset.univ : Finset (Fin k)).card := Finset.card_lt_card hsub
              _ = k := by simp
          change (∑ j : Fin k, if r = j.val then ν.weight i else 0) = ν.weight i
          calc
            _ = (if r = (⟨r, hr⟩ : Fin k).val then ν.weight i else 0) :=
              Finset.sum_eq_single (⟨r, hr⟩ : Fin k)
                (fun b _ hne => by
                  rw [if_neg]
                  exact fun he => hne (Fin.ext he.symm)) (by simp)
            _ = ν.weight i := by simp
        _ = 1 := hν.2.1
  · constructor
    · intro i
      exact inv_nonneg.mpr (Nat.cast_nonneg k)
    · rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)]

/-- The ℓ¹ diameter of the probability simplex is two. -/
-- @node: simplex_l1_le_two
lemma simplex_l1_le_two {k : ℕ} {p q : Fin k → ℝ}
    (hp : InSimplex p) (hq : InSimplex q) : ∑ i, |p i - q i| ≤ 2 := by
  calc
    ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_le]
      exact ⟨by linarith [hp.1 i, hq.1 i], by linarith [hp.1 i, hq.1 i]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num

noncomputable def expectedLawRisk {k dx dz n : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    {L pi0 sigma0 : ℝ}
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (est : LawEstimator k dx dz n (effectRadius dz L sigma0)) : ℝ :=
  ∫ sample, AtomicLaw.LawModulo.wass1 (est.eval sample) (quotientLaw P hM)
    ∂sampleLaw (n := n) P

noncomputable def expectedWeightRisk {k dx dz n : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (target : Fin k → ℝ) (est : WeightEstimator k dx dz n) : ℝ :=
  ∫ sample, ∑ i, |est.eval sample i - target i| ∂sampleLaw (n := n) P

-- keep: canonical ordered-weight risk functional for follow-on estimator comparisons
/-- Risk of the specified ordered-mass estimator derived from the common repaired law estimator. -/
noncomputable def expectedOrderedWeightRisk {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (R : SummaryRepairData k dx dz n L pi0 sigma0) : ℝ :=
  ∫ sample, ∑ i,
    |orderedWeightEstimator R sample i -
      orderedMasses (quotientLaw P hM).representative.1 i|
    ∂sampleLaw (n := n) P

/-- One-Wasserstein loss between two bundled finite probability laws is nonnegative. -/
lemma lawModulo_wass1_nonneg {k : ℕ} {radius : ℝ}
    (ν ξ : AtomicLaw.LawModulo k radius) :
    0 ≤ AtomicLaw.LawModulo.wass1 ν ξ := by
  obtain ⟨γ, hγ⟩ := AtomicLaw.wass1_optimal_plan
    ν.representative.2 ξ.representative.2
  unfold AtomicLaw.LawModulo.wass1
  rw [← hγ]
  unfold AtomicLaw.transportCost
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (γ.nonneg i j) (abs_nonneg _)

/-- Integrating a Gaussian upper-tail envelope gives the corresponding mean bound. -/
-- @node: integral_le_of_gaussian_tail
lemma integral_le_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZnn : ∀ ω, 0 ≤ Z ω) (A b q : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hq : 0 < q)
    (htail : ∀ t : ℝ, b < t → μ.real {ω | t < Z ω} ≤ A * Real.exp (-q * t ^ 2)) :
    ∫ ω, Z ω ∂μ ≤ b + A * Real.sqrt (Real.pi / q) / 2 := by
  by_cases hZi : Integrable Z μ
  · rw [hZi.integral_eq_integral_meas_lt (Eventually.of_forall hZnn)]
    let f : ℝ → ℝ := fun t => μ.real {ω | t < Z ω}
    let g : ℝ → ℝ := fun t => (Set.Ioc 0 b).indicator (fun _ => 1) t +
      A * Real.exp (-q * t ^ 2)
    have hf_meas : Measurable f := by
      exact Measurable.ennreal_toReal
        (Antitone.measurable (fun _ _ hst => measure_mono (fun _ h => lt_of_le_of_lt hst h)))
    have hIocfinite : volume (Set.Ioc 0 b) ≠ ∞ := by
      rw [Real.volume_Ioc]
      finiteness
    have h1_int : IntegrableOn ((Set.Ioc 0 b).indicator (fun _ : ℝ => (1 : ℝ)))
        (Set.Ioi 0) :=
      ((integrableOn_const hIocfinite).integrable_indicator measurableSet_Ioc).integrableOn
    have h2_int : IntegrableOn (fun t : ℝ => A * Real.exp (-q * t ^ 2))
        (Set.Ioi 0) :=
      (Integrable.const_mul (integrable_exp_neg_mul_sq hq) A).integrableOn
    have hg_int : IntegrableOn g (Set.Ioi 0) := h1_int.add h2_int
    have hfg : ∀ t ∈ Set.Ioi (0 : ℝ), f t ≤ g t := by
      intro t ht
      by_cases htb : t ≤ b
      · have hprob : f t ≤ 1 := measureReal_le_one
        rw [show g t = 1 + A * Real.exp (-q * t ^ 2) by
          simp [g, Set.mem_Ioc.mpr ⟨ht, htb⟩]]
        exact hprob.trans (le_add_of_nonneg_right (mul_nonneg hA (Real.exp_pos _).le))
      · have htail' := htail t (lt_of_not_ge htb)
        rw [show g t = A * Real.exp (-q * t ^ 2) by
          simp [g, show t ∉ Set.Ioc 0 b by intro ht'; exact htb ht'.2]]
        exact htail'
    have hf_int : IntegrableOn f (Set.Ioi 0) := by
      exact hg_int.mono' (hf_meas.aestronglyMeasurable.restrict)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg : 0 ≤ f t)]
          exact hfg t ht))
    change ∫ t in Set.Ioi 0, f t ≤ b + A * Real.sqrt (Real.pi / q) / 2
    calc
      ∫ t in Set.Ioi 0, f t ≤ ∫ t in Set.Ioi 0, g t :=
        setIntegral_mono_on hf_int hg_int measurableSet_Ioi hfg
      _ = b + A * Real.sqrt (Real.pi / q) / 2 := by
        unfold g
        rw [integral_add h1_int h2_int]
        rw [setIntegral_indicator measurableSet_Ioc]
        rw [Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
        rw [integral_const, measureReal_restrict_apply_univ, Measure.real_def,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by positivity), sub_zero,
          smul_eq_mul, mul_one]
        rw [integral_const_mul]
        rw [integral_gaussian_Ioi]
        ring
  · rw [integral_undef hZi]
    have hpq : 0 < Real.pi / q := div_pos Real.pi_pos hq
    positivity

/-- A square-root logarithmic deviation inequality, uniform over confidence levels, implies a
root-sample-size mean bound. -/
-- @node: integral_le_of_sqrt_log_tail
lemma integral_le_of_sqrt_log_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZnn : ∀ ω, 0 ≤ Z ω) (A : ℝ) (n : ℕ) (hA : 2 ≤ A) (hn : 1 ≤ n)
    (htail : ∀ eta : ℝ, 0 < eta → eta < 1 / 2 →
      μ.real {ω | A * Real.sqrt (Real.log (A / eta) / n) < Z ω} ≤ eta) :
    ∫ ω, Z ω ∂μ ≤
      (A * Real.sqrt (Real.log (2 * A)) + A ^ 2 * Real.sqrt Real.pi / 2) /
        Real.sqrt n := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlogpos : 0 < Real.log (2 * A) := Real.log_pos (by nlinarith)
  let b := A * Real.sqrt (Real.log (2 * A) / n)
  let q := (n : ℝ) / A ^ 2
  have hb : 0 < b := mul_pos hApos (Real.sqrt_pos.2 (div_pos hlogpos hnpos))
  have hq : 0 < q := div_pos hnpos (sq_pos_of_pos hApos)
  have hgauss : ∀ t : ℝ, b < t →
      μ.real {ω | t < Z ω} ≤ A * Real.exp (-q * t ^ 2) := by
    intro t ht
    let eta := A * Real.exp (-q * t ^ 2)
    have htpos : 0 < t := hb.trans ht
    have hbaseSq : b ^ 2 < t ^ 2 := (sq_lt_sq₀ hb.le htpos.le).2 ht
    have hinside : 0 ≤ Real.log (2 * A) / (n : ℝ) := (div_pos hlogpos hnpos).le
    have hbSq : b ^ 2 = A ^ 2 * (Real.log (2 * A) / (n : ℝ)) := by
      simp only [b, mul_pow, Real.sq_sqrt hinside]
    have hrel : q * (A ^ 2 * (Real.log (2 * A) / (n : ℝ))) =
        Real.log (2 * A) := by
      dsimp [q]
      field_simp
    have hqt : Real.log (2 * A) < q * t ^ 2 := by
      rw [← hrel, ← hbSq]
      exact mul_lt_mul_of_pos_left hbaseSq hq
    have hetaPos : 0 < eta := mul_pos hApos (Real.exp_pos _)
    have hetaHalf : eta < 1 / 2 := by
      have he := Real.exp_lt_exp.mpr (neg_lt_neg hqt)
      rw [Real.exp_neg] at he
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * A)] at he
      have he' : Real.exp (-q * t ^ 2) < (2 * A)⁻¹ := by
        simpa [Real.exp_neg] using he
      dsimp [eta]
      calc
        A * Real.exp (-q * t ^ 2) < A * (2 * A)⁻¹ :=
          mul_lt_mul_of_pos_left he' hApos
        _ = 1 / 2 := by field_simp
    have hthreshold : A * Real.sqrt (Real.log (A / eta) / n) = t := by
      have hratio : A / eta = Real.exp (q * t ^ 2) := by
        dsimp [eta]
        rw [div_mul_eq_div_mul_one_div, div_self hApos.ne', one_mul]
        have hexp : Real.exp (-q * t ^ 2) = (Real.exp (q * t ^ 2))⁻¹ := by
          rw [show -q * t ^ 2 = -(q * t ^ 2) by ring, Real.exp_neg]
        rw [hexp, one_div, inv_inv]
      rw [hratio, Real.log_exp]
      have harg : q * t ^ 2 / (n : ℝ) = (t / A) ^ 2 := by
        dsimp [q]
        field_simp
      rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos htpos hApos)]
      field_simp
    calc
      μ.real {ω | t < Z ω} =
          μ.real {ω | A * Real.sqrt (Real.log (A / eta) / n) < Z ω} := by
        rw [hthreshold]
      _ ≤ eta := htail eta hetaPos hetaHalf
      _ = A * Real.exp (-q * t ^ 2) := rfl
  have hmean := integral_le_of_gaussian_tail μ Z hZnn A b q hApos.le hb hq hgauss
  have hsqrtq : Real.sqrt (Real.pi / q) =
      A * Real.sqrt Real.pi / Real.sqrt n := by
    rw [Real.sqrt_div Real.pi_pos.le]
    have hsqrtq' : Real.sqrt q = Real.sqrt n / A := by
      dsimp [q]
      rw [Real.sqrt_div (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs, abs_of_pos hApos]
    rw [hsqrtq']
    field_simp
  rw [hsqrtq] at hmean
  dsimp [b] at hmean
  calc
    ∫ ω, Z ω ∂μ ≤
        A * Real.sqrt (Real.log (2 * A) / n) +
          A * (A * Real.sqrt Real.pi / Real.sqrt n) / 2 := hmean
    _ = (A * Real.sqrt (Real.log (2 * A)) + A ^ 2 * Real.sqrt Real.pi / 2) /
        Real.sqrt n := by
      rw [Real.sqrt_div (by positivity)]
      field_simp

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
