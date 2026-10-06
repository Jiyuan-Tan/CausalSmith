module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Risk
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MassBudget
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedMeasurability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedBias
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedCellTail
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedScoreConcentration
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedGram
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedWeights
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ConditionalSampling
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ConditionalResiduals
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountLaplace
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ObservedMass
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TailExpectation
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TaylorBias
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Finite-bandwidth balanced-estimator bound -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

/-- A positive-size observed sample is a probability measure: iid sampling
and pathwise consistency transfer the latent product probability law. -/
-- @node: sample_isProbabilityMeasure
lemma sample_isProbabilityMeasure {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n) :
    IsProbabilityMeasure (P.sample n) := by
  letI : IsProbabilityMeasure P.full := hiid.1
  rw [hiid.2.2 n hn, hiid.2.1 n hn]
  have hobs : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact Measurable.ite
      ((by fun_prop : Measurable (fun u : Full d => u.2.1))
        (measurableSet_singleton true)) (by fun_prop) (by fun_prop)
  have hsample : Measurable (fun units : Fin n → Full d => fun i => observe (units i)) := by
    exact measurable_pi_lambda _ (fun i => hobs.comp (measurable_pi_apply i))
  apply Measure.isProbabilityMeasure_map
  exact hsample.aemeasurable.congr (Measure.ae_eq_pi (fun _ =>
    (show P.observedRecord =ᵐ[P.full] observe from hcons.1).symm))

-- @node: balancedEstimator_range
/-- Clipping and the zero fallback keep every fitted value inside the outcome range. -/
lemma balancedEstimator_range {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β M : ℝ) (hM : 0 ≤ M) (x : Fin d → ℝ) :
    balancedEstimator sample j β M x ∈ Set.Icc (-M) M := by
  unfold balancedEstimator armBalancedEstimator
  dsimp only
  split_ifs
  · exact ⟨by linarith, hM⟩
  · exact ⟨le_max_left _ _, (max_le_iff).2 ⟨by linarith, min_le_left _ _⟩⟩

-- @node: supLoss_le_two_mul_of_range
/-- Two functions bounded by `M` have sup loss at most `2M`. -/
lemma supLoss_le_two_mul_of_range {d : ℕ} {f g : (Fin d → ℝ) → ℝ}
    {M : ℝ} (hf : ∀ x ∈ cube d, f x ∈ Set.Icc (-M) M)
    (hg : ∀ x ∈ cube d, g x ∈ Set.Icc (-M) M) :
    supLoss f g ≤ ENNReal.ofReal (2 * M) := by
  unfold supLoss
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hfx := hf x x.property
  have hgx := hg x x.property
  rw [abs_le]
  constructor <;> linarith [hfx.1, hfx.2, hgx.1, hgx.2]

-- @node: balancedEstimator_supLoss_le_two_mul
/-- The finite-bandwidth loss is uniformly bounded, including zero-fit cells. -/
lemma balancedEstimator_supLoss_le_two_mul {d n : ℕ} (sample : Fin n → Obs d)
    (j : ℕ) (β γ C L M : ℝ) (P : Law d)
    (hP : LawClass d β γ C L M P) :
    supLoss (balancedEstimator sample j β M) P.mu1 ≤ ENNReal.ofReal (2 * M) := by
  apply supLoss_le_two_mul_of_range
  · intro x _
    exact balancedEstimator_range sample j β M hP.parameters.2.2.2.2.2.le x
  · exact hP.semantics.2.2.2.2.1

set_option maxHeartbeats 1000000 in
-- @node: stretchedExponentialSeries_summable
/-- A positive power in the exponent makes the cell-rank tail summable. -/
lemma stretchedExponentialSeries_summable (b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    Summable (fun k : ℕ => Real.exp (-b * (k + 1 : ℝ) ^ p)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-b * x ^ p)
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y _ hxy
    apply Real.exp_monotone
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx hxy hp.le) hb.le)
  have hint : IntegrableOn f (Set.Ioi 0) := by
    simpa only [f, Real.rpow_zero, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := p) (s := 0) (b := b)
        (by norm_num) hp hb)
  have hs : Summable (fun k : ℕ => f k) :=
    hanti.summable_of_integrableOn_Ioi_zero hint (fun _ _ => Real.exp_nonneg _)
  simpa only [f, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun k : ℕ => f k) 1).mpr hs

-- @node: stretchedExponentialSeries_factor
/-- The Gaussian parameter separates from the stretched-exponential cell-rank tail.
This is the summation step in the finite-bandwidth deviation argument. -/
lemma stretchedExponentialSeries_factor (c p u : ℝ)
    (hc : 0 < c) (hp : 0 < p) (hu : 1 ≤ u) :
    (∑' k : ℕ, Real.exp (-c * u ^ 2 * (k + 1 : ℝ) ^ p)) ≤
      Real.exp (-c * u ^ 2 / 2) *
        (∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) := by
  have hs : Summable (fun k : ℕ => Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) :=
    by simpa only [neg_div] using
      (stretchedExponentialSeries_summable (c / 2) p (by positivity) hp)
  have hterm (k : ℕ) :
      Real.exp (-c * u ^ 2 * (k + 1 : ℝ) ^ p) ≤
        Real.exp (-c * u ^ 2 / 2) *
          Real.exp (-c / 2 * (k + 1 : ℝ) ^ p) := by
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    have hk : 1 ≤ (k + 1 : ℝ) ^ p :=
      Real.one_le_rpow (by exact_mod_cast Nat.zero_lt_succ k) hp.le
    have hprod : u ^ 2 + (k + 1 : ℝ) ^ p ≤
        2 * (u ^ 2 * (k + 1 : ℝ) ^ p) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sub_nonneg.mpr hk)]
    rw [← Real.exp_add]
    apply Real.exp_monotone
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hc.le]
  have hs' : Summable (fun k : ℕ =>
      Real.exp (-c * u ^ 2 / 2) * Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) :=
    hs.mul_left _
  calc
    (∑' k : ℕ, Real.exp (-c * u ^ 2 * (k + 1 : ℝ) ^ p)) ≤
        ∑' k : ℕ, Real.exp (-c * u ^ 2 / 2) *
          Real.exp (-c / 2 * (k + 1 : ℝ) ^ p) := by
            apply (hs'.of_nonneg_of_le (fun _ => Real.exp_nonneg _) hterm).tsum_le_tsum
            · exact hterm
            · exact hs'
    _ = _ := tsum_mul_left

-- @node: stretchedExponentialSeries_gaussianTail
/-- The rank-union series has a finite Gaussian tail uniformly for `u ≥ 1`. -/
lemma stretchedExponentialSeries_gaussianTail (c p : ℝ)
    (hc : 0 < c) (hp : 0 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 1 ≤ u →
      (∑' k : ℕ, Real.exp (-c * u ^ 2 * (k + 1 : ℝ) ^ p)) ≤
        K * Real.exp (-c * u ^ 2 / 2) := by
  let S : ℝ := ∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)
  have hS : 0 ≤ S := tsum_nonneg (fun _ => Real.exp_nonneg _)
  refine ⟨S + 1, by positivity, ?_⟩
  intro u hu
  calc
    (∑' k : ℕ, Real.exp (-c * u ^ 2 * (k + 1 : ℝ) ^ p)) ≤
        Real.exp (-c * u ^ 2 / 2) * S :=
      stretchedExponentialSeries_factor c p u hc hp hu
    _ ≤ (S + 1) * Real.exp (-c * u ^ 2 / 2) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

/-- Roadmap (17)--(18): a bounded loss with a stretched-exponential rank
union bound has a Gaussian deviation bound at its stochastic scale. Above
`2M` the event is empty, so no concentration premise is needed there. -/
-- @node: rankTail_gaussianDeviation
lemma rankTail_gaussianDeviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (loss : Ω → ENNReal) (b s M K c p : ℝ)
    (hb : 0 ≤ b) (hs : 0 < s) (hc : 0 < c) (hp : 0 < p)
    (hbounded : ∀ ω, loss ω ≤ ENNReal.ofReal (2 * M))
    (hrank : ∀ t : ℝ, 0 < t → t ≤ 2 * M →
      μ.real {ω | loss ω > ENNReal.ofReal (b + t)} ≤
        K * ∑' k : ℕ, Real.exp (-c * (t / s) ^ 2 * (k + 1 : ℝ) ^ p))
    (hK : 0 ≤ K) (u : ℝ) (hu : 1 ≤ u) :
    μ.real {ω | loss ω > ENNReal.ofReal (b + u * s)} ≤
      (K * ((∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) + 1)) *
        Real.exp (-c * u ^ 2 / 2) := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  by_cases ht : u * s ≤ 2 * M
  · have htail := hrank (u * s) (mul_pos hu_pos hs) ht
    have hscale : u * s / s = u := mul_div_cancel_right₀ u hs.ne'
    rw [hscale] at htail
    apply htail.trans
    have hfactor := stretchedExponentialSeries_factor c p u hc hp hu
    calc
      _ ≤ K * (Real.exp (-c * u ^ 2 / 2) *
          ∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) :=
        mul_le_mul_of_nonneg_left hfactor hK
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (show (∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) ≤
            (∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) + 1 by linarith)
          (mul_nonneg hK (Real.exp_nonneg (-c * u ^ 2 / 2)))
        nlinarith only [h]
  · have hempty : {ω | loss ω > ENNReal.ofReal (b + u * s)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hthreshold : ENNReal.ofReal (2 * M) ≤ ENNReal.ofReal (b + u * s) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      exact (not_lt_of_ge ((hbounded ω).trans hthreshold)) hω
    rw [hempty, measureReal_empty]
    have hsum : 0 ≤ ∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p) :=
      tsum_nonneg (fun _ => Real.exp_nonneg _)
    positivity

/-- The sublevel-count formulation implies a lower bound at each rank,
including tied masses; sorting only permutes the finite family. -/
-- @node: sublevelCount_rankEnumeration
lemma sublevelCount_rankEnumeration {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (threshold : ℕ → ℝ)
    (horder : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι →
      (Finset.univ.filter (fun i => mass i < threshold k)).card < k) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, ∀ i,
      threshold (i.val + 1) ≤ mass (e i) := by
  classical
  let e₀ := (Fintype.equivFin ι).symm
  let f : Fin (Fintype.card ι) → ℝ := fun i => mass (e₀ i)
  let e := (Tuple.sort f).trans e₀
  refine ⟨e, ?_⟩
  intro i
  by_contra hbad
  have hlt : mass (e i) < threshold (i.val + 1) := lt_of_not_ge hbad
  have hsub : (Finset.Iic i).map e.toEmbedding ⊆
      Finset.univ.filter (fun a => mass a < threshold (i.val + 1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ hlt⟩
    exact Tuple.monotone_sort f (Finset.mem_Iic.mp hb)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Fin.card_Iic] at hcard
  have hsmall := horder (i.val + 1) (by omega) (by omega)
  omega

/-- Exponentiating the ranked mass lower bounds and extending by nonnegative
terms removes the number of cells from the union bound. -/
-- @node: sublevelCount_exponentialSum_le
lemma sublevelCount_exponentialSum_le {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (a p r : ℝ) (ha : 0 < a) (hp : 0 < p) (hr : 0 < r)
    (horder : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι →
      (Finset.univ.filter (fun i => mass i < a * (k : ℝ) ^ p)).card < k) :
    (∑ i, Real.exp (-r * mass i)) ≤
      ∑' k : ℕ, Real.exp (-r * a * (k + 1 : ℝ) ^ p) := by
  classical
  obtain ⟨e, he⟩ := sublevelCount_rankEnumeration mass (fun k => a * (k : ℝ) ^ p) horder
  have hs : Summable (fun k : ℕ => Real.exp (-r * a * (k + 1 : ℝ) ^ p)) := by
    simpa only [neg_mul] using stretchedExponentialSeries_summable (r * a) p
      (mul_pos hr ha) hp
  calc
    _ = ∑ i : Fin (Fintype.card ι), Real.exp (-r * mass (e i)) :=
      (Equiv.sum_comp e _).symm
    _ ≤ ∑ i : Fin (Fintype.card ι), Real.exp (-r * a * (i.val + 1 : ℝ) ^ p) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (he i) hr.le
      push_cast at h
      nlinarith only [h]
    _ = ∑ k ∈ Finset.range (Fintype.card ι), Real.exp (-r * a * (k + 1 : ℝ) ^ p) := by
      exact Fin.sum_univ_eq_sum_range (fun k => Real.exp (-r * a * (k + 1 : ℝ) ^ p)) _
    _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => Real.exp_nonneg _)

/-- The global tail envelope gives a rank-series bound for the sum of
exponentials of the actual cell masses, uniformly over the law class. -/
-- @node: minimumTreatedMass_exponentialSum_le
lemma minimumTreatedMass_exponentialSum_le (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a : ℝ, 0 < a ∧ ∀ (P : Law d), LawClass d β γ C L M P →
      ∀ (j : ℕ) (r : ℝ), 0 < r →
        (∑ Q : Fin d → Fin (2 ^ j), Real.exp (-r *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q)) ≤
        ∑' k : ℕ, Real.exp (-r * (a * (dyadicWidth j) ^ effectiveDimension d γ) *
          (k + 1 : ℝ) ^ (1 / tailExponent γ)) := by
  obtain ⟨a, ha, horder⟩ := ordered_subcell_mass d β γ C
    hparam.1 hparam.2.1 hparam.2.2.1
    (mass_budget C γ hparam.2.2.2.1 hparam.2.2.1)
  refine ⟨a, ha, ?_⟩
  intro P hP j r hr
  apply sublevelCount_exponentialSum_le
  · have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
    positivity
  · exact one_div_pos.mpr (sub_pos.mpr hparam.2.2.1)
  · exact hr
  · exact horder P j hP.uniformDesign hP.measurablePropensity hP.globalTail

/-- A strict sup-loss exceedance occurs in one of the finitely many cells.
No continuity or attainment of the supremum is needed for this localization. -/
-- @node: supLoss_event_eq_cellUnion
lemma supLoss_event_eq_cellUnion {Ω : Type*} {d : ℕ}
    (f : Ω → (Fin d → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ)
    (j : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    {ω | ENNReal.ofReal b < supLoss (f ω) g} =
      ⋃ Q : Fin d → Fin (2 ^ j),
        {ω | ∃ x ∈ cube d, cellIndex d j x = Q ∧ b < |f ω x - g x|} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, supLoss, lt_iSup_iff,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨cellIndex d j x, x, x.property, rfl, hx⟩
  · rintro ⟨Q, x, hx, _, h⟩
    exact ⟨⟨x, hx⟩, h⟩

/-- Roadmap (15)--(17): averaging cell tails against the minimum-count
Laplace transform and ordering the actual propensity masses gives a global
rank-series bound, including empty subcells. The conditional cell-tail
transfer is deliberately a separate input, rather than assumed in a theorem. -/
-- @node: balancedEstimator_rankTail_of_cellLaplace
lemma balancedEstimator_rankTail_of_cellLaplace (d : ℕ) (β γ C L M c₁ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hc₁ : 0 < c₁) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n → ∀ (b K t : ℝ),
      0 ≤ b → 0 ≤ K → 0 < t → t ≤ 2 * M →
      (∀ Q : Fin d → Fin (2 ^ j),
        (P.sample n).real {sample | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          b + t < |balancedEstimator sample j β M x - P.mu1 x|} ≤
        K * (∫ sample, Real.exp (-(c₁ * t ^ 2 / M ^ 2) *
          (minimumCellCount sample true j (polynomialOrder β)
            (normingSubcells d β).radius Q : ℝ)) ∂P.sample n)) →
      (P.sample n).real {sample | supLoss (balancedEstimator sample j β M) P.mu1 >
        ENNReal.ofReal (b + t)} ≤
        (K * Fintype.card (MultiIndex d (polynomialOrder β))) *
          ∑' k : ℕ, Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ *
            t ^ 2 / M ^ 2 * (k + 1 : ℝ) ^ (1 / tailExponent γ)) := by
  classical
  obtain ⟨a, ha, hsum⟩ := minimumTreatedMass_exponentialSum_le d β γ C L M hparam
  obtain ⟨c₂, hc₂, hlap⟩ := minimumTreatedCount_quadratic_laplace
    d β γ C L M c₁ hparam hc₁
  refine ⟨c₂ * a, mul_pos hc₂ ha, ?_⟩
  intro n j P hP hn b K t hb hK ht htM hcell
  letI : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency hn
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let r : ℝ := c₂ * (n : ℝ) * t ^ 2 / M ^ 2
  have hM : 0 < M := hparam.2.2.2.2.2
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr : 0 < r := by dsimp [r]; positivity
  rw [supLoss_event_eq_cellUnion _ _ j (b + t) (by linarith)]
  calc
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j), (P.sample n).real
        {sample | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          b + t < |balancedEstimator sample j β M x - P.mu1 x|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j), K * (R * Real.exp (-r *
        minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q)) := by
      apply Finset.sum_le_sum
      intro Q _
      apply (hcell Q).trans
      apply mul_le_mul_of_nonneg_left _ hK
      have hexp : -r * minimumTreatedMass P j (polynomialOrder β)
          (normingSubcells d β).radius Q =
          -c₂ * (n : ℝ) * minimumTreatedMass P j (polynomialOrder β)
            (normingSubcells d β).radius Q * t ^ 2 / M ^ 2 := by
        dsimp [r]
        ring
      simpa only [R, hexp] using hlap n j P hP hn Q t ht htM
    _ = (K * R) * ∑ Q : Fin d → Fin (2 ^ j), Real.exp (-r *
        minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ (K * R) * ∑' k : ℕ, Real.exp (-r * (a * (dyadicWidth j) ^ effectiveDimension d γ) *
        (k + 1 : ℝ) ^ (1 / tailExponent γ)) :=
      mul_le_mul_of_nonneg_left (hsum P hP j r hr) (mul_nonneg hK (Nat.cast_nonneg _))
    _ = _ := by
      congr 1
      apply tsum_congr
      intro k
      congr 1
      dsimp [r]
      ring

-- @node: thm:finite-bandwidth
/-- The deviation and expected sup-norm bounds hold for every dyadic width,
including configurations on which the zero fallback is used. -/
theorem finite_bandwidth (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B₀ K₀ c₀ : ℝ, 0 < B₀ ∧ 0 < K₀ ∧ 0 < c₀ ∧
      ∀ (n j : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u →
        (∀ P : Law d, LawClass d β γ C L M P →
          (P.sample n).real
            {sample | supLoss (balancedEstimator sample j β M) P.mu1 >
              ENNReal.ofReal (B₀ * L * (dyadicWidth j) ^ β +
                u * M / Real.sqrt ((n : ℝ) *
                  (dyadicWidth j) ^ (effectiveDimension d γ)))} ≤
            K₀ * Real.exp (-c₀ * u ^ 2)) ∧
        (∀ P : Law d, LawClass d β γ C L M P →
          lawRisk P (fun sample : Fin n → Obs d => balancedEstimator sample j β M) P.mu1 ≤
            ENNReal.ofReal (K₀ * (L * (dyadicWidth j) ^ β +
              M / Real.sqrt ((n : ℝ) *
                (dyadicWidth j) ^ (effectiveDimension d γ))))) := by
  suffices hdeviation : ∃ B K c : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧
      ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d, LawClass d β γ C L M P →
        AEMeasurable
          (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
          (P.sample n) ∧
        ∀ u : ℝ, 1 ≤ u →
          (P.sample n).real
            {sample | supLoss (balancedEstimator sample j β M) P.mu1 >
              ENNReal.ofReal (B * L * (dyadicWidth j) ^ β +
                u * M / Real.sqrt ((n : ℝ) *
                  (dyadicWidth j) ^ (effectiveDimension d γ)))} ≤
            K * Real.exp (-c * u ^ 2) by
    obtain ⟨B, K, c, hB, hK, hc, hdev⟩ := hdeviation
    let A : ℝ := (1 + K) * Real.exp c / c
    let K₀ : ℝ := max K (A * max B 1)
    have hA : 0 < A := by dsimp [A]; positivity
    have hK₀ : 0 < K₀ := hK.trans_le (le_max_left _ _)
    refine ⟨B, K₀, c, hB, hK₀, hc, ?_⟩
    intro n j u hn hu
    constructor
    · intro P hP
      exact ((hdev n j hn P hP).2 u hu).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    · intro P hP
      letI : IsProbabilityMeasure (P.sample n) :=
        sample_isProbabilityMeasure P hP.iid hP.consistency (by omega)
      have hM : 0 < M := hparam.2.2.2.2.2
      have hL : 0 < L := hparam.2.2.2.2.1
      have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      let s : ℝ := M / Real.sqrt
        ((n : ℝ) * (dyadicWidth j) ^ (effectiveDimension d γ))
      have hs : 0 < s := by dsimp [s]; positivity
      have hb : 0 ≤ B * L * (dyadicWidth j) ^ β := by positivity
      have hfinite (sample : Fin n → Obs d) :
          supLoss (balancedEstimator sample j β M) P.mu1 ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (balancedEstimator_supLoss_le_two_mul sample j β γ C L M P hP)
      have hmoment := gaussianTail_ennreal_lintegral_le (P.sample n)
        (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
        (hdev n j hn P hP).1 hfinite (B * L * (dyadicWidth j) ^ β) s K c
        hb hs hK hc (by
          intro v hv
          simpa only [s, mul_div_assoc] using (hdev n j hn P hP).2 v hv)
      apply hmoment.trans
      apply ENNReal.ofReal_le_ofReal
      change A * (B * L * (dyadicWidth j) ^ β + s) ≤
        K₀ * (L * (dyadicWidth j) ^ β + s)
      have hbscale : B * (L * (dyadicWidth j) ^ β) + s ≤
          max B 1 * (L * (dyadicWidth j) ^ β + s) := by
        calc
          _ ≤ max B 1 * (L * (dyadicWidth j) ^ β) + max B 1 * s := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
            · simpa using mul_le_mul_of_nonneg_right (le_max_right B 1) hs.le
          _ = _ := by ring
      calc
        _ ≤ A * (max B 1 * (L * (dyadicWidth j) ^ β + s)) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          simpa only [mul_assoc] using hbscale
        _ = (A * max B 1) * (L * (dyadicWidth j) ^ β + s) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  suffices hrank : ∃ B K c : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧
      ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d, LawClass d β γ C L M P →
        AEMeasurable
          (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
          (P.sample n) ∧
        ∀ t : ℝ, 0 < t → t ≤ 2 * M →
          (P.sample n).real
            {sample | supLoss (balancedEstimator sample j β M) P.mu1 >
              ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t)} ≤
            K * ∑' k : ℕ, Real.exp
              (-c * (t / (M / Real.sqrt ((n : ℝ) *
                (dyadicWidth j) ^ effectiveDimension d γ))) ^ 2 *
                (k + 1 : ℝ) ^ (1 / tailExponent γ)) by
    obtain ⟨B, K, c, hB, hK, hc, hrank⟩ := hrank
    let p : ℝ := 1 / tailExponent γ
    have hp : 0 < p := by
      dsimp [p, tailExponent]
      exact one_div_pos.mpr (sub_pos.mpr hparam.2.2.1)
    let S : ℝ := (∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p)) + 1
    have hS : 0 < S := by
      have hsum : 0 ≤ ∑' k : ℕ, Real.exp (-c / 2 * (k + 1 : ℝ) ^ p) :=
        tsum_nonneg (fun _ => Real.exp_nonneg _)
      dsimp [S]
      linarith
    refine ⟨B, K * S, c / 2, hB, mul_pos hK hS, by positivity, ?_⟩
    intro n j hn P hP
    refine ⟨(hrank n j hn P hP).1, ?_⟩
    intro u hu
    have hs : 0 < M / Real.sqrt ((n : ℝ) *
        (dyadicWidth j) ^ effectiveDimension d γ) := by
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
      have hM : 0 < M := hparam.2.2.2.2.2
      positivity
    have htail := rankTail_gaussianDeviation (P.sample n)
      (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) P.mu1)
      (B * L * (dyadicWidth j) ^ β)
      (M / Real.sqrt ((n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ))
      M K c p (by
        have hL : 0 < L := hparam.2.2.2.2.1
        have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
        positivity) hs hc hp
      (fun sample => balancedEstimator_supLoss_le_two_mul sample j β γ C L M P hP)
      (hrank n j hn P hP).2 hK.le u hu
    have hexp : -(c / 2) * u ^ 2 = -c * u ^ 2 / 2 := by ring
    rw [hexp]
    simpa only [S, p, mul_div_assoc] using htail
  obtain ⟨B, hB, hfiber⟩ := treated_balancedEstimator_productFiber_cell_tail
    d β γ C L M hparam
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c₁ : ℝ := referenceLowerEigenvalue d (polynomialOrder β) ^ 2 / (32 * R)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hc₁ : 0 < c₁ := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [c₁]
    positivity
  -- Supremum-loss measurability is proved from cellwise continuity and the
  -- measurable balanced coefficients; only the conditional-law transfer remains.
  suffices hcell : ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d, LawClass d β γ C L M P →
      ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 < t → t ≤ 2 * M →
        (P.sample n).real {sample | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |balancedEstimator sample j β M x - P.mu1 x|} ≤
          (2 * R) * (∫ sample, Real.exp (-(c₁ * t ^ 2 / M ^ 2) *
            (minimumCellCount sample true j (polynomialOrder β)
              (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) by
    obtain ⟨c, hc, hglobal⟩ := balancedEstimator_rankTail_of_cellLaplace
      d β γ C L M c₁ hparam hc₁
    refine ⟨B, (2 * R) * R, c, hB, by positivity, hc, ?_⟩
    intro n j hn P hP
    refine ⟨(balancedEstimator_supLoss_measurable j β M P.mu1
      (holderOnCube_continuousOn hparam.2.1 hP.treatedHolder)).aemeasurable, ?_⟩
    intro t ht htM
    have hb : 0 ≤ B * L * (dyadicWidth j) ^ β := by
      have hL := hparam.2.2.2.2.1
      have hh := (dyadicWidth_mem_Ioc j).1
      positivity
    have h := hglobal n j P hP (by omega)
      (B * L * (dyadicWidth j) ^ β) (2 * R) t hb (by positivity) ht htM
      (fun Q => hcell n j hn P hP Q t ht htM)
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hh : 0 < dyadicWidth j := (dyadicWidth_mem_Ioc j).1
    have hM : 0 < M := hparam.2.2.2.2.2
    have heff : 0 < (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ := by positivity
    have hsqrt := Real.sq_sqrt heff.le
    have hscale : (t / (M / Real.sqrt ((n : ℝ) *
        (dyadicWidth j) ^ effectiveDimension d γ))) ^ 2 =
        (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ * t ^ 2 / M ^ 2 := by
      rw [div_div_eq_mul_div, div_pow, mul_pow, hsqrt]
      ring
    simp_rw [hscale]
    convert h using 1
    congr 1
    apply tsum_congr
    intro k
    congr 1
    ring
  intro n j hn P hP Q t ht htM
  let : IsProbabilityMeasure P.full := hP.iid.1
  let μ := Measure.pi (fun _ : Fin n =>
    P.full.map (fun u : Full d => (u.1, u.2.1)))
  let N := fun design : Fin n → (Fin d → ℝ) × Bool =>
    minimumCellCount (fun i => ((design i).1, (design i).2, (0 : ℝ)))
      true j (polynomialOrder β) (normingSubcells d β).radius Q
  let g := fun design => (2 * R) * Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ))
  have hN : Measurable N := by dsimp [N]; fun_prop
  have hgmeas : Measurable g := by dsimp [g]; fun_prop
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hg : Integrable g μ := by
    apply Integrable.of_mem_Icc 0 (2 * R) hgmeas.aemeasurable
    apply Filter.Eventually.of_forall
    intro design
    have hexp : Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hNnonneg : (0 : ℝ) ≤ N design := Nat.cast_nonneg _
      have hsnonneg : 0 ≤ c₁ * t ^ 2 / M ^ 2 := by positivity
      nlinarith [mul_nonneg hsnonneg hNnonneg]
    dsimp only [g]
    exact ⟨mul_nonneg (by positivity) (Real.exp_nonneg _),
      (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (mul_one _)⟩
  have hE := balancedEstimator_cellEvent_measurableSet (n := n) j β M
    (B * L * (dyadicWidth j) ^ β + t) (by
      have hL := hparam.2.2.2.2.1
      have hh := (dyadicWidth_mem_Ioc j).1
      positivity) P.mu1 (holderOnCube_continuousOn hparam.2.1 hP.treatedHolder) Q
  have hbound := sample_real_event_le_conditionalFiber_integral P hP.iid
    hP.consistency (by omega : 0 < n) _ hE g hg (by
      filter_upwards [hfiber P hP n j] with design hd
      have h := hd Q t ht.le
      dsimp only at h
      convert h using 1 <;> dsimp [g, N, c₁, R]
      congr 2
      ring)
  apply hbound.trans_eq
  rw [show (∫ design, g design ∂μ) =
      (2 * R) * ∫ design, Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ)) ∂μ by
        exact integral_const_mul _ _]
  congr 1
  exact minimumCellCount_design_integral_eq P hP.iid hP.consistency (by omega)
    true j (polynomialOrder β) (normingSubcells d β).radius (c₁ * t ^ 2 / M ^ 2) Q

end CausalSmith.Stat.GlobalTailDesignRobustCate
