module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.PublishedModel
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.TCompleteRecordPrecisionFrontier

/-!
# Lower-bound transfer to bounded published superclasses

Restriction to the diagonal image and projection onto the unit target range transfer
both minimax lower bounds, with the same complete seeded record law.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- The seeded published original-record experiment uses the same two-sided off-diagonal channel. -/
def pubRecordLaw {V : Type*} [Fintype V] [DecidableEq V] (q r : ℝ)
    (ϑ : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V) : Measure (Record V × ℝ) :=
  (((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V).prod (pubAcquisitionLaw ϑ q r)).prod seedLaw).map
    (fun ω => (pubRecordOf ϑ ω.1, ω.2))
/-- Published estimators are total Borel maps into the declared [-A,A] range. -/
abbrev PubEstimator (V : Type*) (A : ℝ) : Type _ :=
  {T : Record V × ℝ → ℝ // Measurable T ∧ ∀ x, T x ∈ Set.Icc (-A) A}
/-- Published connected intervals have total Borel endpoints in the declared [-A,A] range. -/
abbrev PubIntervalProc (V : Type*) (A : ℝ) : Type _ :=
  {I : Record V × ℝ → ℝ × ℝ // Measurable I ∧ ∀ x, -A ≤ (I x).1 ∧ (I x).1 ≤ (I x).2 ∧ (I x).2 ≤ A}
/-- Honesty is evaluated over every member of the supplied published representation class. -/
def PubHonest {V : Type*} [Fintype V] [DecidableEq V] (q r A : ℝ)
    (𝔖 : Set (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V)) (I : PubIntervalProc V A) : Prop :=
  ∀ ϑ ∈ 𝔖, ENNReal.ofReal (9/10) ≤ pubRecordLaw q r ϑ
    {x | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubTte ϑ ∈ Set.Icc (I.1 x).1 (I.1 x).2}
/-- Published minimax MSE is the same extended infimum-supremum decision construction. -/
def pubMinimaxRisk {V : Type*} [Fintype V] [DecidableEq V] (q r : ℝ)
    (𝔖 : Set (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V)) (A : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal (fun (T : PubEstimator V A) (ϑ : {ϑ // ϑ ∈ 𝔖}) =>
    ∫⁻ x, ENNReal.ofReal ((T.1 x - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubTte ϑ.1)^2) ∂pubRecordLaw q r ϑ.1)
/-- Published minimax expected length ranges precisely over the honest connected interval subtype. -/
def pubMinimaxLength {V : Type*} [Fintype V] [DecidableEq V] (q r : ℝ)
    (𝔖 : Set (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule V)) (A : ℝ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (I : {I : PubIntervalProc V A // PubHonest q r A 𝔖 I}) (ϑ : {ϑ // ϑ ∈ 𝔖}) =>
      ∫⁻ x, ENNReal.ofReal ((I.1.1 x).2 - (I.1.1 x).1) ∂pubRecordLaw q r ϑ.1)
open CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [Diagonal augmentation preserves the raw polynomial outcome by finite sum expansion.](goal) -/
-- @node: pubOutcome_augment_direct
lemma pubOutcome_augment_direct (η : Schedule V) (i : V) (z : Assign V) :
    pubOutcome (augment η) i z = potentialOutcome η i z := by
  classical
  have hc (S : Finset V) : (augment η).coef i S =
      (if S = ∅ then η.a i else 0) +
        ∑ j : V, if S = {j} then
          (if j = i then η.t i else if η.edge j i then η.b i j else 0) else 0 := by
    by_cases h : S = ∅ <;> simp [augment, h]
  simp only [pubOutcome, hc, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_powerset,
    Finset.empty_subset, if_true, Finset.prod_empty, mul_one, Finset.singleton_subset_iff,
    Finset.prod_singleton]
  rw [pubNbhd_augment]
  simp only [Finset.mem_insert]
  simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd, Finset.sum_filter]
  rw [add_assoc]
  congr 1
  have hown : η.t i * treatment (z i) =
      ∑ j : V, if j = i then η.t i * treatment (z j) else 0 := by simp
  rw [hown, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [η.irrefl]
  · by_cases he : η.edge j i <;> simp [hji, he]

/-- [Preserving every outcome preserves the all-treated versus all-control contrast.](goal) -/
-- @node: pubTte_augment_direct
lemma pubTte_augment_direct (η : Schedule V) : pubTte (augment η) = tte η := by
  simp only [pubTte, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte,
    pubOutcome_augment_direct]

/-- [The compulsory diagonals leave the two-sided channel and the entire seeded record unchanged.](goal) -/
-- @node: pubRecordLaw_augment_direct
lemma pubRecordLaw_augment_direct (q r : ℝ) (η : Schedule V) :
    pubRecordLaw q r (augment η) = recordLaw (noisyDesign q r) η := by
  have hacq : pubAcquisitionLaw (augment η) q r = acquisitionLaw η q r := by
    unfold pubAcquisitionLaw acquisitionLaw
    congr 1
    funext e
    simp only [augment, or_iff_left e.2]
  have hrecord : pubRecordOf (augment η) = recordOf η := by
    funext ω
    simp only [pubRecordOf, recordOf, pubOutcome_augment_direct]
  simp only [pubRecordLaw, recordLaw, noisyDesign, hacq, hrecord]

/-- Given [the stated assumptions](hyp:ht), [Unit-interval projection cannot increase squared error at a unit-range target.](goal) -/
-- @node: superclass_clip_sq_error_le
lemma superclass_clip_sq_error_le (x t : ℝ) (ht : |t| ≤ 1) :
    (max (-1) (min 1 x) - t)^2 ≤ (x-t)^2 := by
  obtain ⟨htlo, hthi⟩ := abs_le.mp ht
  by_cases hlo : x < -1
  · rw [min_eq_right (by linarith), max_eq_left hlo.le]
    nlinarith
  · by_cases hhi : 1 < x
    · rw [min_eq_left hhi.le, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      nlinarith
    · rw [min_eq_right (le_of_not_gt hhi), max_eq_right (le_of_not_gt hlo)]

/-- Given [the stated assumptions](hyp:hlu), [Projecting ordered endpoints preserves their order and cannot increase length.](goal) -/
-- @node: superclass_clip_endpoints
lemma superclass_clip_endpoints (l u : ℝ) (hlu : l ≤ u) :
    -1 ≤ max (-1) (min 1 l) ∧
    max (-1) (min 1 l) ≤ max (-1) (min 1 u) ∧
    max (-1) (min 1 u) ≤ 1 ∧
    max (-1) (min 1 u) - max (-1) (min 1 l) ≤ u-l := by
  refine ⟨le_max_left _ _, max_le_max_left _ (min_le_min_left _ hlu),
    max_le (by norm_num) (min_le_left _ _), ?_⟩
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Given [the stated assumptions](hyp:ht,hmem), [Projection preserves membership of every unit-range target in an interval.](goal) -/
-- @node: superclass_clip_coverage
lemma superclass_clip_coverage (l u t : ℝ) (ht : |t| ≤ 1)
    (hmem : t ∈ Set.Icc l u) :
    t ∈ Set.Icc (max (-1) (min 1 l)) (max (-1) (min 1 u)) := by
  obtain ⟨htlo, hthi⟩ := abs_le.mp ht
  constructor
  · exact max_le htlo ((min_le_right _ _).trans hmem.1)
  · exact le_max_of_le_right (le_min hthi hmem.2)

/-- Given [the stated assumptions](hyp:hcontains), [Restriction to the diagonal image and projection compare the two minimax squared risks.](goal) -/
-- @node: minimaxRisk_le_pubMinimaxRisk_projected
lemma minimaxRisk_le_pubMinimaxRisk_projected (d : ℕ) (q r A : ℝ)
    (𝔖 : Set (PublishedSchedule V))
    (hcontains : ∀ η, ScheduleClass η d → augment η ∈ 𝔖) :
    minimaxRisk (noisyDesign (V := V) q r) d ≤ pubMinimaxRisk q r 𝔖 A := by
  unfold minimaxRisk pubMinimaxRisk
  apply Causalean.Stat.minimaxValueENNReal_le_minimaxValue
  intro T
  have hT := T.2.1
  let T' : Estimator V := ⟨fun x => max (-1) (min 1 (T.1 x)),
    by fun_prop,
    by intro x; exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  refine ⟨T', ?_⟩
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  apply le_trans _ (Causalean.Stat.le_worstCaseRiskENNReal T
    (⟨augment η.1, hcontains η.1 η.2⟩ : {ϑ // ϑ ∈ 𝔖}))
  simp only [pubTte_augment_direct, pubRecordLaw_augment_direct]
  unfold sqLoss
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal
    (superclass_clip_sq_error_le (T.1 x) (tte η.1) (abs_tte_le_one η.2))

/-- Given [the stated assumptions](hyp:hcontains), [Restriction and endpoint projection preserve honesty and compare minimax expected lengths.](goal) -/
-- @node: minimaxLength_le_pubMinimaxLength_projected
lemma minimaxLength_le_pubMinimaxLength_projected (d : ℕ) (q r A : ℝ)
    (𝔖 : Set (PublishedSchedule V))
    (hcontains : ∀ η, ScheduleClass η d → augment η ∈ 𝔖) :
    minimaxLength (noisyDesign (V := V) q r) d ≤ pubMinimaxLength q r 𝔖 A := by
  unfold minimaxLength pubMinimaxLength
  apply Causalean.Stat.minimaxValueENNReal_le_minimaxValue
  intro I
  have hI := I.1.2.1
  let I' : IntervalProc V :=
    ⟨fun x => (max (-1) (min 1 (I.1.1 x).1), max (-1) (min 1 (I.1.1 x).2)),
      by fun_prop, by
        intro x
        have h := superclass_clip_endpoints (I.1.1 x).1 (I.1.1 x).2 (I.1.2.2 x).2.1
        exact ⟨h.1, h.2.1, h.2.2.1⟩⟩
  have hhonest : Honest (noisyDesign q r) d I' := by
    intro η hη
    have h := I.2 (augment η) (hcontains η hη)
    rw [pubTte_augment_direct, pubRecordLaw_augment_direct] at h
    apply h.trans
    apply measure_mono
    intro x hx
    exact superclass_clip_coverage _ _ _ (abs_tte_le_one hη) hx
  refine ⟨⟨I', hhonest⟩, ?_⟩
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  apply le_trans _ (Causalean.Stat.le_worstCaseRiskENNReal I
    (⟨augment η.1, hcontains η.1 η.2⟩ : {ϑ // ϑ ∈ 𝔖}))
  simp only [pubRecordLaw_augment_direct]
  unfold expLength
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal
    (superclass_clip_endpoints (I.1.1 x).1 (I.1.1 x).2 (I.1.2.2 x).2.1).2.2.2

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,hA,hord,hcontains,hmass), [Any bounded order-one published class containing the explicit compulsory-diagonal image
inherits both lower bounds by restriction and projection of the decision rules.](goal) -/
-- @node: lem:published-superclass-lower-transfer
lemma published_superclass_lower_transfer (n d : ℕ) (hn : nZero ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) (A : ℝ) (hA : 1 ≤ A)
    (𝔖 : Set (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedSchedule (Fin n)))
    (hord : ∀ ϑ ∈ 𝔖, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.PublishedOrderOne ϑ)
    (hmass : ∀ ϑ ∈ 𝔖, ∀ i, ∑ S ∈ (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.pubNbhd ϑ i).powerset, |ϑ.coef i S| ≤ A)
    (hcontains : ∀ η, ScheduleClass η d → CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.augment η ∈ 𝔖) :
    ENNReal.ofReal (cLower*rho n d q r) ≤ pubMinimaxRisk q r 𝔖 A ∧
    ENNReal.ofReal (cLower*ell n d q r) ≤ pubMinimaxLength q r 𝔖 A := by
  obtain ⟨ha, hH, hi⟩ := noisyDesign_atoms (V := Fin n) q r hqr
  have hfrontier := complete_record_precision_frontier.2.1 n hn d hd hdu q r hqr
    (noisyDesign q r) ha hH hi
  exact ⟨hfrontier.1.trans (minimaxRisk_le_pubMinimaxRisk_projected d q r A 𝔖 hcontains),
    hfrontier.2.2.2.1.trans
      (minimaxLength_le_pubMinimaxLength_projected d q r A 𝔖 hcontains)⟩

end CausalSmith.Experimentation.NoisygraphTtePrecision
