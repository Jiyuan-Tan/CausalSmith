module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.BoundedConvergence
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.DominatedPayoffs
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.EnergyOccupation
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.JumpOccupation
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PredictableApproximation
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.PredictableGenerators

/-!
# From conditional intensity to predictable compensation

The cylinder formula is the direct translation of the conditional count
increment premise. Its extension to predictable payoffs is a monotone-class
and integrable-truncation argument on the predictable σ-algebra.
-/

public section

open MeasureTheory Set Filter

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A bounded observation measurable at time `a` makes the expected weighted
count increment on `(a,b]` equal the expected weighted intensity integral. -/
theorem Model.conditional_increment (M : Model Ω μ) (a b : ℝ)
    (F : Ω → ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.horizon)
    (hF : Measurable[M.filtration a] F)
    (hbounded : ∃ C : ℝ, ∀ ω, |F ω| ≤ C)
    (hcount : Integrable (fun ω => F ω *
      (((M.eventTimes ω).filter (fun t => a < t ∧ t ≤ b)).card : ℝ)) μ)
    (hrate : Integrable (fun ω => F ω *
      ∫ t in Ioc a b, M.atRisk t ω * M.intensity t ω ∂volume) μ) :
    (∫ ω, F ω *
      (((M.eventTimes ω).filter (fun t => a < t ∧ t ≤ b)).card : ℝ) ∂μ) =
    ∫ ω, F ω *
      (∫ t in Ioc a b, M.atRisk t ω * M.intensity t ω ∂volume) ∂μ :=
  M.conditional_intensity_increment a b F ha hab hb hF hbounded hcount hrate

/-- For an elementary predictable payoff `F(ω) 1_(a,b](t)`, the expected
jump sum equals its expected compensator integral. The proof unfolds the
finite sum and applies `conditional_increment`. -/
theorem Model.cylinder_compensator (M : Model Ω μ) (a b : ℝ)
    (F : Ω → ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.horizon)
    (hF : Measurable[M.filtration a] F)
    (hbounded : ∃ C : ℝ, ∀ ω, |F ω| ≤ C)
    (hjump : Integrable
      (M.jumpIntegral (fun t ω => if a < t ∧ t ≤ b then F ω else 0)
        M.horizon) μ)
    (henergy : Integrable
      (M.energyIntegral (fun t ω => if a < t ∧ t ≤ b then F ω else 0)
        M.horizon) μ) :
    (∫ ω, M.jumpIntegral
      (fun t ω => if a < t ∧ t ≤ b then F ω else 0) M.horizon ω ∂μ) =
    ∫ ω, M.energyIntegral
      (fun t ω => if a < t ∧ t ≤ b then F ω else 0) M.horizon ω ∂μ := by
  have hJump (ω : Ω) :
      M.jumpIntegral (fun t ω => if a < t ∧ t ≤ b then F ω else 0) M.horizon ω =
        F ω * (((M.eventTimes ω).filter (fun t => a < t ∧ t ≤ b)).card : ℝ) := by
    classical
    have hfilter : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) =
        M.eventTimes ω := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro ht
        exact ⟨ht, (M.events_in_horizon ω t ht).2⟩
    simp [Model.jumpIntegral, hfilter, Finset.sum_ite, Finset.sum_const,
      mul_comm]
  have hEnergy (ω : Ω) :
      M.energyIntegral (fun t ω => if a < t ∧ t ≤ b then F ω else 0)
          M.horizon ω =
        F ω * (∫ t in Ioc a b,
          M.atRisk t ω * M.intensity t ω ∂volume) := by
    have hset : Ioc 0 M.horizon ∩ Ioc a b = Ioc a b := by
      ext t
      simp only [mem_inter_iff, mem_Ioc]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨⟨lt_of_le_of_lt ha h.1, le_trans h.2 hb⟩, h⟩
    change (∫ t in Ioc 0 M.horizon,
      (if t ∈ Ioc a b then F ω else 0) *
        (M.atRisk t ω * M.intensity t ω) ∂volume) = _
    have heq : (fun t => (if t ∈ Ioc a b then F ω else 0) *
        (M.atRisk t ω * M.intensity t ω)) =
        (Ioc a b).indicator (fun t => F ω *
          (M.atRisk t ω * M.intensity t ω)) := by
      funext t
      simp [Set.indicator]
    rw [heq, setIntegral_indicator measurableSet_Ioc, hset, integral_const_mul]
  have hcount : Integrable (fun ω => F ω *
      (((M.eventTimes ω).filter (fun t => a < t ∧ t ≤ b)).card : ℝ)) μ := by
    simpa only [← hJump] using hjump
  have hrate : Integrable (fun ω => F ω *
      ∫ t in Ioc a b, M.atRisk t ω * M.intensity t ω ∂volume) μ := by
    simpa only [← hEnergy] using henergy
  simpa only [hJump, hEnergy] using
    M.conditional_increment a b F ha hab hb hF hbounded hcount hrate

/-- The finite jump sum of the indicator of a measurable time-sample set is
integrable under the finite event-count second-moment assumption. -/
theorem Model.integrable_jump_indicator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω)) (hS : MeasurableSet S) :
    Integrable
      (M.jumpIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) μ := by
  have hmeas : Measurable
      (M.jumpIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) :=
    M.measurable_jumpIntegral _ (measurable_const.indicator hS)
  have hcard : Integrable (fun ω => ((M.eventTimes ω).card : ℝ)) μ := by
    have hm : Measurable (fun ω => ((M.eventTimes ω).card : ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp M.measurable_eventCard
    exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      M.count_square_integrable).integrable one_le_two
  apply hcard.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  classical
  have hf : (M.eventTimes ω).filter (fun t => t ≤ M.horizon) =
      M.eventTimes ω := Finset.filter_eq_self.mpr
        (fun t ht => (M.events_in_horizon ω t ht).2)
  rw [Model.jumpIntegral, hf, Real.norm_eq_abs]
  calc
    |∑ t ∈ M.eventTimes ω, S.indicator (fun _ => (1 : ℝ)) (t, ω)| ≤
        ∑ t ∈ M.eventTimes ω, |S.indicator (fun _ => (1 : ℝ)) (t, ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ M.eventTimes ω, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hs : (t, ω) ∈ S <;> simp [Set.indicator, hs]
    _ = ((M.eventTimes ω).card : ℝ) := by simp

/-- The finite-horizon intensity integral of the indicator of a measurable
time-sample set is integrable under the uniform intensity bound. -/
theorem Model.integrable_energy_indicator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω)) (hS : MeasurableSet S) :
    Integrable
      (M.energyIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) μ := by
  have hmeas : Measurable
      (M.energyIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω))
        M.horizon) :=
    M.measurable_energyIntegral _ (measurable_const.indicator hS)
  obtain ⟨C, hC, hrate⟩ := M.rate_horizon_uniform_bound
  apply (integrable_const (C * M.horizon : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hdom (t : ℝ) (ht : t ∈ Ioc 0 M.horizon) :
      ‖S.indicator (fun _ => (1 : ℝ)) (t, ω) *
          (M.atRisk t ω * M.intensity t ω)‖ ≤ C := by
    have hr := hrate t ω (le_of_lt ht.1) ht.2
    by_cases hs : (t, ω) ∈ S
    · calc
        ‖S.indicator (fun _ => (1 : ℝ)) (t, ω) *
            (M.atRisk t ω * M.intensity t ω)‖ =
            |M.atRisk t ω * M.intensity t ω| := by
              simp [Set.indicator, hs, Real.norm_eq_abs]
        _ = M.atRisk t ω * M.intensity t ω := abs_of_nonneg hr.1
        _ ≤ C := hr.2
    · simp [Set.indicator, hs, hC]
  have hbound := norm_integral_le_of_norm_le
    (f := fun t => S.indicator (fun _ => (1 : ℝ)) (t, ω) *
      (M.atRisk t ω * M.intensity t ω))
    (g := fun _t : ℝ => C)
    (integrable_const C : Integrable (fun _t : ℝ => C)
      (volume.restrict (Ioc 0 M.horizon)))
    (ae_restrict_of_forall_mem measurableSet_Ioc hdom)
  simpa [Model.energyIntegral, Real.norm_eq_abs, integral_const,
    Real.volume_Ioc, M.horizon_pos.le, mul_comm] using hbound

/-- The event and intensity occupation measures assign the same mass to a
predictable cylinder, by the conditional intensity increment identity. -/
theorem Model.occupation_cylinder_agree (M : Model Ω μ)
    [IsProbabilityMeasure μ] (a b : ℝ) (B : Set Ω)
    (hB : MeasurableSet[M.filtration a] B) :
    M.jumpOccupation (Ioc a b ×ˢ B) =
      M.energyOccupation (Ioc a b ×ˢ B) := by
  let S : Set (ℝ × Ω) := Ioc a b ×ˢ B
  have hS : MeasurableSet S :=
    measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  have hj := M.integrable_jump_indicator S hS
  have he := M.integrable_energy_indicator S hS
  have hreal : (M.jumpOccupation S).toReal =
      (M.energyOccupation S).toReal := by
    rw [M.jumpOccupation_indicator S hS hj,
      M.energyOccupation_indicator S hS he]
    exact M.predictable_cylinder_compensator a b B hB hj he
  exact (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt ((measure_mono (subset_univ S)).trans_lt M.jumpOccupation_finite))
    (ne_of_lt ((measure_mono (subset_univ S)).trans_lt M.energyOccupation_finite))).mp
    hreal

/-- The expected total number of jumps equals the expected total integrated
at-risk intensity, so the two finite occupation measures have equal mass. -/
theorem Model.occupation_univ_agree (M : Model Ω μ)
    [IsProbabilityMeasure μ] :
    M.jumpOccupation univ = M.energyOccupation univ := by
  have hj := M.integrable_jump_indicator univ MeasurableSet.univ
  have he := M.integrable_energy_indicator univ MeasurableSet.univ
  have hf (ω : Ω) : (M.eventTimes ω).filter
      (fun t => 0 < t ∧ t ≤ M.horizon) = M.eventTimes ω :=
    Finset.filter_eq_self.mpr (fun t ht => M.events_in_horizon ω t ht)
  have hfh (ω : Ω) : (M.eventTimes ω).filter
      (fun t => t ≤ M.horizon) = M.eventTimes ω :=
    Finset.filter_eq_self.mpr (fun t ht => (M.events_in_horizon ω t ht).2)
  have hcount : Integrable (fun ω : Ω => (1 : ℝ) *
      (((M.eventTimes ω).filter (fun t => 0 < t ∧ t ≤ M.horizon)).card : ℝ)) μ := by
    convert hj using 1
    funext ω
    simp [Model.jumpIntegral, hf ω, hfh ω]
  have hrate : Integrable (fun ω : Ω => (1 : ℝ) *
      ∫ t in Ioc 0 M.horizon, M.atRisk t ω * M.intensity t ω ∂volume) μ := by
    convert he using 1
    funext ω
    simp [Model.energyIntegral]
  have hreal : (M.jumpOccupation univ).toReal =
      (M.energyOccupation univ).toReal := by
    rw [M.jumpOccupation_indicator univ MeasurableSet.univ hj,
      M.energyOccupation_indicator univ MeasurableSet.univ he]
    simpa [Model.jumpIntegral, Model.energyIntegral, hf, hfh] using
      (M.conditional_increment 0 M.horizon (fun _ => 1)
      (le_refl 0) M.horizon_pos.le le_rfl measurable_const
      ⟨1, by simp⟩ hcount hrate)
  exact (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt M.jumpOccupation_finite)
    (ne_of_lt M.energyOccupation_finite)).mp hreal

/-- The event and intensity occupation measures agree on every predictable
time-sample set. Their equality on cylinders follows from conditional
intensity; finite-measure uniqueness extends it to the generated σ-algebra. -/
theorem Model.occupation_agree (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω))
    (hS : MeasurableSet[predictableSpace M.filtration] S) :
    M.jumpOccupation S = M.energyOccupation S := by
  have hle : predictableSpace M.filtration ≤
      (inferInstance : MeasurableSpace (ℝ × Ω)) := by
    apply (MeasurableSpace.generateFrom_le_iff _).mpr
    rintro T ⟨a, b, B, hB, rfl⟩
    exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  letI : IsFiniteMeasure M.jumpOccupation :=
    ⟨M.jumpOccupation_finite⟩
  apply ext_on_measurableSpace_of_generate_finite
    (inferInstance : MeasurableSpace (ℝ × Ω))
    (predictableCylinders M.filtration) ?_ hle rfl
    (predictableCylinders_isPiSystem M.filtration M.filtration_mono)
    M.occupation_univ_agree hS
  rintro T ⟨a, b, B, hB, rfl⟩
  exact M.occupation_cylinder_agree a b B hB

/-- The indicator of any predictable time-sample set has the same expected
finite jump sum as expected integral against the at-risk intensity. -/
theorem Model.predictable_indicator_compensator (M : Model Ω μ)
    [IsProbabilityMeasure μ] (S : Set (ℝ × Ω))
    (hS : MeasurableSet[predictableSpace M.filtration] S)
    (hjump : Integrable
      (M.jumpIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon) μ)
    (henergy : Integrable
      (M.energyIntegral (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon) μ) :
    (∫ ω, M.jumpIntegral
      (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω ∂μ) =
      ∫ ω, M.energyIntegral
        (fun t ω => S.indicator (fun _ => (1 : ℝ)) (t, ω)) M.horizon ω ∂μ := by
  have hle : predictableSpace M.filtration ≤
      (inferInstance : MeasurableSpace (ℝ × Ω)) := by
    apply (MeasurableSpace.generateFrom_le_iff _).mpr
    rintro T ⟨a, b, B, hB, rfl⟩
    exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  have hS' : MeasurableSet S := hle S hS
  rw [← M.jumpOccupation_indicator S hS' hjump,
    ← M.energyOccupation_indicator S hS' henergy,
    M.occupation_agree S hS]

/-- A predictable payoff taking finitely many real values has equal expected
event and intensity integrals. -/
theorem Model.finiteRange_predictable_compensator (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (G : ℝ → Ω → ℝ) (hG : M.Predictable G)
    (hfinite : Set.Finite (Set.range (fun p : ℝ × Ω => G p.1 p.2))) :
    (∫ ω, M.jumpIntegral G M.horizon ω ∂μ) =
      ∫ ω, M.energyIntegral G M.horizon ω ∂μ := by
  classical
  let s := hfinite.toFinset
  let S (x : ℝ) : Set (ℝ × Ω) := {p | G p.1 p.2 = x}
  let I (x : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
    (S x).indicator (fun _ => (1 : ℝ)) (t, ω)
  have hs (t : ℝ) (ω : Ω) : G t ω ∈ s :=
    by simpa [s] using (show G t ω ∈ Set.range (fun p : ℝ × Ω => G p.1 p.2) from
      ⟨(t, ω), rfl⟩)
  have hS (x : ℝ) : MeasurableSet[predictableSpace M.filtration] (S x) :=
    hG (measurableSet_singleton x)
  have hle : predictableSpace M.filtration ≤
      (inferInstance : MeasurableSpace (ℝ × Ω)) := by
    apply (MeasurableSpace.generateFrom_le_iff _).mpr
    rintro T ⟨a, b, B, hB, rfl⟩
    exact measurableSet_Ioc.prod ((M.filtration_le a) B hB)
  have hS' (x : ℝ) : MeasurableSet (S x) := hle _ (hS x)
  have hdecomp (t : ℝ) (ω : Ω) :
      G t ω = ∑ x ∈ s, x * I x t ω := by
    simp [I, S, Set.indicator, Finset.sum_ite_eq', hs t ω, eq_comm]
  have hjI (x : ℝ) : Integrable (M.jumpIntegral (I x) M.horizon) μ :=
    M.integrable_jump_indicator (S x) (hS' x)
  have heI (x : ℝ) : Integrable (M.energyIntegral (I x) M.horizon) μ :=
    M.integrable_energy_indicator (S x) (hS' x)
  have hjlin (ω : Ω) : M.jumpIntegral G M.horizon ω =
      ∑ x ∈ s, x * M.jumpIntegral (I x) M.horizon ω := by
    simp only [Model.jumpIntegral, hdecomp, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hetime (x : ℝ) (ω : Ω) :
      Integrable (fun t => I x t ω *
        (M.atRisk t ω * M.intensity t ω))
        (volume.restrict (Ioc 0 M.horizon)) := by
    have hsec : MeasurableSet {t : ℝ | (t, ω) ∈ S x} :=
      (hS' x).preimage measurable_prodMk_right
    have h := (M.rate_integrable ω).indicator hsec
    change Integrable (Set.indicator {t : ℝ | (t, ω) ∈ S x}
      (fun t => M.atRisk t ω * M.intensity t ω))
      (volume.restrict (Ioc 0 M.horizon)) at h
    convert h using 1
    funext t
    by_cases ht : (t, ω) ∈ S x <;> simp [I, Set.indicator, ht]
  have helin (ω : Ω) : M.energyIntegral G M.horizon ω =
      ∑ x ∈ s, x * M.energyIntegral (I x) M.horizon ω := by
    simp only [Model.energyIntegral, hdecomp, Finset.sum_mul]
    rw [integral_finsetSum s]
    · simp_rw [mul_assoc, integral_const_mul]
    · intro x hx
      simpa only [mul_assoc] using (hetime x ω).const_mul x
  rw [show (∫ ω, M.jumpIntegral G M.horizon ω ∂μ) =
      ∑ x ∈ s, x * (∫ ω, M.jumpIntegral (I x) M.horizon ω ∂μ) from by
        simp_rw [hjlin]
        rw [integral_finsetSum s]
        · simp_rw [integral_const_mul]
        · intro x hx
          exact (hjI x).const_mul x]
  rw [show (∫ ω, M.energyIntegral G M.horizon ω ∂μ) =
      ∑ x ∈ s, x * (∫ ω, M.energyIntegral (I x) M.horizon ω ∂μ) from by
        simp_rw [helin]
        rw [integral_finsetSum s]
        · simp_rw [integral_const_mul]
        · intro x hx
          exact (heI x).const_mul x]
  apply Finset.sum_congr rfl
  intro x hx
  rw [M.predictable_indicator_compensator (S x) (hS x) (hjI x) (heI x)]

/-- Every bounded predictable payoff satisfies the expected jump-sum equals
expected intensity-integral identity. Approximate it by finite-valued
predictable simple functions after proving the indicator identity. -/
theorem Model.bounded_predictable_compensator (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (G : ℝ → Ω → ℝ) (hG : M.Predictable G)
    (hbounded : ∃ C : ℝ, ∀ t ω, |G t ω| ≤ C) :
    (∫ ω, M.jumpIntegral G M.horizon ω ∂μ) =
      ∫ ω, M.energyIntegral G M.horizon ω ∂μ := by
  obtain ⟨C, hC⟩ := hbounded
  have hbound : ∀ t ω, |G t ω| ≤ |C| :=
    fun t ω => (hC t ω).trans (le_abs_self C)
  obtain ⟨A, hA, hfinite, hAbound, hlim⟩ :=
    M.bounded_predictable_approximation G hG |C| (abs_nonneg C) hbound
  have hj := M.tendsto_expected_jumpIntegral A G hA
    |C| hAbound hlim
  have he := M.tendsto_expected_energyIntegral A G hA
    |C| (abs_nonneg C) hAbound hlim
  have heq (k : ℕ) :
      (∫ ω, M.jumpIntegral (A k) M.horizon ω ∂μ) =
        ∫ ω, M.energyIntegral (A k) M.horizon ω ∂μ :=
    M.finiteRange_predictable_compensator (A k) (hA k) (hfinite k)
  exact tendsto_nhds_unique hj (by simpa only [heq] using he)

/-- An integrable absolute predictable event payoff has an absolutely
integrable time-sample intensity payoff, as a consequence of conditional
intensity and finite-horizon bounded compensation. -/
theorem Model.predictable_rate_product_integrable (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (G : ℝ → Ω → ℝ) (hG : M.Predictable G)
    (hjumpAbs : Integrable
      (M.jumpIntegral (fun t ω => |G t ω|) M.horizon) μ) :
    Integrable (fun p : ℝ × Ω =>
      |G p.1 p.2| * (M.atRisk p.1 p.2 * M.intensity p.1 p.2))
      ((volume.restrict (Ioc 0 M.horizon)).prod μ) := by
  /- Use nonnegative bounded predictable cutoffs
       U_k(t,ω) = if |G(t,ω)| ≤ k then |G(t,ω)| else 0.
     Their expected jump sums are bounded by the finite expected absolute
     jump sum. `bounded_predictable_compensator` identifies each expectation
     with its expected energy. Since U_k is bounded and the rate is bounded
     on the horizon, its product payoff is genuinely Bochner integrable;
     use Fubini and `ofReal_integral_eq_lintegral_ofReal` for those cutoffs.
     Fatou (`lintegral_liminf_le`) or monotone convergence proves finiteness
     of the lintegral of |G| times rate, hence the claimed Integrable fact.
     This must not invoke `predictable_compensator`, any isometry, or the
     downstream Regularity module. It prevents totalized time integrals
     from being used to justify a dominated-convergence step. -/
  let ν := volume.restrict (Ioc 0 M.horizon)
  let rate : ℝ × Ω → ℝ := fun p => M.atRisk p.1 p.2 * M.intensity p.1 p.2
  let U (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
    if |G t ω| ≤ (k : ℝ) then |G t ω| else 0
  let F (k : ℕ) (p : ℝ × Ω) : ℝ := U k p.1 p.2 * rate p
  let f (p : ℝ × Ω) : ℝ := |G p.1 p.2| * rate p
  have hrmeas : Measurable rate :=
    M.atRisk_joint_measurable.mul M.intensity_joint_measurable
  have hrnonneg (p : ℝ × Ω) : 0 ≤ rate p :=
    mul_nonneg (M.atRisk_nonneg p.1 p.2) (M.intensity_nonneg p.1 p.2)
  have hU (k : ℕ) : M.Predictable (U k) := by
    letI : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
    change Measurable[predictableSpace M.filtration]
      (fun p : ℝ × Ω => if |G p.1 p.2| ≤ (k : ℝ) then |G p.1 p.2| else 0)
    exact Measurable.ite (hG.abs measurableSet_Iic) hG.abs measurable_const
  have hUnonneg (k : ℕ) (t : ℝ) (ω : Ω) : 0 ≤ U k t ω := by
    dsimp [U]
    split_ifs <;> positivity
  have hUle (k : ℕ) (t : ℝ) (ω : Ω) : U k t ω ≤ |G t ω| := by
    dsimp [U]
    split_ifs <;> simp
  have hUbound (k : ℕ) : ∀ t ω, |U k t ω| ≤ (k : ℝ) := by
    intro t ω
    rw [abs_of_nonneg (hUnonneg k t ω)]
    dsimp [U]
    split_ifs with h
    · exact h
    · positivity
  have hFmeas (k : ℕ) : Measurable (F k) :=
    (M.predictable_joint_measurable (U k) (hU k)).mul hrmeas
  have hFnonneg (k : ℕ) (p : ℝ × Ω) : 0 ≤ F k p :=
    mul_nonneg (hUnonneg k p.1 p.2) (hrnonneg p)
  obtain ⟨R, hR, hr⟩ := M.rate_horizon_uniform_bound
  have hmem : ∀ᵐ p : ℝ × Ω ∂ν.prod μ, p.1 ∈ Ioc 0 M.horizon :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hFi (k : ℕ) : Integrable (F k) (ν.prod μ) := by
    apply (integrable_const ((k : ℝ) * R)).mono' (hFmeas k).aestronglyMeasurable
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg k p)]
    exact mul_le_mul
      (by simpa only [abs_of_nonneg (hUnonneg k p.1 p.2)] using hUbound k p.1 p.2)
      (hr p.1 p.2 hp.1.le hp.2).2 (hrnonneg p) (Nat.cast_nonneg k)
  have hj (k : ℕ) := M.integrable_jump (U k) (hU k) ⟨k, hUbound k⟩
  have he (k : ℕ) := M.integrable_energy (U k) (hU k) ⟨k, hUbound k⟩
  have hInt (k : ℕ) : (∫ p, F k p ∂ν.prod μ) ≤
      ∫ ω, M.jumpIntegral (fun t ω => |G t ω|) M.horizon ω ∂μ := by
    rw [integral_prod_symm _ (hFi k)]
    change (∫ ω, M.energyIntegral (U k) M.horizon ω ∂μ) ≤ _
    rw [← M.bounded_predictable_compensator (U k) (hU k)
      ⟨k, hUbound k⟩]
    apply integral_mono (hj k) hjumpAbs
    intro ω
    unfold Model.jumpIntegral
    exact Finset.sum_le_sum (fun t _ => hUle k t ω)
  have hlim (p : ℝ × Ω) : Tendsto (fun k => F k p) atTop (nhds (f p)) := by
    obtain ⟨K, hK⟩ := exists_nat_ge |G p.1 p.2|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    simp [F, f, U, hK.trans (Nat.cast_le.mpr hk)]
  have hLeb (k : ℕ) : (∫⁻ p, ‖F k p‖ₑ ∂ν.prod μ) ≤
      ENNReal.ofReal (∫ ω, M.jumpIntegral (fun t ω => |G t ω|) M.horizon ω ∂μ) := by
    have heq := ofReal_integral_eq_lintegral_ofReal (hFi k)
      (Eventually.of_forall (hFnonneg k))
    have hn : (fun p => ‖F k p‖ₑ) = (fun p => ENNReal.ofReal (F k p)) := by
      funext p
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hFnonneg k p)]
    rw [hn, ← heq]
    exact ENNReal.ofReal_le_ofReal (hInt k)
  refine ⟨((M.predictable_joint_measurable G hG).abs.mul hrmeas).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hFatou : (∫⁻ p, ‖f p‖ₑ ∂ν.prod μ) ≤
      liminf (fun k => ∫⁻ p, ‖F k p‖ₑ ∂ν.prod μ) atTop := by
    have heq : (fun p => ‖f p‖ₑ) =
        (fun p => liminf (fun k => ‖F k p‖ₑ) atTop) := by
      funext p
      exact (hlim p).enorm.liminf_eq.symm
    rw [heq]
    exact lintegral_liminf_le' (fun k => (hFmeas k).aemeasurable.enorm)
  exact lt_of_le_of_lt
    (hFatou.trans (liminf_le_of_frequently_le' (Eventually.of_forall hLeb).frequently))
    ENNReal.ofReal_lt_top

/-- Every integrable predictable payoff satisfies the expected jump-sum
equals expected compensator integral identity. Truncate an integrable payoff,
apply the bounded formula, and pass to the limit in both expectations. [The
model and payoff](hyp:M,G), [predictability](hyp:hG), and [absolute
integrability of the event term](hyp:hjumpAbs) give
[the predictable-compensation identity](goal). -/
theorem Model.predictable_compensator (M : Model Ω μ)
    [IsProbabilityMeasure μ]
    (G : ℝ → Ω → ℝ) (hG : M.Predictable G)
    (hjumpAbs : Integrable
      (M.jumpIntegral (fun t ω => |G t ω|) M.horizon) μ) :
    (∫ ω, M.jumpIntegral G M.horizon ω ∂μ) =
      ∫ ω, M.energyIntegral G M.horizon ω ∂μ := by
  /- Cutoffs are bounded and dominated by |G|. Absolute time-sample
     integrability is derived, not added as a new caller hypothesis. -/
  let A (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
    if |G t ω| ≤ (k : ℝ) then G t ω else 0
  have hA (k : ℕ) : M.Predictable (A k) := by
    letI : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
    change Measurable[predictableSpace M.filtration]
      (fun p : ℝ × Ω => if |G p.1 p.2| ≤ (k : ℝ) then G p.1 p.2 else 0)
    apply Measurable.ite
    · exact hG.abs measurableSet_Iic
    · exact hG
    · exact measurable_const
  have hbound (k : ℕ) : ∃ C : ℝ, ∀ t ω, |A k t ω| ≤ C := by
    refine ⟨(k : ℝ), ?_⟩
    intro t ω
    dsimp [A]
    split_ifs with h
    · exact h
    · simp
  have hdom : ∀ k t ω, |A k t ω| ≤ |G t ω| := by
    intro k t ω
    dsimp [A]
    split_ifs <;> simp
  have hlim (t : ℝ) (ω : Ω) :
      Tendsto (fun k => A k t ω) atTop (nhds (G t ω)) := by
    obtain ⟨K, hK⟩ := exists_nat_ge |G t ω|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    simp [A, hK.trans (Nat.cast_le.mpr hk)]
  have hj := M.tendsto_expected_jumpIntegral_of_dominated A G hA
    hdom hjumpAbs hlim
  have he := M.tendsto_expected_energyIntegral_of_dominated A G hA hG
    hdom (M.predictable_rate_product_integrable G hG hjumpAbs) hlim
  have heq (k : ℕ) :
      (∫ ω, M.jumpIntegral (A k) M.horizon ω ∂μ) =
        ∫ ω, M.energyIntegral (A k) M.horizon ω ∂μ :=
    M.bounded_predictable_compensator (A k) (hA k) (hbound k)
  exact tendsto_nhds_unique hj (by simpa only [heq] using he)

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
