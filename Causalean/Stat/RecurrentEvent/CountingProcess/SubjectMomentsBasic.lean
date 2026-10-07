module
public import Causalean.Stat.RecurrentEvent.CountingProcess.CrossPrefix
public import Causalean.Stat.RecurrentEvent.CountingProcess.CrossProduct
public import Causalean.Stat.RecurrentEvent.CountingProcess.HazardBridge
public import Causalean.Stat.RecurrentEvent.CountingProcess.IntegralSquare
public import Causalean.Stat.RecurrentEvent.CountingProcess.NoTies
public import Causalean.Stat.RecurrentEvent.CountingProcess.PathwiseStop
public import Causalean.Stat.RecurrentEvent.CountingProcess.PredictablePrefix

/-!
Second-moment building blocks for predictable pathwise integrals against
compensated censor-event counts: the quadratic-energy definitions, the expected
squared event payoff as the expected at-risk hazard integral of the squared
payoff, and energy bounds for the mixed terms. The subjectwise isometry and the
zero cross moment of different subjects are proved in the `SubjectIsometry` and
`Isometry` modules.

The counting-process and stochastic-integration framework follows Andersen,
Borgan, Gill, and Keiding (1993), Chapter II. The proofs below establish the
finite-sample expectation identities directly from the iid product law.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- [The predictable quadratic energy](goal) of [an integrand](hyp:H) up to [time u](hyp:u) in
[a sample](hyp:x) is the integral over times from 0 to u of the squared integrand times [the
censor hazard](hyp:hazard) times the number of subjects at risk. -/
noncomputable def predictableEnergy {n : ℕ} (hazard : ℝ → ℝ)
    (H : ℝ → Sample n → ℝ) (u : ℝ) (x : Sample n) : ℝ :=
  ∫ s in Set.Icc 0 u,
    (H s x) ^ 2 * hazard s * (∑ i : Fin n, riskIndicator i s x) ∂volume

/-- [The expected quadratic energy is finite](goal) for [an integrand](hyp:H) up to [time
u](hyp:u), with [censor hazard](hyp:hazard), when the sample is drawn from the independent product
law with [failure-time law](hyp:failureLaw) and [censor-time law](hyp:censorLaw): the expected
extended integral over times from 0 to u of the squared integrand times the hazard times the
number of subjects at risk is not infinite.

This is the actual square-integrability condition: a Bochner integral returns zero when its time
integrand is nonintegrable. -/
def QuadraticEnergyFinite {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (H : ℝ → Sample n → ℝ) (u : ℝ) : Prop :=
  (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
    ENNReal.ofReal ((H s x) ^ 2 * hazard s *
      (∑ i : Fin n, riskIndicator i s x)) ∂volume
      ∂sampleLaw n failureLaw censorLaw) ≠ ⊤

/-- For [a nonnegative horizon u](hyp:hu) and [a sample path on which subject i's at-risk payoff,
weighted by the censor hazard, is integrable from 0 to u](hyp:hazard,hPath), [the square of the cumulative payoff up to
u equals the integral of twice the accumulated payoff times its current rate](goal). -/
theorem cumulative_hazard_square {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u) (x : Sample n)
    (hPath : Integrable (fun s => H s x * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u,
      H s x * hazard s * riskIndicator i s x ∂volume) ^ 2 =
    ∫ s in Set.Icc 0 u,
      2 * (∫ t in Set.Icc 0 s,
        H t x * hazard t * riskIndicator i t x ∂volume) *
      (H s x * hazard s * riskIndicator i s x) ∂volume := by
  exact integral_prefix_square
    (fun s => H s x * hazard s * riskIndicator i s x) u hu hPath

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable) and
[jointly measurable in time and sample](hyp:hMeasurable). For a horizon
u and [finite expected quadratic energy](hyp:hQuadratic), [the expected squared
payoff at subject i's observed censor event by u equals the expected integral from 0 to u of the
squared payoff times the hazard times the subject's at-risk indicator](goal). -/
theorem subject_event_square_expectation {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ^ 2
        ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let Q : ℝ → Sample n → ℝ := fun s x => (H s x) ^ 2
  have hQpred : LeftPredictable Q := by
    intro s x y hxy
    simpa [Q] using congrArg (fun z : ℝ => z ^ 2) (hPredictable s x y hxy)
  have hQmeas : Measurable (fun p : ℝ × Sample n => Q p.1 p.2) := by
    exact hMeasurable.pow_const 2
  have hQnonneg : ∀ s x, 0 ≤ Q s x := fun s x => sq_nonneg _
  have hlin := predictable_censor_compensator_lintegral
    failureLaw censorLaw hazard hFailure hHazard Q hQpred hQmeas hQnonneg i u
  have hfinite : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (Q s x * hazard s * riskIndicator i s x)
        ∂volume ∂μ) ≠ ⊤ := by
    have hle : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
        ENNReal.ofReal (Q s x * hazard s * riskIndicator i s x)
          ∂volume ∂μ) ≤
        ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
          ENNReal.ofReal ((H s x) ^ 2 * hazard s *
            (∑ j : Fin n, riskIndicator j s x)) ∂volume ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      dsimp [Q]
      apply mul_le_mul_of_nonneg_left
      · exact Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x) (fun j hj => by
          unfold riskIndicator
          split_ifs <;> norm_num) (Finset.mem_univ i)
      · exact mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)
    exact ne_top_of_le_ne_top hQuadratic hle
  have hEventInt : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) μ := by
    have hm : Measurable (fun x : Sample n =>
        if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) := by
      have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      exact (hQmeas.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (by
      filter_upwards [] with x
      split_ifs <;> positivity)).1
    rw [hlin]
    exact hfinite
  have hcomp := predictable_censor_compensator_nonnegative
    failureLaw censorLaw hazard hFailure hHazard Q hQpred hQmeas hQnonneg
      i u hEventInt
  convert hcomp using 1 <;> simp only [Q, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- Suppose subjects are drawn independently with [failure times following a given
law](hyp:failureLaw) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [jointly measurable in time and
sample](hyp:hMeasurable). For [a horizon u](hyp:u) and [finite expected quadratic
energy](hyp:hQuadratic), [almost every sample path has a hazard-weighted at-risk payoff for
subject i that is integrable from 0 to u](goal). -/
theorem subject_hazard_path_integrable_ae {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    ∀ᵐ x ∂sampleLaw n failureLaw censorLaw,
      Integrable (fun s => H s x * hazard s * riskIndicator i s x)
        (volume.restrict (Set.Icc 0 u)) := by
  /- Tonelli gives finite quadratic energy on almost every path. The
     pointwise Young bound |H| ≤ H² + 1 then controls the L1 payoff by
     that energy and the finite deterministic hazard mass. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 u)
  let e : Sample n → ℝ → ℝ := fun x s =>
    (H s x) ^ 2 * hazard s * (∑ j : Fin n, riskIndicator j s x)
  have he_meas : Measurable (fun p : Sample n × ℝ => e p.1 p.2) := by
    have hrisk (j : Fin n) : Measurable (fun p : Sample n × ℝ =>
        riskIndicator j p.2 p.1) := by
      unfold riskIndicator
      have hf : Measurable (fun p : Sample n × ℝ => (p.1 j).1) := by fun_prop
      have hc : Measurable (fun p : Sample n × ℝ => (p.1 j).2) := by fun_prop
      have hs : MeasurableSet {p : Sample n × ℝ |
          0 ≤ p.2 ∧ p.2 ≤ (p.1 j).1 ∧ p.2 ≤ (p.1 j).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
          (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
            measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd hf)).inter
          (measurableSet_le measurable_snd hc))
      exact measurable_const.ite hs measurable_const
    exact (((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2).mul
      (hHazard.2.1.comp measurable_snd)).mul
      (Finset.measurable_fun_sum _ (fun j _ => hrisk j))
  have he_nonneg (x : Sample n) (s : ℝ) : 0 ≤ e x s := by
    dsimp [e]
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
    exact Finset.sum_nonneg (fun j _ => by unfold riskIndicator; split_ifs <;> norm_num)
  have he_inner_meas : Measurable (fun x => ∫⁻ s, ENNReal.ofReal (e x s) ∂ν) :=
    he_meas.ennreal_ofReal.lintegral_prod_right'
  have he_ae : ∀ᵐ x ∂μ, Integrable (e x) ν := by
    have hfinite : (∫⁻ x, ∫⁻ s, ENNReal.ofReal (e x s) ∂ν ∂μ) ≠ ⊤ :=
      hQuadratic
    filter_upwards [ae_lt_top he_inner_meas hfinite] with x hx
    exact (lintegral_ofReal_ne_top_iff_integrable
      (he_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (he_nonneg x))).1 hx.ne
  filter_upwards [he_ae] with x hx
  have hf_meas : Measurable (fun s => H s x * hazard s * riskIndicator i s x) := by
    have hrisk : Measurable (fun s : ℝ => riskIndicator i s x) := by
      unfold riskIndicator
      have hs : MeasurableSet {s : ℝ |
          0 ≤ s ∧ s ≤ (x i).1 ∧ s ≤ (x i).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
          (((show MeasurableSet {s : ℝ | (0 : ℝ) ≤ s} from
            measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_id measurable_const)).inter
          (measurableSet_le measurable_id measurable_const))
      exact measurable_const.ite hs measurable_const
    exact ((hMeasurable.comp (measurable_id.prodMk measurable_const)).mul
      hHazard.2.1).mul hrisk
  have hbound (s : ℝ) :
      ‖H s x * hazard s * riskIndicator i s x‖ ≤ e x s + hazard s := by
    have hr : 0 ≤ riskIndicator i s x ∧ riskIndicator i s x ≤ 1 := by
      unfold riskIndicator
      split_ifs <;> norm_num
    have hsum : riskIndicator i s x ≤ ∑ j : Fin n, riskIndicator j s x :=
      Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
        (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
        (Finset.mem_univ i)
    have hH : |H s x| ≤ (H s x) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|H s x| - 1), sq_abs (H s x)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hHazard.2.2.1 s),
      abs_of_nonneg hr.1]
    calc
      |H s x| * hazard s * riskIndicator i s x ≤
          ((H s x) ^ 2 + 1) * hazard s * riskIndicator i s x := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hH (hHazard.2.2.1 s)) hr.1
      _ = (H s x) ^ 2 * hazard s * riskIndicator i s x +
          hazard s * riskIndicator i s x := by ring
      _ ≤ e x s + hazard s := by
        dsimp [e]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)))
          (mul_le_of_le_one_right (hHazard.2.2.1 s) hr.2)
  exact (hx.add (hHazard.2.2.2.1 u)).mono' hf_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- If [the censor hazard is nonnegative](hyp:hazard,hHazardNonneg) and [integrable from 0 to
u](hyp:hHazardInt), and on a sample path [subject i's hazard-weighted squared at-risk
payoff](hyp:hEnergyPath) is integrable from 0 to
u, then [the square of the integral of the absolute hazard-weighted payoff is at most the total
hazard mass from 0 to u times the subject's quadratic hazard energy](goal). -/
theorem subject_absolute_payoff_square_le_energy {n : ℕ}
    (hazard : ℝ → ℝ) (hHazardNonneg : ∀ s, 0 ≤ hazard s)
    (H : ℝ → Sample n → ℝ) (i : Fin n) (u : ℝ) (x : Sample n)
    (hHazardInt : Integrable hazard (volume.restrict (Set.Icc 0 u)))
    (hEnergyPath : Integrable (fun s =>
      (H s x) ^ 2 * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u,
      |H s x * hazard s * riskIndicator i s x| ∂volume) ^ 2 ≤
      (∫ s in Set.Icc 0 u, hazard s ∂volume) *
        (∫ s in Set.Icc 0 u,
          (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume) := by
  /- Apply Hölder to the square roots of the hazard and quadratic energy
     densities. The at-risk indicator is idempotent, giving the payoff. -/
  let μ := volume.restrict (Set.Icc 0 u)
  let e : ℝ → ℝ := fun s => (H s x) ^ 2 * hazard s * riskIndicator i s x
  have he_nonneg (s : ℝ) : 0 ≤ e s := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hHazardNonneg s))
      (by simp [riskIndicator]; split_ifs <;> norm_num)
  have hf_meas : AEStronglyMeasurable (fun s => Real.sqrt (hazard s)) μ :=
    hHazardInt.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable (fun s => Real.sqrt (e s)) μ := by
    have h := (show Integrable e μ from hEnergyPath).aestronglyMeasurable
    exact h.aemeasurable.sqrt.aestronglyMeasurable
  have hf_lp : MemLp (fun s => Real.sqrt (hazard s)) 2 μ := by
    have h : MemLp (fun s => ‖Real.sqrt (hazard s)‖ ^ (2 : ENNReal).toReal) 1 μ := by
      apply memLp_one_iff_integrable.mpr
      convert hHazardInt using 1
      funext s
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hHazardNonneg s)]
    have hdiv : (2 / 2 : ENNReal) = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    exact (memLp_norm_rpow_iff (p := 2) (q := 2) hf_meas (by norm_num)
      (by norm_num)).mp (by simpa only [hdiv] using h)
  have hg_lp : MemLp (fun s => Real.sqrt (e s)) 2 μ := by
    have h : MemLp (fun s => ‖Real.sqrt (e s)‖ ^ (2 : ENNReal).toReal) 1 μ := by
      apply memLp_one_iff_integrable.mpr
      convert hEnergyPath using 1
      funext s
      simp [e, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (he_nonneg s)]
    have hdiv : (2 / 2 : ENNReal) = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    exact (memLp_norm_rpow_iff (p := 2) (q := 2) hg_meas (by norm_num)
      (by norm_num)).mp (by simpa only [hdiv] using h)
  have hpoint (s : ℝ) : Real.sqrt (hazard s) * Real.sqrt (e s) =
      |H s x * hazard s * riskIndicator i s x| := by
    calc
      Real.sqrt (hazard s) * Real.sqrt (e s) =
          Real.sqrt (hazard s * e s) := (Real.sqrt_mul (hHazardNonneg s) _).symm
      _ = Real.sqrt ((H s x * hazard s * riskIndicator i s x) ^ 2) := by
        congr 1
        dsimp [e, riskIndicator]
        split_ifs <;> ring
      _ = _ := Real.sqrt_sq_eq_abs _
  have hfsq : (∫ s, (Real.sqrt (hazard s)) ^ (2 : ℝ) ∂μ) = ∫ s, hazard s ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by simpa using Real.sq_sqrt (hHazardNonneg s))
  have hgsq : (∫ s, (Real.sqrt (e s)) ^ (2 : ℝ) ∂μ) = ∫ s, e s ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by simpa using Real.sq_sqrt (he_nonneg s))
  have hholder : (∫ s in Set.Icc 0 u,
      |H s x * hazard s * riskIndicator i s x| ∂volume) ≤
      Real.sqrt (∫ s in Set.Icc 0 u, hazard s ∂volume) *
        Real.sqrt (∫ s in Set.Icc 0 u, e s ∂volume) := by
    have hholder0 := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
      (f := fun s => Real.sqrt (hazard s)) (g := fun s => Real.sqrt (e s))
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (Filter.Eventually.of_forall (fun s => Real.sqrt_nonneg _))
      (Filter.Eventually.of_forall (fun s => Real.sqrt_nonneg _))
      (by simpa only [ENNReal.ofReal_ofNat] using hf_lp)
      (by simpa only [ENNReal.ofReal_ofNat] using hg_lp)
    calc
      _ = ∫ s, Real.sqrt (hazard s) * Real.sqrt (e s) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall (fun s => (hpoint s).symm))
      _ ≤ _ := by
        rw [hfsq, hgsq] at hholder0
        simpa only [Real.sqrt_eq_rpow] using hholder0
  have hB : 0 ≤ ∫ s in Set.Icc 0 u, hazard s ∂volume :=
    integral_nonneg (fun s => hHazardNonneg s)
  have hC : 0 ≤ ∫ s in Set.Icc 0 u, e s ∂volume :=
    integral_nonneg he_nonneg
  have hA : 0 ≤ ∫ s in Set.Icc 0 u,
      |H s x * hazard s * riskIndicator i s x| ∂volume :=
    integral_nonneg (fun s => abs_nonneg _)
  have hsq : (Real.sqrt (∫ s in Set.Icc 0 u, hazard s ∂volume) *
      Real.sqrt (∫ s in Set.Icc 0 u, e s ∂volume)) ^ 2 =
      (∫ s in Set.Icc 0 u, hazard s ∂volume) *
        (∫ s in Set.Icc 0 u, e s ∂volume) := by
    rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hC]
  dsimp [e] at hsq ⊢
  nlinarith [Real.sqrt_nonneg (∫ s in Set.Icc 0 u, hazard s ∂volume),
    Real.sqrt_nonneg (∫ s in Set.Icc 0 u, e s ∂volume)]

/-- If [the censor hazard is nonnegative](hyp:hazard,hHazardNonneg), [the horizon u is
nonnegative](hyp:hu), [the hazard is integrable from 0 to u](hyp:hHazardInt), and on a sample
path both [subject i's hazard-weighted at-risk payoff](hyp:hPath) and [its squared-payoff
analogue](hyp:hEnergyPath) are integrable from 0 to u, then [the integral of the absolute value
of the accumulated payoff times the current payoff is at most the total hazard mass from 0 to u
times the subject's quadratic hazard energy](goal). -/
theorem subject_prefix_mixed_abs_integral_le_energy {n : ℕ}
    (hazard : ℝ → ℝ) (hHazardNonneg : ∀ s, 0 ≤ hazard s)
    (H : ℝ → Sample n → ℝ) (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (x : Sample n)
    (hHazardInt : Integrable hazard (volume.restrict (Set.Icc 0 u)))
    (hPath : Integrable (fun s => H s x * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u)))
    (hEnergyPath : Integrable (fun s =>
      (H s x) ^ 2 * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u,
      |(∫ t in Set.Icc 0 s,
        H t x * hazard t * riskIndicator i t x ∂volume) *
        (H s x * hazard s * riskIndicator i s x)| ∂volume) ≤
      (∫ s in Set.Icc 0 u, hazard s ∂volume) *
        (∫ s in Set.Icc 0 u,
          (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume) := by
  calc
    _ ≤ (∫ s in Set.Icc 0 u,
        |H s x * hazard s * riskIndicator i s x| ∂volume) ^ 2 :=
      integral_prefix_mul_abs_le_square
        (fun s => H s x * hazard s * riskIndicator i s x) u hu hPath
    _ ≤ _ := subject_absolute_payoff_square_le_energy
      hazard hHazardNonneg H i u x hHazardInt hEnergyPath

