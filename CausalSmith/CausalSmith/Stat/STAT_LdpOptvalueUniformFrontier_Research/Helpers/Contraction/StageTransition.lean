module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageScore

/-!
# Conditional message density identification

The affine mixtures of repaired stage rows represent the actual next-message laws
of the symmetric iid experiment, at every history and public seed.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hw condition](hyp:hw), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [measurability of rows](hyp:hrows), and [the stated hrep condition](hyp:hrep). [Mixing finitely many nonnegative row densities commutes with taking the message law, with the original finite input weights retained](goal). -/
-- @node: finite_weighted_density_bind
lemma finite_weighted_density_bind {I Z : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Z]
    (mu : Measure Z) (w : I → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : I → Z → ℝ) (hf : ∀ a, Measurable (f a)) (hf0 : ∀ a z, 0 ≤ f a z)
    (rows : I → Measure Z) (hrows : Measurable rows)
    (hrep : ∀ a, mu.withDensity (fun z => ENNReal.ofReal (f a z)) = rows a) :
    mu.withDensity (fun z => ENNReal.ofReal (∑ a, w a * f a z)) =
      (atomLaw w).bind rows := by
  ext E hE
  rw [withDensity_apply _ hE, Measure.bind_apply hE hrows.aemeasurable]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hw a) (hf0 a _)),
    ENNReal.ofReal_mul (hw _)]
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_const_mul _ (hf _).ennreal_ofReal,
      ← withDensity_apply _ hE, hrep]
    simp [atomLaw, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]
  · intro a _
    exact measurable_const.mul (hf a).ennreal_ofReal

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the Markov kernel hrep](hyp:hrep). [The affine paired mixture is the conditional next-message density for the original-record experiment after the ancillary bit is integrated out](goal). -/
-- @node: stageMixtureDensity_messageLaw
lemma stageMixtureDensity_messageLaw {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (r : Q.Seed) (eta : ProtocolHistory Q i)
    (f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrep : ∀ a, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f (((a, r), eta), z))) =
        averagedKernel Q i ((a, r), eta)) :
    (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (stageMixtureDensity theta
        (fun a => f (((a, r), eta), z)))) =
      (observedLaw (symmetricLaw theta)).bind (fun o => Q.kernels i ((o, r), eta)) := by
  rw [averagedKernel_marginal_messageLaw Q theta htheta hd i eta r]
  exact finite_weighted_density_bind _ (stageInputWeight theta)
    (stageInputWeight_nonneg theta htheta) _
    (fun a => hf.comp (by fun_prop)) (fun a z => hf0 _)
    _ (by fun_prop) hrep

/-- Assume [positive dimension](hyp:hd). [The zero-contrast next-message law is exactly the uniform row reference, including at histories that have zero transcript probability](goal). -/
-- @node: stageReferenceKernel_eq_zero_messageLaw
lemma stageReferenceKernel_eq_zero_messageLaw {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d)
    (r : Q.Seed) (eta : ProtocolHistory Q i) :
    stageReferenceKernel Q i (r, eta) =
      (observedLaw (symmetricLaw (fun _ => 0))).bind
        (fun o => Q.kernels i ((o, r), eta)) := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  rw [averagedKernel_marginal_messageLaw Q _ hcube hd i eta r]
  ext E hE
  rw [Measure.bind_apply hE (by fun_prop)]
  simp [stageReferenceKernel, uniformRowAverage, Kernel.comap_apply,
    Measure.smul_apply, Measure.finsetSum_apply, pairedLaw, atomLaw,
    lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    ENNReal.ofReal_mul, Finset.mul_sum]
  rw [ENNReal.mul_inv (by simp) (by simp)]
  simp [mul_assoc, ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < d by positivity)]

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), and [the stated hbound condition](hyp:hbound). [A convex stage mixture inherits the deterministic positive bounds on all its rows. These bounds make every finite transcript product integrable](goal). -/
-- @node: stageMixtureDensity_bounds
lemma stageMixtureDensity_bounds {d : ℕ} (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (f : PairedSymbol d → ℝ) (lo hi : ℝ)
    (hbound : ∀ a, lo ≤ f a ∧ f a ≤ hi) :
    lo ≤ stageMixtureDensity theta f ∧ stageMixtureDensity theta f ≤ hi := by
  have hw := stageInputWeight_nonneg theta htheta
  have hsum := stageInputWeight_sum hd theta
  have hconst (c : ℝ) : (∑ a, stageInputWeight theta a * c) = c := by
    rw [← Finset.sum_mul, hsum, one_mul]
  constructor
  · calc
      lo = ∑ a, stageInputWeight theta a * lo := (hconst lo).symm
      _ ≤ stageMixtureDensity theta f := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hbound a).1 (hw a)
  · calc
      stageMixtureDensity theta f ≤ ∑ a, stageInputWeight theta a * hi :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hbound a).2 (hw a)
      _ = hi := hconst hi

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [The repaired jointly measurable stage densities simultaneously represent the actual original-record next-message law and give bounded zero-mean coordinate scores under that law. This identifies the measures needed by the transcript martingale argument, rather than an abstract density-weighted proxy](goal). -/
-- @node: stage_message_score_certificate_of_gate
lemma stage_message_score_certificate_of_gate (hRN : MeasurableKernelRadonNikodym)
    {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      Measurable f ∧
      (∀ w, Real.exp (-eps) ≤ f w ∧ f w ≤ Real.exp eps) ∧
      (∀ theta, ∀ r eta z,
        stageMixtureDensity theta (fun a => f (((a, r), eta), z)) =
          1 + ∑ j, theta j * stageCoordinateSlope (fun a => f (((a, r), eta), z)) j) ∧
      (∀ theta ∈ parameterCube d, ∀ r eta,
        (stageReferenceKernel Q i (r, eta)).withDensity
          (fun z => ENNReal.ofReal (stageMixtureDensity theta
            (fun a => f (((a, r), eta), z)))) =
          (observedLaw (symmetricLaw theta)).bind (fun o => Q.kernels i ((o, r), eta))) ∧
      (∀ theta ∈ parameterCube d, ∀ r eta z,
        Real.exp (-eps) ≤ stageMixtureDensity theta (fun a => f (((a, r), eta), z)) ∧
        stageMixtureDensity theta (fun a => f (((a, r), eta), z)) ≤ Real.exp eps) ∧
      (∀ theta ∈ parameterCube d, ∀ r eta z j,
        |stageCoordinateSlope (fun a => f (((a, r), eta), z)) j /
          stageMixtureDensity theta (fun a => f (((a, r), eta), z))| ≤ derivativeScale d eps) ∧
      ∀ theta ∈ parameterCube d, ∀ r eta j,
        (∫ z, stageCoordinateSlope (fun a => f (((a, r), eta), z)) j /
          stageMixtureDensity theta (fun a => f (((a, r), eta), z))
          ∂(observedLaw (symmetricLaw theta)).bind
            (fun o => Q.kernels i ((o, r), eta))) = 0 := by
  obtain ⟨f, hf, hf0, hsum, hpriv, hbound, hrep⟩ :=
    stage_density_repaired_of_gate hRN Q i hd eps heps hQ
  have hscore (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
      (r : Q.Seed) (eta : ProtocolHistory Q i) (z : Q.Message i) (j : Fin d) :=
    stageCoordinateScore_bound hd theta htheta (fun a => f (((a, r), eta), z))
      (fun a => lt_of_lt_of_le (Real.exp_pos (-eps)) (hbound _).1)
      eps heps (fun a b => hpriv a b r eta z) j
  have hmessage (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
      (r : Q.Seed) (eta : ProtocolHistory Q i) :=
    stageMixtureDensity_messageLaw Q i hd theta htheta r eta f hf hf0
      (fun a => hrep a r eta)
  refine ⟨f, hf, hbound, ?_, hmessage, ?_, ?_, ?_⟩
  · intro theta r eta z
    exact stageMixtureDensity_normalized hd theta _ (hsum r eta z)
  · intro theta htheta r eta z
    exact stageMixtureDensity_bounds hd theta htheta _ _ _ (fun a => hbound _)
  · intro theta htheta r eta z j
    exact (hscore theta htheta r eta z j).2
  · intro theta htheta r eta j
    rw [← hmessage theta htheta r eta]
    let := stageReferenceKernel_markov Q i hd
    let := averagedKernel_markov Q i
    apply stageCoordinateScore_integral_zero (stageReferenceKernel Q i (r, eta))
      (fun a z => f (((a, r), eta), z))
      (fun a => hf.comp (by fun_prop)) (fun a z => hf0 _) (Real.exp eps)
    · intro a z
      rw [abs_of_nonneg (hf0 _)]
      exact (hbound _).2
    · intro a
      rw [hrep]
      infer_instance
    · intro z
      exact (hscore theta htheta r eta z j).1

end CausalSmith.Stat.LdpOptvalueUniformFrontier
