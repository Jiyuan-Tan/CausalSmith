module

public import Causalean.Stat.Minimax.Mixture.Iid
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! Normal exponential likelihood moments for the noisy incomplete-cover experiment.
The alternatives perturb distinct coordinates of an identity-covariance Gaussian;
their likelihood products have unit off-diagonal overlap and exponential diagonal
overlap, including after taking independent replicates. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- The scalar likelihood of a mean shift relative to a standard normal law. -/
-- @node: normalTilt
noncomputable def normalTilt (h x : ℝ) : ℝ := Real.exp (h * x - h ^ 2 / 2)

/-- Normal exponential moments, with an arbitrary constant in the exponent. -/
-- @node: normalTilt_exp_integral
lemma normalTilt_exp_integral (a b : ℝ) :
    (∫ x, Real.exp (a * x + b) ∂gaussianReal 0 1) = Real.exp (a ^ 2 / 2 + b) := by
  simp_rw [Real.exp_add]
  rw [integral_mul_const]
  have hmgf : (∫ x, Real.exp (a * x) ∂gaussianReal 0 1) = Real.exp (a ^ 2 / 2) := by
    change mgf id (gaussianReal 0 1) a = _
    rw [mgf_id_gaussianReal]
    simp
  rw [hmgf, ← Real.exp_add]

/-- The scalar likelihood has finite moments of every real order in its exponent. -/
-- @node: normalTilt_exp_integrable
lemma normalTilt_exp_integrable (a b : ℝ) :
    Integrable (fun x => Real.exp (a * x + b)) (gaussianReal 0 1) := by
  simp_rw [Real.exp_add]
  exact (integrable_exp_mul_gaussianReal a).mul_const (Real.exp b)

/-- Normalization and second moment of a scalar Gaussian mean-shift likelihood. -/
-- @node: normalTilt_moments
lemma normalTilt_moments (h : ℝ) :
    (∫ x, normalTilt h x ∂gaussianReal 0 1) = 1 ∧
    (∫ x, normalTilt h x ^ 2 ∂gaussianReal 0 1) = Real.exp (h ^ 2) := by
  constructor
  · have hi := normalTilt_exp_integral h (-(h ^ 2 / 2))
    simpa [normalTilt, sub_eq_add_neg] using hi
  · have heq : (fun x => normalTilt h x ^ 2) =
        fun x => Real.exp ((2 * h) * x + -(h ^ 2)) := by
      funext x
      rw [normalTilt, pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, normalTilt_exp_integral]
    congr 1
    ring

/-- Integrability of both scalar moments used in the Gaussian overlap calculation. -/
-- @node: normalTilt_integrable_moments
lemma normalTilt_integrable_moments (h : ℝ) :
    Integrable (normalTilt h) (gaussianReal 0 1) ∧
    Integrable (fun x => normalTilt h x ^ 2) (gaussianReal 0 1) := by
  constructor
  · change Integrable (fun x => Real.exp (h * x - h ^ 2 / 2)) _
    simpa only [sub_eq_add_neg] using normalTilt_exp_integrable h (-(h ^ 2 / 2))
  · convert normalTilt_exp_integrable (2 * h) (-(h ^ 2)) using 1
    funext x
    rw [normalTilt, pow_two, ← Real.exp_add]
    congr 1
    ring

/-- Pairwise moments of likelihoods perturbing single coordinates of a product normal law. -/
-- @node: normalCoordinate_overlap
lemma normalCoordinate_overlap {p : ℕ} (j k : Fin p) (h : ℝ) :
    Integrable (fun x : Fin p → ℝ => normalTilt h (x j) * normalTilt h (x k))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) ∧
    (∫ x : Fin p → ℝ, normalTilt h (x j) * normalTilt h (x k)
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) =
      if j = k then Real.exp (h ^ 2) else 1 := by
  classical
  let f : Fin p → ℝ → ℝ := fun i x =>
    (if i = j then normalTilt h x else 1) *
      (if i = k then normalTilt h x else 1)
  have hprod (x : Fin p → ℝ) : (∏ i, f i (x i)) =
      normalTilt h (x j) * normalTilt h (x k) := by
    dsimp only [f]
    rw [Finset.prod_mul_distrib]
    simp
  have hf (i : Fin p) : Integrable (f i) (gaussianReal 0 1) := by
    by_cases hij : i = j <;> by_cases hik : i = k
    · simpa only [f, if_pos hij, if_pos hik, ← pow_two] using (normalTilt_integrable_moments h).2
    · simpa only [f, if_pos hij, if_neg hik, mul_one] using (normalTilt_integrable_moments h).1
    · simpa only [f, if_neg hij, if_pos hik, one_mul] using (normalTilt_integrable_moments h).1
    · simp [f, hij, hik]
  constructor
  · simpa only [hprod] using Integrable.fintype_prod hf
  · simp_rw [← hprod]
    rw [integral_fintype_prod_eq_prod]
    have hi (i : Fin p) : (∫ x, f i x ∂gaussianReal 0 1) =
        if i = j ∧ i = k then Real.exp (h ^ 2) else 1 := by
      by_cases hij : i = j <;> by_cases hik : i = k
      · simpa only [f, if_pos hij, if_pos hik, ← pow_two,
          if_pos (And.intro hij hik)] using
          (normalTilt_moments h).2
      · simpa only [f, if_pos hij, if_neg hik, mul_one,
          if_neg (fun hh : i = j ∧ i = k => hik hh.2)] using
          (normalTilt_moments h).1
      · simpa only [f, if_neg hij, if_pos hik, one_mul,
          if_neg (fun hh : i = j ∧ i = k => hij hh.1)] using
          (normalTilt_moments h).1
      · simp [f, hij, hik]
    simp_rw [hi]
    by_cases hjk : j = k
    · subst k
      simp
    · have hne (i : Fin p) : ¬ (i = j ∧ i = k) := by
        rintro ⟨hij, hik⟩
        exact hjk (hij.symm.trans hik)
      simp [hne, hjk]

/-- The likelihood of an alternative over independent latent replicates. -/
-- @node: normalReplicateLikelihood
noncomputable def normalReplicateLikelihood {p n : ℕ} (j : Fin p) (h : ℝ)
    (x : Fin n → Fin p → ℝ) : ℝ := ∏ r, normalTilt h (x r j)

/-- Independent replicates exponentiate diagonal overlaps and preserve unit cross-overlaps. -/
-- @node: normalReplicate_overlap
lemma normalReplicate_overlap {p n : ℕ} (j k : Fin p) (h : ℝ) :
    Integrable (fun x => normalReplicateLikelihood (n := n) j h x *
      normalReplicateLikelihood k h x)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1) ∧
    (∫ x, normalReplicateLikelihood (n := n) j h x * normalReplicateLikelihood k h x
      ∂Measure.pi (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)) =
      if j = k then Real.exp ((n : ℝ) * h ^ 2) else 1 := by
  have hprod (x : Fin n → Fin p → ℝ) :
      normalReplicateLikelihood j h x * normalReplicateLikelihood k h x =
        ∏ r, (normalTilt h (x r j) * normalTilt h (x r k)) := by
    simp [normalReplicateLikelihood, Finset.prod_mul_distrib]
  constructor
  · simp_rw [hprod]
    exact Integrable.fintype_prod (fun _ => (normalCoordinate_overlap j k h).1)
  · simp_rw [hprod]
    rw [integral_fintype_prod_eq_prod
      (fun _ : Fin n => fun z : Fin p → ℝ => normalTilt h (z j) * normalTilt h (z k))]
    simp_rw [(normalCoordinate_overlap j k h).2]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases hjk : j = k
    · simp [hjk, ← Real.exp_nat_mul]
    · simp [hjk]

/-- The product standard-normal reference law for the changing environment. -/
-- @node: normalReplicateReference
noncomputable def normalReplicateReference (p n : ℕ) :
    Measure (Fin n → Fin p → ℝ) :=
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1

/-- The Gaussian exponential likelihood is normalized over independent replicates. -/
-- @node: normalReplicate_normalized
lemma normalReplicate_normalized {p n : ℕ} (j : Fin p) (h : ℝ) :
    Integrable (normalReplicateLikelihood (n := n) j h) (normalReplicateReference p n) ∧
    (∫ x, normalReplicateLikelihood (n := n) j h x ∂normalReplicateReference p n) = 1 := by
  have heval := measurePreserving_eval (fun _ : Fin p => gaussianReal 0 1) j
  have hcoord : Integrable (fun x : Fin p → ℝ => normalTilt h (x j))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
    heval.integrable_comp_of_integrable (normalTilt_integrable_moments h).1
  have hmean : (∫ x : Fin p → ℝ, normalTilt h (x j)
      ∂Measure.pi (fun _ : Fin p => gaussianReal 0 1)) = 1 := by
    have hi := heval.hasLaw.integral_comp (f := normalTilt h)
      (by unfold normalTilt; fun_prop)
    calc
      _ = ∫ x, normalTilt h x ∂gaussianReal 0 1 := by
        simpa only [Function.comp_apply, Function.eval] using hi
      _ = 1 := (normalTilt_moments h).1
  constructor
  · exact Integrable.fintype_prod (fun _ : Fin n => hcoord)
  · change (∫ x : Fin n → Fin p → ℝ, ∏ r, normalTilt h (x r j)
        ∂Measure.pi (fun _ : Fin n => Measure.pi fun _ : Fin p => gaussianReal 0 1)) = 1
    rw [integral_fintype_prod_eq_prod (fun _ : Fin n =>
      fun z : Fin p → ℝ => normalTilt h (z j))]
    simp [hmean]

/-- The alternative latent law, expressed by its explicit Gaussian exponential tilt. -/
-- @node: normalReplicateTiltLaw
noncomputable def normalReplicateTiltLaw {p n : ℕ} (j : Fin p) (h : ℝ) :
    Measure (Fin n → Fin p → ℝ) :=
  (normalReplicateReference p n).withDensity
    (fun x => ENNReal.ofReal (normalReplicateLikelihood j h x))

/-- The tilted latent law is a probability law. -/
-- @node: normalReplicateTiltLaw_probability
lemma normalReplicateTiltLaw_probability {p n : ℕ} (j : Fin p) (h : ℝ) :
    IsProbabilityMeasure (normalReplicateTiltLaw (n := n) j h) := by
  refine ⟨?_⟩
  rw [normalReplicateTiltLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (normalReplicate_normalized (n := n) j h).1]
  · rw [(normalReplicate_normalized (n := n) j h).2]
    norm_num
  · exact Filter.Eventually.of_forall (fun x => by
      unfold normalReplicateLikelihood normalTilt
      positivity)

/-- The explicit exponential tilt is the real Radon--Nikodym likelihood. -/
-- @node: normalReplicateTiltLaw_rnDeriv
lemma normalReplicateTiltLaw_rnDeriv {p n : ℕ} (j : Fin p) (h : ℝ) :
    (fun x => ((normalReplicateTiltLaw (n := n) j h).rnDeriv
      (normalReplicateReference p n) x).toReal) =ᵐ[normalReplicateReference p n]
      normalReplicateLikelihood j h := by
  have hmeas : Measurable (fun x : Fin n → Fin p → ℝ =>
      ENNReal.ofReal (normalReplicateLikelihood j h x)) := by
    unfold normalReplicateLikelihood normalTilt
    fun_prop
  have : IsProbabilityMeasure (normalReplicateReference p n) := by
    unfold normalReplicateReference
    infer_instance
  filter_upwards [Measure.rnDeriv_withDensity (normalReplicateReference p n) hmeas]
    with x hx
  rw [normalReplicateTiltLaw, hx, ENNReal.toReal_ofReal]
  unfold normalReplicateLikelihood normalTilt
  positivity

/-- Orthogonal likelihood perturbations give the exact chi-squared divergence
of their uniform mixture. This is the finite-mixture calculation used for the
Gaussian alternatives before applying the common observation kernel. -/
-- @node: orthogonal_mixture_chiSq
lemma orthogonal_mixture_chiSq {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] [DecidableEq S]
    (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) P)
    (δ : ℝ)
    (hoverlap : ∀ s t, (∫ x, ((Q s).rnDeriv P x).toReal *
      ((Q t).rnDeriv P x).toReal ∂P) = 1 + if s = t then δ else 0) :
    Causalean.Stat.chiSqDiv
      (Causalean.Stat.Minimax.Mixture.uniformMixture Q) P =
      δ / (Fintype.card S : ℝ) := by
  have hbase := Causalean.Stat.Minimax.Mixture.one_add_chiSqDiv_uniformMixture
    Q P hac hpair
  classical
  simp_rw [hoverlap] at hbase
  have hdiag : (∑ s : S, ∑ t : S, if s = t then δ else 0) =
      (Fintype.card S : ℝ) * δ := by simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hbase
  rw [hdiag] at hbase
  have hcard : (Fintype.card S : ℝ) ≠ 0 := by positivity
  field_simp at hbase ⊢
  nlinarith

/-- The exact latent chi-squared calculation: only equal-coordinate alternatives
contribute to the excess second moment of the uniform mixture. -/
-- @node: normalReplicateMixture_chiSq
lemma normalReplicateMixture_chiSq {p n : ℕ} {S : Type*}
    [Fintype S] [Nonempty S] [DecidableEq S] (f : S ↪ Fin p) (h : ℝ) :
    Causalean.Stat.chiSqDiv
      (Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun s => normalReplicateTiltLaw (n := n) (f s) h))
      (normalReplicateReference p n) =
      (Real.exp ((n : ℝ) * h ^ 2) - 1) / (Fintype.card S : ℝ) := by
  let P := normalReplicateReference p n
  let Q := fun s : S => normalReplicateTiltLaw (n := n) (f s) h
  have : IsProbabilityMeasure P := by
    dsimp [P, normalReplicateReference]
    infer_instance
  have (s : S) : IsProbabilityMeasure (Q s) := normalReplicateTiltLaw_probability (f s) h
  have hac (s : S) : Q s ≪ P := withDensity_absolutelyContinuous _ _
  have hpair (s t : S) :
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) =ᵐ[P]
        fun x => normalReplicateLikelihood (f s) h x *
          normalReplicateLikelihood (f t) h x :=
    (normalReplicateTiltLaw_rnDeriv (f s) h).mul (normalReplicateTiltLaw_rnDeriv (f t) h)
  apply orthogonal_mixture_chiSq Q P hac
    (fun s t => (normalReplicate_overlap (n := n) (f s) (f t) h).1.congr (hpair s t).symm)
  intro s t
  rw [integral_congr_ae (hpair s t)]
  change (∫ x, normalReplicateLikelihood (f s) h x * normalReplicateLikelihood (f t) h x
    ∂normalReplicateReference p n) = _
  rw [normalReplicateReference, (normalReplicate_overlap (n := n) (f s) (f t) h).2]
  by_cases hst : s = t
  · simp [hst]
  · simp [hst, f.injective.ne hst]

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
