module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Global tail, design robust CATE model

The probability law is data: every risk statement ranges over a class of laws.
This is a bypass-justified use of product measures. `POSystem` and the CATE
estimation systems fix an ambient probability space and impose stronger overlap.
The model uses whole-space Hölder extensions with Euclidean domain norms and
induced derivative norms. Coordinate norm conversion is confined to proof bridges.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

-- @env: S1
variable (d n : ℕ) -- @realizes d(positive covariate dimension) @realizes n(positive sample size)
variable (M : ℝ) -- @realizes M(positive potential-outcome bound)

/-- Covariate cube. -/
def cube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) -- @realizes Xspace(unit cube)

/-- One latent unit `(X,A,Y(0),Y(1))`. -/
abbrev Full (d : ℕ) := (Fin d → ℝ) × Bool × ℝ × ℝ
  -- @realizes X(covariate carrier) @realizes A(binary treatment carrier)
  -- @realizes Y0(control potential-outcome carrier) @realizes Y1(treated potential-outcome carrier)

/-- One observed unit `(X,A,Y)`. -/
abbrev Obs (d : ℕ) := (Fin d → ℝ) × Bool × ℝ

/-- Observed response follows the selected potential outcome. -/
def observe {d : ℕ} (u : Full d) : Obs d :=
  (u.1, u.2.1, if u.2.1 then u.2.2.2 else u.2.2.1)
  -- @realizes Y(observed response from treatment and potential outcomes)

/-- A law carries selected versions of its propensity and two arm regressions. -/
structure Law (d : ℕ) where
  full : Measure (Full d) -- @realizes P(joint probability law; probability pinned by IidSampling)
  observed : Measure (Obs d) -- @realizes Y(observed law; tied to potentials by Consistency)
  observedRecord : Full d → Obs d -- @realizes Y(pathwise observed unit on the joint model)
  latentSample : (n : ℕ) → Measure (Fin n → Full d)
  sample : (n : ℕ) → Measure (Fin n → Obs d)
  e : (Fin d → ℝ) → ℝ -- @realizes e(propensity carrier; conditional-law tie in LawSemantics)
  mu1 : (Fin d → ℝ) → ℝ -- @realizes mu1(treated regression carrier; conditional-expectation tie)
  mu0 : (Fin d → ℝ) → ℝ -- @realizes mu0(control regression carrier; conditional-expectation tie)

/-- Observed pushforward law. -/
noncomputable def Law.obs {d : ℕ} (P : Law d) : Measure (Obs d) :=
  P.observed

/-- Covariate marginal. -/
noncomputable def Law.xLaw {d : ℕ} (P : Law d) : Measure (Fin d → ℝ) :=
  P.full.map Prod.fst

/-- CATE contrast. -/
def Law.tau {d : ℕ} (P : Law d) (x : Fin d → ℝ) : ℝ :=
  P.mu1 x - P.mu0 x -- @realizes tau(mu1 minus mu0)

/-- Expectation under the latent unit law. -/
noncomputable def Law.E {d : ℕ} (P : Law d) (f : Full d → ℝ) : ℝ :=
  ∫ u, f u ∂P.full -- @realizes EP(expectation under P)

/-- Law-side nuisance versions are tied to the conditional laws of the latent
potential outcomes and treatment. Their cube ranges are part of their types in
the paper. -/
def LawSemantics {d : ℕ} (P : Law d) (M : ℝ) : Prop :=
  (P.full[(fun u : Full d => if u.2.1 then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance]
        =ᵐ[P.full] fun u => P.e u.1) ∧ -- @realizes e(P(A=1 given X))
  (P.full[(fun u : Full d => u.2.2.2) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance]
        =ᵐ[P.full] fun u => P.mu1 u.1) ∧ -- @realizes mu1(E[Y1 given X])
  (P.full[(fun u : Full d => u.2.2.1) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance]
        =ᵐ[P.full] fun u => P.mu0 u.1) ∧ -- @realizes mu0(E[Y0 given X])
  (∀ x ∈ cube d, P.e x ∈ Set.Icc (0 : ℝ) 1) ∧ -- @realizes e(range [0,1])
  (∀ x ∈ cube d, P.mu1 x ∈ Set.Icc (-M) M) ∧ -- @realizes mu1(range [-M,M])
  (∀ x ∈ cube d, P.mu0 x ∈ Set.Icc (-M) M) -- @realizes mu0(range [-M,M])

-- @env: S2
variable (β γ C L κ : ℝ)
  -- @realizes beta(positive smoothness) @realizes gamma(tail parameter above one)
  -- @realizes C(global tail constant at least one) @realizes L(positive Hölder radius)
  -- @realizes kappa(control overlap in (0,1))

/-- Ranges of the public class parameters. -/
def ParameterDomain (d : ℕ) (β γ C L M : ℝ) : Prop :=
  1 ≤ d ∧ 0 < β ∧ 1 < γ ∧ 1 ≤ C ∧ 0 < L ∧ 0 < M
  -- @realizes d(positive) @realizes beta(positive) @realizes gamma(above one)
  -- @realizes C(at least one) @realizes L(positive) @realizes M(positive)

/-- Global lower-tail exponent. -/
def tailExponent (γ : ℝ) : ℝ := γ - 1 -- @realizes q(gamma minus one)

/-- Effective dimension. -/
noncomputable def effectiveDimension (d : ℕ) (γ : ℝ) : ℝ :=
  (d : ℝ) * γ / (γ - 1) -- @realizes D(d gamma divided by gamma minus one)

/-- The coordinate identification from Euclidean space to the sup-norm Pi space.
Its inverse is `WithLp.toLp 2`; the identification is not an isometry. -/
noncomputable def euclideanCoordinates (d : ℕ) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

/-- Whole-space isotropic Hölder ball with Euclidean domain norm and induced
multilinear operator norms. The same radius bounds the value (order zero),
every derivative through `ceil β - 1`, and the top derivative's modulus. -/
def HolderBallEuclid {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (β L : ℝ) : Prop :=
  ContDiff ℝ (⌈β⌉₊ - 1) g ∧
    (∀ j : ℕ, j ≤ ⌈β⌉₊ - 1 → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ L) ∧
    (∀ x y,
      ‖iteratedFDeriv ℝ (⌈β⌉₊ - 1) g x - iteratedFDeriv ℝ (⌈β⌉₊ - 1) g y‖ ≤
        L * ‖x - y‖ ^ (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)))
  -- @realizes HbetaL(global Euclidean derivative and modulus bounds at radius L)

/-- Euclidean Hölder bounds transfer to coordinate sup-norm bounds with a
factor depending only on dimension and smoothness. The inflated radius is for
Taylor approximation, not for membership in the model class. -/
-- @node: holderBallEuclid_to_std
lemma holderBallEuclid_to_std (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ),
      HolderBallEuclid g β L →
        Causalean.Stat.Nonparametric.HolderBallStd
          (fun x => g (WithLp.toLp 2 x)) β (A * L) Set.univ := by
  let T : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (euclideanCoordinates d).symm.toContinuousLinearMap
  let B : ℝ := max ‖T‖ 1
  let m : ℕ := ⌈β⌉₊ - 1
  let α : ℝ := β - (m : ℝ)
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hTB : ‖T‖ ≤ B := le_max_left _ _
  have hα : 0 ≤ α := by
    dsimp [α, m]
    rw [Nat.cast_sub (Nat.one_le_ceil_iff.mpr hβ), Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hβ.le]
  have hBα : 1 ≤ B ^ α := Real.one_le_rpow hB1 hα
  refine ⟨B ^ m * B ^ α, by positivity, ?_⟩
  intro g L hg
  have hL : 0 ≤ L := (norm_nonneg _).trans
    (hg.2.1 0 (Nat.zero_le _) 0)
  have hjet (j : ℕ) (hj : j ≤ m) (x : Fin d → ℝ) :
      iteratedFDeriv ℝ j (g ∘ T) x =
        (iteratedFDeriv ℝ j g (T x)).compContinuousLinearMap (fun _ => T) :=
    T.iteratedFDeriv_comp_right hg.1 x (by
      change ((j : ℕ∞) : WithTop ℕ∞) ≤
        ((⌈β⌉₊ : ℕ∞) : WithTop ℕ∞) - ((1 : ℕ∞) : WithTop ℕ∞)
      have he := ENat.natCast_sub ⌈β⌉₊ 1
      simp only [Nat.cast_one] at he
      rw [← WithTop.coe_sub, ← he]
      exact_mod_cast hj)
  change Causalean.Stat.Nonparametric.HolderBallStd (g ∘ T) β
    (B ^ m * B ^ α * L) Set.univ
  refine ⟨hg.1.comp_continuousLinearMap.contDiffOn, ?_, ?_⟩
  · intro j hj x _
    rw [hjet j hj x]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j g (T x)‖ * ∏ _ : Fin j, ‖T‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ L * B ^ j := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul (hg.2.1 j hj _) (pow_le_pow_left₀ (norm_nonneg _) hTB j)
          (pow_nonneg (norm_nonneg _) _) hL
      _ ≤ L * B ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hj) hL
      _ ≤ B ^ m * B ^ α * L := by
        have := mul_le_mul_of_nonneg_left hBα (mul_nonneg hL (pow_nonneg hB.le m))
        nlinarith
  · intro x _ y _
    rw [hjet m le_rfl x, hjet m le_rfl y]
    have hsub :
        (iteratedFDeriv ℝ m g (T x)).compContinuousLinearMap (fun _ => T) -
          (iteratedFDeriv ℝ m g (T y)).compContinuousLinearMap (fun _ => T) =
        (iteratedFDeriv ℝ m g (T x) - iteratedFDeriv ℝ m g (T y)).compContinuousLinearMap
          (fun _ => T) := by
      ext v
      simp
    rw [hsub]
    have hdist : ‖T x - T y‖ ≤ B * ‖x - y‖ := by
      rw [← T.map_sub]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTB (norm_nonneg _))
    calc
      _ ≤ ‖iteratedFDeriv ℝ m g (T x) - iteratedFDeriv ℝ m g (T y)‖ *
          ∏ _ : Fin m, ‖T‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (L * ‖T x - T y‖ ^ α) * B ^ m := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul (hg.2.2 _ _) (pow_le_pow_left₀ (norm_nonneg _) hTB m)
          (pow_nonneg (norm_nonneg _) _) (mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ (L * (B * ‖x - y‖) ^ α) * B ^ m := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB.le m)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hα) hL
      _ = B ^ m * B ^ α * L * ‖x - y‖ ^ α := by
        rw [Real.mul_rpow hB.le (norm_nonneg _)]
        ring


/-- Sup-norm whole-space Hölder bounds imply Euclidean bounds at the same
radius, since the coordinate map from Euclidean space has operator norm at
most one. This direction preserves the existing tensor-witness estimates. -/
-- @node: holderBallStd_to_euclid
lemma holderBallStd_to_euclid {d : ℕ} {f : (Fin d → ℝ) → ℝ} {β L : ℝ}
    (hβ : 0 < β)
    (hf : Causalean.Stat.Nonparametric.HolderBallStd f β L Set.univ) :
    HolderBallEuclid (fun x => f (WithLp.ofLp x)) β L := by
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ) :=
    (euclideanCoordinates d).toContinuousLinearMap
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound (by norm_num)
    intro x
    change ‖WithLp.ofLp x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun i => PiLp.norm_apply_le x i)
  have hreg : ContDiff ℝ (⌈β⌉₊ - 1) f := contDiffOn_univ.mp hf.1
  have hα : 0 ≤ β - ((⌈β⌉₊ - 1 : ℕ) : ℝ) := by
    have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hβ).ne'
    rw [Nat.cast_sub hceil, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hβ.le]
  change HolderBallEuclid (f ∘ T) β L
  have hjet (j : ℕ) (hj : j ≤ ⌈β⌉₊ - 1) (x : EuclideanSpace ℝ (Fin d)) :
      iteratedFDeriv ℝ j (f ∘ T) x =
        (iteratedFDeriv ℝ j f (T x)).compContinuousLinearMap (fun _ => T) :=
    T.iteratedFDeriv_comp_right hreg x (by
      change ((j : ℕ∞) : WithTop ℕ∞) ≤
        ((⌈β⌉₊ : ℕ∞) : WithTop ℕ∞) - ((1 : ℕ∞) : WithTop ℕ∞)
      have he := ENat.natCast_sub ⌈β⌉₊ 1
      simp only [Nat.cast_one] at he
      rw [← WithTop.coe_sub, ← he]
      exact_mod_cast hj)
  refine ⟨hreg.comp_continuousLinearMap, ?_, ?_⟩
  · intro j hj x
    rw [hjet j hj x]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f (T x)‖ * ∏ _ : Fin j, ‖T‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ j f (T x)‖ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hT)
      _ ≤ L := hf.2.1 j hj (T x) (Set.mem_univ _)
  · intro x y
    rw [hjet _ le_rfl x, hjet _ le_rfl y]
    have hsub :
        (iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T x)).compContinuousLinearMap (fun _ => T) -
          (iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T y)).compContinuousLinearMap (fun _ => T) =
        (iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T x) -
          iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T y)).compContinuousLinearMap (fun _ => T) := by
      ext v
      simp
    rw [hsub]
    have hL : 0 ≤ L := (norm_nonneg _).trans
      (hf.2.1 0 (Nat.zero_le _) (fun _ => 0) (Set.mem_univ _))
    calc
      _ ≤ ‖iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T x) -
          iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T y)‖ * ∏ _ : Fin (⌈β⌉₊ - 1), ‖T‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T x) -
          iteratedFDeriv ℝ (⌈β⌉₊ - 1) f (T y)‖ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hT)
      _ ≤ L * ‖T x - T y‖ ^ (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) :=
        hf.2.2 _ (Set.mem_univ _) _ (Set.mem_univ _)
      _ ≤ L * ‖x - y‖ ^ (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply Real.rpow_le_rpow (norm_nonneg _) _ hα
        rw [← T.map_sub]
        exact (T.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hT)


/-- Ambient Euclidean extension definition of the isotropic Hölder ball on
the cube, with the exact class radius. -/
def holderOnCube {d : ℕ} (f : (Fin d → ℝ) → ℝ) (β L : ℝ) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
    HolderBallEuclid g β L ∧
      ∀ x ∈ cube d, f x = g (WithLp.toLp 2 x)
      -- @realizes HbetaL(restriction of an ambient Euclidean Hölder extension at radius L)

/-- A cube-class member supplies a global coordinate representative for the
Causalean Taylor lemma, with a uniform dimension/smoothness radius factor. -/
lemma holderOnCube_std_extension (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ A : ℝ, 0 < A ∧ ∀ (f : (Fin d → ℝ) → ℝ) (L : ℝ),
      holderOnCube f β L → ∃ g : (Fin d → ℝ) → ℝ,
        Causalean.Stat.Nonparametric.HolderBallStd g β (A * L) Set.univ ∧
          ∀ x ∈ cube d, f x = g x := by
  obtain ⟨A, hA, hbridge⟩ := holderBallEuclid_to_std d β hβ
  refine ⟨A, hA, ?_⟩
  intro f L hf
  obtain ⟨g, hg, heq⟩ := hf
  exact ⟨fun x => g (WithLp.toLp 2 x), hbridge g L hg, heq⟩

-- @node: ass:iid
/-- Every positive-size latent sample has the iid product law, and its observed
sample is the pathwise image. The zero-size measures are unconstrained. -/
def IidSampling {d : ℕ} (P : Law d) : Prop :=
  IsProbabilityMeasure P.full ∧
  (∀ n : ℕ, 0 < n → P.latentSample n = Measure.pi (fun _ : Fin n => P.full)) ∧
  ∀ n : ℕ, 0 < n →
    P.sample n = (P.latentSample n).map (fun units i => P.observedRecord (units i))

-- @node: ass:uniform-design
/-- The covariate law is uniform on the unit cube. -/
def UniformDesign {d : ℕ} (P : Law d) : Prop :=
  P.xLaw = volume.restrict (cube d) -- @realizes X(uniform on unit cube)

-- @node: ass:bounded-outcomes
/-- Both potential outcomes lie in `[-M,M]` almost surely. -/
def BoundedOutcomes {d : ℕ} (P : Law d) (M : ℝ) : Prop :=
  ∀ᵐ u ∂P.full, |u.2.2.1| ≤ M ∧ |u.2.2.2| ≤ M
  -- @realizes Y0(a.s. bounded) @realizes Y1(a.s. bounded)

-- @node: ass:consistency
/-- The observed response equals the selected potential outcome in the given
joint model, and its recorded law is the corresponding pushforward. -/
def Consistency {d : ℕ} (P : Law d) : Prop :=
  (∀ᵐ u ∂P.full, P.observedRecord u = observe u) ∧
    P.obs = P.full.map P.observedRecord -- @realizes Y(pathwise consistency and observed law)

-- @node: ass:exchangeability
/-- Joint conditional exchangeability of both potential outcomes and treatment. -/
def Exchangeability {d : ℕ} (P : Law d) : Prop :=
  ∀ [IsFiniteMeasure P.full], ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap (fun u : Full d => u.1) inferInstance)
    (Measurable.comap_le (by fun_prop : Measurable (fun u : Full d => u.1)))
    (fun u : Full d => (u.2.2.1, u.2.2.2))
    (fun u : Full d => u.2.1) P.full

-- @node: ass:measurable-propensity
/-- A measurable propensity version on the cube. -/
def MeasurablePropensity {d : ℕ} (P : Law d) : Prop :=
  Measurable (fun x : cube d => P.e x) ∧
    ∀ x ∈ cube d, P.e x ∈ Set.Icc (0 : ℝ) 1
  -- @realizes e(Borel measurable, range [0,1])

-- @node: ass:global-tail
/-- Global lower-tail envelope of the propensity. -/
def GlobalTail {d : ℕ} (P : Law d) (C γ : ℝ) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    (P.xLaw).real {x | P.e x ≤ t} ≤ C * t ^ tailExponent γ
    -- @realizes e(global lower tail)

-- @node: ass:treated-holder
/-- The treated conditional mean is in the specified Hölder ball. -/
def TreatedHolder {d : ℕ} (P : Law d) (β L : ℝ) : Prop :=
  holderOnCube P.mu1 β L -- @realizes mu1(Hölder member)

-- @node: ass:control-holder
/-- The control conditional mean is in the specified Hölder ball. -/
def ControlHolder {d : ℕ} (P : Law d) (β L : ℝ) : Prop :=
  holderOnCube P.mu0 β L -- @realizes mu0(Hölder member)

-- @node: ass:control-overlap
/-- One-sided overlap for the control arm. -/
def ControlOverlap {d : ℕ} (P : Law d) (κ : ℝ) : Prop :=
  ∀ᵐ x ∂P.xLaw, κ ≤ 1 - P.e x -- @realizes e(control-arm overlap)

-- @node: def:law-class
/-- The unrestricted measurable-propensity class, including the law-side
semantic ties for the propensity and conditional potential-outcome means. -/
structure LawClass (d : ℕ) (β γ C L M : ℝ) (P : Law d) : Prop where
  parameters : ParameterDomain d β γ C L M -- @realizes Pclass(public parameter domain)
  semantics : LawSemantics P M -- @realizes Pclass(nuisance versions pinned to law)
  iid : IidSampling P
  uniformDesign : UniformDesign P
  boundedOutcomes : BoundedOutcomes P M
  consistency : Consistency P
  exchangeability : Exchangeability P
  measurablePropensity : MeasurablePropensity P
  globalTail : GlobalTail P C γ
  treatedHolder : TreatedHolder P β L
  -- @realizes Pclass(all primary member properties)

-- @node: def:cate-class
/-- Smooth-control CATE class extending the primary law class. -/
structure CATEClass (d : ℕ) (β γ C L M κ : ℝ) (P : Law d) : Prop
    extends LawClass d β γ C L M P where
  controlHolder : ControlHolder P β L
  controlOverlap : ControlOverlap P κ
  controlParameter : 0 < κ ∧ κ < 1 -- @realizes kappa(in (0,1))
  -- @realizes CATEclass(primary class with control smoothness and overlap)

/-- The fixed bandwidth scale at the effective dimension. -/
noncomputable def rateWidth (d n : ℕ) (β γ : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / (2 * β + effectiveDimension d γ))

end CausalSmith.Stat.GlobalTailDesignRobustCate
