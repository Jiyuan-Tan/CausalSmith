import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.AffinePathTopology
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CompactCondIndepBridge
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.TSparseWitnessCertificate
import Causalean.Stat.Sample.PiTransport
import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Main
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Topology.TietzeExtension

/-!
# Analytic edge perturbation

The lemma states the path integral identity, analytic nonidentity certificate,
isolated-zero property, and arbitrarily small stratum-preserving perturbation.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- A strict uniform lower bound for finitely many affine families on a compact space defines an
open set of parameters.  Given [the stated inputs and conditions](hyp:ha,hb), [the stated conclusion](goal) follows. -/
lemma isOpen_affine_forall_gt
    {ι X : Type*} [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
    [TopologicalSpace X] [CompactSpace X]
    (a b : ι → X → ℝ) (c : ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i)) :
    IsOpen {t : ℝ | ∀ i x, c < (1 - t) * a i x + t * b i x} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hcompact : IsCompact (Set.univ : Set (ι × X)) := isCompact_univ
  have ha' : Continuous (fun z : ι × X ↦ a z.1 z.2) :=
    continuous_prod_of_discrete_left.mpr ha
  have hb' : Continuous (fun z : ι × X ↦ b z.1 z.2) :=
    continuous_prod_of_discrete_left.mpr hb
  have hevent : ∀ᶠ u in 𝓝 t, ∀ z : ι × X,
      c < (1 - u) * a z.1 z.2 + u * b z.1 z.2 := by
    simpa only [Set.mem_univ, forall_const] using
      (hcompact.eventually_forall_of_forall_eventually (x₀ := t)
        (P := fun u z ↦ c < (1 - u) * a z.1 z.2 + u * b z.1 z.2) (by
          intro z _
          apply (show ContinuousAt (fun w : ℝ × (ι × X) ↦
              (1 - w.1) * a w.2.1 w.2.2 + w.1 * b w.2.1 w.2.2) (t, z) by
            exact (((continuous_const.sub continuous_fst).mul
              (ha'.comp continuous_snd)).add
                (continuous_fst.mul (hb'.comp continuous_snd))).continuousAt).tendsto
          exact Ioi_mem_nhds (ht z.1 z.2)))
  filter_upwards [hevent] with u hu
  exact fun i x ↦ hu (i, x)

/-- Strict affine lower-bound constraints are convex in the scalar parameter.  [the stated conclusion](goal) follows. -/
lemma convex_affine_forall_gt
    {iota X : Type*} (a b : iota → X → ℝ) (c : ℝ) :
    Convex ℝ {t : ℝ | ∀ i x, c < (1 - t) * a i x + t * b i x} := by
  intro x hx y hy u v hu hv huv i z
  change c < (1 - (u * x + v * y)) * a i z + (u * x + v * y) * b i z
  have hx' := hx i z
  have hy' := hy i z
  have hvEq : v = 1 - u := by linarith
  rw [show (1 - (u * x + v * y)) * a i z + (u * x + v * y) * b i z =
      u * ((1 - x) * a i z + x * b i z) +
        v * ((1 - y) * a i z + y * b i z) by
    rw [hvEq]
    ring,
    show c = u * c + v * c by rw [hvEq]; ring]
  by_cases hupos : 0 < u
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx' hupos)
      (mul_le_mul_of_nonneg_left hy'.le hv)
  · have hvpos : 0 < v := by linarith
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx'.le hu)
      (mul_lt_mul_of_pos_left hy' hvpos)

-- @node: pairFinEquiv
/-- The ordered two-point finset is equivalent to `Fin 2`. -/
def pairFinEquiv {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) :
    Fin 2 ≃ {x : α // x ∈ ({a, b} : Finset α)} where
  toFun k := if hk : k = 0 then ⟨a, by simp⟩ else ⟨b, by simp⟩
  invFun x := if x.1 = a then 0 else 1
  left_inv k := by
    fin_cases k
    · simp
    · simp [Ne.symm hab]
  right_inv x := by
    apply Subtype.ext
    simp only
    by_cases hx : x.1 = a
    · simp [hx]
    · have hxmem := x.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      have hxb : x.1 = b := hxmem.resolve_left hx
      simp [hxb, Ne.symm hab]

-- @node: integral_fin_two_pi_eq_iterated
/-- Fubini's theorem for a two-coordinate product measure in coordinate order.  Given [the stated inputs and conditions](hyp:hf), [the stated conclusion](goal) follows. -/
lemma integral_fin_two_pi_eq_iterated (μ : Measure ℝ) [SigmaFinite μ]
    (f : (Fin 2 → ℝ) → ℝ) (hf : Integrable f (Measure.pi fun _ : Fin 2 => μ)) :
    (∫ v, f v ∂Measure.pi fun _ : Fin 2 => μ) =
      ∫ x, (∫ y, f ![x, y] ∂μ) ∂μ := by
  let e2 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  have he2 := (measurePreserving_piFinSuccAbove (fun _ : Fin 2 => μ) 0).symm
  have hf2 : Integrable (f ∘ e2.symm) (μ.prod (Measure.pi fun _ : Fin 1 => μ)) :=
    (he2.integrable_comp_emb e2.symm.measurableEmbedding).2 hf
  rw [← he2.integral_comp e2.symm.measurableEmbedding]
  have hf2' := hf2
  change Integrable (fun z => f (e2.symm z))
    (μ.prod (Measure.pi fun _ : Fin 1 => μ)) at hf2'
  rw [integral_prod _ hf2']
  apply integral_congr_ae
  filter_upwards [hf2'.prod_right_ae] with x hfx
  let e1 := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he1 := (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm
  rw [← he1.integral_comp e1.symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Direct-edge contrast along the identity-target affine path. -/
def affinePathContrast {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (t : ℝ) : ℝ :=
  let θt := affinePathExtension s θ hji t
  secondMomentContrast (canonicalObservedWorld G θt (Equiv.refl (Fin n))) j i

/-- The explicit rational-integral expression for the direct-edge path contrast. -/
def affinePathContrastIntegral {n : ℕ} {G : Causalean.DAG (Fin n)}
    (s : SignVector n) (θ : StratumPoint G s) {j i : Fin n}
    (hji : G.edge j i) (t : ℝ) : ℝ :=
  let θt := affinePathExtension s θ hji t
  ∫ v in latentCube n,
    (θt.q i (v i)) ^ 2 * (θt.q j (v j) - θt.p j v) *
      (∏ l ∈ (Finset.univ.erase i).erase j, θt.p l v) / θt.p i v

/-- The degree-one polynomial whose value at `t` is the affine interpolation from `a` to `b`. -/
def affineFactorPolynomial (a b : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.X * Polynomial.C (b - a)

/-- The [degree-one factor polynomial evaluates to affine interpolation](goal). -/
@[simp] lemma affineFactorPolynomial_eval (a b t : ℝ) :
    (affineFactorPolynomial a b).eval t = (1 - t) * a + t * b := by
  simp [affineFactorPolynomial]
  ring

/-- The [affine factor polynomial has degree at most one](goal). -/
lemma affineFactorPolynomial_natDegree_le_one (a b : ℝ) :
    (affineFactorPolynomial a b).natDegree ≤ 1 := by
  unfold affineFactorPolynomial
  compute_degree

/-- Polynomial encoding of the complete numerator in `affinePathContrastIntegral`. -/
def affinePathNumeratorPolynomial
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (v : LatentState n) : Polynomial ℝ :=
  let θstar := embeddedSparseWitness s hji
  (affineFactorPolynomial (θs.1.q i (v i)) (θstar.q i (v i))) ^ 2 *
    (affineFactorPolynomial (θs.1.q j (v j)) (θstar.q j (v j)) -
      affineFactorPolynomial (θs.1.p j v) (θstar.p j v)) *
    ∏ l ∈ (Finset.univ.erase i).erase j,
      affineFactorPolynomial (θs.1.p l v) (θstar.p l v)

/-- Evaluating the numerator polynomial recovers exactly the affine-path numerator.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathNumeratorPolynomial_eval
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (t : ℝ) (v : LatentState n) :
    (affinePathNumeratorPolynomial s θs hji v).eval t =
      ((affinePathExtension s θs hji t).q i (v i)) ^ 2 *
      ((affinePathExtension s θs hji t).q j (v j) -
          (affinePathExtension s θs hji t).p j v) *
        (∏ l ∈ (Finset.univ.erase i).erase j,
          (affinePathExtension s θs hji t).p l v) := by
  unfold affinePathNumeratorPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]
  simp_rw [Polynomial.eval_prod]
  simp [affinePathExtension]

/-- Coefficients of the affine-path numerator, padded to the uniform degree bound `n + 3`. -/
def affinePathNumeratorCoefficient
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    Fin (n + 3 + 1) → LatentState n → ℝ :=
  fun k v ↦ (affinePathNumeratorPolynomial s θs hji v).coeff k

/-- If [every coefficient of the first polynomial family is continuous](hyp:hP) and [every
coefficient of the second is continuous](hyp:hQ), then [each product coefficient is continuous](goal). -/
lemma continuousOn_polynomial_mul_coeff
    {α : Type*} [TopologicalSpace α] {K : Set α}
    {P Q : α → Polynomial ℝ}
    (hP : ∀ k, ContinuousOn (fun x ↦ (P x).coeff k) K)
    (hQ : ∀ k, ContinuousOn (fun x ↦ (Q x).coeff k) K)
    (k : ℕ) : ContinuousOn (fun x ↦ (P x * Q x).coeff k) K := by
  simp only [Polynomial.coeff_mul]
  exact continuousOn_finsetSum _ fun ij _ ↦ (hP ij.1).mul (hQ ij.2)

/-- If [the first endpoint varies continuously](hyp:ha) and [the second endpoint varies
continuously](hyp:hb), then [every affine-factor coefficient varies continuously](goal). -/
lemma continuousOn_affineFactorPolynomial_coeff
    {α : Type*} [TopologicalSpace α] {K : Set α} {a b : α → ℝ}
    (ha : ContinuousOn a K) (hb : ContinuousOn b K) (k : ℕ) :
    ContinuousOn (fun x ↦ (affineFactorPolynomial (a x) (b x)).coeff k) K := by
  rcases k with _ | k
  · simpa [affineFactorPolynomial] using ha
  · rcases k with _ | k
    · have h := hb.sub ha
      change ContinuousOn (fun x ↦ b x - a x) K at h
      simpa [affineFactorPolynomial, Polynomial.coeff_X_mul] using h
    · simp [affineFactorPolynomial]
      fun_prop

/-- If [every coefficient in a finite polynomial family is continuous](hyp:hP), then [every
coefficient of its finite product is continuous](goal). -/
lemma continuousOn_polynomial_finsetProd_coeff
    {α ι : Type*} [TopologicalSpace α] [DecidableEq ι]
    {K : Set α} (S : Finset ι) (P : ι → α → Polynomial ℝ)
    (hP : ∀ i ∈ S, ∀ k, ContinuousOn (fun x ↦ (P i x).coeff k) K)
    (k : ℕ) : ContinuousOn (fun x ↦ (∏ i ∈ S, P i x).coeff k) K := by
  classical
  revert hP k
  induction S using Finset.induction_on with
  | empty =>
      intro _ k
      simp
      fun_prop
  | @insert a S ha ih =>
      intro hP k
      simp only [Finset.prod_insert ha]
      exact continuousOn_polynomial_mul_coeff
        (fun m ↦ hP a (by simp) m)
        (fun m ↦ ih (fun i hi k ↦ hP i (by simp [hi]) k) m) k

/-- The uniform padding bound really contains every numerator coefficient.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathNumeratorPolynomial_natDegree_lt
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (v : LatentState n) :
    (affinePathNumeratorPolynomial s θs hji v).natDegree < n + 3 + 1 := by
  unfold affinePathNumeratorPolynomial
  calc
    _ ≤ 2 * 1 + 1 + ∑ l ∈ (Finset.univ.erase i).erase j, 1 := by
      refine Polynomial.natDegree_mul_le.trans ?_
      refine Nat.add_le_add ?_ ?_
      · exact Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add
            (Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul_left 2 (affineFactorPolynomial_natDegree_le_one _ _)))
            ((Polynomial.natDegree_sub_le _ _).trans
              (max_le (affineFactorPolynomial_natDegree_le_one _ _)
                (affineFactorPolynomial_natDegree_le_one _ _))))
      · calc
          _ ≤ ∑ l ∈ (Finset.univ.erase i).erase j,
              (affineFactorPolynomial (θs.1.p l v)
                ((embeddedSparseWitness s hji).p l v)).natDegree :=
            Polynomial.natDegree_prod_le ((Finset.univ.erase i).erase j)
              (fun l ↦ affineFactorPolynomial (θs.1.p l v)
                ((embeddedSparseWitness s hji).p l v))
          _ ≤ ∑ l ∈ (Finset.univ.erase i).erase j, 1 :=
            Finset.sum_le_sum fun l _ ↦ affineFactorPolynomial_natDegree_le_one _ _
    _ ≤ n + 3 := by
      have hc : ((Finset.univ.erase i).erase j).card ≤ n := by
        calc
          _ ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (by simp)
          _ = n := Finset.card_fin n
      simpa [Finset.sum_const, Nat.add_comm] using Nat.add_le_add_left hc 3
    _ < n + 3 + 1 := Nat.lt_succ_self _

/-- The padded coefficient family evaluates to the complete affine numerator.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathNumerator_polynomialNumerator_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (t : ℝ) (v : LatentState n) :
    Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator
      (n + 3) (affinePathNumeratorCoefficient s θs hji) t v =
      (affinePathNumeratorPolynomial s θs hji v).eval t := by
  rw [Polynomial.eval_eq_sum_range'
    (affinePathNumeratorPolynomial_natDegree_lt θs hji v)]
  unfold Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator
  simpa [affinePathNumeratorCoefficient] using
    (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
      (affinePathNumeratorPolynomial s θs hji v).coeff k * t ^ k) (n + 3 + 1))

/-- Every padded numerator coefficient is continuous on the compact latent cube.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathNumeratorCoefficient_continuousOn
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (k : Fin (n + 3 + 1)) :
    ContinuousOn (affinePathNumeratorCoefficient s θs hji k) (latentCube n) := by
  let θstar := embeddedSparseWitness s hji
  have hθ := θs.property.positiveSmooth
  have hstar := embeddedSparseWitness_positive_normalized_smooth s hji
  have hpθ (l : Fin n) : ContinuousOn (θs.1.p l) (latentCube n) :=
    (hθ.2.2.1 l).continuousOn
  have hpstar (l : Fin n) : ContinuousOn (θstar.p l) (latentCube n) :=
    (hstar.2.2.1 l).continuousOn
  have hqθ (l : Fin n) : ContinuousOn (fun v : LatentState n ↦ θs.1.q l (v l))
      (latentCube n) :=
    (hθ.2.2.2.1 l).continuousOn.comp ((continuous_apply l).continuousOn)
      (fun v hv ↦ hv l (Set.mem_univ l))
  have hqstar (l : Fin n) : ContinuousOn (fun v : LatentState n ↦ θstar.q l (v l))
      (latentCube n) :=
    (hstar.2.2.2.1 l).continuousOn.comp ((continuous_apply l).continuousOn)
      (fun v hv ↦ hv l (Set.mem_univ l))
  have hpfac (l : Fin n) (m : ℕ) : ContinuousOn (fun v ↦
      (affineFactorPolynomial (θs.1.p l v) (θstar.p l v)).coeff m)
      (latentCube n) :=
    continuousOn_affineFactorPolynomial_coeff (hpθ l) (hpstar l) m
  have hqfac (l : Fin n) (m : ℕ) : ContinuousOn (fun v ↦
      (affineFactorPolynomial (θs.1.q l (v l)) (θstar.q l (v l))).coeff m)
      (latentCube n) :=
    continuousOn_affineFactorPolynomial_coeff (hqθ l) (hqstar l) m
  have hqpow (m : ℕ) : ContinuousOn (fun v ↦
      ((affineFactorPolynomial (θs.1.q i (v i)) (θstar.q i (v i))) ^ 2).coeff m)
      (latentCube n) := by
    simpa only [pow_two] using continuousOn_polynomial_mul_coeff (hqfac i) (hqfac i) m
  have hdiff (m : ℕ) : ContinuousOn (fun v ↦
      (affineFactorPolynomial (θs.1.q j (v j)) (θstar.q j (v j)) -
        affineFactorPolynomial (θs.1.p j v) (θstar.p j v)).coeff m)
      (latentCube n) := by
    have h := (hqfac j m).sub (hpfac j m)
    change ContinuousOn (fun v ↦
      (affineFactorPolynomial (θs.1.q j (v j)) (θstar.q j (v j))).coeff m -
        (affineFactorPolynomial (θs.1.p j v) (θstar.p j v)).coeff m) (latentCube n) at h
    simpa only [Polynomial.coeff_sub] using h
  have hprod (m : ℕ) : ContinuousOn (fun v ↦
      (∏ l ∈ (Finset.univ.erase i).erase j,
        affineFactorPolynomial (θs.1.p l v) (θstar.p l v)).coeff m)
      (latentCube n) :=
    continuousOn_polynomial_finsetProd_coeff ((Finset.univ.erase i).erase j)
      (fun l v ↦ affineFactorPolynomial (θs.1.p l v) (θstar.p l v))
      (fun l _ m ↦ hpfac l m) m
  have hleft (m : ℕ) := continuousOn_polynomial_mul_coeff hqpow hdiff m
  have hall (m : ℕ) := continuousOn_polynomial_mul_coeff hleft hprod m
  change ContinuousOn (fun v ↦
    (affinePathNumeratorPolynomial s θs hji v).coeff k) (latentCube n)
  simpa [affinePathNumeratorPolynomial, θstar] using hall k

/-- A globally continuous extension of each cube coefficient, needed because the generic
parametric-integral API states measurability on the ambient sample space.  [the stated conclusion](goal) follows. -/
lemma latentCube_isClosed (n : ℕ) : IsClosed (latentCube n) := by
  rw [latentCube]
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).isClosed

/-- For a [finite dimension](hyp:n), [DAG](hyp:G), [sign pattern](hyp:s), [stratum point](hyp:θs),
[directed edge endpoints](hyp:j,i), [edge certificate](hyp:hji), and [coefficient index](hyp:k),
the [globally continuous extension of the affine numerator coefficient](goal) agrees on the cube. -/
noncomputable def affinePathNumeratorCoefficientExtension
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (k : Fin (n + 3 + 1)) : LatentState n → ℝ :=
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ affinePathNumeratorCoefficient s θs hji k v.1,
      (affinePathNumeratorCoefficient_continuousOn θs hji k).restrict⟩
  ⇑(Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f))

/-- Given [the selected directed edge](hyp:hji), the [extended affine numerator coefficient is
continuous on the ambient latent space](goal). -/
lemma affinePathNumeratorCoefficientExtension_continuous
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (k : Fin (n + 3 + 1)) :
    Continuous (affinePathNumeratorCoefficientExtension s θs hji k) := by
  unfold affinePathNumeratorCoefficientExtension
  exact (Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n)
    (show C({v : LatentState n // v ∈ latentCube n}, ℝ) from
      ⟨fun v ↦ affinePathNumeratorCoefficient s θs hji k v.1,
        (affinePathNumeratorCoefficient_continuousOn θs hji k).restrict⟩))).continuous

/-- Given [the selected directed edge](hyp:hji) and [a point in the latent cube](hyp:hv), the
[coefficient extension agrees with the original coefficient](goal). -/
lemma affinePathNumeratorCoefficientExtension_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (k : Fin (n + 3 + 1)) {v : LatentState n} (hv : v ∈ latentCube n) :
    affinePathNumeratorCoefficientExtension s θs hji k v =
      affinePathNumeratorCoefficient s θs hji k v := by
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ affinePathNumeratorCoefficient s θs hji k v.1,
      (affinePathNumeratorCoefficient_continuousOn θs hji k).restrict⟩
  have hs := Classical.choose_spec
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)
  change (Classical.choose
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)) v = _
  exact DFunLike.congr_fun hs ⟨v, hv⟩

/-- Given [the selected directed edge](hyp:hji) and [a point in the latent cube](hyp:hv), the
[extended polynomial numerator equals the original numerator polynomial evaluation](goal). -/
lemma affinePathNumerator_extension_polynomialNumerator_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (t : ℝ) {v : LatentState n} (hv : v ∈ latentCube n) :
    Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator
      (n + 3) (affinePathNumeratorCoefficientExtension s θs hji) t v =
      (affinePathNumeratorPolynomial s θs hji v).eval t := by
  rw [← affinePathNumerator_polynomialNumerator_eq θs hji t v]
  unfold Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator
  apply Finset.sum_congr rfl
  intro k _
  rw [affinePathNumeratorCoefficientExtension_eq θs hji k hv]

/-- Given [the selected directed edge](hyp:hji), the [extended affine numerator coefficient is
measurable](goal). -/
lemma affinePathNumeratorCoefficientExtension_measurable
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (k : Fin (n + 3 + 1)) :
    Measurable (affinePathNumeratorCoefficientExtension s θs hji k) :=
  (affinePathNumeratorCoefficientExtension_continuous θs hji k).measurable

/-- Given [the selected directed edge](hyp:hji), the [extended numerator coefficients have
uniform bounds on the compact latent cube](goal). -/
lemma affinePathNumeratorCoefficientExtension_compact_bounds
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ C : Fin (n + 3 + 1) → ℝ, ∀ k v, v ∈ latentCube n →
      |affinePathNumeratorCoefficientExtension s θs hji k v| ≤ C k := by
  have hK : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  choose C hC using fun k : Fin (n + 3 + 1) ↦
    hK.exists_bound_of_continuousOn
      (affinePathNumeratorCoefficientExtension_continuous θs hji k).continuousOn
  exact ⟨C, fun k v hv ↦ hC k v hv⟩

/-- A globally continuous representative of the initial distinguished denominator factor. -/
noncomputable def affinePathDenominatorStartExtension
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) (i : Fin n) : LatentState n → ℝ :=
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ theta.1.p i v.1, (theta.property.positiveSmooth.2.2.1 i).continuousOn.restrict⟩
  ⇑(Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f))

/-- A globally continuous representative of the terminal distinguished denominator factor. -/
noncomputable def affinePathDenominatorEndExtension
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {j i : Fin n} (hji : G.edge j i) : LatentState n → ℝ :=
  let thetaStar := embeddedSparseWitness s hji
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ thetaStar.p i v.1,
      ((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 i).continuousOn.restrict⟩
  ⇑(Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f))

/-- The [initial denominator extension is continuous on the ambient latent space](goal). -/
lemma affinePathDenominatorStartExtension_continuous
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) (i : Fin n) :
    Continuous (affinePathDenominatorStartExtension theta i) := by
  unfold affinePathDenominatorStartExtension
  exact (Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n)
    (show C({v : LatentState n // v ∈ latentCube n}, ℝ) from
      ⟨fun v ↦ theta.1.p i v.1,
        (theta.property.positiveSmooth.2.2.1 i).continuousOn.restrict⟩))).continuous

/-- Given [the selected directed edge](hyp:hji), the [terminal denominator extension is
continuous on the ambient latent space](goal). -/
lemma affinePathDenominatorEndExtension_continuous
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    {j i : Fin n} (hji : G.edge j i) :
    Continuous (affinePathDenominatorEndExtension s hji) := by
  unfold affinePathDenominatorEndExtension
  exact (Classical.choose (ContinuousMap.exists_restrict_eq (latentCube_isClosed n)
    (show C({v : LatentState n // v ∈ latentCube n}, ℝ) from
      ⟨fun v ↦ (embeddedSparseWitness s hji).p i v.1,
        ((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 i).continuousOn.restrict⟩))).continuous

/-- For [a point in the latent cube](hyp:hv), the [initial denominator extension agrees with
the stratum mechanism factor](goal). -/
lemma affinePathDenominatorStartExtension_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) (i : Fin n) {v : LatentState n}
    (hv : v ∈ latentCube n) :
    affinePathDenominatorStartExtension theta i v = theta.1.p i v := by
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ theta.1.p i v.1, (theta.property.positiveSmooth.2.2.1 i).continuousOn.restrict⟩
  have hs := Classical.choose_spec
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)
  change (Classical.choose
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)) v = _
  exact DFunLike.congr_fun hs ⟨v, hv⟩

/-- Given [the selected directed edge](hyp:hji) and [a point in the latent cube](hyp:hv), the
[terminal denominator extension agrees with the sparse-witness factor](goal). -/
lemma affinePathDenominatorEndExtension_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    {j i : Fin n} (hji : G.edge j i) {v : LatentState n}
    (hv : v ∈ latentCube n) :
    affinePathDenominatorEndExtension s hji v =
      (embeddedSparseWitness s hji).p i v := by
  let f : C({v : LatentState n // v ∈ latentCube n}, ℝ) :=
    ⟨fun v ↦ (embeddedSparseWitness s hji).p i v.1,
      ((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 i).continuousOn.restrict⟩
  have hs := Classical.choose_spec
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)
  change (Classical.choose
    (ContinuousMap.exists_restrict_eq (latentCube_isClosed n) f)) v = _
  exact DFunLike.congr_fun hs ⟨v, hv⟩

-- @node: affinePathExtension_zero
/-- The unrestricted affine extension starts at the supplied stratum point.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_zero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    affinePathExtension s θ hji 0 = θ.1 := by
  rcases θ with ⟨⟨p, q, hlocal⟩, hprop⟩
  simp [affinePathExtension]

-- @node: affinePathExtension_one
/-- The unrestricted affine extension ends at the edge-specific sparse witness.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_one
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    affinePathExtension s θ hji 1 = embeddedSparseWitness s hji := by
  rcases θ with ⟨⟨p, q, hlocal⟩, hprop⟩
  simp [affinePathExtension]

-- @node: affinePathExtension_normalized_smooth
/-- The unrestricted affine extension is normalized and `C³` for every real path
parameter; only positivity requires restricting the parameter to a neighborhood of the
closed unit interval.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_normalized_smooth
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (t : ℝ) :
    (∀ l, ContDiffOn ℝ 3 ((affinePathExtension s θ hji t).p l) (latentCube n)) ∧
    (∀ l, ContDiffOn ℝ 3 ((affinePathExtension s θ hji t).q l) (Set.Icc (0 : ℝ) 1)) ∧
    (∀ l v, v ∈ latentCube n →
      ∫ z in Set.Icc (0 : ℝ) 1,
        (affinePathExtension s θ hji t).p l (Function.update v l z) = 1) ∧
    (∀ l, ∫ z in Set.Icc (0 : ℝ) 1,
      (affinePathExtension s θ hji t).q l z = 1) := by
  let θstar := embeddedSparseWitness s hji
  have hθ := θ.property.positiveSmooth
  have hstar := embeddedSparseWitness_positive_normalized_smooth s hji
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    exact (hθ.2.2.1 l).const_smul (1 - t) |>.add
      ((hstar.2.2.1 l).const_smul t)
  · intro l
    exact (hθ.2.2.2.1 l).const_smul (1 - t) |>.add
      ((hstar.2.2.2.1 l).const_smul t)
  · intro l v hv
    have hupdate : Continuous (fun z : ℝ => Function.update v l z) := by fun_prop
    have hmaps : MapsTo (fun z : ℝ => Function.update v l z)
        (Set.Icc (0 : ℝ) 1) (latentCube n) := by
      intro z hz k _
      by_cases hkl : k = l
      · subst k
        simpa using hz
      · simpa only [Function.update, dif_neg hkl] using hv k (Set.mem_univ k)
    have hpInt : IntegrableOn (fun z : ℝ =>
        (1 - t) * θ.1.p l (Function.update v l z)) (Set.Icc (0 : ℝ) 1) := by
      exact ((hθ.2.2.1 l).continuousOn.comp hupdate.continuousOn hmaps |>.const_mul _)
        |>.integrableOn_Icc
    have hpstarInt : IntegrableOn (fun z : ℝ =>
        t * θstar.p l (Function.update v l z)) (Set.Icc (0 : ℝ) 1) := by
      exact ((hstar.2.2.1 l).continuousOn.comp hupdate.continuousOn hmaps |>.const_mul _)
        |>.integrableOn_Icc
    change ∫ z in Set.Icc (0 : ℝ) 1,
      ((1 - t) * θ.1.p l (Function.update v l z) +
        t * θstar.p l (Function.update v l z)) = 1
    rw [MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hθ.2.2.2.2.1 l v hv, hstar.2.2.2.2.1 l v hv]
    · ring
    · exact hpInt
    · exact hpstarInt
  · intro l
    change ∫ z in Set.Icc (0 : ℝ) 1,
      ((1 - t) * θ.1.q l z + t * θstar.q l z) = 1
    rw [MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hθ.2.2.2.2.2 l, hstar.2.2.2.2.2 l]
    · ring
    · exact ((hθ.2.2.2.1 l).continuousOn.const_mul _).integrableOn_Icc
    · exact ((hstar.2.2.2.1 l).continuousOn.const_mul _).integrableOn_Icc

-- @node: mechanism_p_uniform_lower
/-- Positivity and compactness give one strict lower bound valid for every observational
mechanism slot on the latent cube.  Given [the stated inputs and conditions](hyp:hθ), [the stated conclusion](goal) follows. -/
lemma mechanism_p_uniform_lower
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hθ : PositiveNormalizedSmoothMechanisms G θ) :
    ∃ ε > 0, ∀ i v, v ∈ latentCube n → ε ≤ θ.p i v := by
  let K : Set (Fin n × LatentState n) := Set.univ ×ˢ latentCube n
  have hK : IsCompact K := by
    exact isCompact_univ.prod (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ => isCompact_Icc)
  have hcont : ContinuousOn (fun z : Fin n × LatentState n => θ.p z.1 z.2) K := by
    rw [continuousOn_prod_of_discrete_left]
    intro i
    simpa only [K, Set.mem_prod, Set.mem_univ, true_and, Set.ofPred_mem_eq] using
      (hθ.2.2.1 i).continuousOn
  have hpos : ∀ z ∈ K, (0 : ℝ) < θ.p z.1 z.2 := by
    intro z hz
    exact hθ.1 z.1 z.2 hz.2
  rcases hK.exists_forall_le' hcont hpos with ⟨ε, hε, hbound⟩
  exact ⟨ε, hε, fun i v hv => hbound (i, v) ⟨Set.mem_univ i, hv⟩⟩

-- @node: mechanism_q_uniform_lower
/-- Positivity and compactness give one strict lower bound valid for every intervention
mechanism slot on the unit interval.  Given [the stated inputs and conditions](hyp:hθ), [the stated conclusion](goal) follows. -/
lemma mechanism_q_uniform_lower
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hθ : PositiveNormalizedSmoothMechanisms G θ) :
    ∃ ε > 0, ∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → ε ≤ θ.q i z := by
  let K : Set (Fin n × ℝ) := Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hcont : ContinuousOn (fun z : Fin n × ℝ => θ.q z.1 z.2) K := by
    rw [continuousOn_prod_of_discrete_left]
    intro i
    simpa only [K, Set.mem_prod, Set.mem_univ, true_and, Set.ofPred_mem_eq] using
      (hθ.2.2.2.1 i).continuousOn
  have hpos : ∀ z ∈ K, (0 : ℝ) < θ.q z.1 z.2 := by
    intro z hz
    exact hθ.2.1 z.1 z.2 hz.2
  rcases hK.exists_forall_le' hcont hpos with ⟨ε, hε, hbound⟩
  exact ⟨ε, hε, fun i z hz => hbound (i, z) ⟨Set.mem_univ i, hz⟩⟩

/-- The closed affine path admits an open parameter enlargement on which all factors remain
positive and the distinguished observational denominator has one uniform separation margin.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_open_positive_uniformDenominator
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ O : Set ℝ, ∃ ε > 0, IsOpen O ∧ Set.Icc (0 : ℝ) 1 ⊆ O ∧ Convex ℝ O ∧
      ∀ t ∈ O,
        PositiveNormalizedSmoothMechanisms G (affinePathExtension s θs hji t) ∧
        ∀ v ∈ latentCube n,
          ε ≤ |Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator
            (θs.1.p i) ((embeddedSparseWitness s hji).p i) t v| := by
  let θstar := embeddedSparseWitness s hji
  have hθ := θs.property.positiveSmooth
  have hstar := embeddedSparseWitness_positive_normalized_smooth s hji
  rcases mechanism_p_uniform_lower hθ with ⟨mpθ, hmpθ, hpθ⟩
  rcases mechanism_p_uniform_lower hstar with ⟨mpstar, hmpstar, hpstar⟩
  rcases mechanism_q_uniform_lower hθ with ⟨mqθ, hmqθ, hqθ⟩
  rcases mechanism_q_uniform_lower hstar with ⟨mqstar, hmqstar, hqstar⟩
  let m := min mpθ (min mpstar (min mqθ mqstar))
  have hm : 0 < m := by dsimp [m]; positivity
  let Cube := {v : LatentState n // v ∈ latentCube n}
  let Unit := {z : ℝ // z ∈ Set.Icc (0 : ℝ) 1}
  letI : CompactSpace Cube := isCompact_iff_compactSpace.mp (by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc)
  letI : CompactSpace Unit := isCompact_iff_compactSpace.mp isCompact_Icc
  let Op : Set ℝ := {t | ∀ l (v : Cube),
    m / 2 < (1 - t) * θs.1.p l v.1 + t * θstar.p l v.1}
  let Oq : Set ℝ := {t | ∀ l (z : Unit),
    m / 2 < (1 - t) * θs.1.q l z.1 + t * θstar.q l z.1}
  have hOp : IsOpen Op := isOpen_affine_forall_gt
    (fun l (v : Cube) ↦ θs.1.p l v.1) (fun l (v : Cube) ↦ θstar.p l v.1) (m / 2)
    (fun l ↦ (hθ.2.2.1 l).continuousOn.restrict)
    (fun l ↦ (hstar.2.2.1 l).continuousOn.restrict)
  have hOq : IsOpen Oq := isOpen_affine_forall_gt
    (fun l (z : Unit) ↦ θs.1.q l z.1) (fun l (z : Unit) ↦ θstar.q l z.1) (m / 2)
    (fun l ↦ (hθ.2.2.2.1 l).continuousOn.restrict)
    (fun l ↦ (hstar.2.2.2.1 l).continuousOn.restrict)
  have hOpConvex : Convex ℝ Op := convex_affine_forall_gt
    (fun l (v : Cube) ↦ θs.1.p l v.1) (fun l (v : Cube) ↦ θstar.p l v.1) (m / 2)
  have hOqConvex : Convex ℝ Oq := convex_affine_forall_gt
    (fun l (z : Unit) ↦ θs.1.q l z.1) (fun l (z : Unit) ↦ θstar.q l z.1) (m / 2)
  refine ⟨Op ∩ Oq, m / 2, half_pos hm, hOp.inter hOq, ?_,
    hOpConvex.inter hOqConvex, ?_⟩
  · intro t ht
    constructor
    · intro l v
      have ha : m ≤ θs.1.p l v.1 :=
        le_trans (min_le_left _ _) (hpθ l v.1 v.2)
      have hb : m ≤ θstar.p l v.1 :=
        le_trans (min_le_right _ _ |>.trans (min_le_left _ _)) (hpstar l v.1 v.2)
      calc
        m / 2 < m := half_lt_self hm
        _ = (1 - t) * m + t * m := by ring
        _ ≤ (1 - t) * θs.1.p l v.1 + t * θstar.p l v.1 :=
          add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left hb ht.1)
    · intro l z
      have ha : m ≤ θs.1.q l z.1 :=
        le_trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans
          (min_le_left _ _))) (hqθ l z.1 z.2)
      have hb : m ≤ θstar.q l z.1 :=
        le_trans (min_le_right _ _ |>.trans (min_le_right _ _ |>.trans
          (min_le_right _ _))) (hqstar l z.1 z.2)
      calc
        m / 2 < m := half_lt_self hm
        _ = (1 - t) * m + t * m := by ring
        _ ≤ (1 - t) * θs.1.q l z.1 + t * θstar.q l z.1 :=
          add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left hb ht.1)
  · intro t ht
    have hnorm := affinePathExtension_normalized_smooth θs hji t
    have hposp : ∀ l v, v ∈ latentCube n →
        0 < (affinePathExtension s θs hji t).p l v := by
      intro l v hv
      exact (half_pos hm).trans (ht.1 l ⟨v, hv⟩)
    have hposq : ∀ l z, z ∈ Set.Icc (0 : ℝ) 1 →
        0 < (affinePathExtension s θs hji t).q l z := by
      intro l z hz
      exact (half_pos hm).trans (ht.2 l ⟨z, hz⟩)
    refine ⟨⟨hposp, hposq, hnorm.1, hnorm.2.1, hnorm.2.2.1, hnorm.2.2.2⟩, ?_⟩
    intro v hv
    change m / 2 ≤ |(1 - t) * θs.1.p i v +
      t * (embeddedSparseWitness s hji).p i v|
    rw [abs_of_pos ((half_pos hm).trans (ht.1 i ⟨v, hv⟩))]
    exact (ht.1 i ⟨v, hv⟩).le

/-- The ambient continuous extensions used by the generic analytic theorem give exactly the
paper's rational integral, because the integration measure is restricted to the latent cube.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathContrastIntegral_eq_extendedIntegral
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (t : ℝ) :
    affinePathContrastIntegral s theta hji t =
      ∫ v in latentCube n,
        Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.polynomialNumerator
            (n + 3) (affinePathNumeratorCoefficientExtension s theta hji) t v /
          Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator
            (affinePathDenominatorStartExtension theta i)
            (affinePathDenominatorEndExtension s hji) t v := by
  have hK : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  unfold affinePathContrastIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hK] with v hv
  rw [affinePathNumerator_extension_polynomialNumerator_eq theta hji t hv,
    affinePathNumeratorPolynomial_eval theta hji t v]
  unfold Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator
  rw [
    affinePathDenominatorStartExtension_eq theta i hv,
    affinePathDenominatorEndExtension_eq hji hv]
  simp [affinePathExtension]

/-- The affine-path rational integral is analytic on the common positive enlargement.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathContrastIntegral_analyticOnNhd
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ O : Set ℝ, IsOpen O ∧ Set.Icc (0 : ℝ) 1 ⊆ O ∧ Convex ℝ O ∧
      (∀ t ∈ O, PositiveNormalizedSmoothMechanisms G
        (affinePathExtension s theta hji t)) ∧
      AnalyticOnNhd ℝ (affinePathContrastIntegral s theta hji) O := by
  rcases affinePathExtension_open_positive_uniformDenominator theta hji with
    ⟨O, epsilon, hepsilon, hO, hIcc, hconvex, hpositive⟩
  rcases affinePathNumeratorCoefficientExtension_compact_bounds theta hji with
    ⟨C, hC⟩
  have hK : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hmu : volume (latentCube n) ≠ ⊤ := by
    exact (show IsCompact (latentCube n) by
      rw [latentCube]
      exact isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top.ne
  have hden' : ∀ t ∈ O, ∀ v ∈ latentCube n,
      epsilon ≤
        |Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator
          (affinePathDenominatorStartExtension theta i)
          (affinePathDenominatorEndExtension s hji) t v| := by
    intro t ht v hv
    unfold Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.affineDenominator
    rw [affinePathDenominatorStartExtension_eq theta i hv,
      affinePathDenominatorEndExtension_eq hji hv]
    exact (hpositive t ht).2 v hv
  have han :=
    Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.analyticOnNhd_setIntegral_polynomial_div_affine_of_uniform_nonzero
        volume hK hmu (n + 3) (affinePathNumeratorCoefficientExtension s theta hji)
        (affinePathDenominatorStartExtension theta i)
        (affinePathDenominatorEndExtension s hji) O epsilon C hO hepsilon
        (affinePathNumeratorCoefficientExtension_measurable theta hji)
        (affinePathDenominatorStartExtension_continuous theta i).measurable
        (affinePathDenominatorEndExtension_continuous hji).measurable hC hden'
  refine ⟨O, hO, hIcc, hconvex, fun t ht ↦ (hpositive t ht).1, ?_⟩
  simpa only [← affinePathContrastIntegral_eq_extendedIntegral theta hji] using han

/-- The paper's scalar own-coordinate log-ratio derivative is the difference of the
intervention logarithmic derivative and the full-cube observational Fréchet derivative in the
own-coordinate direction.  Given [the stated inputs and conditions](hyp:hθ,hv), [the stated conclusion](goal) follows. -/
lemma ownLogRatioDerivative_eq_fderivWithin
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hθ : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    ownLogRatioDerivative θ i v =
      fderivWithin ℝ (θ.q i) (Set.Icc (0 : ℝ) 1) (v i) 1 / θ.q i (v i) -
        fderivWithin ℝ (θ.p i) (latentCube n) v (Pi.single i 1) / θ.p i v := by
  have hvi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  have hpsection : DifferentiableOn ℝ
      (fun z ↦ θ.p i (Function.update v i z)) (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    apply ((hθ.2.2.1 i).differentiableOn (by norm_num)
      (Function.update v i z) (by
        intro k _
        by_cases hki : k = i
        · subst k
          simpa using hz
        · simpa [Function.update, hki] using hv k (Set.mem_univ k))).comp z
      (hasDerivAt_update v i z).differentiableAt.differentiableWithinAt
    intro y hy k _
    by_cases hki : k = i
    · subst k
      simpa using hy
    · simpa [Function.update, hki] using hv k (Set.mem_univ k)
  unfold ownLogRatioDerivative
  change derivWithin (Causalean.Mathlib.Analysis.logRatio (θ.q i)
    (fun z ↦ θ.p i (Function.update v i z))) (Set.Icc (0 : ℝ) 1) (v i) = _
  rw [Causalean.Mathlib.Analysis.derivWithin_logRatio (by norm_num)
    ((hθ.2.2.2.1 i).differentiableOn (by norm_num)) hpsection
    (hθ.2.1 i) (fun z hz ↦ hθ.1 i (Function.update v i z) (by
      intro k
      by_cases hki : k = i
      · subst k
        simpa using hz
      · simpa [Function.update, hki] using hv k (Set.mem_univ k))) hvi]
  rw [derivWithin_coordinateSection_eq_fderivWithin_apply
    ((hθ.2.2.1 i).differentiableOn (by norm_num)) hv i hvi]
  simp [derivWithin]

-- @node: affinePathContrast_zero
/-- At the initial endpoint, the affine-path contrast is the original mechanism's contrast.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathContrast_zero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    affinePathContrast s θ hji 0 =
      secondMomentContrast
        (canonicalObservedWorld G θ.1 (Equiv.refl (Fin n))) j i := by
  unfold affinePathContrast
  rw [affinePathExtension_zero]

-- @node: affinePathContrast_one
/-- At the terminal endpoint, the affine-path contrast is the embedded sparse contrast.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathContrast_one
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    affinePathContrast s θ hji 1 =
      secondMomentContrast
        (canonicalObservedWorld G (embeddedSparseWitness s hji)
          (Equiv.refl (Fin n))) j i := by
  unfold affinePathContrast
  rw [affinePathExtension_one]

-- @node: canonical_secondMomentContrast_eq_integral
/-- For a positive normalized mechanism and distinct intervention and ratio targets, the
canonical second-moment contrast equals the rational mechanism integral obtained by cancelling
the observational child-density factor.  Given [the stated inputs and conditions](hyp:hpos,hji), [the stated conclusion](goal) follows. -/
lemma canonical_secondMomentContrast_eq_integral
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) {j i : Fin n}
    (hji : j ≠ i) :
    secondMomentContrast (canonicalObservedWorld G θ (Equiv.refl (Fin n))) j i =
      ∫ v in latentCube n,
        (θ.q i (v i)) ^ 2 * (θ.q j (v j) - θ.p j v) *
          (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) / θ.p i v := by
  let μ : Measure (LatentState n) := volume.restrict (latentCube n)
  let r : LatentState n → ℝ := fun v => θ.q i (v i) / θ.p i v
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcubeCompact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hpcont (l : Fin n) : ContinuousOn (θ.p l) (latentCube n) :=
    (hpos.2.2.1 l).continuousOn
  have hqcont (l : Fin n) : ContinuousOn (fun v : LatentState n => θ.q l (v l))
      (latentCube n) :=
    (hpos.2.2.2.1 l).continuousOn.comp ((continuous_apply l).continuousOn)
      (fun v hv => hv l (Set.mem_univ l))
  have hrcont : ContinuousOn r (latentCube n) := by
    exact (hqcont i).div (hpcont i) fun v hv => ne_of_gt (hpos.1 i v hv)
  have hobscont : ContinuousOn (observationalDensity θ) (latentCube n) := by
    unfold observationalDensity
    exact continuousOn_finsetProd _ fun l _ => hpcont l
  have hintcont : ContinuousOn (interventionalDensity θ j) (latentCube n) := by
    unfold interventionalDensity
    exact (hqcont j).mul (continuousOn_finsetProd _ fun l _ => hpcont l)
  have hobsint : Integrable (fun v => observationalDensity θ v * r v ^ 2) μ := by
    exact (hobscont.mul (hrcont.pow 2)).integrableOn_compact hcubeCompact
  have hintint : Integrable (fun v => interventionalDensity θ j v * r v ^ 2) μ := by
    exact (hintcont.mul (hrcont.pow 2)).integrableOn_compact hcubeCompact
  have hobs : (∫ v, r v ^ 2 ∂observationalLaw θ) =
      ∫ v, observationalDensity θ v * r v ^ 2 ∂μ := by
    unfold observationalLaw
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hcube] with v hv
      rw [ENNReal.toReal_ofReal (le_of_lt (by
        unfold observationalDensity
        exact Finset.prod_pos fun l _ => hpos.1 l v hv))]
      rfl
    · exact (hobscont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
    · filter_upwards with v
      exact ENNReal.ofReal_lt_top
  have hint : (∫ v, r v ^ 2 ∂interventionalLaw θ j) =
      ∫ v, interventionalDensity θ j v * r v ^ 2 ∂μ := by
    unfold interventionalLaw
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hcube] with v hv
      rw [ENNReal.toReal_ofReal (le_of_lt (by
        unfold interventionalDensity
        exact mul_pos (hpos.2.1 j (v j) (hv j (Set.mem_univ j)))
          (Finset.prod_pos fun l _ => hpos.1 l v hv)))]
      rfl
    · exact (hintcont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
    · filter_upwards with v
      exact ENNReal.ofReal_lt_top
  unfold secondMomentContrast
  change (∫ v, r v ^ 2 ∂interventionalLaw θ j) -
    (∫ v, r v ^ 2 ∂observationalLaw θ) = _
  rw [hint, hobs, ← integral_sub hintint hobsint]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hcube] with v hv
  have hpi : θ.p i v ≠ 0 := ne_of_gt (hpos.1 i v hv)
  have hinterDensity : interventionalDensity θ j v =
      θ.q j (v j) * θ.p i v *
        (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) := by
    unfold interventionalDensity
    have hprod : (∏ l ∈ Finset.univ.erase j, θ.p l v) =
        θ.p i v * (∏ l ∈ (Finset.univ.erase j).erase i, θ.p l v) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)]
      simp only [Finset.sdiff_singleton_eq_erase]
    rw [hprod, Finset.erase_right_comm]
    ring
  have hobsDensity : observationalDensity θ v =
      θ.p i v * θ.p j v *
        (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) := by
    unfold observationalDensity
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  unfold r
  rw [hinterDensity, hobsDensity]
  field_simp

-- @node: affinePathContrast_eq_integral_of_mem_Icc
/-- On the closed affine path, the contrast is exactly its rational mechanism integral.  Given [the stated inputs and conditions](hyp:hji,ht), [the stated conclusion](goal) follows. -/
lemma affinePathContrast_eq_integral_of_mem_Icc
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    affinePathContrast s θs hji t = affinePathContrastIntegral s θs hji t := by
  have hne : j ≠ i := by
    intro h
    subst j
    exact G.irrefl i hji
  unfold affinePathContrast affinePathContrastIntegral
  exact canonical_secondMomentContrast_eq_integral
    (affinePathExtension_positive_normalized_smooth θs hji ht) hne

-- @node: analyticOnNhd_isolated_zeros_of_nonzero
/-- A real analytic function on a preconnected set that is nonzero somewhere has an
isolated zero at every point of the set.  Given [the stated inputs and conditions](hyp:hf,hO,hz,hfz,ht,hft), [the stated conclusion](goal) follows. -/
lemma analyticOnNhd_isolated_zeros_of_nonzero {f : ℝ → ℝ} {O : Set ℝ}
    (hf : AnalyticOnNhd ℝ f O) (hO : IsPreconnected O)
    {z t : ℝ} (hz : z ∈ O) (hfz : f z ≠ 0) (ht : t ∈ O) (hft : f t = 0) :
    ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) (t + ε), u ≠ t → f u ≠ 0 := by
  rcases (hf t ht).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact (hfz (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hO ht hzero hz)).elim
  · change {u | f u ≠ 0} ∈ nhdsWithin t {t}ᶜ at hne
    rw [Metric.mem_nhdsWithin_iff] at hne
    rcases hne with ⟨ε, hε, hball⟩
    refine ⟨ε, hε, fun u hu hut => hball ?_⟩
    refine ⟨?_, ?_⟩
    · simp only [Metric.mem_ball, Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]

-- @node: threeNode_affinePathContrast_one_ne_zero
/-- On the explicit three-node edge, the affine path ends at the quantitatively
separated sparse witness.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma threeNode_affinePathContrast_one_ne_zero (s : SignVector 3)
    (θs : StratumPoint threeNodeDAG s)
    (hji : threeNodeDAG.edge (0 : Fin 3) 1) :
    affinePathContrast s θs hji 1 ≠ 0 := by
  rw [affinePathContrast_one]
  have heq : embeddedSparseWitness s hji = sparseWitness s := by
    rfl
  rw [heq]
  have hgap := (sparse_witness_certificate s).2.2.2.2.2.2.2.2.2.2.1
  have hc : secondMomentContrast
      (canonicalObservedWorld threeNodeDAG (sparseWitness s) (Equiv.refl (Fin 3))) 0 1 <
      -(3 / 10000 : ℝ) := by
    unfold secondMomentContrast
    linarith
  exact ne_of_lt (lt_of_lt_of_le hc (by norm_num))

-- @node: affinePathContrast_one_ne_zero
/-- Every edge-specific affine path ends at a sparse mechanism with nonzero contrast.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathContrast_one_ne_zero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    affinePathContrast s θs hji 1 ≠ 0 := by
  have hne : j ≠ i := by
    intro h
    subst j
    exact G.irrefl i hji
  rw [affinePathContrast_one]
  rw [canonical_secondMomentContrast_eq_integral
    (embeddedSparseWitness_positive_normalized_smooth s hji) hne]
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let f : LatentState n → ℝ := fun v =>
    ((embeddedSparseWitness s hji).q i (v i)) ^ 2 *
      ((embeddedSparseWitness s hji).q j (v j) -
        (embeddedSparseWitness s hji).p j v) *
      (∏ l ∈ (Finset.univ.erase i).erase j,
        (embeddedSparseWitness s hji).p l v) /
      (embeddedSparseWitness s hji).p i v
  have hpos := embeddedSparseWitness_positive_normalized_smooth s hji
  have hfcont : ContinuousOn f (latentCube n) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · exact ((hpos.2.2.2.1 i).continuousOn.comp
            ((continuous_apply i).continuousOn)
            (fun (v : LatentState n) (hv : v ∈ latentCube n) =>
              hv i (Set.mem_univ i))).pow 2
        · exact ((hpos.2.2.2.1 j).continuousOn.comp
            ((continuous_apply j).continuousOn)
            (fun (v : LatentState n) (hv : v ∈ latentCube n) =>
              hv j (Set.mem_univ j))).sub (hpos.2.2.1 j).continuousOn
      · exact continuousOn_finsetProd _ fun l _ => (hpos.2.2.1 l).continuousOn
    · exact (hpos.2.2.1 i).continuousOn
    · intro v hv
      exact ne_of_gt (hpos.1 i v hv)
  have hf : Integrable f (volume.restrict (latentCube n)) :=
    hfcont.integrableOn_compact (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ => isCompact_Icc)
  have hμ : volume.restrict (latentCube n) = Measure.pi (fun _ : Fin n => μ) := by
    change volume.restrict (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) = _
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  change (∫ v in latentCube n, f v) ≠ 0
  rw [hμ]
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let S : Finset (Fin n) := {j, i}
  let jj : {l : Fin n // l ∈ S} := ⟨j, by simp [S]⟩
  let ii : {l : Fin n // l ∈ S} := ⟨i, by simp [S]⟩
  let g : ({l : Fin n // l ∈ S} → ℝ) → ℝ := fun z =>
    exponentialInterventionDensity (reflectedCoordinate s i (z ii)) ^ 2 *
      (exponentialInterventionDensity (reflectedCoordinate s j (z jj)) - 1) /
      (1 + (1 / 10 : ℝ) *
        centeredCoordinate (reflectedCoordinate s j (z jj)) *
        centeredCoordinate (reflectedCoordinate s i (z ii)))
  have hfg : f = fun v => g (fun l : {l : Fin n // l ∈ S} => v l.1) := by
    funext v
    simp only [f, g, ii, jj, embeddedSparseWitness, embeddedSparseP]
    simp [hne]
  rw [hfg, Causalean.Stat.integral_comp_pi_restrict_finset μ S g]
  let e : Fin 2 ≃ {l : Fin n // l ∈ S} := pairFinEquiv hne
  have he := measurePreserving_piCongrLeft (fun _ : {l : Fin n // l ∈ S} => μ) e
  rw [← he.integral_comp']
  have hgint : Integrable (g ∘ MeasurableEquiv.piCongrLeft
      (fun _ : {l : Fin n // l ∈ S} => ℝ) e)
      (Measure.pi fun _ : Fin 2 => μ) := by
    apply (he.integrable_comp_emb
      (MeasurableEquiv.piCongrLeft
        (fun _ : {l : Fin n // l ∈ S} => ℝ) e).measurableEmbedding).2
    have hp := Causalean.Stat.measurePreserving_pi_restrict_finset μ S
    have hgmeas : Measurable g := by
      rcases s.signed i with hi | hi <;> rcases s.signed j with hj | hj <;>
        simp [g, exponentialInterventionDensity, reflectedCoordinate, reflect,
          centeredCoordinate, hi, hj, show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
    apply (hp.integrable_comp hgmeas.aestronglyMeasurable).1
    rw [show g ∘ (fun (v : Fin n → ℝ) (l : {l : Fin n // l ∈ S}) => v l.1) = f by
      simpa only [Function.comp_def] using hfg.symm]
    simpa only [← hμ] using hf
  change (∫ v : Fin 2 → ℝ, (g ∘ MeasurableEquiv.piCongrLeft
    (fun _ : {l : Fin n // l ∈ S} => ℝ) e) v
    ∂Measure.pi fun _ : Fin 2 => μ) ≠ 0
  rw [integral_fin_two_pi_eq_iterated μ _ hgint]
  have hj_eval (z : Fin 2 → ℝ) :
      (MeasurableEquiv.piCongrLeft
        (fun _ : {l : Fin n // l ∈ S} => ℝ) e z) jj = z 0 := by
    have hjj : jj = e 0 := by
      apply Subtype.ext
      simp [e, pairFinEquiv, jj, S]
    rw [hjj, MeasurableEquiv.piCongrLeft_apply_apply]
  have hi_eval (z : Fin 2 → ℝ) :
      (MeasurableEquiv.piCongrLeft
        (fun _ : {l : Fin n // l ∈ S} => ℝ) e z) ii = z 1 := by
    have hii : ii = e 1 := by
      apply Subtype.ext
      simp [e, pairFinEquiv, ii, S]
    rw [hii, MeasurableEquiv.piCongrLeft_apply_apply]
  simp_rw [Function.comp_apply, g, hj_eval, hi_eval,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.cons_val_zero]
  have hrefY (x : ℝ) :
      (∫ y in Set.Icc (0 : ℝ) 1,
        exponentialInterventionDensity (reflectedCoordinate s i y) ^ 2 *
          (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) /
          (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s j x) *
            centeredCoordinate (reflectedCoordinate s i y))) =
      (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) *
        sparseA (reflectedCoordinate s j x) := by
    change (∫ y in Set.Icc (0 : ℝ) 1,
      (fun y => exponentialInterventionDensity y ^ 2 *
        (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) /
        (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s j x) *
          centeredCoordinate y)) (reflectedCoordinate s i y)) = _
    have href := integral_reflectedCoordinate s i
      (fun y => exponentialInterventionDensity y ^ 2 *
        (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) /
        (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s j x) *
          centeredCoordinate y))
    rw [href]
    unfold sparseA
    rw [show (fun y : ℝ =>
        exponentialInterventionDensity y ^ 2 *
          (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) /
          (1 + (10 : ℝ)⁻¹ * centeredCoordinate (reflectedCoordinate s j x) *
            centeredCoordinate y)) =
        fun y => (exponentialInterventionDensity (reflectedCoordinate s j x) - 1) *
          (exponentialInterventionDensity y ^ 2 /
            (1 + centeredCoordinate (reflectedCoordinate s j x) / 10 *
              centeredCoordinate y)) by funext y; ring,
      MeasureTheory.integral_const_mul]
  dsimp only [μ]
  simp only [one_div]
  simp_rw [hrefY]
  change (∫ x in Set.Icc (0 : ℝ) 1,
    (fun x => (exponentialInterventionDensity x - 1) * sparseA x)
      (reflectedCoordinate s j x)) ≠ 0
  rw [show (∫ x in Set.Icc (0 : ℝ) 1,
      (fun x => (exponentialInterventionDensity x - 1) * sparseA x)
        (reflectedCoordinate s j x)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity x - 1) * sparseA x by
    simpa only using integral_reflectedCoordinate s j
      (fun x => (exponentialInterventionDensity x - 1) * sparseA x)]
  have hgap := sparse_unreflected_moment_gap
  intro hzero
  have hneg : (∫ x in Set.Icc (0 : ℝ) 1,
      (1 - exponentialInterventionDensity x) * sparseA x) = 0 := by
    rw [show (fun x : ℝ => (1 - exponentialInterventionDensity x) * sparseA x) =
      fun x => -((exponentialInterventionDensity x - 1) * sparseA x) by
        funext x
        ring,
      MeasureTheory.integral_neg, hzero, neg_zero]
  linarith

/-- Causal minimality persists for sufficiently small positive parameters along the affine path.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_eventually_causalMinimal
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ δ > 0, ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, t.1 < δ →
      CausalMinimality G (affinePathExtension s θs hji t.1) := by
  rcases mechanismCompact_all_edge_witnesses_open θs with ⟨ε, hε, hopen⟩
  rcases affinePathExtension_p_eventually_uniform_close θs hji hε with
    ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro t htδ a b hab
  let η := affinePathExtension s θs hji t.1
  have hη : PositiveNormalizedSmoothMechanisms G η :=
    affinePathExtension_positive_normalized_smooth θs hji t.2
  have htAbs : |t.1| < δ := by simpa only [abs_of_nonneg t.2.1] using htδ
  have hfactor :
      (mechanismCompactPositiveFactorization θs.property.positiveSmooth).FactorSupClose
        (mechanismCompactPositiveFactorization hη) ε :=
    mechanismCompact_factorSupClose_of_p_close θs.property.positiveSmooth hη
      (hclose t.1 htAbs)
  have hnotCompact := hopen (mechanismCompactPositiveFactorization hη) hfactor b a hab
  intro hpaper
  apply hnotCompact
  exact (condIndepCoordinates_iff_compactPositiveFactorization_mechanism η
    (mechanismCompactPositiveFactorization hη)
    (mechanismCompactPositiveFactorization_observationalMeasure hη)
    b a ((G.parents b).erase a)).mp hpaper

/-- The prescribed own-coordinate derivative signs persist uniformly for small affine-path
parameters.  Compactness is used only in the latent-state variable; finiteness then combines the
nodewise neighborhoods.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_eventually_fixedOwnDerivativeSign
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ δ > 0, ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, t.1 < δ →
      FixedOwnDerivativeSign G s (affinePathExtension s θs hji t.1) := by
  let θstar := embeddedSparseWitness s hji
  let Cube := {v : LatentState n // v ∈ latentCube n}
  letI : CompactSpace Cube := isCompact_iff_compactSpace.mp (by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc)
  let score (l : Fin n) (t : ℝ) (v : Cube) : ℝ := s.value l *
    (((1 - t) * fderivWithin ℝ (θs.1.q l) (Set.Icc (0 : ℝ) 1) (v.1 l) 1 +
          t * fderivWithin ℝ (θstar.q l) (Set.Icc (0 : ℝ) 1) (v.1 l) 1) /
        ((1 - t) * θs.1.q l (v.1 l) + t * θstar.q l (v.1 l)) -
      ((1 - t) * fderivWithin ℝ (θs.1.p l) (latentCube n) v.1 (Pi.single l 1) +
          t * fderivWithin ℝ (θstar.p l) (latentCube n) v.1 (Pi.single l 1)) /
        ((1 - t) * θs.1.p l v.1 + t * θstar.p l v.1))
  have hnode : ∀ l : Fin n, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v : Cube, 0 < score l t v := by
    intro l
    have huCube : UniqueDiffOn ℝ (latentCube n) := by
      rw [latentCube]
      exact UniqueDiffOn.univ_pi fun _ ↦ uniqueDiffOn_Icc (by norm_num)
    have huIcc : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
      uniqueDiffOn_Icc (by norm_num)
    have hcoord : Continuous (fun v : Cube ↦ v.1 l) :=
      (continuous_apply l).comp continuous_subtype_val
    have hcoordMaps : Set.MapsTo (fun v : Cube ↦ v.1 l) Set.univ
        (Set.Icc (0 : ℝ) 1) := fun v _ ↦ v.2 l (Set.mem_univ l)
    have hqθd : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θs.1.q l) (Set.Icc (0 : ℝ) 1) (v.1 l)) :=
      ((θs.property.positiveSmooth.2.2.2.1 l).continuousOn_fderivWithin huIcc
        (by norm_num)).comp_continuous hcoord (fun v ↦ hcoordMaps (Set.mem_univ v))
    have hstarSmooth := embeddedSparseWitness_positive_normalized_smooth s hji
    have hqstard : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θstar.q l) (Set.Icc (0 : ℝ) 1) (v.1 l)) :=
      (hstarSmooth.2.2.2.1 l).continuousOn_fderivWithin huIcc (by norm_num)
        |>.comp_continuous hcoord (fun v ↦ hcoordMaps (Set.mem_univ v))
    have hpθd : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θs.1.p l) (latentCube n) v.1) :=
      ((θs.property.positiveSmooth.2.2.1 l).continuousOn_fderivWithin huCube
        (by norm_num)).comp_continuous continuous_subtype_val (fun v ↦ v.2)
    have hpstard : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θstar.p l) (latentCube n) v.1) :=
      (hstarSmooth.2.2.1 l).continuousOn_fderivWithin huCube (by norm_num)
        |>.comp_continuous continuous_subtype_val (fun v ↦ v.2)
    have hqθ : Continuous (fun v : Cube ↦ θs.1.q l (v.1 l)) :=
      ((θs.property.positiveSmooth.2.2.2.1 l).continuousOn.comp_continuous
        hcoord (fun v ↦ hcoordMaps (Set.mem_univ v)))
    have hqstar : Continuous (fun v : Cube ↦ θstar.q l (v.1 l)) :=
      (hstarSmooth.2.2.2.1 l).continuousOn.comp_continuous hcoord
        (fun v ↦ hcoordMaps (Set.mem_univ v))
    have hpθ : Continuous (fun v : Cube ↦ θs.1.p l v.1) :=
      ((θs.property.positiveSmooth.2.2.1 l).continuousOn.comp_continuous
        continuous_subtype_val (fun v ↦ v.2))
    have hpstar : Continuous (fun v : Cube ↦ θstar.p l v.1) :=
      (hstarSmooth.2.2.1 l).continuousOn.comp_continuous continuous_subtype_val
        (fun v ↦ v.2)
    have hqθd1 : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θs.1.q l) (Set.Icc (0 : ℝ) 1) (v.1 l) 1) := by
      fun_prop
    have hqstard1 : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θstar.q l) (Set.Icc (0 : ℝ) 1) (v.1 l) 1) := by
      fun_prop
    have hpθd1 : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θs.1.p l) (latentCube n) v.1 (Pi.single l 1)) := by
      fun_prop
    have hpstard1 : Continuous (fun v : Cube ↦
        fderivWithin ℝ (θstar.p l) (latentCube n) v.1 (Pi.single l 1)) := by
      fun_prop
    have hnumq : Continuous (fun z : ℝ × Cube ↦
        (1 - z.1) * fderivWithin ℝ (θs.1.q l) (Set.Icc (0 : ℝ) 1) (z.2.1 l) 1 +
          z.1 * fderivWithin ℝ (θstar.q l) (Set.Icc (0 : ℝ) 1) (z.2.1 l) 1) := by
      exact ((continuous_const.sub continuous_fst).mul (hqθd1.comp continuous_snd)).add
        (continuous_fst.mul (hqstard1.comp continuous_snd))
    have hdenq : Continuous (fun z : ℝ × Cube ↦
        (1 - z.1) * θs.1.q l (z.2.1 l) + z.1 * θstar.q l (z.2.1 l)) := by
      exact ((continuous_const.sub continuous_fst).mul (hqθ.comp continuous_snd)).add
        (continuous_fst.mul (hqstar.comp continuous_snd))
    have hnump : Continuous (fun z : ℝ × Cube ↦
        (1 - z.1) * fderivWithin ℝ (θs.1.p l) (latentCube n) z.2.1
            (Pi.single l 1) +
          z.1 * fderivWithin ℝ (θstar.p l) (latentCube n) z.2.1
            (Pi.single l 1)) := by
      exact ((continuous_const.sub continuous_fst).mul (hpθd1.comp continuous_snd)).add
        (continuous_fst.mul (hpstard1.comp continuous_snd))
    have hdenp : Continuous (fun z : ℝ × Cube ↦
        (1 - z.1) * θs.1.p l z.2.1 + z.1 * θstar.p l z.2.1) := by
      exact ((continuous_const.sub continuous_fst).mul (hpθ.comp continuous_snd)).add
        (continuous_fst.mul (hpstar.comp continuous_snd))
    have hcont : ∀ v : Cube, ContinuousAt
        (fun z : ℝ × Cube ↦ score l z.1 z.2) (0, v) := by
      intro v
      dsimp [score, θstar]
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.sub
      · apply ContinuousAt.div
        · exact hnumq.continuousAt
        · exact hdenq.continuousAt
        · simpa using (θs.property.positiveSmooth.2.1 l (v.1 l)
            (v.2 l (Set.mem_univ l))).ne'
      · apply ContinuousAt.div
        · exact hnump.continuousAt
        · exact hdenp.continuousAt
        · simpa using (θs.property.positiveSmooth.1 l v.1 v.2).ne'
    simpa only [Set.mem_univ, forall_const] using
      (isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
        (P := fun t v ↦ 0 < score l t v) (by
          intro v _
          have hformula := ownLogRatioDerivative_eq_fderivWithin
            θs.property.positiveSmooth l v.1 v.2
          have hpos := θs.property.fixedSign l v.1 v.2
          apply (hcont v).tendsto
          exact Ioi_mem_nhds (by simpa [score, θstar, hformula] using hpos)))
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l : Fin n, ∀ v : Cube, 0 < score l t v := by
    simpa only [Set.mem_univ, forall_const] using
      ((Filter.eventually_all_finite (Set.toFinite (Set.univ : Set (Fin n)))).2
        (fun l _ ↦ hnode l))
  rcases Metric.eventually_nhds_iff.mp hall with ⟨δ, hδ, hδall⟩
  refine ⟨δ, hδ, ?_⟩
  intro t htδ l v hv
  have hscore : 0 < score l t.1 ⟨v, hv⟩ :=
    hδall (by simpa [Real.dist_eq, abs_of_nonneg t.2.1] using htδ) l ⟨v, hv⟩
  have hη := affinePathExtension_positive_normalized_smooth θs hji t.2
  rw [ownLogRatioDerivative_eq_fderivWithin hη l v hv]
  have huCube : UniqueDiffOn ℝ (latentCube n) := by
    rw [latentCube]
    exact UniqueDiffOn.univ_pi fun _ ↦ uniqueDiffOn_Icc (by norm_num)
  have huIcc : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc (by norm_num)
  let hθq := θs.property.positiveSmooth.2.2.2.1 l
  let hstarq := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.2.1 l
  let hθp := θs.property.positiveSmooth.2.2.1 l
  let hstarp := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 l
  have hqfd : fderivWithin ℝ ((affinePathExtension s θs hji t.1).q l)
      (Set.Icc (0 : ℝ) 1) (v l) =
      (1 - t.1) • fderivWithin ℝ (θs.1.q l) (Set.Icc (0 : ℝ) 1) (v l) +
        t.1 • fderivWithin ℝ ((embeddedSparseWitness s hji).q l)
          (Set.Icc (0 : ℝ) 1) (v l) := by
    change fderivWithin ℝ
      (fun z ↦ (1 - t.1) • θs.1.q l z +
        t.1 • (embeddedSparseWitness s hji).q l z)
      (Set.Icc (0 : ℝ) 1) (v l) = _
    rw [fderivWithin_fun_add (huIcc.uniqueDiffWithinAt (hv l (Set.mem_univ l)))
        (((hθq.const_smul (1 - t.1)) (v l) (hv l (Set.mem_univ l))).differentiableWithinAt
          (by norm_num))
        (((hstarq.const_smul t.1) (v l) (hv l (Set.mem_univ l))).differentiableWithinAt
          (by norm_num)),
      fderivWithin_fun_const_smul (huIcc.uniqueDiffWithinAt (hv l (Set.mem_univ l)))
        ((hθq (v l)
          (hv l (Set.mem_univ l))).differentiableWithinAt (by norm_num)) (1 - t.1),
      fderivWithin_fun_const_smul (huIcc.uniqueDiffWithinAt (hv l (Set.mem_univ l)))
        ((hstarq (v l) (hv l (Set.mem_univ l))).differentiableWithinAt
          (by norm_num)) t.1]
  have hpfd : fderivWithin ℝ ((affinePathExtension s θs hji t.1).p l)
      (latentCube n) v =
      (1 - t.1) • fderivWithin ℝ (θs.1.p l) (latentCube n) v +
        t.1 • fderivWithin ℝ ((embeddedSparseWitness s hji).p l) (latentCube n) v := by
    change fderivWithin ℝ
      (fun w ↦ (1 - t.1) • θs.1.p l w +
        t.1 • (embeddedSparseWitness s hji).p l w) (latentCube n) v = _
    rw [fderivWithin_fun_add (huCube.uniqueDiffWithinAt hv)
        (((hθp.const_smul (1 - t.1)) v hv).differentiableWithinAt (by norm_num))
        (((hstarp.const_smul t.1) v hv).differentiableWithinAt (by norm_num)),
      fderivWithin_fun_const_smul (huCube.uniqueDiffWithinAt hv)
        ((hθp v hv).differentiableWithinAt
          (by norm_num)) (1 - t.1),
      fderivWithin_fun_const_smul (huCube.uniqueDiffWithinAt hv)
        ((hstarp v hv).differentiableWithinAt (by norm_num)) t.1]
  rw [hqfd, hpfd]
  simpa [score, θstar, affinePathExtension, smul_eq_mul] using hscore

/-- All three paper-local stratum conditions hold simultaneously along a sufficiently short
positive initial segment of the affine path.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_eventually_modelStratum
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    ∃ δ > 0, ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, t.1 < δ →
      ModelStratum G s (affinePathExtension s θs hji t.1) := by
  rcases affinePathExtension_eventually_causalMinimal θs hji with
    ⟨δmin, hδmin, hmin⟩
  rcases affinePathExtension_eventually_fixedOwnDerivativeSign θs hji with
    ⟨δsign, hδsign, hsign⟩
  refine ⟨min δmin δsign, lt_min hδmin hδsign, ?_⟩
  intro t ht
  exact ⟨affinePathExtension_positive_normalized_smooth θs hji t.2,
    hmin t (ht.trans_le (min_le_left _ _)),
    hsign t (ht.trans_le (min_le_right _ _))⟩

/-- Once the analytic package is available, isolated zeros, affine-path continuity, and local
stratum preservation produce the arbitrarily small nonzero perturbation used by the headline.  Given [the stated inputs and conditions](hyp:hji,hO,hanalytic,hisolated,hN), [the stated conclusion](goal) follows. -/
lemma affinePath_exists_small_stratum_nonzero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    {O : Set ℝ} (hO : Set.Icc (0 : ℝ) 1 ⊆ O)
    (hanalytic : AnalyticOnNhd ℝ (affinePathContrast s θs hji) O)
    (hisolated : ∀ t ∈ O, affinePathContrast s θs hji t = 0 →
      ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) (t + ε), u ≠ t →
        affinePathContrast s θs hji u ≠ 0)
    (N : Set (Mechanism n G)) (hN : N ∈ 𝓝 θs.1) :
    ∃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1},
      affinePath s θs hji ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ ∈ N ∧
      ModelStratum G s (affinePath s θs hji
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) ∧
      affinePathContrast s θs hji t.1 ≠ 0 := by
  rcases affinePathExtension_eventually_modelStratum θs hji with ⟨δs, hδs, hs⟩
  have heventN : ∀ᶠ t in 𝓝 (0 : ℝ), affinePathExtension s θs hji t ∈ N :=
    (tendsto_affinePathExtension_zero θs hji) hN
  rcases Metric.eventually_nhds_iff.mp heventN with ⟨δN, hδN, hnearN⟩
  have hzeroNhd : ∃ δ > 0, ∀ u, |u| < δ → u ≠ 0 →
      affinePathContrast s θs hji u ≠ 0 := by
    by_cases hz : affinePathContrast s θs hji 0 = 0
    · rcases hisolated 0 (hO ⟨by norm_num, by norm_num⟩) hz with ⟨δ, hδ, hiso⟩
      exact ⟨δ, hδ, fun u hu hu0 ↦ hiso u (by simpa [abs_lt] using hu) hu0⟩
    · have hc := (hanalytic 0 (hO ⟨by norm_num, by norm_num⟩)).continuousAt
      have hev : ∀ᶠ u in 𝓝 (0 : ℝ), affinePathContrast s θs hji u ≠ 0 :=
        hc (isOpen_compl_singleton.mem_nhds (by simpa using hz))
      rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hδev⟩
      exact ⟨δ, hδ, fun u hu _ ↦ hδev (by simpa [Real.dist_eq] using hu)⟩
  rcases hzeroNhd with ⟨δz, hδz, hz⟩
  let r := min 1 (min δs (min δN δz))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let u : ℝ := r / 2
  have hu0 : 0 < u := div_pos hr (by norm_num)
  have hu1 : u < 1 := by
    dsimp [u, r]
    have := min_le_left (1 : ℝ) (min δs (min δN δz))
    linarith
  let t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} := ⟨u, hu0, hu1⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · exact hnearN (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu0]
      dsimp [u, r]
      have := min_le_right (1 : ℝ) (min δs (min δN δz))
      have := min_le_right δs (min δN δz)
      have := min_le_left δN δz
      linarith)
  · apply hs ⟨u, ⟨hu0.le, hu1.le⟩⟩
    dsimp [u, r]
    have := min_le_right (1 : ℝ) (min δs (min δN δz))
    have := min_le_left δs (min δN δz)
    linarith
  · apply hz u
    · rw [abs_of_pos hu0]
      dsimp [u, r]
      have := min_le_right (1 : ℝ) (min δs (min δN δz))
      have := min_le_right δs (min δN δz)
      have := min_le_right δN δz
      linarith
    · exact ne_of_gt hu0

-- @node: lem:analytic-edge-perturbation
/-- Every edge admits arbitrarily small stratum-preserving affine perturbations with nonzero
second-moment contrast; the contrast has the stated analytic integral and isolated zeros.  Given [the stated inputs and conditions](hyp:hji,hIntervention), [the stated conclusion](goal) follows. -/
lemma analytic_edge_perturbation
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (hIntervention : OnePerfectInterventionPerNode G θs.1
      (canonicalObservedWorld G θs.1 (Equiv.refl (Fin n)))) :
    (∃ O : Set ℝ, IsOpen O ∧ Set.Icc (0 : ℝ) 1 ⊆ O ∧
      (∀ t ∈ O, affinePathContrast s θs hji t =
        affinePathContrastIntegral s θs hji t) ∧
      AnalyticOnNhd ℝ (affinePathContrast s θs hji) O ∧
      ∀ t ∈ O, affinePathContrast s θs hji t = 0 →
        ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) (t + ε), u ≠ t →
          affinePathContrast s θs hji u ≠ 0) ∧
    affinePathContrast s θs hji 1 ≠ 0 ∧
    (∀ N ∈ 𝓝 θs.1, ∃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1},
      affinePath s θs hji ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ ∈ N ∧
      ModelStratum G s (affinePath s θs hji
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) ∧
      affinePathContrast s θs hji t.1 ≠ 0) := by
  rcases affinePathContrastIntegral_analyticOnNhd θs hji with
    ⟨O, hO, hIcc, hconvex, hpositive, hintegralAnalytic⟩
  have hneji : j ≠ i := by
    intro h
    subst j
    exact G.irrefl i hji
  have heq : ∀ t ∈ O, affinePathContrast s θs hji t =
      affinePathContrastIntegral s θs hji t := by
    intro t ht
    unfold affinePathContrast affinePathContrastIntegral
    exact canonical_secondMomentContrast_eq_integral (hpositive t ht) hneji
  have hanalytic : AnalyticOnNhd ℝ (affinePathContrast s θs hji) O :=
    hintegralAnalytic.congr hO (fun t ht ↦ (heq t ht).symm)
  have hone : affinePathContrast s θs hji 1 ≠ 0 :=
    affinePathContrast_one_ne_zero θs hji
  have hisolated : ∀ t ∈ O, affinePathContrast s θs hji t = 0 →
      ∃ epsilon > 0, ∀ u ∈ Set.Ioo (t - epsilon) (t + epsilon), u ≠ t →
        affinePathContrast s θs hji u ≠ 0 := by
    intro t ht hzero
    exact analyticOnNhd_isolated_zeros_of_nonzero hanalytic hconvex.isPreconnected
      (hIcc ⟨by norm_num, by norm_num⟩) hone ht hzero
  refine ⟨⟨O, hO, hIcc, heq, hanalytic, hisolated⟩, hone, ?_⟩
  intro N hN
  exact affinePath_exists_small_stratum_nonzero θs hji hIcc hanalytic hisolated N hN

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
