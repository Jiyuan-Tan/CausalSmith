module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance

/-!
Finite-coordinate independent-chain energy moments, the moment calculation in (29).
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {J : ℕ} {F G : E → Fin J → ℝ}

/-- Independence of the chains also separates any pair of their coordinates. -/
-- @node: independent_energy_coordinates
lemma independent_energy_coordinates (hind : IndepFun F G ν) (i j : Fin J) :
    IndepFun (fun ω => F ω i) (fun ω => G ω j) ν := by
  exact hind.comp (measurable_pi_apply i) (measurable_pi_apply j)

/-- Independent square-integrable coordinates have integrable cross products. -/
-- @node: independent_energy_coordinate_product_integrable
lemma independent_energy_coordinate_product_integrable (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) (i : Fin J) :
    Integrable (fun ω => F ω i * G ω i) ν := by
  exact (independent_energy_coordinates hind i i).integrable_mul
    ((hF i).integrable (by norm_num)) ((hG i).integrable (by norm_num))

/-- The finite-coordinate energy mean is the dot product of the two coordinate means. -/
-- @node: independent_energy_sum_mean
lemma independent_energy_sum_mean (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) :
    (∫ ω, ∑ i, F ω i * G ω i ∂ν) =
      ∑ i, (∫ ω, F ω i ∂ν) * (∫ ω, G ω i ∂ν) := by
  rw [integral_finsetSum _ (fun i _ =>
    independent_energy_coordinate_product_integrable hind hF hG i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (independent_energy_coordinates hind i i).integral_fun_mul_eq_mul_integral
    (hF i).aestronglyMeasurable (hG i).aestronglyMeasurable

/-- Products of two coordinates in each chain separate across the independent chains. -/
-- @node: independent_energy_fourth_product_integrable
lemma independent_energy_fourth_product_integrable (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) (i j : Fin J) :
    Integrable (fun ω => (F ω i * F ω j) * (G ω i * G ω j)) ν := by
  have hi : IndepFun (fun ω => F ω i * F ω j) (fun ω => G ω i * G ω j) ν :=
    hind.comp (by fun_prop : Measurable (fun v : Fin J → ℝ => v i * v j))
      (by fun_prop : Measurable (fun v : Fin J → ℝ => v i * v j))
  exact hi.integrable_mul ((hF i).integrable_mul (hF j))
    ((hG i).integrable_mul (hG j))

/-- Expanding the energy square gives a double sum of products of second moments. -/
-- @node: independent_energy_sum_second_moment
lemma independent_energy_sum_second_moment (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) :
    (∫ ω, (∑ i, F ω i * G ω i) ^ 2 ∂ν) =
      ∑ i, ∑ j, (∫ ω, F ω i * F ω j ∂ν) * (∫ ω, G ω i * G ω j ∂ν) := by
  have hexpand (ω : E) : (∑ i, F ω i * G ω i) ^ 2 =
      ∑ i, ∑ j, (F ω i * F ω j) * (G ω i * G ω j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    independent_energy_fourth_product_integrable hind hF hG i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    independent_energy_fourth_product_integrable hind hF hG i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hi : IndepFun (fun ω => F ω i * F ω j) (fun ω => G ω i * G ω j) ν :=
    hind.comp (by fun_prop : Measurable (fun v : Fin J → ℝ => v i * v j))
      (by fun_prop : Measurable (fun v : Fin J → ℝ => v i * v j))
  exact hi.integral_fun_mul_eq_mul_integral
    ((hF i).integrable_mul (hF j)).aestronglyMeasurable
    ((hG i).integrable_mul (hG j)).aestronglyMeasurable

/-- Independence makes the energy square-integrable using only second moments of each chain. -/
-- @node: independent_energy_sum_memLp
lemma independent_energy_sum_memLp (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) :
    MemLp (fun ω => ∑ i, F ω i * G ω i) 2 ν := by
  apply memLp_finsetSum
  intro i _
  apply (memLp_two_iff_integrable_sq
    ((hF i).aestronglyMeasurable.mul (hG i).aestronglyMeasurable)).2
  exact (independent_energy_fourth_product_integrable hind hF hG i i).congr
    (Filter.Eventually.of_forall (fun ω => by simp only [Pi.mul_apply]; ring))

/-- A common coordinate mean makes the independent energy mean its squared Hilbert norm. -/
-- @node: independent_energy_common_mean
lemma independent_energy_common_mean (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) (μ : Hj J)
    (hmeanF : ∀ i, (∫ ω, F ω i ∂ν) = μ i)
    (hmeanG : ∀ i, (∫ ω, G ω i ∂ν) = μ i) :
    (∫ ω, ∑ i, F ω i * G ω i ∂ν) = ‖μ‖ ^ 2 := by
  rw [independent_energy_sum_mean hind hF hG, EuclideanSpace.real_norm_sq_eq]
  simp only [hmeanF, hmeanG, pow_two]

/-- Expanding second moments into covariance and mean gives the quadratic form and square trace. -/
-- @node: energy_covariance_sum_algebra
lemma energy_covariance_sum_algebra (σ : Matrix (Fin J) (Fin J) ℝ)
    (hsym : ∀ i j, σ i j = σ j i) (μ : Hj J) :
    (∑ i, ∑ j, (σ i j + μ i * μ j) ^ 2) =
      2 * covarianceForm σ μ + covarianceSquareTrace σ + (‖μ‖ ^ 2) ^ 2 := by
  have hterm (i j : Fin J) : (σ i j + μ i * μ j) ^ 2 =
      2 * (μ i * σ i j * μ j) + σ i j * σ j i + μ i ^ 2 * μ j ^ 2 := by
    rw [← hsym i j]
    ring
  have hnorm : (‖μ‖ ^ 2) ^ 2 = ∑ i, ∑ j, μ i ^ 2 * μ j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hnorm]
  simp only [covarianceForm, covarianceSquareTrace, Finset.mul_sum]

/-- Independent chains with equal first and second moments have the exact energy variance in (29). -/
-- @node: independent_energy_common_variance
lemma independent_energy_common_variance (hind : IndepFun F G ν)
    (hF : ∀ i, MemLp (fun ω => F ω i) 2 ν)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 ν) (μ : Hj J)
    (hmeanF : ∀ i, (∫ ω, F ω i ∂ν) = μ i)
    (hmeanG : ∀ i, (∫ ω, G ω i ∂ν) = μ i)
    (hsecond : ∀ i j, (∫ ω, G ω i * G ω j ∂ν) = ∫ ω, F ω i * F ω j ∂ν) :
    let σ : Matrix (Fin J) (Fin J) ℝ := fun i j =>
      covariance (fun ω => F ω i) (fun ω => F ω j) ν
    variance (fun ω => ∑ i, F ω i * G ω i) ν =
      2 * covarianceForm σ μ + covarianceSquareTrace σ := by
  intro σ
  have hs (i j : Fin J) : (∫ ω, F ω i * F ω j ∂ν) = σ i j + μ i * μ j := by
    have hc := covariance_eq_sub (hF i) (hF j)
    change σ i j = (∫ ω, F ω i * F ω j ∂ν) -
      (∫ ω, F ω i ∂ν) * (∫ ω, F ω j ∂ν) at hc
    rw [hmeanF i, hmeanF j] at hc
    linarith
  have hsym (i j : Fin J) : σ i j = σ j i := covariance_comm _ _
  rw [variance_eq_sub (independent_energy_sum_memLp hind hF hG),
    independent_energy_common_mean hind hF hG μ hmeanF hmeanG]
  change (∫ ω, (∑ i, F ω i * G ω i) ^ 2 ∂ν) - (‖μ‖ ^ 2) ^ 2 = _
  rw [independent_energy_sum_second_moment hind hF hG]
  simp_rw [hsecond, hs]
  simp_rw [← pow_two]
  rw [energy_covariance_sum_algebra σ hsym μ]
  ring

/-- Square integrability of a Hilbert-valued chain implies it for every coordinate. -/
-- @node: hilbert_energy_coordinate_memLp
lemma hilbert_energy_coordinate_memLp {F : E → Hj J} (hF : MemLp F 2 ν) (i : Fin J) :
    MemLp (fun ω => F ω i) 2 ν := by
  apply hF.of_le
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin J => ℝ) i).continuous.comp_aestronglyMeasurable
      hF.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => PiLp.norm_apply_le (F ω) i)

/-- A Hilbert-valued integral commutes with each finite-dimensional coordinate. -/
-- @node: hilbert_energy_coordinate_mean
lemma hilbert_energy_coordinate_mean {F : E → Hj J} (hF : Integrable F ν) (i : Fin J) :
    (∫ ω, F ω i ∂ν) = (∫ ω, F ω ∂ν) i := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin J => ℝ) i).integral_comp_comm hF

variable [MeasurableSpace (Hj J)] [BorelSpace (Hj J)]

/-- Independent identically distributed Hilbert chains give the exact energy moments in (29). -/
-- @node: independent_hilbert_energy_moments
lemma independent_hilbert_energy_moments {F G : E → Hj J}
    (hind : IndepFun F G ν) (hid : IdentDistrib F G ν ν) (hF : MemLp F 2 ν) :
    let μ := ∫ ω, F ω ∂ν
    let σ : Matrix (Fin J) (Fin J) ℝ := fun i j =>
      ∫ ω, (F ω i - μ i) * (F ω j - μ j) ∂ν
    MemLp (fun ω => inner ℝ (F ω) (G ω)) 2 ν ∧
      (∫ ω, inner ℝ (F ω) (G ω) ∂ν) = ‖μ‖ ^ 2 ∧
      variance (fun ω => inner ℝ (F ω) (G ω)) ν =
        2 * covarianceForm σ μ + covarianceSquareTrace σ := by
  intro μ σ
  have hG := hid.memLp_snd hF
  have hFc := fun i => hilbert_energy_coordinate_memLp hF i
  have hGc := fun i => hilbert_energy_coordinate_memLp hG i
  have hindc : IndepFun (fun ω i => F ω i) (fun ω i => G ω i) ν :=
    hind.comp (by fun_prop : Measurable (fun v : Hj J => fun i => v i))
      (by fun_prop : Measurable (fun v : Hj J => fun i => v i))
  have hmF (i : Fin J) : (∫ ω, F ω i ∂ν) = μ i :=
    hilbert_energy_coordinate_mean (hF.integrable (by norm_num)) i
  have hmG (i : Fin J) : (∫ ω, G ω i ∂ν) = μ i := by
    exact (hid.comp (by fun_prop : Measurable (fun v : Hj J => v i))).integral_eq.symm.trans
      (hmF i)
  have hs (i j : Fin J) : (∫ ω, G ω i * G ω j ∂ν) = ∫ ω, F ω i * F ω j ∂ν :=
    (hid.comp (by fun_prop : Measurable (fun v : Hj J => v i * v j))).integral_eq.symm
  have hinner (ω : E) : inner ℝ (F ω) (G ω) = ∑ i, F ω i * G ω i := by
    simp [PiLp.inner_apply, mul_comm]
  simp_rw [hinner]
  refine ⟨independent_energy_sum_memLp hindc hFc hGc,
    independent_energy_common_mean hindc hFc hGc μ hmF hmG, ?_⟩
  have hv := independent_energy_common_variance hindc hFc hGc μ hmF hmG hs
  have hσ : (fun i j => covariance (fun ω => F ω i) (fun ω => F ω j) ν) = σ := by
    funext i j
    simp only [covariance, hmF]
    rfl
  simpa only [hσ] using hv

/-- The observable energy has the centered-chain expansion (29) for every realization. -/
-- @node: energy_centered_chain_expansion
lemma energy_centered_chain_expansion {m : ℕ} (train : Fin m → Omega)
    (mx my L T q : ℕ) (kt : ℕ → ℕ) (eval : EvalData m) (μ : Hj J) :
    energy train mx my L T J q kt eval = ‖μ‖ ^ 2 +
      inner ℝ μ (coefficientChain train mx my L T J q kt eval 0 - μ) +
      inner ℝ μ (coefficientChain train mx my L T J q kt eval 1 - μ) +
      inner ℝ (coefficientChain train mx my L T J q kt eval 0 - μ)
        (coefficientChain train mx my L T J q kt eval 1 - μ) := by
  simp only [energy, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm μ (coefficientChain train mx my L T J q kt eval 0)]
  ring

/-- The general independent-chain calculation specializes to the frozen observable energy,
mean and covariance definitions; independence, equal laws and L² regularity remain explicit inputs. -/
-- @node: energy_moments_of_independent_chains
lemma energy_moments_of_independent_chains {m : ℕ} (P : ObsLaw) (train : Fin m → Omega)
    (mx my L T q : ℕ) (kt : ℕ → ℕ)
    (hind : IndepFun (fun eval => coefficientChain train mx my L T J q kt eval 0)
      (fun eval => coefficientChain train mx my L T J q kt eval 1) (evalLaw P m))
    (hid : IdentDistrib (fun eval => coefficientChain train mx my L T J q kt eval 0)
      (fun eval => coefficientChain train mx my L T J q kt eval 1)
      (evalLaw P m) (evalLaw P m))
    (hL2 : MemLp (fun eval => coefficientChain train mx my L T J q kt eval 0)
      2 (evalLaw P m)) :
    MemLp (energy train mx my L T J q kt) 2 (evalLaw P m) ∧
      (∫ eval, energy train mx my L T J q kt eval ∂evalLaw P m) =
        ‖contrastMean P train mx my L T J q kt‖ ^ 2 ∧
      variance (energy train mx my L T J q kt) (evalLaw P m) =
        2 * covarianceForm (contrastCovariance P train mx my L T J q kt)
          (contrastMean P train mx my L T J q kt) +
        covarianceSquareTrace (contrastCovariance P train mx my L T J q kt) := by
  letI : IsProbabilityMeasure (evalLaw P m) := by
    unfold evalLaw
    infer_instance
  exact independent_hilbert_energy_moments hind hid hL2

end CausalSmith.Stat.DensityEffectRoughNull
