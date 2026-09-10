import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.FiniteKernel
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sequences

/-!
# Existence and uniqueness of finite stationary distributions

This module isolates the topological fixed-point argument for finite stochastic
kernels.  Existence uses compactness of the finite probability simplex, while
strict `ℓ¹` contraction supplies uniqueness.
-/

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- Given [a row-stochastic finite transition matrix](hyp:hP), [a nonnegative contraction coefficient](hyp:hrho0), [the fact that the coefficient is strictly below one](hyp:hrho1), and [a total-variation contraction bound](hyp:hcontract), [there is exactly one stationary probability distribution](goal). -/
theorem existsUnique_stationary_of_contractsL1 {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} {rho : ℝ}
    (hP : IsStochasticMatrix P) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P rho) :
    ∃! π : ι → ℝ, IsStationary P π := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let p₀ : ι → ℝ := Pi.single i₀ 1
  have hp₀ : IsProbabilityVector p₀ := by
    change p₀ ∈ stdSimplex ℝ ι
    simpa only [p₀] using single_mem_stdSimplex ℝ i₀
  let p : ℕ → (ι → ℝ) := markovIterate P p₀
  have hp (n : ℕ) : IsProbabilityVector (p n) := hP.iterate_probability hp₀ n
  have hl1_nonneg (q r : ι → ℝ) : 0 ≤ l1Distance q r := by
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  let d : ℕ → ℝ := fun n => l1Distance (p (n + 1)) (p n)
  have hd_le (n : ℕ) : d n ≤ rho ^ n * d 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          d (n + 1) = l1Distance (markovStep (p (n + 1)) P)
              (markovStep (p n) P) := by
                simp only [d, p, markovIterate]
          _ ≤ rho * l1Distance (p (n + 1)) (p n) :=
            hcontract _ _ (hp (n + 1)) (hp n)
          _ = rho * d n := rfl
          _ ≤ rho * (rho ^ n * d 0) := mul_le_mul_of_nonneg_left ih hrho0
          _ = rho ^ (n + 1) * d 0 := by rw [pow_succ]; ring
  have hd_tendsto : Filter.Tendsto d Filter.atTop (nhds 0) := by
    have hu : Filter.Tendsto (fun n => rho ^ n * d 0) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1).mul_const (d 0)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Filter.Eventually.of_forall fun n => hl1_nonneg _ _
    · exact Filter.Eventually.of_forall hd_le
  have hp_simplex (n : ℕ) : p n ∈ stdSimplex ℝ ι := hp n
  obtain ⟨π, hπ_prob, φ, hφ, hφ_tendsto⟩ :=
    (isCompact_stdSimplex ℝ ι).tendsto_subseq hp_simplex
  have hd_subseq : Filter.Tendsto (fun n => d (φ n)) Filter.atTop (nhds 0) :=
    hd_tendsto.comp hφ.tendsto_atTop
  have hshift : Filter.Tendsto (fun n => p (φ n + 1)) Filter.atTop (nhds π) := by
    rw [tendsto_pi_nhds]
    intro i
    have habs (n : ℕ) : |p (φ n + 1) i - p (φ n) i| ≤ d (φ n) := by
      apply Finset.single_le_sum (fun j _ => abs_nonneg (p (φ n + 1) j - p (φ n) j))
      exact Finset.mem_univ i
    have hdiff : Filter.Tendsto (fun n => p (φ n + 1) i - p (φ n) i)
        Filter.atTop (nhds 0) := by
      have hneg : Filter.Tendsto (fun n => -d (φ n)) Filter.atTop (nhds 0) := by
        simpa using hd_subseq.neg
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hd_subseq
      · exact Filter.Eventually.of_forall fun n => (neg_le_of_abs_le (habs n))
      · exact Filter.Eventually.of_forall fun n => (le_of_abs_le (habs n))
    convert (hφ_tendsto.apply_nhds i).add hdiff using 1 <;> simp
  have hstep : Filter.Tendsto (fun n => markovStep (p (φ n)) P)
      Filter.atTop (nhds (markovStep π P)) := by
    rw [tendsto_pi_nhds]
    intro j
    unfold markovStep Matrix.vecMul dotProduct
    apply tendsto_finsetSum
    intro i hi
    exact (hφ_tendsto.apply_nhds i).mul tendsto_const_nhds
  have hshift_step : Filter.Tendsto (fun n => p (φ n + 1))
      Filter.atTop (nhds (markovStep π P)) := by
    convert hstep using 1
    funext n
    simp only [p, markovIterate]
  have hfixed : markovStep π P = π := tendsto_nhds_unique hshift_step hshift
  refine ⟨π, ⟨hπ_prob, hfixed⟩, ?_⟩
  intro π' hπ'
  have hdist_le : l1Distance π' π ≤ rho * l1Distance π' π := by
    calc
      l1Distance π' π = l1Distance (markovStep π' P) (markovStep π P) := by
        rw [hπ'.2, hfixed]
      _ ≤ rho * l1Distance π' π := hcontract _ _ hπ'.1 hπ_prob
  have hdist_zero : l1Distance π' π = 0 := by
    nlinarith [hl1_nonneg π' π]
  funext i
  have hi : |π' i - π i| ≤ l1Distance π' π := by
    apply Finset.single_le_sum (fun j _ => abs_nonneg (π' j - π j))
    exact Finset.mem_univ i
  rw [hdist_zero] at hi
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
