module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedDuality
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedUpperRegularity
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction

/-! # Weighted upper approximation by Jackson smoothing

The angular regularity of the nonlinear remainder and the promoted Jackson
first-moment estimate give the universal sqrt(M)/K upper order in roadmap (14).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Analysis.JacksonApproximation


-- @node: weightedJackson_angular_approximation
/-- An even periodic continuous function has an even Jackson-smoothed trigonometric approximant, with error controlled by its angular Lipschitz constant. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hf,he,hp,hL,hl), the [stated conclusion](goal) holds. -/
lemma weightedJackson_angular_approximation {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (hf : Continuous f) (he : Function.Even f)
    (hp : Function.Periodic f (2 * Real.pi)) (L : ℝ) (hL : 0 ≤ L)
    (hl : ∀ s t, |f s - f t| ≤ L * |s - t|) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ 2 * (N - 1) ∧
      ∀ t, |f t - p.eval (Real.cos t)| ≤ 32 * L / N := by
  classical
  let q := fun t : ℝ => ∫ u in Set.Icc (-Real.pi) Real.pi, f u * jackson N (t - u)
  obtain ⟨a, b, hab⟩ := jackson_isTrigPolyLE N hN
  have hjp : Function.Periodic (jackson N) (2 * Real.pi) := by
    intro t
    rw [hab, hab]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [mul_add, Int.cast_natCast] using congrArg₂
      (fun c s => a k * c + b k * s)
      (Real.cos_add_int_mul_two_pi ((k : ℝ) * t) (k : ℤ))
      (Real.sin_add_int_mul_two_pi ((k : ℝ) * t) (k : ℤ))
  have htrig : IsTrigPolyLE (2 * (N - 1)) q := by
    refine ⟨fun k => ∫ u in Set.Icc (-Real.pi) Real.pi,
      f u * (a k * Real.cos ((k : ℝ) * u) - b k * Real.sin ((k : ℝ) * u)),
      fun k => ∫ u in Set.Icc (-Real.pi) Real.pi,
      f u * (a k * Real.sin ((k : ℝ) * u) + b k * Real.cos ((k : ℝ) * u)), ?_⟩
    intro t
    dsimp [q]
    simp_rw [hab, Finset.mul_sum]
    rw [integral_finsetSum _ (fun k hk =>
      (show Continuous (fun u : ℝ => f u *
        (a k * Real.cos ((k : ℝ) * (t - u)) + b k * Real.sin ((k : ℝ) * (t - u)))) from by fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
    apply Finset.sum_congr rfl
    intro k hk
    have heq (u : ℝ) : f u *
        (a k * Real.cos ((k : ℝ) * (t - u)) + b k * Real.sin ((k : ℝ) * (t - u))) =
        (f u * (a k * Real.cos ((k : ℝ) * u) - b k * Real.sin ((k : ℝ) * u))) * Real.cos ((k : ℝ) * t) +
        (f u * (a k * Real.sin ((k : ℝ) * u) + b k * Real.cos ((k : ℝ) * u))) * Real.sin ((k : ℝ) * t) := by
      rw [mul_sub, Real.cos_sub, Real.sin_sub]
      ring
    simp_rw [heq]
    rw [integral_add, integral_mul_const, integral_mul_const]
    all_goals
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      fun_prop
  have hqe : Function.Even q := by
    intro t
    let F := fun u : ℝ => f u * jackson N (t - u)
    have heq (u : ℝ) : f u * jackson N (-t - u) = F (-u) := by
      dsimp [F]
      rw [he u]
      have ha : -t - u = -(t - -u) := by ring
      rw [ha, jackson_even]
    dsimp [q]
    simp_rw [heq]
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      intervalIntegral.integral_comp_neg]
    simp only [neg_neg]
    rfl
  obtain ⟨p, hdeg, heval⟩ := even_trigPoly_exists_polynomial htrig hqe
  refine ⟨p, hdeg, ?_⟩
  intro t
  rw [heval]
  have hshift : q t = ∫ u in Set.Icc (-Real.pi) Real.pi, f (u + t) * jackson N u := by
    have hperiod : Function.Periodic (fun u => f (u + t) * jackson N u) (2 * Real.pi) := by
      intro u
      dsimp only
      rw [show u + 2 * Real.pi + t = (u + t) + 2 * Real.pi by ring, hp, hjp]
    convert packet_periodic_integral_translate _ hperiod t using 1
    dsimp [q]
    congr 1
    funext u
    rw [sub_add_cancel]
    rw [show t - u = -(u - t) by ring, jackson_even]
  have hi : IntegrableOn (fun u => (f t - f (u + t)) * jackson N u)
      (Set.Icc (-Real.pi) Real.pi) := by
    exact ((continuous_const.sub (hf.comp (by fun_prop))).mul (continuous_jackson N)).continuousOn.integrableOn_compact isCompact_Icc
  have hdiff : f t - q t = ∫ u in Set.Icc (-Real.pi) Real.pi,
      (f t - f (u + t)) * jackson N u := by
    rw [hshift]
    simp_rw [sub_mul]
    rw [integral_sub, integral_const_mul, jackson_integral_eq_one N hN, mul_one]
    · exact ((continuous_jackson N).const_mul _).continuousOn.integrableOn_compact isCompact_Icc
    · exact ((hf.comp (by fun_prop)).mul (continuous_jackson N)).continuousOn.integrableOn_compact isCompact_Icc
  rw [hdiff]
  calc
    _ ≤ ∫ u in Set.Icc (-Real.pi) Real.pi, |(f t - f (u + t)) * jackson N u| := abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-Real.pi) Real.pi, L * (|u| * jackson N u) := by
      apply integral_mono hi.abs
        (((continuous_id.abs.mul (continuous_jackson N)).const_mul L).continuousOn.integrableOn_compact isCompact_Icc)
      intro u
      change |(f t - f (u + t)) * jackson N u| ≤ L * (|u| * jackson N u)
      rw [abs_mul, abs_of_nonneg (jackson_nonneg N hN u)]
      have h := hl t (u + t)
      rw [show t - (u + t) = -u by ring, abs_neg] at h
      nlinarith [jackson_nonneg N hN u]
    _ ≤ L * (32 / (N : ℝ)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (jackson_first_moment N hN) hL
    _ = 32 * L / N := by ring

/-- Jackson smoothing of the bounded nonlinear remainder, followed by the inverse cosine-coordinate affine substitution, gives an admissible degree-K polynomial with uniform error of order sqrt(M)/K (roadmap (14)). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma weightedApproximation_polynomial_upper {K : ℕ} (hK : 2 ≤ K)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ K ∧
      ∀ z ∈ Set.Icc 0 M, |phiEpsFormula ε z - p.eval z| ≤ 64 * Real.sqrt M / K := by
  let N := K / 2 + 1
  let f := fun t => packetRemainder ε (packetIntensity M t)
  have hf : Continuous f := by
    dsimp [f]
    unfold packetRemainder
    apply Continuous.add
    · fun_prop
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t
        linarith [(packetIntensity_mem_Icc hM.le t).1]
  have he : Function.Even f := by
    intro t
    simp only [f, packetIntensity, Real.cos_neg]
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro t
    simp only [f, packetIntensity, Real.cos_add_two_pi]
  obtain ⟨q, hq, herror⟩ := weightedJackson_angular_approximation
    (N := N) (by dsimp [N]; omega) f hf he hp (Real.sqrt M)
    (Real.sqrt_nonneg M) (packetRemainder_angular_lipschitz hM.le hε hεhi)
  let a : Polynomial ℝ := Polynomial.C (2 / M) * Polynomial.X - 1
  let p : Polynomial ℝ := Polynomial.C ε * (Polynomial.X - 1) + q.comp a
  have ha : a.natDegree ≤ 1 := by
    dsimp [a]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le
      (Polynomial.natDegree_mul_le.trans (by simp)) (by simp))
  have hdeg : p.natDegree ≤ K := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by
        simp only [Polynomial.natDegree_C, zero_add]
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp; omega))
    · exact Polynomial.natDegree_comp_le.trans
        ((Nat.mul_le_mul_right _ hq).trans
          ((Nat.mul_le_mul_left _ ha).trans (by dsimp [N]; simp only [mul_one]; omega)))
  refine ⟨p, hdeg, ?_⟩
  intro z hz
  let t := Real.arccos (2 * z / M - 1)
  have ht : Real.cos t = 2 * z / M - 1 := by
    apply Real.cos_arccos
    · have : 0 ≤ 2 * z / M := div_nonneg (mul_nonneg (by norm_num) hz.1) hM.le
      linarith
    · have : 2 * z / M ≤ 2 := (div_le_iff₀ hM).mpr (by linarith [hz.2])
      linarith
  have hzcoord : packetIntensity M t = z := by
    unfold packetIntensity
    rw [ht]
    field_simp
    ring
  have hpe : p.eval z = ε * (z - 1) + q.eval (Real.cos t) := by
    simp [p, a, Polynomial.eval_comp, ht]
    congr 2
    ring
  rw [hpe, phiEps_eq_packetRemainder hz.1]
  have herr := herror t
  dsimp only [f] at herr
  rw [hzcoord] at herr
  have hc : 32 * Real.sqrt M / (N : ℝ) ≤ 64 * Real.sqrt M / K := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by dsimp [N]; omega : 0 < N)
    have hKN : (K : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (by dsimp [N]; omega : K ≤ 2 * N)
    apply (div_le_div_iff₀ hNR hKR).mpr
    nlinarith [Real.sqrt_nonneg M]
  convert herr.trans hc using 1
  congr 1
  ring


-- @node: weightedApproxError_upper
/-- The explicit Jackson approximant bounds the weighted polynomial infimum with a universal constant, uniformly on the closed overlap interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hε,hεhi), the [stated conclusion](goal) holds. -/
lemma weightedApproxError_upper {K : ℕ} (hK : 2 ≤ K) {M ε : ℝ}
    (hM : 0 < M) (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    weightedApproxError K M ε ≤ 64 * Real.sqrt M / K := by
  obtain ⟨p, hp, herror⟩ := weightedApproximation_polynomial_upper hK hM hε hεhi
  have hb : BddBelow {e : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧
      e = sSup ((fun z : ℝ => |phiEpsFormula ε z - q.eval z| / (1 + z)) '' Set.Icc 0 M)} := by
    refine ⟨0, ?_⟩
    rintro e ⟨q, _, rfl⟩
    exact (weightedPolynomial_error_bound M ε hM.le q).1
  change sInf {e : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧
    e = sSup ((fun z : ℝ => |phiEpsFormula ε z - q.eval z| / (1 + z)) '' Set.Icc 0 M)} ≤ _
  apply (csInf_le hb ⟨p, hp, rfl⟩).trans
  apply csSup_le (by refine ⟨_, 0, ⟨le_rfl, hM.le⟩, rfl⟩)
  rintro v ⟨z, hz, rfl⟩
  apply (div_le_iff₀ (by linarith [hz.1] : 0 < 1 + z)).mpr
  exact (herror z hz).trans (le_mul_of_one_le_right (by positivity) (by linarith [hz.1]))

end CausalSmith.Stat.OptvalueVanishingoverlapRate
