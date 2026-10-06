module
public import Causalean.Stat.CLT.FiniteIidTriangular.FourthMoment
public import Causalean.Stat.FiniteDesign.Chebyshev

/-!
Probability limits for empirical first, second, and centered second moments in bounded finite iid triangular rows. Direct finite-design Chebyshev calculations yield consistency without importing an experimentation layer.
-/

@[expose] public section

namespace Causalean.Stat.CLT.FiniteIidTriangular

open Filter Topology

open Causalean.Experimentation.DesignBased

private theorem finiteDesign_pr_or_le {Ω' : Type*} [Fintype Ω']
    (D : FiniteDesign Ω') (P Q : Ω' → Prop)
    [DecidablePred P] [DecidablePred Q] :
    D.Pr (fun z => P z ∨ Q z) ≤ D.Pr P + D.Pr Q := by
  unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
  by_cases hP : P z <;> by_cases hQ : Q z <;> simp [hP, hQ]

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- The finite-product probability of a predicate is the sum of the masses of the outcome
vectors satisfying it. -/
def eventProbability (n : ℕ) (P : (Fin (M.N n) → Y) → Prop) [DecidablePred P] : ℝ :=
  M.expect n (fun ys => if P ys then 1 else 0)

/-- The literal finite-product event probability equals the probability assigned by
the corresponding finite product design. -/
theorem eventProbability_eq_designPr (n : ℕ)
    (P : (Fin (M.N n) → Y) → Prop) [DecidablePred P] :
    M.eventProbability n P = (M.productDesign n).Pr P := by
  rfl

/-- The empirical second moment has expectation equal to the one-coordinate second moment
whenever the row length is positive. -/
theorem expect_empiricalSecond (n : ℕ) (hn : 0 < M.N n) :
    M.expect n (M.empiricalSecond n) = M.oneSecond n := by
  classical
  have hN : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    M.expect n (M.empiricalSecond n) =
        (M.N n : ℝ)⁻¹ * ∑ i : Fin (M.N n),
          M.expect n (fun ys => (M.f n (ys i)) ^ 2) := by
            simp only [expect, empiricalSecond, Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            ext i
            congr 1
            ext ys
            ring
    _ = (M.N n : ℝ)⁻¹ * ∑ _i : Fin (M.N n), M.oneSecond n := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact M.expect_coordinate n i (fun y => (M.f n y) ^ 2)
    _ = M.oneSecond n := by simp [hN]

/-- The mean-squared error of the empirical second moment is at most the fourth power of
the common score bound divided by the positive row length. -/
theorem empiricalSecond_mse_le (n : ℕ) (hn : 0 < M.N n) :
    M.expect n (fun ys => (M.empiricalSecond n ys - M.oneSecond n) ^ 2) ≤
      M.B ^ 4 / (M.N n : ℝ) := by
  classical
  let μ := M.oneSecond n
  let z (i : Fin (M.N n)) (ys : Fin (M.N n) → Y) := (M.f n (ys i)) ^ 2 - μ
  have hN : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum (g : Fin (M.N n) → (Fin (M.N n) → Y) → ℝ) :
      M.expect n (fun ys => ∑ i, g i ys) = ∑ i, M.expect n (g i) := by
    simp only [expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hscale (c : ℝ) (g : (Fin (M.N n) → Y) → ℝ) :
      M.expect n (fun ys => c * g ys) = c * M.expect n g := by
    simp only [expect]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ys _
    ring
  have hpair (i j : Fin (M.N n)) (hij : i ≠ j) :
      M.expect n (fun ys => z i ys * z j ys) = 0 := by
    rw [M.expect_coordinate_mul n i j hij
      (fun y => (M.f n y) ^ 2 - μ) (fun y => (M.f n y) ^ 2 - μ)]
    simp [μ, oneSecond, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      M.mass_one]
  have hdiag (i : Fin (M.N n)) : M.expect n (fun ys => (z i ys) ^ 2) ≤ M.B ^ 4 := by
    have hc := M.expect_coordinate n i (fun y => ((M.f n y) ^ 2 - μ) ^ 2)
    change M.expect n (fun ys => (z i ys) ^ 2) = _ at hc
    rw [hc]
    have hμsq : 0 ≤ μ ^ 2 := sq_nonneg μ
    have hfourth : (∑ y, M.w n y * (M.f n y) ^ 4) ≤ M.B ^ 4 := by
      calc
        _ ≤ ∑ y, M.w n y * M.B ^ 4 := by
          apply Finset.sum_le_sum
          intro y _
          apply mul_le_mul_of_nonneg_left _ (M.mass_nonneg n y)
          have hb := M.bound n y
          have hb4 : (M.f n y) ^ 4 = |M.f n y| ^ 4 := by
            rw [← abs_pow]
            exact (abs_of_nonneg (by positivity)).symm
          rw [hb4]
          exact pow_le_pow_left₀ (abs_nonneg _) hb _
        _ = M.B ^ 4 := by simp [← Finset.sum_mul, M.mass_one]
    have hv : (∑ y, M.w n y * ((M.f n y) ^ 2 - μ) ^ 2) =
        (∑ y, M.w n y * (M.f n y) ^ 4) - μ ^ 2 := by
      calc
        _ = (∑ y, M.w n y * (M.f n y) ^ 4) -
            2 * μ * (∑ y, M.w n y * (M.f n y) ^ 2) +
            μ ^ 2 * (∑ y, M.w n y) := by
              simp only [Finset.mul_sum]
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ = _ := by rw [M.mass_one]; dsimp [μ, oneSecond]; ring
    rw [hv]
    linarith
  have hcenter (ys : Fin (M.N n) → Y) :
      M.empiricalSecond n ys - μ = (M.N n : ℝ)⁻¹ * ∑ i, z i ys := by
    simp only [empiricalSecond, z, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hvar : M.expect n (fun ys => (∑ i, z i ys) ^ 2) =
      ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
    calc
      _ = ∑ i : Fin (M.N n), ∑ j : Fin (M.N n),
          M.expect n (fun ys => z i ys * z j ys) := by
            calc
              _ = M.expect n (fun ys => ∑ i : Fin (M.N n),
                  ∑ j : Fin (M.N n), z i ys * z j ys) := by
                    congr 1
                    funext ys
                    rw [← Finset.sum_mul_sum]
                    ring
              _ = _ := by
                    rw [hsum]
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [hsum]
      _ = ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · simp only [pow_two]
            · intro j _ hji
              exact hpair i j (Ne.symm hji)
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
  calc
    M.expect n (fun ys => (M.empiricalSecond n ys - M.oneSecond n) ^ 2) =
        ((M.N n : ℝ)⁻¹) ^ 2 *
          ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
            simp_rw [show M.oneSecond n = μ from rfl, hcenter]
            rw [← hvar, ← hscale]
            congr 1
            funext ys
            ring
    _ ≤ ((M.N n : ℝ)⁻¹) ^ 2 * ((M.N n : ℝ) * M.B ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin,
            nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
              (fun i _ => hdiag i)
    _ = M.B ^ 4 / (M.N n : ℝ) := by field_simp

/-- The mean squared empirical score mean is at most the squared common score
bound divided by the positive row length. -/
theorem empiricalMean_mse_le (n : ℕ) (hn : 0 < M.N n) :
    M.expect n (fun ys => (M.empiricalMean n ys) ^ 2) ≤
      M.B ^ 2 / (M.N n : ℝ) := by
  classical
  let z (i : Fin (M.N n)) (ys : Fin (M.N n) → Y) := M.f n (ys i)
  have hN : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum (g : Fin (M.N n) → (Fin (M.N n) → Y) → ℝ) :
      M.expect n (fun ys => ∑ i, g i ys) = ∑ i, M.expect n (g i) := by
    simp only [expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hscale (c : ℝ) (g : (Fin (M.N n) → Y) → ℝ) :
      M.expect n (fun ys => c * g ys) = c * M.expect n g := by
    simp only [expect]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ys _
    ring
  have hpair (i j : Fin (M.N n)) (hij : i ≠ j) :
      M.expect n (fun ys => z i ys * z j ys) = 0 := by
    rw [M.expect_coordinate_mul n i j hij (M.f n) (M.f n)]
    simp [M.centered n]
  have hdiag (i : Fin (M.N n)) :
      M.expect n (fun ys => (z i ys) ^ 2) ≤ M.B ^ 2 := by
    rw [M.expect_coordinate n i (fun y => (M.f n y) ^ 2)]
    calc
      (∑ y, M.w n y * (M.f n y) ^ 2) ≤ ∑ y, M.w n y * M.B ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (M.mass_nonneg n y)
        have hb := M.bound n y
        have hb2 : (M.f n y) ^ 2 = |M.f n y| ^ 2 := by
          rw [← abs_pow]
          exact (abs_of_nonneg (by positivity)).symm
        rw [hb2]
        exact pow_le_pow_left₀ (abs_nonneg _) hb _
      _ = M.B ^ 2 := by simp [← Finset.sum_mul, M.mass_one]
  have hvar : M.expect n (fun ys => (∑ i, z i ys) ^ 2) =
      ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
    calc
      _ = ∑ i : Fin (M.N n), ∑ j : Fin (M.N n),
          M.expect n (fun ys => z i ys * z j ys) := by
            calc
              _ = M.expect n (fun ys => ∑ i : Fin (M.N n),
                  ∑ j : Fin (M.N n), z i ys * z j ys) := by
                    congr 1
                    funext ys
                    rw [← Finset.sum_mul_sum]
                    ring
              _ = _ := by
                    rw [hsum]
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [hsum]
      _ = ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · simp only [pow_two]
            · intro j _ hji
              exact hpair i j (Ne.symm hji)
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
  calc
    M.expect n (fun ys => (M.empiricalMean n ys) ^ 2) =
        ((M.N n : ℝ)⁻¹) ^ 2 *
          ∑ i : Fin (M.N n), M.expect n (fun ys => (z i ys) ^ 2) := by
            simp only [empiricalMean, scoreSum]
            rw [← hvar, ← hscale]
            congr 1
            funext ys
            ring
    _ ≤ ((M.N n : ℝ)⁻¹) ^ 2 * ((M.N n : ℝ) * M.B ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin,
            nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
              (fun i _ => hdiag i)
    _ = M.B ^ 2 / (M.N n : ℝ) := by field_simp

/-- At every positive error tolerance, the finite-product probability that the empirical
second moment differs from the limiting variance by at least that tolerance tends to zero. -/
theorem empiricalSecond_tendstoInProbability (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => M.eventProbability n
      (fun ys => ε ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)|)) atTop (𝓝 0) := by
  classical
  have hhalf : 0 < ε / 2 := by linarith
  have hN : Tendsto (fun n => (M.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp M.length_tendsto
  have hsmall : Tendsto (fun n => M.B ^ 4 / (M.N n : ℝ) / (ε / 2) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (M.B ^ 4)).comp M.length_tendsto
    simpa only [Function.comp_def, zero_div] using h.div_const ((ε / 2) ^ 2)
  have hcenter : ∀ᶠ n in atTop, |M.oneSecond n - (M.v₀ : ℝ)| < ε / 2 := by
    simpa only [oneSecond, Real.dist_eq] using
      (Metric.tendsto_nhds.1 M.variance_tendsto (ε / 2) hhalf)
  have hpositive : ∀ᶠ n in atTop, 0 < M.N n :=
    M.length_tendsto.eventually (eventually_gt_atTop 0)
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ M.eventProbability n
      (fun ys => ε ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)|) := by
    filter_upwards [] with n
    rw [M.eventProbability_eq_designPr]
    exact (M.productDesign n).Pr_nonneg _
  have hupper : ∀ᶠ n in atTop, M.eventProbability n
      (fun ys => ε ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)|) ≤
      M.B ^ 4 / (M.N n : ℝ) / (ε / 2) ^ 2 := by
    filter_upwards [hcenter, hpositive] with n hn hnN
    rw [M.eventProbability_eq_designPr]
    have hE : (M.productDesign n).E (M.empiricalSecond n) = M.oneSecond n :=
      M.expect_empiricalSecond n hnN
    have htail : (M.productDesign n).Pr
        (fun ys => ε ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)|) ≤
        (M.productDesign n).Pr
          (fun ys => ε / 2 ≤ |M.empiricalSecond n ys - M.oneSecond n|) := by
      apply (M.productDesign n).Pr_mono
      intro ys hys
      have ht := abs_sub_le (M.empiricalSecond n ys) (M.oneSecond n) (M.v₀ : ℝ)
      by_contra hc
      have hc' : |M.empiricalSecond n ys - M.oneSecond n| < ε / 2 := lt_of_not_ge hc
      linarith
    have hcheb := (M.productDesign n).chebyshev (M.empiricalSecond n) hhalf
    rw [hE] at hcheb
    have hvar : (M.productDesign n).Var (M.empiricalSecond n) =
        M.expect n (fun ys => (M.empiricalSecond n ys - M.oneSecond n) ^ 2) := by
      rw [show (M.productDesign n).Var (M.empiricalSecond n) =
        M.expect n (fun ys => (M.empiricalSecond n ys -
          (M.productDesign n).E (M.empiricalSecond n)) ^ 2) from rfl, hE]
    rw [hvar] at hcheb
    exact htail.trans (hcheb.trans
      (div_le_div_of_nonneg_right (M.empiricalSecond_mse_le n hnN)
        (sq_nonneg _)))
  exact squeeze_zero' hnonneg hupper hsmall

/-- At every positive error tolerance, the finite-product probability that the empirical
score mean differs from zero by at least that tolerance tends to zero. -/
theorem empiricalMean_tendstoInProbability (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => M.eventProbability n
      (fun ys => ε ≤ |M.empiricalMean n ys|)) atTop (𝓝 0) := by
  classical
  have hN : Tendsto (fun n => (M.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp M.length_tendsto
  have hsmall : Tendsto (fun n => M.B ^ 2 / (M.N n : ℝ) / ε ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (M.B ^ 2)).comp M.length_tendsto
    simpa only [Function.comp_def, zero_div] using h.div_const (ε ^ 2)
  have hpositive : ∀ᶠ n in atTop, 0 < M.N n :=
    M.length_tendsto.eventually (eventually_gt_atTop 0)
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ M.eventProbability n
      (fun ys => ε ≤ |M.empiricalMean n ys|) := by
    filter_upwards [] with n
    rw [M.eventProbability_eq_designPr]
    exact (M.productDesign n).Pr_nonneg _
  have hupper : ∀ᶠ n in atTop, M.eventProbability n
      (fun ys => ε ≤ |M.empiricalMean n ys|) ≤
      M.B ^ 2 / (M.N n : ℝ) / ε ^ 2 := by
    filter_upwards [hpositive] with n hn
    rw [M.eventProbability_eq_designPr]
    have hE : (M.productDesign n).E (M.empiricalMean n) = 0 := by
      have hNne : (M.N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      change M.expect n (M.empiricalMean n) = 0
      simp only [expect, empiricalMean, scoreSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hcoord (i : Fin (M.N n)) :
          ∑ ys : Fin (M.N n) → Y, M.mass n ys * M.f n (ys i) = 0 := by
        change M.expect n (fun ys => M.f n (ys i)) = 0
        rw [M.expect_coordinate]
        exact M.centered n
      calc
        (∑ i : Fin (M.N n), ∑ ys : Fin (M.N n) → Y,
            M.mass n ys * ((M.N n : ℝ)⁻¹ * M.f n (ys i))) =
            ∑ i : Fin (M.N n), (M.N n : ℝ)⁻¹ *
              (∑ ys : Fin (M.N n) → Y, M.mass n ys * M.f n (ys i)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro ys _
                ring
        _ = 0 := by simp [hcoord]
    have hcheb := (M.productDesign n).chebyshev (M.empiricalMean n) hε
    rw [hE] at hcheb
    simp only [sub_zero] at hcheb
    have hvar : (M.productDesign n).Var (M.empiricalMean n) =
        M.expect n (fun ys => (M.empiricalMean n ys) ^ 2) := by
      rw [show (M.productDesign n).Var (M.empiricalMean n) =
        M.expect n (fun ys => (M.empiricalMean n ys -
          (M.productDesign n).E (M.empiricalMean n)) ^ 2) from rfl, hE]
      simp
    rw [hvar] at hcheb
    exact hcheb.trans
      (div_le_div_of_nonneg_right (M.empiricalMean_mse_le n hn) (sq_nonneg _))
  exact squeeze_zero' hnonneg hupper hsmall

/-- At [a positive error tolerance](hyp:ε,hε), [the finite-product probability that the
centered empirical variance differs from the limiting variance by at least that tolerance
tends to zero](goal). -/
theorem empiricalVariance_tendstoInProbability (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => M.eventProbability n
      (fun ys => ε ≤ |M.empiricalVariance n ys - (M.v₀ : ℝ)|)) atTop (𝓝 0) := by
  classical
  have hhalf : 0 < ε / 2 := by linarith
  have hsqrt : 0 < Real.sqrt (ε / 2) := Real.sqrt_pos.2 hhalf
  have hsecond := M.empiricalSecond_tendstoInProbability (ε / 2) hhalf
  have hmean := M.empiricalMean_tendstoInProbability (Real.sqrt (ε / 2)) hsqrt
  have hsum : Tendsto (fun n => M.eventProbability n
      (fun ys => ε / 2 ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)|) +
      M.eventProbability n
      (fun ys => Real.sqrt (ε / 2) ≤ |M.empiricalMean n ys|)) atTop (𝓝 0) := by
    simpa using hsecond.add hmean
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hsum
  · rw [M.eventProbability_eq_designPr]
    exact (M.productDesign n).Pr_nonneg _
  · rw [M.eventProbability_eq_designPr, M.eventProbability_eq_designPr,
      M.eventProbability_eq_designPr]
    have hmono : (M.productDesign n).Pr
        (fun ys => ε ≤ |M.empiricalVariance n ys - (M.v₀ : ℝ)|) ≤
        (M.productDesign n).Pr (fun ys =>
          ε / 2 ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)| ∨
          Real.sqrt (ε / 2) ≤ |M.empiricalMean n ys|) := by
      apply (M.productDesign n).Pr_mono
      intro ys hy
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have hsq : (M.empiricalMean n ys) ^ 2 < ε / 2 := by
        have hpow := (sq_lt_sq₀ (abs_nonneg (M.empiricalMean n ys)) hsqrt.le).2 h2
        rw [sq_abs, Real.sq_sqrt hhalf.le] at hpow
        exact hpow
      have htri : |M.empiricalVariance n ys - (M.v₀ : ℝ)| ≤
          |M.empiricalSecond n ys - (M.v₀ : ℝ)| + (M.empiricalMean n ys) ^ 2 := by
        rw [empiricalVariance]
        have heq : M.empiricalSecond n ys - (M.empiricalMean n ys) ^ 2 - (M.v₀ : ℝ) =
            (M.empiricalSecond n ys - (M.v₀ : ℝ)) - (M.empiricalMean n ys) ^ 2 := by ring
        rw [heq]
        calc
          _ ≤ |M.empiricalSecond n ys - (M.v₀ : ℝ)| +
              |(M.empiricalMean n ys) ^ 2| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (sq_nonneg (M.empiricalMean n ys))]
      linarith
    exact hmono.trans (finiteDesign_pr_or_le
      (M.productDesign n) _ _)

end RowModel
end Causalean.Stat.CLT.FiniteIidTriangular
