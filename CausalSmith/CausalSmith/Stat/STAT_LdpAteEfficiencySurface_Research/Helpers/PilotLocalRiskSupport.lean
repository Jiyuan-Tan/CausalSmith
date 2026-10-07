module
public import Causalean.Stat.CLT.FiniteIidTriangular.Basic
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveTransfer
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowVariance

/-! # Exact conditional local risk of the adaptive main row -/

public section
noncomputable section

namespace Causalean.Stat.CLT.FiniteIidTriangular

open scoped BigOperators

/-- The squared sum of a centered finite iid row has expectation equal to the
row length times the one-coordinate second moment. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:M,n), these specify the stated inputs. -/
lemma RowModel.expect_scoreSum_sq {Y : Type*} [Fintype Y]
    (M : RowModel Y) (n : ℕ) :
    M.expect n (fun ys => (M.scoreSum n ys) ^ 2) =
      (M.N n : ℝ) * M.oneSecond n := by
  classical
  have hsumsq (ys : Fin (M.N n) → Y) :
      (∑ i, M.f n (ys i)) ^ 2 =
        ∑ i, ∑ j, M.f n (ys i) * M.f n (ys j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [scoreSum]
  simp_rw [hsumsq]
  rw [expect]
  simp_rw [Finset.mul_sum]
  calc
    (∑ ys : Fin (M.N n) → Y, ∑ i, ∑ j,
        M.mass n ys * (M.f n (ys i) * M.f n (ys j))) =
        ∑ i, ∑ ys : Fin (M.N n) → Y, ∑ j,
          M.mass n ys * (M.f n (ys i) * M.f n (ys j)) := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ ys : Fin (M.N n) → Y,
          M.mass n ys * (M.f n (ys i) * M.f n (ys j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, M.expect n (fun ys => M.f n (ys i) * M.f n (ys j)) := by
      rfl
    _ = ∑ i, M.expect n (fun ys => (M.f n (ys i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp [pow_two]
      · intro j _ hji
        rw [M.expect_coordinate_mul n i j (Ne.symm hji)]
        simp [M.centered]
      · simp
    _ = ∑ _i : Fin (M.N n), M.oneSecond n := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [oneSecond] using M.expect_coordinate n i (fun y => (M.f n y) ^ 2)
    _ = (M.N n : ℝ) * M.oneSecond n := by simp

end Causalean.Stat.CLT.FiniteIidTriangular

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter
open scoped BigOperators Topology
open Causalean.Stat.CLT.FiniteIidTriangular

/-- Conditional on a convergent sequence of interior pilot selectors, the exact squared main-row estimation error is the adaptive score variance divided by the main-row size. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hηlim,hsub,hN), [the adaptive Pilot Row conditional mean Square](goal).

Under the stated assumptions, the adaptive Pilot Row conditional mean Square. -/
lemma adaptivePilotRow_conditional_meanSquare
    (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (hηlim : Tendsto η atTop (nhds θ)) (hsub : PilotSublinear m)
    (n : ℕ) (hN : 0 < adaptiveMainSize m n) :
    (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
      adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v *
        (contrast (η n) + (adaptiveMainSize m n : ℝ)⁻¹ *
          (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
          contrast (adaptiveTrueParam θ h n)) ^ 2) =
      (adaptiveMainSize m n : ℝ)⁻¹ *
        adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε := by
  let M : RowModel (Fin 14) :=
    { N := adaptiveMainSize m
      w := adaptivePilotRowMass select θ h η p ε hselect hp hε
      f := adaptivePilotRowScore select θ h η p ε hselect hp hε
      B := 2 * pilotPhiUpper p ε
      v₀ := adaptivePilotLimitVariance select θ p ε hselect hp hθ hε
      mass_nonneg := adaptivePilotRowMass_nonneg select θ h η p ε hselect hp hθ hη hε
      mass_one := adaptivePilotRowMass_sum select θ h η p ε hselect hp hη hε
      centered := adaptivePilotRowScore_centered select θ h η p ε hselect hp hη hε
      bound := adaptivePilotRowScore_abs_le select θ h η p ε hselect hp hθ hη hε
      variance_tendsto := adaptivePilotRow_variance_tendsto
        select θ h η p ε hselect hp hθ hη hε hηlim
      variance_pos := adaptivePilotLimitVariance_pos select θ p ε hselect hp hθ hε
      length_tendsto := adaptiveMainSize_tendsto_atTop m hsub }
  have hsquare := M.expect_scoreSum_sq n
  have hNr : (adaptiveMainSize m n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  simp only [M, RowModel.expect, RowModel.mass, RowModel.scoreSum,
    RowModel.oneSecond] at hsquare
  simp_rw [adaptivePilotRow_estimatorError_eq select θ h η p ε m hselect hp hε n hN]
  calc
    _ = ((adaptiveMainSize m n : ℝ)⁻¹) ^ 2 *
        (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
          adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v *
            (∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = ((adaptiveMainSize m n : ℝ)⁻¹) ^ 2 *
        ((adaptiveMainSize m n : ℝ) *
          adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε) := by
      congr 1
      simpa [adaptivePilotRowProductMass,
        adaptivePilotRow_secondMoment_eq select θ h η p ε hselect hp hη hε n] using hsquare
    _ = _ := by field_simp

/-- The exact conditional mean-square error after root-`n` scaling. The finite-sample discrepancy from the selected-score variance is precisely the main-row fraction `n / (n - m n)`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hηlim,hsub,hN), [the adaptive Pilot Row conditional root N mean Square](goal).

Under the stated assumptions, the adaptive Pilot Row conditional root N mean Square. -/
lemma adaptivePilotRow_conditional_rootN_meanSquare
    (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (hηlim : Tendsto η atTop (nhds θ)) (hsub : PilotSublinear m)
    (n : ℕ) (hN : 0 < adaptiveMainSize m n) :
    (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
      adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v *
        (Real.sqrt (n : ℝ) *
          (contrast (η n) + (adaptiveMainSize m n : ℝ)⁻¹ *
            (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
            contrast (adaptiveTrueParam θ h n))) ^ 2) =
      (n : ℝ) / (adaptiveMainSize m n : ℝ) *
        adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε := by
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hrisk := adaptivePilotRow_conditional_meanSquare
    select θ h η p ε m hselect hp hθ hη hε hηlim hsub n hN
  have hNr : (adaptiveMainSize m n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  calc
    _ = (n : ℝ) *
        (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
          adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v *
            (contrast (η n) + (adaptiveMainSize m n : ℝ)⁻¹ *
              (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
              contrast (adaptiveTrueParam θ h n)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_pow, hsqrt]
      ring
    _ = (n : ℝ) * ((adaptiveMainSize m n : ℝ)⁻¹ *
        adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε) := by
      rw [hrisk]
    _ = _ := by
      field_simp

/-- Along every convergent sequence of interior pilot selectors, the exact conditional root-`n` risk value converges to the oracle variance. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hηlim,hsub), [the adaptive Pilot Row root N risk Value tendsto](goal).

Under the stated assumptions, the adaptive Pilot Row root N risk Value tendsto. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma adaptivePilotRow_rootN_riskValue_tendsto
    (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (m : ℕ → ℕ) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (hηlim : Tendsto η atTop (nhds θ)) (hsub : PilotSublinear m) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) / (adaptiveMainSize m n : ℝ) *
        adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε)
      atTop (nhds (Vstar θ p ε)) := by
  have hvar : Tendsto (fun n =>
      adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε)
      atTop (nhds (Vstar θ p ε)) := by
    have ht := adaptivePilotRow_variance_tendsto
      select θ h η p ε hselect hp hθ hη hε hηlim
    convert ht using 1
    · funext n
      rw [adaptivePilotRow_secondMoment_eq select θ h η p ε hselect hp hη hε n]
    · rfl
  exact adaptive_mainScale_mul_tendsto hsub hvar

/-- Averaging the exact conditional risk over every finite pilot prefix leaves only the prefix average of the selected-score variances. This is the exact finite-law risk decomposition, before any pilot-localization limit is used. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn), [the adaptive Pilot Prefix root N mean Square](goal).

Under the stated assumptions, the adaptive Pilot Prefix root N mean Square. -/
lemma adaptivePilotPrefix_rootN_meanSquare
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n) :
    (∑ u : Fin (m n) → Fin 4,
      (∏ j : Fin (m n), ∑ a : Fin 4,
        piTheta (adaptiveTrueParam θ h n) p a * rrPilotProbability ε a (u j)) *
        (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
          (∏ j, adaptiveMainMass select (adaptiveTrueParam θ h n)
            (pilotAdaptivePrefixTheta p ε m
              (Nat.le_of_lt (hsub.2 n hn).2) u) p ε (v j)) *
          (Real.sqrt (n : ℝ) *
            (contrast (pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u) +
              (adaptiveMainSize m n : ℝ)⁻¹ *
                (∑ j, adaptiveSelectedScore select
                  (pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u)
                  p ε (v j)) -
              contrast (adaptiveTrueParam θ h n))) ^ 2)) =
      ∑ u : Fin (m n) → Fin 4,
        (∏ j : Fin (m n), ∑ a : Fin 4,
          piTheta (adaptiveTrueParam θ h n) p a * rrPilotProbability ε a (u j)) *
          ((n : ℝ) / (adaptiveMainSize m n : ℝ) *
            adaptiveScoreVariance select (adaptiveTrueParam θ h n)
              (pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u) p ε) := by
  classical
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  have hN : 0 < adaptiveMainSize m n := by
    rw [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
    exact Nat.sub_pos_of_lt (hsub.2 n hn).2
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  let η₀ := pilotAdaptivePrefixTheta p ε m hmn u
  let η : ℕ → TrialParameter := fun k => if k = n then η₀ else θ
  have hη₀ : InteriorMeans η₀ := by
    exact pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))
  have hη : ∀ k, InteriorMeans (η k) := by
    intro k
    simp only [η]
    split_ifs <;> assumption
  have hηlim : Tendsto η atTop (nhds θ) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with k hk
    simp [η, ne_of_gt hk]
  have hrisk := adaptivePilotRow_conditional_rootN_meanSquare
    select θ h η p ε m hselect hp hθ hη hε hηlim hsub n hN
  simpa only [adaptivePilotRowProductMass, adaptivePilotRowMass, η, if_pos, η₀,
    hmn] using hrisk

end CausalSmith.Stat.LdpAteEfficiencySurface
