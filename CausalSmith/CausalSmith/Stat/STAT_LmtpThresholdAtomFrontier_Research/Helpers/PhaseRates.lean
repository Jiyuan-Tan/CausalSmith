/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.THonestLength
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Pushforward

/-!
# Four-regime threshold phase diagram

The statement spells out every limiting regime and retains the almost-sure
zero-threshold reduction to the ordinary bounded-mean estimator.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology

noncomputable section

/-- Under the conditional-density model, the continuous treatment is strictly
positive almost surely; the boundary singleton has no mass in any stratum. The result uses [the `hmodel` condition](hyp:hmodel). [This is the stated conclusion](goal).
-/
-- @node: treatment_strictly_positive_ae
lemma treatment_strictly_positive_ae
    (J : ℕ) (P : ClampLaw J) (beta kappa L cminus cplus pmin : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    ∀ᵐ o ∂P.dataMeasure, 0 < o.A := by
  letI := hmodel.probability
  have hstratum_zero : ∀ x : Fin J,
      P.dataMeasure {o : ClampObs J | o.X = x ∧ o.A ∈ ({0} : Set ℝ)} = 0 := by
    intro x
    have hreal := (hmodel.condDensity.2.2 x).2 ({0} : Set ℝ) (measurableSet_singleton 0)
      (by
        intro a ha
        have : a = 0 := by simpa using ha
        subst a
        norm_num)
    rw [show (∫ a in ({0} : Set ℝ), P.pi x a) = 0 by simp, mul_zero,
      measureReal_def] at hreal
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hz | htop
    · exact hz
    · exact (measure_ne_top P.dataMeasure _ htop).elim
  have hA_zero : P.dataMeasure {o : ClampObs J | o.A = 0} = 0 := by
    rw [show {o : ClampObs J | o.A = 0} =
        ⋃ x : Fin J, {o : ClampObs J | o.X = x ∧ o.A ∈ ({0} : Set ℝ)} by
      ext o
      simp]
    exact measure_iUnion_null hstratum_zero
  have hne : ∀ᵐ o ∂P.dataMeasure, o.A ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hA_zero
  filter_upwards [hmodel.treatmentSupport, hne] with o ho hne
  exact lt_of_le_of_ne ho.1 (Ne.symm hne)

/-- At threshold zero the observed clamp functional is the ordinary outcome
mean, including the boundary point because the treatment law has no atom there. The result uses [the `hmodel` condition](hyp:hmodel). [This is the stated conclusion](goal).
-/
-- @node: zero_threshold_functional
lemma zero_threshold_functional
    (J : ℕ) (P : ClampLaw J) (beta kappa L cminus cplus pmin : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    clampFunctional P 0 = ∫ o, o.Y ∂P.dataMeasure := by
  have hretained : retainedMean P 0 = ∫ o, o.Y ∂P.dataMeasure := by
    apply integral_congr_ae
    filter_upwards [treatment_strictly_positive_ae J P beta kappa L cminus cplus pmin
      hmodel] with o ho
    simp [ho]
  simp [clampFunctional, hretained, atomMass]

/-- At threshold zero every empirical atom term vanishes almost surely, so the
total-Gram estimator is exactly the clamped block-zero outcome mean. The result uses [the `hmodel` condition](hyp:hmodel). [This is the stated conclusion](goal).
-/
-- @node: zero_threshold_totalGramEstimator
lemma zero_threshold_totalGramEstimator
    (J n : ℕ) (P : ClampLaw J) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    let h := infoBandwidth n 0 beta kappa deltaBar
    (fun z : Fin n → ClampObs J =>
      totalGramEstimator B z (ellOf beta) kappa cminus cplus 0 h) =ᵐ[iidProduct P n]
    (fun z => clampUnit (blockAverage B.I0 z (fun o => o.Y))) := by
  letI := hmodel.probability
  have hcoord : ∀ i : Fin n, ∀ᵐ z ∂iidProduct P n, 0 < (z i).A := by
    intro i
    have hmap : (iidProduct P n).map (Function.eval i) = P.dataMeasure := by
      simpa [iidProduct] using
        (Measure.pi_map_eval (fun _ : Fin n => P.dataMeasure) i)
    have hpos := treatment_strictly_positive_ae J P beta kappa L cminus cplus pmin
      hmodel
    rw [← hmap] at hpos
    have hAmeas : Measurable (fun o : ClampObs J => o.A) := by
      have ht : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) := by
        rw [measurable_iff_comap_le]
        rfl
      exact (measurable_fst.comp measurable_snd).comp ht
    exact (ae_map_iff (μ := iidProduct P n) (f := Function.eval i)
      (p := fun o : ClampObs J => 0 < o.A)
      (measurable_pi_apply i).aemeasurable
      (measurableSet_Ioi.preimage hAmeas)).mp hpos
  have hall : ∀ᵐ z ∂iidProduct P n, ∀ i : Fin n, 0 < (z i).A :=
    ae_all_iff.mpr hcoord
  dsimp
  filter_upwards [hall] with z hz
  have hatom : ∀ x : Fin J, atomEstimate B z x 0 = 0 := by
    intro x
    simp [atomEstimate, blockAverage, fun i => not_le_of_gt (hz i)]
  simp [totalGramEstimator, retainedEstimate, blockAverage, hatom, hz]

/-- At the identity threshold the density-created atom vanishes, and hence the
candidate frontier has exactly its root-sample-size summand. The result uses [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
-- @node: zero_threshold_atom_and_frontier
lemma zero_threshold_atom_and_frontier
    (J n : ℕ) (P : ClampLaw J) (beta kappa deltaBar : ℝ)
    (hkappa : 0 ≤ kappa) :
    (∀ x : Fin J, atomMass P x 0 = 0) ∧
      clampFrontier n 0 kappa (infoBandwidth n 0 beta kappa deltaBar) beta =
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  constructor
  · intro x
    simp [atomMass]
  · simp [clampFrontier, Real.zero_rpow (by linarith : kappa + 1 ≠ 0)]

/-- The critical threshold is asymptotically separated above the design-edge
scale under the declared exponent restrictions. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: critical_scale_div_edge_scale_tendsto_top
lemma critical_scale_div_edge_scale_tendsto_top
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    Tendsto (fun n => deltaCrit n beta kappa / deltaEdge n beta kappa)
      atTop atTop := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  let D : ℝ := beta * kappa + 2 * beta + kappa + 1
  let E : ℝ := 2 * beta + kappa + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  have hE : 0 < E := by
    dsimp [E]
    linarith
  have hgap : 0 < 1 / E - 1 / (2 * D) := by
    rw [sub_pos, div_lt_div_iff₀ (by positivity : 0 < (2 : ℝ) * D) hE]
    dsimp [D, E]
    nlinarith
  refine ((tendsto_rpow_atTop hgap).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  symm
  calc
    deltaCrit n beta kappa / deltaEdge n beta kappa =
        (n : ℝ) ^ (-1 / (2 * D)) / (n : ℝ) ^ (-1 / E) := by
          simp [deltaCrit, deltaEdge, D, E]
    _ = (n : ℝ) ^ ((-1 / (2 * D)) - (-1 / E)) :=
      (Real.rpow_sub hn' _ _).symm
    _ = (n : ℝ) ^ (1 / E - 1 / (2 * D)) := by
      congr 1
      ring

/-- At the design edge, the largest boundary-band atom term is negligible
relative to the root-sample-size scale. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
-- @node: edge_atom_scale_isLittleO_root
lemma edge_atom_scale_isLittleO_root
    (beta kappa : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa) :
    Tendsto (fun n =>
      (deltaEdge n beta kappa) ^ (beta + kappa + 1) /
        (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop (nhds 0) := by
  let E : ℝ := 2 * beta + kappa + 1
  let gap : ℝ := (beta + kappa + 1) / E - 1 / 2
  have hE : 0 < E := by dsimp [E]; linarith
  have hgap : 0 < gap := by
    dsimp [gap, E]
    rw [sub_pos, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hE]
    linarith
  refine ((tendsto_rpow_neg_atTop hgap).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  symm
  rw [deltaEdge, ← Real.rpow_mul hnR.le]
  rw [← Real.rpow_sub hnR]
  congr 1
  dsimp [gap, E]
  ring

/-- In the interior-bandwidth regime, the atom contribution has the exact
power-law form used to compare thresholds with the critical scale. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hbeta` condition](hyp:hbeta). [This is the stated conclusion](goal).
-/
-- @node: atom_interior_scale_exact
lemma atom_interior_scale_exact (n d beta kappa : ℝ) (hn : 0 < n) (hd : 0 < d)
    (hbeta : 0 < beta) :
    d ^ (kappa + 1) *
        ((n * d ^ kappa) ^ (-(1 : ℝ) / (2 * beta + 1))) ^ beta =
      n ^ (-beta / (2 * beta + 1)) *
        d ^ ((beta * kappa + 2 * beta + kappa + 1) /
          (2 * beta + 1)) := by
  have hp : 0 < 2 * beta + 1 := by linarith
  rw [← Real.rpow_mul (mul_nonneg hn.le (Real.rpow_nonneg hd.le kappa))]
  rw [Real.mul_rpow hn.le (Real.rpow_nonneg hd.le kappa)]
  rw [← Real.rpow_mul hd.le]
  calc
    _ = n ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) *
        (d ^ (kappa + 1) *
          d ^ (kappa * ((-(1 : ℝ) / (2 * beta + 1)) * beta))) := by ring
    _ = n ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) *
        d ^ ((kappa + 1) +
          kappa * ((-(1 : ℝ) / (2 * beta + 1)) * beta)) := by
      exact congrArg
        (fun t : ℝ => n ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) * t)
        (Real.rpow_add hd _ _).symm
    _ = n ^ (-beta / (2 * beta + 1)) *
        d ^ ((beta * kappa + 2 * beta + kappa + 1) /
          (2 * beta + 1)) := by
      congr 1 <;> field_simp <;> ring

/-- At the critical threshold, the interior-form atom contribution is exactly
the root-sample-size scale. The result uses [the `hn` condition](hyp:hn), [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
-- @node: critical_atom_interior_scale_exact
lemma critical_atom_interior_scale_exact
    (n : ℕ) (beta kappa : ℝ) (hn : 0 < n) (hbeta : 0 < beta)
    (hkappa : 0 ≤ kappa) :
    (deltaCrit n beta kappa) ^ (kappa + 1) *
        (((n : ℝ) * (deltaCrit n beta kappa) ^ kappa) ^
          (-(1 : ℝ) / (2 * beta + 1))) ^ beta =
      (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let D : ℝ := beta * kappa + 2 * beta + kappa + 1
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hp : 0 < 2 * beta + 1 := by linarith
  have hc : 0 < deltaCrit n beta kappa := Real.rpow_pos_of_pos hnR _
  rw [← Real.rpow_mul
    (mul_nonneg hnR.le (Real.rpow_nonneg hc.le kappa))]
  rw [Real.mul_rpow hnR.le (Real.rpow_nonneg hc.le kappa)]
  rw [← Real.rpow_mul hc.le]
  calc
    _ = (n : ℝ) ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) *
        ((deltaCrit n beta kappa) ^ (kappa + 1) *
          (deltaCrit n beta kappa) ^
            (kappa * ((-(1 : ℝ) / (2 * beta + 1)) * beta))) := by ring
    _ = (n : ℝ) ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) *
        (deltaCrit n beta kappa) ^
          ((kappa + 1) + kappa * ((-(1 : ℝ) / (2 * beta + 1)) * beta)) := by
      exact congrArg
        (fun t : ℝ =>
          (n : ℝ) ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) * t)
        (Real.rpow_add hc _ _).symm
    _ = (n : ℝ) ^ ((-(1 : ℝ) / (2 * beta + 1)) * beta) *
        (n : ℝ) ^ ((-(1 : ℝ) / (2 * D)) *
          ((kappa + 1) + kappa * ((-(1 : ℝ) / (2 * beta + 1)) * beta))) := by
      rw [deltaCrit, ← Real.rpow_mul hnR.le]
    _ = (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hnR]
      congr 1
      dsimp [D]
      field_simp
      ring

/-- The interior-form atom contribution, normalized by the root-sample-size
scale, is exactly a positive power of the threshold-to-critical-scale ratio. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
-- @node: atom_interior_div_root_exact
lemma atom_interior_div_root_exact
    (n : ℕ) (d beta kappa : ℝ) (hn : 0 < n) (hd : 0 < d)
    (hbeta : 0 < beta) (hkappa : 0 ≤ kappa) :
    (d ^ (kappa + 1) *
          (((n : ℝ) * d ^ kappa) ^ (-(1 : ℝ) / (2 * beta + 1))) ^ beta) /
        (n : ℝ) ^ (-(1 : ℝ) / 2) =
      (d / deltaCrit n beta kappa) ^
        ((beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let D : ℝ := beta * kappa + 2 * beta + kappa + 1
  let p : ℝ := 2 * beta + 1
  have hD : 0 < D := by dsimp [D]; nlinarith
  have hp : 0 < p := by dsimp [p]; linarith
  have hc : 0 < deltaCrit n beta kappa := Real.rpow_pos_of_pos hnR _
  rw [atom_interior_scale_exact (n : ℝ) d beta kappa hnR hd hbeta]
  have hleft :
      ((n : ℝ) ^ (-beta / p) * d ^ (D / p)) /
          (n : ℝ) ^ (-(1 : ℝ) / 2) =
        (n : ℝ) ^ (1 / (2 * p)) * d ^ (D / p) := by
    calc
      ((n : ℝ) ^ (-beta / p) * d ^ (D / p)) /
          (n : ℝ) ^ (-(1 : ℝ) / 2) =
          ((n : ℝ) ^ (-beta / p) /
            (n : ℝ) ^ (-(1 : ℝ) / 2)) * d ^ (D / p) := by ring
      _ = (n : ℝ) ^ ((-beta / p) - (-(1 : ℝ) / 2)) * d ^ (D / p) := by
        rw [Real.rpow_sub hnR]
      _ = (n : ℝ) ^ (1 / (2 * p)) * d ^ (D / p) := by
        congr 2
        dsimp [p]
        field_simp
        ring
  rw [show (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1) =
      D / p by rfl]
  rw [hleft]
  rw [Real.div_rpow hd.le hc.le]
  have hcrit : (deltaCrit n beta kappa) ^ (D / p) =
      (n : ℝ) ^ (-1 / (2 * p)) := by
    rw [deltaCrit, ← Real.rpow_mul hnR.le]
    congr 1
    dsimp [D, p]
    field_simp
  rw [hcrit]
  calc
    (n : ℝ) ^ (1 / (2 * p)) * d ^ (D / p) =
        d ^ (D / p) * (n : ℝ) ^ (1 / (2 * p)) := mul_comm _ _
    _ = d ^ (D / p) * ((n : ℝ) ^ (-1 / (2 * p)))⁻¹ := by
      congr 1
      rw [← Real.rpow_neg hnR.le]
      congr 1
      ring
    _ = d ^ (D / p) / (n : ℝ) ^ (-1 / (2 * p)) := by
      simp only [div_eq_mul_inv]

/-- If the threshold-to-critical-scale ratio converges to a positive constant,
the normalized interior atom contribution converges to the corresponding
positive power of that constant. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hc0` condition](hyp:hc0), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: atom_interior_normalized_tendsto_critical
lemma atom_interior_normalized_tendsto_critical
    (beta kappa c0 : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hc0 : 0 < c0) (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds c0)) :
    Tendsto (fun n =>
      ((deltaSeq n) ^ (kappa + 1) *
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta) /
        (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop
      (nhds (c0 ^ ((beta * kappa + 2 * beta + kappa + 1) /
        (2 * beta + 1)))) := by
  let a : ℝ := (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hpow := (Real.continuousAt_rpow_const c0 a (Or.inr ha.le)).tendsto.comp hratio
  refine hpow.congr' ?_
  have hratioPos : ∀ᶠ n in atTop,
      0 < deltaSeq n / deltaCrit n beta kappa :=
    hratio (Ioi_mem_nhds hc0)
  filter_upwards [eventually_gt_atTop 0, hratioPos] with n hn hnratio
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcrit : 0 < deltaCrit n beta kappa := Real.rpow_pos_of_pos hnR _
  have hdelta : 0 < deltaSeq n :=
    ((div_pos_iff.mp hnratio).resolve_right fun hneg =>
      (not_lt_of_ge hcrit.le) hneg.2).1
  symm
  exact atom_interior_div_root_exact n (deltaSeq n) beta kappa hn hdelta hbeta hkappa

/-- A positive finite limit for a ratio gives an eventual two-sided constant
sandwich of its numerator by its denominator. The result uses [the `hc` condition](hyp:hc), [the `hg` condition](hyp:hg), [the `hfg` condition](hyp:hfg). [This is the stated conclusion](goal).
-/
-- @node: asympSeq_of_tendsto_div_pos
lemma asympSeq_of_tendsto_div_pos (f g : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hfg : Tendsto (fun n => f n / g n) atTop (nhds c)) :
    AsympSeq f g := by
  refine ⟨c / 2, 2 * c, by linarith, by linarith, ?_⟩
  have hratio : ∀ᶠ n in atTop, f n / g n ∈ Set.Ioo (c / 2) (2 * c) :=
    hfg (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hg, hratio] with n hgn hn
  constructor
  · exact ((le_div_iff₀ hgn).mp hn.1.le)
  · exact ((div_le_iff₀ hgn).mp hn.2.le)

/-- In the critical regime, the exact interior-form atom term has
root-sample-size order. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hc0` condition](hyp:hc0), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: critical_interior_atom_asymp
lemma critical_interior_atom_asymp
    (beta kappa c0 : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hc0 : 0 < c0) (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds c0)) :
    AsympSeq (fun n =>
      (deltaSeq n) ^ (kappa + 1) *
        (((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-(1 : ℝ) / (2 * beta + 1))) ^ beta)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  let a : ℝ := (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlimit := atom_interior_normalized_tendsto_critical beta kappa c0 hbeta
    hkappa hc0 deltaSeq hratio
  have hpow : 0 < c0 ^ a := Real.rpow_pos_of_pos hc0 _
  apply asympSeq_of_tendsto_div_pos _ _ (c0 ^ a) hpow
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  · simpa [a] using hlimit

/-- If the threshold is asymptotically far above the critical scale, the
interior atom contribution dominates the root-sample-size term. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: atom_interior_normalized_tendsto_top
lemma atom_interior_normalized_tendsto_top
    (beta kappa : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop atTop) :
    Tendsto (fun n =>
      ((deltaSeq n) ^ (kappa + 1) *
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta) /
        (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop atTop := by
  let a : ℝ := (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hpow := (tendsto_rpow_atTop ha).comp hratio
  refine hpow.congr' ?_
  have hratioOne : ∀ᶠ n in atTop,
      1 ≤ deltaSeq n / deltaCrit n beta kappa :=
    (Filter.tendsto_atTop.1 hratio) 1
  filter_upwards [eventually_gt_atTop 0, hratioOne] with n hn hnratioOne
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcrit : 0 < deltaCrit n beta kappa := Real.rpow_pos_of_pos hnR _
  have hnratio : 0 < deltaSeq n / deltaCrit n beta kappa := by linarith
  have hdelta : 0 < deltaSeq n :=
    ((div_pos_iff.mp hnratio).resolve_right fun hneg =>
      (not_lt_of_ge hcrit.le) hneg.2).1
  symm
  exact atom_interior_div_root_exact n (deltaSeq n) beta kappa hn hdelta hbeta hkappa

/-- In the supercritical regime, the root-sample-size contribution is
eventually bounded by the exact interior-form atom contribution. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: supercritical_root_le_interior_atom
lemma supercritical_root_le_interior_atom
    (beta kappa : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
        (deltaSeq n) ^ (kappa + 1) *
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta := by
  have htop := atom_interior_normalized_tendsto_top beta kappa hbeta hkappa
    deltaSeq hratio
  have hratioOne : ∀ᶠ n in atTop, 1 ≤
      ((deltaSeq n) ^ (kappa + 1) *
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta) /
        (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    (Filter.tendsto_atTop.1 htop) 1
  filter_upwards [eventually_gt_atTop 0, hratioOne] with n hn hratioN
  have hroot : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  simpa using (le_div_iff₀ hroot).mp hratioN

/-- A threshold asymptotic to a positive multiple of the critical scale lies
asymptotically above the design-edge scale. The result uses [the `hreg` condition](hyp:hreg), [the `hc0` condition](hyp:hc0), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: critical_ratio_tendsto_edge_ratio_top
lemma critical_ratio_tendsto_edge_ratio_top
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha c0 : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hc0 : 0 < c0) (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds c0)) :
    Tendsto (fun n => deltaSeq n / deltaEdge n beta kappa) atTop atTop := by
  have hscale := critical_scale_div_edge_scale_tendsto_top J beta kappa L cminus
    cplus pmin deltaBar alpha hreg
  have hprod := Filter.Tendsto.pos_mul_atTop hc0 hratio hscale
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : deltaCrit n beta kappa ≠ 0 :=
    (Real.rpow_pos_of_pos hnR _).ne'
  have he : deltaEdge n beta kappa ≠ 0 :=
    (Real.rpow_pos_of_pos hnR _).ne'
  field_simp

/-- A threshold asymptotically larger than the critical scale also lies
asymptotically above the smaller design-edge scale. The result uses [the `hreg` condition](hyp:hreg), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: supercritical_ratio_tendsto_edge_ratio_top
lemma supercritical_ratio_tendsto_edge_ratio_top
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop atTop) :
    Tendsto (fun n => deltaSeq n / deltaEdge n beta kappa) atTop atTop := by
  have hscale := critical_scale_div_edge_scale_tendsto_top J beta kappa L cminus
    cplus pmin deltaBar alpha hreg
  have hprod := Filter.Tendsto.atTop_mul_atTop₀ hratio hscale
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : deltaCrit n beta kappa ≠ 0 :=
    (Real.rpow_pos_of_pos hnR _).ne'
  have he : deltaEdge n beta kappa ≠ 0 :=
    (Real.rpow_pos_of_pos hnR _).ne'
  field_simp

/-- A threshold converging to a positive fixed value is asymptotically above
the vanishing critical scale. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta0` condition](hyp:hdelta0), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: fixed_positive_threshold_ratio_critical_top
lemma fixed_positive_threshold_ratio_critical_top
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha delta0 : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hdelta0 : 0 < delta0) (deltaSeq : ℕ → ℝ)
    (hdelta : Tendsto deltaSeq atTop (nhds delta0)) :
    Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa) atTop atTop := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  let D : ℝ := beta * kappa + 2 * beta + kappa + 1
  have hD : 0 < D := by dsimp [D]; nlinarith
  have ha : 0 < 1 / (2 * D) := by positivity
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (2 * D))) atTop atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hprod := Filter.Tendsto.pos_mul_atTop hdelta0 hdelta hpow
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [deltaCrit]
  apply (eq_div_iff (Real.rpow_pos_of_pos hnR _).ne').2
  rw [mul_assoc, ← Real.rpow_add hnR]
  have hexp : 1 / (2 * D) +
      (-1 / (2 * (beta * kappa + 2 * beta + kappa + 1))) = 0 := by
    dsimp [D]
    ring
  rw [hexp]
  simp

/-- At the identity threshold, the concrete stabilized estimator inherits the
root-sample-size risk sandwich from the minimax theorem. The result uses [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
-- @node: zero_threshold_stabilizedWorstRisk_asymp
lemma zero_threshold_stabilizedWorstRisk_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha) :
    ∀ Bseq : ∀ n, SplitBlocks n,
      AsympSeq
        (fun n => stabilizedWorstRisk J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar 0)
        (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin, hpminJ,
      hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  rcases clamp_minimax_risk J beta kappa L cminus cplus pmin deltaBar alpha hreg' with
    ⟨c, C, amplitude, hc, hcC, hamp, hamp_le, hrisk⟩
  have hzero : ThresholdSequence deltaBar (fun _ => 0) := by
    intro n
    exact ⟨le_rfl, hdeltaBar_pos.le⟩
  intro Bseq
  refine ⟨c, C, hc, hcC.le, ?_⟩
  filter_upwards [hrisk (fun _ => 0) hzero Bseq] with n hn
  dsimp at hn
  have hfront :
      clampFrontier n 0 kappa (infoBandwidth n 0 beta kappa deltaBar) beta =
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    simp [clampFrontier, Real.zero_rpow (by linarith : kappa + 1 ≠ 0)]
  rw [hfront] at hn
  exact ⟨hn.1.trans hn.2.1, hn.2.2.1⟩

/-- Adding a nonnegative reference term preserves an asymptotic comparison
when the other summand already has that reference order. The result uses [the `hfg` condition](hyp:hfg), [the `hg` condition](hyp:hg). [This is the stated conclusion](goal).
-/
-- @node: asymp_add_reference_left
lemma asymp_add_reference_left (f g : ℕ → ℝ)
    (hfg : AsympSeq f g) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    AsympSeq (fun n => g n + f n) g := by
  rcases hfg with ⟨c, C, hc, hcC, hfg⟩
  refine ⟨c, C + 1, hc, by linarith, ?_⟩
  filter_upwards [hfg, hg] with n hn hgn
  constructor
  · linarith [hn.1]
  · nlinarith [hn.2]

/-- If a nonnegative summand is eventually no larger than a sequence already
of the target order, adding it preserves that asymptotic order. The result uses [the `hfs` condition](hyp:hfs), [the `hg` condition](hyp:hg). [This is the stated conclusion](goal).
-/
-- @node: asymp_add_eventually_le_left
lemma asymp_add_eventually_le_left (f g s : ℕ → ℝ)
    (hfs : AsympSeq f s) (hg : ∀ᶠ n in atTop, 0 ≤ g n ∧ g n ≤ f n) :
    AsympSeq (fun n => g n + f n) s := by
  rcases hfs with ⟨c, C, hc, hcC, hfs⟩
  refine ⟨c, 2 * C, hc, by linarith, ?_⟩
  filter_upwards [hfs, hg] with n hn hgn
  constructor
  · linarith [hn.1, hgn.1]
  · nlinarith [hn.2, hgn.2]

/-- Raising eventually nonnegative comparable sequences to a fixed positive
real power preserves their asymptotic comparison. The result uses [the `ha` condition](hyp:ha), [the `hfg` condition](hyp:hfg), [the `hf` condition](hyp:hf), [the `hg` condition](hyp:hg). [This is the stated conclusion](goal).
-/
-- @node: asympSeq_rpow
lemma asympSeq_rpow (f g : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hfg : AsympSeq f g) (hf : ∀ᶠ n in atTop, 0 ≤ f n)
    (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    AsympSeq (fun n => (f n) ^ a) (fun n => (g n) ^ a) := by
  rcases hfg with ⟨c, C, hc, hcC, hfg⟩
  refine ⟨c ^ a, C ^ a, Real.rpow_pos_of_pos hc _,
    Real.rpow_le_rpow hc.le hcC ha.le, ?_⟩
  filter_upwards [hfg, hf, hg] with n hn hfn hgn
  constructor
  · rw [← Real.mul_rpow hc.le hgn]
    exact Real.rpow_le_rpow (mul_nonneg hc.le hgn) hn.1 ha.le
  · rw [← Real.mul_rpow (hc.le.trans hcC) hgn]
    exact Real.rpow_le_rpow hfn hn.2 ha.le

/-- Multiplication by a common eventually nonnegative factor preserves an
asymptotic comparison. The result uses [the `hfg` condition](hyp:hfg), [the `hq` condition](hyp:hq). [This is the stated conclusion](goal).
-/
-- @node: asympSeq_mul_nonnegative_left
lemma asympSeq_mul_nonnegative_left (q f g : ℕ → ℝ)
    (hfg : AsympSeq f g) (hq : ∀ᶠ n in atTop, 0 ≤ q n) :
    AsympSeq (fun n => q n * f n) (fun n => q n * g n) := by
  rcases hfg with ⟨c, C, hc, hcC, hfg⟩
  refine ⟨c, C, hc, hcC, ?_⟩
  filter_upwards [hfg, hq] with n hn hqn
  constructor
  · calc
      c * (q n * g n) = q n * (c * g n) := by ring
      _ ≤ q n * f n := mul_le_mul_of_nonneg_left hn.1 hqn
  · calc
      q n * f n ≤ q n * (C * g n) :=
        mul_le_mul_of_nonneg_left hn.2 hqn
      _ = C * (q n * g n) := by ring

/-- Asymptotic comparison is transitive. The result uses [the `hfg` condition](hyp:hfg), [the `hgs` condition](hyp:hgs). [This is the stated conclusion](goal).
-/
-- @node: asympSeq_trans
lemma asympSeq_trans {f g s : ℕ → ℝ} (hfg : AsympSeq f g)
    (hgs : AsympSeq g s) : AsympSeq f s := by
  rcases hfg with ⟨c₁, C₁, hc₁, hcC₁, hfg⟩
  rcases hgs with ⟨c₂, C₂, hc₂, hcC₂, hgs⟩
  refine ⟨c₁ * c₂, C₁ * C₂, mul_pos hc₁ hc₂, ?_, ?_⟩
  · exact mul_le_mul hcC₁ hcC₂ hc₂.le (hc₁.le.trans hcC₁)
  · filter_upwards [hfg, hgs] with n hn hns
    constructor
    · calc
        (c₁ * c₂) * s n = c₁ * (c₂ * s n) := by ring
        _ ≤ c₁ * g n := mul_le_mul_of_nonneg_left hns.1 hc₁.le
        _ ≤ f n := hn.1
    · calc
        f n ≤ C₁ * g n := hn.2
        _ ≤ C₁ * (C₂ * s n) :=
          mul_le_mul_of_nonneg_left hns.2 (hc₁.le.trans hcC₁)
        _ = (C₁ * C₂) * s n := by ring

/-- In the above-edge regime, replacing the implicit information bandwidth by
its interior closed form preserves the order of the atom contribution. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hfar` condition](hyp:hfar). [This is the stated conclusion](goal).
-/
-- @node: atomSeq_asymp_interior_of_edge_ratio_top
lemma atomSeq_asymp_interior_of_edge_ratio_top
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hfar : Tendsto (fun n => deltaSeq n / deltaEdge n beta kappa)
      atTop atTop) :
    AsympSeq
      (fun n => (deltaSeq n) ^ (kappa + 1) *
        (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta)
      (fun n => (deltaSeq n) ^ (kappa + 1) *
        (((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-(1 : ℝ) / (2 * beta + 1))) ^ beta) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin, hpminJ,
      hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hbw := infoBandwidth_interior_asymp J beta kappa L cminus cplus pmin
    deltaBar alpha hreg' deltaSeq hdelta hfar
  apply asympSeq_mul_nonnegative_left
  · apply asympSeq_rpow _ _ beta hbeta hbw
    · exact (infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
        ⟨hdeltaBar_pos, hdeltaBar_lt⟩ deltaSeq hdelta).mono
        (fun _ hn => hn.1.le)
    · exact Filter.Eventually.of_forall fun n => Real.rpow_nonneg
        (mul_nonneg (Nat.cast_nonneg n)
          (Real.rpow_nonneg (hdelta n).1 kappa)) _
  · exact Filter.Eventually.of_forall fun n =>
      Real.rpow_nonneg (hdelta n).1 (kappa + 1)

/-- At a positive finite critical ratio, the actual implicit-bandwidth atom
term and the resulting frontier both have root-sample-size order. The result uses [the `hreg` condition](hyp:hreg), [the `hc0` condition](hyp:hc0), [the `hdelta` condition](hyp:hdelta), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: critical_atom_and_frontier_asymp
lemma critical_atom_and_frontier_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha c0 : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hc0 : 0 < c0) (deltaSeq : ℕ → ℝ)
    (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds c0)) :
    let atomSeq := fun n => (deltaSeq n) ^ (kappa + 1) *
      (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta
    let rSeq := fun n => clampFrontier n (deltaSeq n) kappa
      (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta
    AsympSeq atomSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
      AsympSeq rSeq (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin, hpminJ,
      hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hedge := critical_ratio_tendsto_edge_ratio_top J beta kappa L cminus
    cplus pmin deltaBar alpha c0 hreg' hc0 deltaSeq hratio
  have hactual := atomSeq_asymp_interior_of_edge_ratio_top J beta kappa L cminus
    cplus pmin deltaBar alpha hreg' deltaSeq hdelta hedge
  have hinterior := critical_interior_atom_asymp beta kappa c0 hbeta hkappa
    hc0 deltaSeq hratio
  have hatom := asympSeq_trans hactual hinterior
  dsimp
  refine ⟨hatom, ?_⟩
  simpa [clampFrontier] using asymp_add_reference_left _ _ hatom
    (Filter.Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- At a positive finite critical ratio, adding the regular root term to the
interior-form atom term preserves root-sample-size order. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hc0` condition](hyp:hc0), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: critical_interior_frontier_asymp
lemma critical_interior_frontier_asymp
    (beta kappa c0 : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hc0 : 0 < c0) (deltaSeq : ℕ → ℝ)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds c0)) :
    AsympSeq (fun n =>
      (n : ℝ) ^ (-(1 : ℝ) / 2) +
        (deltaSeq n) ^ (kappa + 1) *
          (((n : ℝ) * (deltaSeq n) ^ kappa) ^
            (-(1 : ℝ) / (2 * beta + 1))) ^ beta)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  apply asymp_add_reference_left
  · exact critical_interior_atom_asymp beta kappa c0 hbeta hkappa hc0
      deltaSeq hratio
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).le

/-- In the supercritical moving-threshold regime, the actual implicit-bandwidth
frontier is comparable to the interior atom scale, since that scale dominates
the root-sample-size summand. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: supercritical_frontier_asymp
lemma supercritical_frontier_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop atTop) :
    AsympSeq
      (fun n => clampFrontier n (deltaSeq n) kappa
        (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta)
      (fun n => (deltaSeq n) ^ (kappa + 1) *
        ((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-beta / (2 * beta + 1))) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hreg' : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin, hpminJ,
      hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  let interior : ℕ → ℝ := fun n =>
    (deltaSeq n) ^ (kappa + 1) *
      (((n : ℝ) * (deltaSeq n) ^ kappa) ^
        (-(1 : ℝ) / (2 * beta + 1))) ^ beta
  let atom : ℕ → ℝ := fun n =>
    (deltaSeq n) ^ (kappa + 1) *
      (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta
  have hedge := supercritical_ratio_tendsto_edge_ratio_top J beta kappa L cminus
    cplus pmin deltaBar alpha hreg' deltaSeq hratio
  have ha := atomSeq_asymp_interior_of_edge_ratio_top J beta kappa L cminus
    cplus pmin deltaBar alpha hreg' deltaSeq hdelta hedge
  have hroot := supercritical_root_le_interior_atom beta kappa hbeta hkappa
    deltaSeq hratio
  rcases ha with ⟨c, C, hc, hcC, ha⟩
  refine ⟨c, C + 1, hc, by linarith, ?_⟩
  have hratioOne : ∀ᶠ n in atTop,
      1 ≤ deltaSeq n / deltaCrit n beta kappa :=
    (Filter.tendsto_atTop.1 hratio) 1
  filter_upwards [ha, hroot, eventually_gt_atTop 0, hratioOne] with n han hr hn hrat
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcrit : 0 < deltaCrit n beta kappa := Real.rpow_pos_of_pos hnR _
  have hd : 0 < deltaSeq n := by
    have : 0 < deltaSeq n / deltaCrit n beta kappa := by linarith
    rcases div_pos_iff.mp this with h | h
    · exact h.1
    · exact (not_lt_of_ge hcrit.le h.2).elim
  have hinterior_nonneg : 0 ≤ interior n := by
    dsimp [interior]
    exact mul_nonneg (Real.rpow_nonneg hd.le _)
      (Real.rpow_nonneg
        (Real.rpow_nonneg
          (mul_nonneg hnR.le (Real.rpow_nonneg hd.le kappa)) _ ) beta)
  have hatom_nonneg : 0 ≤ atom n := by
    exact (mul_nonneg hc.le hinterior_nonneg).trans han.1
  have htarget : interior n =
      (deltaSeq n) ^ (kappa + 1) *
        ((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-beta / (2 * beta + 1)) := by
    dsimp [interior]
    rw [← Real.rpow_mul
      (mul_nonneg hnR.le (Real.rpow_nonneg hd.le kappa))]
    congr 2
    ring
  rw [← htarget]
  change c * interior n ≤
      (n : ℝ) ^ (-(1 : ℝ) / 2) + atom n ∧
    (n : ℝ) ^ (-(1 : ℝ) / 2) + atom n ≤ (C + 1) * interior n
  constructor
  · exact han.1.trans (le_add_of_nonneg_left
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · calc
      (n : ℝ) ^ (-(1 : ℝ) / 2) + atom n ≤ interior n + C * interior n :=
        add_le_add hr han.2
      _ = (C + 1) * interior n := by ring
/-- Below the critical scale, the actual implicit-bandwidth frontier has
root-sample-size order. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hratio` condition](hyp:hratio). [This is the stated conclusion](goal).
-/
-- @node: regular_frontier_asymp
lemma regular_frontier_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hratio : Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa)
      atTop (nhds 0)) :
    AsympSeq (fun n => clampFrontier n (deltaSeq n) kappa
        (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hbalance := infoBandwidth_eventually_balance beta kappa deltaBar hbeta
    hkappa ⟨hdeltaBar_pos, hdeltaBar_lt⟩ deltaSeq hdelta
  have hsmall : ∀ᶠ n in atTop, deltaSeq n / deltaCrit n beta kappa < 1 :=
    hratio (Iio_mem_nhds (by norm_num))
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hbalance, hsmall, eventually_gt_atTop 0] with n hb hs hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
  have hatom : (deltaSeq n) ^ (kappa + 1) *
      (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta ≤
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rcases eq_or_lt_of_le (hdelta n).1 with hd | hd
    · simp [← hd, Real.zero_rpow (by linarith : kappa + 1 ≠ 0), hroot.le]
    · let w := ((n : ℝ) * (deltaSeq n) ^ kappa) ^
          (-(1 : ℝ) / (2 * beta + 1))
      have hbw : infoBandwidth n (deltaSeq n) beta kappa deltaBar ≤ w := by
        exact balance_root_le_interior_scale (n : ℝ) (deltaSeq n)
          (infoBandwidth n (deltaSeq n) beta kappa deltaBar)
          (2 * beta + 1) kappa hnR hd hb.1 (by linarith) hkappa
          (by simpa [w] using hb.2.2)
      have hatomInterior : (deltaSeq n) ^ (kappa + 1) *
          (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta ≤
          (deltaSeq n) ^ (kappa + 1) * w ^ beta := by gcongr; exact hb.1.le
      have hratioNonneg : 0 ≤ deltaSeq n / deltaCrit n beta kappa :=
        div_nonneg hd.le (Real.rpow_pos_of_pos hnR _).le
      have hpow : (deltaSeq n / deltaCrit n beta kappa) ^
          ((beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1)) ≤ 1 := by
        simpa using Real.rpow_le_rpow hratioNonneg hs.le (show 0 ≤
          (beta * kappa + 2 * beta + kappa + 1) / (2 * beta + 1) by positivity)
      have hinterior : (deltaSeq n) ^ (kappa + 1) * w ^ beta ≤
          (n : ℝ) ^ (-(1 : ℝ) / 2) := by
        apply (div_le_one hroot).mp
        rw [atom_interior_div_root_exact n (deltaSeq n) beta kappa hn hd hbeta hkappa]
        exact hpow
      exact hatomInterior.trans hinterior
  simp only [clampFrontier]
  have hatom_nonneg : 0 ≤ (deltaSeq n) ^ (kappa + 1) *
      (infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ beta :=
    mul_nonneg (Real.rpow_nonneg (hdelta n).1 _) (Real.rpow_nonneg hb.1.le _)
  constructor <;> nlinarith
end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
