/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperTotal

/-! # Deterministic error event for the bias-aware interval -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

private lemma honest_weightedPolynomial_reproduce {ι : Type} [Fintype ι]
    {ell : ℕ} (I : Finset ι) (w a : ι → ℝ) (c : ℕ → ℝ)
    (delta h : ℝ) (hh : 0 < h)
    (hrepro : ∀ j : Fin (ell + 1),
      ∑ i ∈ I, w i * ((a i - delta) / h) ^ (j : ℕ) =
        if j = 0 then 1 else 0) :
    ∑ i ∈ I, w i *
      (∑ j ∈ Finset.range (ell + 1), c j * (a i - delta) ^ j) = c 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.range (ell + 1),
        ∑ i ∈ I, w i * (c j * (a i - delta) ^ j)) =
        ∑ j ∈ Finset.range (ell + 1), c j * h ^ j *
          (if j = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hre := hrepro ⟨j, Finset.mem_range.mp hj⟩
      have hre' : ∑ i ∈ I, w i * ((a i - delta) / h) ^ j =
          if j = 0 then 1 else 0 := by
        simpa [Fin.ext_iff] using hre
      rw [← hre', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_pow]
      field_simp [hh.ne']
    _ = c 0 := by simp

/-- The intermediate, realized-weight form of the Hölder bias bound.  This is
the form used by the honest interval, before replacing the realized `l1`
weight norm by its deterministic good-Gram upper bound. The result uses [the `hmodel` condition](hyp:hmodel), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
lemma localRegression_holderBias_le_empirical {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hbeta : 0 < beta) (hL : 0 < L)
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus)
    (hgood : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h) :
    |(∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus
        delta h i * clampRegressionExtension P ((z i).X, (z i).A)) -
      P.mu x delta| ≤
      L * h ^ beta * ∑ i ∈ B.I2,
        |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| := by
  classical
  let ell := ellOf beta
  let w : Fin n → ℝ := fun i =>
    interceptWeight B z x ell kappa cminus cplus delta h i
  let T : ℝ → ℝ := fun a => ∑ j ∈ Finset.range (ell + 1),
    (iteratedDerivWithin j (P.mu x) (Set.Icc (0 : ℝ) 1) delta /
      (Nat.factorial j : ℝ)) * (a - delta) ^ j
  have hdeltaI : delta ∈ Set.Icc (0 : ℝ) 1 := ⟨hdelta, by linarith⟩
  have hrepro := (goodGram_weight_controls B z x kappa cminus cplus delta h
    hh hlambda hgood).1
  have hpoly : ∑ i ∈ B.I2, w i * T (z i).A = P.mu x delta := by
    have hp := honest_weightedPolynomial_reproduce B.I2 w (fun i => (z i).A)
      (fun j => iteratedDerivWithin j (P.mu x) (Set.Icc (0 : ℝ) 1) delta /
        (Nat.factorial j : ℝ)) delta h hh hrepro
    simpa [T, ell, w] using hp
  have hrewrite :
      (∑ i ∈ B.I2, w i * clampRegressionExtension P ((z i).X, (z i).A)) -
          P.mu x delta =
        ∑ i ∈ B.I2, w i * (P.mu x (z i).A - T (z i).A) := by
    rw [← hpoly, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
    · have hu := ha.2
      have hAlo : delta ≤ (z i).A := by
        have hs := (div_nonneg_iff.mp hu.1).resolve_right
          (fun hn => (not_lt_of_ge hn.2 hh))
        exact sub_nonneg.mp hs.1
      have hAhi : (z i).A ≤ delta + h := by
        have hs := (div_le_iff₀ hh).mp hu.2
        linarith
      have hAI : (z i).A ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨hdelta.trans hAlo, hAhi.trans hupper⟩
      rw [show (z i).X = x from ha.1, clampRegressionExtension_eq P x hAI]
      simp only [w]
      ring
    · have hw0 : w i = 0 := by
        dsimp [w, ell]
        exact interceptWeight_eq_zero_of_inactive B z x (ellOf beta)
          kappa cminus cplus delta h i hgood (fun hi => ha ⟨hi.2.1, hi.2.2⟩)
      simp [hw0]
  rw [hrewrite]
  calc
    |∑ i ∈ B.I2, w i * (P.mu x (z i).A - T (z i).A)| ≤
        ∑ i ∈ B.I2, |w i| * |P.mu x (z i).A - T (z i).A| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul])
    _ ≤ ∑ i ∈ B.I2, |w i| * (L * h ^ beta) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hu := ha.2
        have hAlo : delta ≤ (z i).A := by
          have hs := (div_nonneg_iff.mp hu.1).resolve_right
            (fun hn => (not_lt_of_ge hn.2 hh))
          exact sub_nonneg.mp hs.1
        have hAhi : (z i).A ≤ delta + h := by
          have hs := (div_le_iff₀ hh).mp hu.2
          linarith
        have hAI : (z i).A ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hdelta.trans hAlo, hAhi.trans hupper⟩
        have hrem := (hmodel.holder x).2.2.2 delta hdeltaI (z i).A hAI
        have habs : |(z i).A - delta| ≤ h := by
          rw [abs_of_nonneg (sub_nonneg.mpr hAlo)]
          linarith
        have hpw := Real.rpow_le_rpow (abs_nonneg _) habs hbeta.le
        have hrem' : |P.mu x (z i).A - T (z i).A| ≤
            L * |(z i).A - delta| ^ beta := by
          simpa [T, ell, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrem
        exact hrem'.trans (mul_le_mul_of_nonneg_left hpw hL.le)
      · have hw0 : w i = 0 := by
          dsimp [w, ell]
          exact interceptWeight_eq_zero_of_inactive B z x (ellOf beta)
            kappa cminus cplus delta h i hgood (fun hi => ha ⟨hi.2.1, hi.2.2⟩)
        simp [hw0]
    _ = L * h ^ beta * ∑ i ∈ B.I2, |w i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Good-Gram local error decomposition retaining the empirical Hölder radius. The result uses [the `hmodel` condition](hyp:hmodel), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
lemma localRegression_good_error_le_empirical {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hbeta : 0 < beta) (hL : 0 < L)
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus)
    (hgood : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h) :
    |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
        P.mu x delta| ≤
      L * h ^ beta * ∑ i ∈ B.I2,
          |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
        |∑ i ∈ B.I2,
          interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
            ((z i).Y -
              clampRegressionExtension P ((z i).X, (z i).A))| := by
  have hmu := (hmodel.holder x).2.1 delta ⟨hdelta, by linarith⟩
  rw [localRegressionEstimate, if_pos hgood]
  change |clampUnit (∑ i ∈ B.I2,
      interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
        (z i).Y) - P.mu x delta| ≤ _
  refine (abs_clampUnit_sub_le _ _ hmu).trans ?_
  have hbias := localRegression_holderBias_le_empirical P hmodel hbeta hL B z x
    hdelta hh hupper hlambda hgood
  have htri := abs_add_le
      (∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
      ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A)))
    ((∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
      clampRegressionExtension P ((z i).X, (z i).A)) - P.mu x delta)
  have hid :
      (∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          (z i).Y) - P.mu x delta =
      (∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
        ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A))) +
      ((∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
        clampRegressionExtension P ((z i).X, (z i).A)) - P.mu x delta) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact htri.trans (by linarith)

/-- Retained-mean, atom-mass, and good-Gram local-regression deviations imply
that the total estimator lies within the displayed honest radius. The result uses [the `hmodel` condition](hyp:hmodel), [the `hdelta` condition](hyp:hdelta), [the `hdelta1` condition](hyp:hdelta1), [the `hh` condition](hyp:hh), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `htAlpha` condition](hyp:htAlpha), [the `hb0` condition](hyp:hb0), [the `hb1` condition](hyp:hb1), [the `hret` condition](hyp:hret), [the `hatom` condition](hyp:hatom), [the `hlocal` condition](hyp:hlocal). [This is the stated conclusion](goal).
-/
lemma totalGramEstimator_error_le_honestRadius
    {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h tAlpha b0 b1 : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hh : 0 < h)
    (hbeta : 0 ≤ beta) (hL : 0 ≤ L) (htAlpha : 0 ≤ tAlpha)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (hret : |retainedEstimate B z delta - retainedMean P delta| ≤ b0)
    (hatom : ∀ x : Fin J,
      |atomEstimate B z x delta - P.px x * atomMass P x delta| ≤ b1)
    (hlocal : ∀ x : Fin J,
      GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h →
      |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
          P.mu x delta| ≤
        L * h ^ beta * ∑ i ∈ B.I2,
            |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
          tAlpha * Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)) :
    |totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h -
        clampFunctional P delta| ≤
      b0 + ∑ x : Fin J,
        stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h
          tAlpha b1 := by
  let center := retainedEstimate B z delta + ∑ x : Fin J,
    atomEstimate B z x delta * localRegressionEstimate B z x (ellOf beta)
      kappa cminus cplus delta h
  have htarget := clampFunctional_mem_Icc P hmodel hdelta hdelta1
  have hclamp := abs_clampUnit_sub_le center (clampFunctional P delta) htarget
  have hbase : |totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h -
      clampFunctional P delta| ≤
      |retainedEstimate B z delta - retainedMean P delta| +
        ∑ x : Fin J, |atomEstimate B z x delta *
          localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
          P.px x * atomMass P x delta * P.mu x delta| := by
    calc
      _ ≤ |center - clampFunctional P delta| := by
        simpa [totalGramEstimator, center] using hclamp
      _ = |(retainedEstimate B z delta - retainedMean P delta) +
          ∑ x : Fin J, (atomEstimate B z x delta *
            localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
            P.px x * atomMass P x delta * P.mu x delta)| := by
        congr 1
        simp only [clampFunctional, Finset.sum_sub_distrib]
        ring
      _ ≤ |retainedEstimate B z delta - retainedMean P delta| +
          |∑ x : Fin J, (atomEstimate B z x delta *
            localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
            P.px x * atomMass P x delta * P.mu x delta)| := abs_add_le _ _
      _ ≤ _ := by
        simpa [add_comm] using add_le_add_left
          (Finset.abs_sum_le_sum_abs
            (fun x : Fin J => atomEstimate B z x delta *
              localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
              P.px x * atomMass P x delta * P.mu x delta) Finset.univ)
          |retainedEstimate B z delta - retainedMean P delta|
  refine hbase.trans (add_le_add hret ?_)
  apply Finset.sum_le_sum
  intro x hx
  let a := P.px x * atomMass P x delta
  let ah := atomEstimate B z x delta
  have haI := atomCoefficient_mem_Icc P hmodel x hdelta1
  have hahI := atomEstimate_mem_Icc B z x delta
  have ha0 : 0 ≤ a := by simpa [a] using haI.1
  have hah0 : 0 ≤ ah := by simpa [ah] using hahI.1
  have haUpper : a ≤ ah + b1 := by
    have habs := hatom x
    dsimp [a, ah] at habs ⊢
    rw [abs_le] at habs
    linarith
  by_cases hg : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h
  · rw [stratumRadius, if_pos hg]
    let R := L * h ^ beta * ∑ i ∈ B.I2,
          |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
        tAlpha * Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)
    have hR0 : 0 ≤ R := by
      dsimp [R]
      have hsumAbs : 0 ≤ ∑ i ∈ B.I2,
          |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hsumSq : 0 ≤ ∑ i ∈ B.I2,
          (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact add_nonneg
        (mul_nonneg (mul_nonneg hL (Real.rpow_nonneg hh.le _)) hsumAbs)
        (mul_nonneg htAlpha (Real.sqrt_nonneg _))
    have hmhatI := localRegressionEstimate_mem_Icc (ell := ellOf beta)
      B z x kappa cminus cplus delta h
    have hmuI := (hmodel.holder x).2.1 delta ⟨hdelta, hdelta1⟩
    have hprod : |ah * localRegressionEstimate B z x (ellOf beta) kappa
        cminus cplus delta h - a * P.mu x delta| ≤ b1 + (ah + b1) * R := by
      have hid : ah * localRegressionEstimate B z x (ellOf beta) kappa cminus
          cplus delta h - a * P.mu x delta =
          (ah - a) * localRegressionEstimate B z x (ellOf beta) kappa cminus
            cplus delta h + a * (localRegressionEstimate B z x (ellOf beta)
              kappa cminus cplus delta h - P.mu x delta) := by ring
      rw [hid]
      calc
        _ ≤ |ah - a| * |localRegressionEstimate B z x (ellOf beta) kappa
              cminus cplus delta h| +
            a * |localRegressionEstimate B z x (ellOf beta) kappa cminus
              cplus delta h - P.mu x delta| := by
          simpa [abs_mul, abs_of_nonneg ha0] using abs_add_le
            ((ah - a) * localRegressionEstimate B z x (ellOf beta) kappa
              cminus cplus delta h)
            (a * (localRegressionEstimate B z x (ellOf beta) kappa cminus
              cplus delta h - P.mu x delta))
        _ ≤ b1 + a * R := by
          apply add_le_add
          · exact mul_le_of_le_one_right (abs_nonneg _) (by
              rw [abs_of_nonneg hmhatI.1]
              exact hmhatI.2) |>.trans (hatom x)
          · exact mul_le_mul_of_nonneg_left (hlocal x hg) ha0
        _ ≤ b1 + (ah + b1) * R := by
          simpa [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_right haUpper hR0) b1
    simpa [a, ah, R, add_comm] using hprod
  · rw [stratumRadius, if_neg hg]
    have hlocalI := localRegressionEstimate_mem_Icc (ell := ellOf beta)
      B z x kappa cminus cplus delta h
    have hmuI := (hmodel.holder x).2.1 delta ⟨hdelta, hdelta1⟩
    have herr : |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus
        delta h - P.mu x delta| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hlocalI.1, hlocalI.2, hmuI.1, hmuI.2]
    let u := ah * localRegressionEstimate B z x (ellOf beta) kappa cminus
      cplus delta h
    let v := a * P.mu x delta
    have hu0 : 0 ≤ u := mul_nonneg hah0 hlocalI.1
    have hv0 : 0 ≤ v := mul_nonneg ha0 hmuI.1
    have huu : u ≤ ah := by dsimp [u]; nlinarith [hlocalI.2]
    have hvv : v ≤ a := by dsimp [v]; nlinarith [hmuI.2]
    have huv : |u - v| ≤ max ah a := by
      rw [abs_le]
      constructor
      · linarith [hu0, hvv, le_max_right ah a]
      · linarith [hv0, huu, le_max_left ah a]
    have hmax : max ah a ≤ ah + b1 := max_le (by linarith) haUpper
    simpa [u, v, a, ah] using huv.trans hmax

/-- The deterministic deviations used in the coverage proof put the target
inside the clipped bias-aware interval. The result uses [the `hmodel` condition](hyp:hmodel), [the `hdelta` condition](hyp:hdelta), [the `hdelta1` condition](hyp:hdelta1), [the `hh` condition](hyp:hh), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `htAlpha` condition](hyp:htAlpha), [the `hb0` condition](hyp:hb0), [the `hb1` condition](hyp:hb1), [the `htdef` condition](hyp:htdef), [the `hb0def` condition](hyp:hb0def), [the `hb1def` condition](hyp:hb1def), [the `hret` condition](hyp:hret), [the `hatom` condition](hyp:hatom), [the `hlocal` condition](hyp:hlocal). [This is the stated conclusion](goal).
-/
lemma clampFunctional_mem_honestInterval_of_deviations
    {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h alpha tAlpha b0 b1 : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hh : 0 < h)
    (hbeta : 0 ≤ beta) (hL : 0 ≤ L) (htAlpha : 0 ≤ tAlpha)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (B : SplitBlocks n) (z : Fin n → ClampObs J)
    (htdef : tAlpha = Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
    (hb0def : b0 = tAlpha / Real.sqrt (B.I0.card : ℝ))
    (hb1def : b1 = tAlpha / Real.sqrt (B.I1.card : ℝ))
    (hret : |retainedEstimate B z delta - retainedMean P delta| ≤ b0)
    (hatom : ∀ x : Fin J,
      |atomEstimate B z x delta - P.px x * atomMass P x delta| ≤ b1)
    (hlocal : ∀ x : Fin J,
      GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h →
      |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
          P.mu x delta| ≤
        L * h ^ beta * ∑ i ∈ B.I2,
            |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
          tAlpha * Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)) :
    clampFunctional P delta ∈
      honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha := by
  let radius := b0 + ∑ x : Fin J,
    stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h tAlpha b1
  have hdev := totalGramEstimator_error_le_honestRadius P hmodel hdelta hdelta1 hh
    hbeta hL htAlpha hb0 hb1 B z hret hatom hlocal
  have htI := clampFunctional_mem_Icc P hmodel hdelta hdelta1
  have hr0 : 0 ≤ radius := by
    dsimp [radius]
    apply add_nonneg hb0
    apply Finset.sum_nonneg
    intro x hx
    unfold stratumRadius atomEstimate blockAverage
    split_ifs <;> positivity
  simp only [honestInterval]
  rw [← htdef, ← hb0def, ← hb1def]
  change clampFunctional P delta ∈ Set.Icc
    (max 0 (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h - radius))
    (min 1 (totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h + radius))
  constructor
  · apply max_le htI.1
    dsimp [radius] at hdev ⊢
    rw [abs_le] at hdev
    linarith
  · apply le_min htI.2
    dsimp [radius] at hdev ⊢
    rw [abs_le] at hdev
    linarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
