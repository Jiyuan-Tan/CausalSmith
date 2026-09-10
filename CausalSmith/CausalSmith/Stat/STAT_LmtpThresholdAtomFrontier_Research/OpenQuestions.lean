/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.TPhaseDiagram

/-!
# Open question: sharp confidence-length constant

The declaration is a never-proved proposition, not a theorem. It asks for one
sharp constant over every threshold regime and attainment by intervals whose
radius is built from the realized-design exact-modulus handle.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set Topology

noncomputable section

/-- Worst-case integrated exact-modulus radius over the model and strata. -/
def worstExactModulus (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin deltaBar delta alpha : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (P : ClampLaw J) (x : Fin J),
    ∃ hmodel : ClampModel P beta kappa L cminus cplus pmin,
    ∃ hh : 0 < infoBandwidth n delta beta kappa deltaBar,
    v = exactModulusHandle P B x (ellOf beta) beta kappa L cminus cplus pmin delta
      (infoBandwidth n delta beta kappa deltaBar)
      (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)) hh
      (Real.sqrt_nonneg _) hmodel}

/-- Worst conditional exact modulus on the realized design. -/
def worstRealizedExactModulus (J n : ℕ) (B : SplitBlocks n)
    (beta kappa L _cminus _cplus deltaBar delta alpha : ℝ)
    (z : Fin n → ClampObs J) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin J,
    ∃ hh : 0 < infoBandwidth n delta beta kappa deltaBar,
    v = realizedExactModulus B z x (ellOf beta) beta L delta
      (infoBandwidth n delta beta kappa deltaBar)
      (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
      (Real.sqrt_nonneg _)}

/-- Conditional-modulus interval centered at the realized total-Gram estimate. -/
def exactModulusInterval (B : SplitBlocks n)
    (beta kappa L cminus cplus _pmin deltaBar delta alpha : ℝ) :
    ConfidenceProcedure n J :=
  fun z =>
    let center := totalGramEstimator B z (ellOf beta) kappa cminus cplus delta
      (infoBandwidth n delta beta kappa deltaBar)
    let radius := worstRealizedExactModulus J n B beta kappa L cminus cplus
      deltaBar delta alpha z
    Set.Icc (max 0 (center - radius)) (min 1 (center + radius))

/-- The threshold sequence approaches one of the finite or infinite phase
regimes; oscillating sequences with no ratio limit are intentionally excluded. -/
def HasThresholdRegimeLimit (deltaSeq : ℕ → ℝ) (beta kappa : ℝ) : Prop :=
  (∃ q : ℝ, 0 ≤ q ∧ Tendsto
      (fun n => deltaSeq n / deltaCrit n beta kappa) atTop (nhds q)) ∨
  Tendsto (fun n => deltaSeq n / deltaCrit n beta kappa) atTop atTop

/-- The conditional modulus interval matches both the integrated realized
modulus and the minimax length of the least-favorable mixed regular-plus-local
experiment. -/
def LeastFavorableMixedExperimentMatch (J : ℕ)
    (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (deltaSeq : ℕ → ℝ) (Bseq : ∀ n, SplitBlocks n) : Prop :=
  (∃ D amplitude : ℝ, 0 < D ∧ 0 < amplitude ∧ amplitude ≤ 1 / 4 ∧
    ∃ P0 Preg Ploc : ℕ → ClampLaw J,
      (∀ᶠ n in atTop,
        ClampModel (P0 n) beta kappa L cminus cplus pmin ∧
        ClampModel (Preg n) beta kappa L cminus cplus pmin ∧
        ClampModel (Ploc n) beta kappa L cminus cplus pmin ∧
        IidSampling (P0 n) n ∧ IidSampling (Preg n) n ∧ IidSampling (Ploc n) n ∧
        GlobalBernoulliShift (P0 n) (Preg n)
          ((n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        LocalizedBernoulliPerturbation (P0 n) (Ploc n) beta (deltaSeq n)
          (infoBandwidth n (deltaSeq n) beta kappa deltaBar) amplitude ∧
        productChiSq (Preg n) (P0 n) n ≤ D ∧
        productChiSq (Ploc n) (P0 n) n ≤ D) ∧
      Tendsto (fun n =>
          (|clampFunctional (Preg n) (deltaSeq n) -
              clampFunctional (P0 n) (deltaSeq n)| +
            |clampFunctional (Ploc n) (deltaSeq n) -
              clampFunctional (P0 n) (deltaSeq n)|) /
            (2 * worstExactModulus J n (Bseq n) beta kappa L cminus cplus pmin
              deltaBar (deltaSeq n) alpha))
        atTop (nhds 1)) ∧
  Tendsto (fun n =>
      confidenceWorstLength J n beta kappa L cminus cplus pmin
          (exactModulusInterval (Bseq n) beta kappa L cminus cplus pmin
            deltaBar (deltaSeq n) alpha) /
        ENNReal.ofReal (2 * worstExactModulus J n (Bseq n) beta kappa L cminus cplus
          pmin deltaBar (deltaSeq n) alpha))
    atTop (nhds 1) ∧
  Tendsto (fun n =>
      ENNReal.ofReal (2 * worstExactModulus J n (Bseq n) beta kappa L cminus cplus pmin
          deltaBar (deltaSeq n) alpha) /
        observedMinimaxLength J n beta kappa L cminus cplus pmin
          (deltaSeq n) alpha)
    atTop (nhds 1)

/-- Does a realized-design exact-modulus interval attain one sharp asymptotic
constant for `L_n^star / r_n` across regular, critical, atom-dominated, and
fixed-threshold limits while retaining the stated model class? -/
-- @node: oeq:sharp-constant
def SharpConfidenceLengthConstantQuestion : Prop :=
  ∀ (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ),
    RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha →
    ∃ c : ℝ, 0 < c ∧
      ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
        HasThresholdRegimeLimit deltaSeq beta kappa →
        Tendsto (fun n =>
          observedMinimaxLength J n beta kappa L cminus cplus pmin
              (deltaSeq n) alpha /
            ENNReal.ofReal (clampFrontier n (deltaSeq n) kappa
              (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta))
          atTop (nhds (ENNReal.ofReal c)) ∧
        ∃ Bseq : ∀ n, SplitBlocks n,
          (∀ᶠ n in atTop,
            ∀ P : ClampLaw J,
              ClampModel P beta kappa L cminus cplus pmin →
                1 - alpha ≤ (iidProduct P n).real {z |
                  clampFunctional P (deltaSeq n) ∈
                    exactModulusInterval (Bseq n) beta kappa L cminus cplus pmin
                      deltaBar (deltaSeq n) alpha z}) ∧
          Tendsto (fun n =>
            confidenceWorstLength J n beta kappa L cminus cplus pmin
                (exactModulusInterval (Bseq n) beta kappa L cminus cplus pmin
                  deltaBar (deltaSeq n) alpha) /
              ENNReal.ofReal (clampFrontier n (deltaSeq n) kappa
                (infoBandwidth n (deltaSeq n) beta kappa deltaBar) beta))
            atTop (nhds (ENNReal.ofReal c)) ∧
          LeastFavorableMixedExperimentMatch J beta kappa L cminus cplus pmin
            deltaBar alpha deltaSeq Bseq

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
