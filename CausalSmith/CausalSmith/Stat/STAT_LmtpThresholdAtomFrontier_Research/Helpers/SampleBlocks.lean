/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Causalean.Stat.Sample.PiTransport

/-!
# Finite-product transport to deterministic sample blocks

These build-inline bridges restrict the canonical finite product sample to an
arbitrary deterministic block, reindex that block by `Fin I.card`, and connect
the resulting coordinate sum to the range-indexed Causalean count API through
the canonical infinite-product sample. No ambient i.i.d. stream is assumed.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Membership in the observed clamp model supplies the canonical finite-product
sampling certificate at every horizon. Independence and marginal laws follow
from the product measure rather than from an ambient sample stream. The result uses [the `hP` condition](hyp:hP). [This is the stated conclusion](goal).
-/
lemma clampModel_iidSampling {J n : ℕ} {P : ClampLaw J}
    {beta kappa L cminus cplus pmin : ℝ}
    (hP : ClampModel P beta kappa L cminus cplus pmin) : IidSampling P n := by
  let _ : IsProbabilityMeasure P.dataMeasure := hP.probability
  refine ⟨hP.probability, hP.treatmentSupport, hP.outcomeSupport, ?_, ?_⟩
  · change iIndepFun (fun i z => z i) (Measure.pi fun _ : Fin n => P.dataMeasure)
    exact iIndepFun_pi
      (μ := fun _ : Fin n => P.dataMeasure)
      (X := fun _ : Fin n => id) (fun _ => measurable_id.aemeasurable)
  · intro i
    change (Measure.pi (fun _ : Fin n => P.dataMeasure)).map (fun z => z i) =
      P.dataMeasure
    exact (MeasureTheory.measurePreserving_eval
      (fun _ : Fin n => P.dataMeasure) i).map_eq

/-- Continuity-only model membership supplies the same canonical finite-product
sampling certificate. The result uses [the `hP` condition](hyp:hP). [This is the stated conclusion](goal).
-/
lemma contClampModel_iidSampling {J n : ℕ} {P : ClampLaw J}
    {kappa cminus cplus pmin deltaBar : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar) : IidSampling P n := by
  let _ : IsProbabilityMeasure P.dataMeasure := hP.probability
  refine ⟨hP.probability, hP.treatmentSupport, hP.outcomeSupport, ?_, ?_⟩
  · change iIndepFun (fun i z => z i) (Measure.pi fun _ : Fin n => P.dataMeasure)
    exact iIndepFun_pi
      (μ := fun _ : Fin n => P.dataMeasure)
      (X := fun _ : Fin n => id) (fun _ => measurable_id.aemeasurable)
  · intro i
    change (Measure.pi (fun _ : Fin n => P.dataMeasure)).map (fun z => z i) =
      P.dataMeasure
    exact (MeasureTheory.measurePreserving_eval
      (fun _ : Fin n => P.dataMeasure) i).map_eq

/-- After increasing-order reindexing, the tuple retained by a deterministic
block has the ordinary product law on `Fin I.card`. [This is the stated conclusion](goal).
-/
lemma block_reindexed_law_eq {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] {n : ℕ} (I : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => P)).map
        (fun z => fun j : Fin I.card => z ((I.orderIsoOfFin rfl) j).1) =
      Measure.pi (fun _ : Fin I.card => P) := by
  let e : Fin I.card ↪ Fin n :=
    ⟨fun j => ((I.orderIsoOfFin rfl) j).1,
      fun _ _ h => (I.orderIsoOfFin rfl).injective (Subtype.ext h)⟩
  have hindep : iIndepFun (fun j : Fin I.card => fun z : Fin n → X => z (e j))
      (Measure.pi fun _ : Fin n => P) := by
    exact (iIndepFun_pi
      (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => measurable_id.aemeasurable)).precomp e.injective
  have hmap := hindep.map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (e j)).aemeasurable)
  calc
    (Measure.pi (fun _ : Fin n => P)).map
        (fun z => fun j : Fin I.card => z ((I.orderIsoOfFin rfl) j).1) =
        Measure.pi (fun j : Fin I.card =>
          (Measure.pi (fun _ : Fin n => P)).map (fun z => z (e j))) := by
            simpa [e] using hmap
    _ = Measure.pi (fun _ : Fin I.card => P) := by
      congr 1
      funext j
      exact (MeasureTheory.measurePreserving_eval
        (fun _ : Fin n => P) (e j)).map_eq

/-- The law of a statistic summed over an arbitrary deterministic block is the
law of the same statistic summed over `Fin I.card` product coordinates. The result uses [the `hf` condition](hyp:hf). [This is the stated conclusion](goal).
-/
lemma block_count_law_eq {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] {n : ℕ} (I : Finset (Fin n))
    (f : X → ℝ) (hf : Measurable f) :
    (Measure.pi (fun _ : Fin n => P)).map
        (fun z => ∑ i ∈ I, f (z i)) =
      (Measure.pi (fun _ : Fin I.card => P)).map
        (fun z => ∑ j : Fin I.card, f (z j)) := by
  let restrictBlock : (Fin n → X) → (Fin I.card → X) :=
    fun z j => z ((I.orderIsoOfFin rfl) j).1
  let blockSum : (Fin I.card → X) → ℝ := fun z => ∑ j, f (z j)
  have hrestrict : Measurable restrictBlock := by
    exact measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hsum : Measurable blockSum := by
    exact Finset.measurable_fun_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hfun : (fun z : Fin n → X => ∑ i ∈ I, f (z i)) =
      blockSum ∘ restrictBlock := by
    funext z
    dsimp [blockSum, restrictBlock]
    rw [← Finset.sum_attach]
    exact (Equiv.sum_comp (I.orderIsoOfFin rfl).toEquiv
      (fun i : {i : Fin n // i ∈ I} => f (z i.1))).symm
  rw [hfun, ← MeasureTheory.Measure.map_map hsum hrestrict,
    block_reindexed_law_eq P I]

/-- A range-indexed count on the canonical infinite-product stream has the same
law as the corresponding sum on the finite product `Fin m → X`. The result uses [the `hf` condition](hyp:hf). [This is the stated conclusion](goal).
-/
lemma range_count_transport {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (m : ℕ)
    (f : X → ℝ) (hf : Measurable f) :
    (Measure.pi (fun _ : Fin m => P)).map
        (fun z => ∑ j : Fin m, f (z j)) =
      (Measure.infinitePi (fun _ : ℕ => P)).map
        (Causalean.Stat.Concentration.bernoulliCount
          (Causalean.Stat.iidSample_infinitePi P) f m) := by
  let S := Causalean.Stat.iidSample_infinitePi P
  let first : (ℕ → X) → (Fin m → X) := fun w j => S.Z j w
  let total : (Fin m → X) → ℝ := fun z => ∑ j, f (z j)
  have hfirst : Measurable first :=
    Causalean.Stat.iidSample_finN_measurable S m
  have htotal : Measurable total := by
    exact Finset.measurable_fun_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hfirstLaw :
      (Measure.infinitePi (fun _ : ℕ => P)).map first =
        Measure.pi (fun _ : Fin m => P) := by
    exact Causalean.Stat.iidSample_finN_pushforward S m
  have hcount :
      Causalean.Stat.Concentration.bernoulliCount S f m = total ∘ first := by
    funext w
    change (∑ i ∈ Finset.range m, f (S.Z i w)) =
      ∑ j : Fin m, f (S.Z j w)
    exact (Fin.sum_univ_eq_sum_range (fun i => f (S.Z i w)) m).symm
  rw [← hfirstLaw, MeasureTheory.Measure.map_map htotal hfirst, ← hcount]

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
