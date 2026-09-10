import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TriangularArray
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.RegularBenchmark
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FixedWaldLocalization
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.SetGeometry
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TFiniteSampleProjectionCoverage
import Causalean.Stat.Minimax.TotalVariation
import Causalean.PO.ID.Partial.RandomSet.Hausdorff
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option linter.style.longLine false

/-! Impossibility of uniform studentized Wald adaptation, together with the attainable
concentration-projection coverage half. -/

open MeasureTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

private theorem liminf_le_liminf_of_le_add_vanishing
    (u v err : ℕ → ℝ)
    (hu0 : ∀ n, 0 ≤ u n)
    (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n ≤ 1)
    (he0 : ∀ n, 0 ≤ err n) (he1 : ∀ n, err n ≤ 1)
    (huv : ∀ n, u n ≤ v n + err n)
    (herr : Filter.Tendsto err Filter.atTop (nhds 0)) :
    Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop := by
  have hu_lower : Filter.atTop.IsBoundedUnder (· ≥ ·) u :=
    Filter.isBoundedUnder_of ⟨0, hu0⟩
  have hv_lower : Filter.atTop.IsBoundedUnder (· ≥ ·) v :=
    Filter.isBoundedUnder_of ⟨0, hv0⟩
  have hv_upper : Filter.atTop.IsBoundedUnder (· ≤ ·) v :=
    Filter.isBoundedUnder_of ⟨1, hv1⟩
  have he_lower : Filter.atTop.IsBoundedUnder (· ≥ ·) err :=
    Filter.isBoundedUnder_of ⟨0, he0⟩
  have he_upper : Filter.atTop.IsBoundedUnder (· ≤ ·) err :=
    Filter.isBoundedUnder_of ⟨1, he1⟩
  have hsum_cobounded : Filter.atTop.IsCoboundedUnder (· ≥ ·) (v + err) :=
    Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 2) fun n => by
      simp only [Pi.add_apply]
      linarith [hv1 n, he1 n]
  calc
    Filter.liminf u Filter.atTop ≤ Filter.liminf (v + err) Filter.atTop :=
      Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun n => by simpa using huv n)
        hu_lower hsum_cobounded
    _ = Filter.liminf (err + v) Filter.atTop := by
      congr 1
      ext n
      exact add_comm _ _
    _ ≤ Filter.limsup err Filter.atTop + Filter.liminf v Filter.atTop :=
      liminf_add_le he_lower he_upper hv_lower
        hv_upper.isCoboundedUnder_ge
    _ = Filter.liminf v Filter.atTop := by rw [herr.limsup_eq]; simp

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
  [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass E] [MeasurableSingletonClass W]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

/-- [The model, treatment, outcome, rank index, allocation fraction, source sample size, target sample size, row index, row-size certificate, nominal level, sample point](hyp:_Mdl,x,y,r0,p,ns,nt,n,hn,alpha,omega) determine [the studentized rank-truncated Wald confidence interval computed from one two-sample observation](goal). -/
noncomputable def waldSet
    (_Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y)
    (r0 : RankIndex E W) (p : Set.Ioo (0 : ℝ) 1)
    (ns nt : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) (alpha : Set.Ioo (0 : ℝ) 1)
    (omega : Omega E W X Y (ns n) (nt n)) : Set ℝ :=
  regularWaldInterval
    (regularWaldEstimator r0 (finEmpProxyMoment (ns n) x omega)
      (finEmpOutcomeMoment (ns n) x y omega) (finEmpTargetProxy (nt n) omega))
    (regularWaldVariance r0 p (finEmpObservedLaw (ns n) omega) x y
      (finEmpTargetProxy (nt n) omega)) n hn alpha
-- @realizes I^W_{n,1-\alpha}(row Wald benchmark)

-- @node: thm:no-uniform-studentized-wald-adaptation
/-- Given [the admissible allocation condition](hyp:halloc), [no studentized fixed-rank Wald rule can both localize at the regular baseline and attain uniform asymptotic coverage over the unrestricted changing-rank array class](goal). -/
theorem no_uniform_studentized_wald_adaptation
    (p alpha : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p) :
    ∃ (M0 : LatentShiftSCM (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 2))
      (A : TwoSampleArray (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 2) ns nt),
      M0 ∈ stronglyIdentifiedSubmodelSet
        (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) (1 / 4) (1 / 16) p 0 1 ∧
      A ∈ studentizedArrayClassSet p (0 : Fin 1) ns nt ∧
      interventionalProb M0 0 1 = 1 / 2 ∧
      (∀ n, 2 ≤ n → rowInterventionalProb A n 0 1 = 5 / 8) ∧
      Filter.Tendsto
        (fun n => Causalean.Stat.tvDist (A.rowLaw n) (constRowLaw M0 ns nt n))
        Filter.atTop (nhds 0) ∧
      ∀ C : ConfidenceSetSeq (Fin 2) (Fin 2) (Fin 1) (Fin 2) ns nt,
        UniformArrayCoverage (U := Fin 2) C p (0 : Fin 1) (1 : Fin 2) alpha →
        ∀ eps : Set.Ioo (0 : ℝ) (1 / 8),
          1 - (alpha : ℝ) ≤ Filter.liminf
            (fun n => (constRowLaw M0 ns nt n).real {omega |
              if hn : 2 ≤ n then
                (waldSet M0 0 1 (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                    p ns nt n hn alpha omega).Nonempty ∧
                  1 / 8 - (eps : ℝ) ≤
                    Causalean.PartialID.RandomSet.hausdorffDist (C.set n omega)
                      (waldSet M0 0 1 (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                        p ns nt n hn alpha omega)
              else True}) Filter.atTop := by
  refine ⟨studentizedBaseline, studentizedWeakArray ns nt,
    studentizedBaseline_stronglyIdentified p,
    studentizedWeakArray_mem p ns nt halloc,
    studentizedBaseline_interventional,
    studentizedWeakArray_interventional ns nt, ?_, ?_⟩
  · simpa [constRowLaw] using
      studentizedWeakArray_rowLaw_tendsto_tv_zero p ns nt halloc
  · intro C hCov eps
    let ArrayClass := studentizedArrayClassSet
      (E := Fin 2) (U := Fin 2) (W := Fin 2) (Y := Fin 2)
      p (0 : Fin 1) ns nt
    let Aw : ArrayClass := ⟨studentizedWeakArray ns nt,
      studentizedWeakArray_mem p ns nt halloc⟩
    let rowInf : ℕ → ℝ := fun n => Causalean.Stat.coverageInfOrOne
      (fun A : ArrayClass => (A.1.rowLaw n).real {omega |
        rowInterventionalProb A.1 n 0 1 ∈ C.set n omega})
    let weakCover : ℕ → ℝ := fun n =>
      ((studentizedWeakArray ns nt).rowLaw n).real {omega |
        rowInterventionalProb (studentizedWeakArray ns nt) n 0 1 ∈ C.set n omega}
    let weakProb : ℕ → ℝ := fun n =>
      ((studentizedWeakArray ns nt).rowLaw n).real {omega | (5 / 8 : ℝ) ∈ C.set n omega}
    let baseProb : ℕ → ℝ := fun n =>
      (constRowLaw studentizedBaseline ns nt n).real {omega | (5 / 8 : ℝ) ∈ C.set n omega}
    let tv : ℕ → ℝ := fun n => Causalean.Stat.tvDist
      ((studentizedWeakArray ns nt).rowLaw n)
      (constRowLaw studentizedBaseline ns nt n)
    let good : ∀ n, Omega (Fin 2) (Fin 2) (Fin 1) (Fin 2) (ns n) (nt n) → Prop :=
      fun n omega => if hn : 2 ≤ n then
        (waldSet studentizedBaseline 0 1
          (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p ns nt n hn alpha omega).Nonempty ∧
        ∀ t ∈ waldSet studentizedBaseline 0 1
          (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p ns nt n hn alpha omega,
          |t - 1 / 2| < eps
      else True
    let badProb : ℕ → ℝ := fun n =>
      (constRowLaw studentizedBaseline ns nt n).real {omega | ¬ good n omega}
    let desired : ∀ n, Omega (Fin 2) (Fin 2) (Fin 1) (Fin 2) (ns n) (nt n) → Prop :=
      fun n omega => if hn : 2 ≤ n then
        (waldSet studentizedBaseline 0 1
          (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p ns nt n hn alpha omega).Nonempty ∧
        1 / 8 - (eps : ℝ) ≤
          Causalean.PartialID.RandomSet.hausdorffDist (C.set n omega)
            (waldSet studentizedBaseline 0 1
              (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
              p ns nt n hn alpha omega)
      else True
    let desiredProb : ℕ → ℝ := fun n =>
      (constRowLaw studentizedBaseline ns nt n).real {omega | desired n omega}
    letI : Nonempty ArrayClass := ⟨Aw⟩
    have weak_isProbability (n : ℕ) :
        IsProbabilityMeasure ((studentizedWeakArray ns nt).rowLaw n) := by
      change IsProbabilityMeasure
        (twoSampleLaw (studentizedWeakModel n) (ns n) (nt n))
      infer_instance
    have base_isProbability (n : ℕ) :
        IsProbabilityMeasure (constRowLaw studentizedBaseline ns nt n) := by
      change IsProbabilityMeasure
        (twoSampleLaw studentizedBaseline (ns n) (nt n))
      infer_instance
    have hrow_le (n : ℕ) : rowInf n ≤ weakCover n := by
      dsimp only [rowInf]
      rw [Causalean.Stat.coverageInfOrOne_of_nonempty]
      exact ciInf_le (show BddBelow (Set.range fun A : ArrayClass =>
        (A.1.rowLaw n).real {omega |
          rowInterventionalProb A.1 n 0 1 ∈ C.set n omega}) from ⟨0, by
            rintro _ ⟨A, rfl⟩
            exact measureReal_nonneg⟩) Aw
    have hrow0 (n : ℕ) : 0 ≤ rowInf n := by
      dsimp only [rowInf]
      rw [Causalean.Stat.coverageInfOrOne_of_nonempty]
      exact le_ciInf fun A => measureReal_nonneg
    have hweakCover1 (n : ℕ) : weakCover n ≤ 1 := by
      letI := weak_isProbability n
      exact measureReal_le_one
    have hCovRow : 1 - (alpha : ℝ) ≤ Filter.liminf rowInf Filter.atTop := by
      simpa [UniformArrayCoverage, rowInf, ArrayClass] using hCov
    have hCovWeakCover :
        1 - (alpha : ℝ) ≤ Filter.liminf weakCover Filter.atTop := by
      refine hCovRow.trans (Filter.liminf_le_liminf
        (Filter.Eventually.of_forall hrow_le)
        (Filter.isBoundedUnder_of ⟨0, hrow0⟩) ?_)
      exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1) hweakCover1
    have hweak_eq : Filter.liminf weakCover Filter.atTop =
        Filter.liminf weakProb Filter.atTop := by
      apply Filter.liminf_congr
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      simp [weakCover, weakProb, studentizedWeakArray_interventional ns nt n hn]
    have hCovWeak : 1 - (alpha : ℝ) ≤ Filter.liminf weakProb Filter.atTop := by
      rw [← hweak_eq]
      exact hCovWeakCover
    have htv : Filter.Tendsto tv Filter.atTop (nhds 0) := by
      simpa [tv, constRowLaw] using
        studentizedWeakArray_rowLaw_tendsto_tv_zero p ns nt halloc
    have hweak_base (n : ℕ) : weakProb n ≤ baseProb n + tv n := by
      letI := weak_isProbability n
      letI := base_isProbability n
      have hgap := Causalean.Stat.measureReal_sub_le_tvDist
        (μ := constRowLaw studentizedBaseline ns nt n)
        (ν := (studentizedWeakArray ns nt).rowLaw n)
        (confidenceSetSeq_measurableSet C n (5 / 8 : ℝ))
      dsimp only [weakProb, baseProb, tv]
      rw [Causalean.Stat.tvDist_symm] at hgap
      linarith
    have hweakProb0 (n : ℕ) : 0 ≤ weakProb n := measureReal_nonneg
    have hweakProb1 (n : ℕ) : weakProb n ≤ 1 := by
      letI := weak_isProbability n
      exact measureReal_le_one
    have hbaseProb0 (n : ℕ) : 0 ≤ baseProb n := measureReal_nonneg
    have hbaseProb1 (n : ℕ) : baseProb n ≤ 1 := by
      letI := base_isProbability n
      exact measureReal_le_one
    have htv0 (n : ℕ) : 0 ≤ tv n := by
      letI := weak_isProbability n
      letI := base_isProbability n
      exact Causalean.Stat.tvDist_nonneg
    have htv1 (n : ℕ) : tv n ≤ 1 := by
      letI := weak_isProbability n
      letI := base_isProbability n
      exact Causalean.Stat.tvDist_le_one
    have hCovBase : 1 - (alpha : ℝ) ≤ Filter.liminf baseProb Filter.atTop :=
      hCovWeak.trans (liminf_le_liminf_of_le_add_vanishing weakProb baseProb tv
        hweakProb0 hbaseProb0 hbaseProb1 htv0 htv1 hweak_base htv)
    have hbad : Filter.Tendsto badProb Filter.atTop (nhds 0) := by
      let epsHalf : Set.Ioo (0 : ℝ) (1 / 2) :=
        ⟨(eps : ℝ), eps.2.1,
          eps.2.2.trans (by norm_num : (1 / 8 : ℝ) < 1 / 2)⟩
      simpa [badProb, good, constRowLaw, waldSet] using
        studentizedBaseline_waldLocalization_bad_tendsto_zero
          p alpha ns nt halloc epsHalf
    have hbase_desired (n : ℕ) : baseProb n ≤ desiredProb n + badProb n := by
      letI := base_isProbability n
      calc
        baseProb n ≤ (constRowLaw studentizedBaseline ns nt n).real
            ({omega | desired n omega} ∪ {omega | ¬ good n omega}) := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro omega hcover
          by_cases hn : 2 ≤ n
          · by_cases hg : good n omega
            · left
              change desired n omega
              simp only [desired, dif_pos hn]
              have hg' := hg
              simp only [good, dif_pos hn] at hg'
              refine ⟨hg'.1, ?_⟩
              have hCbounded : Bornology.IsBounded (C.set n omega) :=
                (Metric.isBounded_Icc (0 : ℝ) 1).subset (C.sub_unit n omega)
              have hinf : 1 / 8 - (eps : ℝ) ≤ Metric.infDist (5 / 8 : ℝ)
                  (waldSet studentizedBaseline 0 1
                    (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                    p ns nt n hn alpha omega) := by
                rw [Metric.le_infDist hg'.1]
                intro t ht
                rw [Real.dist_eq]
                have hrev := abs_sub_abs_le_abs_sub
                  ((5 / 8 : ℝ) - 1 / 2) (t - 1 / 2)
                have htclose := hg'.2 t ht
                norm_num at hrev
                have heq : (1 / 8 : ℝ) - (t - 1 / 2) = 5 / 8 - t := by ring
                rw [heq] at hrev
                linarith
              exact hinf.trans (infDist_le_randomSet_hausdorffDist_of_mem
                hCbounded hcover)
            · right
              exact hg
          · left
            change desired n omega
            simp [desired, hn]
        _ ≤ desiredProb n + badProb n := measureReal_union_le _ _
    have hdesired0 (n : ℕ) : 0 ≤ desiredProb n := measureReal_nonneg
    have hdesired1 (n : ℕ) : desiredProb n ≤ 1 := by
      letI := base_isProbability n
      exact measureReal_le_one
    have hbad0 (n : ℕ) : 0 ≤ badProb n := measureReal_nonneg
    have hbad1 (n : ℕ) : badProb n ≤ 1 := by
      letI := base_isProbability n
      exact measureReal_le_one
    have hDesired : 1 - (alpha : ℝ) ≤ Filter.liminf desiredProb Filter.atTop :=
      hCovBase.trans (liminf_le_liminf_of_le_add_vanishing baseProb desiredProb badProb
        hbaseProb0 hdesired0 hdesired1 hbad0 hbad1
        hbase_desired hbad)
    simpa [desiredProb, desired, constRowLaw] using hDesired

/-- Given [the admissible allocation condition](hyp:halloc), [the concentration projection set retains uniform row-wise coverage over the unrestricted changing-rank array class](goal). -/
-- keep: delivers the source's separately advertised attainable uniform-coverage half on changing-rank arrays
theorem uniform_coverage_of_concentration_projection
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (p alpha : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p) (x : X) (y : Y) :
    1 - (alpha : ℝ) ≤ Filter.liminf
      (fun n => Causalean.Stat.coverageInfOrOne
        (fun A : studentizedArrayClassSet (E := E) (U := U) (W := W) (Y := Y)
            p x ns nt =>
          (A.1.rowLaw n).real {omega |
            rowInterventionalProb A.1 n x y ∈
              concentrationProjectionSet (rowEmpProxyMoment A.1 x n omega)
                (rowEmpOutcomeMoment A.1 x y n omega) (rowEmpTargetProxy A.1 n omega)
                (ns n) (nt n) alpha})) Filter.atTop := by
  let rowCoverage : ℕ → ℝ := fun n => Causalean.Stat.coverageInfOrOne
    (fun A : studentizedArrayClassSet (E := E) (U := U) (W := W) (Y := Y)
        p x ns nt =>
      (A.1.rowLaw n).real {omega |
        rowInterventionalProb A.1 n x y ∈
          concentrationProjectionSet (rowEmpProxyMoment A.1 x n omega)
            (rowEmpOutcomeMoment A.1 x y n omega) (rowEmpTargetProxy A.1 n omega)
            (ns n) (nt n) alpha})
  have hrow_lower : ∀ n, 2 ≤ n → 1 - (alpha : ℝ) ≤ rowCoverage n := by
    intro n hn
    classical
    let ArrayClass := studentizedArrayClassSet (E := E) (U := U) (W := W) (Y := Y)
      p x ns nt
    by_cases hne : Nonempty ArrayClass
    · letI : Nonempty ArrayClass := hne
      dsimp only [rowCoverage]
      rw [Causalean.Stat.coverageInfOrOne_of_nonempty]
      apply le_ciInf
      intro A
      have hA := A.2
      have hcls : PositiveLatentShiftClass (A.1.Mn n) := A.1.rows_positive n hn
      have hsizes := halloc.2.2.1 n hn
      rw [(hA.source_iid n hn).1]
      simpa [rowCoverage, rowInterventionalProb, rowEmpProxyMoment,
        rowEmpOutcomeMoment, rowEmpTargetProxy] using
        finite_sample_projection_coverage_twoSampleLaw
          (A.1.Mn n) (observedLaw (A.1.Mn n)) (targetProxyVector (A.1.Mn n))
          hcls ⟨hcls, rfl, rfl⟩ x y
          (hA.target_span n hn) (ns n) (nt n) hsizes.1 hsizes.2.1 alpha
    · letI : IsEmpty ArrayClass := not_nonempty_iff.mp hne
      dsimp only [rowCoverage]
      rw [Causalean.Stat.coverageInfOrOne_of_isEmpty]
      exact sub_le_self 1 alpha.2.1.le
  have hrow_upper : ∀ n, 2 ≤ n → rowCoverage n ≤ 1 := by
    intro n hn
    classical
    let ArrayClass := studentizedArrayClassSet (E := E) (U := U) (W := W) (Y := Y)
      p x ns nt
    by_cases hne : Nonempty ArrayClass
    · letI : Nonempty ArrayClass := hne
      dsimp only [rowCoverage]
      rw [Causalean.Stat.coverageInfOrOne_of_nonempty]
      obtain ⟨A⟩ := hne
      exact (ciInf_le (show BddBelow (Set.range fun A : ArrayClass =>
        (A.1.rowLaw n).real {omega |
          rowInterventionalProb A.1 n x y ∈
            concentrationProjectionSet (rowEmpProxyMoment A.1 x n omega)
              (rowEmpOutcomeMoment A.1 x y n omega) (rowEmpTargetProxy A.1 n omega)
              (ns n) (nt n) alpha}) from ⟨0, by
                rintro _ ⟨A, rfl⟩
                exact measureReal_nonneg⟩) A).trans (by
                  rw [(A.2.source_iid n hn).1]
                  exact measureReal_le_one)
    · letI : IsEmpty ArrayClass := not_nonempty_iff.mp hne
      dsimp only [rowCoverage]
      rw [Causalean.Stat.coverageInfOrOne_of_isEmpty]
  change 1 - (alpha : ℝ) ≤ Filter.liminf rowCoverage Filter.atTop
  apply Filter.le_liminf_of_le
  · change ∃ b, ∀ a, (∀ᶠ n in Filter.atTop, a ≤ rowCoverage n) → a ≤ b
    exact ⟨1, fun a ha => by
      obtain ⟨n, han, hn⟩ := (ha.and (Filter.eventually_ge_atTop 2)).exists
      exact han.trans (hrow_upper n hn)⟩
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact hrow_lower n hn

end CausalSmith.SCM.ProxyTargetspanTransport
