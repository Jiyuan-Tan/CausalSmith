import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelSpectralConstruction

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

/-! A concrete metric on finite-dimensional summary coordinates and comparison with `dS`. -/

-- @node: summaryMetric_toCoordinates_injective
lemma SummarySpace.toCoordinates_injective {dx dz : ℕ} :
    Function.Injective (@SummarySpace.toCoordinates dx dz) := by
  intro p q h
  cases p
  cases q
  simp only [SummarySpace.toCoordinates] at h
  simp_all

-- @node: summaryMetric_coordinates
abbrev SummaryMetricCoordinates (dx dz : ℕ) :=
  EuclideanSpace ℝ (Fin dz × Fin dx) × EuclideanSpace ℝ (Fin dz × Fin dx) ×
    EuclideanSpace ℝ (Fin dz × Fin dx) × EuclideanSpace ℝ (Fin dz × Fin dx) × Euc dx

-- @node: summaryMetric_toMetricCoordinates
noncomputable def SummarySpace.toMetricCoordinates {dx dz : ℕ} (s : SummarySpace dx dz) :
    SummaryMetricCoordinates dx dz :=
  (WithLp.toLp 2 (fun ij => s.M0 ij.1 ij.2),
    WithLp.toLp 2 (fun ij => s.M1 ij.1 ij.2),
    WithLp.toLp 2 (fun ij => s.N0 ij.1 ij.2),
    WithLp.toLp 2 (fun ij => s.N1 ij.1 ij.2), WithLp.toLp 2 s.mX)

-- @node: summaryMetric_toMetricCoordinates_injective
lemma SummarySpace.toMetricCoordinates_injective {dx dz : ℕ} :
    Function.Injective (@SummarySpace.toMetricCoordinates dx dz) := by
  intro p q h
  cases p
  cases q
  simp only [SummarySpace.toMetricCoordinates, Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  congr
  · funext i j
    exact congrFun (congrArg WithLp.ofLp h0) (i, j)
  · funext i j
    exact congrFun (congrArg WithLp.ofLp h1) (i, j)
  · funext i j
    exact congrFun (congrArg WithLp.ofLp h2) (i, j)
  · funext i j
    exact congrFun (congrArg WithLp.ofLp h3) (i, j)
  · exact congrArg WithLp.ofLp h4

-- @node: summaryMetric_fromMetricCoordinates
noncomputable def fromMetricCoordinates {dx dz : ℕ} (c : SummaryMetricCoordinates dx dz) :
    SummaryCoordinates dx dz :=
  ((fun i j => c.1.ofLp (i, j)), (fun i j => c.2.1.ofLp (i, j)),
    (fun i j => c.2.2.1.ofLp (i, j)), (fun i j => c.2.2.2.1.ofLp (i, j)),
    c.2.2.2.2.ofLp)

-- @node: summaryMetric_toMetricCoordinates_continuous
lemma SummarySpace.toMetricCoordinates_continuous {dx dz : ℕ} :
    Continuous (@SummarySpace.toMetricCoordinates dx dz) := by
  unfold SummarySpace.toMetricCoordinates
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  have hM0 : Continuous (fun s : SummarySpace dx dz => s.M0) :=
    continuous_fst.comp hcoord
  have hM1 : Continuous (fun s : SummarySpace dx dz => s.M1) :=
    (continuous_fst.comp continuous_snd).comp hcoord
  have hN0 : Continuous (fun s : SummarySpace dx dz => s.N0) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hcoord
  have hN1 : Continuous (fun s : SummarySpace dx dz => s.N1) :=
    (continuous_fst.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord
  have hmX : Continuous (fun s : SummarySpace dx dz => s.mX) :=
    (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord
  fun_prop

-- @node: summaryMetric_fromMetricCoordinates_continuous
lemma fromMetricCoordinates_continuous {dx dz : ℕ} :
    Continuous (@fromMetricCoordinates dx dz) := by
  unfold fromMetricCoordinates
  fun_prop

-- @node: summaryMetric_from_toMetricCoordinates
lemma from_toMetricCoordinates {dx dz : ℕ} (s : SummarySpace dx dz) :
    fromMetricCoordinates s.toMetricCoordinates = s.toCoordinates := by
  rfl

-- @node: summaryMetric_metricSpace
noncomputable instance summaryMetricSpace {dx dz : ℕ} : MetricSpace (SummarySpace dx dz) :=
  let m := MetricSpace.induced SummarySpace.toMetricCoordinates
    SummarySpace.toMetricCoordinates_injective inferInstance
  m.replaceTopology (by
    change TopologicalSpace.induced SummarySpace.toCoordinates inferInstance =
      TopologicalSpace.induced SummarySpace.toMetricCoordinates inferInstance
    apply le_antisymm
    · exact continuous_iff_le_induced.mp SummarySpace.toMetricCoordinates_continuous
    · apply continuous_iff_le_induced.mp
      have hc : @Continuous (SummarySpace dx dz) (SummaryCoordinates dx dz)
          (TopologicalSpace.induced SummarySpace.toMetricCoordinates inferInstance)
          inferInstance SummarySpace.toCoordinates := by
        have hind : @Continuous (SummarySpace dx dz) (SummaryMetricCoordinates dx dz)
            (TopologicalSpace.induced SummarySpace.toMetricCoordinates inferInstance)
            inferInstance SummarySpace.toMetricCoordinates := continuous_induced_dom
        have hcomp : @Continuous (SummarySpace dx dz) (SummaryCoordinates dx dz)
            (TopologicalSpace.induced SummarySpace.toMetricCoordinates inferInstance)
            instTopologicalSpaceProd
            (fromMetricCoordinates ∘ SummarySpace.toMetricCoordinates) :=
          @Continuous.comp (SummarySpace dx dz) (SummaryMetricCoordinates dx dz)
            (SummaryCoordinates dx dz)
            (TopologicalSpace.induced SummarySpace.toMetricCoordinates inferInstance)
            inferInstance instTopologicalSpaceProd _ _
            fromMetricCoordinates_continuous hind
        convert hcomp using 1
        funext s
        exact from_toMetricCoordinates s
      exact hc)

-- @node: summaryMetric_dS_self
@[simp] lemma dS_self {dx dz : ℕ} (p : SummarySpace dx dz) : dS p p = 0 := by
  unfold dS
  have hz : matrixCLM (0 : RectMatrix dz dx) = 0 := by
    ext x i
    simp [matrixCLM, Matrix.toEuclideanLin_apply]
  simp [hz]

-- @node: summaryMetric_dS_le_dist
lemma dS_le_dist_mul {dx dz : ℕ} (p q : SummarySpace dx dz) :
    dS p q ≤ (4 * entryNormConstant dz dx + dx) * dist p q := by
  have hcomp0 : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx =>
      (p.M0 - q.M0) ij.1 ij.2)‖ ≤ dist p q := by
    have hproj : dist p.toMetricCoordinates.1 q.toMetricCoordinates.1 ≤
        dist p.toMetricCoordinates q.toMetricCoordinates := by simp [Prod.dist_eq]
    calc
      _ = dist p.toMetricCoordinates.1 q.toMetricCoordinates.1 := by
        rw [dist_eq_norm]
        congr 1
      _ ≤ dist p q := hproj
  have hcomp1 : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx =>
      (p.M1 - q.M1) ij.1 ij.2)‖ ≤ dist p q := by
    have hproj : dist p.toMetricCoordinates.2.1 q.toMetricCoordinates.2.1 ≤
        dist p.toMetricCoordinates q.toMetricCoordinates := by simp [Prod.dist_eq]
    calc
      _ = dist p.toMetricCoordinates.2.1 q.toMetricCoordinates.2.1 := by
        rw [dist_eq_norm]
        congr 1
      _ ≤ dist p q := hproj
  have hcomp2 : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx =>
      (p.N0 - q.N0) ij.1 ij.2)‖ ≤ dist p q := by
    have hproj : dist p.toMetricCoordinates.2.2.1 q.toMetricCoordinates.2.2.1 ≤
        dist p.toMetricCoordinates q.toMetricCoordinates := by simp [Prod.dist_eq]
    calc
      _ = dist p.toMetricCoordinates.2.2.1 q.toMetricCoordinates.2.2.1 := by
        rw [dist_eq_norm]
        congr 1
      _ ≤ dist p q := hproj
  have hcomp3 : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx =>
      (p.N1 - q.N1) ij.1 ij.2)‖ ≤ dist p q := by
    have hproj : dist p.toMetricCoordinates.2.2.2.1 q.toMetricCoordinates.2.2.2.1 ≤
        dist p.toMetricCoordinates q.toMetricCoordinates := by simp [Prod.dist_eq]
    calc
      _ = dist p.toMetricCoordinates.2.2.2.1 q.toMetricCoordinates.2.2.2.1 := by
        rw [dist_eq_norm]
        congr 1
      _ ≤ dist p q := hproj
  have hcomp4 : ‖(WithLp.toLp 2 (p.mX - q.mX) : Euc dx)‖ ≤ dist p q := by
    have hproj : dist p.toMetricCoordinates.2.2.2.2 q.toMetricCoordinates.2.2.2.2 ≤
        dist p.toMetricCoordinates q.toMetricCoordinates := by simp [Prod.dist_eq]
    calc
      _ = dist p.toMetricCoordinates.2.2.2.2 q.toMetricCoordinates.2.2.2.2 := by
        simp [dist_eq_norm, SummarySpace.toMetricCoordinates]
      _ ≤ dist p q := hproj
  have hblock (A B : RectMatrix dz dx)
      (hAB : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx => (A - B) ij.1 ij.2)‖ ≤
        dist p q) :
      ‖matrixCLM (A - B)‖ ≤ entryNormConstant dz dx * dist p q := by
    apply matrixNorm_le_entryBound (A - B) (dist p q) dist_nonneg
    intro i j
    have hij := PiLp.norm_apply_le
      (WithLp.toLp 2 (fun ij : Fin dz × Fin dx => (A - B) ij.1 ij.2)) (i, j)
    have hflat : ‖WithLp.toLp 2 (fun ij : Fin dz × Fin dx => (A - B) ij.1 ij.2)‖ ≤
        dist p q := by
      simpa [dist_eq_norm] using hAB
    simpa [Real.norm_eq_abs] using hij.trans hflat
  have hm : Real.sqrt (∑ i, (p.mX i - q.mX i) ^ 2) ≤ dx * dist p q := by
    have hm' : ‖(WithLp.toLp 2 (p.mX - q.mX) : Euc dx)‖ ≤ dx * dist p q := by
      apply eucNorm_le_card_mul_bound _ _ dist_nonneg
      intro i
      have hi := PiLp.norm_apply_le (WithLp.toLp 2 (p.mX - q.mX) : Euc dx) i
      simpa [Real.norm_eq_abs] using hi.trans hcomp4
    simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hm'
  unfold dS
  have h0 := hblock p.M0 q.M0 hcomp0
  have h1 := hblock p.M1 q.M1 hcomp1
  have h2 := hblock p.N0 q.N0 hcomp2
  have h3 := hblock p.N1 q.N1 hcomp3
  nlinarith [entryNormConstant_nonneg dz dx, dist_nonneg (x := p) (y := q)]

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
