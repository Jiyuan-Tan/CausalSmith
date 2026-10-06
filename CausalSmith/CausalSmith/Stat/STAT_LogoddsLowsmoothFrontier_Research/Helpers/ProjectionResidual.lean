module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionMoments

/-! # The degenerate projection-kernel residual

The order-two Hoeffding residual has zero conditional mean in both coordinates.
Its energy is the kernel energy minus the constant and first-order energies.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The uncentered first projection of the symmetric marked kernel. -/
-- @node: projectionFirst
def projectionFirst (P : ObservedLaw) (W V : BoundedMark) (k : ℕ) (o : Record) : ℝ :=
  ∫ p, symmetricProjectionKernel k W.value V.value o p ∂P.measure

/-- The constant term of the Hoeffding decomposition. -/
-- @node: projectionMean
def projectionMean (P : ObservedLaw) (W V : BoundedMark) (k : ℕ) : ℝ :=
  uniformInner (cosineProjection k (conditionalMarkMean P W))
    (cosineProjection k (conditionalMarkMean P V))

/-- The completely degenerate second-order residual. -/
-- @node: projectionResidual
def projectionResidual (P : ObservedLaw) (W V : BoundedMark) (k : ℕ)
    (o p : Record) : ℝ :=
  symmetricProjectionKernel k W.value V.value o p - projectionFirst P W V k o -
    projectionFirst P W V k p + projectionMean P W V k

/-- Each kernel section is integrable, including at records in null sets. [the stated conclusion](goal) holds. -/
-- @node: symmetricProjectionKernel_section_integrable
lemma symmetricProjectionKernel_section_integrable (P : ObservedLaw) (W V : BoundedMark)
    (k : ℕ) (o : Record) :
    Integrable (symmetricProjectionKernel k W.value V.value o) P.measure := by
  have hc : Continuous (fun p : Record => projectionKernel k (covariate o) (covariate p)) := by
    unfold projectionKernel covariate
    fun_prop
  have hi (B : BoundedMark) := boundedMark_mul_continuous_integrable P B _ hc
  exact (((hi V).const_mul (W.value o)).add ((hi W).const_mul (V.value o))).div_const 2
    |>.congr (Filter.Eventually.of_forall (fun p => by unfold symmetricProjectionKernel; dsimp; ring))

/-- The first projection is measurable by its explicit conditional-mean formula. [the documented result](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionFirst_measurable
@[fun_prop]
lemma projectionFirst_measurable (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) : Measurable (projectionFirst P W V k) := by
  unfold projectionFirst
  simp_rw [symmetricProjectionKernel_integral_right P hDesign W V k]
  have hw := W.measurable_value
  have hv := V.measurable_value
  unfold cosineProjection covariate
  fun_prop

/-- [Fubini gives integrability of the first projection. [the stated conclusion](goal) holds. -/
-- @node: projectionFirst_integrable
lemma projectionFirst_integrable (P : ObservedLaw) (W V : BoundedMark) (k : ℕ) :
    Integrable (projectionFirst P W V k) P.measure :=
  (symmetricProjectionKernel_integrable P k W V).integral_prod_left

/-- The mean of the first projection is the kernel mean. Under the stated assumptions. [The stated hypotheses](hyp:hDesign) hold, and [the stated conclusion follows](goal). -/
-- @node: projectionFirst_integral
lemma projectionFirst_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ o, projectionFirst P W V k o ∂P.measure) = projectionMean P W V k :=
  symmetricProjectionKernel_integral P hDesign W V k

/-- [Symmetry is preserved when removing the two first projections. [the stated conclusion](goal) holds. -/
-- @node: projectionResidual_symm
lemma projectionResidual_symm (P : ObservedLaw) (W V : BoundedMark) (k : ℕ)
    (o p : Record) : projectionResidual P W V k o p = projectionResidual P W V k p o := by
  unfold projectionResidual
  rw [symmetricProjectionKernel_symm k W.value V.value o p]
  ring

/-- Integrating out the second coordinate kills the residual exactly. Under the stated assumptions. [The stated hypotheses](hyp:hDesign) hold, and [the stated conclusion follows](goal). -/
-- @node: projectionResidual_integral_right
lemma projectionResidual_integral_right (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (o : Record) :
    (∫ p, projectionResidual P W V k o p ∂P.measure) = 0 := by
  unfold projectionResidual
  have hi := symmetricProjectionKernel_section_integrable P W V k o
  have hf := projectionFirst_integrable P W V k
  integral_linearity
  rw [projectionFirst_integral P hDesign W V k]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul]
  unfold projectionFirst
  ring

/-- [Symmetry gives the other coordinate's degeneracy.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_integral_left
lemma projectionResidual_integral_left (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (p : Record) :
    (∫ o, projectionResidual P W V k o p ∂P.measure) = 0 := by
  simp_rw [projectionResidual_symm P W V k _ p]
  exact projectionResidual_integral_right P hDesign W V k p

/-- [The residual is Borel measurable on the product record space. [the documented result](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_measurable
@[fun_prop]
lemma projectionResidual_measurable (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    Measurable (fun z : Record × Record => projectionResidual P W V k z.1 z.2) := by
  have hq := symmetricProjectionKernel_measurable k W V
  have hf := projectionFirst_measurable P hDesign W V k
  unfold projectionResidual
  fun_prop

/-- [Removing square-integrable projections preserves square integrability.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_sq_integrable
lemma projectionResidual_sq_integrable (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    Integrable (fun z : Record × Record => (projectionResidual P W V k z.1 z.2)^2)
      (P.measure.prod P.measure) := by
  have hq : MemLp (fun z : Record × Record => symmetricProjectionKernel k W.value V.value z.1 z.2)
      2 (P.measure.prod P.measure) :=
    (memLp_two_iff_integrable_sq (symmetricProjectionKernel_measurable k W V).aestronglyMeasurable).mpr
      (symmetricProjectionKernel_sq_integrable P k W V)
  have hf := projectionFirst_measurable P hDesign W V k
  have hs := symmetricProjectionKernel_first_sq_integrable P hDesign W V k
  have hfst : MemLp (fun z : Record × Record => projectionFirst P W V k z.1)
      2 (P.measure.prod P.measure) :=
    (memLp_two_iff_integrable_sq (hf.comp measurable_fst).aestronglyMeasurable).mpr
      (hs.comp_fst P.measure)
  have hsnd : MemLp (fun z : Record × Record => projectionFirst P W V k z.2)
      2 (P.measure.prod P.measure) :=
    (memLp_two_iff_integrable_sq (hf.comp measurable_snd).aestronglyMeasurable).mpr
      (hs.comp_snd P.measure)
  exact (memLp_two_iff_integrable_sq
    (projectionResidual_measurable P hDesign W V k).aestronglyMeasurable).mp
      (((hq.sub hfst).sub hsnd).add (memLp_const (projectionMean P W V k)))

/-- [Orthogonality removes twice the first-projection energy from the kernel energy.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_energy
lemma projectionResidual_energy (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ z : Record × Record, (projectionResidual P W V k z.1 z.2)^2
      ∂(P.measure.prod P.measure)) =
      (∫ z : Record × Record, (symmetricProjectionKernel k W.value V.value z.1 z.2)^2
        ∂(P.measure.prod P.measure)) -
      2 * (∫ o, (projectionFirst P W V k o)^2 ∂P.measure) +
      (projectionMean P W V k)^2 := by
  let q := fun z : Record × Record => symmetricProjectionKernel k W.value V.value z.1 z.2
  let f := projectionFirst P W V k
  let τ := projectionMean P W V k
  let μ := P.measure.prod P.measure
  have hf : Integrable f P.measure := projectionFirst_integrable P W V k
  have hfm : Measurable f := projectionFirst_measurable P hDesign W V k
  have hfmean : (∫ o, f o ∂P.measure) = τ := projectionFirst_integral P hDesign W V k
  have hs : Integrable (fun o => (f o)^2) P.measure :=
    symmetricProjectionKernel_first_sq_integrable P hDesign W V k
  have hq : MemLp q 2 μ :=
    (memLp_two_iff_integrable_sq (symmetricProjectionKernel_measurable k W V).aestronglyMeasurable).mpr
      (symmetricProjectionKernel_sq_integrable P k W V)
  have hf1 : MemLp (fun z : Record × Record => f z.1) 2 μ :=
    (memLp_two_iff_integrable_sq (hfm.comp measurable_fst).aestronglyMeasurable).mpr
      (hs.comp_fst P.measure)
  have hf2 : MemLp (fun z : Record × Record => f z.2) 2 μ :=
    (memLp_two_iff_integrable_sq (hfm.comp measurable_snd).aestronglyMeasurable).mpr
      (hs.comp_snd P.measure)
  have hqf1 : Integrable (fun z : Record × Record => q z * f z.1) μ := hq.integrable_mul hf1
  have hqf2 : Integrable (fun z : Record × Record => q z * f z.2) μ := hq.integrable_mul hf2
  have h12 : Integrable (fun z : Record × Record => f z.1 * f z.2) μ := hf.mul_prod hf
  have hcross1 : (∫ z : Record × Record, q z * f z.1 ∂μ) =
      ∫ o, (f o)^2 ∂P.measure := by
    rw [integral_prod _ hqf1]
    simp_rw [integral_mul_const]
    change (∫ o, f o * f o ∂P.measure) = _
    simp only [← pow_two]
  have hcross2 : (∫ z : Record × Record, q z * f z.2 ∂μ) =
      ∫ o, (f o)^2 ∂P.measure := by
    rw [integral_prod_symm _ hqf2]
    simp_rw [integral_mul_const]
    have he (p : Record) : (∫ o, q (o, p) ∂P.measure) = f p := by
      dsimp [q, f, projectionFirst]
      simp_rw [symmetricProjectionKernel_symm k W.value V.value _ p]
    simp_rw [he, ← pow_two]
  have hfirst1 : (∫ z : Record × Record, f z.1 ∂μ) = τ := by
    rw [integral_prod _ (hf.comp_fst P.measure)]
    simpa using hfmean
  have hfirst2 : (∫ z : Record × Record, f z.2 ∂μ) = τ := by
    rw [integral_prod_symm _ (hf.comp_snd P.measure)]
    simpa using hfmean
  have hs1 : (∫ z : Record × Record, (f z.1)^2 ∂μ) = ∫ o, (f o)^2 ∂P.measure := by
    rw [integral_prod _ (hs.comp_fst P.measure)]
    simp
  have hs2 : (∫ z : Record × Record, (f z.2)^2 ∂μ) = ∫ o, (f o)^2 ∂P.measure := by
    rw [integral_prod_symm _ (hs.comp_snd P.measure)]
    simp
  have hcross12 : (∫ z : Record × Record, f z.1 * f z.2 ∂μ) = τ^2 := by
    rw [integral_prod_mul, hfmean]
    ring
  have hqmean : (∫ z, q z ∂μ) = τ := by
    rw [integral_prod _ (symmetricProjectionKernel_integrable P k W V)]
    exact symmetricProjectionKernel_integral P hDesign W V k
  change (∫ z : Record × Record, (q z - f z.1 - f z.2 + τ)^2 ∂μ) =
    (∫ z, (q z)^2 ∂μ) - 2 * (∫ o, (f o)^2 ∂P.measure) + τ^2
  have he (z : Record × Record) : (q z - f z.1 - f z.2 + τ)^2 =
      (q z)^2 + (f z.1)^2 + (f z.2)^2 + τ^2 -
      2 * (q z * f z.1) - 2 * (q z * f z.2) + 2 * (q z * τ) +
      2 * (f z.1 * f z.2) - 2 * (f z.1 * τ) - 2 * (f z.2 * τ) := by ring
  simp_rw [he]
  have hqs := symmetricProjectionKernel_sq_integrable P k W V
  have hqi := symmetricProjectionKernel_integrable P k W V
  have hfs1 := hs.comp_fst P.measure
  have hfs2 := hs.comp_snd P.measure
  have hfi1 := hf.comp_fst P.measure
  have hfi2 := hf.comp_snd P.measure
  have h0 : Integrable (fun z => (q z)^2 + (f z.1)^2) μ := hqs.add hfs1
  have h1 := h0.add hfs2
  have h2 := h1.add (integrable_const (τ^2) : Integrable (fun _ : Record × Record => τ^2) μ)
  have h3 := h2.sub (hqf1.const_mul 2)
  have h4 := h3.sub (hqf2.const_mul 2)
  have h5 := h4.add ((hqi.mul_const τ).const_mul 2)
  have h6 := h5.add (h12.const_mul 2)
  have h7 := h6.sub ((hfi1.mul_const τ).const_mul 2)
  have ht1 := hqf1.const_mul 2
  have ht2 := hqf2.const_mul 2
  have ht3 := (hqi.mul_const τ).const_mul 2
  have ht4 := h12.const_mul 2
  have ht5 := (hfi1.mul_const τ).const_mul 2
  have ht6 := (hfi2.mul_const τ).const_mul 2
  integral_linearity
  rw [hs1, hs2, hcross1, hcross2, hcross12, hqmean, hfirst1, hfirst2]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul]
  ring

/-- [The residual energy is bounded by k, with the exact Hoeffding constant preserved.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_energy_le_rank
lemma projectionResidual_energy_le_rank (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ z : Record × Record, (projectionResidual P W V k z.1 z.2)^2
      ∂(P.measure.prod P.measure)) ≤ (k : ℝ) := by
  rw [projectionResidual_energy P hDesign W V k]
  have hc := symmetricProjectionKernel_first_centered_energy P hDesign W V k
  have hn : 0 ≤ ∫ o, (projectionFirst P W V k o - projectionMean P W V k)^2 ∂P.measure :=
    integral_nonneg (fun o => sq_nonneg _)
  have hs : 0 ≤ ∫ o, (projectionFirst P W V k o)^2 ∂P.measure :=
    integral_nonneg (fun o => sq_nonneg _)
  change (∫ o, (projectionFirst P W V k o - projectionMean P W V k)^2 ∂P.measure) =
    (∫ o, (projectionFirst P W V k o)^2 ∂P.measure) - (projectionMean P W V k)^2 at hc
  have hk := symmetricProjectionKernel_energy_le_rank P hDesign W V k
  linarith


/-- [The run's residual satisfies the library's exact order-two variance interface.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_degenKernel
lemma projectionResidual_degenKernel (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    Causalean.Stat.DegenKernel P.measure (projectionResidual P W V k) :=
  ⟨projectionResidual_measurable P hDesign W V k,
    projectionResidual_symm P W V k,
    projectionResidual_integral_right P hDesign W V k,
    projectionResidual_sq_integrable P hDesign W V k⟩

/-- [The first Hoeffding component is centered under the record law.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionFirst_centered_integral
lemma projectionFirst_centered_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ o, (projectionFirst P W V k o - projectionMean P W V k) ∂P.measure) = 0 := by
  rw [integral_sub (projectionFirst_integrable P W V k) (integrable_const _),
    projectionFirst_integral P hDesign W V k]
  simp

/-- [Exact fixed-order variance specializes to the run's degenerate residual.](goal) Under [the stated assumptions](hyp:hDesign,μ,hn). -/
-- @node: projectionResidual_rescaled_secondMoment
lemma projectionResidual_rescaled_secondMoment (P : ObservedLaw)
    (hDesign : UniformDesign P) (W V : BoundedMark) (k : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Record μ P.measure) (n : ℕ) (hn : 2 ≤ n) :
    (∫ ω, (Real.sqrt (n : ℝ) *
      Causalean.Stat.uStatistic S (projectionResidual P W V k) n ω)^2 ∂μ) =
      2 * (∫ z : Record × Record, (projectionResidual P W V k z.1 z.2)^2
        ∂(P.measure.prod P.measure)) / ((n : ℝ) - 1) := by
  exact S.integral_rescaled_sq (projectionResidual_degenKernel P hDesign W V k) hn

/-- [Removing the square-root rescaling gives the sharp residual second moment.](goal) Under [the stated assumptions](hyp:hDesign,μ,hn). -/
-- @node: projectionResidual_secondMoment
lemma projectionResidual_secondMoment (P : ObservedLaw)
    (hDesign : UniformDesign P) (W V : BoundedMark) (k : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Record μ P.measure) (n : ℕ) (hn : 2 ≤ n) :
    (∫ ω, (Causalean.Stat.uStatistic S (projectionResidual P W V k) n ω)^2 ∂μ) =
      2 * (∫ z : Record × Record, (projectionResidual P W V k z.1 z.2)^2
        ∂(P.measure.prod P.measure)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h := projectionResidual_rescaled_secondMoment P hDesign W V k S n hn
  simp_rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)] at h
  rw [integral_const_mul] at h
  apply (eq_div_iff (mul_ne_zero hn0 hn1)).mpr
  have h' := (eq_div_iff hn1).mp h
  nlinarith [h']

/-- [The residual contributes exactly the required 2k/(n(n-1)) upper bound.](goal) Under [the stated assumptions](hyp:hDesign,μ,hn). -/
-- @node: projectionResidual_secondMoment_le
lemma projectionResidual_secondMoment_le (P : ObservedLaw)
    (hDesign : UniformDesign P) (W V : BoundedMark) (k : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Record μ P.measure) (n : ℕ) (hn : 2 ≤ n) :
    (∫ ω, (Causalean.Stat.uStatistic S (projectionResidual P W V k) n ω)^2 ∂μ) ≤
      2 * k / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [projectionResidual_secondMoment P hDesign W V k S n hn]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (projectionResidual_energy_le_rank P hDesign W V k)
      (by norm_num)) (mul_nonneg (by positivity) (by linarith))


/-- [Each record occurs n-1 times as the first coordinate of the ordered pair sum.](goal) Under [the stated assumptions](hyp:f). -/
-- @node: projection_offDiag_sum_first
lemma projection_offDiag_sum_first (n : ℕ) (f : Fin n → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag, f ij.1) =
      ((n : ℝ) - 1) * ∑ i, f i := by
  classical
  have h := Finset.sum_union (Finset.disjoint_diag_offDiag
    (Finset.univ : Finset (Fin n))) (f := fun ij => f ij.1)
  rw [Finset.diag_union_offDiag, Finset.sum_product] at h
  simp only [Finset.sum_diag, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at h
  nlinarith [h]

/-- [Each record occurs n-1 times as the second coordinate of the ordered pair sum.](goal) Under [the stated assumptions](hyp:f). -/
-- @node: projection_offDiag_sum_second
lemma projection_offDiag_sum_second (n : ℕ) (f : Fin n → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag, f ij.2) =
      ((n : ℝ) - 1) * ∑ i, f i := by
  classical
  have h := Finset.sum_union (Finset.disjoint_diag_offDiag
    (Finset.univ : Finset (Fin n))) (f := fun ij => f ij.2)
  rw [Finset.diag_union_offDiag, Finset.sum_product] at h
  simp only [Finset.sum_diag, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith [h]

/-- [The original statistic has the exact finite-sample Hoeffding decomposition.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: projectionStatistic_hoeffding
lemma projectionStatistic_hoeffding (P : ObservedLaw) (W V : BoundedMark)
    (k n : ℕ) (hn : 2 ≤ n) (o : Fin n → Record) :
    projectionStatistic n k W.value V.value o - projectionMean P W V k =
      2 / (n : ℝ) * ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k) +
      ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          projectionResidual P W V k (o ij.1) (o ij.2) := by
  classical
  let s := (Finset.univ : Finset (Fin n)).offDiag
  have hs : (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2) = s := by
    ext ij
    simp [s, Finset.mem_offDiag]
  have hcard : (s.card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    dsimp [s]
    rw [Finset.offDiag_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by nlinarith : n ≤ n*n), Nat.cast_mul]
    ring
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsum : (∑ ij ∈ s, projectionResidual P W V k (o ij.1) (o ij.2)) =
      (∑ ij ∈ s, symmetricProjectionKernel k W.value V.value (o ij.1) (o ij.2)) -
        2 * (((n : ℝ) - 1) * ∑ i, projectionFirst P W V k (o i)) +
        (n : ℝ) * ((n : ℝ) - 1) * projectionMean P W V k := by
    simp only [projectionResidual, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hcard]
    dsimp only [s]
    rw [projection_offDiag_sum_first n (fun i => projectionFirst P W V k (o i)),
      projection_offDiag_sum_second n (fun i => projectionFirst P W V k (o i))]
    ring
  rw [projectionStatistic_eq_symmetric, hs]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  field_simp
  <;> ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
