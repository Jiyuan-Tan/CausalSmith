module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEndpointAlgebra
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Quantile.FiniteMassTransport
public import Causalean.Stat.Quantile.Pushforward

/-!
Finite-measure transport, inverse-weight pushforward, and product-integral
lemmas used by projected-cell stability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:a,x), [this definition](goal) introduces the corresponding object. -/
def projectionInverseArmProbReal (a : ArmSpace) (x : ℝ) : ℝ :=
  if a then x⁻¹ else (1 - x)⁻¹

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,a,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionInverseArmProbReal_coe {ε : ℝ} (a : ArmSpace) (e : ScoreSpace ε) :
    projectionInverseArmProbReal a (e : ℝ) = (armProb a e)⁻¹ := by
  cases a <;> rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:a), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_projectionInverseArmProbReal (a : ArmSpace) :
    Measurable (projectionInverseArmProbReal a) := by
  cases a
  · exact (measurable_const.sub measurable_id).inv
  · exact measurable_id.inv

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,x,hx,y,hy), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionInverseArmProbReal_lipschitzOn {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (x : ℝ) (hx : x ∈ Icc ε (1 - ε))
    (y : ℝ) (hy : y ∈ Icc ε (1 - ε)) :
    |projectionInverseArmProbReal a x - projectionInverseArmProbReal a y| ≤
      (ε ^ 2)⁻¹ * |x - y| := by
  let ex : ScoreSpace ε := ⟨x, hx⟩
  let ey : ScoreSpace ε := ⟨y, hy⟩
  have h := projectionInverseArmProb_lipschitz hOverlap a ex ey
  cases a <;> simpa [ex, ey, projectionInverseArmProbReal, armProb] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:α,μ), this result [establishes the stated mathematical conclusion](goal). -/
lemma real_univ_map_subtype_val {α : Set ℝ} (μ : Measure α) [IsFiniteMeasure μ] :
    (μ.map (fun x : α => (x : ℝ))).real univ = μ.real univ := by
  rw [Measure.real, Measure.real, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,μ), this result [establishes the stated mathematical conclusion](goal). -/
lemma map_subtype_val_support_Icc {a b : ℝ} (μ : Measure (Icc a b)) :
    (μ.map (fun x : Icc a b => (x : ℝ))) (Icc a b)ᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:α,μ,hp), this result [establishes the stated mathematical conclusion](goal). -/
lemma map_normalized_subtype_eq_finiteNormalize {α : Set ℝ}
    (μ : Measure α) [IsFiniteMeasure μ] (hp : 0 < μ.real univ) :
    ((μ univ)⁻¹ • μ).map (fun x : α => (x : ℝ)) =
      (FiniteMeasure.normalize
        (⟨μ.map (fun x : α => (x : ℝ)), inferInstance⟩ : FiniteMeasure ℝ) :
        Measure ℝ) := by
  let μR : FiniteMeasure ℝ := ⟨μ.map (fun x : α => (x : ℝ)), inferInstance⟩
  have hmass : (μR.mass : ℝ) = μ.real univ := by
    change (μ.map (fun x : α => (x : ℝ))).real univ = μ.real univ
    exact real_univ_map_subtype_val μ
  have hμR : μR ≠ 0 := by
    intro h
    have : (μR.mass : ℝ) = 0 := by simp [h]
    linarith
  rw [Measure.map_smul, μR.toMeasure_normalize_eq_of_nonzero hμR]
  change (μ univ)⁻¹ • μ.map (fun x : α => (x : ℝ)) =
    (μR.mass⁻¹ : NNReal) • (μR : Measure ℝ)
  have hmassENN : μ univ = (μR.mass : ENNReal) := by
    dsimp [μR, FiniteMeasure.mass]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [hmassENN]
  have hmass0 : μR.mass ≠ 0 := by
    intro h
    exact hμR ((FiniteMeasure.mass_zero_iff μR).mp h)
  change (μR.mass : ENNReal)⁻¹ • (μR : Measure ℝ) =
    ((μR.mass⁻¹ : NNReal) : ENNReal) • (μR : Measure ℝ)
  rw [ENNReal.coe_inv hmass0]

/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,μ,ν,hp,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma finite_mass_subtype_quantile_transport_le {a b : ℝ} (hab : a ≤ b)
    (μ ν : Measure (Icc a b)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hp : 0 < μ.real univ) (hq : 0 < ν.real univ) :
    min (μ.real univ) (ν.real univ) *
        (∫ u in (0 : ℝ)..1,
          |Causalean.Stat.quantile
              (((μ univ)⁻¹ • μ).map (fun x : Icc a b => (x : ℝ))) u -
            Causalean.Stat.quantile
              (((ν univ)⁻¹ • ν).map (fun x : Icc a b => (x : ℝ))) u|) ≤
      (∫ t in a..b,
        |(μ {x | (x : ℝ) ≤ t}).toReal -
          (ν {x | (x : ℝ) ≤ t}).toReal|) +
        (b - a) * |μ.real univ - ν.real univ| := by
  let μR : FiniteMeasure ℝ := ⟨μ.map (fun x : Icc a b => (x : ℝ)), inferInstance⟩
  let νR : FiniteMeasure ℝ := ⟨ν.map (fun x : Icc a b => (x : ℝ)), inferInstance⟩
  have hμmass : (μR.mass : ℝ) = μ.real univ := by
    change (μ.map (fun x : Icc a b => (x : ℝ))).real univ = μ.real univ
    exact real_univ_map_subtype_val μ
  have hνmass : (νR.mass : ℝ) = ν.real univ := by
    change (ν.map (fun x : Icc a b => (x : ℝ))).real univ = ν.real univ
    exact real_univ_map_subtype_val ν
  have htransport :=
    Causalean.Stat.Quantile.FiniteMassTransport.finite_mass_quantile_transport_le
      μR νR hab (hμmass.symm ▸ hp) (hνmass.symm ▸ hq)
      (map_subtype_val_support_Icc μ) (map_subtype_val_support_Icc ν)
  rw [← map_normalized_subtype_eq_finiteNormalize μ hp,
    ← map_normalized_subtype_eq_finiteNormalize ν hq] at htransport
  rw [hμmass, hνmass] at htransport
  have hμcdf (t : ℝ) :
      (μ.map (fun x : Icc a b => (x : ℝ))) (Iic t) =
        μ {x | (x : ℝ) ≤ t} := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  have hνcdf (t : ℝ) :
      (ν.map (fun x : Icc a b => (x : ℝ))) (Iic t) =
        ν {x | (x : ℝ) ≤ t} := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  simpa only [μR, νR, FiniteMeasure.toMeasure_mk,
    hμcdf, hνcdf] using htransport

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,μ,ν,hp,hq), this result [establishes the stated mathematical conclusion](goal). -/
lemma inverseArmProb_quantile_distance_le {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (μ ν : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hp : 0 < μ.real univ) (hq : 0 < ν.real univ) :
    (∫ u in (0 : ℝ)..1,
      |Causalean.Stat.quantile
          (((μ univ)⁻¹ • μ).map (fun e => (armProb a e)⁻¹)) u -
        Causalean.Stat.quantile
          (((ν univ)⁻¹ • ν).map (fun e => (armProb a e)⁻¹)) u|) ≤
      (ε ^ 2)⁻¹ *
        ∫ u in (0 : ℝ)..1,
          |Causalean.Stat.quantile
              (((μ univ)⁻¹ • μ).map (fun e : ScoreSpace ε => (e : ℝ))) u -
            Causalean.Stat.quantile
              (((ν univ)⁻¹ • ν).map (fun e : ScoreSpace ε => (e : ℝ))) u| := by
  let μR : FiniteMeasure ℝ :=
    ⟨μ.map (fun e : ScoreSpace ε => (e : ℝ)), inferInstance⟩
  let νR : FiniteMeasure ℝ :=
    ⟨ν.map (fun e : ScoreSpace ε => (e : ℝ)), inferInstance⟩
  let μP : Measure ℝ := FiniteMeasure.normalize μR
  let νP : Measure ℝ := FiniteMeasure.normalize νR
  letI : IsProbabilityMeasure μP := by dsimp [μP]; infer_instance
  letI : IsProbabilityMeasure νP := by dsimp [νP]; infer_instance
  have hpush := Causalean.Stat.Quantile.Pushforward.quantile_pushforward_lipschitzOn
    μP νP (by linarith [hOverlap.2] : ε ≤ 1 - ε) (by
      dsimp [μP]
      exact Causalean.Stat.Quantile.FiniteMassTransport.normalize_support_Icc
        μR (by
          rw [show (μR.mass : ℝ) = μ.real univ by
            change (μ.map (fun e : ScoreSpace ε => (e : ℝ))).real univ = μ.real univ
            exact real_univ_map_subtype_val μ]
          exact hp)
        (map_subtype_val_support_Icc μ)) (by
      dsimp [νP]
      exact Causalean.Stat.Quantile.FiniteMassTransport.normalize_support_Icc
        νR (by
          rw [show (νR.mass : ℝ) = ν.real univ by
            change (ν.map (fun e : ScoreSpace ε => (e : ℝ))).real univ = ν.real univ
            exact real_univ_map_subtype_val ν]
          exact hq)
        (map_subtype_val_support_Icc ν))
    (by positivity : 0 ≤ (ε ^ 2)⁻¹) (projectionInverseArmProbReal a)
    (measurable_projectionInverseArmProbReal a)
    (projectionInverseArmProbReal_lipschitzOn hOverlap a)
  have hμnorm := map_normalized_subtype_eq_finiteNormalize μ hp
  have hνnorm := map_normalized_subtype_eq_finiteNormalize ν hq
  change _ ≤ _
  dsimp [μP, νP] at hpush
  rw [← hμnorm, ← hνnorm] at hpush
  rw [Measure.map_map (measurable_projectionInverseArmProbReal a) (by fun_prop),
    Measure.map_map (measurable_projectionInverseArmProbReal a) (by fun_prop)] at hpush
  have hfun : projectionInverseArmProbReal a ∘
      (fun e : ScoreSpace ε => (e : ℝ)) = fun e => (armProb a e)⁻¹ := by
    funext e
    exact projectionInverseArmProbReal_coe a e
  rw [hfun] at hpush
  exact hpush

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,μ',ν,ν',A,B,hA,hB,hμ,hμ',hν,hν',upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma quantile_product_integral_stability
    (μ μ' ν ν' : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : μ (Icc 0 A)ᶜ = 0) (hμ' : μ' (Icc 0 A)ᶜ = 0)
    (hν : ν (Icc 0 B)ᶜ = 0) (hν' : ν' (Icc 0 B)ᶜ = 0)
    (upper : Bool) :
    |(∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile μ u *
          Causalean.Stat.quantile ν (if upper then u else 1 - u)) -
      ∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile μ' u *
          Causalean.Stat.quantile ν' (if upper then u else 1 - u)| ≤
      B * (∫ u in (0 : ℝ)..1,
        |Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u|) +
      A * (∫ u in (0 : ℝ)..1,
        |Causalean.Stat.quantile ν u - Causalean.Stat.quantile ν' u|) := by
  let s : ℝ → ℝ := if upper then id else fun u => 1 - u
  have hsmeas : Measurable s := by
    cases upper <;> simp [s] <;> fun_prop
  have hsmap : Causalean.Stat.unifOI.map s = Causalean.Stat.unifOI := by
    cases upper
    · simpa [s] using Causalean.Stat.map_one_sub_unifOI
    · simp [s]
  have hsp : MeasurePreserving s Causalean.Stat.unifOI Causalean.Stat.unifOI :=
    ⟨hsmeas, hsmap⟩
  have hs_apply (u : ℝ) : s u = if upper then u else 1 - u := by
    cases upper <;> rfl
  have hμb := Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae μ hμ
  have hμb' := Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae μ' hμ'
  have hνb := hsp.quasiMeasurePreserving.tendsto_ae.eventually
    (Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae ν hν)
  have hνb' := hsp.quasiMeasurePreserving.tendsto_ae.eventually
    (Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae ν' hν')
  have hμi : Integrable (Causalean.Stat.quantile μ) Causalean.Stat.unifOI := by
    apply (integrable_const A).mono'
    · exact (Causalean.Stat.aemeasurable_quantile_unifOI μ).aestronglyMeasurable
    · filter_upwards [hμb] with u hu
      simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2
  have hμi' : Integrable (Causalean.Stat.quantile μ') Causalean.Stat.unifOI := by
    apply (integrable_const A).mono'
    · exact (Causalean.Stat.aemeasurable_quantile_unifOI μ').aestronglyMeasurable
    · filter_upwards [hμb'] with u hu
      simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2
  have hνae : AEMeasurable (fun u => Causalean.Stat.quantile ν (s u))
      Causalean.Stat.unifOI := by
    have h := Causalean.Stat.aemeasurable_quantile_unifOI ν
    rw [← hsmap] at h
    exact h.comp_measurable hsmeas
  have hνae' : AEMeasurable (fun u => Causalean.Stat.quantile ν' (s u))
      Causalean.Stat.unifOI := by
    have h := Causalean.Stat.aemeasurable_quantile_unifOI ν'
    rw [← hsmap] at h
    exact h.comp_measurable hsmeas
  have hνi : Integrable (fun u => Causalean.Stat.quantile ν (s u))
      Causalean.Stat.unifOI := by
    apply (integrable_const B).mono' hνae.aestronglyMeasurable
    filter_upwards [hνb] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2
  have hνi' : Integrable (fun u => Causalean.Stat.quantile ν' (s u))
      Causalean.Stat.unifOI := by
    apply (integrable_const B).mono' hνae'.aestronglyMeasurable
    filter_upwards [hνb'] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2
  have hprod : Integrable
      (fun u => Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (s u))
      Causalean.Stat.unifOI := by
    apply (integrable_const (A * B)).mono'
    · exact ((Causalean.Stat.aemeasurable_quantile_unifOI μ).mul hνae).aestronglyMeasurable
    · filter_upwards [hμb, hνb] with u hy hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.1 hw.1)]
      exact mul_le_mul hy.2 hw.2 hw.1 hA
  have hprod' : Integrable
      (fun u => Causalean.Stat.quantile μ' u * Causalean.Stat.quantile ν' (s u))
      Causalean.Stat.unifOI := by
    apply (integrable_const (A * B)).mono'
    · exact ((Causalean.Stat.aemeasurable_quantile_unifOI μ').mul hνae').aestronglyMeasurable
    · filter_upwards [hμb', hνb'] with u hy hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy.1 hw.1)]
      exact mul_le_mul hy.2 hw.2 hw.1 hA
  have hdy : Integrable
      (fun u => |Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u|)
      Causalean.Stat.unifOI := (hμi.sub hμi').abs
  have hdw : Integrable
      (fun u => |Causalean.Stat.quantile ν (s u) - Causalean.Stat.quantile ν' (s u)|)
      Causalean.Stat.unifOI := (hνi.sub hνi').abs
  have hdw_eq :
      (∫ u, |Causalean.Stat.quantile ν (s u) - Causalean.Stat.quantile ν' (s u)|
        ∂Causalean.Stat.unifOI) =
      ∫ u, |Causalean.Stat.quantile ν u - Causalean.Stat.quantile ν' u|
        ∂Causalean.Stat.unifOI := by
    let f : ℝ → ℝ := fun u =>
      |Causalean.Stat.quantile ν u - Causalean.Stat.quantile ν' u|
    have hf : AEStronglyMeasurable f (Causalean.Stat.unifOI.map s) := by
      rw [hsmap]
      exact ((Causalean.Stat.aemeasurable_quantile_unifOI ν).sub
        (Causalean.Stat.aemeasurable_quantile_unifOI ν')).norm.aestronglyMeasurable
    have hmap := integral_map hsmeas.aemeasurable hf
    rw [hsmap] at hmap
    exact hmap.symm
  have hpoint : ∀ᵐ u ∂Causalean.Stat.unifOI,
      |Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (s u) -
        Causalean.Stat.quantile μ' u * Causalean.Stat.quantile ν' (s u)| ≤
      B * |Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u| +
        A * |Causalean.Stat.quantile ν (s u) - Causalean.Stat.quantile ν' (s u)| := by
    filter_upwards [hμb', hνb] with u hy' hw
    calc
      _ = |(Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u) *
            Causalean.Stat.quantile ν (s u) +
          Causalean.Stat.quantile μ' u *
            (Causalean.Stat.quantile ν (s u) -
              Causalean.Stat.quantile ν' (s u))| := by ring_nf
      _ ≤ |(Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u) *
            Causalean.Stat.quantile ν (s u)| +
          |Causalean.Stat.quantile μ' u *
            (Causalean.Stat.quantile ν (s u) -
              Causalean.Stat.quantile ν' (s u))| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hw.1, abs_of_nonneg hy'.1]
        apply add_le_add
        · simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hw.2 (abs_nonneg
              (Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u)))
        · exact mul_le_mul_of_nonneg_right hy'.2 (abs_nonneg _)
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
    rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
  simp_rw [hs_apply] at hprod hprod' hdy hdw hdw_eq hpoint
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
  rw [← integral_sub hprod hprod']
  calc
    |∫ u, (Causalean.Stat.quantile μ u *
          Causalean.Stat.quantile ν (if upper then u else 1 - u) -
        Causalean.Stat.quantile μ' u *
          Causalean.Stat.quantile ν' (if upper then u else 1 - u))
        ∂Causalean.Stat.unifOI| ≤
      ∫ u, |Causalean.Stat.quantile μ u *
          Causalean.Stat.quantile ν (if upper then u else 1 - u) -
        Causalean.Stat.quantile μ' u *
          Causalean.Stat.quantile ν' (if upper then u else 1 - u)|
        ∂Causalean.Stat.unifOI := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (μ := Causalean.Stat.unifOI)
              (f := fun u => Causalean.Stat.quantile μ u *
                Causalean.Stat.quantile ν (if upper then u else 1 - u) -
              Causalean.Stat.quantile μ' u *
                Causalean.Stat.quantile ν' (if upper then u else 1 - u)))
    _ ≤ ∫ u, (B * |Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u| +
        A * |Causalean.Stat.quantile ν (if upper then u else 1 - u) -
          Causalean.Stat.quantile ν' (if upper then u else 1 - u)|)
        ∂Causalean.Stat.unifOI := integral_mono_ae
          (hprod.sub hprod').abs
          (hdy.const_mul B |>.add (hdw.const_mul A)) hpoint
    _ = B * ∫ u, |Causalean.Stat.quantile μ u - Causalean.Stat.quantile μ' u|
          ∂Causalean.Stat.unifOI +
        A * ∫ u, |Causalean.Stat.quantile ν u - Causalean.Stat.quantile ν' u|
          ∂Causalean.Stat.unifOI := by
      rw [integral_add (hdy.const_mul B) (hdw.const_mul A),
        integral_const_mul, integral_const_mul]
      rw [← hdw_eq]

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,hp), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedOutcome_support (μ : Measure OutcomeSpace) [IsFiniteMeasure μ]
    (hp : 0 < μ.real univ) :
    (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ)))
      (Icc 0 1)ᶜ = 0 := by
  rw [map_normalized_subtype_eq_finiteNormalize μ hp]
  apply Causalean.Stat.Quantile.FiniteMassTransport.normalize_support_Icc
    (⟨μ.map (fun y : OutcomeSpace => (y : ℝ)), inferInstance⟩ : FiniteMeasure ℝ)
  · rw [show (FiniteMeasure.mass
        (⟨μ.map (fun y : OutcomeSpace => (y : ℝ)), inferInstance⟩ :
          FiniteMeasure ℝ) : ℝ) = μ.real univ by
      change (μ.map (fun y : OutcomeSpace => (y : ℝ))).real univ = μ.real univ
      exact real_univ_map_subtype_val μ]
    exact hp
  · exact map_subtype_val_support_Icc μ

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_inverseArmProb {ε : ℝ} (a : ArmSpace) :
    Measurable (fun e : ScoreSpace ε => (armProb a e)⁻¹) := by
  rw [show (fun e : ScoreSpace ε => (armProb a e)⁻¹) =
      projectionInverseArmProbReal a ∘ (fun e : ScoreSpace ε => (e : ℝ)) by
    funext e
    exact (projectionInverseArmProbReal_coe a e).symm]
  exact (measurable_projectionInverseArmProbReal a).comp (by fun_prop)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,σ,hp), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedInverseArmProb_support {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (σ : Measure (ScoreSpace ε)) [IsFiniteMeasure σ]
    (hp : 0 < σ.real univ) :
    (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹))
      (Icc 0 ε⁻¹)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_inverseArmProb a) measurableSet_Icc.compl]
  have hpre : (fun e : ScoreSpace ε => (armProb a e)⁻¹) ⁻¹' (Icc 0 ε⁻¹)ᶜ = ∅ := by
    ext e
    have hb := projectionArmProb_bounds hOverlap a e
    have hpos : 0 < armProb a e := lt_of_lt_of_le hOverlap.1 hb.1
    have hinv : (armProb a e)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hpos hOverlap.1).2 hb.1
    simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false, iff_false]
    exact fun h => h ⟨(inv_pos.mpr hpos).le, hinv⟩
  rw [hpre]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,a,σ,hp), this result [establishes the stated mathematical conclusion](goal). -/
lemma map_normalized_inverseArmProb_eq_finiteNormalize_map {ε : ℝ}
    (a : ArmSpace) (σ : Measure (ScoreSpace ε)) [IsFiniteMeasure σ]
    (hp : 0 < σ.real univ) :
    ((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹) =
      (FiniteMeasure.normalize
        (⟨σ.map (fun e : ScoreSpace ε => (e : ℝ)), inferInstance⟩ :
          FiniteMeasure ℝ) : Measure ℝ).map (projectionInverseArmProbReal a) := by
  have hnorm := map_normalized_subtype_eq_finiteNormalize σ hp
  calc
    ((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹) =
        (((σ univ)⁻¹ • σ).map (fun e : ScoreSpace ε => (e : ℝ))).map
          (projectionInverseArmProbReal a) := by
      rw [Measure.map_map (measurable_projectionInverseArmProbReal a) (by fun_prop)]
      congr 1
      funext e
      exact (projectionInverseArmProbReal_coe a e).symm
    _ = _ := by rw [hnorm]

/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν,A,B,hA,hB,hμ,hν,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma abs_quantile_product_integral_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : μ (Icc 0 A)ᶜ = 0) (hν : ν (Icc 0 B)ᶜ = 0)
    (upper : Bool) :
    |∫ u in (0 : ℝ)..1,
      Causalean.Stat.quantile μ u *
        Causalean.Stat.quantile ν (if upper then u else 1 - u)| ≤ A * B := by
  let s : ℝ → ℝ := if upper then id else fun u => 1 - u
  have hsmeas : Measurable s := by cases upper <;> simp [s] <;> fun_prop
  have hsmap : Causalean.Stat.unifOI.map s = Causalean.Stat.unifOI := by
    cases upper
    · simpa [s] using Causalean.Stat.map_one_sub_unifOI
    · simp [s]
  have hsp : MeasurePreserving s Causalean.Stat.unifOI Causalean.Stat.unifOI :=
    ⟨hsmeas, hsmap⟩
  have hs_apply (u : ℝ) : s u = if upper then u else 1 - u := by
    cases upper <;> rfl
  have hy := Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae μ hμ
  have hw := hsp.quasiMeasurePreserving.tendsto_ae.eventually
    (Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae ν hν)
  have hwae : AEMeasurable (fun u => Causalean.Stat.quantile ν (s u))
      Causalean.Stat.unifOI := by
    have h := Causalean.Stat.aemeasurable_quantile_unifOI ν
    rw [← hsmap] at h
    exact h.comp_measurable hsmeas
  have hprod : Integrable
      (fun u => Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (s u))
      Causalean.Stat.unifOI := by
    apply (integrable_const (A * B)).mono'
    · exact ((Causalean.Stat.aemeasurable_quantile_unifOI μ).mul hwae).aestronglyMeasurable
    · filter_upwards [hy, hw] with u hyu hwu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hyu.1 hwu.1)]
      exact mul_le_mul hyu.2 hwu.2 hwu.1 hA
  have hnonneg : 0 ≤ ∫ u,
      Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (s u)
      ∂Causalean.Stat.unifOI := integral_nonneg_of_ae (by
    filter_upwards [hy, hw] with u hyu hwu
    exact mul_nonneg hyu.1 hwu.1)
  have hupper : (∫ u,
      Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (s u)
      ∂Causalean.Stat.unifOI) ≤ A * B := by
    calc
      _ ≤ ∫ _ : ℝ, A * B ∂Causalean.Stat.unifOI := integral_mono_ae hprod
        (integrable_const (A * B)) (by
          filter_upwards [hy, hw] with u hyu hwu
          exact mul_le_mul hyu.2 hwu.2 hwu.1 hA)
      _ = A * B := by simp
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
    rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
  simp_rw [hs_apply] at hnonneg hupper
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest,
    abs_of_nonneg hnonneg]
  exact hupper

/-- Given [the stated mathematical inputs and assumptions](hyp:p,q,A,A',B,hp,hq,hA,hA'), this result [establishes the stated mathematical conclusion](goal). -/
lemma abs_mass_mul_sub_mass_mul_le {p q A A' B : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA : |A| ≤ B) (hA' : |A'| ≤ B) :
    |p * A - q * A'| ≤ min p q * |A - A'| + B * |p - q| := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq]
    have hid : p * A - q * A' = p * (A - A') + (p - q) * A' := by ring
    rw [hid]
    calc
      _ ≤ |p * (A - A')| + |(p - q) * A'| := abs_add_le _ _
      _ = p * |A - A'| + |p - q| * |A'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp]
      _ ≤ p * |A - A'| + |p - q| * B :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hA' (abs_nonneg _))
      _ = _ := by ring
  · rw [min_eq_right hqp]
    have hid : p * A - q * A' = q * (A - A') + (p - q) * A := by ring
    rw [hid]
    calc
      _ ≤ |q * (A - A')| + |(p - q) * A| := abs_add_le _ _
      _ = q * |A - A'| + |p - q| * |A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq]
      _ ≤ q * |A - A'| + |p - q| * B :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (abs_nonneg _))
      _ = _ := by ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
