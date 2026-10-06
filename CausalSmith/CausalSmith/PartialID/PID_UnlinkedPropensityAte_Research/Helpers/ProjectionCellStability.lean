module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionCellTransport

/-!
Cellwise stability of the quantile product used by the projected arm endpoint.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,upper,μ,μ',σ,σ',hcompat,hcompat',hp,hp'), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedCellSummand_abs_le_of_pos {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (upper : Bool)
    (μ μ' : Measure OutcomeSpace) (σ σ' : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    [IsFiniteMeasure σ] [IsFiniteMeasure σ']
    (hcompat : μ.real univ = σ.real univ)
    (hcompat' : μ'.real univ = σ'.real univ)
    (hp : 0 < μ.real univ) (hp' : 0 < μ'.real univ) :
    |μ.real univ * (∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
          (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))) u *
        Causalean.Stat.quantile
          (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹))
            (if upper then u else 1 - u)) -
      μ'.real univ * (∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
          (((μ' univ)⁻¹ • μ').map (fun y : OutcomeSpace => (y : ℝ))) u *
        Causalean.Stat.quantile
          (((σ' univ)⁻¹ • σ').map (fun e => (armProb a e)⁻¹))
            (if upper then u else 1 - u))| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        (outcomeCDFDistance μ μ' + scoreCDFDistance σ σ') := by
  let Y : Measure ℝ := ((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))
  let Y' : Measure ℝ := ((μ' univ)⁻¹ • μ').map (fun y : OutcomeSpace => (y : ℝ))
  let W : Measure ℝ := ((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹)
  let W' : Measure ℝ := ((σ' univ)⁻¹ • σ').map (fun e => (armProb a e)⁻¹)
  let A : ℝ := ∫ u in (0 : ℝ)..1, Causalean.Stat.quantile Y u *
    Causalean.Stat.quantile W (if upper then u else 1 - u)
  let A' : ℝ := ∫ u in (0 : ℝ)..1, Causalean.Stat.quantile Y' u *
    Causalean.Stat.quantile W' (if upper then u else 1 - u)
  have hσp : 0 < σ.real univ := hcompat ▸ hp
  have hσp' : 0 < σ'.real univ := hcompat' ▸ hp'
  letI : IsProbabilityMeasure Y := by
    dsimp [Y]
    rw [map_normalized_subtype_eq_finiteNormalize μ hp]
    infer_instance
  letI : IsProbabilityMeasure Y' := by
    dsimp [Y']
    rw [map_normalized_subtype_eq_finiteNormalize μ' hp']
    infer_instance
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    rw [map_normalized_inverseArmProb_eq_finiteNormalize_map a σ hσp]
    exact Measure.isProbabilityMeasure_map
      (measurable_projectionInverseArmProbReal a).aemeasurable
  letI : IsProbabilityMeasure W' := by
    dsimp [W']
    rw [map_normalized_inverseArmProb_eq_finiteNormalize_map a σ' hσp']
    exact Measure.isProbabilityMeasure_map
      (measurable_projectionInverseArmProbReal a).aemeasurable
  have hYs : Y (Icc 0 1)ᶜ = 0 := by
    dsimp [Y]
    exact normalizedOutcome_support μ hp
  have hYs' : Y' (Icc 0 1)ᶜ = 0 := by
    dsimp [Y']
    exact normalizedOutcome_support μ' hp'
  have hWs : W (Icc 0 ε⁻¹)ᶜ = 0 := by
    dsimp [W]
    exact normalizedInverseArmProb_support hOverlap a σ hσp
  have hWs' : W' (Icc 0 ε⁻¹)ᶜ = 0 := by
    dsimp [W']
    exact normalizedInverseArmProb_support hOverlap a σ' hσp'
  have hεinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hOverlap.1).le
  have hε2inv : 0 ≤ (ε ^ 2)⁻¹ := by positivity
  have hAb : |A| ≤ ε⁻¹ := by
    dsimp [A]
    simpa using abs_quantile_product_integral_le Y W (by norm_num) hεinv hYs hWs upper
  have hAb' : |A'| ≤ ε⁻¹ := by
    dsimp [A']
    simpa using abs_quantile_product_integral_le Y' W' (by norm_num) hεinv hYs' hWs' upper
  let DY : ℝ := ∫ u in (0 : ℝ)..1,
    |Causalean.Stat.quantile Y u - Causalean.Stat.quantile Y' u|
  let DW : ℝ := ∫ u in (0 : ℝ)..1,
    |Causalean.Stat.quantile W u - Causalean.Stat.quantile W' u|
  let O : ℝ := ∫ t in (0 : ℝ)..1,
    |(μ {y | (y : ℝ) ≤ t}).toReal - (μ' {y | (y : ℝ) ≤ t}).toReal|
  let S : ℝ := ∫ t in ε..(1 - ε),
    |(σ {e | (e : ℝ) ≤ t}).toReal - (σ' {e | (e : ℝ) ≤ t}).toReal|
  let d : ℝ := |μ.real univ - μ'.real univ|
  have hDY : 0 ≤ DY := by
    dsimp [DY]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
  have hDW : 0 ≤ DW := by
    dsimp [DW]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
  have hO : 0 ≤ O := by
    dsimp [O]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact intervalIntegral.integral_nonneg (by linarith [hOverlap.2])
      (fun _ _ => abs_nonneg _)
  have hd : 0 ≤ d := abs_nonneg _
  have hout : min (μ.real univ) (μ'.real univ) * DY ≤ O + d := by
    dsimp [DY, O, d, Y, Y']
    simpa using finite_mass_subtype_quantile_transport_le (by norm_num) μ μ' hp hp'
  have hscore : min (μ.real univ) (μ'.real univ) *
      (∫ u in (0 : ℝ)..1,
        |Causalean.Stat.quantile
            (((σ univ)⁻¹ • σ).map (fun e : ScoreSpace ε => (e : ℝ))) u -
          Causalean.Stat.quantile
            (((σ' univ)⁻¹ • σ').map (fun e : ScoreSpace ε => (e : ℝ))) u|) ≤
      S + (1 - 2 * ε) * d := by
    have h := finite_mass_subtype_quantile_transport_le
      (by linarith [hOverlap.2] : ε ≤ 1 - ε) σ σ' hσp hσp'
    rw [← hcompat, ← hcompat'] at h
    simpa [S, d, sub_sub, two_mul, Measure.map_smul] using h
  have hpush : DW ≤ (ε ^ 2)⁻¹ *
      (∫ u in (0 : ℝ)..1,
        |Causalean.Stat.quantile
            (((σ univ)⁻¹ • σ).map (fun e : ScoreSpace ε => (e : ℝ))) u -
          Causalean.Stat.quantile
            (((σ' univ)⁻¹ • σ').map (fun e : ScoreSpace ε => (e : ℝ))) u|) := by
    dsimp [DW, W, W']
    exact inverseArmProb_quantile_distance_le hOverlap a σ σ' hσp hσp'
  have hwidth : 0 ≤ 1 - 2 * ε ∧ 1 - 2 * ε ≤ 1 := by
    constructor <;> linarith [hOverlap.1, hOverlap.2]
  have hweight : min (μ.real univ) (μ'.real univ) * DW ≤
      (ε ^ 2)⁻¹ * (S + d) := by
    have hmin : 0 ≤ min (μ.real univ) (μ'.real univ) :=
      le_min measureReal_nonneg measureReal_nonneg
    calc
      _ ≤ min (μ.real univ) (μ'.real univ) *
          ((ε ^ 2)⁻¹ * ∫ u in (0 : ℝ)..1,
            |Causalean.Stat.quantile
                (((σ univ)⁻¹ • σ).map (fun e : ScoreSpace ε => (e : ℝ))) u -
              Causalean.Stat.quantile
                (((σ' univ)⁻¹ • σ').map (fun e : ScoreSpace ε => (e : ℝ))) u|) :=
        mul_le_mul_of_nonneg_left hpush hmin
      _ = (ε ^ 2)⁻¹ * (min (μ.real univ) (μ'.real univ) *
          ∫ u in (0 : ℝ)..1,
            |Causalean.Stat.quantile
                (((σ univ)⁻¹ • σ).map (fun e : ScoreSpace ε => (e : ℝ))) u -
              Causalean.Stat.quantile
                (((σ' univ)⁻¹ • σ').map (fun e : ScoreSpace ε => (e : ℝ))) u|) := by ring
      _ ≤ (ε ^ 2)⁻¹ * (S + (1 - 2 * ε) * d) :=
        mul_le_mul_of_nonneg_left hscore hε2inv
      _ ≤ (ε ^ 2)⁻¹ * (S + d) := by
        gcongr
        nlinarith [mul_nonneg hd (sub_nonneg.mpr hwidth.2)]
  have hprod : |A - A'| ≤ ε⁻¹ * DY + DW := by
    dsimp [A, A', DY, DW]
    simpa using quantile_product_integral_stability Y Y' W W'
      (by norm_num) hεinv hYs hYs' hWs hWs' upper
  have hmin : 0 ≤ min (μ.real univ) (μ'.real univ) :=
    le_min measureReal_nonneg measureReal_nonneg
  have hprodScaled : min (μ.real univ) (μ'.real univ) * |A - A'| ≤
      ε⁻¹ * (O + d) + (ε ^ 2)⁻¹ * (S + d) := by
    calc
      _ ≤ min (μ.real univ) (μ'.real univ) * (ε⁻¹ * DY + DW) :=
        mul_le_mul_of_nonneg_left hprod hmin
      _ = ε⁻¹ * (min (μ.real univ) (μ'.real univ) * DY) +
          min (μ.real univ) (μ'.real univ) * DW := by ring
      _ ≤ ε⁻¹ * (O + d) + (ε ^ 2)⁻¹ * (S + d) :=
        add_le_add (mul_le_mul_of_nonneg_left hout hεinv) hweight
  have hscale : |μ.real univ * A - μ'.real univ * A'| ≤
      min (μ.real univ) (μ'.real univ) * |A - A'| +
        ε⁻¹ * |μ.real univ - μ'.real univ| :=
    abs_mass_mul_sub_mass_mul_le
      (p := μ.real univ) (q := μ'.real univ) (A := A) (A' := A')
      (B := ε⁻¹) measureReal_nonneg measureReal_nonneg hAb hAb'
  change |μ.real univ * A - μ'.real univ * A'| ≤ _
  calc
    _ ≤ min (μ.real univ) (μ'.real univ) * |A - A'| +
        ε⁻¹ * |μ.real univ - μ'.real univ| := hscale
    _ ≤ (ε⁻¹ * (O + d) + (ε ^ 2)⁻¹ * (S + d)) + ε⁻¹ * d :=
      add_le_add hprodScaled le_rfl
    _ ≤ (ε⁻¹ + (ε ^ 2)⁻¹) * ((d + O) + (d + S)) := by
      nlinarith [mul_nonneg hεinv hS, mul_nonneg hε2inv hO,
        mul_nonneg hε2inv hd]
    _ = (ε⁻¹ + (ε ^ 2)⁻¹) *
        (outcomeCDFDistance μ μ' + scoreCDFDistance σ σ') := by
      unfold outcomeCDFDistance scoreCDFDistance
      rw [← hcompat, ← hcompat']

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,upper,μ,σ,hcompat,hp), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedCellTerm_abs_le {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (upper : Bool)
    (μ : Measure OutcomeSpace) (σ : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (hcompat : μ.real univ = σ.real univ) (hp : 0 < μ.real univ) :
    |μ.real univ * (∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
          (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))) u *
        Causalean.Stat.quantile
          (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹))
            (if upper then u else 1 - u))| ≤ ε⁻¹ * μ.real univ := by
  let Y : Measure ℝ := ((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))
  let W : Measure ℝ := ((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹)
  have hσp : 0 < σ.real univ := hcompat ▸ hp
  letI : IsProbabilityMeasure Y := by
    dsimp [Y]
    rw [map_normalized_subtype_eq_finiteNormalize μ hp]
    infer_instance
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    rw [map_normalized_inverseArmProb_eq_finiteNormalize_map a σ hσp]
    exact Measure.isProbabilityMeasure_map
      (measurable_projectionInverseArmProbReal a).aemeasurable
  have hY : Y (Icc 0 1)ᶜ = 0 := by
    dsimp [Y]
    exact normalizedOutcome_support μ hp
  have hW : W (Icc 0 ε⁻¹)ᶜ = 0 := by
    dsimp [W]
    exact normalizedInverseArmProb_support hOverlap a σ hσp
  have hI : |∫ u in (0 : ℝ)..1,
      Causalean.Stat.quantile Y u *
        Causalean.Stat.quantile W (if upper then u else 1 - u)| ≤ ε⁻¹ := by
    simpa using abs_quantile_product_integral_le Y W (by norm_num)
      (inv_pos.mpr hOverlap.1).le hY hW upper
  rw [abs_mul, abs_of_pos hp]
  have hmul := mul_le_mul_of_nonneg_left hI hp.le
  dsimp only [Y, W] at hmul
  simpa only [mul_comm] using hmul

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,upper,μ,μ',σ,σ',hcompat,hcompat'), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedCellSummand_abs_le {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (upper : Bool)
    (μ μ' : Measure OutcomeSpace) (σ σ' : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    [IsFiniteMeasure σ] [IsFiniteMeasure σ']
    (hcompat : μ.real univ = σ.real univ)
    (hcompat' : μ'.real univ = σ'.real univ) :
    |(let q := μ.real univ
      if 0 < q then
        q * ∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile
            (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))) u *
          Causalean.Stat.quantile
            (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹))
              (if upper then u else 1 - u)
      else 0) -
     (let q := μ'.real univ
      if 0 < q then
        q * ∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile
            (((μ' univ)⁻¹ • μ').map (fun y : OutcomeSpace => (y : ℝ))) u *
          Causalean.Stat.quantile
            (((σ' univ)⁻¹ • σ').map (fun e => (armProb a e)⁻¹))
              (if upper then u else 1 - u)
      else 0)| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        (outcomeCDFDistance μ μ' + scoreCDFDistance σ σ') := by
  have hL : 0 ≤ ε⁻¹ + (ε ^ 2)⁻¹ :=
    add_nonneg (inv_pos.mpr hOverlap.1).le (by positivity)
  have hout0 := outcomeCDFDistance_nonneg μ μ'
  have hscore0 := scoreCDFDistance_nonneg hOverlap σ σ'
  by_cases hp : 0 < μ.real univ
  · by_cases hp' : 0 < μ'.real univ
    · simpa [hp, hp'] using
        projectedCellSummand_abs_le_of_pos hOverlap a upper μ μ' σ σ'
          hcompat hcompat' hp hp'
    · have hq' : μ'.real univ = 0 := le_antisymm (le_of_not_gt hp') measureReal_nonneg
      simp only [hp, hp', if_true, if_false, sub_zero]
      have hterm := projectedCellTerm_abs_le hOverlap a upper μ σ hcompat hp
      have hmass : μ.real univ ≤ outcomeCDFDistance μ μ' := by
        unfold outcomeCDFDistance
        rw [hq', sub_zero, abs_of_pos hp]
        have hi : 0 ≤ ∫ t in (0 : ℝ)..1,
            |(μ {y | (y : ℝ) ≤ t}).toReal - (μ' {y | (y : ℝ) ≤ t}).toReal| :=
          intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
        linarith
      calc
        _ ≤ ε⁻¹ * μ.real univ := hterm
        _ ≤ (ε⁻¹ + (ε ^ 2)⁻¹) * μ.real univ := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (by positivity : 0 ≤ (ε ^ 2)⁻¹)) hp.le
        _ ≤ (ε⁻¹ + (ε ^ 2)⁻¹) *
            (outcomeCDFDistance μ μ' + scoreCDFDistance σ σ') := by
          gcongr
          linarith
  · have hq : μ.real univ = 0 := le_antisymm (le_of_not_gt hp) measureReal_nonneg
    by_cases hp' : 0 < μ'.real univ
    · simp only [hp, hp', if_true, if_false, zero_sub, abs_neg]
      have hterm := projectedCellTerm_abs_le hOverlap a upper μ' σ' hcompat' hp'
      have hmass : μ'.real univ ≤ outcomeCDFDistance μ μ' := by
        unfold outcomeCDFDistance
        rw [hq, zero_sub, abs_neg, abs_of_pos hp']
        have hi : 0 ≤ ∫ t in (0 : ℝ)..1,
            |(μ {y | (y : ℝ) ≤ t}).toReal - (μ' {y | (y : ℝ) ≤ t}).toReal| :=
          intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)
        linarith
      calc
        _ ≤ ε⁻¹ * μ'.real univ := hterm
        _ ≤ (ε⁻¹ + (ε ^ 2)⁻¹) * μ'.real univ := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (by positivity : 0 ≤ (ε ^ 2)⁻¹)) hp'.le
        _ ≤ (ε⁻¹ + (ε ^ 2)⁻¹) *
            (outcomeCDFDistance μ μ' + scoreCDFDistance σ σ') := by
          gcongr
          linarith
    · simp only [hp, hp', if_true, if_false, sub_self, abs_zero]
      exact mul_nonneg hL (add_nonneg hout0 hscore0)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,lam,lam',σ,σ',hfinLam,hfinLam',hfinσ,hfinσ',hcompat,hcompat',a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedArmEndpoint_abs_le_of_compatible_cells
    {ε : ℝ} {J : ℕ} (hOverlap : Overlap ε)
    (lam lam' : ArmCellArray J OutcomeSpace)
    (σ σ' : ArmCellArray J (ScoreSpace ε))
    (hfinLam : ∀ a r, IsFiniteMeasure (lam a r))
    (hfinLam' : ∀ a r, IsFiniteMeasure (lam' a r))
    (hfinσ : ∀ a r, IsFiniteMeasure (σ a r))
    (hfinσ' : ∀ a r, IsFiniteMeasure (σ' a r))
    (hcompat : ProjectionCompatible lam σ)
    (hcompat' : ProjectionCompatible lam' σ')
    (a : ArmSpace) (upper : Bool) :
    |projectedArmEndpoint lam σ a upper -
      projectedArmEndpoint lam' σ' a upper| ≤
      (ε⁻¹ + (ε ^ 2)⁻¹) *
        ((∑ r : LabelSpace J, outcomeCDFDistance (lam a r) (lam' a r)) +
          ∑ r : LabelSpace J, scoreCDFDistance (σ a r) (σ' a r)) := by
  apply projectedArmEndpoint_abs_le_of_cellBounds lam lam' σ σ' a upper
    (ε⁻¹ + (ε ^ 2)⁻¹)
  intro r
  letI : IsFiniteMeasure (lam a r) := hfinLam a r
  letI : IsFiniteMeasure (lam' a r) := hfinLam' a r
  letI : IsFiniteMeasure (σ a r) := hfinσ a r
  letI : IsFiniteMeasure (σ' a r) := hfinσ' a r
  exact projectedCellSummand_abs_le hOverlap a upper
    (lam a r) (lam' a r) (σ a r) (σ' a r)
    (hcompat a r) (hcompat' a r)
end
end CausalSmith.PartialID.UnlinkedPropensityAte
