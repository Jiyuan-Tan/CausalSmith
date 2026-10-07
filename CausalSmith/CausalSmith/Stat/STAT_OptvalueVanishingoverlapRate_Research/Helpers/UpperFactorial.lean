module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperClipping
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotMoments
public import Causalean.Stat.Concentration.Poisson.FactorialProduct
public import Mathlib.Probability.Moments.Variance

/-! # Localized factorial moments

Roadmap equations (23)–(26) connect independent Poisson factorial moments to
actual pilot rectangles and the centered Jackson factorial statistic.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped BigOperators

/-- Positive pilot level gives strictly positive coordinate radii, even at zero counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotRadius_pos (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    0 < pilotRadiusFormula H hH m L Np j := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by unfold pilotCenterFormula; positivity
  have hh : 0 < pilotHalfWidthFormula H hH m L Np j := by
    unfold pilotHalfWidthFormula
    exact mul_pos hH (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (div_pos hL hm))
  dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
  rw [max_def]
  split_ifs <;> linarith

/-- Membership in the pilot interval is precisely the centering condition for the normalized factorial envelope, including a lower endpoint truncated at zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hq), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_center_bound (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (Np : Fin 4 → ℕ) (q : Fin 4 → ℝ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (j : Fin 4) :
    |q j - pilotMidpoint H hH m L Np j| ≤ pilotRadiusFormula H hH m L Np j := by
  have hj := hq j
  apply abs_le.mpr
  dsimp [pilotMidpoint, pilotRadiusFormula]
  constructor <;> linarith [hj.1, hj.2]

-- @node: cellFactorial_mixed_moment
/-- Equation (23) specializes the exact mixed factorial identity to intensity m q. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hm,hq), the [stated conclusion](goal) holds. -/
lemma cellFactorial_mixed_moment (m q b : ℝ) (hm : 0 < m) (hq : 0 ≤ q)
    (h t : ℕ) :
    (∫ N : ℕ, factorialLift m b N h * factorialLift m b N t
      ∂poissonMeasure ⟨m * q, mul_nonneg hm.le hq⟩) =
      ∑ l ∈ Finset.range (min h t + 1),
        (h.choose l : ℝ) * (t.choose l : ℝ) * (Nat.factorial l : ℝ) *
          (q / m) ^ l * (q - b) ^ (h + t - 2 * l) := by
  have hmean : m * q / m = q := mul_div_cancel_left₀ q (ne_of_gt hm)
  have hvar : m * q / m ^ 2 = q / m := by field_simp
  have hx := poisson_factorialLift_mixed ⟨m * q, mul_nonneg hm.le hq⟩ m b (ne_of_gt hm) h t
  change (∫ N : ℕ, factorialLift m b N h * factorialLift m b N t
      ∂poissonMeasure ⟨m * q, mul_nonneg hm.le hq⟩) =
      ∑ l ∈ Finset.range (min h t + 1),
        (h.choose l : ℝ) * (t.choose l : ℝ) * (Nat.factorial l : ℝ) *
          (m * q / m ^ 2) ^ l * (m * q / m - b) ^ (h + t - 2 * l) at hx
  simpa only [hmean, hvar] using hx

/-- Equations (24)–(25) give the four-coordinate exponential envelope on the actual pilot rectangle. The factor eight comes from the pilot variance bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hdegree), the [stated conclusion](goal) holds. -/
lemma pilotFactorialProduct_square_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (h : Fin 4 → ℕ) (D : ℕ) (hdegree : ∀ j, h j ≤ D) :
    (∫ ω, (∏ j, factorialLift m (pilotMidpoint H hH m L Np j) (W j ω) (h j) /
        pilotRadiusFormula H hH m L Np j ^ h j) ^ 2 ∂μ) ≤
      Real.exp (32 * (D : ℝ) ^ 2 / L) := by
  have hc (j : Fin 4) :
      |(m * q j) / m - pilotMidpoint H hH m L Np j| ≤ pilotRadiusFormula H hH m L Np j := by
    rw [mul_div_cancel_left₀ _ (ne_of_gt hm)]
    exact pilotRectangle_center_bound H hH m L Np q hq j
  have hv (j : Fin 4) :
      (m * q j) / (m ^ 2 * pilotRadiusFormula H hH m L Np j ^ 2) ≤ 1 / (L / 8) := by
    have he : (m * q j) / (m ^ 2 * pilotRadiusFormula H hH m L Np j ^ 2) =
        q j / (m * pilotRadiusFormula H hH m L Np j ^ 2) := by field_simp
    rw [he, show (1 : ℝ) / (L / 8) = 8 / L by ring]
    exact pilotRadius_variance_bound H hH hHlarge m L hm hL Np j (q j) (hq j).2
  have hb := factorialProduct_four_square_envelope μ W
    (fun j => ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) hWlaw hind m (L / 8)
    hm (by positivity) (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
    (pilotRadius_pos H hH m L hm hL Np) hc hv h D hdegree
  simpa only [factorialProduct, Finset.prod_div_distrib,
    show 4 * (D : ℝ) ^ 2 / (L / 8) = 32 * (D : ℝ) ^ 2 / L by ring] using hb

-- @node: cellFactorial_square_integrable
/-- Every scalar factorial lift has an integrable square under a Poisson law. This regularity is derived from raw factorial moments, rather than assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma cellFactorial_square_integrable (rate : NNReal) (m b : ℝ) (h : ℕ) :
    Integrable (fun N : ℕ => (factorialLift m b N h) ^ 2) (poissonMeasure rate) := by
  have hraw (j k : ℕ) : Integrable (fun N : ℕ =>
      (N.descFactorial j : ℝ) * (N.descFactorial k : ℝ)) (poissonMeasure rate) := by
    have hi := integrable_finsetSum (Finset.range (min j k + 1))
      (fun l _ => (poisson_descFactorial_integrable rate (j + k - l)).const_mul
        ((j.choose l : ℝ) * (k.choose l : ℝ) * (Nat.factorial l : ℝ)))
    have he : (fun N : ℕ => (N.descFactorial j : ℝ) * (N.descFactorial k : ℝ)) =
        (fun N : ℕ => ∑ l ∈ Finset.range (min j k + 1),
          (j.choose l : ℝ) * (k.choose l : ℝ) * (Nat.factorial l : ℝ) *
            (N.descFactorial (j + k - l) : ℝ)) := by
      funext N
      exact descFactorial_mul N j k
    rw [he]
    exact hi
  have hi := integrable_finsetSum (Finset.range (h + 1)) (fun j _ =>
    integrable_finsetSum (Finset.range (h + 1)) (fun k _ =>
      (hraw j k).const_mul (((h.choose j : ℝ) * (-b) ^ (h - j) / m ^ j) *
        ((h.choose k : ℝ) * (-b) ^ (h - k) / m ^ k))))
  have he : (fun N : ℕ => (factorialLift m b N h) ^ 2) =
      (fun N : ℕ => ∑ j ∈ Finset.range (h + 1), ∑ k ∈ Finset.range (h + 1),
        (((h.choose j : ℝ) * (-b) ^ (h - j) / m ^ j) *
          ((h.choose k : ℝ) * (-b) ^ (h - k) / m ^ k)) *
            ((N.descFactorial j : ℝ) * (N.descFactorial k : ℝ))) := by
    funext N
    simp only [factorialLift, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact hi

-- @node: cellFactorialProduct_memLp_two
/-- Independent Poisson coordinates make every normalized factorial monomial L². No integrability premise is needed for the subsequent polynomial assembly. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hWlaw,hind), the [stated conclusion](goal) holds. -/
lemma cellFactorialProduct_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (rate : Fin 4 → NNReal)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure (rate j)) μ)
    (hind : iIndepFun W μ) (m : ℝ) (b r : Fin 4 → ℝ) (h : Fin 4 → ℕ) :
    MemLp (fun ω => ∏ j, factorialLift m (b j) (W j ω) (h j) / r j ^ h j) 2 μ := by
  let f (j : Fin 4) (N : ℕ) : ℝ := (factorialLift m (b j) N (h j) / r j ^ h j) ^ 2
  have hf (j : Fin 4) : Integrable (f j) (poissonMeasure (rate j)) := by
    simpa only [f, div_pow] using
      (cellFactorial_square_integrable (rate j) m (b j) (h j)).div_const ((r j ^ h j) ^ 2)
  have hpi := Integrable.fintype_prod hf
  have hmap : μ.map (fun ω j => W j ω) = Measure.pi (fun j => poissonMeasure (rate j)) := by
    rw [hind.map_fun_eq_pi_map (fun j => (hWlaw j).aemeasurable)]
    congr 1
    funext j
    exact (hWlaw j).map_eq
  have hmeas : AEMeasurable (fun ω j => W j ω) μ :=
    aemeasurable_pi_lambda _ (fun j => (hWlaw j).aemeasurable)
  have hsq : Integrable (fun ω => (∏ j, factorialLift m (b j) (W j ω) (h j) /
      r j ^ h j) ^ 2) μ := by
    have hcomp := (hmap ▸ hpi).comp_aemeasurable hmeas
    convert hcomp using 1
    funext ω
    simp only [Function.comp_apply, f, Finset.prod_pow]
  have ha : AEStronglyMeasurable (fun ω => ∏ j,
      factorialLift m (b j) (W j ω) (h j) / r j ^ h j) μ := by
    exact ((Measurable.of_discrete : Measurable (fun v : Fin 4 → ℕ =>
      ∏ j, factorialLift m (b j) (v j) (h j) / r j ^ h j)).comp_aemeasurable
        hmeas).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq ha).2 hsq

-- @node: factorialCellValue_memLp_two
/-- The actual Jackson factorial statistic is square-integrable under the independent Poisson experiment. This derives all regularity needed for clipping. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hWlaw,hind), the [stated conclusion](goal) holds. -/
lemma factorialCellValue_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (rate : Fin 4 → NNReal)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure (rate j)) μ)
    (hind : iIndepFun W μ) (ε : ℝ) (K : ℕ) (m : ℝ) (b r : Fin 4 → ℝ) :
    MemLp (fun ω => factorialCellValue ε K m b r (fun j => W j ω)) 2 μ := by
  have hmono (α : Fin 4 → Fin (2 * (K - 1) + 1)) :=
    (cellFactorialProduct_memLp_two μ W rate hWlaw hind m b r
      (fun j => (α j).val)).const_mul (jacksonCoeff ε K b r α)
  exact (memLp_const (armwiseExtensionFormula ε b)).add
    (memLp_finsetSum Finset.univ (fun α _ => hmono α))

-- @node: factorialCellValue_centered_square_integrable
/-- Centering the factorial cell statistic at any fixed value preserves L², so its second moments exist without extra integrability assumptions. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hWlaw,hind), the [stated conclusion](goal) holds. -/
lemma factorialCellValue_centered_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (rate : Fin 4 → NNReal)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure (rate j)) μ)
    (hind : iIndepFun W μ) (ε : ℝ) (K : ℕ) (m : ℝ) (b r : Fin 4 → ℝ) (p : ℝ) :
    Integrable (fun ω =>
      (factorialCellValue ε K m b r (fun j => W j ω) - p) ^ 2) μ := by
  exact ((factorialCellValue_memLp_two μ W rate hWlaw hind ε K m b r).sub
    (memLp_const p)).integrable_sq

/-- The actual factorial cell statistic is unbiased for evaluation of its centered Jackson monomial expansion at the Poisson mean (roadmap equation (23)). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hWlaw,hind,hm), the [stated conclusion](goal) holds. -/
lemma factorialCellValue_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (rate : Fin 4 → NNReal)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure (rate j)) μ)
    (hind : iIndepFun W μ) (ε : ℝ) (K : ℕ) (m : ℝ) (hm : m ≠ 0)
    (b r : Fin 4 → ℝ) :
    (∫ ω, factorialCellValue ε K m b r (fun j => W j ω) ∂μ) =
      armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
        jacksonCoeff ε K b r α * ∏ j, (((rate j : ℝ) / m - b j) / r j) ^ (α j).val := by
  have hX (α : Fin 4 → Fin (2 * (K - 1) + 1)) :=
    (cellFactorialProduct_memLp_two μ W rate hWlaw hind m b r (fun j => (α j).val)).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
  simp only [factorialCellValue]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun α _ =>
    (hX α).const_mul _)), integral_const, probReal_univ, one_smul,
    integral_finsetSum _ (fun α _ => (hX α).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [integral_const_mul]
  congr 1
  simp only [Finset.prod_div_distrib]
  rw [integral_div]
  change (∫ ω, factorialProduct W m b (fun j => (α j).val) ω ∂μ) / _ = _
  rw [factorialProduct_mean μ W rate hWlaw hind m]
  simp only [Finset.prod_div_distrib, div_pow]

-- @node: centeredClip_integral_sq_mean_le
/-- Clipping around a fixed center contracts squared error at the unclipped mean when that mean lies in the clipping interval. Its risk is bounded by the original second moment around the fixed center, as in roadmap equation (28). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hZ,hmean), the [stated conclusion](goal) holds. -/
lemma centeredClip_integral_sq_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (c A : ℝ)
    (hA : 0 ≤ A) (hZ : MemLp Z 2 μ)
    (hmean : |(∫ ω, Z ω ∂μ) - c| ≤ A) :
    (∫ ω, (max (c - A) (min (c + A) (Z ω)) - ∫ v, Z v ∂μ) ^ 2 ∂μ) ≤
      ∫ ω, (Z ω - c) ^ 2 ∂μ := by
  have hpoint (ω : Ω) :
      (max (c - A) (min (c + A) (Z ω)) - ∫ v, Z v ∂μ) ^ 2 ≤
        (Z ω - ∫ v, Z v ∂μ) ^ 2 := by
    rw [centeredClip_eq]
    have h := Causalean.Stat.Sample.Stratified.TreatmentRegression.clip_sq_error_le A (Z ω - c) ((∫ v, Z v ∂μ) - c)
      hA (abs_le.mp hmean)
    convert h using 1 <;> congr 1 <;> ring
  calc
    _ ≤ ∫ ω, (Z ω - ∫ v, Z v ∂μ) ^ 2 ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
        ((hZ.sub (memLp_const _)).integrable_sq) (ae_of_all _ hpoint)
    _ = ProbabilityTheory.variance Z μ :=
      (ProbabilityTheory.variance_eq_integral hZ.aemeasurable).symm
    _ = ProbabilityTheory.variance (fun ω => Z ω - c) μ :=
      (ProbabilityTheory.variance_sub_const hZ.aestronglyMeasurable c).symm
    _ ≤ _ := ProbabilityTheory.variance_le_expectation_sq
      ((hZ.sub (memLp_const c)).aestronglyMeasurable)

/-- At intensities m times q, the factorial statistic has exactly the centered Jackson polynomial as its expectation, with the intensity normalization canceled. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hm,hWlaw,hind), the [stated conclusion](goal) holds. -/
lemma factorialCellValue_integral_eq_scaled {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j) (m : ℝ) (hm : 0 < m)
    (hWlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ) (ε : ℝ) (K : ℕ) (b r : Fin 4 → ℝ) :
    (∫ ω, factorialCellValue ε K m b r (fun j => W j ω) ∂μ) =
      armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
        jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val := by
  rw [factorialCellValue_integral_eq μ W _ hWlaw hind ε K m (ne_of_gt hm)]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  change ((m * q j / m - b j) / r j) ^ (α j).val = _
  rw [mul_div_cancel_left₀ _ (ne_of_gt hm)]

-- @node: factorialPolynomial_square_envelope
/-- Summing normalized monomials costs the square of the coefficient ℓ¹ norm, rather than an extra alphabet factor. This is the finite polynomial step of (26). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hX,hmom), the [stated conclusion](goal) holds. -/
lemma factorialPolynomial_square_envelope {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (β : ι → ℝ) (X : ι → Ω → ℝ) (B : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hmom : ∀ i, (∫ ω, (X i ω) ^ 2 ∂μ) ≤ B) :
    (∫ ω, (∑ i, β i * X i ω) ^ 2 ∂μ) ≤ (∑ i, |β i|) ^ 2 * B := by
  have hpoint (ω : Ω) : (∑ i, β i * X i ω) ^ 2 ≤
      (∑ i, |β i|) * ∑ i, |β i| * (X i ω) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => abs_nonneg (β i)) (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro i _
    apply le_of_eq
    rw [mul_pow, ← sq_abs (β i)]
    ring
  have hs : Integrable (fun ω => (∑ i, |β i|) * ∑ i, |β i| * (X i ω) ^ 2) μ :=
    (integrable_finsetSum _ (fun i _ => (hX i).integrable_sq.const_mul _)).const_mul _
  calc
    _ ≤ ∫ ω, (∑ i, |β i|) * ∑ i, |β i| * (X i ω) ^ 2 ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hs (ae_of_all _ hpoint)
    _ = (∑ i, |β i|) * ∑ i, |β i| * (∫ ω, (X i ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hX i).integrable_sq.const_mul _)]
      simp only [integral_const_mul]
    _ ≤ (∑ i, |β i|) * ∑ i, |β i| * B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmom i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- On the localized pilot rectangle, equation (26) holds for the estimator's actual centered factorial cell statistic, with its explicit coefficient norm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq), the [stated conclusion](goal) holds. -/
lemma pilotFactorialCellValue_square_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (K : ℕ) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    (∫ ω, (factorialCellValue ε K m b r (fun j => W j ω) - armwiseExtensionFormula ε b) ^ 2 ∂μ) ≤
      (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ^ 2 *
        Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / L) := by
  dsimp only
  simp only [factorialCellValue, add_sub_cancel_left]
  apply factorialPolynomial_square_envelope
  · intro α
    exact cellFactorialProduct_memLp_two μ W _ hWlaw hind m
      (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) (fun j => (α j).val)
  · intro α
    exact pilotFactorialProduct_square_envelope μ W q hqnonneg H hH hHlarge m L hm hL
      Np hWlaw hind hq (fun j => (α j).val) (2 * (K - 1))
      (fun j => Nat.le_of_lt_succ (α j).isLt)

/-- Combining the exact Poisson mean, derived L² regularity, the localized factorial envelope, and clipping displacement proves the bias transfer in (28) for the actual statistic. The coefficient norm remains explicit for (14). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hwidth), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_bias_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j) (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (K d : ℕ)
    (hwidth : 0 < (d : ℝ) ^ (1 / 4 : ℝ) *
      clippingScaleFormula ε (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    |(∫ ω, clippedCellValueFormula ε K d m b r (fun j => W j ω) ∂μ) -
      (armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
        jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val)| ≤
      ((∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ^ 2 *
        Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / L)) /
        ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r) := by
  dsimp only
  have hmean' := factorialCellValue_integral_eq_scaled μ W q hqnonneg m hm
    hWlaw hind ε K (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
  have hreg := factorialCellValue_memLp_two μ W _ hWlaw hind ε K m
    (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
  have hsecond := factorialCellValue_centered_square_integrable μ W _ hWlaw hind ε K m
    (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
    (armwiseExtensionFormula ε (pilotMidpoint H hH m L Np))
  have hb := clippedCellValue_integral_bias_le μ (fun ω j => W j ω) ε K d m
    (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) _ hwidth
    (hreg.integrable (by norm_num)) hmean' hsecond
  exact hb.trans (div_le_div_of_nonneg_right
    (pilotFactorialCellValue_square_envelope μ W q hqnonneg H hH hHlarge m L hm hL
      Np hWlaw hind hq ε K) hwidth.le)

/-- On a localized pilot rectangle, clipping the actual Poisson factorial statistic preserves the second-moment envelope around its exact polynomial mean provided that mean lies in the clipping interval. The coefficient norm remains explicit; this is the contraction step of the second assertion of equation (28). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_square_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (K d : ℕ) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val
    0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r →
    |p - armwiseExtensionFormula ε b| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r →
    (∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) ≤
      (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ^ 2 *
        Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / L) := by
  dsimp only
  intro hwidth hp
  have hmean := factorialCellValue_integral_eq_scaled μ W q hqnonneg m hm
    hWlaw hind ε K (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
  have hreg := factorialCellValue_memLp_two μ W _ hWlaw hind ε K m
    (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)
  have hclip := centeredClip_integral_sq_mean_le μ
    (fun ω => factorialCellValue ε K m
      (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) (fun j => W j ω))
    (armwiseExtensionFormula ε (pilotMidpoint H hH m L Np))
    ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε
      (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np))
    hwidth hreg (by simpa only [hmean] using hp)
  simp only [hmean] at hclip
  exact hclip.trans (pilotFactorialCellValue_square_envelope μ W q hqnonneg
    H hH hHlarge m L hm hL Np hWlaw hind hq ε K)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
