module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.ArmwiseExtension
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Observable capped-Poisson Jackson factorial estimator

The final estimator is a finite sum over counts and marks. The Jackson polynomial
is selected from the canonical tensor convolution representation.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory Filter Causalean.Mathlib.Analysis.JacksonApproximation
open scoped BigOperators Topology

/-- For the displayed parameters, sampleCellCount is the object specified by this definition. -/
 def sampleCellCount {n d : ℕ} (o : Fin n → Obs d) (x : Fin d) : ℕ := ∑ i, if (o i).1 = x then 1 else 0 -- @realizes \(N_x\)(full-sample cell count) 
/-- For the displayed parameters, sampleArmCount is the object specified by this definition. -/
 def sampleArmCount {n d : ℕ} (o : Fin n → Obs d) (x : Fin d) (a : Bool) : ℕ := ∑ i, if (o i).1 = x ∧ (o i).2.1 = a then 1 else 0 -- @realizes \(N_{ax}\)(full-sample arm count) 
/-- For the displayed parameters, sampleSuccessCount is the object specified by this definition. -/
 def sampleSuccessCount {n d : ℕ} (o : Fin n → Obs d) (x : Fin d) (a : Bool) : ℕ := ∑ i, if (o i).1 = x ∧ (o i).2.1 = a ∧ (o i).2.2 then 1 else 0 -- @realizes \(S_{ax}\)(full-sample successes) 
/-- For the displayed parameters, projectUnit is the object specified by this definition. -/
 def projectUnit (z : ℝ) : ℝ := max 0 (min 1 z) 
/-- For the displayed parameters, empiricalValue is the object specified by this definition. -/
 noncomputable def empiricalValue {n d : ℕ} (o : Fin n → Obs d) : ℝ := projectUnit <| ∑ x : Fin d, (sampleCellCount o x : ℝ) / n * max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false) ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true) 
/-- For the displayed parameters, jacksonDegree is the object specified by this definition. -/
 noncomputable def jacksonDegree (κ : ℝ) (d : ℕ) : ℕ := max 2 ⌊κ * logAlphabet d⌋₊ -- @realizes \(K_n\)(degree max two) 
/-- For the displayed parameters, poissonIntensityFormula is the object specified by this definition. -/
 noncomputable def poissonIntensityFormula (n : ℕ) : ℝ := n / 8 
/-- For the displayed parameters, markedCount is the object specified by this definition. -/
 def markedCount {n d k : ℕ} (hk : k ≤ n) (o : Fin n → Obs d) (marks : Fin k → Bool) (pilot : Bool) (x : Fin d) (j : Fin 4) : ℕ := ∑ i : Fin k, if marks i = pilot ∧ o ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ = (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)) then 1 else 0 -- @realizes \(\mathsf B_i\)(fair marks) @realizes \(N'_{ay,x}\)(pilot count) -- @realizes \(N_{ay,x}\)(evaluation count) 
/-- For the displayed parameters, pilotCenterFormula is the object specified by this definition. -/
 noncomputable def pilotCenterFormula (m : ℝ) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := (Np j : ℝ) / m 
/-- For the displayed parameters, pilotHalfWidthFormula is the object specified by this definition. -/
 noncomputable def pilotHalfWidthFormula (H₀ : ℝ) (_hH₀ : 0 < H₀) (m L : ℝ) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := H₀ * (Real.sqrt (pilotCenterFormula m Np j * L / m) + L / m) 
/-- For the displayed parameters, pilotLower is the object specified by this definition. -/
 noncomputable def pilotLower (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := max 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H₀ hH₀ m L Np j) -- @realizes \(\ell_{ay,x}\)(rectangle lower endpoint) 
/-- For the displayed parameters, pilotUpperFormula is the object specified by this definition. -/
 noncomputable def pilotUpperFormula (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := pilotCenterFormula m Np j + pilotHalfWidthFormula H₀ hH₀ m L Np j 
/-- Pilot empirical mass on the paper's positive intensity domain. For the displayed parameters, pilotCenter is the object specified by this definition. -/
 noncomputable def pilotCenter (m : ℝ) (_hm : 0 < m) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := (Np j : ℝ) / m -- @realizes \(c_{ay,x}\)(pilot category mass; m>0) 
/-- Pilot half-width with all positive calibration inputs explicit. For the displayed parameters, pilotHalfWidth is the object specified by this definition. -/
 noncomputable def pilotHalfWidth (H₀ : ℝ) (_hH₀ : 0 < H₀) (m L : ℝ) (hm : 0 < m) (_hL : 0 < L) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := H₀ * (Real.sqrt (pilotCenter m hm Np j * L / m) + L / m) -- @realizes \(h_{ay,x}\)(pilot half width; H₀,m,L>0) -- @realizes \(H_0\)(positive universal width) 
/-- Pilot upper endpoint on the positive width and intensity domain. For the displayed parameters, pilotUpper is the object specified by this definition. -/
 noncomputable def pilotUpper (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ) (j : Fin 4) : ℝ := pilotCenter m hm Np j + pilotHalfWidth H₀ hH₀ m L hm hL Np j -- @realizes \(u_{ay,x}\)(rectangle upper endpoint; H₀,m,L>0) 
/-- For the displayed parameters, pilotMidpoint is the object specified by this definition. -/
 noncomputable def pilotMidpoint (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (Np : Fin 4 → ℕ) : Fin 4 → ℝ := fun j => (pilotLower H₀ hH₀ m L Np j + pilotUpperFormula H₀ hH₀ m L Np j) / 2 -- @realizes \(b_x\)(pilot rectangle center) 
/-- For the displayed parameters, pilotRadiusFormula is the object specified by this definition. -/
 noncomputable def pilotRadiusFormula (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (Np : Fin 4 → ℕ) : Fin 4 → ℝ := fun j => (pilotUpperFormula H₀ hH₀ m L Np j - pilotLower H₀ hH₀ m L Np j) / 2 
/-- For the displayed parameters, pilotRectangle is the object specified by this definition. -/
 def pilotRectangle (lo hi : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {v | ∀ j, v j ∈ Set.Icc (lo j) (hi j)} -- @realizes \(Q_x\)(pilot rectangle) 
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hr,hQ), the [stated conclusion](goal) holds. -/
lemma armwise_continuousOn_rectangle (ε : ℝ) (hε : 0 < ε)
    (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r,
      ∀ j, 0 ≤ v j) :
    ContinuousOn (armwiseExtensionFormula ε)
      (Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r) := by
  let Q := Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r
  intro v hv
  have hvpos : ∀ j, 0 ≤ v j := hQ v hv
  by_cases hv0 : v = 0
  · have hmass : ContinuousAt totalMassVecFormula v := by
      unfold totalMassVecFormula armMassVecFormula
      fun_prop
    have hmass0 : totalMassVecFormula v = 0 := by simp [hv0, totalMassVecFormula, armMassVecFormula]
    have ht : Tendsto totalMassVecFormula (𝓝[Q] v) (𝓝 (0 : ℝ)) := by
      simpa [hmass0] using hmass.tendsto.mono_left nhdsWithin_le_nhds
    have hlow : ∀ᶠ u in 𝓝[Q] v, (0 : ℝ) ≤ armwiseExtensionFormula ε u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (armwiseExtension_nonneg_le_totalMassVec hε (hQ u hu)).1
    have hhigh : ∀ᶠ u in 𝓝[Q] v, armwiseExtensionFormula ε u ≤ totalMassVecFormula u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (armwiseExtension_nonneg_le_totalMassVec hε (hQ u hu)).2
    simpa [ContinuousWithinAt, hv0, armwiseExtensionFormula] using
      (tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds ht hlow hhigh)
  · have hs : 0 < totalMassVecFormula v := by
      have h := totalMassVec_pos_of_nonzero hvpos hv0
      exact h
    have hden (a : Bool) : anchoredDenomFormula ε v a ≠ 0 := by
      have := lt_of_lt_of_le (mul_pos hε hs)
        (le_max_right (armMassVecFormula v a) (ε * totalMassVecFormula v))
      exact ne_of_gt this
    have hform : ContinuousAt (fun u : Fin 4 → ℝ =>
        max (totalMassVecFormula u * u (cellIdx false true) / anchoredDenomFormula ε u false)
          (totalMassVecFormula u * u (cellIdx true true) / anchoredDenomFormula ε u true)) v := by
      have ht : ContinuousAt totalMassVecFormula v := by
        unfold totalMassVecFormula armMassVecFormula
        fun_prop
      have ha (a : Bool) : ContinuousAt (anchoredDenomFormula ε · a) v := by
        dsimp [anchoredDenomFormula, armMassVecFormula, totalMassVecFormula]
        fun_prop
      have hf (a : Bool) : ContinuousAt
          (fun u : Fin 4 → ℝ => totalMassVecFormula u * u (cellIdx a true) /
            anchoredDenomFormula ε u a) v := by
        exact (ht.mul (continuousAt_apply (cellIdx a true) v)).div (ha a) (hden a)
      exact (hf false).max (hf true)
    have hev : ∀ᶠ u : Fin 4 → ℝ in 𝓝 v, u ≠ 0 :=
      eventually_ne_nhds hv0
    have heq : (armwiseExtensionFormula ε) =ᶠ[𝓝[Q] v]
        (fun u : Fin 4 → ℝ =>
          max (totalMassVecFormula u * u (cellIdx false true) / anchoredDenomFormula ε u false)
            (totalMassVecFormula u * u (cellIdx true true) / anchoredDenomFormula ε u true)) := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with u hu
      simp [armwiseExtensionFormula, hu]
    have hgoal := hform.continuousWithinAt.congr_of_eventuallyEq heq
    exact hgoal (by simp [armwiseExtensionFormula, hv0])

/-- For the displayed parameters, jacksonPolynomialPair is the object specified by this definition. -/
noncomputable def jacksonPolynomialPair (ε : ℝ) (K : ℕ) (c r : Fin 4 → ℝ) :
    MvPolynomial (Fin 4) ℝ × MvPolynomial (Fin 4) ℝ := by
  classical
  exact if hK : 0 < K then
    if hε : 0 < ε then
      if hr : ∀ j, 0 < r j then
        if hQ : ∀ v ∈
            Causalean.Mathlib.Analysis.JacksonApproximation.centeredRectangle c r,
            ∀ j, 0 ≤ v j then
          let h := affineJackson_exists_mvPolynomial_four hK c r hr
            (armwiseExtensionFormula ε) (armwise_continuousOn_rectangle ε hε c r hr hQ)
          (Classical.choose h, Classical.choose (Classical.choose_spec h))
        else (0, 0)
      else (0, 0)
    else (0, 0)
  else (0, 0)
  -- @realizes \(P_{x,K_n}\)(tensor Jackson polynomial)
/-- For the displayed parameters, jacksonCoeff is the object specified by this definition. -/
 noncomputable def jacksonCoeff (ε : ℝ) (K : ℕ) (c r : Fin 4 → ℝ) (α : Fin 4 → Fin (2 * (K - 1) + 1)) : ℝ := Causalean.Mathlib.Analysis.Approximation.Chebyshev.tensorCoeffs ((jacksonPolynomialPair ε K c r).2 - MvPolynomial.C (armwiseExtensionFormula ε c)) α -- @realizes \(\boldsymbol\alpha\)(four-coordinate multi-index) -- @realizes \(\beta_{x,\boldsymbol\alpha}\)(centered coefficient) 
/-- For the displayed parameters, factorialCellValue is the object specified by this definition. -/
 noncomputable def factorialCellValue (ε : ℝ) (K : ℕ) (m : ℝ) (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) : ℝ := armwiseExtensionFormula ε c + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1), jacksonCoeff ε K c r α * ∏ j : Fin 4, Causalean.Stat.Concentration.Poisson.factorialLift m (c j) (Ne j) (α j).val / (r j) ^ (α j).val -- @realizes \(U_k(N;\zeta)\)(Poisson factorial lift) -- @realizes \(Z_x\)(unclipped cell statistic) 
/-- For the displayed parameters, armRadiusFormula is the object specified by this definition. -/
 noncomputable def armRadiusFormula (r : Fin 4 → ℝ) (a : Bool) : ℝ := r (cellIdx a false) + r (cellIdx a true) 
/-- For the displayed parameters, armWeightFormula is the object specified by this definition. -/
 noncomputable def armWeightFormula (ε : ℝ) (c : Fin 4 → ℝ) (a : Bool) : ℝ := 1 + totalMassVecFormula c / anchoredDenomFormula ε c a 
/-- For the displayed parameters, clippingScaleFormula is the object specified by this definition. -/
 noncomputable def clippingScaleFormula (ε : ℝ) (c r : Fin 4 → ℝ) : ℝ := 2 * ∑ a : Bool, armWeightFormula ε c a * armRadiusFormula r a 
/-- For the displayed parameters, clippedCellValueFormula is the object specified by this definition. -/
noncomputable def clippedCellValueFormula (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) : ℝ :=
  let center := armwiseExtensionFormula ε c
  let width := (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r
  max (center - width) (min (center + width) (factorialCellValue ε K m c r Ne))
/-- For the displayed parameters, cappedStatisticFormula is the object specified by this definition. -/
noncomputable def cappedStatisticFormula {n d k : ℕ} (hk : k ≤ n) (H₀ : ℝ)
    (hH₀ : 0 < H₀) (κ ε : ℝ) (o : Fin n → Obs d) (marks : Fin k → Bool) : ℝ :=
  let m := poissonIntensityFormula n
  let L := logAlphabet d
  let K := jacksonDegree κ d
  projectUnit <| ∑ x : Fin d,
    let Np := markedCount hk o marks true x
    let Ne := markedCount hk o marks false x
    let c := pilotMidpoint H₀ hH₀ m L Np
    let r := pilotRadiusFormula H₀ hH₀ m L Np
    clippedCellValueFormula ε K d m c r Ne
/-- For the displayed parameters, poissonWeight is the object specified by this definition. -/
 noncomputable def poissonWeight (rate : ℝ) (k : ℕ) : ℝ := Real.exp (-rate) * rate ^ k / (k.factorial : ℝ) -- @realizes \(\mathsf M\)(Pois(n/4) count weight) 
/-- For the displayed parameters, armwiseEstimatorFormula is the object specified by this definition. -/
 noncomputable def armwiseEstimatorFormula (H₀ κ : ℝ) (D₀ : ℕ) (hH₀ : 0 < H₀) (_hκ : 0 < κ) (_hD₀ : 2 ≤ D₀) (n d : ℕ) (ε : ℝ) (o : Fin n → Obs d) : ℝ := if d < D₀ then empiricalValue o else if (n : ℝ) * ε < (d : ℝ) / logAlphabet d then 1 / 2 else ∑ k ∈ Finset.range (n + 1), if hk : k ≤ n then poissonWeight (n / 4) k * ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k * cappedStatisticFormula hk H₀ hH₀ κ ε o marks else 0 
/-- The Poisson comparison intensity for a positive sample size. For the displayed parameters, poissonIntensity is the object specified by this definition. -/
 noncomputable def poissonIntensity (n : ℕ) (_hn : 0 < n) : ℝ := poissonIntensityFormula n -- @realizes \(m\)(n/8; n>0) 
/-- The pilot radius on the positive width, intensity, and logarithm domain. For the displayed parameters, pilotRadius is the object specified by this definition. -/
 noncomputable def pilotRadius (H₀ : ℝ) (hH₀ : 0 < H₀) (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ) : Fin 4 → ℝ := fun j => (pilotUpper H₀ hH₀ m L hm hL Np j - pilotLower H₀ hH₀ m L Np j) / 2 -- @realizes \(r_{ay,x}\)(rectangle coordinate radius; H₀,m,L>0) 
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotRadius_positive (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    0 < pilotRadius H hH m L hm hL Np j := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by unfold pilotCenterFormula; positivity
  have hh : 0 < pilotHalfWidthFormula H hH m L Np j := by
    unfold pilotHalfWidthFormula
    exact mul_pos hH (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (div_pos hL hm))
  change 0 < pilotRadiusFormula H hH m L Np j
  dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
  rw [max_def]
  split_ifs <;> linarith

/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_nonnegative (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    0 ≤ pilotMidpoint H hH m L Np j := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by unfold pilotCenterFormula; positivity
  have hh : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by
    unfold pilotHalfWidthFormula
    exact mul_nonneg hH.le (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hL.le hm.le))
  dsimp [pilotMidpoint, pilotUpperFormula]
  exact div_nonneg (add_nonneg (le_max_left _ _) (add_nonneg hc hh)) (by norm_num)

/-- An arm radius is the sum of two strictly positive coordinate radii.

For [the displayed parameters](hyp:r,hr,a), [armRadius](goal) is the object specified by this definition. -/
noncomputable def armRadius (r : Fin 4 → ℝ) (_hr : ∀ j, 0 < r j) (a : Bool) : ℝ :=
  armRadiusFormula r a
  -- @realizes \(R_{a,x}\)(sum of positive coordinate radii)

/-- Sensitivity on nonnegative pilot centers and the public positive overlap domain.

For [the displayed parameters](hyp:h,c,hc,a), [armWeight](goal) is the object specified by this definition. -/
noncomputable def armWeight (ε : ℝ) (_hε : 0 < ε ∧ ε ≤ 1 / 2)
    (c : Fin 4 → ℝ) (_hc : ∀ j, 0 ≤ c j) (a : Bool) : ℝ :=
  armWeightFormula ε c a
  -- @realizes \(w_{a,x}\)(weight at least one; nonnegative center and 0<ε≤1/2)

/-- The paper's strictly positive clipping scale; the unrestricted analytic
extension is clippingScaleFormula.

For [the displayed parameters](hyp:h,c,r,hc,hr), [clippingScale](goal) is the object specified by this definition. -/
noncomputable def clippingScale (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 2)
    (c r : Fin 4 → ℝ) (hc : ∀ j, 0 ≤ c j) (hr : ∀ j, 0 < r j) : ℝ :=
  2 * ∑ a : Bool, armWeight ε hε c hc a * armRadius r hr a
  -- @realizes \(S_x^{\mathrm{aw}}\)(positive scale; nonnegative centers and positive radii)

/-- For [the displayed parameters](hyp:h,K,d,m,c,r,hc,hr,Ne), [clippedCellValue](goal) is the object specified by this definition. -/
noncomputable def clippedCellValue (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 2)
    (K d : ℕ) (m : ℝ) (c r : Fin 4 → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hr : ∀ j, 0 < r j) (Ne : Fin 4 → ℕ) : ℝ :=
  let center := armwiseExtensionFormula ε c
  let width := (d : ℝ) ^ (1 / 4 : ℝ) * clippingScale ε hε c r hc hr
  max (center - width) (min (center + width) (factorialCellValue ε K m c r Ne))
  -- @realizes \(T_x\)(clipped cell statistic on the positive scale domain)

/-- For [the displayed parameters](hyp:n,d,k,hk,hn,hd,H₀,hH₀,h,o,marks), [cappedStatistic](goal) is the object specified by this definition. -/
noncomputable def cappedStatistic {n d k : ℕ} (hk : k ≤ n)
    (hn : 0 < n) (hd : 2 ≤ d) (H₀ : ℝ) (hH₀ : 0 < H₀) (κ ε : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1 / 2)
    (o : Fin n → Obs d) (marks : Fin k → Bool) : ℝ :=
  let m := poissonIntensity n hn
  let L := logAlphabet d
  let hm : 0 < m := by dsimp [m, poissonIntensity, poissonIntensityFormula]; positivity
  let hL : 0 < L := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    apply Real.log_pos
    exact lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num))
      (le_mul_of_one_le_right (Real.exp_pos 1).le hdR)
  let K := jacksonDegree κ d
  projectUnit <| ∑ x : Fin d,
    let Np := markedCount hk o marks true x
    let Ne := markedCount hk o marks false x
    let c := pilotMidpoint H₀ hH₀ m L Np
    let r := pilotRadius H₀ hH₀ m L hm hL Np
    clippedCellValue ε hε K d m c r
      (pilotMidpoint_nonnegative H₀ hH₀ m L hm hL Np)
      (pilotRadius_positive H₀ hH₀ m L hm hL Np) Ne
  -- @realizes \(\widetilde V\)(projected capped statistic; positive pilot domain threaded)

-- @node: def:armwise-estimator
/-- For [the displayed parameters](hyp:H₀,D₀,hH₀,h,hD₀,n,d,hn,hd,o), [armwiseEstimator](goal) is the object specified by this definition. -/
noncomputable def armwiseEstimator (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (_hκ : 0 < κ) (_hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hε : 0 < ε ∧ ε ≤ 1 / 2) (o : Fin n → Obs d) : ℝ :=
  if d < D₀ then empiricalValue o
  else if (n : ℝ) * ε < (d : ℝ) / logAlphabet d then 1 / 2
  else
    ∑ k ∈ Finset.range (n + 1),
      if hk : k ≤ n then
        poissonWeight (n / 4) k *
          ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k *
            cappedStatistic hk (Nat.lt_of_lt_of_le (by decide : 0 < 1) hn)
              hd H₀ hH₀ κ ε hε o marks
      else 0
  -- @realizes \(\widehat V_{n,d,\epsilon}^{\mathrm{AF}}\)(Rao-Blackwell sum; paper regime)
  -- @realizes \(\kappa\)(positive degree tuning) @realizes \(D_0\)(cutoff at least two)



/-- For [the displayed parameters](hyp:H₀,D₀,hH₀,h,hD₀,n,d), [armwiseEstimatorWitness](goal) is the object specified by this definition. -/
noncomputable def armwiseEstimatorWitness (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) :
    Estimator n d :=
  ⟨armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε, Measurable.of_discrete⟩


/-- For [the displayed parameters](hyp:H₀,D₀,hH₀,h,hD₀,n,d), [armwiseWorstRisk](goal) is the object specified by this definition. -/
noncomputable def armwiseWorstRisk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.worstCaseRiskReal (observedRisk n (d := d) (ε := ε))
    (armwiseEstimatorWitness H₀ κ D₀ hH₀ hκ hD₀ n d ε)

/-- Worst-case causal squared risk of the same observed-sample armwise estimator.

For [the displayed parameters](hyp:H₀,D₀,hH₀,h,hD₀,n,d), [causalArmwiseWorstRisk](goal) is the object specified by this definition. -/
noncomputable def causalArmwiseWorstRisk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.worstCaseRiskReal (causalRisk n (d := d) (ε := ε))
    (armwiseEstimatorWitness H₀ κ D₀ hH₀ hκ hD₀ n d ε)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
