module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.FactorialMoments
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.BVLipschitz
public import Causalean.Stat.Concentration.BoundedVariation.WeightedIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Jackson coefficient bounded-variation envelopes and their Poisson path consequences. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Stat.Concentration.BoundedVariation
open Causalean.Stat.Concentration.Poisson
open Causalean.Mathlib.Analysis.JacksonApproximation

/-- A finite-variation continuous path is controlled by its value at the left
endpoint and its total variation. With [the specified inputs and conditions](hyp:f,hBV), [the stated relationship holds](goal). -/
-- @node: pathSize_le_two_endpointVariation
lemma pathSize_le_two_endpointVariation (f : Path)
    (hBV : eVariationOn f Set.univ < ⊤) :
    pathSize f ≤ 2 * (|f timeZero| + pathTV f) := by
  have hincENN (t : Time) : edist (f timeZero) (f t) ≤ eVariationOn f Set.univ :=
    eVariationOn.edist_le f (Set.mem_univ t) (Set.mem_univ timeZero)
  have hpoint (t : Time) : |f t - f timeZero| ≤ pathTV f := by
    have h := ENNReal.toReal_mono (ne_of_lt hBV) (hincENN t)
    simpa [pathTV, edist_dist, Real.dist_eq, abs_sub_comm] using h
  have hnorm : ‖f‖ ≤ |f timeZero| + pathTV f := by
    apply (ContinuousMap.norm_le f
      (add_nonneg (abs_nonneg _) (pathTV_nonneg f))).2
    intro t
    rw [Real.norm_eq_abs]
    calc
      |f t| = |f timeZero + (f t - f timeZero)| := by ring_nf
      _ ≤ |f timeZero| + |f t - f timeZero| := abs_add_le _ _
      _ ≤ |f timeZero| + pathTV f := by linarith [hpoint t]
  unfold pathSize
  have htv := pathTV_nonneg f
  linarith [abs_nonneg (f timeZero)]

/-- Summing the deterministic endpoint/variation bound over a finite family
costs only the universal numerical factor four after squaring. With [the specified inputs and conditions](hyp:f,hBV), [the stated relationship holds](goal). -/
-- @node: sum_pathSize_sq_le_four_endpointVariation_sq
lemma sum_pathSize_sq_le_four_endpointVariation_sq {ι : Type*} [Fintype ι]
    (f : ι → Path) (hBV : ∀ i, eVariationOn (f i) Set.univ < ⊤) :
    ∑ i, pathSize (f i) ^ 2 ≤
      4 * (∑ i, (|f i timeZero| + pathTV (f i))) ^ 2 := by
  let b : ι → ℝ := fun i => |f i timeZero| + pathTV (f i)
  have hb (i : ι) : 0 ≤ b i :=
    add_nonneg (abs_nonneg _) (pathTV_nonneg _)
  have hpoint (i : ι) : pathSize (f i) ^ 2 ≤ 4 * b i ^ 2 := by
    have hsize := pathSize_le_two_endpointVariation (f i) (hBV i)
    have hsize0 := pathSize_nonneg (f i)
    dsimp [b] at hsize ⊢
    nlinarith [sq_nonneg (pathSize (f i) - 2 *
      (|f i timeZero| + pathTV (f i)))]
  calc
    ∑ i, pathSize (f i) ^ 2 ≤ ∑ i, 4 * b i ^ 2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 4 * ∑ i, b i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * (∑ i, b i) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hb i) (by norm_num)

/-- Restricting a real function to the ordered interval `[0,1]` preserves
exactly its extended variation. With [the specified inputs and conditions](hyp:f), [the stated relationship holds](goal). -/
-- @node: eVariationOn_time_eq_Icc
lemma eVariationOn_time_eq_Icc (f : ℝ → ℝ) :
    eVariationOn (fun t : Time => f t) Set.univ =
      eVariationOn f (Set.Icc 0 1) := by
  unfold eVariationOn
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    let v : ℕ → ℝ := fun i => (u i : ℝ)
    have hv : Monotone v := fun i j hij => hu hij
    have hvs : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1 := fun i => (u i).property
    apply le_iSup_of_le (n, ⟨v, hv, hvs⟩)
    rfl
  · apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    let v : ℕ → Time := fun i => ⟨u i, hus i⟩
    have hv : Monotone v := fun i j hij => hu hij
    have hvs : ∀ i, v i ∈ Set.univ := fun i => Set.mem_univ _
    apply le_iSup_of_le (n, ⟨v, hv, hvs⟩)
    rfl

/-- A normalized-cube affine perturbation moves from its center by at most
the sum of its nonnegative coordinate radii in cellwise L1 distance. With [the specified inputs and conditions](hyp:center,radius,hR,x,hx), [the stated relationship holds](goal). -/
-- @node: affinePoint_l1_sub_center_le_sum_radius
lemma affinePoint_l1_sub_center_le_sum_radius (center radius : Cell → ℝ)
    (hR : ∀ zeta, 0 ≤ radius zeta) (x : Fin 4 → ℝ)
    (hx : x ∈ normalizedCube 4) :
    ∑ zeta : Cell,
        |affinePoint (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) x (CellFourEquiv zeta) -
          center zeta| ≤
      ∑ zeta : Cell, radius zeta := by
  apply Finset.sum_le_sum
  intro zeta hzeta
  have hxabs : |x (CellFourEquiv zeta)| ≤ 1 :=
    abs_le.2 (hx (CellFourEquiv zeta))
  simp only [affinePoint, Equiv.symm_apply_apply, add_sub_cancel_left, abs_mul]
  rw [abs_of_nonneg (hR zeta)]
  exact mul_le_of_le_one_right (hR zeta) hxabs

/-- Averaging paths against the normalized positive tensor Jackson kernel
does not increase a common path-size bound. With [the specified inputs and conditions](hyp:K,hK,f,B,hB,hInt,hBV,hsize), [the stated relationship holds](goal). -/
-- @node: tensorJacksonPathIntegral_size_le
lemma tensorJacksonPathIntegral_size_le (K : ℕ) (hK : 0 < K)
    (f : (Fin 4 → ℝ) → Path) (B : ℝ) (hB : 0 ≤ B)
    (hInt : ∀ t : Time, IntegrableOn
      (fun u => tensorJackson K 4 u * f u t) (periodBox 4))
    (hBV : ∀ u, eVariationOn (f u) Set.univ < ⊤)
    (hsize : ∀ u, pathSize (f u) ≤ B) :
    ∃ g : Path,
      (∀ t : Time, g t = ∫ u in periodBox 4,
        tensorJackson K 4 u * f u t) ∧
      eVariationOn g Set.univ < ⊤ ∧ pathSize g ≤ B := by
  let k : (Fin 4 → ℝ) → NNReal := fun u =>
    ⟨tensorJackson K 4 u, tensorJackson_nonneg hK u⟩
  let μ := (volume.restrict (periodBox 4)).withDensity
    (fun u => (k u : ENNReal))
  letI : IsProbabilityMeasure μ := by
    apply (isProbabilityMeasure_iff).2
    rw [show μ Set.univ = ∫⁻ u, (k u : ENNReal)
        ∂(volume.restrict (periodBox 4)) by
      unfold μ
      rw [withDensity_apply _ MeasurableSet.univ]
      simp]
    rw [lintegral_coe_eq_integral]
    · have hi : (∫ u, (k u : ℝ) ∂(volume.restrict (periodBox 4))) = 1 := by
        change (∫ u in periodBox 4, tensorJackson K 4 u) = 1
        exact tensorJackson_integral_eq_one hK
      rw [hi]
      simp
    · change IntegrableOn (tensorJackson K 4) (periodBox 4)
      exact integrableOn_tensorJackson K 4
  have hkmeas : Measurable k := by
    unfold k
    fun_prop
  have hfInt (t : Time) : Integrable (fun u => f u t) μ := by
    rw [integrable_withDensity_iff_integrable_smul hkmeas]
    change IntegrableOn (fun u => tensorJackson K 4 u * f u t) (periodBox 4)
    exact hInt t
  obtain ⟨g, hg, hgbv, hgsize⟩ := weightedPathIntegral_size_le μ f
    (fun _ => 1) B 1 hB (by norm_num) (fun t => by simpa using hfInt t)
    (fun _ => by norm_num) hBV hsize
  refine ⟨g, ?_, hgbv, by simpa using hgsize⟩
  intro t
  rw [hg t, integral_withDensity_eq_integral_smul hkmeas]
  simp only [one_mul]
  change (∫ u in periodBox 4, tensorJackson K 4 u * f u t) = _
  rfl

/-- The centered local Jackson polynomial has a uniform cube path-size
envelope obtained from the spatial BV Lipschitz constant and the radius sum. With [the specified inputs and conditions](hyp:epsilon,K,center,radius,hK,hpull,hcenter,hR,haffine,C,hC,hthreshold,x,hx), [the stated relationship holds](goal). -/
-- @node: localJacksonPolynomial_cube_pathSize_le
lemma localJacksonPolynomial_cube_pathSize_le
    (epsilon : ℝ) (K : ℕ) (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (normalizedCube 4))
    (hcenter : ∀ zeta, 0 ≤ center zeta)
    (hR : ∀ zeta, 0 ≤ radius zeta)
    (haffine : ∀ x ∈ normalizedCube 4, ∀ zeta,
      0 ≤ affinePoint
        (fun i => center (CellFourEquiv.symm i))
        (fun i => radius (CellFourEquiv.symm i)) x (CellFourEquiv zeta))
    (C : ℝ) (hC : 0 ≤ C)
    (hthreshold : ∀ u v : Cell → ℝ,
      (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ v z) →
      bvNorm (fun lambda => thresholdFunReal epsilon lambda u -
        thresholdFunReal epsilon lambda v) ≤ C * ∑ z, |u z - v z|)
    (x : Fin 4 → ℝ) (hx : x ∈ normalizedCube 4) :
    pathSize (⟨fun lambda : Time => MvPolynomial.eval x
      (localJacksonPolynomial epsilon lambda K center radius),
      localJacksonPolynomial_eval_continuous_time epsilon K center radius
        hK hpull x hx⟩ : Path) ≤
      2 * C * ∑ zeta : Cell, radius zeta := by
  let theta : Fin 4 → ℝ := fun i => Real.arccos (x i)
  have hcos : (fun i => Real.cos (theta i)) = x := by
    funext i
    exact Real.cos_arccos (hx i).1 (hx i).2
  let v (u : Fin 4 → ℝ) : Cell → ℝ := fun zeta =>
    affinePoint (fun i => center (CellFourEquiv.symm i))
      (fun i => radius (CellFourEquiv.symm i))
      (cosPoint (theta - u)) (CellFourEquiv zeta)
  have hvnonneg (u : Fin 4 → ℝ) (zeta : Cell) : 0 ≤ v u zeta :=
    haffine _ (cosPoint_mem_normalizedCube _) zeta
  let f (u : Fin 4 → ℝ) : Path :=
    ⟨fun lambda : Time => thresholdFunReal epsilon lambda (v u) -
        thresholdFunReal epsilon lambda center,
      (thresholdFunReal_continuous_time epsilon (v u)).sub
        (thresholdFunReal_continuous_time epsilon center)⟩
  have hfBV (u : Fin 4 → ℝ) : eVariationOn (f u) Set.univ < ⊤ := by
    have hlip := (thresholdFunReal_lipschitz_time epsilon (v u)).sub
      (thresholdFunReal_lipschitz_time epsilon center)
    have hid : BoundedVariationOn (id : Time → Time) Set.univ := by
      have hm : Monotone (fun t : Time => (t : ℝ)) := fun s t hst => hst
      exact MonotoneOn.boundedVariationOn (hm.monotoneOn _)
        (fun t _ => abs_le.2 ⟨by linarith [t.property.1], t.property.2⟩)
    apply lt_top_iff_ne_top.mpr
    simpa [f, BoundedVariationOn, Function.comp_def] using
      hlip.comp_boundedVariationOn hid
  have hfsize (u : Fin 4 → ℝ) :
      pathSize (f u) ≤ 2 * C * ∑ zeta : Cell, radius zeta := by
    have hbv := hthreshold (v u) center (hvnonneg u) hcenter
    have hdist := affinePoint_l1_sub_center_le_sum_radius center radius hR
      (cosPoint (theta - u)) (cosPoint_mem_normalizedCube _)
    have hbase := pathSize_le_two_endpointVariation (f u) (hfBV u)
    have heq : |f u timeZero| + pathTV (f u) =
        bvNorm (fun lambda => thresholdFunReal epsilon lambda (v u) -
          thresholdFunReal epsilon lambda center) := by
      change |thresholdFunReal epsilon 0 (v u) -
          thresholdFunReal epsilon 0 center| +
        (eVariationOn (fun lambda : Time =>
          thresholdFunReal epsilon lambda (v u) -
            thresholdFunReal epsilon lambda center) Set.univ).toReal = _
      unfold bvNorm
      congr 1
      exact congrArg ENNReal.toReal (eVariationOn_time_eq_Icc
        (fun lambda : ℝ => thresholdFunReal epsilon lambda (v u) -
          thresholdFunReal epsilon lambda center))
    rw [heq] at hbase
    nlinarith [mul_le_mul_of_nonneg_left (hbv.trans
      (mul_le_mul_of_nonneg_left hdist hC)) (by norm_num : (0 : ℝ) ≤ 2)]
  have hfInt (t : Time) : IntegrableOn
      (fun u => tensorJackson K 4 u * f u t) (periodBox 4) := by
    have hcosCont : Continuous (fun u : Fin 4 → ℝ => cosPoint (theta - u)) := by
      unfold cosPoint
      fun_prop
    have ht : ContinuousOn (fun u => thresholdFunReal epsilon t (v u))
        (periodBox 4) := by
      apply (hpull t).comp hcosCont.continuousOn
      intro u hu
      exact cosPoint_mem_normalizedCube _
    have hc : Continuous (fun u : Fin 4 → ℝ =>
        thresholdFunReal epsilon t center) := continuous_const
    have hk : Continuous (tensorJackson K 4) := by
      unfold tensorJackson
      fun_prop
    exact (hk.continuousOn.mul (ht.sub hc.continuousOn)).integrableOn_compact
      (by
        change IsCompact {u : Fin 4 → ℝ | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi}
        exact isCompact_pi_infinite fun _ => isCompact_Icc)
  obtain ⟨g, hg, hgbv, hgsize⟩ := tensorJacksonPathIntegral_size_le K hK f
    (2 * C * ∑ zeta : Cell, radius zeta)
    (mul_nonneg (mul_nonneg (by norm_num) hC) (Finset.sum_nonneg
      (fun z _ => hR z))) hfInt hfBV hfsize
  have hpath : (⟨fun lambda : Time => MvPolynomial.eval x
      (localJacksonPolynomial epsilon lambda K center radius),
      localJacksonPolynomial_eval_continuous_time epsilon K center radius
        hK hpull x hx⟩ : Path) = g := by
    ext t
    change MvPolynomial.eval x
      (localJacksonPolynomial epsilon t K center radius) = g t
    have heval := localJacksonPolynomial_eval_cos epsilon t K center radius
      hK (hpull t) theta
    have hevalx : MvPolynomial.eval x
        (localJacksonPolynomial epsilon t K center radius) =
        localJacksonConvolution epsilon t K center radius theta -
          thresholdFunReal epsilon t center := by
      simpa only [hcos] using heval
    rw [hevalx, hg t]
    unfold localJacksonConvolution tensorConvolution f v
    have hcenterInt : IntegrableOn (fun u : Fin 4 → ℝ =>
        thresholdFunReal epsilon t center * tensorJackson K 4 u) (periodBox 4) :=
      (integrableOn_tensorJackson K 4).const_mul _
    have hfirstInt : IntegrableOn (fun u : Fin 4 → ℝ =>
        thresholdFunReal epsilon t
          (fun zeta => affinePoint
            (fun i => center (CellFourEquiv.symm i))
            (fun i => radius (CellFourEquiv.symm i))
            (cosPoint (theta - u)) (CellFourEquiv zeta)) *
          tensorJackson K 4 u) (periodBox 4) := by
      have hcosCont : Continuous (fun u : Fin 4 → ℝ => cosPoint (theta - u)) := by
        unfold cosPoint
        fun_prop
      have hk : Continuous (tensorJackson K 4) := by
        unfold tensorJackson
        fun_prop
      exact (((hpull t).comp hcosCont.continuousOn
        (fun u hu => cosPoint_mem_normalizedCube _)).mul
          hk.continuousOn).integrableOn_compact
        (by
          change IsCompact {u : Fin 4 → ℝ | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi}
          exact isCompact_pi_infinite fun _ => isCompact_Icc)
    let a (u : Fin 4 → ℝ) := thresholdFunReal epsilon t
      (fun zeta => affinePoint
        (fun i => center (CellFourEquiv.symm i))
        (fun i => radius (CellFourEquiv.symm i))
        (cosPoint (theta - u)) (CellFourEquiv zeta))
    let c := thresholdFunReal epsilon t center
    change (∫ u in periodBox 4, a u * tensorJackson K 4 u) - c =
      ∫ u in periodBox 4, tensorJackson K 4 u * (a u - c)
    have hfirstInt' : IntegrableOn
        (fun u => a u * tensorJackson K 4 u) (periodBox 4) := by
      simpa [a] using hfirstInt
    have hcenterInt' : IntegrableOn
        (fun u => c * tensorJackson K 4 u) (periodBox 4) := by
      simpa [c] using hcenterInt
    calc
      (∫ u in periodBox 4, a u * tensorJackson K 4 u) - c =
          (∫ u in periodBox 4, a u * tensorJackson K 4 u) - c * 1 := by ring
      _ = (∫ u in periodBox 4, a u * tensorJackson K 4 u) -
          c * (∫ u in periodBox 4, tensorJackson K 4 u) := by
            rw [tensorJackson_integral_eq_one hK]
      _ = (∫ u in periodBox 4, a u * tensorJackson K 4 u) -
          (∫ u in periodBox 4, c * tensorJackson K 4 u) := by
            rw [integral_const_mul]
      _ = ∫ u in periodBox 4,
          (a u * tensorJackson K 4 u - c * tensorJackson K 4 u) := by
            rw [integral_sub hfirstInt' hcenterInt']
      _ = ∫ u in periodBox 4, tensorJackson K 4 u * (a u - c) := by
            apply integral_congr_ae
            filter_upwards [] with u
            ring
  rw [hpath]
  exact hgsize

/-- The explicit four-dimensional Chebyshev conversion factor is absorbed
by the paper's `exp (12 K)` budget. With [the specified inputs and conditions](hyp:K,hK), [the stated relationship holds](goal). -/
-- @node: jacksonChebyshevFactor_le_exp_twelve
lemma jacksonChebyshevFactor_le_exp_twelve (K : ℕ) (hK : 0 < K) :
    (16 : ℝ) * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
      (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) ≤
        Real.exp (12 * K) := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsub : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hD : (↑(2 * (K - 1) + 1) : ℝ) ≤ 2 * K := by
    norm_cast
    omega
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg 2
    nlinarith
  have hbase : 1 + Real.sqrt 2 ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have htwoK : 2 * (K : ℝ) ≤ Real.exp K := by
    have he := Real.add_one_le_exp ((K : ℝ) / 2)
    have hexp0 : 0 ≤ Real.exp ((K : ℝ) / 2) := (Real.exp_pos _).le
    have hsq : (2 * (K : ℝ)) ≤ (1 + (K : ℝ) / 2) ^ 2 := by
      nlinarith [sq_nonneg ((K : ℝ) - 2)]
    calc
      2 * (K : ℝ) ≤ (1 + (K : ℝ) / 2) ^ 2 := hsq
      _ ≤ (Real.exp ((K : ℝ) / 2)) ^ 2 := by nlinarith
      _ = Real.exp K := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have hpoly : (↑(2 * (K - 1) + 1) : ℝ) ^ 4 ≤ Real.exp (4 * K) := by
    calc
      _ ≤ (2 * (K : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hD _
      _ ≤ (Real.exp K) ^ 4 := pow_le_pow_left₀ (by positivity) htwoK _
      _ = Real.exp (4 * K) := by rw [← Real.exp_nat_mul]; norm_num
  have hcheb : (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) ≤
      Real.exp (4 * (2 * (K - 1))) := by
    calc
      _ ≤ (Real.exp 1) ^ (4 * (2 * (K - 1))) :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rw [hsub]; ring
  calc
    _ ≤ Real.exp 4 * Real.exp (4 * K) *
        Real.exp (4 * (2 * (K - 1))) := by gcongr
    _ = Real.exp (4 + 4 * K + 4 * (2 * (K - 1))) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (12 * K) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The finite four-coordinate factorial index set, together with the degree
exponential from equation (21), is absorbed by the structural `d^(1/16)`
budget. With [the specified inputs and conditions](hyp:d,hd), [the stated relationship holds](goal). -/
-- @node: jacksonDegree_factorial_index_exponential_budget
lemma jacksonDegree_factorial_index_exponential_budget (d : ℕ) (hd : 16 ≤ d) :
    (↑(2 * (jacksonDegree d - 1) + 1) : ℝ) ^ 4 *
        Real.exp (24 * jacksonDegree d +
          16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d) ≤
      Real.exp 123 * (d : ℝ) ^ (1 / 16 : ℝ) := by
  let K := jacksonDegree d
  let L := logAlphabet d
  have hKnat : 0 < K := by unfold K jacksonDegree; omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hKnat
  have hD : (↑(2 * (K - 1) + 1) : ℝ) ≤ 2 * K := by
    norm_cast
    omega
  have htwoK : 2 * (K : ℝ) ≤ Real.exp K := by
    have he := Real.add_one_le_exp ((K : ℝ) / 2)
    have hexp0 : 0 ≤ Real.exp ((K : ℝ) / 2) := (Real.exp_pos _).le
    have hsq : (2 * (K : ℝ)) ≤ (1 + (K : ℝ) / 2) ^ 2 := by
      nlinarith [sq_nonneg ((K : ℝ) - 2)]
    calc
      2 * (K : ℝ) ≤ (1 + (K : ℝ) / 2) ^ 2 := hsq
      _ ≤ (Real.exp ((K : ℝ) / 2)) ^ 2 := by nlinarith
      _ = Real.exp K := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hcard : (↑(2 * (K - 1) + 1) : ℝ) ^ 4 ≤ Real.exp (4 * K) := by
    calc
      _ ≤ (2 * (K : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hD _
      _ ≤ (Real.exp K) ^ 4 := pow_le_pow_left₀ (by positivity) htwoK _
      _ = Real.exp (4 * K) := by rw [← Real.exp_nat_mul]; norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hL : L = 1 + Real.log d := by
    unfold L logAlphabet
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp]
  have hLge : 1 ≤ L := by
    rw [hL]
    linarith [Real.log_nonneg hdge]
  have hfloor : (⌊jacksonDegreeConstant * L⌋₊ : ℝ) ≤ L / 512 := by
    calc
      _ ≤ jacksonDegreeConstant * L :=
        Nat.floor_le (by unfold jacksonDegreeConstant; positivity)
      _ = L / 512 := by unfold jacksonDegreeConstant; ring
  have hK : (K : ℝ) ≤ 2 + L / 512 := by
    unfold K jacksonDegree
    rw [Nat.cast_max]
    exact max_le (by linarith) (by linarith)
  have hKnonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hscale :
      28 * (K : ℝ) * L + 16 * (K : ℝ) ^ 2 ≤
        122 * L + L ^ 2 / 16 := by
    have hprod := mul_nonneg
      (show 0 ≤ 2 + L / 512 - (K : ℝ) by linarith)
      (show 0 ≤ 2 + L / 512 + (K : ℝ) by positivity)
    nlinarith [sq_nonneg (L - 1)]
  have hbound :
      28 * (K : ℝ) + 16 * (K : ℝ) ^ 2 / L ≤ 122 + L / 16 := by
    have hLpos : 0 < L := by linarith
    calc
      _ = (28 * (K : ℝ) * L + 16 * (K : ℝ) ^ 2) / L := by
        field_simp
      _ ≤ (122 * L + L ^ 2 / 16) / L := by gcongr
      _ = _ := by field_simp
  calc
    (↑(2 * (jacksonDegree d - 1) + 1) : ℝ) ^ 4 *
        Real.exp (24 * jacksonDegree d +
          16 * (jacksonDegree d : ℝ) ^ 2 / logAlphabet d) ≤
        Real.exp (4 * K) * Real.exp
          (24 * K + 16 * (K : ℝ) ^ 2 / L) := by
      simpa [K, L] using mul_le_mul_of_nonneg_right hcard
        (Real.exp_nonneg _)
    _ = Real.exp (28 * K + 16 * (K : ℝ) ^ 2 / L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (123 + Real.log d / 16) := by
      apply Real.exp_le_exp.mpr
      rw [hL] at hbound ⊢
      linarith
    _ = Real.exp 123 * (d : ℝ) ^ (1 / 16 : ℝ) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hdpos]
      congr 1
      ring_nf

/-- A uniform path-size bound for every normalized-cube evaluation of the
local Jackson polynomial implies the paper's coefficient BV envelope. With [the specified inputs and conditions](hyp:epsilon,m,d,pilot,hK,hpull,B,hB,hbound), [the stated relationship holds](goal). -/
-- @node: jacksonCoefficientBV_le_of_cube_pathSize
lemma jacksonCoefficientBV_le_of_cube_pathSize
    (epsilon m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (hK : 0 < jacksonDegree d)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c))) (normalizedCube 4))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun lambda : Time => MvPolynomial.eval x
        (localJacksonPolynomial epsilon lambda (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)),
        localJacksonPolynomial_eval_continuous_time epsilon (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot) hK hpull x hx⟩ : Path) ≤ B) :
    jacksonCoefficientBV epsilon m d pilot ≤
      Real.exp (12 * jacksonDegree d) * B := by
  let K := jacksonDegree d
  let center := pilotMidpoint m d pilot
  let radius := pilotRadius m d pilot
  let p : Time → MvPolynomial (Fin 4) ℝ := fun lambda =>
    localJacksonPolynomial epsilon lambda K center radius
  have hdeg (lambda : Time) (i : Fin 4) :
      (p lambda).degreeOf i ≤ 2 * (K - 1) :=
    localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
      (hpull lambda) i
  have hgrid (a : Fin 4 → Fin (2 * (K - 1) + 1)) :
      Continuous (fun lambda : Time =>
        MvPolynomial.eval (fun i => (a i : ℝ)) (p lambda)) :=
    localJacksonPolynomial_fixed_eval_continuous_time epsilon K center radius
      hK hpull (le_refl _) (fun i => (a i : ℝ))
  have hcont (x : Fin 4 → ℝ) (hx : x ∈ normalizedCube 4) :
      Continuous (fun lambda : Time => MvPolynomial.eval x (p lambda)) :=
    localJacksonPolynomial_eval_continuous_time epsilon K center radius hK hpull x hx
  have hBV (x : Fin 4 → ℝ) (hx : x ∈ normalizedCube 4) :
      eVariationOn
        (⟨fun lambda : Time => MvPolynomial.eval x (p lambda), hcont x hx⟩ : Path)
        Set.univ < ⊤ := by
    obtain ⟨C, hLip⟩ := localJacksonPolynomial_eval_lipschitz_time
      epsilon K center radius hK hpull x hx
    have hid : BoundedVariationOn (id : Time → Time) Set.univ := by
      have hm : Monotone (fun t : Time => (t : ℝ)) := fun s t hst => hst
      exact MonotoneOn.boundedVariationOn (hm.monotoneOn _)
        (fun t _ => abs_le.2 ⟨by linarith [t.property.1], t.property.2⟩)
    apply lt_top_iff_ne_top.mpr
    simpa [BoundedVariationOn, Function.comp_def] using
      hLip.comp_boundedVariationOn hid
  have henv := tensorCoefficientPath_four_chebyshev_size_envelope p B hB
    hdeg hgrid hcont hBV (by simpa [p, K, center, radius] using hbound)
  have hcoeff : jacksonCoefficientBV epsilon m d pilot ≤
      ∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a) := by
    unfold jacksonCoefficientBV
    dsimp only
    apply Finset.sum_le_sum
    intro a ha
    have hzero : |jacksonCoefficient epsilon 0 K center radius
        (fun i => (a i : ℕ))| ≤
        ‖tensorCoefficientPath p hdeg hgrid a‖ := by
      have hz := ContinuousMap.norm_coe_le_norm
        (tensorCoefficientPath p hdeg hgrid a) timeZero
      rw [Real.norm_eq_abs] at hz
      simpa [tensorCoefficientPath, p, K, center, radius, timeZero,
        jacksonCoefficient_eq_tensorCoeffs] using hz
    have htv : (eVariationOn (fun lambda : ℝ =>
        jacksonCoefficient epsilon lambda K center radius
          (fun i => (a i : ℕ))) (Set.Icc 0 1)).toReal =
        pathTV (tensorCoefficientPath p hdeg hgrid a) := by
      unfold pathTV
      rw [← eVariationOn_time_eq_Icc]
      rfl
    rw [htv]
    unfold pathSize
    simpa [add_comm] using
      add_le_add_right hzero (pathTV (tensorCoefficientPath p hdeg hgrid a))
  calc
    jacksonCoefficientBV epsilon m d pilot ≤
        ∑ a, pathSize (tensorCoefficientPath p hdeg hgrid a) := hcoeff
    _ ≤ (16 : ℝ) * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) * B := henv
    _ ≤ Real.exp (12 * K) * B :=
      mul_le_mul_of_nonneg_right (jacksonChebyshevFactor_le_exp_twelve K hK) hB

/-- The squared path sizes of all local Jackson coefficient paths are bounded
by four times the paper's coefficient bounded-variation envelope squared. With [the specified inputs and conditions](hyp:epsilon,m,d,pilot,hK,hpull), [the stated relationship holds](goal). -/
-- @node: localJacksonCoefficientPath_sq_sum_le_jacksonCoefficientBV
lemma localJacksonCoefficientPath_sq_sum_le_jacksonCoefficientBV
    (epsilon m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (hK : 0 < jacksonDegree d)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4)) :
    ∑ a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
        pathSize (localJacksonCoefficientPath epsilon (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot) hK hpull
          (le_refl _) a) ^ 2 ≤
      4 * jacksonCoefficientBV epsilon m d pilot ^ 2 := by
  let c : (Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1)) → Path := fun a =>
    localJacksonCoefficientPath epsilon (jacksonDegree d)
      (pilotMidpoint m d pilot) (pilotRadius m d pilot) hK hpull
      (le_refl _) a
  have hBV (a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1)) :
      eVariationOn (c a) Set.univ < ⊤ := by
    exact localJacksonCoefficientPath_bv epsilon (jacksonDegree d)
      (pilotMidpoint m d pilot) (pilotRadius m d pilot) hK hpull
      (le_refl _) a
  calc
    ∑ a, pathSize (c a) ^ 2 ≤
        4 * (∑ a, (|c a timeZero| + pathTV (c a))) ^ 2 :=
      sum_pathSize_sq_le_four_endpointVariation_sq c hBV
    _ = 4 * jacksonCoefficientBV epsilon m d pilot ^ 2 := by
      congr 2
      unfold jacksonCoefficientBV
      dsimp only
      apply Finset.sum_congr rfl
      intro a ha
      change |jacksonCoefficient epsilon 0 (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          (fun i => (a i : ℕ))| +
        (eVariationOn (fun lambda : Time =>
          jacksonCoefficient epsilon lambda (jacksonDegree d)
            (pilotMidpoint m d pilot) (pilotRadius m d pilot)
            (fun i => (a i : ℕ))) Set.univ).toReal = _
      congr 1
      exact congrArg ENNReal.toReal (eVariationOn_time_eq_Icc
        (fun lambda : ℝ => jacksonCoefficient epsilon lambda (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          (fun i => (a i : ℕ))))

/-- The four-Poisson factorial path square moment is controlled directly by
the paper's Jackson coefficient bounded-variation envelope. With [the specified inputs and conditions](hyp:epsilon,m,d,pilot,hK,hpull,W,rate,hWmeas,hWlaw,hWindep,L,hm,hL,hR,hcenter,hvariance,cap,hcap), [the stated relationship holds](goal). -/
-- @node: localJacksonFourPoissonFactorialPath_sq_integral_le_coefficientBV
lemma localJacksonFourPoissonFactorialPath_sq_integral_le_coefficientBV
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (epsilon m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (hK : 0 < jacksonDegree d)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hR : ∀ i, 0 < pilotRadius m d pilot (CellFourEquiv.symm i))
    (hcenter : ∀ i, |(rate i : ℝ) / m -
      pilotMidpoint m d pilot (CellFourEquiv.symm i)| ≤
        pilotRadius m d pilot (CellFourEquiv.symm i))
    (hvariance : ∀ i, (rate i : ℝ) /
      (m ^ 2 * pilotRadius m d pilot (CellFourEquiv.symm i) ^ 2) ≤ 1 / L)
    (cap : ℝ) (hcap : 0 ≤ cap) :
    (∫ ω, pathSize (localJacksonFourPoissonFactorialPath epsilon
      (jacksonDegree d) (pilotMidpoint m d pilot) (pilotRadius m d pilot)
      hK hpull (le_refl _) W m cap ω) ^ 2 ∂μ) ≤
      (4 * jacksonCoefficientBV epsilon m d pilot ^ 2) *
        ∑ _a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
          Real.exp (4 * ((2 * (jacksonDegree d - 1) : ℕ) : ℝ) ^ 2 / L) := by
  have h := localJacksonFourPoissonFactorialPath_sq_bound μ epsilon
    (jacksonDegree d) (pilotMidpoint m d pilot) (pilotRadius m d pilot)
    hK hpull (le_refl _) W rate hWmeas hWlaw hWindep m L hm hL hR
    hcenter hvariance cap hcap
  calc
    _ ≤ (∑ a, pathSize (localJacksonCoefficientPath epsilon
          (jacksonDegree d) (pilotMidpoint m d pilot) (pilotRadius m d pilot)
          hK hpull (le_refl _) a) ^ 2) *
        ∑ _a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
          Real.exp (4 * ((2 * (jacksonDegree d - 1) : ℕ) : ℝ) ^ 2 / L) :=
      h.2.2.2.2
    _ ≤ (4 * jacksonCoefficientBV epsilon m d pilot ^ 2) *
        ∑ _a : Fin 4 → Fin (2 * (jacksonDegree d - 1) + 1),
          Real.exp (4 * ((2 * (jacksonDegree d - 1) : ℕ) : ℝ) ^ 2 / L) := by
      apply mul_le_mul_of_nonneg_right
        (localJacksonCoefficientPath_sq_sum_le_jacksonCoefficientBV
          epsilon m d pilot hK hpull)
      exact Finset.sum_nonneg fun _ _ => Real.exp_nonneg _

end CausalSmith.Stat.DiscreteBudgetvalueCurve
