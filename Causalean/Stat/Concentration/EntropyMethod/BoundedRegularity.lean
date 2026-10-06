/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.FiniteTensorization
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Automatic entropy regularity for bounded positive functions

The real-valued entropy tensorization API records explicit Bochner and Fubini hypotheses.  This
file discharges those hypotheses for measurable functions bounded between two positive finite
constants, the situation needed for exponential tilts of bounded empirical suprema.
-/

public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u

private lemma integrable_of_measurable_abs_le''
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    {f : X → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f mu := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

private lemma abs_log_le_of_mem_Icc {c C z : ℝ}
    (hc : 0 < c) (hz : c ≤ z) (hzC : z ≤ C) :
    |Real.log z| ≤ max |Real.log c| |Real.log C| := by
  have hzpos : 0 < z := hc.trans_le hz
  have hCpos : 0 < C := hzpos.trans_le hzC
  have hlo : Real.log c ≤ Real.log z := Real.log_le_log hc hz
  have hhi : Real.log z ≤ Real.log C := Real.log_le_log hzpos hzC
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_max_left |Real.log c| |Real.log C|)).trans
      ((neg_abs_le (Real.log c)).trans hlo)
  · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))

private lemma integral_section_mem_Icc
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    {f : X → Y → ℝ} {c C : ℝ}
    (hf : ∀ y, Integrable (fun x => f x y) mu)
    (hlower : ∀ x y, c ≤ f x y) (hupper : ∀ x y, f x y ≤ C) (y : Y) :
    c ≤ ∫ x, f x y ∂mu ∧ (∫ x, f x y ∂mu) ≤ C := by
  constructor
  · have h := integral_mono (integrable_const c) (hf y) (fun x => hlower x y)
    simpa using h
  · have h := integral_mono (hf y) (integrable_const C) (fun x => hupper x y)
    simpa using h

/-- If [a jointly measurable function `f`](hyp:hf) is [bounded below by a positive constant
`c`](hyp:hc,hlower) and [above by `C`](hyp:hupper), then its [entropy in the first coordinate is
measurable as a function of the second coordinate](goal) under [the probability law `mu`](hyp:mu). -/
@[fun_prop]
theorem measurable_entropy_section_of_bounded_positive
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    {f : X × Y → ℝ} {c C : ℝ}
    (hf : Measurable f) (hc : 0 < c)
    (hlower : ∀ z, c ≤ f z) (hupper : ∀ z, f z ≤ C) :
    Measurable (fun y => entropy mu (fun x => f (x, y))) := by
  have hfStrong : StronglyMeasurable f := hf.stronglyMeasurable
  have hflogStrong : StronglyMeasurable (fun z => f z * Real.log (f z)) := by
    fun_prop
  have hfirst : StronglyMeasurable (fun y => ∫ x, f (x, y) * Real.log (f (x, y)) ∂mu) :=
    hflogStrong.integral_prod_left'
  have hmean : StronglyMeasurable (fun y => ∫ x, f (x, y) ∂mu) :=
    hfStrong.integral_prod_left'
  unfold entropy
  exact hfirst.measurable.sub (hmean.measurable.mul hmean.measurable.log)

/-- If [a jointly measurable function `f`](hyp:hf) is [bounded below by a positive constant
`c`](hyp:hc,hlower) and [above by `C`](hyp:hupper), then every [first-coordinate entropy section
is bounded by twice `C` times the maximum endpoint log-magnitude](goal) under [the probability
law `mu`](hyp:mu), at each [second-coordinate value `y`](hyp:y). -/
theorem abs_entropy_section_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    {f : X × Y → ℝ} {c C : ℝ}
    (hf : Measurable f) (hc : 0 < c)
    (hlower : ∀ z, c ≤ f z) (hupper : ∀ z, f z ≤ C) (y : Y) :
    |entropy mu (fun x => f (x, y))| ≤
      2 * C * max |Real.log c| |Real.log C| := by
  let L := max |Real.log c| |Real.log C|
  let x0 : X := Classical.choice (nonempty_of_isProbabilityMeasure mu)
  have hCpos : 0 < C := hc.trans_le ((hlower (x0, y)).trans (hupper _))
  have hsecMeas : Measurable (fun x => f (x, y)) :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hsec : Integrable (fun x => f (x, y)) mu :=
    integrable_of_measurable_abs_le'' hsecMeas (fun x => by
      rw [abs_of_pos (hc.trans_le (hlower (x, y)))]
      exact hupper (x, y))
  have hflog : Integrable (fun x => f (x, y) * Real.log (f (x, y))) mu := by
    apply integrable_of_measurable_abs_le'' (C := C * L)
      ((hf.mul hf.log).comp (measurable_id.prodMk measurable_const))
    intro x
    change |f (x, y) * Real.log (f (x, y))| ≤ C * L
    rw [abs_mul, abs_of_pos (hc.trans_le (hlower (x, y)))]
    exact mul_le_mul (hupper _) (abs_log_le_of_mem_Icc hc (hlower _) (hupper _))
      (abs_nonneg _) hCpos.le
  have hmean := integral_section_mem_Icc mu (fun _ => hsec)
    (fun x _ => hlower (x, y)) (fun x _ => hupper (x, y)) y
  unfold entropy
  have hfirst : |∫ x, f (x, y) * Real.log (f (x, y)) ∂mu| ≤ C * L := by
    calc
      _ ≤ ∫ x, |f (x, y) * Real.log (f (x, y))| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x, C * L ∂mu := integral_mono hflog.abs (integrable_const _) (fun x => by
        rw [abs_mul, abs_of_pos (hc.trans_le (hlower (x, y)))]
        exact mul_le_mul (hupper _) (abs_log_le_of_mem_Icc hc (hlower _) (hupper _))
          (abs_nonneg _) hCpos.le)
      _ = C * L := by simp
  have hsecond : |(∫ x, f (x, y) ∂mu) * Real.log (∫ x, f (x, y) ∂mu)| ≤ C * L := by
    rw [abs_mul, abs_of_pos (hc.trans_le hmean.1)]
    exact mul_le_mul hmean.2 (abs_log_le_of_mem_Icc hc hmean.1 hmean.2)
      (abs_nonneg _) hCpos.le
  exact (abs_sub _ _).trans (by dsimp [L] at hfirst hsecond ⊢; linarith)

/-- If [two probability laws `mu,nu`](hyp:mu,nu) and [a measurable product function
`f`](hyp:hf) satisfy [a strictly positive lower bound `c`](hyp:hc,hlower) and [a finite upper
bound `C`](hyp:hupper), then [all regularity hypotheses for binary entropy tensorization hold](goal). -/
theorem entropyTensorizationIntegrable_of_bounded_positive
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : X × Y → ℝ) (hf : Measurable f) {c C : ℝ} (hc : 0 < c)
    (hlower : ∀ z, c ≤ f z) (hupper : ∀ z, f z ≤ C) :
    EntropyTensorizationIntegrable mu nu f := by
  have hCpos : 0 < C := by
    let x : X := Classical.choice (nonempty_of_isProbabilityMeasure mu)
    let y : Y := Classical.choice (nonempty_of_isProbabilityMeasure nu)
    exact hc.trans_le ((hlower (x, y)).trans (hupper (x, y)))
  let L := max |Real.log c| |Real.log C|
  have hfInt : Integrable f (mu.prod nu) :=
    integrable_of_measurable_abs_le'' hf (fun z => by
      rw [abs_of_pos (hc.trans_le (hlower z))]
      exact hupper z)
  have hflog : Integrable (fun z => f z * Real.log (f z)) (mu.prod nu) := by
    apply integrable_of_measurable_abs_le'' (by fun_prop)
    intro z
    rw [abs_mul, abs_of_pos (hc.trans_le (hlower z))]
    exact mul_le_mul (hupper z) (abs_log_le_of_mem_Icc hc (hlower z) (hupper z))
      (abs_nonneg _) hCpos.le
  have hsectionX (x : X) : Integrable (fun y => f (x, y)) nu :=
    integrable_of_measurable_abs_le'' (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => by rw [abs_of_pos (hc.trans_le (hlower (x, y)))]; exact hupper _)
  have hsectionY (y : Y) : Integrable (fun x => f (x, y)) mu :=
    integrable_of_measurable_abs_le'' (hf.comp (measurable_id.prodMk measurable_const))
      (fun x => by rw [abs_of_pos (hc.trans_le (hlower (x, y)))]; exact hupper _)
  let A : Y → ℝ := fun y => ∫ x, f (x, y) ∂mu
  have hAmeas : Measurable A := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hAbounds : ∀ y, c ≤ A y ∧ A y ≤ C :=
    integral_section_mem_Icc mu hsectionY
      (fun x y => hlower (x, y)) (fun x y => hupper (x, y))
  have hAlog : Integrable (fun y => A y * Real.log (A y)) nu := by
    apply integrable_of_measurable_abs_le'' (by fun_prop)
    intro y
    rw [abs_mul, abs_of_pos (hc.trans_le (hAbounds y).1)]
    exact mul_le_mul (hAbounds y).2
      (abs_log_le_of_mem_Icc hc (hAbounds y).1 (hAbounds y).2)
      (abs_nonneg _) hCpos.le
  have hmBounds : c ≤ ∫ y, A y ∂nu ∧ (∫ y, A y ∂nu) ≤ C :=
    integral_section_mem_Icc nu (fun _ =>
      integrable_of_measurable_abs_le'' hAmeas (fun y => by
        rw [abs_of_pos (hc.trans_le (hAbounds y).1)]; exact (hAbounds y).2))
      (fun y (_ : Unit) => (hAbounds y).1)
      (fun y (_ : Unit) => (hAbounds y).2) ()
  let m := ∫ y, A y ∂nu
  let R := max |Real.log (c / C)| |Real.log (C / c)|
  have hratio (y : Y) : c / C ≤ A y / m ∧ A y / m ≤ C / c := by
    have hmpos : 0 < m := hc.trans_le hmBounds.1
    constructor
    · apply (div_le_div_iff₀ hCpos hmpos).2
      exact (mul_le_mul_of_nonneg_left hmBounds.2 hc.le).trans
        (mul_le_mul_of_nonneg_right (hAbounds y).1 hCpos.le)
    · apply (div_le_div_iff₀ hmpos hc).2
      exact (mul_le_mul_of_nonneg_right (hAbounds y).2 hc.le).trans
        (mul_le_mul_of_nonneg_left hmBounds.1 hCpos.le)
  have hratioLower : 0 < c / C := div_pos hc hCpos
  have hfg : Integrable (fun z => f z * Real.log (A z.2 / m)) (mu.prod nu) := by
    apply integrable_of_measurable_abs_le'' (by fun_prop)
    intro z
    rw [abs_mul, abs_of_pos (hc.trans_le (hlower z))]
    exact mul_le_mul (hupper z)
      (abs_log_le_of_mem_Icc hratioLower (hratio z.2).1 (hratio z.2).2)
      (abs_nonneg _) hCpos.le
  have hfswap : Measurable (fun z : Y × X => f z.swap) := hf.comp measurable_swap
  have hEntropyMeas := measurable_entropy_section_of_bounded_positive nu hfswap hc
    (fun z => hlower z.swap) (fun z => hupper z.swap)
  have hEntropy : Integrable (fun x => entropy nu (fun y => f (x, y))) mu := by
    apply integrable_of_measurable_abs_le'' hEntropyMeas
    intro x
    exact abs_entropy_section_le nu hfswap hc
      (fun z => hlower z.swap) (fun z => hupper z.swap) x
  refine
    { hf := hfInt
      hflog := hflog
      hfpos := fun x y => hc.trans_le (hlower (x, y))
      hsectionMeanPos := ae_of_all _ fun x => hc.trans_le
        (integral_section_mem_Icc nu hsectionX
          (fun y x => hlower (x, y)) (fun y x => hupper (x, y)) x).1
      hAlog := hAlog
      hApos := ae_of_all _ fun y => hc.trans_le (hAbounds y).1
      hm := hc.trans_le hmBounds.1
      hfg := by simpa [A, m] using hfg
      hEntropy := hEntropy }

private theorem measurable_coordinateEntropySum_param
    {X : Type u} [MeasurableSpace X]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (n : ℕ) {P : Type u} [MeasurableSpace P]
    (f : P × (Fin n → X) → ℝ) (hf : Measurable f)
    {c C : ℝ} (hc : 0 < c) (hlower : ∀ z, c ≤ f z) (hupper : ∀ z, f z ≤ C) :
    Measurable (fun p => coordinateEntropySum mu n (fun s => f (p, s))) ∧
      ∀ p, |coordinateEntropySum mu n (fun s => f (p, s))| ≤
        (n : ℝ) * (2 * C * max |Real.log c| |Real.log C|) := by
  induction n generalizing P mu with
  | zero => simp [coordinateEntropySum]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu : Measure (Fin n → X) := Measure.pi (fun j : Fin n => mu (j.val + 1))
      let headIntegrand : X × (P × (Fin n → X)) → ℝ := fun q =>
        f (q.2.1, e.symm (q.1, q.2.2))
      have hheadMeas : Measurable headIntegrand := by
        dsimp [headIntegrand]
        fun_prop
      have hheadLower : ∀ z, c ≤ headIntegrand z := fun z => hlower _
      have hheadUpper : ∀ z, headIntegrand z ≤ C := fun z => hupper _
      have hheadEntropy : Measurable (fun q : P × (Fin n → X) =>
          entropy (mu 0) (fun x => headIntegrand (x, q))) :=
        measurable_entropy_section_of_bounded_positive (mu 0)
          hheadMeas hc hheadLower hheadUpper
      have hfirst : Measurable (fun p => ∫ rest,
          entropy (mu 0) (fun x => f (p, e.symm (x, rest))) ∂nu) := by
        exact hheadEntropy.stronglyMeasurable.integral_prod_right'.measurable
      let tailIntegrand : (P × X) × (Fin n → X) → ℝ := fun q =>
        f (q.1.1, e.symm (q.1.2, q.2))
      have htailMeas : Measurable tailIntegrand := by
        dsimp [tailIntegrand]
        fun_prop
      have htail := ih (P := P × X) (fun i => mu (i + 1)) tailIntegrand htailMeas
        (by
          intro (z : (P × X) × (Fin n → X))
          change c ≤ f (z.1.1, e.symm (z.1.2, z.2))
          exact hlower _)
        (by
          intro (z : (P × X) × (Fin n → X))
          change f (z.1.1, e.symm (z.1.2, z.2)) ≤ C
          exact hupper _)
      have hsecond : Measurable (fun p => ∫ x,
          coordinateEntropySum (fun i => mu (i + 1)) n
            (fun rest => f (p, e.symm (x, rest))) ∂mu 0) := by
        exact htail.1.stronglyMeasurable.integral_prod_right'.measurable
      constructor
      · change Measurable (fun p =>
            (∫ rest, entropy (mu 0) (fun x => f (p, e.symm (x, rest))) ∂nu) +
              ∫ x, coordinateEntropySum (fun i => mu (i + 1)) n
                (fun rest => f (p, e.symm (x, rest))) ∂mu 0)
        exact hfirst.add hsecond
      · intro p
        let K := 2 * C * max |Real.log c| |Real.log C|
        have hCpos : 0 < C := by
          let x : X := Classical.choice (nonempty_of_isProbabilityMeasure (mu 0))
          let s : Fin n → X := fun _ => x
          exact hc.trans_le ((hlower (p, e.symm (x, s))).trans (hupper _))
        have hKnonneg : 0 ≤ K := by
          dsimp [K]
          positivity
        have hheadBound : ∀ rest,
            |entropy (mu 0) (fun x => f (p, e.symm (x, rest)))| ≤ K := by
          intro rest
          exact abs_entropy_section_le (mu 0) hheadMeas hc
            hheadLower hheadUpper (p, rest)
        have hfirstBound :
            |∫ rest, entropy (mu 0) (fun x => f (p, e.symm (x, rest))) ∂nu| ≤ K := by
          calc
            _ ≤ ∫ rest, |entropy (mu 0) (fun x => f (p, e.symm (x, rest)))| ∂nu :=
              abs_integral_le_integral_abs
            _ ≤ ∫ _rest, K ∂nu := by
              apply integral_mono
              · have hm : Measurable (fun rest =>
                    entropy (mu 0) (fun x => f (p, e.symm (x, rest)))) :=
                    hheadEntropy.comp (measurable_const.prodMk measurable_id)
                apply integrable_of_measurable_abs_le''
                  (by simpa [Real.norm_eq_abs] using hm.norm)
                intro rest
                rw [abs_of_nonneg (abs_nonneg _)]
                exact hheadBound rest
              · exact integrable_const K
              · exact hheadBound
            _ = K := by simp [nu]
        have htailBound : ∀ x,
            |coordinateEntropySum (fun i => mu (i + 1)) n
              (fun rest => f (p, e.symm (x, rest)))| ≤ (n : ℝ) * K := by
          intro x
          exact htail.2 (p, x)
        have hsecondBound :
            |∫ x, coordinateEntropySum (fun i => mu (i + 1)) n
              (fun rest => f (p, e.symm (x, rest))) ∂mu 0| ≤ (n : ℝ) * K := by
          calc
            _ ≤ ∫ x, |coordinateEntropySum (fun i => mu (i + 1)) n
                (fun rest => f (p, e.symm (x, rest)))| ∂mu 0 :=
              abs_integral_le_integral_abs
            _ ≤ ∫ _x, (n : ℝ) * K ∂mu 0 := by
              apply integral_mono
              · have hm : Measurable (fun x =>
                    coordinateEntropySum (fun i => mu (i + 1)) n
                      (fun rest => f (p, e.symm (x, rest)))) :=
                    htail.1.comp (measurable_const.prodMk measurable_id)
                apply integrable_of_measurable_abs_le''
                  (by simpa [Real.norm_eq_abs] using hm.norm)
                intro x
                rw [abs_of_nonneg (abs_nonneg _)]
                exact htailBound x
              · exact integrable_const _
              · exact htailBound
            _ = (n : ℝ) * K := by simp
        change |(∫ rest, entropy (mu 0) (fun x => f (p, e.symm (x, rest))) ∂nu) +
            ∫ x, coordinateEntropySum (fun i => mu (i + 1)) n
              (fun rest => f (p, e.symm (x, rest))) ∂mu 0| ≤
          ((n + 1 : ℕ) : ℝ) * K
        calc
          _ ≤ |∫ rest, entropy (mu 0) (fun x => f (p, e.symm (x, rest))) ∂nu| +
              |∫ x, coordinateEntropySum (fun i => mu (i + 1)) n
                (fun rest => f (p, e.symm (x, rest))) ∂mu 0| := abs_add_le _ _
          _ ≤ K + (n : ℝ) * K := add_le_add hfirstBound hsecondBound
          _ = ((n + 1 : ℕ) : ℝ) * K := by push_cast; ring

/-- If [the coordinate laws `mu` are probability laws](hyp:hprob), [a measurable function
`f`](hyp:hf) on an `n`-fold product is [bounded below by a positive constant `c`](hyp:hc,hlower)
and [above by a finite constant `C`](hyp:hupper), then [all finite entropy-tensorization
regularity conditions hold](goal). -/
theorem finiteTensorizationRegularity_of_bounded_positive
    {X : Type*} [MeasurableSpace X]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    {c C : ℝ} (hc : 0 < c) (hlower : ∀ s, c ≤ f s) (hupper : ∀ s, f s ≤ C) :
    FiniteTensorizationRegularity mu n f := by
  induction n generalizing mu with
  | zero => trivial
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let nu : Measure (Fin n → X) := Measure.pi (fun j : Fin n => mu (j.val + 1))
      let g : X × (Fin n → X) → ℝ := fun p => f (e.symm p)
      have hg : Measurable g := hf.comp e.symm.measurable
      have hbin : EntropyTensorizationIntegrable (mu 0) nu g :=
        entropyTensorizationIntegrable_of_bounded_positive (mu 0) nu g hg hc
          (fun z => hlower _) (fun z => hupper _)
      have htail : ∀ x, FiniteTensorizationRegularity (fun i => mu (i + 1)) n
          (fun rest => f (e.symm (x, rest))) := by
        intro x
        exact ih (fun i => mu (i + 1)) (fun rest => f (e.symm (x, rest)))
          (hf.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id)))
          (fun rest => hlower _) (fun rest => hupper _)
      let gswap : (Fin n → X) × X → ℝ := fun q => f (e.symm (q.2, q.1))
      have hgswap : Measurable gswap := by
        dsimp [gswap]
        fun_prop
      have hEntropyMeas : Measurable (fun x => entropy nu
          (fun rest => f (e.symm (x, rest)))) :=
        measurable_entropy_section_of_bounded_positive nu hgswap hc
          (fun z => hlower _) (fun z => hupper _)
      have hEntropyInt : Integrable (fun x => entropy nu
          (fun rest => f (e.symm (x, rest)))) (mu 0) := by
        apply integrable_of_measurable_abs_le'' hEntropyMeas
        intro x
        exact abs_entropy_section_le nu hgswap hc
          (fun z => hlower _) (fun z => hupper _) x
      let tailParam : X × (Fin n → X) → ℝ := fun p => f (e.symm p)
      have hsum := measurable_coordinateEntropySum_param
        (fun i => mu (i + 1)) n tailParam hg hc
        (fun z => hlower _) (fun z => hupper _)
      have hsumInt : Integrable (fun x =>
          coordinateEntropySum (fun i => mu (i + 1)) n
            (fun rest => f (e.symm (x, rest)))) (mu 0) := by
        exact integrable_of_measurable_abs_le'' hsum.1 hsum.2
      exact ⟨hbin, htail, hEntropyInt, hsumInt⟩

end Causalean.Stat.Concentration.EntropyMethod
