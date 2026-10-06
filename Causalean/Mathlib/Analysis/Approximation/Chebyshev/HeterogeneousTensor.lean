module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorExtraction
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Heterogeneous tensor Jackson convolution

This module defines product Jackson convolution for an arbitrary finite coordinate type with a
separate order in every coordinate.  It establishes integrability, parameter measurability, and
the period-box translation identity used by the algebraic extraction layer.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

/-- The normalized cube [is the set of coordinate vectors with every entry between minus one and one](goal).
[This set](step:1) is specified coordinatewise. -/
def cube : Set (ι → ℝ) := {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- The period box [is the set of angle vectors with every entry between minus π and π](goal).
[This set](step:1) is specified coordinatewise. -/
def periodBox : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ : ι => Set.Icc (-Real.pi) Real.pi)

/-- [An angle vector](hyp:x) determines [its coordinatewise cosine point](goal).
[The point](step:1) applies cosine in every coordinate. -/
def cosPoint (x : ι → ℝ) : ι → ℝ := fun i => Real.cos (x i)

/-- [A coordinate-specific order map](hyp:d) and [an angle vector](hyp:u) determine [the heterogeneous Jackson kernel](goal).
[The kernel](step:1) is the finite product of the one-dimensional Jackson kernels. -/
def kernel (d : ι → ℕ) (u : ι → ℝ) : ℝ :=
  ∏ i, Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d i) (u i)

/-- [A coordinate-specific order map](hyp:d), [a cube target](hyp:f), and [a phase vector](hyp:x) determine [the heterogeneous Jackson convolution](goal).
[The convolution](step:1) integrates the translated cosine lift against the product kernel over the period box. -/
def convolution (d : ι → ℕ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ u in periodBox, f (cosPoint (x - u)) * kernel d u

/-- For [a coordinate-specific order map](hyp:d), [a target function](hyp:f) that is
[measurable](hyp:hf), [a real bound B](hyp:B) such that [the target is at most B in absolute value
on the cube](hyp:hB), and [a phase vector](hyp:x), [the heterogeneous Jackson integrand, the
translated cosine lift of the target times the product kernel, is integrable on the period
box](goal). -/
theorem integrableOn_convolution_integrand (d : ι → ℕ)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x ∈ cube, |f x| ≤ B) (x : ι → ℝ) :
    IntegrableOn (fun u => f (cosPoint (x - u)) * kernel d u) periodBox := by
  have hcos : Continuous (fun u : ι → ℝ => cosPoint (x - u)) := by
    unfold cosPoint
    fun_prop
  have hk : Continuous (kernel d) := by
    unfold kernel
    fun_prop (disch := exact Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
  have hbox : IsCompact (periodBox (ι := ι)) := by
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hki : IntegrableOn (kernel d) periodBox :=
    hk.continuousOn.integrableOn_compact hbox
  have hmeas : Measurable (fun u => f (cosPoint (x - u)) * kernel d u) :=
    ((hf.comp hcos.measurable).mul hk.measurable)
  apply Integrable.mono' (hki.norm.const_mul B) hmeas.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hbox.measurableSet] with u hu
  have hfB : |f (cosPoint (x - u))| ≤ B := hB _ (by
    intro i
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  simpa [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hfB (abs_nonneg (kernel d u))

/-- [A coordinate-specific order map](hyp:d), [a parameter-indexed target](hyp:g), [its joint measurability](hyp:hg), and [a fixed phase vector](hyp:x) imply that [the heterogeneous convolution is measurable in the parameter](goal). -/
@[fun_prop] theorem measurable_convolution (d : ι → ℕ)
    (g : Ω → (ι → ℝ) → ℝ)
    (hg : Measurable (fun z : Ω × (ι → ℝ) => g z.1 z.2))
    (x : ι → ℝ) : Measurable (fun ω => convolution d (g ω) x) := by
  have hcos : Measurable (fun u : ι → ℝ => cosPoint (x - u)) := by
    unfold cosPoint
    fun_prop
  have hk : Measurable (kernel d) := by
    unfold kernel
    fun_prop (disch := exact Causalean.Mathlib.Analysis.JacksonApproximation.measurable_jackson _)
  have hpair : Measurable (fun z : Ω × (ι → ℝ) => (z.1, cosPoint (x - z.2))) :=
    measurable_fst.prodMk (hcos.comp measurable_snd)
  have h : Measurable (fun z : Ω × (ι → ℝ) =>
      g z.1 (cosPoint (x - z.2)) * kernel d z.2) :=
    (hg.comp hpair).mul (hk.comp measurable_snd)
  simpa only [convolution] using
    (h.stronglyMeasurable.integral_prod_right'
      (ν := (volume.restrict periodBox))).measurable

variable [DecidableEq ι]

/-- [A finite dimension](hyp:n), [a function on its phase vectors](hyp:F), [its measurability](hyp:hF), [a uniform bound](hyp:B), [the bound on every vector](hyp:hB), [coordinatewise periodicity](hyp:hper), and [a translation vector](hyp:x) imply that [reflection and translation leave the period-box integral unchanged](goal). -/
theorem periodBox_integral_sub_eq_fin (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Measurable F) (B : ℝ) (hB : ∀ y, |F y| ≤ B)
    (hper : ∀ i y,
      Function.Periodic (fun t => F (Function.update y i t)) (2 * Real.pi))
    (x : Fin n → ℝ) :
    (∫ u in periodBox, F (x - u)) = ∫ u in periodBox, F u := by
  classical
  have hsplit : ∀ {m : ℕ} (G : (Fin (m + 1) → ℝ) → ℝ),
      Measurable G → (∀ y, |G y| ≤ B) →
      (∫ u in periodBox, G u) =
        ∫ t in Set.Icc (-Real.pi) Real.pi,
          ∫ v in periodBox, G (Fin.insertNth 0 t v) := by
    intro m G hG hGb
    let e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
    have hem : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _
    have he : e ⁻¹' periodBox =
        Set.Icc (-Real.pi) Real.pi ×ˢ periodBox := by
      ext z
      simp only [Set.mem_preimage, periodBox, Set.mem_prod]
      constructor
      · intro h
        constructor
        · simpa [e] using h 0 (Set.mem_univ _)
        · intro i hi
          simpa [e] using h i.succ (Set.mem_univ _)
      · rintro ⟨h0, hs⟩ i
        intro _
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [e] using h0
        · simpa [e] using hs j (Set.mem_univ _)
    rw [← hem.setIntegral_preimage_emb e.measurableEmbedding, he,
      Measure.volume_eq_prod, setIntegral_prod]
    · rfl
    · have hm : Measurable (fun z : ℝ × (Fin m → ℝ) =>
          G (Fin.insertNth 0 z.1 z.2)) :=
        hG.comp (by fun_prop)
      have hc : IsCompact (Set.Icc (-Real.pi) Real.pi ×ˢ
          periodBox (ι := Fin m)) :=
        isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
      apply Measure.integrableOn_of_bounded (hc.measure_lt_top.ne)
        hm.aestronglyMeasurable
      filter_upwards with z
      simpa [Real.norm_eq_abs] using hGb (Fin.insertNth 0 z.1 z.2)
  induction n with
  | zero =>
      congr 1
      funext u
      congr 1
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      have hsub : Measurable (fun u : Fin (m + 1) → ℝ => x - u) := by
        fun_prop
      rw [hsplit (fun u => F (x - u)) (hF.comp hsub) (fun y => hB _)]
      have hxsub (t : ℝ) (v : Fin m → ℝ) :
          x - Fin.insertNth 0 t v =
            Fin.insertNth 0 (x 0 - t) ((x ∘ Fin.succ) - v) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      simp_rw [hxsub]
      have hinner (t : ℝ) :
          (∫ v in periodBox,
              F (Fin.insertNth 0 (x 0 - t) ((x ∘ Fin.succ) - v))) =
            ∫ v in periodBox, F (Fin.insertNth 0 (x 0 - t) v) := by
        let G : (Fin m → ℝ) → ℝ := fun v => F (Fin.insertNth 0 (x 0 - t) v)
        apply ih G
        · exact hF.comp (by fun_prop)
        · intro y
          exact hB _
        · intro i y
          have hp := hper i.succ (Fin.insertNth 0 (x 0 - t) y)
          intro s
          change G (Function.update y i (s + 2 * Real.pi)) =
            G (Function.update y i s)
          dsimp [G]
          have hu (r : ℝ) :
              Fin.insertNth 0 (x 0 - t) (Function.update y i r) =
                (Function.update (Fin.insertNth 0 (x 0 - t) y) i.succ r :
                  Fin (m + 1) → ℝ) := by
            funext j
            refine Fin.cases ?_ (fun k => ?_) j
            · have hne : (0 : Fin (m + 1)) ≠ i.succ :=
                ne_of_lt (Fin.succ_pos i)
              simp [Function.update, hne]
            · by_cases hki : k = i
              · subst k
                simp
              · simp [hki]
          rw [hu, hu]
          exact hp s
      simp_rw [hinner]
      let A : ℝ → ℝ := fun s => ∫ v in periodBox, F (Fin.insertNth 0 s v)
      have hAp : Function.Periodic A (2 * Real.pi) := by
        intro s
        apply integral_congr_ae
        filter_upwards
        intro v
        have hp := hper 0 (Fin.insertNth 0 s v) s
        simpa using hp
      rw [show (fun t => ∫ v in periodBox, F (Fin.insertNth 0 (x 0 - t) v)) =
          fun t => A (x 0 - t) by rfl]
      rw [show (∫ t in Set.Icc (-Real.pi) Real.pi, A (x 0 - t)) =
          ∫ t in (-Real.pi)..Real.pi, A (x 0 - t) by
        rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
          ← integral_Icc_eq_integral_Ioc]]
      rw [intervalIntegral.integral_comp_sub_left]
      have hshift := hAp.intervalIntegral_add_eq (x 0 - Real.pi) (-Real.pi)
      have heq : (∫ t in (x 0 - Real.pi)..(x 0 - -Real.pi), A t) =
          ∫ t in (-Real.pi)..Real.pi, A t := by
        convert hshift using 1 <;> ring
      rw [heq]
      rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        ← integral_Icc_eq_integral_Ioc]
      rw [hsplit F hF hB]

/-- [A function on finitely many phase coordinates](hyp:F), [its measurability](hyp:hF), [a uniform bound](hyp:B), [the bound on every vector](hyp:hB), [coordinatewise periodicity](hyp:hper), and [a translation vector](hyp:x) imply that [reflection and translation leave the period-box integral unchanged](goal). -/
theorem periodBox_integral_sub_eq (F : (ι → ℝ) → ℝ)
    (hF : Measurable F) (B : ℝ) (hB : ∀ y, |F y| ≤ B)
    (hper : ∀ i y,
      Function.Periodic (fun t => F (Function.update y i t)) (2 * Real.pi))
    (x : ι → ℝ) :
    (∫ u in periodBox, F (x - u)) = ∫ u in periodBox, F u := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let p : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp (u : Fin (Fintype.card ι) → ℝ) (i : Fin (Fintype.card ι)) :
      p u (e i) = u i := by
    simp [p, MeasurableEquiv.coe_piCongrLeft]
  have hbox : p ⁻¹' periodBox = periodBox := by
    ext u
    constructor
    · intro hu i _
      exact hp u i ▸ hu (e i) (Set.mem_univ _)
    · intro hu i _
      obtain ⟨j, rfl⟩ := e.surjective i
      rw [hp]
      exact hu j (Set.mem_univ _)
  have hmp : MeasurePreserving p :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have htrans (H : (ι → ℝ) → ℝ) :
      (∫ u in periodBox, H u) = ∫ v in periodBox, H (p v) := by
    rw [← hmp.setIntegral_preimage_emb p.measurableEmbedding, hbox]
  let G : (Fin (Fintype.card ι) → ℝ) → ℝ := fun u => F (p u)
  have hG : Measurable G := hF.comp p.measurable
  have hGb : ∀ y, |G y| ≤ B := fun y => hB (p y)
  have hupdate (y : Fin (Fintype.card ι) → ℝ)
      (i : Fin (Fintype.card ι)) (t : ℝ) :
      p (Function.update y i t) = Function.update (p y) (e i) t := by
    funext j
    obtain ⟨k, rfl⟩ := e.surjective j
    simp [hp, Function.update, e.injective.eq_iff]
  have hGp : ∀ i y,
      Function.Periodic (fun t => G (Function.update y i t)) (2 * Real.pi) := by
    intro i y t
    change F (p (Function.update y i (t + 2 * Real.pi))) =
      F (p (Function.update y i t))
    rw [hupdate, hupdate]
    exact hper (e i) (p y) t
  let x' : Fin (Fintype.card ι) → ℝ := p.symm x
  have hsub (u : Fin (Fintype.card ι) → ℝ) :
      p (x' - u) = x - p u := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [hp]
    change x' j - u j = x (e j) - p u (e j)
    rw [hp]
    congr 1
  rw [htrans (fun u => F (x - u)), htrans F]
  change (∫ u in periodBox, F (x - p u)) = ∫ u in periodBox, G u
  simp_rw [← hsub]
  exact periodBox_integral_sub_eq_fin (Fintype.card ι) G hG B hGb hGp x'

/-- For [a coordinate-specific positive order map](hyp:d,hd), [a measurable cube target](hyp:f,hf),
[a real bound B](hyp:B) such that [the target is at most B in absolute value on the cube](hyp:hB),
and [a phase vector x](hyp:x), [the heterogeneous Jackson convolution at x equals the integral over
the period box of the cosine lift of the target at v times the product kernel at x − v](goal). -/
theorem convolution_shifted (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ y ∈ cube, |f y| ≤ B) (x : ι → ℝ) :
    convolution d f x =
      ∫ v in periodBox, f (cosPoint v) * kernel d (x - v) := by
  classical
  let J (i : ι) : ℝ → ℝ :=
    Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d i)
  have hjp (i : ι) : Function.Periodic (J i) (2 * Real.pi) := by
    rcases Causalean.Mathlib.Analysis.JacksonApproximation.jackson_isTrigPolyLE
      (d i) (hd i) with ⟨a, b, hab⟩
    intro t
    change Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d i)
      (t + 2 * Real.pi) =
      Causalean.Mathlib.Analysis.JacksonApproximation.jackson (d i) t
    rw [hab, hab]
    apply Finset.sum_congr rfl
    intro k hk
    have hc : Real.cos ((k : ℝ) * (t + 2 * Real.pi)) =
        Real.cos ((k : ℝ) * t) := by
      rw [show (k : ℝ) * (t + 2 * Real.pi) =
          (k : ℝ) * t + k * (2 * Real.pi) by push_cast; ring,
        Real.cos_add_nat_mul_two_pi]
    have hs : Real.sin ((k : ℝ) * (t + 2 * Real.pi)) =
        Real.sin ((k : ℝ) * t) := by
      rw [show (k : ℝ) * (t + 2 * Real.pi) =
          (k : ℝ) * t + k * (2 * Real.pi) by push_cast; ring,
        Real.sin_add_nat_mul_two_pi]
    rw [hc, hs]
  have hjbound : ∀ i, ∃ C : ℝ, ∀ t, |J i t| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := ((hjp i).isBounded_of_continuous
      (by positivity) (by
        dsimp [J]
        exact Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)).exists_norm_le
    exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC _ ⟨t, rfl⟩⟩
  choose C hC using hjbound
  have hCnonneg (i : ι) : 0 ≤ C i :=
    le_trans (abs_nonneg _) (hC i 0)
  have hkernel (y : ι → ℝ) : |kernel d y| ≤ ∏ i, C i := by
    simp only [kernel, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hC i (y i))
  have hBnonneg : 0 ≤ B := by
    exact le_trans (abs_nonneg _) (hB (cosPoint (fun _ => 0)) (by
      intro i
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  let F : (ι → ℝ) → ℝ := fun v => f (cosPoint v) * kernel d (x - v)
  have hFm : Measurable F := by
    have hcos : Measurable (cosPoint (ι := ι)) := by
      unfold cosPoint
      fun_prop
    have hk : Measurable (fun v : ι → ℝ => kernel d (x - v)) := by
      unfold kernel
      fun_prop (disch := exact Causalean.Mathlib.Analysis.JacksonApproximation.measurable_jackson _)
    exact (hf.comp hcos).mul hk
  have hFb : ∀ y, |F y| ≤ B * ∏ i, C i := by
    intro y
    have hfy : |f (cosPoint y)| ≤ B := hB _ (by
      intro i
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    calc
      |F y| = |f (cosPoint y)| * |kernel d (x - y)| := by simp [F, abs_mul]
      _ ≤ B * |kernel d (x - y)| :=
        mul_le_mul_of_nonneg_right hfy (abs_nonneg _)
      _ ≤ B * ∏ i, C i := mul_le_mul_of_nonneg_left (hkernel _) hBnonneg
  have hFp : ∀ (i : ι) (y : ι → ℝ),
      Function.Periodic (fun t => F (Function.update y i t)) (2 * Real.pi) := by
    intro i y t
    dsimp [F, kernel, cosPoint]
    congr 1
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simpa [cosPoint] using Real.cos_add_two_pi t
      · simp [cosPoint, Function.update, hji]
    · apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp only [Function.update, if_pos rfl]
        change J i (x i - (t + 2 * Real.pi)) = J i (x i - t)
        convert (hjp i (x i - t - 2 * Real.pi)).symm using 1 <;> ring
      · simp only [Function.update]
        split <;> simp_all
  have ht := periodBox_integral_sub_eq F hFm (B * ∏ i, C i) hFb hFp x
  dsimp [F] at ht
  convert ht using 1
  · apply integral_congr_ae
    filter_upwards
    intro u
    congr 1
    · congr 1
      funext i
      change u i = x i - (x i - u i)
      ring

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor
