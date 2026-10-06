module
public import Causalean.Stat.UStatistic.LocalizedVariance.Basic

/-!
# Integration over distinct product coordinates

These lemmas identify integrals of functions of two, three, and four distinct sample
coordinates with their independent iterated integrals. The bounded measurable form is
suited to products of bounded localized kernels and weights.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]

/-- For a [probability law](hyp:P), [two distinct coordinates](hyp:hij), [measurable
two-variable function](hyp:f,hf), and [uniform bound](hyp:B,hB), [the finite-product integral
equals the two independent-draw integral](goal). -/
theorem integral_two_coordinates {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (f : X → X → ℝ) (hf : Measurable fun z : X × X => f z.1 z.2)
    (B : ℝ) (hB : ∀ x y, |f x y| ≤ B) :
    ∫ ω, f (ω i) (ω j) ∂iidLaw P n = ∫ x, ∫ y, f x y ∂P ∂P := by
  -- Use independence of the two coordinate projections under `Measure.pi` to identify
  -- their joint law with `P.prod P`; bounded measurability supplies integrability.
  have hcoord : iIndepFun (fun a : Fin n => fun ω : Fin n → X => ω a) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair : (iidLaw P n).map (fun ω => (ω i, ω j)) = P.prod P := by
    letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
    have hind := hcoord.indepFun hij
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) j).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable)
  have hfi : Integrable (fun z : X × X => f z.1 z.2) (P.prod P) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall (by
      intro z
      simpa only [Real.norm_eq_abs] using hB z.1 z.2))
  calc
    _ = ∫ z : X × X, f z.1 z.2 ∂(iidLaw P n).map (fun ω => (ω i, ω j)) := by
      rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ z : X × X, f z.1 z.2 ∂(P.prod P) := by rw [hpair]
    _ = _ := integral_prod _ hfi

/-- For a [probability law](hyp:P), [three pairwise distinct coordinates](hyp:hij,hik,hjk),
[measurable three-variable function](hyp:f,hf), and [uniform bound](hyp:B,hB), [the
finite-product integral equals the three independent-draw integral](goal). -/
theorem integral_three_coordinates {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (f : X → X → X → ℝ)
    (hf : Measurable fun z : (X × X) × X => f z.1.1 z.1.2 z.2)
    (B : ℝ) (hB : ∀ x y z, |f x y z| ≤ B) :
    ∫ ω, f (ω i) (ω j) (ω k) ∂iidLaw P n =
      ∫ x, ∫ y, ∫ z, f x y z ∂P ∂P ∂P := by
  -- Push the product law along the three distinct coordinate projections, then
  -- apply Fubini twice. A reusable finite-coordinate map theorem may shorten this.
  letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hcoord : iIndepFun (fun a : Fin n => fun ω : Fin n → X => ω a) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair : (iidLaw P n).map (fun ω => (ω i, ω j)) = P.prod P := by
    have hind := hcoord.indepFun hij
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) j).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable)
  have htriple : (iidLaw P n).map (fun ω => ((ω i, ω j), ω k)) =
      (P.prod P).prod P := by
    have hind := hcoord.indepFun_prodMk (fun a => measurable_pi_apply a) i j k hik hjk
    have h := hind.map_prod_eq_prod_map_map
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      (measurable_pi_apply k).aemeasurable
    rw [hpair] at h
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) k).map_eq,
      iidLaw] using h
  have hfi : Integrable (fun z : (X × X) × X => f z.1.1 z.1.2 z.2)
      ((P.prod P).prod P) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall (by
      intro z
      simpa only [Real.norm_eq_abs] using hB z.1.1 z.1.2 z.2))
  calc
    _ = ∫ z : (X × X) × X, f z.1.1 z.1.2 z.2 ∂
        (iidLaw P n).map (fun ω => ((ω i, ω j), ω k)) := by
      rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ z : (X × X) × X, f z.1.1 z.1.2 z.2 ∂((P.prod P).prod P) := by rw [htriple]
    _ = ∫ z : X × X, ∫ w : X, f z.1 z.2 w ∂P ∂(P.prod P) := integral_prod _ hfi
    _ = _ := by
      exact integral_prod _ hfi.integral_prod_left

/-- For a [probability law](hyp:P), [four pairwise distinct coordinates](hyp:hij,hik,hil,hjk,hjl,hkl),
[measurable four-variable function](hyp:f,hf), and [uniform bound](hyp:B,hB), [the
finite-product integral equals the four independent-draw integral](goal). -/
theorem integral_four_coordinates {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (f : X → X → X → X → ℝ)
    (hf : Measurable fun z : ((X × X) × X) × X => f z.1.1.1 z.1.1.2 z.1.2 z.2)
    (B : ℝ) (hB : ∀ x y z w, |f x y z w| ≤ B) :
    ∫ ω, f (ω i) (ω j) (ω k) (ω l) ∂iidLaw P n =
      ∫ x, ∫ y, ∫ z, ∫ w, f x y z w ∂P ∂P ∂P ∂P := by
  -- As above for four projections; use the independent coordinate family
  -- `iIndepFun_pi` and a product-law characterization of the joint map.
  letI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hcoord : iIndepFun (fun a : Fin n => fun ω : Fin n → X => ω a) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hpair₁ : (iidLaw P n).map (fun ω => (ω i, ω j)) = P.prod P := by
    have hind := hcoord.indepFun hij
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) j).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable)
  have hpair₂ : (iidLaw P n).map (fun ω => (ω k, ω l)) = P.prod P := by
    have hind := hcoord.indepFun hkl
    simpa only [(measurePreserving_eval (fun _ : Fin n => P) k).map_eq,
      (measurePreserving_eval (fun _ : Fin n => P) l).map_eq, iidLaw] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply k).aemeasurable
        (measurable_pi_apply l).aemeasurable)
  have hfour : (iidLaw P n).map (fun ω => ((ω i, ω j), (ω k, ω l))) =
      (P.prod P).prod (P.prod P) := by
    have hind := hcoord.indepFun_prodMk_prodMk (fun a => measurable_pi_apply a)
      i j k l hik hil hjk hjl
    have h := hind.map_prod_eq_prod_map_map
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      ((measurable_pi_apply k).prodMk (measurable_pi_apply l)).aemeasurable
    rw [hpair₁, hpair₂] at h
    simpa only using h
  have hmeas : Measurable (fun z : (X × X) × (X × X) =>
      f z.1.1 z.1.2 z.2.1 z.2.2) := by
    have hassoc : Measurable (fun z : (X × X) × (X × X) => ((z.1, z.2.1), z.2.2)) :=
      by fun_prop
    exact hf.comp hassoc
  have hfi : Integrable (fun z : (X × X) × (X × X) =>
      f z.1.1 z.1.2 z.2.1 z.2.2) ((P.prod P).prod (P.prod P)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable B (Filter.Eventually.of_forall (by
      intro z
      simpa only [Real.norm_eq_abs] using hB z.1.1 z.1.2 z.2.1 z.2.2))
  have hinner (p : X × X) : Integrable (fun q : X × X => f p.1 p.2 q.1 q.2)
      (P.prod P) :=
    Integrable.of_bound
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall (by
        intro q
        simpa only [Real.norm_eq_abs] using hB p.1 p.2 q.1 q.2))
  calc
    _ = ∫ z : (X × X) × (X × X), f z.1.1 z.1.2 z.2.1 z.2.2 ∂
        (iidLaw P n).map (fun ω => ((ω i, ω j), (ω k, ω l))) := by
      rw [integral_map (by fun_prop) hmeas.aestronglyMeasurable]
    _ = ∫ z : (X × X) × (X × X), f z.1.1 z.1.2 z.2.1 z.2.2 ∂
        ((P.prod P).prod (P.prod P)) := by rw [hfour]
    _ = ∫ p : X × X, ∫ q : X × X, f p.1 p.2 q.1 q.2 ∂(P.prod P) ∂(P.prod P) :=
      integral_prod _ hfi
    _ = ∫ p : X × X, ∫ z : X, ∫ w : X, f p.1 p.2 z w ∂P ∂P ∂(P.prod P) := by
      congr 1
      funext p
      exact integral_prod _ (hinner p)
    _ = _ := integral_prod _ (by
      convert hfi.integral_prod_left using 1
      funext p
      exact (integral_prod _ (hinner p)).symm)

end Causalean.Stat.UStatistic.LocalizedVariance
