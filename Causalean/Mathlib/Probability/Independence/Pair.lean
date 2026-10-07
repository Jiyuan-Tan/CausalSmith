module

public import Mathlib.Probability.Independence.InfinitePi

/-!
# Paired independent families

This module transports indexed independence across a product probability space:
two independent families on separate samples become independent after their
corresponding coordinates are paired.
-/

public section

open MeasureTheory
open MeasureTheory.Measure
open ProbabilityTheory

namespace Causalean.Mathlib.Probability.Independence

variable {J Ω Ω' A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : J → Ω → A} {Y : J → Ω' → B}

/-- Given [an indexed collection of probability laws on the first value space](hyp:μj) and
[an indexed collection of probability laws on the second value space](hyp:νj), [pairing the
corresponding coordinates sends the product of their array laws to the array law with
coordinatewise product factors](goal). -/
theorem map_pair_infinitePi_prod
    (μj : J → Measure A) (νj : J → Measure B)
    [∀ j, IsProbabilityMeasure (μj j)]
    [∀ j, IsProbabilityMeasure (νj j)] :
    Measure.map (fun p : (J → A) × (J → B) => fun j => (p.1 j, p.2 j))
        ((infinitePi μj).prod (infinitePi νj)) =
      infinitePi (fun j => (μj j).prod (νj j)) := by
  classical
  apply eq_infinitePi
  intro s t ht
  have hfinite :
      Measure.map (fun p : (J → A) × (J → B) => fun j : s => (p.1 j, p.2 j))
          ((infinitePi μj).prod (infinitePi νj)) =
        Measure.pi (fun j : s => (μj j).prod (νj j)) := by
    have hprod := Measure.map_prod_map (infinitePi μj) (infinitePi νj)
      (Finset.measurable_restrict s) (Finset.measurable_restrict s)
    rw [infinitePi_map_restrict, infinitePi_map_restrict] at hprod
    have hpair := (measurePreserving_arrowProdEquivProdArrow A B s
      (fun j : s => μj j) (fun j : s => νj j)).symm.map_eq
    calc
      _ = Measure.map (fun q : (s → A) × (s → B) => fun j => (q.1 j, q.2 j))
            (Measure.map (Prod.map (s.restrict : (J → A) → (s → A))
              (s.restrict : (J → B) → (s → B)))
              ((infinitePi μj).prod (infinitePi νj))) := by
              rw [map_map (by fun_prop) (by fun_prop)]
              rfl
      _ = Measure.map (fun q : (s → A) × (s → B) => fun j => (q.1 j, q.2 j))
            ((Measure.pi (fun j : s => μj j)).prod
              (Measure.pi (fun j : s => νj j))) := by rw [← hprod]
      _ = _ := by simpa [MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow] using hpair
  calc
    _ = (Measure.pi (fun j : s => (μj j).prod (νj j)))
          (Set.univ.pi (fun j : s => t j)) := by
          rw [← hfinite]
          rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ => ht _)]
          rw [map_apply (by fun_prop) (.pi Set.countable_univ fun _ _ => ht _)]
          congr 1
          ext p
          simp [Set.mem_pi]
    _ = ∏ j : s, ((μj j).prod (νj j)) (t j) := by rw [Measure.pi_pi]
    _ = ∏ j ∈ s, ((μj j).prod (νj j)) (t j) := by
      simpa using (Finset.prod_attach s (fun j => ((μj j).prod (νj j)) (t j)))

/-- Given two probability spaces, [a measurable indexed family of observations on the
first](hyp:mX), [a measurable family with the same index set on the second](hyp:mY), [mutual
independence of the first family under its probability law](hyp:hX), and [mutual independence
of the second family under its probability law](hyp:hY), [the index-by-index pairs of
observations form a mutually independent family under the product of the two probability
laws](goal). -/
theorem iIndepFun_pair_prod
    (mX : ∀ j, Measurable (X j)) (mY : ∀ j, Measurable (Y j))
    (hX : iIndepFun X μ) (hY : iIndepFun Y ν) :
    iIndepFun (fun j p => (X j p.1, Y j p.2)) (μ.prod ν) := by
  let FX : Ω → J → A := fun ω j => X j ω
  let FY : Ω' → J → B := fun ω j => Y j ω
  have mFX : Measurable FX := measurable_pi_iff.mpr mX
  have mFY : Measurable FY := measurable_pi_iff.mpr mY
  have mPair : ∀ j, Measurable (fun p : Ω × Ω' => (X j p.1, Y j p.2)) := by
    intro j
    exact (mX j).comp measurable_fst |>.prodMk ((mY j).comp measurable_snd)
  have hXm : μ.map FX = infinitePi (fun j => μ.map (X j)) :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map mX).mp hX
  have hYm : ν.map FY = infinitePi (fun j => ν.map (Y j)) :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map mY).mp hY
  have hcoord (j : J) :
      (μ.prod ν).map (fun p : Ω × Ω' => (X j p.1, Y j p.2)) =
        (μ.map (X j)).prod (ν.map (Y j)) := by
    calc
      _ = (μ.prod ν).map (Prod.map (X j) (Y j)) := by
        congr 1
      _ = _ := (Measure.map_prod_map μ ν (mX j) (mY j)).symm
  letI : ∀ j, IsProbabilityMeasure (μ.map (X j)) :=
    fun j => Measure.isProbabilityMeasure_map (mX j).aemeasurable
  letI : ∀ j, IsProbabilityMeasure (ν.map (Y j)) :=
    fun j => Measure.isProbabilityMeasure_map (mY j).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map mPair).mpr
  calc
    (μ.prod ν).map (fun p : Ω × Ω' => fun j => (X j p.1, Y j p.2)) =
        Measure.map (fun q : (J → A) × (J → B) => fun j => (q.1 j, q.2 j))
          ((μ.map FX).prod (ν.map FY)) := by
            rw [Measure.map_prod_map μ ν mFX mFY,
              Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = Measure.map (fun q : (J → A) × (J → B) => fun j => (q.1 j, q.2 j))
          ((infinitePi (fun j => μ.map (X j))).prod
            (infinitePi (fun j => ν.map (Y j)))) := by rw [hXm, hYm]
    _ = infinitePi (fun j => (μ.map (X j)).prod (ν.map (Y j))) :=
      map_pair_infinitePi_prod _ _
    _ = infinitePi (fun j => (μ.prod ν).map
          (fun p : Ω × Ω' => (X j p.1, Y j p.2))) := by simp_rw [hcoord]

end Causalean.Mathlib.Probability.Independence
