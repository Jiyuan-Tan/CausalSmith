module
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.AeDescent
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.BernsteinKernel
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformTaggedRank
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Rank-weighted concomitant expectation

Continuous CDF transport of iid sorting coordinates, almost-sure rank
equivalence, and the conditional-mean and tagged-rank ingredients of the
Bernstein-kernel expectation of bounded marks; the expectation formula itself
is proved in `ConcomitantExpectation`.

Proof route: apply `Measure.pi_map_pi` to the one-coordinate CDF transport.
Uniform coordinates have no ties; strict ordering is therefore preserved by
the monotone CDF almost surely. Conditional expectation against the CDF's
comap sigma algebra replaces each mark by `m(U)`. The rank of one tagged
uniform observation has the binomial cell kernel. Pull almost-everywhere
measurability and bounds of `m` back along the measure-preserving CDF map.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic
open scoped BigOperators

noncomputable section

/-- For [cell weights](hyp:a) and a [sample of sorting coordinates with marks](hyp:x), the
 [rank-weighted concomitant statistic](goal) sums each sorted mark against its cell weight. -/
def rankConcomitant {N : ℕ} (a : Fin N → ℝ) (x : Fin N → ℝ × ℝ) : ℝ :=
  ∑ j : Fin N, a j * (x (Tuple.sort (fun i => (x i).1) j)).2

/-- For a [probability law of marked observations](hyp:μ) whose
 [sorting-coordinate CDF is continuous](hyp:hcont),
 [the coordinatewise CDF pushforward of the iid sample is iid unit-uniform](goal). -/
theorem cdf_transport_iid {N : ℕ} (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t)) :
    (Measure.pi (fun _ : Fin N => μ)).map
      (fun x i => ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1) =
      iidSample uniform01 N := by
  have hfst : Measurable (Prod.fst : ℝ × ℝ → ℝ) := measurable_fst
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map hfst.aemeasurable
  have hmap : μ.map (fun p : ℝ × ℝ =>
      ProbabilityTheory.cdf (μ.map Prod.fst) p.1) = uniform01 := by
    simpa only [Function.comp_def] using
      (Measure.map_map hcont.measurable hfst).symm.trans
        (cdf_pushforward_of_continuous (μ.map Prod.fst) hcont)
  change (Measure.pi (fun _ : Fin N => μ)).map
      (fun x i => ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1) =
      Measure.pi (fun _ : Fin N => uniform01)
  haveI : IsProbabilityMeasure (μ.map (fun p : ℝ × ℝ =>
      ProbabilityTheory.cdf (μ.map Prod.fst) p.1)) :=
    Measure.isProbabilityMeasure_map (hcont.measurable.comp hfst).aemeasurable
  haveI : ∀ _ : Fin N, SigmaFinite (μ.map (fun p : ℝ × ℝ =>
      ProbabilityTheory.cdf (μ.map Prod.fst) p.1)) := fun _ => inferInstance
  simpa only [Function.comp_def, hmap] using
    (Measure.pi_map_pi (μ := fun _ : Fin N => μ)
      (f := fun _ p => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
      (fun _ : Fin N =>
      (hcont.measurable.comp hfst).aemeasurable))

/-- For a [marked observation law](hyp:μ) with [continuous sorting-coordinate CDF](hyp:hcont),
 [original and CDF coordinates sort in the same order almost surely](goal). -/
theorem sort_cdf_eq_ae {N : ℕ} (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t)) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      Tuple.sort (fun i => (x i).1) =
        Tuple.sort (fun i => ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1) := by
  classical
  have hface (i j : Fin N) (hij : i ≠ j) :
      volume {u : Fin N → ℝ | u i = u j} = 0 := by
    let L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj i : (Fin N → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
    have hL : L ≠ 0 := by
      intro h
      have h' := LinearMap.congr_fun h (fun k => if k = i then 1 else 0)
      simp [L, hij.symm] at h'
    have hker : LinearMap.ker L ≠ ⊤ := by
      intro h
      exact hL (LinearMap.ker_eq_top.mp h)
    have hs : {u : Fin N → ℝ | u i = u j} =
        (LinearMap.ker L : Set (Fin N → ℝ)) := by
      ext u
      simp [L, LinearMap.mem_ker, sub_eq_zero]
    rw [hs]
    exact Measure.addHaar_submodule volume (LinearMap.ker L) hker
  have huniform : ∀ᵐ u ∂iidSample uniform01 N,
      ∀ i j : Fin N, i ≠ j → u i ≠ u j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · have hne : ∀ᵐ u ∂(volume : Measure (Fin N → ℝ)), u i ≠ u j := by
        exact ae_iff.mpr (by simpa only [not_not] using hface i j hij)
      rw [iid_uniform_cube_law]
      exact (ae_restrict_of_ae hne).mono (fun u hu _ => hu)
  have htransport := cdf_transport_iid (N := N) μ hcont
  have hcoord : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin N, i ≠ j →
        ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1 ≠
          ProbabilityTheory.cdf (μ.map Prod.fst) (x j).1 := by
    rw [← htransport] at huniform
    exact ae_of_ae_map
      (by
        apply Measurable.aemeasurable
        apply measurable_pi_iff.mpr
        intro i
        exact hcont.measurable.comp (measurable_fst.comp (measurable_pi_apply i))
        : AEMeasurable
        (fun x : Fin N → ℝ × ℝ => fun i =>
          ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1)
        (Measure.pi (fun _ : Fin N => μ))) huniform
  filter_upwards [hcoord] with x hx
  let f : Fin N → ℝ := fun i => (x i).1
  let g : Fin N → ℝ := fun i => ProbabilityTheory.cdf (μ.map Prod.fst) (x i).1
  have hg : Function.Injective g := by
    intro i j h
    by_contra hij
    exact hx i j hij h
  have hmono : Monotone (g ∘ Tuple.sort f) :=
    (ProbabilityTheory.monotone_cdf (μ.map Prod.fst)).comp (Tuple.monotone_sort f)
  change Tuple.sort f = Tuple.sort g
  apply (Tuple.eq_sort_iff).2
  constructor
  · exact hmono
  · intro i j hij heq
    exact (hij.ne ((Tuple.sort f).injective (hg heq))).elim

/-- For a [marked observation law](hyp:μ) and an [almost-everywhere conditional
 mean version](hyp:hm), [that version has a measurable representative on the CDF
 coordinate](goal). -/
theorem conditionalMean_exists_measurable_version (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    ∃ g : ℝ → ℝ, Measurable g ∧
      (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1)) =ᵐ[μ]
        (fun p => g (ProbabilityTheory.cdf (μ.map Prod.fst) p.1)) := by
  let F : ℝ × ℝ → ℝ := fun p => ProbabilityTheory.cdf (μ.map Prod.fst) p.1
  let c : ℝ × ℝ → ℝ := μ[(fun p : ℝ × ℝ => p.2) |
    MeasurableSpace.comap F inferInstance]
  have hc : @StronglyMeasurable (ℝ × ℝ) ℝ _
      (MeasurableSpace.comap F inferInstance) c := stronglyMeasurable_condExp
  obtain ⟨g, hg, hgc⟩ := hc.exists_eq_measurable_comp
  refine ⟨g, hg.measurable, ?_⟩
  exact hm.trans (Filter.Eventually.of_forall fun p => by
    simpa only [Function.comp_apply] using congrFun hgc p)

/-- A conditional-mean version that factors measurably through a continuous
 CDF equals that measurable factor almost everywhere under the uniform law. -/
theorem conditionalMean_ae_eq_uniform_version (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    ∃ g : ℝ → ℝ, Measurable g ∧ m =ᵐ[uniform01] g := by
  obtain ⟨g, hg, hcomp⟩ := conditionalMean_exists_measurable_version μ m hm
  refine ⟨g, hg, ?_⟩
  let ν : Measure ℝ := μ.map Prod.fst
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hfst :
      (fun t => m (ProbabilityTheory.cdf ν t)) =ᵐ[ν]
        (fun t => g (ProbabilityTheory.cdf ν t)) := by
    exact ae_eq_of_comp_fst μ
      (fun t => m (ProbabilityTheory.cdf ν t))
      (fun t => g (ProbabilityTheory.cdf ν t)) hcomp
  exact ae_eq_of_comp_continuous_cdf ν hcont m g hfst

/-- A conditional mean of a mark in `[0,1]` stays in `[0,1]` almost surely
 under the original marked observation law. -/
theorem conditionalMean_comp_mem_Icc_ae (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    ∀ᵐ p ∂μ, m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1) ∈
      Set.Icc (0 : ℝ) 1 := by
  have hlo : ∀ᵐ p ∂μ, (0 : ℝ) ≤ p.2 := hmark.mono fun _ hp => hp.1
  have hhi : ∀ᵐ p ∂μ, p.2 ≤ (1 : ℝ) := hmark.mono fun _ hp => hp.2
  have hcondlo : ∀ᵐ p ∂μ,
      (0 : ℝ) ≤ μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance] p := condExp_nonneg hlo
  have hcondhi : ∀ᵐ p ∂μ,
      μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance] p ≤ (1 : ℝ) := condExp_le_nonneg_const (by norm_num) hhi
  filter_upwards [hm, hcondlo, hcondhi] with p hp hp0 hp1
  constructor
  · simpa only [hp] using hp0
  · simpa only [hp] using hp1

/-- For a [marked observation law](hyp:μ), [continuous sorting-coordinate CDF](hyp:hcont),
 and [conditional mean version](hyp:hm),
 [the version is almost-everywhere measurable under the unit-uniform law](goal). -/
theorem aemeasurable_conditionalMean_uniform (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    AEMeasurable m uniform01 := by
  obtain ⟨g, hg, hmg⟩ :=
    conditionalMean_ae_eq_uniform_version μ hcont m hm
  exact hg.aemeasurable.congr hmg.symm

/-- For a [marked observation law](hyp:μ), [continuous sorting-coordinate CDF](hyp:hcont),
 [marks in the unit interval almost surely](hyp:hmark), and a
 [conditional mean version](hyp:hm),
 [that version lies in the unit interval almost everywhere under the uniform law](goal). -/
theorem conditionalMean_mem_Icc_ae (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (m : ℝ → ℝ)
    (hm : (fun p : ℝ × ℝ => m (ProbabilityTheory.cdf (μ.map Prod.fst) p.1))
      =ᵐ[μ] μ[(fun p : ℝ × ℝ => p.2) |
        MeasurableSpace.comap
          (fun p : ℝ × ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) p.1)
          inferInstance]) :
    ∀ᵐ u ∂uniform01, m u ∈ Set.Icc (0 : ℝ) 1 := by
  let ν : Measure ℝ := μ.map Prod.fst
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let bad : ℝ → ℝ := fun u => if m u ∈ Set.Icc (0 : ℝ) 1 then 0 else 1
  have hcomp :
      (fun p : ℝ × ℝ => bad (ProbabilityTheory.cdf ν p.1)) =ᵐ[μ]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [conditionalMean_comp_mem_Icc_ae μ hmark m hm] with p hp
    change (if m (ProbabilityTheory.cdf ν p.1) ∈ Set.Icc (0 : ℝ) 1
      then (0 : ℝ) else 1) = 0
    exact if_pos hp
  have hfst :
      (fun t => bad (ProbabilityTheory.cdf ν t)) =ᵐ[ν]
        (fun _ => (0 : ℝ)) :=
    ae_eq_of_comp_fst μ (fun t => bad (ProbabilityTheory.cdf ν t))
      (fun _ => 0) hcomp
  have huni : bad =ᵐ[uniform01] (fun _ => (0 : ℝ)) :=
    ae_eq_of_comp_continuous_cdf ν hcont bad (fun _ => 0) hfst
  filter_upwards [huni] with u hu
  by_contra hnot
  have hbad : bad u = 1 := if_neg hnot
  rw [hbad] at hu
  norm_num at hu

/-- For a [positive sample size](hyp:hN), a [tagged coordinate](hyp:i), a
 [rank](hyp:j), and an [almost-everywhere measurable bounded test function](hyp:f,hf,hbound),
 [the iid unit-uniform expectation of the test function at the tagged coordinate, on the event
 that this coordinate has that (zero-based) rank `j` in the sample, equals the integral over
 the unit interval of the test function against the binomial weight
 `C(N−1, j) v^j (1−v)^(N−1−j)`](goal). -/
theorem uniform_tagged_rank_cell_integral {N : ℕ} (hN : 0 < N)
    (i j : Fin N) (f : ℝ → ℝ)
    (hf : AEMeasurable f uniform01)
    (hbound : ∀ᵐ u ∂uniform01, |f u| ≤ 1) :
    (∫ u, (if (Tuple.sort u).symm i = j then f (u i) else 0)
      ∂iidSample uniform01 N) =
      ∫ v in Set.Icc (0 : ℝ) 1,
        f v * ((Nat.choose (N - 1) j.val : ℝ) *
          v ^ j.val * (1 - v) ^ (N - 1 - j.val)) ∂volume := by
  classical
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  let g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hfg : f =ᵐ[uniform01] g := hf.ae_eq_mk
  have hgbound : ∀ᵐ v ∂uniform01, |g v| ≤ 1 := by
    filter_upwards [hbound, hfg] with v hv heq
    simpa only [← heq] using hv
  have hmain (g : ℝ → ℝ) (hg : Measurable g)
      (hgbound : ∀ᵐ v ∂uniform01, |g v| ≤ 1) :
      (∫ u, (if (Tuple.sort u).symm i = j then g (u i) else 0)
        ∂iidSample uniform01 N) =
        ∫ v in Set.Icc (0 : ℝ) 1,
          g v * ((Nat.choose (N - 1) j.val : ℝ) *
            v ^ j.val * (1 - v) ^ (N - 1 - j.val)) ∂volume := by
    cases N with
    | zero => omega
    | succ n =>
      let ν : Measure (Fin (n + 1) → ℝ) :=
        Measure.pi (fun _ => uniform01)
      let ρ : Measure (Fin n → ℝ) :=
        Measure.pi (fun _ => uniform01)
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) i
      let A (v : ℝ) : Set (Fin n → ℝ) :=
        {w | ((Finset.univ : Finset (Fin n)).filter
          (fun k => w k < v)).card = j.val}
      let C : Set (Fin (n + 1) → ℝ) :=
        {u | (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
          (fun k => u k < u i)).card = j.val}
      have hcount (v : ℝ) (u : Fin (n + 1) → ℝ) :
          (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
            (fun k => u k < v)).card =
          ((Finset.univ : Finset (Fin n)).filter
            (fun k => i.removeNth u k < v)).card := by
        have hindex : ((Finset.univ : Finset (Fin (n + 1))).erase i) =
            (Finset.univ : Finset (Fin n)).image i.succAbove := by
          ext k
          simp only [Finset.mem_erase, Finset.mem_univ, and_true,
            Finset.mem_image, Finset.mem_univ, true_and]
          rw [← Set.mem_range]
          simp [Fin.range_succAbove]
        rw [hindex, Finset.filter_image, Finset.card_image_of_injective]
        · rfl
        · exact Fin.succAbove_right_injective
      have hA (v : ℝ) : MeasurableSet (A v) := by
        dsimp [A]
        apply measurableSet_eq_fun
        · simp_rw [Finset.card_filter]
          apply Finset.measurable_sum
          intro k _
          apply Measurable.ite
          · exact measurableSet_lt (measurable_pi_apply k) measurable_const
          · exact measurable_const
          · exact measurable_const
        · exact measurable_const
      have hC : MeasurableSet C := by
        dsimp [C]
        apply measurableSet_eq_fun
        · simp_rw [Finset.card_filter]
          apply Finset.measurable_sum
          intro k _
          apply Measurable.ite
          · exact measurableSet_lt (measurable_pi_apply k)
              (measurable_pi_apply i)
          · exact measurable_const
          · exact measurable_const
        · exact measurable_const
      have hmass (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
          ρ (A v) =
            ENNReal.ofReal ((Nat.choose n j.val : ℝ) *
              v ^ j.val * (1 - v) ^ (n - j.val)) := by
        let B : Set (Fin (n + 1) → ℝ) :=
          {u | (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
            (fun k => u k < v)).card = j.val}
        have hB : B = e ⁻¹' (Set.univ ×ˢ A v) := by
          ext u
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
          change (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
              (fun k => u k < v)).card = j.val ↔
            ((Finset.univ : Finset (Fin n)).filter
              (fun k => i.removeNth u k < v)).card = j.val
          rw [hcount]
        have he := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => uniform01) i
        have hBmass : ρ (A v) = ν B := by
          rw [hB, he.measure_preimage
            ((MeasurableSet.univ.prod (hA v)).nullMeasurableSet)]
          rw [Measure.prod_prod]
          simp [ρ]
        simpa [ν, ρ, B] using
          hBmass.trans (uniform_other_lt_count_mass i j hv)
      let F : (Fin (n + 1) → ℝ) → ℝ :=
        fun u => if u ∈ C then g (u i) else 0
      have hFmeas : Measurable F := by
        apply Measurable.ite hC
        · exact hg.comp (measurable_pi_apply i)
        · exact measurable_const
      have hpi_bound : ∀ᵐ u ∂ν, |g (u i)| ≤ 1 := by
        have hmap : ν.map (fun u => u i) = uniform01 := by
          exact (measurePreserving_eval
            (fun _ : Fin (n + 1) => uniform01) i).map_eq
        exact ae_of_ae_map (μ := ν)
          (f := fun u : Fin (n + 1) → ℝ => u i)
          (p := fun v => |g v| ≤ 1) (measurable_pi_apply i).aemeasurable
          (by simpa [hmap] using hgbound)
      have hFint : Integrable F ν := by
        apply Integrable.of_bound hFmeas.aestronglyMeasurable 1
        filter_upwards [hpi_bound] with u hu
        by_cases hc : u ∈ C
        · simpa [F, hc, Real.norm_eq_abs] using hu
        · simp [F, hc]
      have hrank : (fun u : Fin (n + 1) → ℝ =>
          if (Tuple.sort u).symm i = j then g (u i) else 0) =ᵐ[ν] F := by
        filter_upwards [iid_uniform_coordinates_injective_ae (N := n + 1)]
          with u hu
        have hiff : (Tuple.sort u).symm i = j ↔ u ∈ C := by
          change (Tuple.sort u).symm i = j ↔
            (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
              (fun k => u k < u i)).card = j.val
          rw [← uniform_tagged_rank_eq_count u i hu]
          exact Fin.ext_iff
        simp only [F, hiff]
      have he := measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => uniform01) i
      have hcomp : (fun z => F (e.symm z)) ∘ e = F := by
        funext u
        simp
      have hsplit :
          (∫ u, F u ∂ν) =
            ∫ v, ∫ w : Fin n → ℝ, F (e.symm (v, w)) ∂ρ ∂uniform01 := by
        calc
          _ = ∫ z : ℝ × (Fin n → ℝ), F (e.symm z)
                ∂uniform01.prod ρ := by
                  have hh := he.integral_comp' (fun z => F (e.symm z))
                  change (∫ u, ((fun z => F (e.symm z)) ∘ e) u
                    ∂ν) = _ at hh
                  rw [hcomp] at hh
                  exact hh
          _ = _ := by
            apply integral_prod
            apply (he.integrable_comp_emb e.measurableEmbedding).mp
            change Integrable (((fun z => F (e.symm z)) ∘ e)) ν
            rw [hcomp]
            exact hFint
      have hinner (v : ℝ) :
          (∫ w : Fin n → ℝ, (if w ∈ A v then g v else 0) ∂ρ) =
            (ρ (A v)).toReal * g v := by
        simpa [Set.indicator, Measure.real, smul_eq_mul] using
          (integral_indicator_const (g v) (hA v) (μ := ρ))
      have hfiber (v : ℝ) (w : Fin n → ℝ) :
          F (e.symm (v, w)) = if w ∈ A v then g v else 0 := by
        have heval : (e.symm (v, w)) i = v := by simp [e]
        have hrem : i.removeNth (e.symm (v, w)) = w := by
          have hh := congrArg Prod.snd (e.apply_symm_apply (v, w))
          exact hh
        simp only [F]
        change (if (((Finset.univ : Finset (Fin (n + 1))).erase i).filter
              (fun k => (e.symm (v, w)) k < (e.symm (v, w)) i)).card = j.val
            then g ((e.symm (v, w)) i) else 0) =
          if ((Finset.univ : Finset (Fin n)).filter
              (fun k => w k < v)).card = j.val then g v else 0
        rw [heval, hcount v (e.symm (v, w)), hrem]
      have hkernel_nonneg (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
          0 ≤ (Nat.choose n j.val : ℝ) *
            v ^ j.val * (1 - v) ^ (n - j.val) := by
        have hv0 : 0 ≤ v := hv.1
        have hv1 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
        positivity
      calc
        (∫ u, (if (Tuple.sort u).symm i = j then g (u i) else 0)
          ∂iidSample uniform01 (n + 1)) = ∫ u, F u ∂ν := by
            exact integral_congr_ae hrank
        _ = ∫ v, ∫ w : Fin n → ℝ, F (e.symm (v, w)) ∂ρ ∂uniform01 :=
          hsplit
        _ = ∫ v, (ρ (A v)).toReal * g v ∂uniform01 := by
          congr 1
          funext v
          simp_rw [hfiber]
          exact hinner v
        _ = ∫ v, g v * ((Nat.choose n j.val : ℝ) *
              v ^ j.val * (1 - v) ^ (n - j.val)) ∂uniform01 := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
          rw [hmass v hv, ENNReal.toReal_ofReal (hkernel_nonneg v hv)]
          ring
        _ = _ := by
          simp only [uniform01, Nat.succ_sub_one]
  calc
    (∫ u, (if (Tuple.sort u).symm i = j then f (u i) else 0)
      ∂iidSample uniform01 N) =
        ∫ u, (if (Tuple.sort u).symm i = j then g (u i) else 0)
          ∂iidSample uniform01 N := by
            apply integral_congr_ae
            have hmap : (iidSample uniform01 N).map (fun u => u i) =
                uniform01 := (measurePreserving_eval
                  (fun _ : Fin N => uniform01) i).map_eq
            have hcomp : ∀ᵐ u ∂iidSample uniform01 N, f (u i) = g (u i) := by
              exact ae_of_ae_map (μ := iidSample uniform01 N)
                (f := fun u : Fin N → ℝ => u i)
                (p := fun v => f v = g v)
                (measurable_pi_apply i).aemeasurable
                (by rw [hmap]; exact hfg)
            filter_upwards [hcomp] with u hu
            split_ifs <;> simp [hu]
    _ = ∫ v in Set.Icc (0 : ℝ) 1,
          g v * ((Nat.choose (N - 1) j.val : ℝ) *
            v ^ j.val * (1 - v) ^ (N - 1 - j.val)) ∂volume :=
      hmain g hg hgbound
    _ = _ := by
      apply integral_congr_ae
      have hfg' : f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] g := by
        simpa only [uniform01] using hfg
      filter_upwards [hfg'] with v hv
      simp [hv]

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
