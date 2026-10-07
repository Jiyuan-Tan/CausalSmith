module
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Mathlib.Probability.Distributions.Binomial

/-!
# Ranks and binomial counts in an iid uniform tuple

These facts isolate the finite-product and tie-free steps used by the tagged
concomitant cell law. A tagged point's rank is the number of other observations
below it, and that count at a fixed threshold has a binomial law.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- For an iid unit-uniform tuple, its coordinates are pairwise distinct almost surely. -/
theorem iid_uniform_coordinates_injective_ae {N : ℕ} :
    ∀ᵐ u ∂iidSample uniform01 N, Function.Injective u := by
  rw [iid_uniform_cube_law]
  apply ae_restrict_of_ae
  have hpair (i j : Fin N) (hij : i ≠ j) :
      ∀ᵐ u : Fin N → ℝ ∂volume, u i ≠ u j := by
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
    apply (ae_iff).2
    simp only [not_not]
    change volume {u : Fin N → ℝ | u i = u j} = 0
    rw [hs]
    exact Measure.addHaar_submodule volume (LinearMap.ker L) hker
  have hall : ∀ᵐ u : Fin N → ℝ ∂volume,
      ∀ i j : Fin N, i ≠ j → u i ≠ u j := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact hpair i j hij
  filter_upwards [hall] with u hu i j hij
  by_contra hne
  exact hu i j hne hij

/-- For an iid unit-uniform tuple with [no ties](hyp:hu), [the zero-based rank of a
 tagged coordinate equals the number of other coordinates below it](goal). -/
theorem uniform_tagged_rank_eq_count {N : ℕ} (u : Fin N → ℝ) (i : Fin N)
    (hu : Function.Injective u) :
    ((Tuple.sort u).symm i).val =
      (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => u k < u i)).card := by
  let σ := Tuple.sort u
  have hs : StrictMono (u ∘ σ) :=
    (Tuple.monotone_sort u).strictMono_of_injective (hu.comp σ.injective)
  have hcard : ((Finset.univ : Finset (Fin N)).filter
      (fun k => k < σ.symm i)).card = (σ.symm i).val := by
    simpa using (Fin.card_filter_val_lt (n := N) (m := (σ.symm i).val))
  rw [← hcard]
  apply Finset.card_equiv σ
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, ne_eq, and_true]
  constructor
  · intro hk
    have : u (σ k) < u i := by
      simpa only [Function.comp_apply, σ.apply_symm_apply] using hs hk
    exact ⟨by intro h; subst h; exact (lt_irrefl _ this), this⟩
  · intro hk
    apply hs.lt_iff_lt.mp
    simpa only [Function.comp_apply, σ.apply_symm_apply] using hk.2

/-- For any finite set of coordinates in an iid unit-uniform tuple, the number
 strictly below a threshold in the unit interval has the binomial mass with
 one trial per selected coordinate. -/
theorem uniform_subset_lt_count_mass {N : ℕ} (S : Finset (Fin N))
    (r : ℕ) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    iidSample uniform01 N
      {u | (S.filter (fun k => u k < v)).card = r} =
      ENNReal.ofReal ((Nat.choose S.card r : ℝ) *
        v ^ r * (1 - v) ^ (S.card - r)) := by
  let p : unitInterval := ⟨v, hv⟩
  let f : Fin N → ℝ → Prop := fun k x => k ∈ S ∧ x < v
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  have hbase : Measure.map (fun x : ℝ => x < v) uniform01 =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
    apply Measure.ext_of_singleton
    intro b
    by_cases hb : b
    · have he : b = True := propext (iff_true_intro hb)
      rw [he]
      rw [show (Measure.map (fun x : ℝ => x < v) uniform01) {True} =
        uniform01 (Set.Iio v) by
          rw [Measure.map_apply (by fun_prop) (by simp)]
          congr 1
          ext x
          simp]
      simp only [Measure.add_apply, Measure.smul_apply]
      simp
      rw [uniform01, Measure.restrict_apply measurableSet_Iio]
      have hs : Set.Iio v ∩ Set.Icc 0 1 = Set.Ico 0 v := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
        exact ⟨fun h => ⟨h.2.1, h.1⟩,
          fun h => ⟨h.2, h.1, le_trans h.2.le hv.2⟩⟩
      rw [hs, Real.volume_Ico]
      simp only [sub_zero, ENNReal.ofReal, unitInterval.toNNReal]
      congr 1
      exact Subtype.ext (Real.coe_toNNReal v hv.1)
    · have he : b = False := propext (iff_false_intro hb)
      rw [he]
      rw [show (Measure.map (fun x : ℝ => x < v) uniform01) {False} =
        uniform01 (Set.Ici v) by
          rw [Measure.map_apply (by fun_prop) (by simp)]
          congr 1
          ext x
          simp]
      simp only [Measure.add_apply, Measure.smul_apply]
      simp
      rw [uniform01, Measure.restrict_apply measurableSet_Ici]
      have hs : Set.Ici v ∩ Set.Icc 0 1 = Set.Icc v 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩,
          fun h => ⟨h.1, le_trans hv.1 h.1, h.2⟩⟩
      rw [hs, Real.volume_Icc]
      simp only [ENNReal.ofReal, unitInterval.toNNReal]
      congr 1
      exact Subtype.ext (Real.coe_toNNReal (1 - v) (sub_nonneg.mpr hv.2))
  haveI (k : Fin N) : IsProbabilityMeasure (uniform01.map (f k)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcoord (k : Fin N) :
      uniform01.map (f k) =
        unitInterval.toNNReal p • Measure.dirac (k ∈ (S : Set (Fin N))) +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
    by_cases hk : k ∈ S
    · simpa [f, p, hk] using hbase
    · simp [f, hk, ← add_smul, unitInterval.toNNReal_add_toNNReal_symm]
  have hLaw : (iidSample uniform01 N).map
      (fun u => {k | k ∈ S ∧ u k < v}) =
      ProbabilityTheory.setBernoulli (S : Set (Fin N)) p := by
    calc
      (iidSample uniform01 N).map (fun u => {k | k ∈ S ∧ u k < v})
          = (Measure.pi fun k => uniform01.map (f k)).map (fun b => {k | b k}) := by
            rw [← Measure.pi_map_pi (fun k =>
              (show AEMeasurable (f k) uniform01 from by fun_prop))]
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = ProbabilityTheory.setBernoulli (S : Set (Fin N)) p := by
            simp_rw [hcoord]
            rw [ProbabilityTheory.setBernoulli_eq_map, Measure.infinitePi_eq_pi]
  calc
    iidSample uniform01 N {u | (S.filter (fun k => u k < v)).card = r}
        = ((iidSample uniform01 N).map
            (fun u => {k | k ∈ S ∧ u k < v})).map Set.ncard {r} := by
              rw [Measure.map_apply (by fun_prop) (by simp)]
              rw [Measure.map_apply (by fun_prop) (by measurability)]
              congr 1
              ext u
              have he : {k | k ∈ S ∧ u k < v} =
                  (S.filter (fun k => u k < v) : Set (Fin N)) := by
                ext k
                simp
              change (S.filter (fun k => u k < v)).card = r ↔
                ({k | k ∈ S ∧ u k < v} : Set (Fin N)).ncard = r
              rw [he, Set.ncard_coe_finset]
    _ = (ProbabilityTheory.setBernoulli (S : Set (Fin N)) p).map Set.ncard {r} := by
          rw [hLaw]
    _ = _ := by
          rw [ProbabilityTheory.map_ncard_setBernoulli_singleton
            (Set.toFinite (S : Set (Fin N)))]
          simp [p]

/-- Relabeling the coordinates of an iid unit-uniform tuple by a permutation
preserves its finite-product probability law. -/
theorem iid_uniform_relabel_law {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (iidSample uniform01 N).map (fun u i => u (σ i)) =
      iidSample uniform01 N := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  have hf : (fun u : Fin N → ℝ => fun i => u (σ i)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ.symm :
        (Fin N → ℝ) → (Fin N → ℝ)) := by
    funext u i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  simpa [iidSample] using
    Measure.pi_map_piCongrLeft σ.symm (fun _ : Fin N => uniform01)

/-- For an iid uniform tuple, two tagged coordinates have the same probability
of occupying any specified rank. -/
theorem uniform_tagged_rank_mass_eq_of_tag {N : ℕ}
    (i k j : Fin N) :
    iidSample uniform01 N {u | (Tuple.sort u).symm i = j} =
      iidSample uniform01 N {u | (Tuple.sort u).symm k = j} := by
  classical
  let μ := iidSample uniform01 N
  let σ : Equiv.Perm (Fin N) := Equiv.swap i k
  let R : (Fin N → ℝ) → Fin N → Prop :=
    fun u a => (Tuple.sort u).symm a = j
  have hmeas : NullMeasurableSet {u | R u i} μ := by
    let F : Set (Fin N → ℝ) :=
      {u | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun a => u a < u i)).card = j.val}
    have hF : MeasurableSet F := by
      dsimp [F]
      apply measurableSet_eq_fun
      · simp_rw [Finset.card_filter]
        apply Finset.measurable_sum
        intro a _
        apply Measurable.ite
        · exact measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply i)
        · exact measurable_const
        · exact measurable_const
      · exact measurable_const
    apply hF.nullMeasurableSet.congr
    filter_upwards [iid_uniform_coordinates_injective_ae (N := N)] with u hu
    apply propext
    change
      (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun a => u a < u i)).card = j.val ↔
      ((Tuple.sort u).symm i = j)
    rw [← uniform_tagged_rank_eq_count u i hu]
    exact Fin.ext_iff.symm
  have hsort (u : Fin N → ℝ) (hu : Function.Injective u) :
      (Tuple.sort (fun a => u (σ a))).symm i =
        (Tuple.sort u).symm (σ i) := by
    have hs (a : Fin N) :
        σ (Tuple.sort (fun a => u (σ a)) a) = Tuple.sort u a := by
      apply hu
      exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort
        (f := u) (σ := σ)) a
    apply (Tuple.sort u).injective
    calc
      (Tuple.sort u) ((Tuple.sort (fun a => u (σ a))).symm i) =
          σ (Tuple.sort (fun a => u (σ a))
            ((Tuple.sort (fun a => u (σ a))).symm i)) := (hs _).symm
      _ = σ i := by simp
      _ = (Tuple.sort u) ((Tuple.sort u).symm (σ i)) := by simp
  have hrelabel : Measurable (fun u : Fin N → ℝ => fun a => u (σ a)) := by
    fun_prop
  have hmeas' : NullMeasurableSet {u | R u i}
      (μ.map (fun u => fun a => u (σ a))) := by
    rw [iid_uniform_relabel_law σ]
    exact hmeas
  calc
    μ {u | R u i} = (μ.map (fun u => fun a => u (σ a))) {u | R u i} := by
      rw [iid_uniform_relabel_law σ]
    _ = μ {u | R (fun a => u (σ a)) i} := by
      rw [Measure.map_apply₀ hrelabel.aemeasurable hmeas']
      rfl
    _ = μ {u | R u k} := by
      apply measure_congr
      filter_upwards [iid_uniform_coordinates_injective_ae (N := N)] with u hu
      apply propext
      change (Tuple.sort (fun a => u (σ a))).symm i = j ↔
        (Tuple.sort u).symm k = j
      rw [hsort u hu]
      simp [σ]

/-- For one rank of an iid uniform tuple, the masses of the events
that each possible tag occupies that rank sum to one. -/
theorem sum_uniform_tagged_rank_mass {N : ℕ}
    (j : Fin N) :
    (∑ i : Fin N,
      iidSample uniform01 N {u | (Tuple.sort u).symm i = j}) = 1 := by
  classical
  let μ := iidSample uniform01 N
  let E : Fin N → Set (Fin N → ℝ) :=
    fun i => {u | (Tuple.sort u).symm i = j}
  have hmeas (i : Fin N) : NullMeasurableSet (E i) μ := by
    let F : Set (Fin N → ℝ) :=
      {u | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => u k < u i)).card = j.val}
    have hF : MeasurableSet F := by
      dsimp [F]
      apply measurableSet_eq_fun
      · simp_rw [Finset.card_filter]
        apply Finset.measurable_sum
        intro k _
        apply Measurable.ite
        · exact measurableSet_lt (measurable_pi_apply k) (measurable_pi_apply i)
        · exact measurable_const
        · exact measurable_const
      · exact measurable_const
    apply hF.nullMeasurableSet.congr
    filter_upwards [iid_uniform_coordinates_injective_ae (N := N)] with u hu
    apply propext
    change (
      (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => u k < u i)).card = j.val) ↔
      ((Tuple.sort u).symm i = j)
    rw [← uniform_tagged_rank_eq_count u i hu]
    exact Fin.ext_iff.symm
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) E) := by
    intro i k hik
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro u hi hk
    have hi' : (Tuple.sort u).symm i = j := hi
    have hk' : (Tuple.sort u).symm k = j := hk
    exact hik ((Tuple.sort u).symm.injective (hi'.trans hk'.symm))
  have hcover : (⋃ i, E i) = Set.univ := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨(Tuple.sort u) j, by simp [E]⟩
  haveI : IsProbabilityMeasure μ := by
    haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
    dsimp [μ, iidSample]
    infer_instance
  calc
    (∑ i : Fin N, μ (E i)) = ∑' i : Fin N, μ (E i) := (tsum_fintype _).symm
    _ = μ (⋃ i, E i) := (measure_iUnion₀ hdisj hmeas).symm
    _ = 1 := by rw [hcover]; exact measure_univ

/-- A [positive sample size](hyp:hN), [tagged coordinate](hyp:i), and [rank](hyp:j)
have [uniform rank mass under the iid unit-uniform law](goal): the probability that the
tagged observation occupies that position in the sorted sample is one over the sample size. -/
theorem uniform_tagged_rank_mass {N : ℕ} (hN : 0 < N)
    (i j : Fin N) :
    iidSample uniform01 N {u | (Tuple.sort u).symm i = j} =
      ENNReal.ofReal (1 / (N : ℝ)) := by
  let m := iidSample uniform01 N {u | (Tuple.sort u).symm i = j}
  have hsum : N • m = 1 := by
    calc
      N • m = ∑ _ : Fin N, m := (Fin.sum_const N m).symm
      _ = ∑ k : Fin N,
          iidSample uniform01 N {u | (Tuple.sort u).symm k = j} := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [m] using uniform_tagged_rank_mass_eq_of_tag i k j
      _ = 1 := sum_uniform_tagged_rank_mass j
  have hN0 : (N : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hNtop : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hm : (N : ENNReal) * m = 1 := by simpa [nsmul_eq_mul] using hsum
  have ht : (N : ENNReal) * ENNReal.ofReal (1 / (N : ℝ)) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN)]
    simpa [one_div] using ENNReal.mul_inv_cancel hN0 hNtop
  exact (ENNReal.mul_left_inj hN0 hNtop).mp (by
    simpa only [mul_comm] using hm.trans ht.symm)

/-- For a tagged coordinate of an iid unit-uniform tuple and a point [inside the unit interval](hyp:hv),
[the number of other coordinates below that point has the binomial mass with
`N-1` trials](goal). -/
theorem uniform_other_lt_count_mass {N : ℕ}
    (i j : Fin N) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    iidSample uniform01 N
      {u | (((Finset.univ : Finset (Fin N)).erase i).filter
        (fun k => u k < v)).card = j.val} =
      ENNReal.ofReal ((Nat.choose (N - 1) j.val : ℝ) *
        v ^ j.val * (1 - v) ^ (N - 1 - j.val)) := by
  have hcard : ((Finset.univ : Finset (Fin N)).erase i).card = N - 1 := by
    simp
  simpa [hcard] using
    (uniform_subset_lt_count_mass ((Finset.univ : Finset (Fin N)).erase i)
      j.val hv)

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
