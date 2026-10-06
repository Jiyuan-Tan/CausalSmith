module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.ComponentProduct
public import Causalean.Stat.RandomGraph
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lower/TreeCount

Two-channel point-CATE annotation frontier: Lower/TreeCount
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


variable {d n m : ℕ}

private lemma measurable_maxDist (d : ℕ) :
    Measurable (fun q : Cov d × Cov d => maxDist q.1 q.2) := by
  unfold maxDist
  exact (Continuous.finset_sup'_apply
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (d + 1))).Nonempty)
    (fun i _ => show Continuous (fun q : Cov d × Cov d =>
      if hi : i.val < d then |q.1 ⟨i.val, hi⟩ - q.2 ⟨i.val, hi⟩| else 0) by
      split_ifs <;> fun_prop)).measurable

private def recordCoordinateGraph (d n m : ℕ) (h delta : ℝ) :
    Causalean.Stat.RandomGraph.CoordinateGraph (fun _ : Fin (n + m) => Cov d) where
  edgeEvent _ _ := {q | q.1 ∈ locCube d h ∧ q.2 ∈ locCube d h ∧
    maxDist q.1 q.2 ≤ 2 * delta}
  measurable_edgeEvent _ _ :=
    ((isClosed_locCube d h).measurableSet.preimage measurable_fst).inter
      (((isClosed_locCube d h).measurableSet.preimage measurable_snd).inter
        (measurableSet_Iic.preimage (measurable_maxDist d)))
  symmetric _ _ z y := by
    simp only [Set.mem_ofPred_eq]
    rw [maxDist_comm z y]
    aesop

private lemma recordCoordinateGraph_graph (d n m : ℕ) (h delta : ℝ)
    (x : Fin (n + m) → Cov d) :
    (recordCoordinateGraph d n m h delta).graph x = recordGraph h delta x := by
  ext i j
  rfl

private def maxBox (d : ℕ) (delta : ℝ) (y : Cov d) : Set (Cov d) :=
  {z | ∀ k, z k ∈ Set.Icc (y k - 2 * delta) (y k + 2 * delta)}

private lemma measurableSet_maxBox (d : ℕ) (delta : ℝ) (y : Cov d) :
    MeasurableSet (maxBox d delta y) := by
  rw [show maxBox d delta y = ⋂ k : Fin d,
      (fun z : Cov d => z k) ⁻¹' Set.Icc (y k - 2 * delta) (y k + 2 * delta) by
    ext z
    simp [maxBox]]
  exact MeasurableSet.iInter fun k => measurableSet_Icc.preimage (by fun_prop)

private lemma maxDist_mem_maxBox {d : ℕ} {delta : ℝ} {z y : Cov d}
    (hdist : maxDist z y ≤ 2 * delta) : z ∈ maxBox d delta y := by
  intro k
  have hk : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (d + 1)).val < d := k.isLt
  have hcoord : |z k - y k| ≤ maxDist z y := by
    unfold maxDist
    simpa only [dif_pos hk] using Finset.le_sup'
      (fun i : Fin (d + 1) => if hi : i.val < d then
        |z ⟨i.val, hi⟩ - y ⟨i.val, hi⟩| else 0)
      (Finset.mem_univ (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (d + 1)))
  have habs : |z k - y k| ≤ 2 * delta := hcoord.trans hdist
  constructor <;> linarith [abs_le.mp habs |>.1, abs_le.mp habs |>.2]

private lemma volume_maxBox (d : ℕ) (delta : ℝ) (y : Cov d) (hd : 0 ≤ delta) :
    volume (maxBox d delta y) = ENNReal.ofReal ((4 * delta) ^ d) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    (measurableSet_maxBox d delta y).nullMeasurableSet]
  rw [show WithLp.toLp 2 ⁻¹' maxBox d delta y =
      Set.Icc (fun k : Fin d => y k - 2 * delta) (fun k => y k + 2 * delta) by
    ext z
    simp only [Set.mem_preimage, maxBox, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
    aesop]
  rw [Real.volume_Icc_pi]
  calc
    (∏ k : Fin d, ENNReal.ofReal (y k + 2 * delta - (y k - 2 * delta))) =
        ∏ _k : Fin d, ENNReal.ofReal (4 * delta) := by
      apply Finset.prod_congr rfl
      intro k hk
      congr 1
      ring
    _ = ENNReal.ofReal ((4 * delta) ^ d) := by
      rw [Fin.prod_const]
      exact (ENNReal.ofReal_pow (mul_nonneg (by norm_num) hd) d).symm

private lemma uniformLaw_edge_section_le (d n m : ℕ) (h delta : ℝ) (hd : 0 < delta)
    (i j : Fin (n + m)) (y : Cov d) :
    uniformLaw d {z | (z, y) ∈ (recordCoordinateGraph d n m h delta).edgeEvent i j} ≤
      ENNReal.ofReal ((4 * delta) ^ d) := by
  calc
    uniformLaw d {z | (z, y) ∈ (recordCoordinateGraph d n m h delta).edgeEvent i j} ≤
        volume {z | (z, y) ∈ (recordCoordinateGraph d n m h delta).edgeEvent i j} := by
      unfold uniformLaw
      exact Measure.le_iff'.mp (Measure.restrict_le_self (μ := volume) (s := cube d)) _
    _ ≤ volume (maxBox d delta y) := measure_mono (by
      intro z hz
      exact maxDist_mem_maxBox hz.2.2)
    _ = ENNReal.ofReal ((4 * delta) ^ d) := volume_maxBox d delta y hd.le

private lemma componentVertices_eq_support (h delta : ℝ) (x : Fin (n + m) → Cov d)
    (c : (recordGraph h delta x).ConnectedComponent) :
    componentVertices h delta x c = c.supp.toFinset := by
  ext i
  simp [componentVertices, SimpleGraph.ConnectedComponent.mem_supp_iff]

private lemma component_vertex_mem_locCube (h delta : ℝ) (x : Fin (n + m) → Cov d)
    (c : (recordGraph h delta x).ConnectedComponent) (i : Fin (n + m))
    (hi : i ∈ componentVertices h delta x c)
    (hcard : 2 ≤ (componentVertices h delta x c).card) : x i ∈ locCube d h := by
  have htwo : 1 < (componentVertices h delta x c).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  let j := if a = i then b else a
  have hj : j ∈ componentVertices h delta x c := by
    dsimp [j]
    split_ifs <;> assumption
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with hai
    · intro hbi
      exact hab (hai.trans hbi.symm)
    · exact ‹a ≠ i›
  have heq : (recordGraph h delta x).connectedComponentMk i =
      (recordGraph h delta x).connectedComponentMk j := by
    simpa [componentVertices] using (Finset.mem_filter.mp hi).2.trans
      (Finset.mem_filter.mp hj).2.symm
  have hreach : (recordGraph h delta x).Reachable i j := by
    simpa only [SimpleGraph.ConnectedComponent.eq] using heq
  obtain ⟨w⟩ := hreach
  have hfirst : ∀ {a b : Fin (n + m)}, (recordGraph h delta x).Walk a b →
      a ≠ b → x a ∈ locCube d h := by
    intro a b walk hab
    cases walk with
    | nil => exact False.elim (hab rfl)
    | cons hadj walk => exact hadj.2.1
  exact hfirst w hji.symm

private lemma labeledComponentCount_eq_record_count (d n m : ℕ) (h delta : ℝ)
    (p : ℕ) (hp : 2 ≤ p) (x : Fin (n + m) → Cov d) :
    Causalean.Stat.RandomGraph.labeledComponentCount
        (recordCoordinateGraph d n m h delta)
        (Finset.univ.filter fun i : Fin (n + m) => i.val < n)
        (fun _ => locCube d h) p x =
      ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
        (componentVertices h delta x c).card = p ∧
        ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ) := by
  classical
  let comps := Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
    (componentVertices h delta x c).card = p ∧
      ∃ i ∈ componentVertices h delta x c, i.val < n)
  let sets := ((Finset.univ : Finset (Fin (n + m))).powersetCard p).filter
    (fun S => x ∈ Causalean.Stat.RandomGraph.componentEvent
      (recordCoordinateGraph d n m h delta)
      (Finset.univ.filter fun i : Fin (n + m) => i.val < n)
      (fun _ => locCube d h) S)
  have hcards : comps.card = sets.card := by
    apply Finset.card_bij (fun c _ => componentVertices h delta x c)
    · intro c hc
      have hc' := Finset.mem_filter.mp hc
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc'.2.1⟩, ?_⟩
      obtain ⟨i, hi, hin⟩ := hc'.2.2
      refine ⟨?_, i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩, hi, ?_⟩
      · rw [recordCoordinateGraph_graph,
          Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent]
        exact ⟨c, by simp [componentVertices_eq_support]⟩
      · exact component_vertex_mem_locCube h delta x c i hi (hc'.2.1 ▸ hp)
    · intro c hc c' hc' heq
      apply SimpleGraph.ConnectedComponent.supp_injective
      simpa only [componentVertices_eq_support, Set.toFinset_inj] using heq
    · intro S hS
      have hS' := Finset.mem_filter.mp hS
      obtain ⟨hcomp, i, hiR, hiS, hiloc⟩ := hS'.2
      rw [recordCoordinateGraph_graph] at hcomp
      obtain ⟨c, hc⟩ :=
        (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent _ _).mp hcomp
      refine ⟨c, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, i, ?_, (Finset.mem_filter.mp hiR).2⟩
        · simpa [componentVertices_eq_support, hc] using
            (Finset.mem_powersetCard.mp hS'.1).2
        · simpa [componentVertices_eq_support, hc] using hiS
      · simp [componentVertices_eq_support, hc]
  unfold Causalean.Stat.RandomGraph.labeledComponentCount
  rw [← Finset.sum_filter]
  change (∑ _S ∈ sets, (1 : ℝ)) = (comps.card : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hcards.symm
/-- The informative-component count is integrable under the finite uniform covariate experiment.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the labeled record count integrable conclusion](goal) holds. -/
lemma labeled_record_count_integrable (d n m : ℕ) (h delta : ℝ) (p : ℕ) (hp : 2 ≤ p) :
    Integrable (fun x : Fin (n+m) → Cov d =>
      ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
        (componentVertices h delta x c).card = p ∧
        ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ))
      (Measure.pi (fun _ : Fin (n+m) => uniformLaw d)) := by
  letI := uniformLaw_probability d
  simp_rw [← labeledComponentCount_eq_record_count d n m h delta p hp]
  exact Causalean.Stat.RandomGraph.integrable_labeledComponentCount _ _ _ _ _
    (fun _ => (isClosed_locCube d h).measurableSet)

/-- The uniform design mass of the localization cube is its side length to the
ambient dimension.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the uniform law loc cube real conclusion](goal) holds. -/
lemma uniformLaw_locCube_real (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 2) :
    (uniformLaw d).real (locCube d h) = h ^ d := by
  have hsub : locCube d h ⊆ cube d := by
    intro x hx i
    exact ⟨by linarith [hx i |>.1], by linarith [hx i |>.2]⟩
  rw [measureReal_def, uniformLaw, Measure.restrict_apply]
  · rw [inter_eq_left.2 hsub]
    rw [← (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
      (isClosed_locCube d h).measurableSet.nullMeasurableSet]
    rw [show WithLp.toLp 2 ⁻¹' locCube d h =
        Set.Icc (fun _ : Fin d => 1 / 2 - h / 2)
          (fun _ : Fin d => 1 / 2 + h / 2) by
      ext x
      simp only [Set.mem_preimage, locCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
      constructor
      · intro hx
        exact ⟨fun i => by linarith [(hx i).1], fun i => (hx i).2⟩
      · rintro ⟨hxl, hxu⟩ i
        exact ⟨by linarith [hxl i], hxu i⟩]
    change (volume (Set.Icc (fun _ : Fin d => 1 / 2 - h / 2)
        (fun _ : Fin d => 1 / 2 + h / 2))).toReal = h ^ d
    rw [Real.volume_Icc_pi_toReal]
    · simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ring
    · intro i
      linarith
  · exact isClosed_locCube d h |>.measurableSet

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the labeled root tree count conclusion](goal) holds. -/
lemma labeled_root_tree_count (d n m : ℕ) (h delta : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hd : 0 < delta) (hdh : delta ≤ h) (p : ℕ) (hp : 2 ≤ p) :
    (∫ x : Fin (n+m) → Cov d,
      ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
        (componentVertices h delta x c).card = p ∧
        ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ)
      ∂Measure.pi (fun _ : Fin (n+m) => uniformLaw d)) ≤
      (n:ℝ)*h^d*(Nat.choose (n+m-1) (p-1):ℝ)*(p:ℝ)^(p-1)*((4*delta)^d)^(p-1) := by
  let _ := uniformLaw_probability d
  let M := recordCoordinateGraph d n m h delta
  let R := Finset.univ.filter fun i : Fin (n + m) => i.val < n
  have hrootMass : ∀ r ∈ R,
      uniformLaw d (locCube d h) ≤ ENNReal.ofReal (h ^ d) := by
    intro r hr
    have htop : uniformLaw d (locCube d h) ≠ ∞ := measure_ne_top _ _
    calc
      uniformLaw d (locCube d h) =
          ENNReal.ofReal ((uniformLaw d).real (locCube d h)) := by
        rw [measureReal_def, ENNReal.ofReal_toReal htop]
      _ ≤ ENNReal.ofReal (h ^ d) := by
        rw [uniformLaw_locCube_real d h hh hh']
  have hbound := Causalean.Stat.RandomGraph.expected_labeled_component_count_le
    (fun _ : Fin (n + m) => uniformLaw d) M R (fun _ => locCube d h)
    p hp (h ^ d) ((4 * delta) ^ d)
    (pow_nonneg hh.le d) (pow_nonneg (mul_nonneg (by norm_num) hd.le) d)
    (fun _ => (isClosed_locCube d h).measurableSet) hrootMass
    (fun i j hij y => uniformLaw_edge_section_le d n m h delta hd i j y)
  dsimp [M, R] at hbound
  calc
    _ = ∫ x, Causalean.Stat.RandomGraph.labeledComponentCount
        (recordCoordinateGraph d n m h delta)
        (Finset.univ.filter fun i : Fin (n + m) => i.val < n)
        (fun _ => locCube d h) p x
        ∂Measure.pi (fun _ : Fin (n + m) => uniformLaw d) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (labeledComponentCount_eq_record_count d n m h delta p hp x).symm
    _ ≤ ((Finset.univ.filter fun i : Fin (n + m) => i.val < n).card : ℝ) *
        (Nat.choose (Fintype.card (Fin (n + m)) - 1) (p - 1) : ℝ) *
        (p : ℝ) ^ (p - 1) * h ^ d * ((4 * delta) ^ d) ^ (p - 1) := hbound
    _ = (n:ℝ)*h^d*(Nat.choose (n+m-1) (p-1):ℝ)*(p:ℝ)^(p-1)*
        ((4*delta)^d)^(p-1) := by
      rw [show (Finset.univ.filter fun i : Fin (n + m) => i.val < n).card = n by
        rw [Fin.card_filter_val_lt, min_eq_right (by omega : n ≤ n + m)], Fintype.card_fin]
      ring
/-- The exponential series bounds the rooted-tree factorial ratio.  Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the factorial tree bound conclusion](goal) holds. -/
lemma factorial_tree_bound (p : ℕ) (hp : 2 ≤ p) :
    (p:ℝ)^(p-1)/(Nat.factorial (p-1):ℝ) ≤ Real.exp (p:ℝ) := by
  exact Real.pow_div_factorial_le_exp (p : ℝ) (Nat.cast_nonneg p) (p-1)
/-- [the tree series summable conclusion](goal) holds. -/
lemma tree_series_summable : Summable (fun p : ℕ => ((p+2:ℕ):ℝ)^4*(1/2:ℝ)^p) := by
  have hs : Summable (fun p : ℕ => (p:ℝ)^4*(1/2:ℝ)^p) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by norm_num)
  have ht : Summable (fun p : ℕ => ((p+2:ℕ):ℝ)^4*(1/2:ℝ)^(p+2)) :=
    (summable_nat_add_iff 2).2 hs
  convert ht.mul_left 4 using 1 <;> try rfl
  ext p
  rw [pow_add]
  ring


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
