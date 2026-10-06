module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Projection

/-!
# Helpers/LocalPolynomial/Taylor

Two-channel point-CATE annotation frontier: Helpers/LocalPolynomial/Taylor
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- The zero multi-index evaluates the zeroth within-cube derivative.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input x](hyp:x), [the coordinate partial zero index conclusion](goal) holds. -/
lemma coordinatePartial_zero_index (d : ℕ) (f : Cov d → ℝ) (x : Cov d) :
    coordinatePartial f (fun _ => 0) x = f x := by
  have he (k : ℕ) (hk : k = 0) (v : Fin k → Cov d) :
      iteratedFDerivWithin ℝ k f (cube d) x v = f x := by
    subst k
    simp
  exact he _ (by simp [multiOrder]) _

/-- The centre belongs to the design cube in every dimension.  Given [the specified input d](hyp:d), [the x0 mem cube conclusion](goal) holds. -/
lemma x0_mem_cube (d : ℕ) : x0 d ∈ cube d := by
  intro i
  norm_num [x0]

/-- The canonical contrast agrees with its admissible raw version on the cube.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the tau eq canonical contrast conclusion](goal) holds. -/
lemma tau_eq_canonicalContrast {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (x : Cov d) (hx : x ∈ cube d) :
    tau P hP x = rawContrast (canonicalLaw P hP) x := by
  simp [tau, designatedTreated, designatedControl, hx, rawContrast]

/-- A first-order Hölder norm bounds the contrast's Lipschitz modulus on the cube.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hL](hyp:hL), [the specified input x](hyp:x), [the specified input y](hyp:y), [the specified input hx](hyp:hx), [the specified input hy](hyp:hy), [the tau lipschitz gamma one conclusion](goal) holds. -/
lemma tau_lipschitz_gamma_one {d : ℕ} {alpha beta L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta 1 L eps P) (hL : 0 ≤ L)
    (x y : Cov d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |tau P hP x-tau P hP y| ≤ L*dist x y := by
  have hh := (holderNorm_le_iff (rawContrast (canonicalLaw P hP)) 1 L hL).mp
    (canonicalLaw_spec P hP).2.2.2.2.2.2.1
  by_cases he : x = y
  · subst y
    simp
  · have hm := hh.2.2 (fun _ => 0) (by simp [multiOrder]) x hx y hy he
    simpa [coordinatePartial_zero_index, tau_eq_canonicalContrast P hP x hx,
      tau_eq_canonicalContrast P hP y hy] using hm

/-- A localization window has radius at most its side times the square root of dimension.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the loc cube distance center bound conclusion](goal) holds. -/
lemma locCube_distance_center_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) :
    dist x (x0 d) ≤ Real.sqrt (d:ℝ)*h := by
  have hs : (∑ i : Fin d, dist (x i) (x0 d i)^2) ≤ (d:ℝ)*h^2 := by
    calc
      _ ≤ ∑ _i : Fin d, h^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hx i
        have hb : |x i-1/2| ≤ h := by
          rw [abs_le]
          constructor <;> linarith [hi.1, hi.2]
        simp only [x0, WithLp.ofLp_toLp, Real.dist_eq]
        nlinarith [abs_nonneg (x i-1/2), sq_abs (x i-1/2)]
      _ = _ := by simp
  rw [EuclideanSpace.dist_eq]
  calc
    _ ≤ Real.sqrt ((d:ℝ)*h^2) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hh.le]

/-- The only multi-index of total order zero is the zero index.  Given [the specified input d](hyp:d), [the poly idx order zero iff conclusion](goal) holds. -/
lemma polyIdx_order_zero_iff {d : ℕ} (κ : PolyIdx d) :
    multiOrder κ.1 ≤ 0 ↔ κ = ⟨fun _ => 0, by simp⟩ := by
  constructor
  · intro hk
    apply Subtype.ext
    funext i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (κ.1 j))
      (Finset.mem_univ i)
    change κ.1 i = 0
    unfold multiOrder at hk
    omega
  · rintro rfl
    simp [multiOrder]

/-- The degree-zero Taylor polynomial is the function's value at the centre.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input x](hyp:x), [the taylor poly zero degree conclusion](goal) holds. -/
lemma taylorPoly_zero_degree {d : ℕ} (f : Cov d → ℝ) (x : Cov d) :
    taylorPoly f 0 x = f (x0 d) := by
  classical
  let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
  have hfilter : Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ 0) = {z} := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact polyIdx_order_zero_iff κ
  rw [taylorPoly, hfilter, Finset.sum_singleton]
  simp [z, coordinatePartial_zero_index]

/-- A single constant-basis coefficient represents a constant polynomial.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input c](hyp:c), [the specified input x](hyp:x), [the pv constant coefficient conclusion](goal) holds. -/
lemma pv_constant_coefficient {d : ℕ} (h c : ℝ) (x : Cov d) :
    pv h (Pi.single (⟨fun _ => 0, by simp⟩ : PolyIdx d) c) x = c := by
  simp [pv, Pi.single_apply, coarseBasis, legendre]

private def coordPrefix {d : ℕ} (κ : Fin d → ℕ) (i : Fin d) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => j < i), κ j

private lemma bucket_exists_unique {d : ℕ} (κ : Fin d → ℕ)
    (r : ℕ) (hr : r < ∑ i, κ i) :
    ∃! i : Fin d, coordPrefix κ i ≤ r ∧ r < coordPrefix κ i + κ i := by
  induction d generalizing r with
  | zero => simp at hr
  | succ d ih =>
      rw [Fin.sum_univ_succ] at hr
      by_cases h0 : r < κ 0
      · refine ⟨0, ?_, ?_⟩
        · simpa [coordPrefix] using h0
        · intro i hi
          by_contra hne
          have hipos : 0 < i := Fin.pos_iff_ne_zero.mpr hne
          have hle : κ 0 ≤ coordPrefix κ i := by
            unfold coordPrefix
            apply Finset.single_le_sum (fun j _ => Nat.zero_le (κ j))
            simp [hipos]
          apply hne
          apply Fin.ext
          omega
      · have hr' : r - κ 0 < ∑ i : Fin d, κ i.succ := by omega
        obtain ⟨i, hi, hui⟩ := ih (fun j => κ j.succ) (r - κ 0) hr'
        refine ⟨i.succ, ?_, ?_⟩
        · have hp : coordPrefix κ i.succ = κ 0 + coordPrefix (fun j => κ j.succ) i := by
            simp [coordPrefix, Finset.sum_filter, Fin.sum_univ_succ]
          change coordPrefix κ i.succ ≤ r ∧ r < coordPrefix κ i.succ + κ i.succ
          rw [hp]
          omega
        · intro j hj
          have hj0 : j ≠ 0 := by
            intro he
            subst j
            simp [coordPrefix] at hj
            omega
          obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          congr 1
          apply hui
          have hp : coordPrefix κ j.succ = κ 0 + coordPrefix (fun q => κ q.succ) j := by
            simp [coordPrefix, Finset.sum_filter, Fin.sum_univ_succ]
          rw [hp] at hj
          omega

private noncomputable def paperWord {d : ℕ} (κ : Fin d → ℕ) :
    Fin (multiOrder κ) → Fin d := fun r =>
  Classical.choose (bucket_exists_unique κ r r.isLt)

private lemma paperWord_spec {d : ℕ} (κ : Fin d → ℕ) (r : Fin (multiOrder κ)) :
    coordPrefix κ (paperWord κ r) ≤ r ∧
      r < coordPrefix κ (paperWord κ r) + κ (paperWord κ r) :=
  (Classical.choose_spec (bucket_exists_unique κ r r.isLt)).1

private lemma coordinateDirections_eq_paperWord {d : ℕ} (κ : Fin d → ℕ) :
    coordinateDirections κ = fun r => EuclideanSpace.single (paperWord κ r) 1 := by
  funext r
  unfold coordinateDirections
  rw [Finset.sum_eq_single (paperWord κ r)]
  · rw [if_pos]
    exact paperWord_spec κ r
  · intro b _ hb
    have hu := (Classical.choose_spec (bucket_exists_unique κ r r.isLt)).2 b
    simp only [coordPrefix] at hu
    split_ifs with h
    · exact (hb (hu h)).elim
    · rfl
  · simp

private lemma coordPrefix_add_le_order {d : ℕ} (κ : Fin d → ℕ) (i : Fin d) :
    coordPrefix κ i + κ i ≤ multiOrder κ := by
  have hi : i ∉ Finset.univ.filter (fun j => j < i) := by simp
  rw [coordPrefix, multiOrder, add_comm, ← Finset.sum_insert hi]
  apply Finset.sum_le_sum_of_subset
  intro j _
  simp

private lemma paperWord_count {d : ℕ} (κ : Fin d → ℕ) :
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordCount (paperWord κ) = κ := by
  funext i
  let A := {r : Fin (multiOrder κ) // paperWord κ r = i}
  let e : A ≃ Fin (κ i) :=
    { toFun := fun r => ⟨r.1.val - coordPrefix κ i, by
          have hs := paperWord_spec κ r.1
          rw [r.2] at hs
          omega⟩
      invFun := fun q =>
        ⟨⟨coordPrefix κ i + q.val, by
            exact (Nat.lt_of_lt_of_le (Nat.add_lt_add_left q.isLt _)
              (coordPrefix_add_le_order κ i))⟩,
          by
            change Classical.choose _ = i
            symm
            apply (Classical.choose_spec
              (bucket_exists_unique κ (coordPrefix κ i + q.val)
                (Nat.lt_of_lt_of_le (Nat.add_lt_add_left q.isLt _)
                  (coordPrefix_add_le_order κ i)))).2
            omega⟩
      left_inv := fun r => by
        apply Subtype.ext
        apply Fin.ext
        change coordPrefix κ i + (r.1.val - coordPrefix κ i) = r.1.val
        have hs := paperWord_spec κ r.1
        rw [r.2] at hs
        omega
      right_inv := fun q => by
        apply Fin.ext
        change coordPrefix κ i + q.val - coordPrefix κ i = q.val
        omega }
  change (Finset.univ.filter fun r => paperWord κ r = i).card = κ i
  calc
    _ = Fintype.card A := by
      exact (Fintype.subtype_card _ (by simp)).symm
    _ = Fintype.card (Fin (κ i)) := Fintype.card_congr e
    _ = κ i := Fintype.card_fin _

private lemma coordinatePartial_eq_sorted {d m : ℕ} (f : Cov d → ℝ)
    (hf : ContDiffOn ℝ m f (cube d)) (κ : Fin d → ℕ) (hκ : multiOrder κ ≤ m)
    (x : Cov d) (hx : x ∈ cube d) :
    coordinatePartial f κ x =
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
        (cube d) f κ x := by
  unfold coordinatePartial
  rw [coordinateDirections_eq_paperWord]
  change Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.wordPartialWithin
      (cube d) f (paperWord κ) x = _
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
  apply Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.wordPartialWithin_eq_of_count
    (cube d) f x
  · intro σ v
    exact Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.euclidean_within_jet_perm
      (uniqueDiffOn_cube d) (hf.of_le (by exact_mod_cast hκ)) hx
      (cube_subset_closure_interior d hx) σ v
  · rw [paperWord_count]
    have hs :=
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.sortedWord_count κ
    simpa only [Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder,
      multiOrder] using hs.symm

private abbrev GenericIndex (d m : ℕ) :=
  Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.MultiIndex d m

private def genericIndexEquiv {d m : ℕ} (hm : m ≤ 2) :
    GenericIndex d m ≃ {κ : PolyIdx d // multiOrder κ.1 ≤ m} :=
  { toFun := fun κ => ⟨⟨κ.1, by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using
            κ.2.trans hm⟩, by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2⟩
    invFun := fun κ => ⟨κ.1.1, by
      simpa only [multiOrder,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2⟩
    left_inv := fun κ => by apply Subtype.ext; rfl
    right_inv := fun κ => by apply Subtype.ext; apply Subtype.ext; rfl }

private def extendCoefficients {d m : ℕ} (hm : m ≤ 2) (θ : GenericIndex d m → ℝ) :
    PolyIdx d → ℝ := fun κ => if hκ : multiOrder κ.1 ≤ m then
      θ ((genericIndexEquiv (d := d) (m := m) hm).symm ⟨κ, hκ⟩) else 0

private lemma coarseBasis_eq_scaled {d m : ℕ} (hm : m ≤ 2) (h : ℝ)
    (κ : GenericIndex d m) (x : Cov d) :
    coarseBasis h x (genericIndexEquiv hm κ).1 =
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.scaledTensorLegendre
        (x0 d) h κ x := by
  unfold coarseBasis
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.scaledTensorLegendre
  apply Finset.prod_congr rfl
  intro i _
  simp only [genericIndexEquiv, x0, WithLp.ofLp_toLp]
  have hi := Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinate_le_order κ.1 i
  have hki : κ.1 i ≤ 2 := hi.trans (κ.2.trans hm)
  interval_cases κ.1 i <;>
    simp [legendre,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.legendreEntry]

private lemma pv_extendCoefficients {d m : ℕ} (hm : m ≤ 2) (h : ℝ)
    (θ : GenericIndex d m → ℝ) (x : Cov d) :
    pv h (extendCoefficients hm θ) x =
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.legendrePolynomial
        (x0 d) h θ x := by
  unfold pv
  rw [show (∑ κ, coarseBasis h x κ * extendCoefficients hm θ κ) =
      ∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m),
        coarseBasis h x κ * extendCoefficients hm θ κ by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro κ _ hκ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hκ
    simp [extendCoefficients, hκ]]
  have hsub :
      (∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m),
        coarseBasis h x κ * extendCoefficients hm θ κ) =
      ∑ κ : {κ : PolyIdx d // multiOrder κ.1 ≤ m},
        coarseBasis h x κ.1 * θ ((genericIndexEquiv hm).symm κ) := by
    rw [Finset.sum_subtype (p := fun κ : PolyIdx d => multiOrder κ.1 ≤ m)
      (Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m))
      (by intro κ; simp)]
    apply Finset.sum_congr rfl
    intro κ _
    simp [extendCoefficients, κ.2]
  rw [hsub, ← (genericIndexEquiv hm).sum_comp]
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.legendrePolynomial
  apply Finset.sum_congr rfl
  intro κ _
  simp only [Equiv.symm_apply_apply]
  rw [coarseBasis_eq_scaled]

private lemma sum_sq_extendCoefficients {d m : ℕ} (hm : m ≤ 2)
    (θ : GenericIndex d m → ℝ) :
    (∑ κ, (extendCoefficients hm θ κ) ^ 2) = ∑ κ, θ κ ^ 2 := by
  rw [show (∑ κ, (extendCoefficients hm θ κ) ^ 2) =
      ∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m),
        (extendCoefficients hm θ κ) ^ 2 by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro κ _ hκ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hκ
    simp [extendCoefficients, hκ]]
  have hsub :
      (∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m),
        (extendCoefficients hm θ κ) ^ 2) =
      ∑ κ : {κ : PolyIdx d // multiOrder κ.1 ≤ m},
        (θ ((genericIndexEquiv hm).symm κ)) ^ 2 := by
    rw [Finset.sum_subtype (p := fun κ : PolyIdx d => multiOrder κ.1 ≤ m)
      (Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m))
      (by intro κ; simp)]
    apply Finset.sum_congr rfl
    intro κ _
    simp [extendCoefficients, κ.2]
  rw [hsub, ← (genericIndexEquiv hm).sum_comp]
  simp

private lemma taylorPoly_eq_multiindexTaylor {d m : ℕ} (hm : m ≤ 2)
    (f : Cov d → ℝ) (hf : ContDiffOn ℝ m f (cube d)) (x : Cov d) :
    taylorPoly f m x =
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiindexTaylor
        (cube d) f m (x0 d) x := by
  unfold taylorPoly
  have hsub :
      (∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m),
        coordinatePartial f κ.1 (x0 d) /
            (∏ i, (Nat.factorial (κ.1 i) : ℝ)) *
          ∏ i, (x i - 1 / 2) ^ κ.1 i) =
      ∑ κ : {κ : PolyIdx d // multiOrder κ.1 ≤ m},
        coordinatePartial f κ.1.1 (x0 d) /
            (∏ i, (Nat.factorial (κ.1.1 i) : ℝ)) *
          ∏ i, (x i - 1 / 2) ^ κ.1.1 i := by
    rw [Finset.sum_subtype (p := fun κ : PolyIdx d => multiOrder κ.1 ≤ m)
      (Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ m))
      (by intro κ; simp)]
  rw [hsub, ← (genericIndexEquiv hm).sum_comp]
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiindexTaylor
  apply Finset.sum_congr rfl
  intro κ _
  simp only [genericIndexEquiv, Equiv.coe_fn_mk]
  rw [coordinatePartial_eq_sorted f hf κ.1 (by
    simpa only [multiOrder,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2)
    (x0 d) (x0_mem_cube d)]
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.taylorCoefficient
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiFactorial
  unfold Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredMonomial
  simp only [x0, WithLp.ofLp_toLp]
  norm_cast

private lemma coordinatePartial_congr {d : ℕ} {f g : Cov d → ℝ}
    (hfg : Set.EqOn f g (cube d)) (κ : Fin d → ℕ) (x : Cov d)
    (hx : x ∈ cube d) : coordinatePartial f κ x = coordinatePartial g κ x := by
  unfold coordinatePartial
  rw [iteratedFDerivWithin_congr hfg hx]

/-- At smoothness one, the prescribed Taylor construction is the constant centre value.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the taylor coefficient bounds gamma one conclusion](goal) holds. -/
lemma taylor_coefficient_bounds_gamma_one (d : ℕ) (alpha beta L eps : ℝ)
    (hdom : PublicDomain d alpha beta 1 L eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta 1 L eps P),
      ∀ h, 0 < h → h ≤ 1/2 → ∃ theta : PolyIdx d → ℝ,
        (∀ x ∈ locCube d h, |tau P hP x-pv h theta x| ≤ C*h^(1:ℝ)) ∧
        Real.sqrt (∑ u, theta u^2) ≤ C ∧ pv h theta (x0 d) = tau P hP (x0 d) ∧
        (∀ x ∈ locCube d h, pv h theta x = taylorPoly (tau P hP) (Nat.ceil (1:ℝ)-1) x) := by
  have hL : 0 < L := by have := hdom.2.2.2.2.2.2.2.1; linarith
  let C := L*(Real.sqrt (d:ℝ)+1)
  have hLC : L ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (d:ℝ)]
  refine ⟨C, hL.trans_le hLC, ?_⟩
  intro P hP h hh hh'
  let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
  let theta : PolyIdx d → ℝ := Pi.single z (tau P hP (x0 d))
  have hp (x : Cov d) : pv h theta x = tau P hP (x0 d) :=
    pv_constant_coefficient h _ x
  have htarget : |tau P hP (x0 d)| ≤ L := by
    have hb := (holderNorm_le_iff (rawContrast (canonicalLaw P hP)) 1 L hL.le).mp
      (canonicalLaw_spec P hP).2.2.2.2.2.2.1
    have ht := hb.2.1 (fun _ => 0) (by simp [multiOrder]) (x0 d) (x0_mem_cube d)
    simpa [coordinatePartial_zero_index,
      tau_eq_canonicalContrast P hP (x0 d) (x0_mem_cube d)] using ht
  refine ⟨theta, ?_, ?_, hp _, ?_⟩
  · intro x hx
    have hxc : x ∈ cube d := by
      intro i
      have hi := hx i
      constructor <;> linarith [hi.1, hi.2]
    rw [hp, Real.rpow_one]
    calc
      _ ≤ L*dist x (x0 d) := tau_lipschitz_gamma_one P hP hL.le x _ hxc (x0_mem_cube d)
      _ ≤ L*(Real.sqrt (d:ℝ)*h) := mul_le_mul_of_nonneg_left
        (locCube_distance_center_bound d h hh x hx) hL.le
      _ ≤ C*h := by dsimp [C]; nlinarith
  · have hs : (∑ u, theta u^2) = (tau P hP (x0 d))^2 := by
      simp [theta, Pi.single_apply]
    rw [hs, Real.sqrt_sq_eq_abs]
    exact htarget.trans hLC
  · intro x hx
    rw [hp]
    norm_num [taylorPoly_zero_degree]

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the taylor coefficient bounds conclusion](goal) holds. -/
lemma taylor_coefficient_bounds (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h, 0 < h → h ≤ 1/2 → ∃ theta : PolyIdx d → ℝ,
        (∀ x ∈ locCube d h, |tau P hP x-pv h theta x| ≤ C*h^gamma) ∧
        Real.sqrt (∑ u, theta u^2) ≤ C ∧ pv h theta (x0 d) = tau P hP (x0 d) ∧
        (∀ x ∈ locCube d h, pv h theta x = taylorPoly (tau P hP) (Nat.ceil gamma-1) x) := by
  by_cases hg : gamma = 1
  · subst gamma
    exact taylor_coefficient_bounds_gamma_one d alpha beta L eps hdom
  · let m := Nat.ceil gamma - 1
    let s := gamma - m
    have hgamma : 1 ≤ gamma := hdom.2.2.2.2.2.1
    have hgamma3 : gamma ≤ 3 := hdom.2.2.2.2.2.2.1
    have hL : 0 < L := by linarith [hdom.2.2.2.2.2.2.2.1]
    have hgamma1 : 1 < gamma := lt_of_le_of_ne hgamma (Ne.symm hg)
    have hceil1 : 1 < Nat.ceil gamma := by
      have hc : gamma ≤ (Nat.ceil gamma : ℝ) := Nat.le_ceil gamma
      by_contra hn
      have hn' : Nat.ceil gamma ≤ 1 := by omega
      have hnR : (Nat.ceil gamma : ℝ) ≤ 1 := by exact_mod_cast hn'
      linarith
    have hceil3 : Nat.ceil gamma ≤ 3 := Nat.ceil_le.mpr (by norm_num; exact hgamma3)
    have hm : m ≤ 2 := by dsimp [m]; omega
    have hmcast : (m : ℝ) = (Nat.ceil gamma : ℝ) - 1 := by
      dsimp [m]
      rw [Nat.cast_sub hceil1.le]
      norm_num
    have hs : 0 < s := by
      dsimp [s]
      rw [hmcast]
      linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ gamma)]
    have hs1 : s ≤ 1 := by
      dsimp [s]
      rw [hmcast]
      linarith [Nat.le_ceil gamma]
    have hms : (m : ℝ) + s = gamma := by dsimp [s]; ring
    obtain ⟨C0, hC0, hC0spec⟩ :=
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.euclidean_multiindex_taylor_legendre_adapter
        d m hm
    refine ⟨C0 * L, mul_pos hC0 hL, ?_⟩
    intro P hP h hh hhhalf
    let g := rawContrast (canonicalLaw P hP)
    have heq : Set.EqOn (tau P hP) g (cube d) := by
      intro x hx
      exact tau_eq_canonicalContrast P hP x hx
    have hgdata := (holderNorm_le_iff g gamma L hL.le).mp
      (canonicalLaw_spec P hP).2.2.2.2.2.2.1
    have hu : ContDiffOn ℝ m (tau P hP) (cube d) := by
      apply (hgdata.1.congr heq).of_le
      rfl
    have hderiv : ∀ κ : GenericIndex d m, ∀ x ∈ cube d,
        |Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
          (cube d) (tau P hP) κ.1 x| ≤ L := by
      intro κ x hx
      rw [← coordinatePartial_eq_sorted (tau P hP) hu κ.1 (by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2) x hx,
        coordinatePartial_congr heq κ.1 x hx]
      exact hgdata.2.1 κ.1 (by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2) x hx
    have hmod : ∀ κ :
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.ExactIndex d m,
        ∀ x ∈ cube d, ∀ z ∈ cube d,
        |Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
            (cube d) (tau P hP) κ.1 x -
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
            (cube d) (tau P hP) κ.1 z| ≤ L * ‖x - z‖ ^ s := by
      intro κ x hx z hz
      rw [← coordinatePartial_eq_sorted (tau P hP) hu κ.1 (by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2.le) x hx,
        ← coordinatePartial_eq_sorted (tau P hP) hu κ.1 (by
          simpa only [multiOrder,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2.le) z hz,
        coordinatePartial_congr heq κ.1 x hx,
        coordinatePartial_congr heq κ.1 z hz]
      by_cases hxz : x = z
      · subst z
        simp only [sub_self, norm_zero, abs_zero]
        exact mul_nonneg hL.le (Real.rpow_nonneg (by norm_num) _)
      · simpa [s, dist_eq_norm] using hgdata.2.2 κ.1 (by
          simpa only [multiOrder,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2) x hx z hz hxz
    have hloc : locCube d h =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) h := by
      ext x
      simp only [locCube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
        Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
      constructor
      · intro hx i
        rw [abs_le]
        constructor <;> linarith [(hx i).1, (hx i).2]
      · intro hx i
        have hi := abs_le.mp (hx i)
        constructor <;> linarith
    have hsub :
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) h ⊆
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 := by
      rw [← hloc,
        ← show cube d =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 by
          ext x
          simp only [cube,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
            Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
          constructor
          · intro hx i
            rw [abs_le]
            constructor <;> linarith [(hx i).1, (hx i).2]
          · intro hx i
            have hi := abs_le.mp (hx i)
            constructor <;> linarith]
      intro x hx i
      have hi := hx i
      constructor <;> linarith [hi.1, hi.2]
    have hcube : cube d =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 := by
      ext x
      simp only [cube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
        Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
      constructor
      · intro hx i
        rw [abs_le]
        constructor <;> linarith [(hx i).1, (hx i).2]
      · intro hx i
        have hi := abs_le.mp (hx i)
        constructor <;> linarith
    obtain ⟨θ, _hθ, hpoly, hrem, hnorm, hcenter⟩ :=
      hC0spec (x0 d) (x0 d) 1 h L s (tau P hP) (by norm_num) hh hhhalf hL.le
        hs hs1 (by simpa [← hcube] using hu)
        (by simpa [← hcube] using hderiv) (by simpa [← hcube] using hmod)
        (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.center_mem_interior_cube
          (x0 d) 1 (by norm_num)) hsub
    let theta := extendCoefficients hm θ
    refine ⟨theta, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [pv_extendCoefficients hm h θ x]
      have hx' : x ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube
          (x0 d) h := by
        rw [← hloc]
        exact hx
      simpa only [theta, hms, mul_assoc] using hrem x hx'
    · rw [sum_sq_extendCoefficients hm θ]
      simpa only [theta, mul_assoc] using hnorm
    · rw [pv_extendCoefficients hm h θ (x0 d)]
      exact hcenter
    · intro x hx
      rw [pv_extendCoefficients hm h θ x, hpoly x]
      simpa only [hcube, m] using
        (taylorPoly_eq_multiindexTaylor hm (tau P hP) hu x).symm

/-- Taylor approximation and center reproduction on every oracle window contained in the design cube.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle taylor approximation conclusion](goal) holds. -/
lemma oracle_taylor_approximation (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h, 0 < h → h ≤ 1 → ∃ theta : PolyIdx d → ℝ,
        (∀ x ∈ locCube d h, |tau P hP x-pv h theta x| ≤ C*h^gamma) ∧
        pv h theta (x0 d) = tau P hP (x0 d) ∧
        (∀ x ∈ locCube d h, pv h theta x = taylorPoly (tau P hP) (Nat.ceil gamma-1) x) := by
  by_cases hg : gamma = 1
  · subst gamma
    have hL : 0 < L := by linarith [hdom.2.2.2.2.2.2.2.1]
    refine ⟨L*(Real.sqrt (d:ℝ)+1), by positivity, ?_⟩
    intro P hP h hh hh'
    let theta : PolyIdx d → ℝ := Pi.single ⟨fun _ => 0, by simp⟩ (tau P hP (x0 d))
    have hp (x : Cov d) : pv h theta x = tau P hP (x0 d) := pv_constant_coefficient h _ x
    refine ⟨theta, ?_, hp _, ?_⟩
    · intro x hx
      have hxc : x ∈ cube d := by
        intro i
        constructor <;> linarith [(hx i).1, (hx i).2]
      rw [hp, Real.rpow_one]
      calc
        _ ≤ L*dist x (x0 d) := tau_lipschitz_gamma_one P hP hL.le x _ hxc (x0_mem_cube d)
        _ ≤ L*(Real.sqrt (d:ℝ)*h) := mul_le_mul_of_nonneg_left
          (locCube_distance_center_bound d h hh x hx) hL.le
        _ ≤ _ := by nlinarith [Real.sqrt_nonneg (d:ℝ)]
    · intro x hx
      rw [hp]
      norm_num [taylorPoly_zero_degree]
  · let m := Nat.ceil gamma - 1
    let s := gamma - m
    have hgamma : 1 ≤ gamma := hdom.2.2.2.2.2.1
    have hgamma3 : gamma ≤ 3 := hdom.2.2.2.2.2.2.1
    have hL : 0 < L := by linarith [hdom.2.2.2.2.2.2.2.1]
    have hgamma1 : 1 < gamma := lt_of_le_of_ne hgamma (Ne.symm hg)
    have hceil1 : 1 < Nat.ceil gamma := by
      have hc : gamma ≤ (Nat.ceil gamma : ℝ) := Nat.le_ceil gamma
      by_contra hn
      have hn' : Nat.ceil gamma ≤ 1 := by omega
      have hnR : (Nat.ceil gamma : ℝ) ≤ 1 := by exact_mod_cast hn'
      linarith
    have hceil3 : Nat.ceil gamma ≤ 3 := Nat.ceil_le.mpr (by norm_num; exact hgamma3)
    have hm : m ≤ 2 := by dsimp [m]; omega
    have hmcast : (m : ℝ) = (Nat.ceil gamma : ℝ) - 1 := by
      dsimp [m]
      rw [Nat.cast_sub hceil1.le]
      norm_num
    have hs : 0 < s := by
      dsimp [s]
      rw [hmcast]
      linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ gamma)]
    have hs1 : s ≤ 1 := by
      dsimp [s]
      rw [hmcast]
      linarith [Nat.le_ceil gamma]
    have hms : (m : ℝ) + s = gamma := by dsimp [s]; ring
    obtain ⟨C0, hC0, hC0spec⟩ :=
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.local_cube_multiindex_remainder d m
    refine ⟨C0 * L, mul_pos hC0 hL, ?_⟩
    intro P hP h hh hhhalf
    let g := rawContrast (canonicalLaw P hP)
    have heq : Set.EqOn (tau P hP) g (cube d) := by
      intro x hx
      exact tau_eq_canonicalContrast P hP x hx
    have hgdata := (holderNorm_le_iff g gamma L hL.le).mp
      (canonicalLaw_spec P hP).2.2.2.2.2.2.1
    have hu : ContDiffOn ℝ m (tau P hP) (cube d) := by
      apply (hgdata.1.congr heq).of_le
      rfl
    have hmod : ∀ κ :
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.ExactIndex d m,
        ∀ x ∈ cube d, ∀ z ∈ cube d,
        |Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
            (cube d) (tau P hP) κ.1 x -
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordinatePartial
            (cube d) (tau P hP) κ.1 z| ≤ L * ‖x - z‖ ^ s := by
      intro κ x hx z hz
      rw [← coordinatePartial_eq_sorted (tau P hP) hu κ.1 (by
        simpa only [multiOrder,
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2.le) x hx,
        ← coordinatePartial_eq_sorted (tau P hP) hu κ.1 (by
          simpa only [multiOrder,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2.le) z hz,
        coordinatePartial_congr heq κ.1 x hx,
        coordinatePartial_congr heq κ.1 z hz]
      by_cases hxz : x = z
      · subst z
        simp only [sub_self, norm_zero, abs_zero]
        exact mul_nonneg hL.le (Real.rpow_nonneg (by norm_num) _)
      · simpa [s, dist_eq_norm] using hgdata.2.2 κ.1 (by
          simpa only [multiOrder,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiOrder] using κ.2) x hx z hz hxz
    have hloc : locCube d h =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) h := by
      ext x
      simp only [locCube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
        Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
      constructor
      · intro hx i
        rw [abs_le]
        constructor <;> linarith [(hx i).1, (hx i).2]
      · intro hx i
        have hi := abs_le.mp (hx i)
        constructor <;> linarith
    have hsub :
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) h ⊆
          Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 := by
      rw [← hloc,
        ← show cube d =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 by
          ext x
          simp only [cube,
            Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
            Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
          constructor
          · intro hx i
            rw [abs_le]
            constructor <;> linarith [(hx i).1, (hx i).2]
          · intro hx i
            have hi := abs_le.mp (hx i)
            constructor <;> linarith]
      intro x hx i
      have hi := hx i
      constructor <;> linarith [hi.1, hi.2]
    have hcube : cube d =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube (x0 d) 1 := by
      ext x
      simp only [cube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube,
        Set.mem_ofPred_eq, x0, WithLp.ofLp_toLp]
      constructor
      · intro hx i
        rw [abs_le]
        constructor <;> linarith [(hx i).1, (hx i).2]
      · intro hx i
        have hi := abs_le.mp (hx i)
        constructor <;> linarith
    let θ := Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.taylorLegendreCoefficients
      (cube d) (tau P hP) m (x0 d) h
    have hpoly (x : Cov d) :
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.legendrePolynomial (x0 d) h θ x =
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiindexTaylor
          (cube d) (tau P hP) m (x0 d) x :=
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.taylorLegendreCoefficients_realize
        hm _ _ _ _ h hh
    have hrem := hC0spec (x0 d) (x0 d) 1 h L s (tau P hP) (by norm_num) hh hL.le
      hs hs1 (by simpa [← hcube] using hu) (by simpa [← hcube] using hmod)
      (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.center_mem_interior_cube
        (x0 d) 1 (by norm_num)) hsub
    let theta := extendCoefficients hm θ
    refine ⟨theta, ?_, ?_, ?_⟩
    · intro x hx
      rw [pv_extendCoefficients hm h θ x]
      have hx' : x ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.centeredCube
          (x0 d) h := by
        rw [← hloc]
        exact hx
      rw [hpoly]
      simpa only [hcube, theta, hms, mul_assoc] using hrem x hx'
    · rw [pv_extendCoefficients hm h θ (x0 d)]
      rw [hpoly]
      exact Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiindexTaylor_center _ _ _ _
    · intro x hx
      rw [pv_extendCoefficients hm h θ x, hpoly x]
      simpa only [hcube, m] using
        (taylorPoly_eq_multiindexTaylor hm (tau P hP) hu x).symm

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
