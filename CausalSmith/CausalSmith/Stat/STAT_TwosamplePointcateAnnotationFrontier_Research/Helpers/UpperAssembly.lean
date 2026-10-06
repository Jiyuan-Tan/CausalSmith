module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationBiasGeometry
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationCausalEntries
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularSampling
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.TuningBalance
public import Causalean.Mathlib.MeasureTheory.Matrix

/-!
# Helpers/UpperAssembly

Two-channel point-CATE annotation frontier: Helpers/UpperAssembly
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


/-- Population bias assembly from the causal outcome identities and projection bounds.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the population bias bound conclusion](goal) holds. -/
lemma population_bias_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
        ∃ theta : PolyIdx d → ℝ,
          (∀ x ∈ locCube d h, pv h theta x = taylorPoly (tau P hP) (Nat.ceil gamma-1) x) ∧
          Real.sqrt (∑ u, (rBar P n m h J u-((qPop P n m h J).mulVec theta) u)^2) ≤
            C*(h^gamma+(h/J)^(alpha+beta)) := by
  obtain ⟨C, hC, hlocal⟩ := local_polynomial_projection_facts d alpha beta gamma L eps hdom
  let D := Real.sqrt (Fintype.card (PolyIdx d)) * (C^2+2*C)
  have hcard : 0 < Fintype.card (PolyIdx d) := by
    have : Nonempty (PolyIdx d) := ⟨⟨fun _ => 0, by simp⟩⟩
    exact Fintype.card_pos
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hcard)) (by nlinarith [sq_nonneg C])
  refine ⟨D, hD, ?_⟩
  intro P hP n m h J hn hh hh' hJ
  obtain ⟨⟨theta, herr, htheta, hcenter, htaylor⟩, hcoarse, hrow, htrace, he, hmu⟩ :=
    hlocal P hP h J hh hh' hJ
  refine ⟨theta, htaylor, ?_⟩
  have hB : 0 ≤ (C^2+2*C)*(h^gamma+(h/J)^(alpha+beta)) := by positivity
  have hb := population_finite_norm_bound
    (fun u => rBar P n m h J u - ((qPop P n m h J).mulVec theta) u)
    _ hB (population_bias_coordinate_bound P hP n m hn h hh hh' J hJ theta C hC herr he hmu)
  calc
    _ ≤ Real.sqrt (Fintype.card (PolyIdx d)) *
        ((C^2+2*C)*(h^gamma+(h/J)^(alpha+beta))) := hb
    _ = D*(h^gamma+(h/J)^(alpha+beta)) := by dsimp [D]; ring
/-- Unit quadratic forms are bounded below by the sum of absolute matrix entries.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the unit quadratic bdd below conclusion](goal) holds. -/
lemma unit_quadratic_bddBelow {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ) :
    BddBelow {c : ℝ | ∃ v : PolyIdx d → ℝ, (∑ u, v u^2) = 1 ∧
      c = ∑ u, v u * (Q.mulVec v) u} := by
  refine ⟨-(∑ u, ∑ w, |Q u w|), ?_⟩
  rintro c ⟨v, hv, rfl⟩
  have hcoord : ∀ u, |v u| ≤ 1 := by
    intro u
    have hu : v u ^ 2 ≤ ∑ w, v w ^ 2 :=
      Finset.single_le_sum (fun w _ => sq_nonneg (v w)) (Finset.mem_univ u)
    rw [hv] at hu
    have habs := sq_abs (v u)
    nlinarith [abs_nonneg (v u)]
  have hbound : |∑ u, v u * (Q.mulVec v) u| ≤ ∑ u, ∑ w, |Q u w| := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    calc
      |∑ u, ∑ w, v u * (Q u w * v w)| ≤
          ∑ u, |∑ w, v u * (Q u w * v w)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u, ∑ w, |v u * (Q u w * v w)| := by
        apply Finset.sum_le_sum
        intro u _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u, ∑ w, |Q u w| := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro w _
        rw [abs_mul, abs_mul]
        calc
          |v u| * (|Q u w| * |v w|) ≤ 1 * (|Q u w| * 1) :=
            mul_le_mul (hcoord u)
              (mul_le_mul_of_nonneg_left (hcoord w) (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
          _ = |Q u w| := by ring
  exact (abs_le.mp hbound).1

/-- The Rayleigh infimum is at most every unit-vector quadratic form.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input v](hyp:v), [the specified input hv](hyp:hv), [the lambda min le unit quadratic conclusion](goal) holds. -/
lemma lambdaMin_le_unit_quadratic {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (v : PolyIdx d → ℝ) (hv : (∑ u, v u^2) = 1) :
    lambdaMin Q ≤ ∑ u, v u * (Q.mulVec v) u := by
  exact csInf_le (unit_quadratic_bddBelow Q) ⟨v, hv, rfl⟩

/-- [the measurable bit conclusion](goal) holds. -/
@[fun_prop] lemma measurable_bit : Measurable bit := by
  fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the measurable treatment records conclusion](goal) holds. -/
@[fun_prop] lemma measurable_treatmentRecords (d n m : ℕ) (i : Fin (n+m)) :
    Measurable (fun D : Dataset d n m => treatmentRecords D i) := by
  unfold treatmentRecords
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left]
    fun_prop
  · intro j
    simp only [Fin.addCases_right]
    fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the measurable eta hat conclusion](goal) holds. -/
@[fun_prop] lemma measurable_etaHat (d n m : ℕ) (h : ℝ) (J : ℕ) :
    Measurable (fun p : Dataset d n m × Cov d => etaHat p.1 h J p.2) := by
  unfold etaHat
  apply Measurable.ite ((isClosed_locCube d h).measurableSet.preimage measurable_snd)
  · fun_prop
  · fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the measurable r hat conclusion](goal) holds. -/
@[fun_prop] lemma measurable_rHat (d n m : ℕ) (h : ℝ) (J : ℕ) (u : PolyIdx d) :
    Measurable (fun D : Dataset d n m => rHat D h J u) := by
  unfold rHat
  fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input u](hyp:u), [the specified input v](hyp:v), [the measurable q hat conclusion](goal) holds. -/
@[fun_prop] lemma measurable_qHat (d n m : ℕ) (h : ℝ) (J : ℕ) (u v : PolyIdx d) :
    Measurable (fun D : Dataset d n m => qHat D h J u v) := by
  unfold qHat qRaw
  fun_prop

/-- The guard is the intersection of closed inequalities over all unit vectors.  Given [the specified input d](hyp:d), [the specified input a](hyp:a), [the is closed lambda min ge conclusion](goal) holds. -/
lemma isClosed_lambdaMin_ge (d : ℕ) (a : ℝ) :
    IsClosed {Q : PolyIdx d → PolyIdx d → ℝ | a ≤ lambdaMin Q} := by
  have hne (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ) :
      Set.Nonempty {c : ℝ | ∃ v : PolyIdx d → ℝ, (∑ u, v u^2) = 1 ∧
        c = ∑ u, v u * (Matrix.mulVec Q v) u} := by
    let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
    let v : PolyIdx d → ℝ := Pi.single z 1
    refine ⟨_, v, ?_, rfl⟩
    simp [v, Pi.single_apply]
  have heq : {Q : PolyIdx d → PolyIdx d → ℝ | a ≤ lambdaMin Q} =
      ⋂ (v : PolyIdx d → ℝ) (_ : (∑ u, v u^2) = 1),
        {Q : PolyIdx d → PolyIdx d → ℝ | a ≤ ∑ u, v u * (Matrix.mulVec Q v) u} := by
    ext Q
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro ha v hv
      exact ha.trans (lambdaMin_le_unit_quadratic Q v hv)
    · intro ha
      apply le_csInf (hne Q)
      rintro c ⟨v, hv, rfl⟩
      exact ha v hv
  rw [heq]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  apply isClosed_le continuous_const
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the overlap level eps](hyp:eps), [the measurable t hat total conclusion](goal) holds. -/
@[fun_prop] lemma measurable_tHat_total (d n m : ℕ) (eps h : ℝ) (J : ℕ) :
    Measurable (fun D : Dataset d n m => tHat eps h J D) := by
  have hQ : Measurable (fun D : Dataset d n m => fun u v => qHat D h J u v) := by
    exact measurable_pi_lambda _ (fun u => measurable_pi_lambda _ (fun v => measurable_qHat d n m h J u v))
  have hguard : MeasurableSet {D : Dataset d n m | gramGuard eps ≤ lambdaMin (qHat D h J)} :=
    (isClosed_lambdaMin_ge d (gramGuard eps)).measurableSet.preimage hQ
  unfold tHat
  apply Measurable.ite hguard
  · unfold clip Matrix.mulVec dotProduct
    fun_prop
  · fun_prop

/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hn](hyp:hn), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the overlap level eps](hyp:eps), [the t hat measurable conclusion](goal) holds. -/
@[fun_prop] lemma tHat_measurable (d n m : ℕ) (eps h : ℝ) (J : ℕ)
    (hn : 2 ≤ n) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) :
    Measurable (fun w : Sample d n m => tHat eps h J w.1) := by
  exact (measurable_tHat_total d n m eps h J).comp measurable_fst

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the sharp decision measurable conclusion](goal) holds. -/
@[fun_prop] lemma sharpDecision_measurable (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n m : ℕ) (hn : 2 ≤ n) :
    Measurable (sharpDecision d alpha beta gamma eps n m) := by
  exact (measurable_tHat_total d n m eps _ _).comp measurable_fst

/-- A positive Rayleigh infimum excludes a nonzero kernel and makes the matrix invertible.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input hmin](hyp:hmin), [the is unit of lambda min pos conclusion](goal) holds. -/
lemma isUnit_of_lambdaMin_pos {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (hmin : 0 < lambdaMin Q) : IsUnit Q := by
  have hkernel : ∀ v : PolyIdx d → ℝ, Q.mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have hs : 0 < ∑ u, v u ^ 2 := by
      have hex : ∃ u, v u ≠ 0 := by
        by_contra h
        apply hne
        ext u
        simpa using (not_exists.mp h u)
      obtain ⟨u, hu⟩ := hex
      exact lt_of_lt_of_le (sq_pos_of_ne_zero hu)
        (Finset.single_le_sum (fun w _ => sq_nonneg (v w)) (Finset.mem_univ u))
    let w : PolyIdx d → ℝ := (Real.sqrt (∑ u, v u ^ 2))⁻¹ • v
    have hwunit : (∑ u, w u ^ 2) = 1 := by
      simp only [w, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow]
      rw [Real.sq_sqrt hs.le]
      exact inv_mul_cancel₀ hs.ne'
    have hwzero : Q.mulVec w = 0 := by
      dsimp only [w]
      rw [Matrix.mulVec_smul, hv, smul_zero]
    have hle := lambdaMin_le_unit_quadratic Q w hwunit
    rw [hwzero] at hle
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hle
    exact (not_le_of_gt hmin) hle
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hk : Q.mulVec (v-w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hkernel (v-w) hk)

/-- Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input hQ](hyp:hQ), [the specified input hmin](hyp:hmin), [the specified input R](hyp:R), [the specified input theta](hyp:theta), [the good branch resolvent conclusion](goal) holds. -/
lemma good_branch_resolvent {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (hQ : Q.transpose = Q) (g : ℝ) (hg : 0 < g) (hmin : g ≤ lambdaMin Q)
    (R theta : PolyIdx d → ℝ) :
    Q⁻¹.mulVec R-theta = Q⁻¹.mulVec (R-Q.mulVec theta) := by
  have hunit : IsUnit Q := isUnit_of_lambdaMin_pos Q (by linarith)
  have hinv : Q⁻¹.mulVec (Q.mulVec theta) = theta := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q
      ((Matrix.isUnit_iff_isUnit_det Q).mp hunit), Matrix.one_mulVec]
  rw [Matrix.mulVec_sub, hinv]
/-- Given [the specified input x](hyp:x), [the specified input y](hyp:y), [the specified input hy](hyp:hy), [the clipping contraction conclusion](goal) holds. -/
lemma clipping_contraction (x y : ℝ) (hy : y ∈ Icc (-1) 1) :
    |clip x-y| ≤ |x-y| := by
  rcases hy with ⟨hyl, hyu⟩
  by_cases hxl : x ≤ -1
  · have hxu : x ≤ 1 := by linarith
    rw [clip, min_eq_right hxu, max_eq_left hxl,
      abs_of_nonpos (by linarith : -1-y ≤ 0),
      abs_of_nonpos (by linarith : x-y ≤ 0)]
    linarith
  · by_cases hxu : 1 ≤ x
    · rw [clip, min_eq_left hxu, max_eq_right (by norm_num : (-1:ℝ) ≤ 1),
        abs_of_nonneg (by linarith : 1-y ≥ 0),
        abs_of_nonneg (by linarith : x-y ≥ 0)]
      linarith
    · rw [clip, min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hxl)]

/-- Localization boxes are compact, including degenerate parameter values.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the is compact loc cube conclusion](goal) holds. -/
lemma isCompact_locCube (d : ℕ) (h : ℝ) : IsCompact (locCube d h) := by
  have heq : locCube d h = ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
    Set.pi Set.univ (fun _ => Icc (1/2-h/2) (1/2+h/2))) := by
    ext x
    simp only [locCube, mem_setOf_eq, mem_preimage, mem_pi, mem_univ, forall_const]
    rfl
  rw [heq]
  exact (Homeomorph.isCompact_preimage _).2 (isCompact_univ_pi fun _ => isCompact_Icc)

/-- A measurable function supported on a localization box and dominated there by a continuous function is essentially bounded after any measurable covariate map.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hbound](hyp:hbound), [the specified input hsupp](hyp:hsupp), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [the compact supported mem lp top conclusion](goal) holds. -/
lemma compact_supported_memLp_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (h : ℝ) (f g : Cov d → ℝ)
    (hf : Measurable f) (hg : Continuous g)
    (hbound : ∀ x ∈ locCube d h, |f x| ≤ |g x|)
    (hsupp : ∀ x, x ∉ locCube d h → f x = 0)
    (X : Ω → Cov d) (hX : Measurable X) : MemLp (fun w => f (X w)) ∞ μ := by
  obtain ⟨C, hC⟩ := (isCompact_locCube d h).exists_bound_of_continuousOn hg.continuousOn
  apply memLp_top_of_bound (hf.comp hX).aestronglyMeasurable (max C 0)
  filter_upwards [] with w
  change |f (X w)| ≤ max C 0
  by_cases hx : X w ∈ locCube d h
  · exact (hbound _ hx).trans ((hC _ hx).trans (le_max_left _ _))
  · rw [hsupp _ hx, abs_zero]
    exact le_max_right _ _

/-- Localized finite products of coarse polynomial entries are essentially bounded on any sample space.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input us](hyp:us), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [the weighted coarse mem lp top conclusion](goal) holds. -/
lemma weighted_coarse_memLp_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (h : ℝ) (us : Finset (PolyIdx d))
    (X : Ω → Cov d) (hX : Measurable X) :
    MemLp (fun w => locWeight h (X w) * ∏ u ∈ us, coarseBasis h (X w) u) ∞ μ := by
  apply compact_supported_memLp_top μ d h (fun x => locWeight h x * ∏ u ∈ us, coarseBasis h x u)
    (fun x => h^(-(d:ℝ)) * ∏ u ∈ us, coarseBasis h x u) ?_ ?_ ?_ ?_ X hX
  · fun_prop
  · unfold coarseBasis
    fun_prop
  · intro x hx
    simp only [locWeight, if_pos hx, le_refl]
  · intro x hx
    simp [locWeight, hx]

/-- Each cellwise basis entry is essentially bounded after a measurable covariate map.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the specified input X](hyp:X), [the specified input hX](hyp:hX), [the fine basis mem lp top comp conclusion](goal) holds. -/
lemma fineBasis_memLp_top_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (z : FineIdx d J) (X : Ω → Cov d) (hX : Measurable X) :
    MemLp (fun w => fineBasis h J (X w) z) ∞ μ := by
  apply compact_supported_memLp_top μ d h (fun x => fineBasis h J x z)
    (fun x => Real.sqrt ((J:ℝ)^d) * ∏ i, legendre (z.2.1 i)
      ((x i-(1/2-h/2+((z.1 i:ℝ)+1/2)*(h/J)))/(h/J))) ?_ ?_ ?_ ?_ X hX
  · fun_prop
  · fun_prop
  · intro x hx
    unfold fineBasis
    split_ifs
    · exact le_refl _
    · simpa only [abs_zero] using (abs_nonneg (Real.sqrt ((J:ℝ)^d) * ∏ i, legendre (z.2.1 i)
        ((x i-(1/2-h/2+((z.1 i:ℝ)+1/2)*(h/J)))/(h/J))))
  · intro x hx
    exact if_neg (fun hc => hx (cell_subset_locCube h J hh hJ z.1 hc))

/-- Each empirical Gram entry is essentially bounded at every fixed admissible resolution.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the q hat mem lp top conclusion](goal) holds. -/
lemma qHat_memLp_top (d n m : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 1 ≤ J) (μ : Measure (Sample d n m)) (u v : PolyIdx d) :
    MemLp (fun w => qHat w.1 h J u v) ∞ μ := by
  have hw (X : Sample d n m → Cov d) (hX : Measurable X) (u : PolyIdx d) :
      MemLp (fun w => locWeight h (X w) * coarseBasis h (X w) u) ∞ μ := by
    simpa using weighted_coarse_memLp_top μ d h {u} X hX
  have hw2 (X : Sample d n m → Cov d) (hX : Measurable X) (u v : PolyIdx d) :
      MemLp (fun w => locWeight h (X w) * coarseBasis h (X w) u * coarseBasis h (X w) v) ∞ μ := by
    apply compact_supported_memLp_top μ d h (fun x => locWeight h x * coarseBasis h x u * coarseBasis h x v)
      (fun x => h^(-(d:ℝ)) * coarseBasis h x u * coarseBasis h x v) ?_ ?_ ?_ ?_ X hX
    · fun_prop
    · unfold coarseBasis; fun_prop
    · intro x hx; simp only [locWeight, if_pos hx, le_refl]
    · intro x hx; simp [locWeight, hx]
  have hb (A : Sample d n m → Bool) (hA : Measurable A) :
      MemLp (fun w => bit (A w)) ∞ μ := by
    apply memLp_top_of_bound (by fun_prop) 1
    filter_upwards [] with w
    cases A w <;> norm_num [bit]
  have hk (X Y : Sample d n m → Cov d) (hX : Measurable X) (hY : Measurable Y) :
      MemLp (fun w => fineKernel d h J (X w) (Y w)) ∞ μ := by
    exact memLp_finsetSum _ (fun z _ =>
      (fineBasis_memLp_top_comp μ d h J hh hJ z Y hY).mul'
        (fineBasis_memLp_top_comp μ d h J hh hJ z X hX))
  have hraw (u v : PolyIdx d) : MemLp (fun w => qRaw w.1 h J u v) ∞ μ := by
    unfold qRaw
    apply MemLp.sub
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro j hj
      exact (hb (fun w => (w.1.1 j).2.1) (by fun_prop)).mul'
        (hw2 (fun w => (w.1.1 j).1) (by fun_prop) u v)
    · apply MemLp.const_mul
      apply memLp_finsetSum
      intro i hi
      apply memLp_finsetSum
      intro j hj
      have hiX : Measurable (fun w : Sample d n m => (treatmentRecords w.1 i).1) := by fun_prop
      have hiA : Measurable (fun w : Sample d n m => (treatmentRecords w.1 i).2) := by fun_prop
      convert (((hw _ hiX u).mul (r := ∞) (hw (fun w => (w.1.1 j).1) (by fun_prop) v)).mul (r := ∞)
        (hb _ hiA)).mul (r := ∞) (hb (fun w => (w.1.1 j).2.1) (by fun_prop)) |>.mul (r := ∞)
          (hk _ _ hiX (show Measurable (fun w : Sample d n m => (w.1.1 j).1) by fun_prop)) using 1
      ext w
      simp only [Pi.mul_apply]
      ring
  simpa only [qHat, div_eq_mul_inv, Pi.add_apply] using ((hraw u v).add (hraw v u)).mul_const (2:ℝ)⁻¹


/-- The original-record experiment, including its independent randomizer, is a probability law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the experiment probability conclusion](goal) holds. -/
lemma experiment_probability (d n m : ℕ) (P : PrimitiveLaw d) :
    IsProbabilityMeasure (experiment P n m) := by
  have ho : Measurable (observed (d:=d)) := by
    unfold observed
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact Measurable.ite ((measurableSet_singleton true).preimage (by fun_prop))
      (by fun_prop) (by fun_prop)
  letI : IsProbabilityMeasure (obsLaw P) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map ho.aemeasurable
  letI : IsProbabilityMeasure (xaLaw P) := by
    unfold xaLaw
    exact Measure.isProbabilityMeasure_map (show Measurable (fun w : FullRecord d => (w.1,w.2.1)) by fun_prop).aemeasurable
  letI : IsProbabilityMeasure (volume.restrict (Icc (0:ℝ) 1)) := ⟨by simp⟩
  unfold experiment
  infer_instance

/-- The squared Frobenius deviation of the empirical Gram matrix is integrable, as a finite sum of bounded measurable terms.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the q hat square deviation integrable conclusion](goal) holds. -/
lemma qHat_square_deviation_integrable (d n m : ℕ) (P : PrimitiveLaw d)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J) :
    Integrable (fun w : Sample d n m => ∑ u, ∑ v,
      (qHat w.1 h J u v-qPop P n m h J u v)^2) (experiment P n m) := by
  letI := experiment_probability d n m P
  apply integrable_finsetSum
  intro u hu
  apply integrable_finsetSum
  intro v hv
  have hq := qHat_memLp_top d n m h J hh hJ (experiment P n m) u v
  exact ((hq.sub (memLp_const _)).mono_exponent (show (2:ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq

/-- A constant-polynomial coordinate supplies a unit vector for the Rayleigh infimum.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the unit quadratic nonempty conclusion](goal) holds. -/
lemma unit_quadratic_nonempty {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ) :
    Set.Nonempty {c : ℝ | ∃ v : PolyIdx d → ℝ, (∑ u, v u^2) = 1 ∧
      c = ∑ u, v u*(Q.mulVec v) u} := by
  let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
  let v : PolyIdx d → ℝ := Pi.single z 1
  refine ⟨_, v, ?_, rfl⟩
  simp [v, Pi.single_apply]

/-- Finite Cauchy–Schwarz bounds the squared quadratic form of a unit vector by the squared Frobenius norm.  Given [the specified input E](hyp:E), [the specified input v](hyp:v), [the specified input hv](hyp:hv), [the quadratic sq le frobenius sq conclusion](goal) holds. -/
lemma quadratic_sq_le_frobenius_sq {ι : Type*} [Fintype ι]
    (E : Matrix ι ι ℝ) (v : ι → ℝ) (hv : (∑ u, v u^2) = 1) :
    (∑ u, v u*(E.mulVec v) u)^2 ≤ ∑ u, ∑ w, (E u w)^2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun uw => E uw.1 uw.2) (fun uw => v uw.1 * v uw.2)
  have hn : (∑ uw : ι × ι, (v uw.1 * v uw.2)^2) = 1 := by
    simp only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, hv, mul_one]
  rw [hn, mul_one] at hc
  convert hc using 1
  · rfl
  · congr 1
    simp only [Fintype.sum_prod_type, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro w hw
    ring
  · simp only [Fintype.sum_prod_type]

/-- Failure of the empirical Rayleigh guard forces a squared Frobenius deviation of at least the squared guard threshold.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hcut](hyp:hcut), [the gram cutoff sq deviation conclusion](goal) holds. -/
lemma gram_cutoff_sq_deviation {d : ℕ} (Q B : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (g : ℝ) (hg : 0 < g)
    (hB : ∀ v : PolyIdx d → ℝ, (∑ u, v u^2) = 1 →
      2*g ≤ ∑ u, v u*(B.mulVec v) u)
    (hcut : lambdaMin Q < g) :
    g^2 ≤ ∑ u, ∑ v, (Q u v-B u v)^2 := by
  by_contra hnot
  have hs : (∑ u, ∑ v, (Q u v-B u v)^2) < g^2 := lt_of_not_ge hnot
  have hmin : g ≤ lambdaMin Q := by
    apply le_csInf (unit_quadratic_nonempty Q)
    rintro c ⟨v, hv, rfl⟩
    have hpop := hB v hv
    have hc := (quadratic_sq_le_frobenius_sq (Q-B) v hv).trans_lt hs
    have he : (∑ u, v u*((Q-B).mulVec v) u) =
        (∑ u, v u*(Q.mulVec v) u) - (∑ u, v u*(B.mulVec v) u) := by
      simp only [Matrix.sub_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [he] at hc
    nlinarith
  exact (not_lt_of_ge hmin) hcut


/-- Population positivity and the rectangular second-moment bound control the probability that the empirical Gram guard fails.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the gram cutoff probability conclusion](goal) holds. -/
lemma gram_cutoff_probability (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
        experiment P n m {w | lambdaMin (qHat w.1 h J) < gramGuard eps} ≤
          ENNReal.ofReal (C*(1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
            ((n:ℝ)*((n:ℝ)+m)*h^(2*d)))) := by
  obtain ⟨C, hC, hsampling⟩ := rectangular_sampling_bound d alpha beta gamma L eps hdom
  have hg : 0 < gramGuard eps := hdom.gramGuard_pos
  refine ⟨C / (gramGuard eps)^2, by positivity, ?_⟩
  intro P hP n m h J hn hh hh' hJ
  letI := experiment_probability d n m P
  let f : Sample d n m → ℝ := fun w => ∑ u, ∑ v,
    (qHat w.1 h J u v-qPop P n m h J u v)^2
  have hf : Integrable f (experiment P n m) :=
    qHat_square_deviation_integrable d n m P h J hh hJ
  have hf0 : ∀ w, 0 ≤ f w := fun w =>
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hsub : {w : Sample d n m | lambdaMin (qHat w.1 h J) < gramGuard eps} ⊆
      {w | (gramGuard eps)^2 ≤ f w} := by
    intro w hw
    apply gram_cutoff_sq_deviation _ _ _ hg _ hw
    intro v hv
    have hb := (population_positivity d alpha beta gamma L eps hdom P hP n m hn h hh hh' J hJ v).2
    have h2 : 2*gramGuard eps = eps*(1-eps) := by unfold gramGuard; ring
    rw [h2]
    simpa only [hv, mul_one] using hb
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hf ((gramGuard eps)^2)
  have hreal : (experiment P n m).real {w | lambdaMin (qHat w.1 h J) < gramGuard eps} ≤
      (∫ w, f w ∂experiment P n m) / (gramGuard eps)^2 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < (gramGuard eps)^2)).mpr
    calc
      _ ≤ (experiment P n m).real {w | (gramGuard eps)^2 ≤ f w} * (gramGuard eps)^2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) (by positivity)
      _ ≤ _ := by nlinarith [hmarkov]
  have hs := hsampling P hP n m h J hn hh hh' hJ
  have hvariance : (∫ w, f w ∂experiment P n m) ≤
      C*(1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
        ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
    have hr : 0 ≤ (∫ w : Sample d n m, ∑ u, (rHat w.1 h J u-rBar P n m h J u)^2 ∂experiment P n m) :=
      integral_nonneg (fun w => Finset.sum_nonneg fun u _ => sq_nonneg _)
    dsimp only [f]
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (experiment P n m) _)]
  apply ENNReal.ofReal_le_ofReal
  change (experiment P n m).real _ ≤ _
  calc
    _ ≤ _ := hreal
    _ ≤ _ := div_le_div_of_nonneg_right hvariance (by positivity)
    _ = _ := by ring


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
