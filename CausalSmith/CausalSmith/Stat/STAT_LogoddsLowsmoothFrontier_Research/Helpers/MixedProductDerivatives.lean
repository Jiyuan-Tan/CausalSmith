module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureProductDerivatives
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedMixtureTaylor

/-! # Mixed partial derivatives of record products

Leibniz differentiation bounds the mixed amplitude derivative of a finite
product using only derivatives of its individual records. -/
public section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The mixed Leibniz estimate counts both diagonal and off-diagonal terms.
First-coordinate differentiability is needed only near the second coordinate,
so this applies inside a signed calibration neighborhood. [the documented result](goal) Under [the stated assumptions](hyp:f,x,hM,hx,hy,hxy,h0,h1x,h1y,h2). -/
-- @node: mixture_product_mixed_derivative_bounds
lemma mixture_product_mixed_derivative_bounds {ι : Type*}
    (I : Finset ι) (f : ι → ℝ → ℝ → ℝ) (x y M : ℝ) (hM : 1 ≤ M)
    (hx : ∀ᶠ z in 𝓝 y, ∀ i ∈ I, DifferentiableAt ℝ (fun r => f i r z) x)
    (hy : ∀ i ∈ I, DifferentiableAt ℝ (f i x) y)
    (hxy : ∀ i ∈ I, DifferentiableAt ℝ (fun z => deriv (fun r => f i r z) x) y)
    (h0 : ∀ i ∈ I, |f i x y| ≤ 2)
    (h1x : ∀ i ∈ I, |deriv (fun r => f i r y) x| ≤ M)
    (h1y : ∀ i ∈ I, |deriv (f i x) y| ≤ M)
    (h2 : ∀ i ∈ I, |deriv (fun z => deriv (fun r => f i r z) x) y| ≤ M) :
    DifferentiableAt ℝ (fun z => deriv (fun r => ∏ i ∈ I, f i r z) x) y ∧
    |∏ i ∈ I, f i x y| ≤ 2 ^ I.card ∧
    |deriv (fun r => ∏ i ∈ I, f i r y) x| ≤ M * (I.card : ℝ) * 2 ^ I.card ∧
    |deriv (fun z => ∏ i ∈ I, f i x z) y| ≤ M * (I.card : ℝ) * 2 ^ I.card ∧
    |deriv (fun z => deriv (fun r => ∏ i ∈ I, f i r z) x) y| ≤
      M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hxI : ∀ᶠ z in 𝓝 y, ∀ j ∈ I, DifferentiableAt ℝ (fun r => f j r z) x :=
      hx.mono (fun z hz j hj => hz j (Finset.mem_insert_of_mem hj))
    have hyI := fun j hj => hy j (Finset.mem_insert_of_mem hj)
    have hxyI := fun j hj => hxy j (Finset.mem_insert_of_mem hj)
    obtain ⟨hpd, hv, hdx, hdy, hdxy⟩ := ih hxI hyI hxyI
      (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1x j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1y j (Finset.mem_insert_of_mem hj))
      (fun j hj => h2 j (Finset.mem_insert_of_mem hj))
    have hxi := hx.self_of_nhds i (Finset.mem_insert_self i I)
    have hyi := hy i (Finset.mem_insert_self i I)
    have hxyi := hxy i (Finset.mem_insert_self i I)
    have hvi := h0 i (Finset.mem_insert_self i I)
    have hdi := h1x i (Finset.mem_insert_self i I)
    have hei := h1y i (Finset.mem_insert_self i I)
    have hdei := h2 i (Finset.mem_insert_self i I)
    have hpx : DifferentiableAt ℝ (fun r => ∏ j ∈ I, f j r y) x :=
      DifferentiableAt.fun_finsetProd (fun j hj => hxI.self_of_nhds j hj)
    have hpy : DifferentiableAt ℝ (fun z => ∏ j ∈ I, f j x z) y :=
      DifferentiableAt.fun_finsetProd hyI
    have hdxEq := (hxi.hasDerivAt.fun_mul hpx.hasDerivAt).deriv
    have hdyEq := (hyi.hasDerivAt.fun_mul hpy.hasDerivAt).deriv
    have hEq : (fun z => deriv (fun r => f i r z * ∏ j ∈ I, f j r z) x) =ᶠ[𝓝 y]
        (fun z => deriv (fun r => f i r z) x * (∏ j ∈ I, f j x z) +
          f i x z * deriv (fun r => ∏ j ∈ I, f j r z) x) := by
      filter_upwards [hx] with z hz
      exact ((hz i (Finset.mem_insert_self i I)).hasDerivAt.mul
        (DifferentiableAt.fun_finsetProd
          (fun j hj => hz j (Finset.mem_insert_of_mem hj))).hasDerivAt).deriv
    have hCross := ((hxyi.hasDerivAt.mul hpy.hasDerivAt).add
      (hyi.hasDerivAt.mul hpd.hasDerivAt)).congr_of_eventuallyEq hEq
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, pow_succ, pow_zero, one_mul]
    refine ⟨hCross.differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [abs_mul]
      exact (mul_le_mul hvi hv (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    · rw [hdxEq]
      calc
        _ ≤ |deriv (fun r => f i r y) x| * |∏ j ∈ I, f j x y| +
            |f i x y| * |deriv (fun r => ∏ j ∈ I, f j r y) x| := by
          simp only [← abs_mul]
          exact abs_add_le _ _
        _ ≤ M * 2 ^ I.card + 2 * (M * (I.card : ℝ) * 2 ^ I.card) := by gcongr
        _ ≤ _ := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ M)
            (by positivity : 0 ≤ (2 : ℝ)^I.card)]
    · rw [hdyEq]
      calc
        _ ≤ |deriv (f i x) y| * |∏ j ∈ I, f j x y| +
            |f i x y| * |deriv (fun z => ∏ j ∈ I, f j x z) y| := by
          simp only [← abs_mul]
          exact abs_add_le _ _
        _ ≤ M * 2 ^ I.card + 2 * (M * (I.card : ℝ) * 2 ^ I.card) := by gcongr
        _ ≤ _ := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ M)
            (by positivity : 0 ≤ (2 : ℝ)^I.card)]
    · rw [hCross.deriv]
      calc
        _ ≤ |deriv (fun z => deriv (fun r => f i r z) x) y| * |∏ j ∈ I, f j x y| +
            |deriv (fun r => f i r y) x| * |deriv (fun z => ∏ j ∈ I, f j x z) y| +
            (|deriv (f i x) y| * |deriv (fun r => ∏ j ∈ I, f j r y) x| +
            |f i x y| * |deriv (fun z => deriv (fun r => ∏ j ∈ I, f j r z) x) y|) := by
          simp only [← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ ≤ M * 2 ^ I.card + M * (M * (I.card : ℝ) * 2 ^ I.card) +
            (M * (M * (I.card : ℝ) * 2 ^ I.card) +
            2 * (M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card)) := by gcongr
        _ ≤ _ := by
          have hp : 0 ≤ (2 : ℝ) ^ I.card := by positivity
          have hm2 : M ≤ M ^ 2 := by nlinarith
          have hc : 0 ≤ (I.card : ℝ) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hp,
            mul_nonneg (by positivity : 0 ≤ M ^ 2 * (I.card : ℝ)) hp]

/-- [Finite hidden-sign averages commute with the two amplitude derivatives;
the difference of two averages costs a factor of two in the envelope. [the documented result](goal) Under [the stated assumptions](hyp:f,x,hx,hxy,hb). -/
-- @node: mixture_average_mixed_derivative_bound
lemma mixture_average_mixed_derivative_bound {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : Bool → σ → ℝ → ℝ → ℝ) (x y C : ℝ)
    (hx : ∀ᶠ z in 𝓝 y, ∀ b s, DifferentiableAt ℝ (fun r => f b s r z) x)
    (hxy : ∀ b s, DifferentiableAt ℝ (fun z => deriv (fun r => f b s r z) x) y)
    (hb : ∀ b s, |deriv (fun z => deriv (fun r => f b s r z) x) y| ≤ C) :
    DifferentiableAt ℝ (fun z => deriv (fun r => (Fintype.card σ : ℝ)⁻¹ *
      ((∑ s, f false s r z) - ∑ s, f true s r z)) x) y ∧
    |deriv (fun z => deriv (fun r => (Fintype.card σ : ℝ)⁻¹ *
      ((∑ s, f false s r z) - ∑ s, f true s r z)) x) y| ≤ 2*C := by
  classical
  let a : ℝ := (Fintype.card σ : ℝ)⁻¹
  let df := fun b s z => deriv (fun r => f b s r z) x
  have he : (fun z => deriv (fun r => a *
      ((∑ s, f false s r z) - ∑ s, f true s r z)) x) =ᶠ[𝓝 y]
      (fun z => a * ((∑ s, df false s z) - ∑ s, df true s z)) := by
    filter_upwards [hx] with z hz
    exact (((HasDerivAt.fun_sum (fun s _ => (hz false s).hasDerivAt)).sub
      (HasDerivAt.fun_sum (fun s _ => (hz true s).hasDerivAt))).const_mul a).deriv
  have hd := (((HasDerivAt.fun_sum (fun s _ => (hxy false s).hasDerivAt)).sub
    (HasDerivAt.fun_sum (fun s _ => (hxy true s).hasDerivAt))).const_mul a).congr_of_eventuallyEq he
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hcard : (Fintype.card σ : ℝ) ≠ 0 := by positivity
  have havg (b : Bool) : |a * ∑ s, deriv (df b s) y| ≤ C := by
    calc
      _ = a * |∑ s, deriv (df b s) y| := by rw [abs_mul, abs_of_nonneg ha]
      _ ≤ a * ∑ s, |deriv (df b s) y| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ a * ∑ _s : σ, C := by
        gcongr with s
        exact hb b s
      _ = C := by simp [a, hcard]
  rw [mul_sub]
  have h := abs_sub_le (a * ∑ s, deriv (df false s) y) 0
    (a * ∑ s, deriv (df true s) y)
  simp only [sub_zero, zero_sub, abs_neg] at h
  exact h.trans (by linarith [havg false, havg true])

/-- [The actual mixed block inherits its mixed derivative envelope from
one-record partial derivatives, with all calibration roots substituted. [the documented result](goal) Under [the stated assumptions](hyp:x,hxsmall,hysmall,hM,hx,hy,hxy,hdx,hdy,hdxy). -/
-- @node: mixedComponentDifference_cross_derivative_bound
lemma mixedComponentDifference_cross_derivative_bound {n : ℕ} (k : ℕ)
    (I : Finset (Fin n)) (o : Fin n → Record) (x y M : ℝ)
    (hxsmall : |x| ≤ 1/100) (hysmall : |y| ≤ 1/100) (hM : 1 ≤ M)
    (hx : ∀ᶠ z in 𝓝 y, ∀ b σ i, i ∈ I → DifferentiableAt ℝ
      (fun r => recordCellDensity (mixedLaw b k σ r z) (o i)) x)
    (hy : ∀ b σ i, i ∈ I → DifferentiableAt ℝ
      (fun z => recordCellDensity (mixedLaw b k σ x z) (o i)) y)
    (hxy : ∀ b σ i, i ∈ I → DifferentiableAt ℝ
      (fun z => deriv (fun r => recordCellDensity (mixedLaw b k σ r z) (o i)) x) y)
    (hdx : ∀ b σ i, i ∈ I →
      |deriv (fun r => recordCellDensity (mixedLaw b k σ r y) (o i)) x| ≤ M)
    (hdy : ∀ b σ i, i ∈ I →
      |deriv (fun z => recordCellDensity (mixedLaw b k σ x z) (o i)) y| ≤ M)
    (hdxy : ∀ b σ i, i ∈ I →
      |deriv (fun z => deriv (fun r =>
        recordCellDensity (mixedLaw b k σ r z) (o i)) x) y| ≤ M) :
    DifferentiableAt ℝ (fun z => deriv (fun r => mixedComponentDifference k I o r z) x) y ∧
    |deriv (fun z => deriv (fun r => mixedComponentDifference k I o r z) x) y| ≤
      2 * M^2 * (I.card : ℝ)^2 * 2^I.card := by
  classical
  let f := fun b σ i r z => recordCellDensity (mixedLaw b k σ r z) (o i)
  have hp (b : Bool) (σ : Fin (k+1) → Bool) :=
    mixture_product_mixed_derivative_bounds I (f b σ) x y M hM
      (hx.mono (fun z hz => hz b σ)) (hy b σ) (hxy b σ)
      (fun i _ => by
        have hv := mixedDensity_bounds b k σ x y hxsmall hysmall
          (o i).2.1 (o i).2.2 (o i).1
        change (1/2 : ℝ) ≤ f b σ i x y ∧ f b σ i x y ≤ 2 at hv
        rw [abs_of_nonneg (by linarith [hv.1])]
        exact hv.2)
      (hdx b σ) (hdy b σ) (hdxy b σ)
  have hprod : ∀ᶠ z in 𝓝 y, ∀ b σ,
      DifferentiableAt ℝ (fun r => ∏ i ∈ I, f b σ i r z) x := by
    filter_upwards [hx] with z hz b σ
    exact DifferentiableAt.fun_finsetProd (hz b σ)
  have h := mixture_average_mixed_derivative_bound
    (fun b σ r z => ∏ i ∈ I, f b σ i r z) x y
    (M^2 * (I.card : ℝ)^2 * 2^I.card) hprod
    (fun b σ => (hp b σ).1) (fun b σ => (hp b σ).2.2.2.2)
  simpa only [mixedComponentDifference, mul_assoc] using h

/-- [Product differentiation, sign averaging, axis cancellation, and rectangular
Taylor control assemble the mixed component Hellinger bound directly from
one-record analytic inputs. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hM,hx,hy,hxy,hdx,hdy,hdxy). -/
-- @node: mixed_component_hellinger_of_record_derivatives
lemma mixed_component_hellinger_of_record_derivatives {n : ℕ} (k : ℕ)
    (I : Finset (Fin n)) (o : Fin n → Record) (η ζ M : ℝ)
    (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (hM : 1 ≤ M)
    (hx : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ,
      ∀ᶠ z in 𝓝 y, ∀ b σ i, i ∈ I → DifferentiableAt ℝ
        (fun r => recordCellDensity (mixedLaw b k σ r z) (o i)) x)
    (hy : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ, ∀ b σ i, i ∈ I →
      DifferentiableAt ℝ (fun z => recordCellDensity (mixedLaw b k σ x z) (o i)) y)
    (hxy : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ, ∀ b σ i, i ∈ I →
      DifferentiableAt ℝ (fun z => deriv (fun r =>
        recordCellDensity (mixedLaw b k σ r z) (o i)) x) y)
    (hdx : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ, ∀ b σ i, i ∈ I →
      |deriv (fun r => recordCellDensity (mixedLaw b k σ r y) (o i)) x| ≤ M)
    (hdy : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ, ∀ b σ i, i ∈ I →
      |deriv (fun z => recordCellDensity (mixedLaw b k σ x z) (o i)) y| ≤ M)
    (hdxy : ∀ x ∈ Set.uIcc 0 η, ∀ y ∈ Set.uIcc 0 ζ, ∀ b σ i, i ∈ I →
      |deriv (fun z => deriv (fun r =>
        recordCellDensity (mixedLaw b k σ r z) (o i)) x) y| ≤ M) :
    (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw false k σ η ζ) (o i)) -
      Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (mixedLaw true k σ η ζ) (o i)))^2 ≤
      M^4 * (I.card : ℝ)^4 * 8^I.card * (η*ζ)^2 := by
  classical
  have hsmall (z a : ℝ) (hz : z ∈ Set.uIcc 0 a) (ha : |a| ≤ 1/100) :
      |z| ≤ 1/100 := by
    rw [Set.mem_uIcc] at hz
    rcases hz with hz | hz
    · rw [abs_of_nonneg hz.1]
      exact hz.2.trans ((le_abs_self a).trans ha)
    · rw [abs_of_nonpos hz.2]
      exact (neg_le_neg hz.1).trans ((neg_le_abs a).trans ha)
  have hp (x : ℝ) (hxx : x ∈ Set.uIcc 0 η) (y : ℝ) (hyy : y ∈ Set.uIcc 0 ζ) :=
    mixedComponentDifference_cross_derivative_bound k I o x y M
      (hsmall x η hxx hη) (hsmall y ζ hyy hζ) hM
      (hx x hxx y hyy) (hy x hxx y hyy) (hxy x hxx y hyy)
      (hdx x hxx y hyy) (hdy x hxx y hyy) (hdxy x hxx y hyy)
  apply mixed_component_hellinger_taylor_bound k I o η ζ M hη hζ
    ?_ (fun x hxx y hyy => (hp x hxx y hyy).1)
    (fun x hxx y hyy => (hp x hxx y hyy).2)
  intro x hxx
  unfold mixedComponentDifference
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub <;> apply DifferentiableAt.fun_sum <;> intro σ _
  · exact DifferentiableAt.fun_finsetProd
      ((hx x hxx ζ Set.right_mem_uIcc).self_of_nhds false σ)
  · exact DifferentiableAt.fun_finsetProd
      ((hx x hxx ζ Set.right_mem_uIcc).self_of_nhds true σ)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
