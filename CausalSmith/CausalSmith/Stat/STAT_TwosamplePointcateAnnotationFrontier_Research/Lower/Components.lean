module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.Hellinger
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.Likelihood
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Lower/Components

Two-channel point-CATE annotation frontier: Lower/Components
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


variable {d n m : ℕ}
/-- Given [the specified input x](hyp:x), [the specified input xp](hyp:xp), [max dist](goal) is the corresponding construction. -/
def maxDist (x xp : Cov d) : ℝ := Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin (d+1))).Nonempty)
  (fun i : Fin (d+1) => if hi : i.val < d then |x ⟨i.val,hi⟩-xp ⟨i.val,hi⟩| else 0)
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [the specified input i](hyp:i), [the specified input j](hyp:j), [record adj](goal) is the corresponding construction. -/
def recordAdj (h delta : ℝ) (x : Fin (n+m) → Cov d) (i j : Fin (n+m)) : Prop :=
  i ≠ j ∧ x i ∈ locCube d h ∧ x j ∈ locCube d h ∧ maxDist (x i) (x j) ≤ 2*delta
/-- Given [the specified input x](hyp:x), [the specified input xp](hyp:xp), [the max dist comm conclusion](goal) holds. -/
lemma maxDist_comm (x xp : Cov d) : maxDist x xp = maxDist xp x := by
  unfold maxDist
  congr 1
  funext i
  split_ifs <;> simp only [abs_sub_comm]

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [the record adj symmetric conclusion](goal) holds. -/
lemma recordAdj_symmetric (h delta : ℝ) (x : Fin (n+m) → Cov d) : Std.Symm (recordAdj h delta x) := by
  constructor
  intro i j hij
  rcases hij with ⟨hne, hi, hj, hdist⟩
  exact ⟨hne.symm, hj, hi, by simpa only [maxDist_comm (x j) (x i)] using hdist⟩
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [the record adj irreflexive conclusion](goal) holds. -/
lemma recordAdj_irreflexive (h delta : ℝ) (x : Fin (n+m) → Cov d) : Std.Irrefl (recordAdj h delta x) := by
  constructor
  intro i hii
  exact hii.1 rfl
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [record graph](goal) is the corresponding construction. -/
def recordGraph (h delta : ℝ) (x : Fin (n+m) → Cov d) : SimpleGraph (Fin (n+m)) where
  Adj := recordAdj h delta x
  symm := recordAdj_symmetric h delta x
  loopless := recordAdj_irreflexive h delta x
/-- For [bandwidth h](hyp:h), [proximity radius δ](hyp:delta), and [the covariate record x](hyp:x), [the connected components of the record graph form a finite type](goal). -/
instance (h delta : ℝ) (x : Fin (n+m) → Cov d) : Fintype (recordGraph h delta x).ConnectedComponent := Fintype.ofFinite _
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [the specified input c](hyp:c), [component vertices](goal) is the corresponding construction. -/
def componentVertices (h delta : ℝ) (x : Fin (n+m) → Cov d)
    (c : (recordGraph h delta x).ConnectedComponent) : Finset (Fin (n+m)) :=
  Finset.univ.filter (fun i => (recordGraph h delta x).connectedComponentMk i = c)
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input s](hyp:s), [component density](goal) is the corresponding construction. -/
def componentDensity (H : MarkedPriors d) (theta : Bool) (x : Fin (n+m) → Cov d)
    (V : Finset (Fin (n+m))) (s : RecordSpins n m) : ℝ :=
  ∑ sigma, H.weight theta sigma * ∏ i ∈ V, recordLikelihood (H.law theta sigma) x s i
/-- Explicit conditional factorization over the covariate proximity graph.  Given [the specified input H](hyp:H), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input n](hyp:n), [the specified input m](hyp:m), [conditional factorization](goal) is the corresponding construction. -/
def ConditionalFactorization (H : MarkedPriors d) (h delta : ℝ) (n m : ℕ) : Prop :=
  ∀ (x : Fin (n+m) → Cov d), (∀ i, x i ∈ cube d) → ∀ theta (s : RecordSpins n m),
    mixedDensity H theta x s =
      ∏ c : (recordGraph h delta x).ConnectedComponent,
        componentDensity H theta x (componentVertices h delta x c) s
/-- The uninformative components have identical full conditional laws, expressed in their fair-spin densities.  Given [the specified input H](hyp:H), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input n](hyp:n), [the specified input m](hyp:m), [uninformative components agree](goal) is the corresponding construction. -/
def UninformativeComponentsAgree (H : MarkedPriors d) (h delta : ℝ) (n m : ℕ) : Prop :=
  ∀ (x : Fin (n+m) → Cov d), (∀ i, x i ∈ cube d) →
    ∀ c : (recordGraph h delta x).ConnectedComponent,
      let V := componentVertices h delta x c
      ((∀ i ∈ V, n ≤ i.val) ∨ (V.card = 1 ∧ ∃ i ∈ V, i.val < n)) →
      ∀ s : RecordSpins n m, componentDensity H true x V s = componentDensity H false x V s
/-- Telescoping a product of bounded factors controls its perturbation by the
sum of the factor perturbations, including the empty product.  Given [the specified input V](hyp:V), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input M](hyp:M), [the specified input hM](hyp:hM), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the finite product perturbation bound conclusion](goal) holds. -/
lemma finite_product_perturbation_bound {ι : Type*} (V : Finset ι)
    (f g : ι → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hf : ∀ i ∈ V, |f i| ≤ M) (hg : ∀ i ∈ V, |g i| ≤ M) :
    |(∏ i ∈ V, f i) - ∏ i ∈ V, g i| ≤
      M^V.card * ∑ i ∈ V, |f i - g i| := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert i V hi ih =>
    have hfV := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hgV := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hprod : |∏ j ∈ V, g j| ≤ M^V.card := by
      rw [Finset.abs_prod]
      calc
        (∏ j ∈ V, |g j|) ≤ ∏ _j ∈ V, M :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) hgV
        _ = M^V.card := by rw [Finset.prod_const]
    have hsum : 0 ≤ ∑ j ∈ V, |f j - g j| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Finset.sum_insert hi, pow_succ]
    calc
      |f i * (∏ j ∈ V, f j) - g i * ∏ j ∈ V, g j| =
          |f i * ((∏ j ∈ V, f j) - ∏ j ∈ V, g j) +
            (f i - g i) * ∏ j ∈ V, g j| := by congr 1; ring
      _ ≤ |f i| * |(∏ j ∈ V, f j) - ∏ j ∈ V, g j| +
          |f i - g i| * |∏ j ∈ V, g j| := by
        simpa only [abs_mul] using abs_add_le
          (f i * ((∏ j ∈ V, f j) - ∏ j ∈ V, g j))
          ((f i - g i) * ∏ j ∈ V, g j)
      _ ≤ M * (M^V.card * ∑ j ∈ V, |f j - g j|) +
          |f i - g i| * M^V.card := by
        gcongr
        · exact hf i (Finset.mem_insert_self i V)
        · exact ih hfV hgV
      _ ≤ M * (M^V.card * ∑ j ∈ V, |f j - g j|) +
          |f i - g i| * (M^V.card * M) := by
        gcongr
        exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) hM
      _ = M^V.card * M * (|f i - g i| + ∑ j ∈ V, |f j - g j|) := by ring

/-- A product of small perturbations of one keeps the amplitude as a factor.  Given [the specified input V](hyp:V), [the specified input f](hyp:f), [the specified input M](hyp:M), [the specified input D](hyp:D), [the specified input hM](hyp:hM), [the specified input hf](hyp:hf), [the specified input hD](hyp:hD), [the finite product deviation bound conclusion](goal) holds. -/
lemma finite_product_deviation_bound {ι : Type*} (V : Finset ι)
    (f : ι → ℝ) (M D : ℝ) (hM : 1 ≤ M)
    (hf : ∀ i ∈ V, |f i| ≤ M) (hD : ∀ i ∈ V, |f i - 1| ≤ D) :
    |(∏ i ∈ V, f i) - 1| ≤ (V.card : ℝ) * D * M^V.card := by
  have hp := finite_product_perturbation_bound V f (fun _ => 1) M hM hf
    (fun _ _ => by simpa only [abs_one] using hM)
  simp only [Finset.prod_const_one] at hp
  calc
    _ ≤ M^V.card * ∑ i ∈ V, |f i - 1| := hp
    _ ≤ M^V.card * ∑ _i ∈ V, D := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hD) (pow_nonneg (by linarith) _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Averaging over a finite probability prior preserves a uniform absolute bound.  Given [the specified input S](hyp:S), [the specified input w](hyp:w), [the specified input F](hyp:F), [the specified input hw](hyp:hw), [the specified input hmass](hyp:hmass), [the specified input D](hyp:D), [the specified input hF](hyp:hF), [the finite prior absolute bound conclusion](goal) holds. -/
lemma finite_prior_absolute_bound {S : Type*} [Fintype S]
    (w F : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hmass : ∑ s, w s = 1)
    (D : ℝ) (hF : ∀ s, |F s| ≤ D) : |∑ s, w s * F s| ≤ D := by
  calc
    _ ≤ ∑ s, |w s * F s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, w s * |F s| := by
      apply Finset.sum_congr rfl
      intro s _
      rw [abs_mul, abs_of_nonneg (hw s)]
    _ ≤ ∑ s, w s * D := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hF s) (hw s))
    _ = D := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Equal one-channel marginals cancel, leaving only the product of the two
centered channel factors in the difference between mixture expectations (MC27).  Given [the specified input S](hyp:S), [the specified input wplus](hyp:wplus), [the specified input wminus](hyp:wminus), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hp](hyp:hp), [the specified input hm](hyp:hm), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the finite prior common marginals cancel conclusion](goal) holds. -/
lemma finite_prior_common_marginals_cancel {S : Type*} [Fintype S]
    (wplus wminus A B : S → ℝ)
    (hp : ∑ s, wplus s = 1) (hm : ∑ s, wminus s = 1)
    (hA : ∑ s, wplus s * A s = ∑ s, wminus s * A s)
    (hB : ∑ s, wplus s * B s = ∑ s, wminus s * B s) :
    (∑ s, wplus s * (A s * B s)) - (∑ s, wminus s * (A s * B s)) =
      (∑ s, wplus s * ((A s - 1) * (B s - 1))) -
        (∑ s, wminus s * ((A s - 1) * (B s - 1))) := by
  have hexpand (w : S → ℝ) :
      (∑ s, w s * ((A s - 1) * (B s - 1))) =
        (∑ s, w s * (A s * B s)) - (∑ s, w s * A s) -
          (∑ s, w s * B s) + ∑ s, w s := by
    simp_rw [show ∀ s, w s * ((A s - 1) * (B s - 1)) =
      w s * (A s * B s) - w s * A s - w s * B s + w s by intro s; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hexpand, hexpand, hp, hm, hA, hB]
  ring

/-- The difference of two finite mixture expectations retains both channel
amplitudes when their separate marginals agree (MC27--MC28).  Given [the specified input S](hyp:S), [the specified input wplus](hyp:wplus), [the specified input wminus](hyp:wminus), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hwp](hyp:hwp), [the specified input hwm](hyp:hwm), [the specified input hp](hyp:hp), [the specified input hm](hyp:hm), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input UA](hyp:UA), [the specified input UB](hyp:UB), [the specified input hUA](hyp:hUA), [the specified input hUB](hyp:hUB), [the specified input hAb](hyp:hAb), [the specified input hBb](hyp:hBb), [the finite prior two channel bound conclusion](goal) holds. -/
lemma finite_prior_two_channel_bound {S : Type*} [Fintype S]
    (wplus wminus A B : S → ℝ)
    (hwp : ∀ s, 0 ≤ wplus s) (hwm : ∀ s, 0 ≤ wminus s)
    (hp : ∑ s, wplus s = 1) (hm : ∑ s, wminus s = 1)
    (hA : ∑ s, wplus s * A s = ∑ s, wminus s * A s)
    (hB : ∑ s, wplus s * B s = ∑ s, wminus s * B s)
    (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hAb : ∀ s, |A s - 1| ≤ UA) (hBb : ∀ s, |B s - 1| ≤ UB) :
    |(∑ s, wplus s * (A s * B s)) - (∑ s, wminus s * (A s * B s))| ≤
      2 * UA * UB := by
  rw [finite_prior_common_marginals_cancel wplus wminus A B hp hm hA hB]
  have hcenter (s : S) : |(A s - 1) * (B s - 1)| ≤ UA * UB := by
    rw [abs_mul]
    exact mul_le_mul (hAb s) (hBb s) (abs_nonneg _) hUA
  have hplus := finite_prior_absolute_bound wplus _ hwp hp (UA * UB) hcenter
  have hminus := finite_prior_absolute_bound wminus _ hwm hm (UA * UB) hcenter
  exact (abs_sub _ _).trans (by linarith)

/-- Two product channels with common marginal expectations retain the product
of their factor amplitudes, rather than either amplitude alone.  Given [the specified input S](hyp:S), [the specified input V](hyp:V), [the specified input W](hyp:W), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input wplus](hyp:wplus), [the specified input wminus](hyp:wminus), [the specified input hwp](hyp:hwp), [the specified input hwm](hyp:hwm), [the specified input hp](hyp:hp), [the specified input hm](hyp:hm), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input M](hyp:M), [the specified input DA](hyp:DA), [the specified input DB](hyp:DB), [the specified input hM](hyp:hM), [the specified input hDA](hyp:hDA), [the specified input hDB](hyp:hDB), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hfd](hyp:hfd), [the specified input hgd](hyp:hgd), [the finite prior product channel bound conclusion](goal) holds. -/
lemma finite_prior_product_channel_bound {S ι κ : Type*} [Fintype S]
    (V : Finset ι) (W : Finset κ) (f : S → ι → ℝ) (g : S → κ → ℝ)
    (wplus wminus : S → ℝ)
    (hwp : ∀ s, 0 ≤ wplus s) (hwm : ∀ s, 0 ≤ wminus s)
    (hp : ∑ s, wplus s = 1) (hm : ∑ s, wminus s = 1)
    (hA : ∑ s, wplus s * (∏ i ∈ V, f s i) = ∑ s, wminus s * (∏ i ∈ V, f s i))
    (hB : ∑ s, wplus s * (∏ i ∈ W, g s i) = ∑ s, wminus s * (∏ i ∈ W, g s i))
    (M DA DB : ℝ) (hM : 1 ≤ M) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hf : ∀ s i, i ∈ V → |f s i| ≤ M) (hg : ∀ s i, i ∈ W → |g s i| ≤ M)
    (hfd : ∀ s i, i ∈ V → |f s i - 1| ≤ DA)
    (hgd : ∀ s i, i ∈ W → |g s i - 1| ≤ DB) :
    |(∑ s, wplus s * ((∏ i ∈ V, f s i) * ∏ i ∈ W, g s i)) -
      (∑ s, wminus s * ((∏ i ∈ V, f s i) * ∏ i ∈ W, g s i))| ≤
      2 * ((V.card : ℝ) * DA * M^V.card) * ((W.card : ℝ) * DB * M^W.card) := by
  apply finite_prior_two_channel_bound wplus wminus _ _ hwp hwm hp hm hA hB
  · positivity
  · positivity
  · intro s
    exact finite_product_deviation_bound V (f s) M DA hM (hf s) (hfd s)
  · intro s
    exact finite_product_deviation_bound W (g s) M DB hM (hg s) (hgd s)

/-- Adding the two contrast-deletion errors to the centered channel bound
assembles the finite-mixture information estimate of MC26--MC29.  Given [the specified input S](hyp:S), [the specified input wplus](hyp:wplus), [the specified input wminus](hyp:wminus), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input Fplus](hyp:Fplus), [the specified input Fminus](hyp:Fminus), [the specified input hwp](hyp:hwp), [the specified input hwm](hyp:hwm), [the specified input hp](hyp:hp), [the specified input hm](hyp:hm), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input UA](hyp:UA), [the specified input UB](hyp:UB), [the specified input Dplus](hyp:Dplus), [the specified input Dminus](hyp:Dminus), [the specified input hUA](hyp:hUA), [the specified input hUB](hyp:hUB), [the specified input hAb](hyp:hAb), [the specified input hBb](hyp:hBb), [the specified input hdelp](hyp:hdelp), [the specified input hdelm](hyp:hdelm), [the finite prior contrast deletion bound conclusion](goal) holds. -/
lemma finite_prior_contrast_deletion_bound {S : Type*} [Fintype S]
    (wplus wminus A B Fplus Fminus : S → ℝ)
    (hwp : ∀ s, 0 ≤ wplus s) (hwm : ∀ s, 0 ≤ wminus s)
    (hp : ∑ s, wplus s = 1) (hm : ∑ s, wminus s = 1)
    (hA : ∑ s, wplus s * A s = ∑ s, wminus s * A s)
    (hB : ∑ s, wplus s * B s = ∑ s, wminus s * B s)
    (UA UB Dplus Dminus : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hAb : ∀ s, |A s - 1| ≤ UA) (hBb : ∀ s, |B s - 1| ≤ UB)
    (hdelp : ∀ s, |Fplus s - A s * B s| ≤ Dplus)
    (hdelm : ∀ s, |Fminus s - A s * B s| ≤ Dminus) :
    |(∑ s, wplus s * Fplus s) - (∑ s, wminus s * Fminus s)| ≤
      Dplus + 2 * UA * UB + Dminus := by
  have hdel (w F : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hmass : ∑ s, w s = 1)
      (D : ℝ) (hF : ∀ s, |F s - A s * B s| ≤ D) :
      |(∑ s, w s * F s) - (∑ s, w s * (A s * B s))| ≤ D := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    exact finite_prior_absolute_bound w _ hw hmass D hF
  have hdplus := hdel wplus Fplus hwp hp Dplus hdelp
  have hdminus := hdel wminus Fminus hwm hm Dminus hdelm
  have hchannel := finite_prior_two_channel_bound wplus wminus A B hwp hwm hp hm
    hA hB UA UB hUA hUB hAb hBb
  have htriangle := abs_sub_le (∑ s, wplus s * Fplus s)
    (∑ s, wplus s * (A s * B s)) (∑ s, wminus s * Fminus s)
  have htriangle' := abs_sub_le (∑ s, wplus s * (A s * B s))
    (∑ s, wminus s * (A s * B s)) (∑ s, wminus s * Fminus s)
  rw [abs_sub_comm (∑ s, wminus s * (A s * B s))] at htriangle'
  linarith

/-- Regrouping independent sign coordinates by their owner factors a finite weighted sum.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input w](hyp:w), [the specified input G](hyp:G), [the finite fiber weighted sum conclusion](goal) holds. -/
lemma finite_fiber_weighted_sum {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]
    (owner : ι → κ) (w : ι → S → ℝ)
    (G : ∀ c, ({z // owner z = c} → S) → ℝ) :
    (∑ sigma : ι → S, (∏ z, w z (sigma z)) *
      ∏ c, G c (fun z => sigma z.1)) =
    ∏ c, ∑ s : {z // owner z = c} → S, (∏ z, w z.1 (s z)) * G c s := by
  let e : (ι → S) ≃ (∀ c, {z // owner z = c} → S) :=
    Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
  calc
    _ = ∑ s : ∀ c, {z // owner z = c} → S,
        ∏ c, (∏ z : {z // owner z = c}, w z.1 (s c z)) * G c (s c) := by
      apply Fintype.sum_equiv e
      intro sigma
      simp only [e, Equiv.piCongrFiberwise_apply, Equiv.refl_apply,
        Finset.prod_mul_distrib]
      rw [Fintype.prod_fiberwise owner (fun z => w z (sigma z))]
    _ = _ := (Fintype.prod_sum (fun c (s : {z // owner z = c} → S) =>
      (∏ z, w z.1 (s z)) * G c s)).symm

/-- Expectations of functions depending on separate coordinate blocks multiply under a normalized product prior.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input w](hyp:w), [the specified input hw](hyp:hw), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the finite fiber expectation factorization conclusion](goal) holds. -/
lemma finite_fiber_expectation_factorization {ι κ S : Type*}
    [Fintype ι] [Fintype κ] [Fintype S] [Nonempty S]
    (owner : ι → κ) (w : ι → S → ℝ) (hw : ∀ z, ∑ s, w z s = 1)
    (F : κ → (ι → S) → ℝ)
    (hF : ∀ c sigma sigma', (∀ z, owner z = c → sigma z = sigma' z) →
      F c sigma = F c sigma') :
    (∑ sigma : ι → S, (∏ z, w z (sigma z)) * ∏ c, F c sigma) =
    ∏ c, ∑ sigma : ι → S, (∏ z, w z (sigma z)) * F c sigma := by
  let lift (c : κ) (s : {z // owner z = c} → S) (z : ι) : S :=
    if hz : owner z = c then s ⟨z, hz⟩ else Classical.choice ‹Nonempty S›
  let G (c : κ) (s : {z // owner z = c} → S) : ℝ := F c (lift c s)
  have hG (c : κ) (sigma : ι → S) : F c sigma = G c (fun z => sigma z.1) := by
    apply hF
    intro z hz
    simp [lift, hz]
  have hmass (c : κ) : (∑ s : {z // owner z = c} → S,
      ∏ z, w z.1 (s z)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hw]
  have hmarg (c : κ) : (∑ sigma : ι → S, (∏ z, w z (sigma z)) * F c sigma) =
      ∑ s : {z // owner z = c} → S, (∏ z, w z.1 (s z)) * G c s := by
    have ht := finite_fiber_weighted_sum owner w
      (fun j s => if hj : j = c then G c (hj ▸ s) else 1)
    have hprod (sigma : ι → S) :
        (∏ j, if hj : j = c then G c (hj ▸ (fun z => sigma z.1)) else 1) = F c sigma := by
      simp [← hG]
    simp_rw [hprod] at ht
    rw [ht]
    have hsum (j : κ) :
        (∑ s : {z // owner z = j} → S, (∏ z, w z.1 (s z)) *
          (if hj : j = c then G c (hj ▸ s) else 1)) =
        if hj : j = c then (∑ s : {z // owner z = c} → S,
          (∏ z, w z.1 (s z)) * G c s) else 1 := by
      by_cases hj : j = c
      · subst j; simp
      · simp [hj, hmass]
    simp_rw [hsum]
    simp
  simp_rw [hG] at ⊢
  rw [finite_fiber_weighted_sum]
  apply Finset.prod_congr rfl
  intro c _
  exact (hmarg c).symm.trans (by simp_rw [hG])


/-- A nonzero frame is supported inside the localization cube and one grid radius.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hh](hyp:hh), [the specified input z](hyp:z), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the frame nonzero support conclusion](goal) holds. -/
lemma frame_nonzero_support {d : ℕ} (h delta : ℝ) (hh : 0 < h)
    (z : Fin d → ℤ) (x : Cov d) (hx : frame h delta z x ≠ 0) :
    x ∈ locCube d h ∧ ∀ j, |(x j-1/2)/delta - (z j:ℝ)| < 1 := by
  constructor
  · by_contra hout
    exact hx (by simp [frame, macroBump_zero_outside h hh x hout])
  · intro j
    have hj : frame1d (z j) ((x j-1/2)/delta) ≠ 0 := by
      intro hz
      apply hx
      unfold frame
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
    rw [abs_lt]
    constructor
    · by_contra hn
      exact hj (frame1d_zero_left _ _ (by linarith))
    · by_contra hn
      exact hj (frame1d_zero_right _ _ (by linarith))

/-- Two records sharing an active frame belong to the same graph component.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hh](hyp:hh), [the specified input hd](hyp:hd), [the specified input x](hyp:x), [the specified input z](hyp:z), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the shared frame component conclusion](goal) holds. -/
lemma shared_frame_component {d n m : ℕ} (h delta : ℝ) (hh : 0 < h)
    (hd : 0 < delta) (x : Fin (n+m) → Cov d) (z : Fin d → ℤ)
    (i j : Fin (n+m)) (hi : frame h delta z (x i) ≠ 0)
    (hj : frame h delta z (x j) ≠ 0) :
    (recordGraph h delta x).connectedComponentMk i =
      (recordGraph h delta x).connectedComponentMk j := by
  by_cases hij : i = j
  · subst j; rfl
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  refine ⟨hij, (frame_nonzero_support h delta hh z (x i) hi).1,
    (frame_nonzero_support h delta hh z (x j) hj).1, ?_⟩
  unfold maxDist
  apply Finset.sup'_le
  intro k hk
  split_ifs with hk'
  · have hu := (frame_nonzero_support h delta hh z (x i) hi).2 ⟨k.val,hk'⟩
    have hv := (frame_nonzero_support h delta hh z (x j) hj).2 ⟨k.val,hk'⟩
    rw [abs_lt] at hu hv
    rw [abs_le]
    have h1 := (lt_div_iff₀ hd).mp (show (z ⟨k.val,hk'⟩:ℝ)-1 <
      (x i ⟨k.val,hk'⟩-1/2)/delta by linarith)
    have h2 := (div_lt_iff₀ hd).mp (show (x i ⟨k.val,hk'⟩-1/2)/delta <
      (z ⟨k.val,hk'⟩:ℝ)+1 by linarith)
    have h3 := (lt_div_iff₀ hd).mp (show (z ⟨k.val,hk'⟩:ℝ)-1 <
      (x j ⟨k.val,hk'⟩-1/2)/delta by linarith)
    have h4 := (div_lt_iff₀ hd).mp (show (x j ⟨k.val,hk'⟩-1/2)/delta <
      (z ⟨k.val,hk'⟩:ℝ)+1 by linarith)
    constructor <;> linarith
  · linarith

/-- At a record, only the sign pairs of its nonzero frames affect the likelihood.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input s](hyp:s), [the specified input i](hyp:i), [the specified input sigma](hyp:sigma), [the specified input sigma'](hyp:sigma'), [the specified input hs](hyp:hs), [the record likelihood active signs conclusion](goal) holds. -/
lemma recordLikelihood_active_signs {d n m : ℕ} (h delta a b : ℝ) (theta : Bool)
    (x : Fin (n+m) → Cov d) (s : RecordSpins n m) (i : Fin (n+m))
    (sigma sigma' : SignArray d h delta)
    (hs : ∀ z, frame h delta z.1 (x i) ≠ 0 → sigma z = sigma' z) :
    recordLikelihood (markedLaw h delta a b theta sigma) x s i =
      recordLikelihood (markedLaw h delta a b theta sigma') x s i := by
  have hf (control : Bool) : signField h delta sigma control (x i) =
      signField h delta sigma' control (x i) := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hn : frame h delta z.1 (x i) = 0
    · simp only [hn, mul_zero]
    · rw [hs z hn]
  have he : (markedLaw h delta a b theta sigma).e (x i) =
      (markedLaw h delta a b theta sigma').e (x i) := by
    change probabilityClip (1/2+a*signField h delta sigma false (x i)) = _
    rw [hf false]
    rfl
  have hm (arm : Bool) :
      (if arm then (markedLaw h delta a b theta sigma).mu1 (x i)
        else (markedLaw h delta a b theta sigma).mu0 (x i)) =
      (if arm then (markedLaw h delta a b theta sigma').mu1 (x i)
        else (markedLaw h delta a b theta sigma').mu0 (x i)) := by
    cases arm <;> change probabilityClip (1/2+b*signField h delta sigma true (x i)+_) = _ <;>
      rw [hf true] <;> rfl
  induction i using Fin.addCases with
  | left i => simp only [recordLikelihood, Fin.addCases_left, labelLikelihood, he, hm]
  | right i => simp only [recordLikelihood, Fin.addCases_right, auxiliaryLikelihood, he]

/-- Disjoint active frame blocks factor the conditional likelihood across graph components.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input hh](hyp:hh), [the specified input n](hyp:n), [the specified input m](hyp:m), [the marked conditional factorization conclusion](goal) holds. -/
lemma marked_conditional_factorization (d : ℕ) (h delta a b : ℝ)
    (hd : 0 < delta) (hdh : delta ≤ h) (hh : h ≤ 1/2) (n m : ℕ) :
    ConditionalFactorization (markedHandle d h delta a b) h delta n m := by
  intro x hx theta s
  let comp := (recordGraph h delta x).connectedComponentMk
  let owner (z : {z // z ∈ frameIdx d h delta}) :
      Option (recordGraph h delta x).ConnectedComponent :=
    if hz : ∃ i, frame h delta z.1 (x i) ≠ 0 then some (comp hz.choose) else none
  let F : Option (recordGraph h delta x).ConnectedComponent → SignArray d h delta → ℝ :=
    fun c sigma => match c with
      | none => 1
      | some c => ∏ i ∈ componentVertices h delta x c,
          recordLikelihood (markedLaw h delta a b theta sigma) x s i
  have howner (z : {z // z ∈ frameIdx d h delta}) (i : Fin (n+m))
      (hi : frame h delta z.1 (x i) ≠ 0) : owner z = some (comp i) := by
    have hz : ∃ j, frame h delta z.1 (x j) ≠ 0 := ⟨i,hi⟩
    simp only [owner, dif_pos hz]
    congr 1
    exact shared_frame_component h delta (hd.trans_le hdh) hd x z.1 _ i hz.choose_spec hi
  have hF : ∀ c sigma sigma', (∀ z, owner z = c → sigma z = sigma' z) →
      F c sigma = F c sigma' := by
    intro c sigma sigma' hs
    cases c with
    | none => rfl
    | some c =>
      apply Finset.prod_congr rfl
      intro i hi
      apply recordLikelihood_active_signs
      intro z hz
      apply hs z
      have hc : comp i = c := (Finset.mem_filter.mp hi).2
      rw [howner z i hz, hc]
  have hw (z : {z // z ∈ frameIdx d h delta}) :
      (∑ v : Bool × Bool, (1+thetaSign theta*thetaSign v.1*thetaSign v.2/2)/4) = 1 := by
    cases theta <;> norm_num [Fintype.sum_prod_type, thetaSign]
  have hfactor := finite_fiber_expectation_factorization owner
    (fun _ v => (1+thetaSign theta*thetaSign v.1*thetaSign v.2/2)/4) hw F hF
  have hprod (sigma : SignArray d h delta) :
      (∏ c, F c sigma) = ∏ i, recordLikelihood (markedLaw h delta a b theta sigma) x s i := by
    simp only [F, Fintype.prod_option, one_mul]
    have ht := Fintype.prod_fiberwise comp
      (fun i => recordLikelihood (markedLaw h delta a b theta sigma) x s i)
    convert ht using 1
    apply Finset.prod_congr rfl
    intro c hc
    exact Finset.prod_subtype (p := fun i => comp i = c) (componentVertices h delta x c)
      (by intro i; simp [componentVertices, comp])
      (fun i => recordLikelihood (markedLaw h delta a b theta sigma) x s i)
  simp_rw [hprod] at hfactor
  change mixedDensity (markedHandle d h delta a b) theta x s = _
  change (∑ sigma, markedWeight h delta theta sigma *
    ∏ i, recordLikelihood (markedLaw h delta a b theta sigma) x s i) = _
  trans ∏ c, ∑ sigma : SignArray d h delta, markedWeight h delta theta sigma * F c sigma
  · dsimp only [markedWeight]
    with_reducible
      convert hfactor using 2
      · ext; simp
      · apply Finset.sum_congr (by ext; simp)
        intro sigma _
        rfl
  · rw [Fintype.prod_option]
    change (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma * 1) *
      (∏ c, ∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
        ∏ i ∈ componentVertices h delta x c,
          recordLikelihood (markedLaw h delta a b theta sigma) x s i) = _
    simp only [mul_one, (marked_prior_mass d h delta theta).2, one_mul]
    rfl

/-- An auxiliary likelihood ignores the flipped outcome signs and hypothesis index.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input sigma](hyp:sigma), [the specified input x](hyp:x), [the specified input s](hyp:s), [the specified input i](hyp:i), [the specified input hi](hyp:hi), [the auxiliary record likelihood flip conclusion](goal) holds. -/
lemma auxiliary_recordLikelihood_flip {d n m : ℕ} (h delta a b : ℝ)
    (sigma : SignArray d h delta) (x : Fin (n+m) → Cov d) (s : RecordSpins n m)
    (i : Fin (n+m)) (hi : n ≤ i.val) :
    recordLikelihood (markedLaw h delta a b true sigma) x s i =
      recordLikelihood (markedLaw h delta a b false (flipOutcomeSigns d h delta sigma)) x s i := by
  induction i using Fin.addCases with
  | left i => simp only [Fin.val_castAdd] at hi; omega
  | right i =>
    simp only [recordLikelihood, Fin.addCases_right, auxiliaryLikelihood,
      markedPropensity_flipOutcomeSigns]

/-- A component containing only auxiliary records has the same density under both sign priors.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input hV](hyp:hV), [the specified input s](hyp:s), [the auxiliary component density equality conclusion](goal) holds. -/
lemma auxiliary_componentDensity_equality {d n m : ℕ} (h delta a b : ℝ)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m)))
    (hV : ∀ i ∈ V, n ≤ i.val) (s : RecordSpins n m) :
    componentDensity (markedHandle d h delta a b) true x V s =
      componentDensity (markedHandle d h delta a b) false x V s := by
  unfold componentDensity
  apply Fintype.sum_equiv (flipOutcomeSigns d h delta)
  intro sigma
  change markedWeight h delta true sigma * _ =
    markedWeight h delta false (flipOutcomeSigns d h delta sigma) * _
  rw [markedWeight_flipOutcomeSigns]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact auxiliary_recordLikelihood_flip h delta a b sigma x s i (hV i hi)

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the uninformative component equality conclusion](goal) holds. -/
lemma uninformative_component_equality (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(positive claim-local constant)
       c ≤ 1 ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma → ∀ n m,
      UninformativeComponentsAgree (markedHandle d h delta a b) h delta n m := by
  obtain ⟨c, hc, hc1, hsingle⟩ := singleton_cancellation d alpha beta gamma L eps hdom
  refine ⟨c, hc, hc1, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab n m
  unfold UninformativeComponentsAgree
  intro x hx comp
  dsimp only
  intro hV s
  rcases hV with haux | ⟨hcard, i, hi, hilab⟩
  · exact auxiliary_componentDensity_equality h delta a b x _ haux s
  · have hset : componentVertices h delta x comp = {i} :=
      by
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
        have hij : i = j := by simpa only [hj, Finset.mem_singleton] using hi
        simpa only [hij] using hj
    simp only [componentDensity, hset, Finset.prod_singleton]
    have hcancel := hsingle h delta a b hd hdh hh ha hac hb hbc hab
    induction i using Fin.addCases with
    | left i =>
      simp only [recordLikelihood, Fin.addCases_left]
      have ht := singletonMixture_density (markedHandle d h delta a b) true
        (marked_prior_mass d h delta true).1 (x (Fin.castAdd m i)) (s.1 i)
      have hf := singletonMixture_density (markedHandle d h delta a b) false
        (marked_prior_mass d h delta false).1 (x (Fin.castAdd m i)) (s.1 i)
      rw [hcancel true] at ht
      rw [hcancel false] at hf
      exact ht.symm.trans hf
    | right i => simp only [Fin.val_natAdd] at hilab; omega

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
