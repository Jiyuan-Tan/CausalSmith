module
public import Causalean.Mathlib.Probability.ProductAbsolutelyContinuous
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.Mixture
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Iid second moments of uniform finite mixtures

This module proves the Radon--Nikodym density formula for finite iid product
laws, expands uniform finite-mixture chi-squared second moments into pairwise
overlaps, and identifies iid overlaps as powers of their one-sample versions.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Mixture

open MeasureTheory
open scoped BigOperators ENNReal

/-- Given [two probability laws on a measurable sample space](hyp:P,Q), [the
second law is dominated by the first](hyp:hQ), and [a sample size](hyp:n), [the
Radon--Nikodym density of the iid product law is almost everywhere the product
of the one-observation densities](goal). -/
theorem iidRnDeriv_eq_prod {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q ≪ P) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => Q)).rnDeriv
      (Measure.pi (fun _ : Fin n => P)) =ᵐ[Measure.pi (fun _ : Fin n => P)]
      (fun x => ∏ i : Fin n, Q.rnDeriv P (x i)) := by
  induction n with
  | zero =>
      have heq : Measure.pi (fun _ : Fin 0 => Q) =
          Measure.pi (fun _ : Fin 0 => P) := by
        rw [Measure.pi_of_empty, Measure.pi_of_empty]
      rw [heq]
      simpa using (Measure.rnDeriv_self (Measure.pi (fun _ : Fin 0 => P)))
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
      have hQmap := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) 0
      have hPmap := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
      have htail : Measure.pi (fun _ : Fin n => Q) ≪
          Measure.pi (fun _ : Fin n => P) :=
        Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
          Q P hQ n
      have hb := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
        Q P (Measure.pi (fun _ : Fin n => Q)) (Measure.pi (fun _ : Fin n => P)) hQ htail
      have hitail := (Measure.quasiMeasurePreserving_snd
        (μ := P) (ν := Measure.pi (fun _ : Fin n => P))).ae_eq_comp ih
      have hprod : (Q.prod (Measure.pi (fun _ : Fin n => Q))).rnDeriv
          (P.prod (Measure.pi (fun _ : Fin n => P))) =ᵐ[
            P.prod (Measure.pi (fun _ : Fin n => P))]
          fun z => Q.rnDeriv P z.1 * ∏ i, Q.rnDeriv P (z.2 i) := by
        filter_upwards [hb, hitail] with z hz ht
        simp only [Function.comp_apply] at ht
        rw [hz, ht]
      have hpull := hPmap.quasiMeasurePreserving.ae_eq_comp hprod
      have hmap := e.measurableEmbedding.rnDeriv_map
        (Measure.pi (fun _ : Fin (n + 1) => Q))
        (Measure.pi (fun _ : Fin (n + 1) => P))
      filter_upwards [hmap, hpull] with x hm hp
      simp only [Function.comp_apply] at hp
      rw [← hm, hQmap.map_eq, hPmap.map_eq, hp, Fin.prod_univ_succ]
      congr 1

/-- Given [two probability laws on a measurable sample space](hyp:P,Q), [the
second law is dominated by the first](hyp:hQ), and [a sample size](hyp:n), [the
real-valued Radon--Nikodym density of the iid product law is almost everywhere
the product of the real-valued one-observation densities](goal). -/
theorem iidRnDeriv_toReal_eq_prod {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q ≪ P) (n : ℕ) :
    (fun x => ((Measure.pi (fun _ : Fin n => Q)).rnDeriv
      (Measure.pi (fun _ : Fin n => P)) x).toReal) =ᵐ[
        Measure.pi (fun _ : Fin n => P)]
      (fun x => ∏ i : Fin n, (Q.rnDeriv P (x i)).toReal) := by
  filter_upwards [iidRnDeriv_eq_prod P Q hQ n] with x hx
  simpa only [hx, ENNReal.toReal_prod]

/-- Given [a finite nonempty family of measures](hyp:Q), [the uniform finite
mixture](goal) assigns equal mass to every component. -/
noncomputable def uniformMixture {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) : Measure Ω :=
  Causalean.Stat.mixture (fun _ => (Fintype.card S : ℝ≥0∞)⁻¹) Q

/-- Given [a finite nonempty family of probability measures](hyp:Q), [its
uniform mixture is a probability measure](goal). -/
theorem uniformMixture_isProbability {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω)
    [∀ s, IsProbabilityMeasure (Q s)] :
    IsProbabilityMeasure (uniformMixture Q) := by
  apply Causalean.Stat.mixture_isProbabilityMeasure
  have hc : (Fintype.card S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel hc (by simp)

/-- Given [a finite nonempty family of measures](hyp:Q), [a reference
measure](hyp:P), and [componentwise domination by that reference](hyp:hac),
[the uniform mixture is also dominated by the reference measure](goal). -/
theorem uniformMixture_absolutelyContinuous {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    (hac : ∀ s, Q s ≪ P) : uniformMixture Q ≪ P := by
  unfold uniformMixture Causalean.Stat.mixture
  have h (t : Finset S) : t.sum (fun s => (Fintype.card S : ℝ≥0∞)⁻¹ • Q s) ≪ P := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert s t hs ih =>
        simpa [Finset.sum_insert hs] using
          Measure.AbsolutelyContinuous.add_left
            ((hac s).smul_left ((Fintype.card S : ℝ≥0∞)⁻¹)) ih
  exact h Finset.univ

/-- Given [a finite nonempty family of probability laws](hyp:Q) and [a reference
probability law](hyp:P), [the
real-valued density of the uniform mixture is almost everywhere the average of
the component densities](goal). -/
theorem uniformMixture_rnDeriv {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)] :
    (fun x => ((uniformMixture Q).rnDeriv P x).toReal) =ᵐ[P]
      (fun x => (∑ s, ((Q s).rnDeriv P x).toReal) / (Fintype.card S : ℝ)) := by
  classical
  let w : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞)⁻¹
  have hw : w ≠ ⊤ := by simp [w]
  haveI (s : S) : IsFiniteMeasure (w • Q s) := (Q s).smul_finite hw
  have hrn (t : Finset S) :
      (t.sum (fun s => w • Q s)).rnDeriv P =ᵐ[P]
        fun x => t.sum (fun s => w * (Q s).rnDeriv P x) := by
    induction t using Finset.induction_on with
    | empty =>
        filter_upwards [Measure.rnDeriv_zero P] with x hx
        simpa using hx
    | @insert s t hs ih =>
        haveI : IsFiniteMeasure (t.sum (fun s => w • Q s)) := inferInstance
        have hadd := Measure.rnDeriv_add (w • Q s)
          (t.sum (fun s => w • Q s)) P
        have hsmul := Measure.rnDeriv_smul_left_of_ne_top (Q s) P hw
        filter_upwards [hadd, hsmul, ih] with x hx ha hb
        simpa [Finset.sum_insert hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb]
          using hx
  have hfinite : ∀ᵐ x ∂P, ∀ s : S, (Q s).rnDeriv P x ≠ ⊤ := by
    rw [Filter.eventually_all]
    intro s
    exact (Measure.rnDeriv_lt_top (Q s) P).mono (fun x hx => ne_of_lt hx)
  filter_upwards [hrn Finset.univ, hfinite] with x hx hfx
  change ((Finset.univ.sum (fun s => w • Q s)).rnDeriv P x).toReal =
    (∑ s, ((Q s).rnDeriv P x).toReal) / (Fintype.card S : ℝ)
  rw [hx, ENNReal.toReal_sum (fun s _ => ENNReal.mul_ne_top hw (hfx s))]
  simp_rw [ENNReal.toReal_mul]
  simp [w, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    div_eq_mul_inv, Finset.mul_sum, mul_comm]

/-- Given [a finite nonempty family of probability laws](hyp:Q), [a reference
probability law](hyp:P), [componentwise domination](hyp:hac), and [integrable
pairwise density products](hyp:hpair), [one plus the chi-squared divergence of
the uniform mixture is the average of all pairwise Radon--Nikodym overlaps](goal). -/
theorem one_add_chiSqDiv_uniformMixture {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) P) :
    1 + Causalean.Stat.chiSqDiv (uniformMixture Q) P =
      (∑ s : S, ∑ t : S,
        ∫ x, ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal ∂P) /
        (Fintype.card S : ℝ) ^ 2 := by
  classical
  haveI : IsProbabilityMeasure (uniformMixture Q) := uniformMixture_isProbability Q
  let d (s : S) (x : Ω) : ℝ := ((Q s).rnDeriv P x).toReal
  let p (x : Ω) : ℝ := ((uniformMixture Q).rnDeriv P x).toReal
  let n : ℝ := Fintype.card S
  have hdouble : Integrable (fun x => ∑ s : S, ∑ t : S, d s x * d t x) P := by
    apply integrable_finsetSum Finset.univ
    intro s _
    apply integrable_finsetSum Finset.univ
    intro t _
    exact hpair s t
  have hpoint : ∀ᵐ x ∂P, p x ^ 2 =
      (∑ s : S, ∑ t : S, d s x * d t x) / n ^ 2 := by
    filter_upwards [uniformMixture_rnDeriv Q P] with x hx
    change p x = (∑ s : S, d s x) / n at hx
    rw [hx, div_pow, sq, Finset.sum_mul_sum]
  have hsq : Integrable (fun x => p x ^ 2) P := by
    exact (hdouble.div_const (n ^ 2)).congr (hpoint.mono fun x hx => hx.symm)
  have hp : Integrable p P := Measure.integrable_toReal_rnDeriv
  have hdev : Integrable (fun x => (p x - 1) ^ 2) P := by
    have heq : (fun x => (p x - 1) ^ 2) =
        (fun x => p x ^ 2 - 2 * p x + 1) := by
      funext x; ring
    rw [heq]
    exact (hsq.sub (hp.const_mul 2)).add (integrable_const 1)
  have hint : (∫ x, p x ^ 2 ∂P) =
      (∑ s : S, ∑ t : S, ∫ x, d s x * d t x ∂P) / n ^ 2 := by
    calc
      (∫ x, p x ^ 2 ∂P) =
          ∫ x, (∑ s : S, ∑ t : S, d s x * d t x) / n ^ 2 ∂P :=
        integral_congr_ae hpoint
      _ = (∫ x, ∑ s : S, ∑ t : S, d s x * d t x ∂P) / n ^ 2 :=
        integral_div _ _
      _ = (∑ s : S, ∑ t : S, ∫ x, d s x * d t x ∂P) / n ^ 2 := by
        rw [integral_finsetSum]
        · congr 1
          apply Finset.sum_congr rfl
          intro s _
          rw [integral_finsetSum]
          intro t _
          exact hpair s t
        · intro s _
          apply integrable_finsetSum Finset.univ
          intro t _
          exact hpair s t
  have hchi := Causalean.Stat.chiSqDiv_eq
    (uniformMixture_absolutelyContinuous Q P hac) hdev
  change Causalean.Stat.chiSqDiv (uniformMixture Q) P = (∫ x, p x ^ 2 ∂P) - 1 at hchi
  rw [hchi, hint]
  ring

/-- Given [a reference probability law and two dominated probability
laws](hyp:P,Q,R), [domination of the two laws](hyp:hQ,hR), [an integrable
one-observation density product](hyp:hint), and [a sample size](hyp:n), [the
product of their iid sample densities is integrable](goal). -/
theorem iidPairIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P Q R : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hQ : Q ≪ P) (hR : R ≪ P)
    (hint : Integrable (fun x => (Q.rnDeriv P x).toReal *
      (R.rnDeriv P x).toReal) P) (n : ℕ) :
    Integrable (fun x =>
      (((Measure.pi (fun _ : Fin n => Q)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal) *
      (((Measure.pi (fun _ : Fin n => R)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal))
      (Measure.pi (fun _ : Fin n => P)) := by
  have hprod : Integrable (fun x : Fin n → Ω =>
      ∏ i : Fin n, (Q.rnDeriv P (x i)).toReal *
        (R.rnDeriv P (x i)).toReal)
      (Measure.pi (fun _ : Fin n => P)) :=
    Integrable.fin_nat_prod (fun _ => hint)
  have heq : (fun x =>
      (((Measure.pi (fun _ : Fin n => Q)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal) *
      (((Measure.pi (fun _ : Fin n => R)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal)) =ᵐ[
          Measure.pi (fun _ : Fin n => P)]
      (fun x => ∏ i : Fin n,
        (Q.rnDeriv P (x i)).toReal * (R.rnDeriv P (x i)).toReal) := by
    filter_upwards [iidRnDeriv_toReal_eq_prod P Q hQ n,
      iidRnDeriv_toReal_eq_prod P R hR n] with x hqx hrx
    rw [hqx, hrx, ← Finset.prod_mul_distrib]
  exact hprod.congr heq.symm

/-- Given [a reference probability law and two dominated probability
laws](hyp:P,Q,R), [domination of the two laws](hyp:hQ,hR), and [a sample size](hyp:n), [the
overlap of their iid sample laws is the corresponding power of the
one-observation overlap](goal).

Integrability of the product of the two one-observation densities is not assumed: when it fails,
the one-observation overlap is zero by the convention that the integral of a non-integrable
function is zero, and for a positive sample size so is the overlap of the sample laws, although
the true overlap is infinite. -/
theorem iidPairOverlap {Ω : Type*} [MeasurableSpace Ω]
    (P Q R : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hQ : Q ≪ P) (hR : R ≪ P) (n : ℕ) :
    (∫ x,
      (((Measure.pi (fun _ : Fin n => Q)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal) *
      (((Measure.pi (fun _ : Fin n => R)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal)
        ∂(Measure.pi (fun _ : Fin n => P))) =
      (∫ x, (Q.rnDeriv P x).toReal * (R.rnDeriv P x).toReal ∂P) ^ n := by
  have heq : (fun x =>
      (((Measure.pi (fun _ : Fin n => Q)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal) *
      (((Measure.pi (fun _ : Fin n => R)).rnDeriv
        (Measure.pi (fun _ : Fin n => P)) x).toReal)) =ᵐ[
          Measure.pi (fun _ : Fin n => P)]
      (fun x => ∏ i : Fin n,
        (Q.rnDeriv P (x i)).toReal * (R.rnDeriv P (x i)).toReal) := by
    filter_upwards [iidRnDeriv_toReal_eq_prod P Q hQ n,
      iidRnDeriv_toReal_eq_prod P R hR n] with x hqx hrx
    rw [hqx, hrx, ← Finset.prod_mul_distrib]
  rw [integral_congr_ae heq]
  simpa using (integral_fintype_prod_eq_pow
    (ι := Fin n) (μ := P)
    (fun x => (Q.rnDeriv P x).toReal * (R.rnDeriv P x).toReal))

/-- Given [a finite nonempty family of probability laws](hyp:Q), [a reference
probability law](hyp:P), [componentwise domination](hyp:hac), [integrable
pairwise one-observation density products](hyp:hpair), and [a sample
size](hyp:n), [one plus the chi-squared divergence, from the iid product of the reference law, of
the uniform mixture of the components' iid product laws equals the average over all ordered pairs
of components of the one-observation overlap raised to the sample size, where the overlap of two
components is the reference-law integral of the product of their densities](goal). -/
theorem one_add_chiSqDiv_uniformMixture_iid {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) P)
    (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv
      (uniformMixture (fun s => Measure.pi (fun _ : Fin n => Q s)))
      (Measure.pi (fun _ : Fin n => P)) =
      (∑ s : S, ∑ t : S,
        (∫ x, ((Q s).rnDeriv P x).toReal *
          ((Q t).rnDeriv P x).toReal ∂P) ^ n) /
        (Fintype.card S : ℝ) ^ 2 := by
  classical
  haveI : ∀ s : S, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => Q s)) := by infer_instance
  have hpi : ∀ s : S, Measure.pi (fun _ : Fin n => Q s) ≪
      Measure.pi (fun _ : Fin n => P) := by
    intro s
    exact Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      (Q s) P (hac s) n
  have hbase := one_add_chiSqDiv_uniformMixture
    (fun s => Measure.pi (fun _ : Fin n => Q s))
    (Measure.pi (fun _ : Fin n => P)) hpi
    (fun s t => iidPairIntegrable P (Q s) (Q t) (hac s) (hac t) (hpair s t) n)
  rw [hbase]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact iidPairOverlap P (Q s) (Q t) (hac s) (hac t) n

end Causalean.Stat.Minimax.Mixture
namespace Causalean.Stat.Minimax.Mixture
open MeasureTheory
open scoped ENNReal
/-- Given [a measurable sample space](hyp:Ω), [a reference probability law](hyp:μ),
[an alternative probability law](hyp:Q), [a likelihood](hyp:L),
[its likelihood representation](hyp:hQ), and [a sample size](hyp:n),
[the iid alternative law is dominated by the iid reference law](goal). -/
theorem iid_absolutelyContinuous_of_likelihood {Ω : Type*} [MeasurableSpace Ω] (μ Q : Measure Ω) [IsProbabilityMeasure
    μ] [IsProbabilityMeasure Q] (L : Ω → ℝ) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (L x))) (n : ℕ) :
    Measure.pi (fun _ : Fin n => Q) ≪ Measure.pi (fun _ : Fin n => μ) := by
  apply Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
    Q μ _ n
  rw [hQ]
  exact withDensity_absolutelyContinuous μ _
/-- Given [a measurable sample space](hyp:Ω), [a reference probability law and
two alternative probability laws](hyp:μ,Q,R), [two likelihoods](hyp:L,M),
[their measurability](hyp:hL,hM), [their nonnegativity](hyp:hL0,hM0),
[their likelihood representations](hyp:hQ,hR), [an integrable one-observation
likelihood product](hyp:hpairInt), and [a sample size](hyp:n), [the product of
the iid densities is integrable under the iid reference law](goal). -/
theorem iid_pair_integrable_of_likelihood {Ω : Type*} [MeasurableSpace Ω] (μ Q R : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (L M : Ω → ℝ) (hL : Measurable L) (hM : Measurable M) (hL0 : ∀ x,
    0 ≤ L x) (hM0 : ∀ x, 0 ≤ M x) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (L x))) (hR : R = μ.withDensity (fun
    x => ENNReal.ofReal (M x))) (hpairInt : Integrable (fun x => L x * M x) μ) (n : ℕ) : Integrable (fun x =>
    (((Measure.pi (fun _ : Fin n => Q)).rnDeriv (Measure.pi (fun _ : Fin n => μ)) x).toReal) * (((Measure.pi (fun _ :
    Fin n => R)).rnDeriv (Measure.pi (fun _ : Fin n => μ)) x).toReal)) (Measure.pi (fun _ : Fin n => μ)) := by
  have hLeq : (fun x => (Q.rnDeriv μ x).toReal) =ᵐ[μ] L := by
    rw [hQ]
    filter_upwards [Measure.rnDeriv_withDensity μ hL.ennreal_ofReal] with x hx
    simp [hx, ENNReal.toReal_ofReal (hL0 x)]
  have hMeq : (fun x => (R.rnDeriv μ x).toReal) =ᵐ[μ] M := by
    rw [hR]
    filter_upwards [Measure.rnDeriv_withDensity μ hM.ennreal_ofReal] with x hx
    simp [hx, ENNReal.toReal_ofReal (hM0 x)]
  have hprod : (fun x => (Q.rnDeriv μ x).toReal *
      (R.rnDeriv μ x).toReal) =ᵐ[μ] (fun x => L x * M x) := by
    filter_upwards [hLeq, hMeq] with x hx hy
    simp [hx, hy]
  have hacQ : Q ≪ μ := by
    rw [hQ]
    exact withDensity_absolutelyContinuous μ _
  have hacR : R ≪ μ := by
    rw [hR]
    exact withDensity_absolutelyContinuous μ _
  have hint : Integrable (fun x => (Q.rnDeriv μ x).toReal *
      (R.rnDeriv μ x).toReal) μ := hpairInt.congr hprod.symm
  exact Causalean.Stat.Minimax.Mixture.iidPairIntegrable μ Q R hacQ hacR hint n
/-- Given [the first channel sample space](hyp:Ω₁), [the second channel sample
space](hyp:Ω₂), [the first channel's reference and component laws](hyp:P₁,Q₁,R₁),
[the second channel's reference and component laws](hyp:P₂,Q₂,R₂),
[domination in both channels](hyp:hQ₁,hR₁,hQ₂,hR₂), and [integrable component-density
products in both channels](hyp:hInt₁,hInt₂), [the product joint-density product
is integrable under the product reference law](goal). -/
theorem product_pair_integrable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ Q₁ R₁ : Measure Ω₁) (P₂ Q₂
    R₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁] [IsProbabilityMeasure R₁] [IsProbabilityMeasure
    P₂] [IsProbabilityMeasure Q₂] [IsProbabilityMeasure R₂] (hQ₁ : Q₁ ≪ P₁) (hR₁ : R₁ ≪ P₁) (hQ₂ : Q₂ ≪ P₂) (hR₂ : R₂ ≪
    P₂) (hInt₁ : Integrable (fun x => (Q₁.rnDeriv P₁ x).toReal * (R₁.rnDeriv P₁ x).toReal) P₁) (hInt₂ : Integrable (fun
    x => (Q₂.rnDeriv P₂ x).toReal * (R₂.rnDeriv P₂ x).toReal) P₂) : Integrable (fun z => ((Q₁.prod Q₂).rnDeriv (P₁.prod
    P₂) z).toReal * ((R₁.prod R₂).rnDeriv (P₁.prod P₂) z).toReal) (P₁.prod P₂) := by
  have hQ := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
    Q₁ P₁ Q₂ P₂ hQ₁ hQ₂
  have hR := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
    R₁ P₁ R₂ P₂ hR₁ hR₂
  have hEq : (fun z => ((Q₁.prod Q₂).rnDeriv (P₁.prod P₂) z).toReal *
      ((R₁.prod R₂).rnDeriv (P₁.prod P₂) z).toReal) =ᵐ[P₁.prod P₂]
      (fun z => ((Q₁.rnDeriv P₁ z.1).toReal * (R₁.rnDeriv P₁ z.1).toReal) *
        ((Q₂.rnDeriv P₂ z.2).toReal * (R₂.rnDeriv P₂ z.2).toReal)) := by
    filter_upwards [hQ, hR] with z hzQ hzR
    simp only [hzQ, hzR, ENNReal.toReal_mul]
    ring
  exact (Integrable.mul_prod hInt₁ hInt₂).congr hEq.symm
/-- Given [the first channel sample space](hyp:Ω₁), [the second channel sample
space](hyp:Ω₂), [the first channel's reference and component laws](hyp:P₁,Q₁,R₁),
[the second channel's reference and component laws](hyp:P₂,Q₂,R₂), and
[domination in both channels](hyp:hQ₁,hR₁,hQ₂,hR₂), [the overlap of the two product component
laws, meaning the integral under the product reference law of the product of their densities,
is the product of the two channels' separate overlaps](goal).

Integrability of the density products is not assumed: when a channel's density product is not
integrable, both sides are zero by the convention that the integral of a non-integrable function
is zero. -/
theorem product_pair_overlap {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ Q₁ R₁ : Measure Ω₁) (P₂ Q₂ R₂
    : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁] [IsProbabilityMeasure R₁] [IsProbabilityMeasure
    P₂] [IsProbabilityMeasure Q₂] [IsProbabilityMeasure R₂] (hQ₁ : Q₁ ≪ P₁) (hR₁ : R₁ ≪ P₁) (hQ₂ : Q₂ ≪ P₂) (hR₂ : R₂ ≪
    P₂) : (∫ z, ((Q₁.prod Q₂).rnDeriv (P₁.prod P₂) z).toReal *
    ((R₁.prod R₂).rnDeriv (P₁.prod P₂) z).toReal ∂(P₁.prod P₂)) = (∫ x, (Q₁.rnDeriv P₁ x).toReal * (R₁.rnDeriv P₁
    x).toReal ∂P₁) * (∫ x, (Q₂.rnDeriv P₂ x).toReal * (R₂.rnDeriv P₂ x).toReal ∂P₂) := by
  have hQ := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
    Q₁ P₁ Q₂ P₂ hQ₁ hQ₂
  have hR := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
    R₁ P₁ R₂ P₂ hR₁ hR₂
  have hEq : (fun z => ((Q₁.prod Q₂).rnDeriv (P₁.prod P₂) z).toReal *
      ((R₁.prod R₂).rnDeriv (P₁.prod P₂) z).toReal) =ᵐ[P₁.prod P₂]
      (fun z => ((Q₁.rnDeriv P₁ z.1).toReal * (R₁.rnDeriv P₁ z.1).toReal) *
        ((Q₂.rnDeriv P₂ z.2).toReal * (R₂.rnDeriv P₂ z.2).toReal)) := by
    filter_upwards [hQ, hR] with z hzQ hzR
    simp only [hzQ, hzR, ENNReal.toReal_mul]
    ring
  rw [integral_congr_ae hEq]
  exact integral_prod_mul
    (fun x => (Q₁.rnDeriv P₁ x).toReal * (R₁.rnDeriv P₁ x).toReal)
    (fun x => (Q₂.rnDeriv P₂ x).toReal * (R₂.rnDeriv P₂ x).toReal)
end Causalean.Stat.Minimax.Mixture

