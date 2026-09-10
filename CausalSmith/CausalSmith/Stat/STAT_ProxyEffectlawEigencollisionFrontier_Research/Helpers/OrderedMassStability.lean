import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Risk

/-! # Ordered masses of locally separated finite atomic laws -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

private def atomicRank {k : ℕ} {radius : ℝ} (nu : AtomicLaw k radius) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun l => nu.atom l < nu.atom i).card

private lemma atomicRank_lt {k : ℕ} {radius : ℝ} (nu : AtomicLaw k radius)
    (i : Fin k) : atomicRank nu i < k := by
  unfold atomicRank
  have hsub : (Finset.univ.filter fun l => nu.atom l < nu.atom i) ⊂
      (Finset.univ : Finset (Fin k)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hi : i ∈ Finset.univ.filter (fun l => nu.atom l < nu.atom i) := by
      rw [heq]
      simp
    exact (lt_irrefl _) (Finset.mem_filter.mp hi).2
  simpa using Finset.card_lt_card hsub

private lemma atomicRank_lt_of_atom_lt {k : ℕ} {radius : ℝ}
    (nu : AtomicLaw k radius) (i j : Fin k) (hij : nu.atom i < nu.atom j) :
    atomicRank nu i < atomicRank nu j := by
  unfold atomicRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hl).2.trans hij⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun l => nu.atom l < nu.atom j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    rw [← heq] at hi
    exact (lt_irrefl _) (Finset.mem_filter.mp hi).2

private lemma atomicRank_injective {k : ℕ} {radius : ℝ}
    (nu : AtomicLaw k radius) (hinj : Function.Injective nu.atom) :
    Function.Injective (atomicRank nu) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (hinj.ne hne) with hlt | hgt
  · exact (Nat.ne_of_lt (atomicRank_lt_of_atom_lt nu i j hlt)) hij
  · exact (Nat.ne_of_gt (atomicRank_lt_of_atom_lt nu j i hgt)) hij

private lemma orderedMasses_apply_rank {k : ℕ} {radius : ℝ}
    (nu : AtomicLaw k radius) (hpos : ∀ i, 0 < nu.weight i)
    (hinj : Function.Injective nu.atom) (i : Fin k) :
    orderedMasses nu ⟨atomicRank nu i, atomicRank_lt nu i⟩ = nu.weight i := by
  unfold orderedMasses
  rw [if_pos ⟨hpos, hinj⟩]
  calc
    _ = if atomicRank nu i = atomicRank nu i then nu.weight i else 0 := by
      apply Finset.sum_eq_single i
      · intro l _ hli
        rw [if_neg]
        intro hr
        exact hli (atomicRank_injective nu hinj hr)
      · simp
    _ = nu.weight i := by simp

private lemma rank_bijective {k : ℕ} {radius : ℝ}
    (nu : AtomicLaw k radius) (hinj : Function.Injective nu.atom) :
    Function.Bijective (fun i : Fin k =>
      (⟨atomicRank nu i, atomicRank_lt nu i⟩ : Fin k)) := by
  have hi : Function.Injective (fun i : Fin k =>
      (⟨atomicRank nu i, atomicRank_lt nu i⟩ : Fin k)) :=
    fun _ _ h => atomicRank_injective nu hinj (Fin.ext_iff.mp h)
  exact ⟨hi, Finite.surjective_of_injective hi⟩

private lemma full_support_iff {k : ℕ} {radius : ℝ}
    (nu : AtomicLaw k radius) (hnu : AtomicLaw.Valid nu) :
    nu.support.card = k ↔ (∀ i, 0 < nu.weight i) ∧ Function.Injective nu.atom := by
  classical
  let s := Finset.univ.filter fun i : Fin k => 0 < nu.weight i
  constructor
  · intro hcard
    have himage : (s.image nu.atom).card = k := by simpa [AtomicLaw.support, s] using hcard
    have hsle : s.card ≤ k := by
      calc
        s.card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = k := by simp
    have himageLe : (s.image nu.atom).card ≤ s.card := Finset.card_image_le
    have hsCard : s.card = k := by omega
    have hs : s = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa [hsCard])
    have hpos : ∀ i, 0 < nu.weight i := by
      intro i
      have hi : i ∈ s := by rw [hs]; simp
      change i ∈ Finset.univ.filter (fun i : Fin k => 0 < nu.weight i) at hi
      exact (Finset.mem_filter.mp hi).2
    have hinjOn : Set.InjOn nu.atom s :=
      Finset.card_image_iff.mp (by omega : (s.image nu.atom).card = s.card)
    exact ⟨hpos, fun i j hij => hinjOn (by rw [hs]; simp) (by rw [hs]; simp) hij⟩
  · rintro ⟨hpos, hinj⟩
    rw [AtomicLaw.support, Finset.filter_eq_self.mpr (fun i _ => hpos i)]
    rw [Finset.card_image_iff.mpr
      (fun i (_hi : i ∈ (Finset.univ : Finset (Fin k)))
        j (_hj : j ∈ (Finset.univ : Finset (Fin k))) hij => hinj hij)]
    simp

private lemma support_eq_of_measureEquivalent {k : ℕ} {radius : ℝ}
    (nu xi : AtomicLaw.ProbabilityLaw k radius)
    (h : nu.MeasureEquivalent xi) : nu.1.support = xi.1.support := by
  classical
  have oneSide (a b : AtomicLaw.ProbabilityLaw k radius)
      (hab : a.MeasureEquivalent b) : a.1.support ⊆ b.1.support := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hipos := (Finset.mem_filter.mp hi).2
    have hleft : 0 < ∑ l with a.1.atom l = a.1.atom i, a.1.weight l :=
      Finset.sum_pos' (fun l _ => a.2.1 l) ⟨i, by simp, hipos⟩
    have hright : 0 < ∑ l with b.1.atom l = a.1.atom i, b.1.weight l := by
      rw [← hab.aggregate_weight]
      exact hleft
    obtain ⟨j, hjmem, hjpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun l _ => b.2.1 l)).mp hright
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hjpos⟩, (Finset.mem_filter.mp hjmem).2⟩
  ext x
  exact ⟨fun hx => oneSide nu xi h hx, fun hx => oneSide xi nu h.symm hx⟩

/-- Ordered aggregate masses depend only on the represented probability measure, despite being
computed from a chosen finite representative. -/
lemma orderedMasses_eq_of_measureEquivalent {k : ℕ} {radius : ℝ}
    (nu xi : AtomicLaw.ProbabilityLaw k radius)
    (h : nu.MeasureEquivalent xi) : orderedMasses nu.1 = orderedMasses xi.1 := by
  classical
  have hsupp := support_eq_of_measureEquivalent nu xi h
  by_cases hfull : nu.1.support.card = k
  · have hfullXi : xi.1.support.card = k := by rw [← hsupp]; exact hfull
    obtain ⟨hnuPos, hnuInj⟩ := (full_support_iff nu.1 nu.2).mp hfull
    obtain ⟨hxiPos, hxiInj⟩ := (full_support_iff xi.1 xi.2).mp hfullXi
    funext a
    obtain ⟨i, hi⟩ := (rank_bijective nu.1 hnuInj).2 a
    have hi' : a = ⟨atomicRank nu.1 i, atomicRank_lt nu.1 i⟩ := hi.symm
    rw [hi', orderedMasses_apply_rank nu.1 hnuPos hnuInj i]
    have hatomMem : nu.1.atom i ∈ xi.1.support := by
      rw [← hsupp]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnuPos i⟩, rfl⟩
    rcases Finset.mem_image.mp hatomMem with ⟨j, hj, hji⟩
    have hjpos := (Finset.mem_filter.mp hj).2
    have hweightEq : nu.1.weight i = xi.1.weight j := by
      have ha := h.aggregate_weight (nu.1.atom i)
      have hnuSum : ∑ l with nu.1.atom l = nu.1.atom i, nu.1.weight l = nu.1.weight i := by
        apply Finset.sum_eq_single i
        · intro l hl hli
          exact False.elim (hli (hnuInj (Finset.mem_filter.mp hl).2))
        · simp
      have hxiSum : ∑ l with xi.1.atom l = nu.1.atom i, xi.1.weight l = xi.1.weight j := by
        apply Finset.sum_eq_single j
        · intro l hl hlj
          exact False.elim
            (hlj (hxiInj ((Finset.mem_filter.mp hl).2.trans hji.symm)))
        · simp [hji]
      rwa [hnuSum, hxiSum] at ha
    have hmatch (l : Fin k) : ∃ q : Fin k, xi.1.atom q = nu.1.atom l := by
      have hm : nu.1.atom l ∈ xi.1.support := by
        rw [← hsupp]
        exact Finset.mem_image.mpr ⟨l,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnuPos l⟩, rfl⟩
      rcases Finset.mem_image.mp hm with ⟨q, _hq, hql⟩
      exact ⟨q, hql⟩
    let psi : Fin k → Fin k := fun l => Classical.choose (hmatch l)
    have hpsi (l : Fin k) : xi.1.atom (psi l) = nu.1.atom l := Classical.choose_spec (hmatch l)
    have hpsiInj : Function.Injective psi := by
      intro l q heq
      apply hnuInj
      rw [← hpsi l, ← hpsi q, heq]
    have hpsiBij : Function.Bijective psi := ⟨hpsiInj, Finite.surjective_of_injective hpsiInj⟩
    have hrankEq : atomicRank nu.1 i = atomicRank xi.1 j := by
      unfold atomicRank
      apply Finset.card_bijective psi hpsiBij
      intro l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpsi, ← hji]
    have hfin : (⟨atomicRank nu.1 i, atomicRank_lt nu.1 i⟩ : Fin k) =
        ⟨atomicRank xi.1 j, atomicRank_lt xi.1 j⟩ := Fin.ext hrankEq
    rw [hfin, orderedMasses_apply_rank xi.1 hxiPos hxiInj j, hweightEq]
  · have hfullXi : xi.1.support.card ≠ k := by rwa [← hsupp]
    unfold orderedMasses
    rw [if_neg (fun hcond => hfull ((full_support_iff nu.1 nu.2).mpr hcond)),
      if_neg (fun hcond => hfullXi ((full_support_iff xi.1 xi.2).mpr hcond))]

/-- Ordered masses descend to a measurable function on extensional atomic laws. -/
lemma orderedMasses_representative_measurable {k : ℕ} {radius : ℝ} :
    Measurable (fun q : AtomicLaw.LawModulo k radius =>
      orderedMasses q.representative.1) := by
  have heq : (fun q : AtomicLaw.LawModulo k radius =>
      orderedMasses q.representative.1) ∘ AtomicLaw.LawModulo.ofProbabilityLaw =
      fun nu : AtomicLaw.ProbabilityLaw k radius => orderedMasses nu.1 := by
    funext nu
    apply orderedMasses_eq_of_measureEquivalent
    change (AtomicLaw.probabilityLawSetoid k radius).r
      (AtomicLaw.LawModulo.ofProbabilityLaw nu).representative nu
    exact (Quotient.eq_mk_iff_out
      (x := AtomicLaw.LawModulo.ofProbabilityLaw nu) (y := nu)).mp rfl
  change Measurable
    ((fun q : AtomicLaw.LawModulo k radius => orderedMasses q.representative.1) ∘
      AtomicLaw.LawModulo.ofProbabilityLaw)
  rw [heq]
  exact orderedMasses_measurable.comp measurable_subtype_coe

/-- The canonical ordered-weight estimator is measurable. -/
lemma orderedWeightEstimator_measurable {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0) :
    Measurable (orderedWeightEstimator R) := by
  exact orderedMasses_representative_measurable.comp R.measurableRepair

/-- Below the localization radius, ordered atomic weights are Lipschitz in `W₁` with the
expected inverse support-gap factor. -/
theorem orderedMasses_l1_le_four_mul_wass1_div_gap
    {k : ℕ} {radius m delta : ℝ} (nu xi : AtomicLaw k radius)
    (hnu : AtomicLaw.Valid nu) (hxi : AtomicLaw.Valid xi)
    (hm : 0 < m) (hdelta : 0 < delta)
    (hweight : ∀ i, m ≤ nu.weight i)
    (hinj : Function.Injective nu.atom)
    (hgap : ∀ i j, i ≠ j → delta ≤ |nu.atom i - nu.atom j|)
    (hsmall : AtomicLaw.wass1 nu xi < m * delta / 4) :
    ∑ a, |orderedMasses xi a - orderedMasses nu a| ≤
      4 * AtomicLaw.wass1 nu xi / delta := by
  classical
  obtain ⟨gamma, hgamma⟩ := AtomicLaw.wass1_optimal_plan hnu hxi
  have hnear (i : Fin k) : ∃ j : Fin k,
      0 < xi.weight j ∧ |nu.atom i - xi.atom j| < delta / 4 := by
    by_contra hnone
    push_neg at hnone
    have hrow (j : Fin k) : gamma.mass i j * (delta / 4) ≤
        gamma.mass i j * |nu.atom i - xi.atom j| := by
      by_cases hz : gamma.mass i j = 0
      · simp [hz]
      · have hmass : 0 < gamma.mass i j := lt_of_le_of_ne (gamma.nonneg i j) (Ne.symm hz)
        have hxipos : 0 < xi.weight j := by
          rw [← gamma.snd_marginal j]
          exact lt_of_lt_of_le hmass
            (Finset.single_le_sum (fun l _ => gamma.nonneg l j) (Finset.mem_univ i))
        exact mul_le_mul_of_nonneg_left (hnone j hxipos) (gamma.nonneg i j)
    have hcost : m * delta / 4 ≤ AtomicLaw.transportCost gamma := by
      calc
        m * delta / 4 ≤ nu.weight i * (delta / 4) := by
          nlinarith [hweight i, hdelta]
        _ = (∑ j, gamma.mass i j) * (delta / 4) := by rw [gamma.fst_marginal]
        _ = ∑ j, gamma.mass i j * (delta / 4) := by rw [Finset.sum_mul]
        _ ≤ ∑ j, gamma.mass i j * |nu.atom i - xi.atom j| :=
          Finset.sum_le_sum fun j _ => hrow j
        _ ≤ ∑ l, ∑ j, gamma.mass l j * |nu.atom l - xi.atom j| := by
          calc
            _ = Finset.sum {i}
                (fun l => ∑ j, gamma.mass l j * |nu.atom l - xi.atom j|) := by simp
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun l _ _ =>
              Finset.sum_nonneg fun j _ =>
                mul_nonneg (gamma.nonneg l j) (abs_nonneg _)
        _ = AtomicLaw.transportCost gamma := rfl
    linarith [hgamma]
  let phi : Fin k → Fin k := fun i => Classical.choose (hnear i)
  have hphiPos (i : Fin k) : 0 < xi.weight (phi i) := (Classical.choose_spec (hnear i)).1
  have hphiClose (i : Fin k) : |nu.atom i - xi.atom (phi i)| < delta / 4 :=
    (Classical.choose_spec (hnear i)).2
  have hphiInj : Function.Injective phi := by
    intro i j hij
    by_contra hne
    have hg := hgap i j hne
    have ht := abs_sub_le (nu.atom i) (xi.atom (phi i)) (nu.atom j)
    have hclosej : |xi.atom (phi i) - nu.atom j| < delta / 4 := by
      rw [hij, abs_sub_comm]
      exact hphiClose j
    linarith [hphiClose i]
  have hphiBij : Function.Bijective phi :=
    ⟨hphiInj, Finite.surjective_of_injective hphiInj⟩
  let ephi : Fin k ≃ Fin k := Equiv.ofBijective phi hphiBij
  have hephi (i : Fin k) : ephi i = phi i := rfl
  have hxiPos (j : Fin k) : 0 < xi.weight j := by
    obtain ⟨i, rfl⟩ := hphiBij.2 j
    exact hphiPos i
  have hxiInj : Function.Injective xi.atom := by
    intro a b hab
    obtain ⟨i, rfl⟩ := hphiBij.2 a
    obtain ⟨j, rfl⟩ := hphiBij.2 b
    apply congrArg phi
    apply hinj
    by_contra hneAtoms
    have hne : i ≠ j := fun h => hneAtoms (congrArg nu.atom h)
    have hg := hgap i j hne
    have ht := abs_sub_le (nu.atom i) (xi.atom (phi i)) (nu.atom j)
    have hclosej : |xi.atom (phi i) - nu.atom j| < delta / 4 := by
      rw [hab, abs_sub_comm]
      exact hphiClose j
    linarith [hphiClose i]
  have horder (i j : Fin k) :
      nu.atom i < nu.atom j ↔ xi.atom (phi i) < xi.atom (phi j) := by
    constructor
    · intro hij
      have hne : i ≠ j := fun h => by subst j; exact (lt_irrefl _ hij)
      have hg := hgap i j hne
      rw [abs_of_neg (sub_neg.mpr hij)] at hg
      have hi := (abs_lt.mp (hphiClose i)).1
      have hj := (abs_lt.mp (hphiClose j)).2
      linarith
    · intro hij
      by_contra hnot
      have hne : i ≠ j := fun h => by subst j; exact (lt_irrefl _ hij)
      have hji : nu.atom j < nu.atom i := lt_of_le_of_ne (le_of_not_gt hnot)
        (hinj.ne hne).symm
      have hg := hgap j i hne.symm
      rw [abs_of_neg (sub_neg.mpr hji)] at hg
      have hj := (abs_lt.mp (hphiClose j)).1
      have hi := (abs_lt.mp (hphiClose i)).2
      linarith
  have hrank (i : Fin k) : atomicRank xi (phi i) = atomicRank nu i := by
    unfold atomicRank
    symm
    apply Finset.card_bijective ephi hphiBij
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [hephi] using horder j i
  have hl1 : ∑ a, |orderedMasses xi a - orderedMasses nu a| =
      ∑ i, |xi.weight (phi i) - nu.weight i| := by
    rw [← (rank_bijective nu hinj).sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [orderedMasses_apply_rank nu (fun i => hm.trans_le (hweight i)) hinj i]
    have hfin : (⟨atomicRank nu i, atomicRank_lt nu i⟩ : Fin k) =
        ⟨atomicRank xi (phi i), atomicRank_lt xi (phi i)⟩ := by
      apply Fin.ext
      exact (hrank i).symm
    rw [hfin, orderedMasses_apply_rank xi hxiPos hxiInj (phi i)]
  let diag : ℝ := ∑ i, gamma.mass i (phi i)
  let off : ℝ := 1 - diag
  have hrowOff (i : Fin k) : 0 ≤ nu.weight i - gamma.mass i (phi i) := by
    rw [← gamma.fst_marginal i]
    exact sub_nonneg.mpr (Finset.single_le_sum (fun j _ => gamma.nonneg i j)
      (Finset.mem_univ (phi i)))
  have hcolOff (i : Fin k) : 0 ≤ xi.weight (phi i) - gamma.mass i (phi i) := by
    rw [← gamma.snd_marginal (phi i)]
    exact sub_nonneg.mpr (Finset.single_le_sum (fun l _ => gamma.nonneg l (phi i))
      (Finset.mem_univ i))
  have hsumRow : ∑ i, (nu.weight i - gamma.mass i (phi i)) = off := by
    simp only [Finset.sum_sub_distrib, hnu.2.1, diag, off]
  have hsumCol : ∑ i, (xi.weight (phi i) - gamma.mass i (phi i)) = off := by
    rw [Finset.sum_sub_distrib]
    rw [hphiBij.sum_comp]
    simp [hxi.2.1, diag, off]
  have hl1off : ∑ i, |xi.weight (phi i) - nu.weight i| ≤ 2 * off := by
    calc
      _ = ∑ i, |(xi.weight (phi i) - gamma.mass i (phi i)) -
          (nu.weight i - gamma.mass i (phi i))| := by congr 1; funext i; ring
      _ ≤ ∑ i, ((xi.weight (phi i) - gamma.mass i (phi i)) +
          (nu.weight i - gamma.mass i (phi i))) := by
        gcongr with i
        rw [abs_le]
        constructor <;> linarith [hrowOff i, hcolOff i]
      _ = 2 * off := by rw [Finset.sum_add_distrib, hsumCol, hsumRow]; ring
  have hcost : delta / 2 * off ≤ AtomicLaw.transportCost gamma := by
    have hoffEq : off = ∑ i, Finset.sum (Finset.univ.erase (phi i)) (gamma.mass i) := by
      have hrow (i : Fin k) : Finset.sum (Finset.univ.erase (phi i)) (gamma.mass i) =
          nu.weight i - gamma.mass i (phi i) := by
        have hsplit := Finset.sum_erase_add Finset.univ (gamma.mass i)
          (Finset.mem_univ (phi i))
        rw [gamma.fst_marginal] at hsplit
        linarith
      rw [show off = ∑ i, (nu.weight i - gamma.mass i (phi i)) by symm; exact hsumRow]
      apply Finset.sum_congr rfl
      intro i _
      exact (hrow i).symm
    rw [hoffEq]
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, Finset.sum (Finset.univ.erase (phi i))
          (fun j => gamma.mass i j * (delta / 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_comm, Finset.sum_mul]
      _ ≤ ∑ i, Finset.sum (Finset.univ.erase (phi i))
          (fun j => gamma.mass i j * |nu.atom i - xi.atom j|) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        have hjne : j ≠ phi i := Finset.ne_of_mem_erase hj
        obtain ⟨l, hl⟩ := hphiBij.2 j
        have hil : i ≠ l := fun h => hjne (by subst l; exact hl.symm)
        subst j
        have hg := hgap i l hil
        have ht := abs_sub_le (nu.atom i) (xi.atom (phi l)) (nu.atom l)
        have hdist : delta / 2 ≤ |nu.atom i - xi.atom (phi l)| := by
          rw [abs_sub_comm (xi.atom (phi l)) (nu.atom l)] at ht
          linarith [hphiClose l]
        exact mul_le_mul_of_nonneg_left hdist (gamma.nonneg i (phi l))
      _ ≤ ∑ i, ∑ j, gamma.mass i j * |nu.atom i - xi.atom j| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ =>
          mul_nonneg (gamma.nonneg i j) (abs_nonneg _)
      _ = AtomicLaw.transportCost gamma := rfl
  rw [hl1, ← hgamma]
  have hw0 : 0 ≤ AtomicLaw.transportCost gamma := by
    unfold AtomicLaw.transportCost
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (gamma.nonneg i j) (abs_nonneg _)
  have hoffBound : off ≤ 2 * AtomicLaw.transportCost gamma / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  calc
    ∑ i, |xi.weight (phi i) - nu.weight i| ≤ 2 * off := hl1off
    _ ≤ 4 * AtomicLaw.transportCost gamma / delta := by
      rw [show 4 * AtomicLaw.transportCost gamma / delta =
        2 * (2 * AtomicLaw.transportCost gamma / delta) by ring]
      gcongr

/-- Gap-stratum membership supplies the positive weights, injectivity, and numerical gap needed
by the finite-atomic stability lemma. -/
theorem gapStratum_orderedMasses_l1_le
    {k dx dz : ℕ} {L pi0 sigma0 g : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : GapStratum (L := L) (pi0 := pi0) (sigma0 := sigma0) (g := g) P)
    (hg : 0 < g)
    (xi : AtomicLaw k (effectRadius dz L sigma0)) (hxi : AtomicLaw.Valid xi)
    (hsmall : AtomicLaw.wass1 (quotientLawRaw P (effectRadius dz L sigma0)) xi <
      pi0 * (g / 2) / 4) :
    ∑ a, |orderedMasses xi a -
        orderedMasses (quotientLawRaw P (effectRadius dz L sigma0)) a| ≤
      8 * AtomicLaw.wass1 (quotientLawRaw P (effectRadius dz L sigma0)) xi / g := by
  rcases hM.toUCVMWModel.coreDomain with
    ⟨_hk, _hkx, _hkz, _hL, hpi, _hpiMax, _hsigma, _hsigmaMax⟩
  have hmass (u : Fin k) : pi0 ≤ latentMass P u :=
    (hM.toUCVMWModel.latentArmPositivity u false).trans
      (measureReal_mono (fun _ hw => hw.1))
  have hmassPos (u : Fin k) : 0 < latentMass P u :=
    hpi.trans_le (hmass u)
  have hfilter : (Finset.univ.filter fun u : Fin k => 0 < latentMass P u) =
      Finset.univ := Finset.filter_eq_self.mpr fun u _ => hmassPos u
  have hcard : ((Finset.univ : Finset (Fin k)).image (latentEffect P)).card =
      (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ]
    simpa [DistinctEffects, hfilter] using hM.distinctEffects
  have hinjOn := Finset.card_image_iff.mp hcard
  have hinj : Function.Injective (latentEffect P) := by
    intro i j hij
    exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hgap (i j : Fin k) (hij : i ≠ j) :
      g / 2 ≤ |latentEffect P i - latentEffect P j| := by
    have hmem : ((|latentEffect P i - latentEffect P j| : ℝ) : EReal) ∈
        {d : EReal | ∃ u v : Fin k,
          0 < latentMass P u ∧ 0 < latentMass P v ∧ latentEffect P u ≠ latentEffect P v ∧
          d = ((|latentEffect P u - latentEffect P v| : ℝ) : EReal)} := by
      exact ⟨i, j, hmassPos i, hmassPos j, hinj.ne hij, rfl⟩
    have hsinf : effectGap P ≤ (|latentEffect P i - latentEffect P j| : ℝ) :=
      sInf_le hmem
    have := hM.gapWindow.1.trans hsinf
    exact EReal.coe_le_coe_iff.mp this
  have hbase := orderedMasses_l1_le_four_mul_wass1_div_gap
    (quotientLawRaw P (effectRadius dz L sigma0)) xi
    (quotientLawRaw_valid P hM.toUCVMWModel) hxi
    hpi (by linarith)
    hmass hinj hgap hsmall
  convert hbase using 1 <;> field_simp <;> ring

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
