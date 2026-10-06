module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LowerInformation

/-! # Supported learner families

Joint measurability on valid data, randomizers, and scores gives a Borel policy
family on the ambient parameter space with identical risks on each legal law.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- An admissible fixed-logger learner has a jointly Borel representative on
the ambient data and randomizer space, agreeing on every valid input. -/
-- @node: learner_family_representative
lemma learner_family_representative (n : ℕ) (e : ℝ → ℝ)
    (he : Measurable (fun x : Set.Icc (0:ℝ) 1 => e x))
    (hepos : ∀ x ∈ Set.Icc (0:ℝ) 1, e x ∈ Set.Ioo (0:ℝ) 1)
    (Φ : Learner n) (hΦ : LearnerClass n Φ) :
    ∃ ψ : ((Fin n → Observation) × ℝ) → ℝ → Bool,
      Measurable (fun z : ((Fin n → Observation) × ℝ) × Set.Icc (0:ℝ) 1 =>
        ψ z.1 z.2) ∧
      ∀ d u, (∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧
        (d i).Y ∈ Set.Icc (-1:ℝ) 1) → u ∈ Set.Icc (0:ℝ) 1 →
        Set.EqOn (ψ (d,u)) (Φ e d u) (Set.Icc (0:ℝ) 1) := by
  classical
  have hX : Measurable (fun o : Observation => o.X) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
      (comap_measurable _)
  have hY : Measurable (fun o : Observation => o.Y) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
      (comap_measurable _)
  let S : Set (((Fin n → Observation) × ℝ) × Set.Icc (0:ℝ) 1) :=
    {z | (∀ i, (z.1.1 i).X ∈ Set.Icc (0:ℝ) 1 ∧
      (z.1.1 i).Y ∈ Set.Icc (-1:ℝ) 1) ∧ z.1.2 ∈ Set.Icc (0:ℝ) 1}
  have hS : MeasurableSet S := by
    apply MeasurableSet.inter
    · change MeasurableSet {z : ((Fin n → Observation) × ℝ) ×
          Set.Icc (0:ℝ) 1 | ∀ i, (z.1.1 i).X ∈ Set.Icc (0:ℝ) 1 ∧
            (z.1.1 i).Y ∈ Set.Icc (-1:ℝ) 1}
      rw [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro i
      have hm : Measurable (fun z : ((Fin n → Observation) × ℝ) ×
          Set.Icc (0:ℝ) 1 => z.1.1 i) := by fun_prop
      exact ((hX.comp hm) measurableSet_Icc).inter
        ((hY.comp hm) measurableSet_Icc)
    · exact (measurable_snd.comp measurable_fst) measurableSet_Icc
  let g : S → Bool := fun z => Φ e z.1.1.1 z.1.1.2 z.1.2
  have hg : Measurable g := by
    have hm : Measurable (fun z : S =>
      ((fun i => (⟨z.1.1.1 i, z.2.1 i⟩ : {o : Observation //
        o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1})),
        (⟨z.1.1.2, z.2.2⟩ : Set.Icc (0:ℝ) 1), z.1.2)) := by fun_prop
    exact (hΦ e he hepos).1.comp hm
  obtain ⟨f, hf, hfg⟩ := (MeasurableEmbedding.subtype_coe hS).exists_measurable_extend
    hg (fun _ => inferInstance)
  let ψ : ((Fin n → Observation) × ℝ) → ℝ → Bool :=
    fun w x => if hx : x ∈ Set.Icc (0:ℝ) 1 then f (w, ⟨x,hx⟩) else false
  refine ⟨ψ, ?_, ?_⟩
  · have heq : (fun z : ((Fin n → Observation) × ℝ) × Set.Icc (0:ℝ) 1 =>
        ψ z.1 z.2) = f := by
      funext z
      dsimp only [ψ]
      rw [dif_pos z.2.2]
    rw [heq]
    exact hf
  · intro d u hd hu x hx
    have h := congrFun hfg (⟨((d,u),⟨x,hx⟩), hd, hu⟩ : S)
    dsimp only [ψ]
    rw [dif_pos hx]
    exact h

/-- Legal experiments are supported on valid observed data and randomizers. -/
-- @node: learner_input_support_ae
lemma learner_input_support_ae (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e) :
    ∀ᵐ du ∂experiment P n,
      (∀ i, (du.1 i).X ∈ Set.Icc (0:ℝ) 1 ∧ (du.1 i).Y ∈ Set.Icc (-1:ℝ) 1) ∧
      du.2 ∈ Set.Icc (0:ℝ) 1 := by
  have hψ : Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ =>
      (t.1,t.2.1,t.2.2.1))).comp (comap_measurable _)
  have hX : Measurable (fun o : Observation => o.X) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
      (comap_measurable _)
  have hY : Measurable (fun o : Observation => o.Y) :=
    (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
      (comap_measurable _)
  have hobs : ∀ᵐ o ∂P.obsLaw,
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1 := by
    apply (ae_map_iff hψ.aemeasurable
      ((hX measurableSet_Icc).inter (hY measurableSet_Icc))).2
    filter_upwards [ae_iff.mpr hP.wf.2.1, ae_iff.mpr hP.wf.2.2.1] with o hx hy
    exact ⟨hx,hy⟩
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw := Measure.isProbabilityMeasure_map hψ.aemeasurable
  have hdata : ∀ᵐ d ∂sampleLaw P n, ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1 :=
    Filter.eventually_all.2 (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => P.obsLaw) (i := i)).eventually hobs)
  have hU : ∀ᵐ u ∂uniformRandomizer, u ∈ Set.Icc (0:ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdata,
    Measure.quasiMeasurePreserving_snd.ae hU] with du hd hu
  exact ⟨hd, hu⟩

/-- Policies agreeing on the score interval have equal raw regret under a
legal score law. -/
-- @node: rawRegret_eq_of_eqOn_score
lemma rawRegret_eq_of_eqOn_score (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (φ ψ : ℝ → Bool) (h : Set.EqOn φ ψ (Set.Icc (0:ℝ) 1)) :
    rawRegret P φ = rawRegret P ψ := by
  unfold rawRegret rawWelfare
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr hP.score.2] with x hx
  rw [h hx]

end CausalSmith.Stat.ScorethresholdOverlapRegret
