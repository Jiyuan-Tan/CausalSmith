module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionTV

/-! # Risk transport for estimators that ignore audit labels. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory

/-- Embed an ordinary observed path into the audited-record carrier using
dummy audit coordinates. -/
def observedRecord {T nX nH k : Nat} (w : ObsPath T nX k) :
    AuditedRecord T nX nH k :=
  fun t => ((w t).1, ((w t).2.1, ((w t).2.2, (false, none))))

/-- The PHIW estimator regarded as a function of the ordinary observed path. -/
noncomputable def observedPhiwEstimator {T nX nH k : Nat}
    (t0 zeta : ℝ) (b e : Policy nX k) (w : ObsPath T nX k) : ℝ :=
  phiwEstimator t0 zeta b e (observedRecord (nH := nH) w)

/-- PHIW ignores the audit bit and atomic state label. -/
lemma phiwEstimator_eq_observedProjection {T nX nH k : Nat}
    (t0 zeta : ℝ) (b e : Policy nX k) (w : AuditedRecord T nX nH k) :
    phiwEstimator t0 zeta b e w =
      observedPhiwEstimator (nH := nH) t0 zeta b e (auditedProjection w) := by
  unfold phiwEstimator observedPhiwEstimator phiwScore observedRecord auditedProjection
  rfl

/-- The observed-path version of PHIW is measurable. -/
lemma measurable_observedPhiwEstimator {T nX nH k : Nat}
    (t0 zeta : ℝ) (b e : Policy nX k) :
    Measurable (observedPhiwEstimator (T := T) (nH := nH) t0 zeta b e) := by
  unfold observedPhiwEstimator phiwEstimator phiwScore observedRecord clipUnit
  fun_prop

/-- Auditing does not change the risk of PHIW because it is measurable through
the ordinary observation projection. -/
lemma sqRisk_audited_phiw_eq_observed {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (t0 zeta theta : ℝ) :
    Causalean.Stat.sqRisk (auditedLaw eta M)
        (phiwEstimator t0 zeta M.b M.e) theta =
      Causalean.Stat.sqRisk (obsLaw M)
        (observedPhiwEstimator (nH := nH) t0 zeta M.b M.e) theta := by
  have hproj : Measurable (auditedProjection (T := T) (nX := nX)
      (nH := nH) (k := k)) := by
    unfold auditedProjection
    fun_prop
  have hmap := Causalean.Stat.sqRisk_map_affinePullback
    (law := auditedLaw eta M) (phi := auditedProjection)
    (a := (1 : ℝ)) (b := 0) (theta := theta)
    (targetEst := observedPhiwEstimator (nH := nH) t0 zeta M.b M.e)
    one_ne_zero hproj (measurable_observedPhiwEstimator t0 zeta M.b M.e)
  simp only [one_pow, one_mul, add_zero] at hmap
  have hpull : Causalean.Stat.affinePullbackEstimator
      (auditedProjection (T := T) (nX := nX) (nH := nH) (k := k)) 1 0
      (observedPhiwEstimator (T := T) (nH := nH) t0 zeta M.b M.e) =
      phiwEstimator (T := T) (nH := nH) t0 zeta M.b M.e := by
    funext w
    unfold Causalean.Stat.affinePullbackEstimator
    rw [← phiwEstimator_eq_observedProjection]
    ring
  rw [hpull, auditedLaw_projection M eta heta] at hmap
  exact hmap

end CausalSmith.Stat.PomdpStateauditMinimax
