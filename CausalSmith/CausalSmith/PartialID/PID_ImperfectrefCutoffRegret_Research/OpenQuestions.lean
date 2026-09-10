/-! Nonassertive descriptions of the directional-inference route and open question. -/

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

-- @node: def:directional-optimizer-handle
def directionalOptimizerHandle : _root_.String :=
  "For a prespecified finite cutoff-policy class, H_dir starts from the stacked empirical process of the cutoff-atom--reference frequencies together with the two external binomial accuracy samples. It applies a Fang--Santos estimated directional derivative to the finite compositions of positive parts, minima, maxima, and comparator maxima defining the common-primitive complete regret vector and its sign--comparator graph; estimates contact sets with a vanishing tolerance; and inverts Armstrong--Shen simultaneous one-sided tests to seek refinements of the common-primitive inner and outer optimizer sets for T*. The handle specifies the technique and target but does not pre-commit a relative rate regime for n, n_1, n_0, a derivative estimator, a contact tolerance, or a critical-value formula. Uniform exactness at unstable optimizer ties and inference over an unrestricted continuum of cutoff policies remain open."
  -- @realizes \(\mathsf H_{\mathrm{dir}}\)(nonassertive directional-bootstrap handle)

-- @node: oeq:directional-optimizer-efficiency
def directionalOptimizerEfficiencyQuestion : _root_.String :=
  "Open question: for a prespecified finite cutoff-policy class under n, n_1, n_0 >= 1, can a primitive-process resampling scheme complete H_dir to give contact-adaptive refinements of the common-primitive inner and outer optimizer sets while retaining uniform asymptotic size control through capacity contacts and changing masks? Any positive answer must specify a relative rate regime for n, n_1, n_0, a uniformly consistent estimator of the directional derivative and its contact-set tolerance, local-size conditions for optimizer-set inversion, and an audit against both latent-cell linear programs and the four-mask Scan. These ingredients are not consequences of the present sampling assumptions; uniform exactness at unstable optimizer ties and inference over an unrestricted continuum of cutoff policies remain open."

end CausalSmith.PartialID.ImperfectrefCutoffRegret
