/-!
# Bibliographic comparator-scope records

These closed string payloads record cited scope facts. They are metadata only
and are not logical hypotheses of any theorem.
-/

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: lem:cauca-comparator-scope
/-- Wendong, Kekić, von Kügelgen, Buchholz, Besserve, Gresele, and Schölkopf (2023),
"Causal Component Analysis," Definition 3.2, Theorem 4.2, and Appendix E.2,
NeurIPS paper handle `WendongEtAl2023CauCA`.

The source assumes the graph is known and intervention targets are observed;
with one perfect stochastic intervention per node, each satisfying Assumption 4.1,
CauCA is identifiable up to componentwise scaling. -/
def caucaComparatorScope : _root_.String :=
  "Wendong et al. (2023), Causal Component Analysis, Definition 3.2, Theorem 4.2, and Appendix E.2 (WendongEtAl2023CauCA; https://papers.nips.cc/paper_files/paper/2023/file/67089958e98b243d5cc1881ad60418b8-Paper-Conference.pdf): the graph G is assumed known, intervention targets are observed and fixed across candidate models, and one perfect stochastic intervention per node, each satisfying Assumption 4.1, gives identification up to componentwise scaling."

-- @node: lem:von-kugelgen-comparator-scope
/-- von Kügelgen, Besserve, Wendong, Gresele, Kekić, Bareinboim, Blei, and Schölkopf
(2023), "Nonparametric Identifiability of Causal Representations from Unknown
Interventions," Theorems 3.2 and 3.4 and Section 7, handle
`vonKugelgenEtAl2023UnknownInterventions`.

The source proves the bivariate one-intervention result under continuous
genericity, uses paired interventions in arbitrary dimension, and describes the
arbitrary-dimensional one-intervention extension as a conjecture. -/
def vonKugelgenComparatorScope : _root_.String :=
  "von Kugelgen et al. (2023), Nonparametric Identifiability of Causal Representations from Unknown Interventions, Theorems 3.2 and 3.4 and Section 7 (vonKugelgenEtAl2023UnknownInterventions; https://papers.nips.cc/paper_files/paper/2023/file/97fe251c25b6f99a2a23b330a75b11d4-Paper-Conference.pdf): Theorem 3.2 is bivariate with one unknown-target perfect intervention per node and a continuous witness genericity condition; Theorem 3.4 uses two paired perfect interventions per node in arbitrary dimension; the one-intervention extension for n greater than two is stated as a conjecture."

-- @node: lem:yao-comparator-scope
/-- Yao, Rancati, Cadei, Fumero, and Locatello (2025), "Unifying Causal
Representation Learning with the Invariance Principle," Assumption D.1,
Corollary D.1, and the following remark, arXiv handle `2409.02772v2`.

The source assumes targets supplied in topological order and treats recovery of
that order as a separate subproblem. -/
def yaoComparatorScope : _root_.String :=
  "Yao et al. (2025), Unifying Causal Representation Learning with the Invariance Principle, Assumption D.1, Corollary D.1, and the immediately following remark (YaoEtAl2025InvariancePrinciple; arXiv:2409.02772v2; https://arxiv.org/abs/2409.02772v2): exactly one imperfect intervention is supplied per node, the target labels preserve a supplied topological order, componentwise identification follows from marginal and score invariances, and identifying the order is explicitly treated as a separate subproblem."

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
