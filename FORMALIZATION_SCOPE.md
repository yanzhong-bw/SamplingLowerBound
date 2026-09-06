# Formalization scope

## Published inputs

The project adds no axioms or incomplete proof terms. These published inputs
are propositions received as explicit theorem arguments:

- `KSOneThirdInput d`: a positive acceptance-probability gap chosen before the
  number of input variables and every degree-at-most-d Boolean polynomial.
  Source: Khodabandeh--Shinkar, arXiv:2605.00995v1, Theorem 6.4 and Remark 6.5.
- `PublishedAcceptanceGap d p`: the analogous fixed-bias input. Theorem A.8
  supplies it for fixed non-dyadic p in (0,1) and positive degree.
- `PublishedQuadraticGap`: the exact 1/24 gap recorded in KS Section 6.1.
  The manuscript's standard polar-form explanation is not separately proved
  in this development.

The main one-third, non-dyadic, and explicit quadratic bounds are verified
relative to these inputs. A successful axiom audit alone does not prove these
input propositions. The dyadic product and hierarchy require none of them.

## Paper-to-code correspondence

| Paper result | Formal development |
|---|---|
| Weighted affine-cube inequality | `Cube`, including degenerate cubes in every finite additive commutative group |
| General exponential amplification | `ActualAmplification`, deriving the tilted law, KL, Pinsker, tensorization and moments internally |
| Fixed-degree one-third target | `PolynomialModel`, `UniformAmplification`, `PolynomialSampling`, `Main.oneThird`; actual polynomials, arbitrary seed/output lengths, rate delta^6 |
| Non-dyadic and functional rank | `Main.productBias`, `FunctionalRank`, `SamplingConsequences`; explicit truth-table representation proves degree at most d*r |
| Quadratic constant and translations | `polynomial_quadratic_overlap`, `SourceTranslations`, relative to the published quadratic gap |
| Hellinger and entropy corollaries | `PolynomialHellinger` constructs actual tensor repetitions; `HellingerEntropy` proves the variational identity including an attaining law; `EntropyDecomposition` proves the exact Shannon, TC, and binary-KL identities |
| Entropy and bounded variance | `BoundedVariance`; finite strictly positive product references, as now specified in the manuscript and used in every application |
| Products of AND outputs | `MinimumWeight`, `BernoulliVariance`, `VarianceAmplification`, `DyadicSampling`, without KS |
| Prescribed-entropy hierarchy | `HierarchySampling`, `AndPolynomialBridge`, `Main.hierarchy`; ordinary N-bit target, exact atom mass, actual degree-(d+1) sampler, locality and overlap |
| Optimal entropy dependence | `FlatOptimality`; actual constant or identity polynomial sources for every flat normalized target |
| Growing-degree range | `GrowingDegree` finite estimates; `GrowingDegreeAsymptotic` and `Main.growingDegree` prove eventual bounds simultaneously for all allowed degrees and each positive exponent loss |
| Deterministic construction and cost | Executable sampler; `HierarchyCost` proves correctness of an explicitly counted recursive evaluator and at most N field multiplications |
| Constant-source lower witness and flat Shannon entropy | `LowerWitness` |

Flat entropy is represented by normalization and nonzero atom mass 2^(-k),
with support-cardinality and Shannon-entropy identities also proved.
`Main.hierarchy_not_degree_d` rules out any lower-degree sampler of the target
law; strictness therefore does not rely only on the degree of a chosen
polynomial representative.

## Verification boundary

The source audit rejects proof holes, unsafe declarations, native decision
trust, and local axioms. `Audit.lean` prints explicit dependencies;
`TrustAudit.lean` enumerates imported project theorems independently of that
readable list. Hashes identify the checked source files.

This is not a formalization of the proofs in the KS paper and its antecedents.
The operation model counts field multiplications, not CPU instructions,
indexing, copying, memory allocation, or I/O. Novelty, bibliographic
interpretation, and English-to-formal statement correspondence still require
scholarly review.
