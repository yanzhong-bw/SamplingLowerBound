# Exponential Sampling Lower Bounds for Polynomial Sources

Lean 4 formalization accompanying Yan Zhong's paper.

Repository: <https://github.com/yanzhong-bw/SamplingLowerBound>.

Start with `SamplingLowerBounds/Main.lean`. Its theorems concern actual
multivariate polynomials over `ZMod 2`, their output distributions on uniform
seeds, and actual Bernoulli or constructed graph distributions. All information
and moment bounds are derived for those distributions.

## Results and external inputs

| Result | Entry point | External input |
|---|---|---|
| Fixed-degree one-third bound, uniform in seed length | `Main.oneThird` | KS uniform acceptance gap |
| Other fixed product biases | `Main.productBias` | Corresponding acceptance gap |
| Quadratic exponent and translated targets | `Main.quadratic`, `polynomial_quadratic_translated_overlap` | Published quadratic gap of 1/24 |
| Dyadic product exponent | `Main.dyadicProduct` | None |
| Explicit adjacent-degree sampler, entropy, locality, overlap | `Main.hierarchy`, `hierarchy_entropy_overlap` | None |
| Uniform growing-degree asymptotics | `Main.growingDegree` | None |
| Entropy optimality for every flat target | `flat_overlap_lower_bound` | None |
| Hellinger and entropy-cost corollaries | `polynomial_oneThird_affinity`, `polynomial_entropy_cost` | Same KS gap |
| Functional-rank extension | `functional_rank_product_exponential` | Gap at degree d*r; representation is proved |

`ExternalInputs.lean` records the published results as propositions received
through explicit proof arguments. It declares no new axioms. The one-third
results are formal verification **relative to the specified published inputs**;
their proofs in the KS paper are not re-proved here. The dyadic hierarchy has
no such external hypothesis. See `FORMALIZATION_SCOPE.md`.

## Reproduce the verification

Lean 4.19.0 and Mathlib v4.19.0 are pinned, including exact dependency commits.
With Lean's elan installer available:

```sh
lake exe cache get
python3 scripts/verify.py
```

The verifier builds the project, checks source files for proof holes and trust
extensions, runs `Audit.lean`, and independently enumerates imported project
theorems in `TrustAudit.lean`. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. An axiom audit does not discharge explicit theorem hypotheses.

The GitHub Actions workflow runs the same checks on pushes and pull requests,
and can also be started manually. Check the repository's Actions tab for the
status of a particular commit.

The recorded full verification and the release checksums are in `validation/`.
`VALIDATION.md` distinguishes the original Lean build from subsequent
documentation updates. `BUILD-ENVIRONMENT.md` describes the pinned environment
and a local executable-path adjustment used for that recorded build.

## Executable construction

`canonicalSampler` evaluates the padded AND construction. `HierarchyCost.lean`
implements a recursive evaluator counting each actual AND as a field
multiplication, proves that it returns the same polynomial sampler, and proves
its count is exactly q*d, at most k and hence at most N. Copying, index
arithmetic, and constant padding have zero field-operation cost in this model;
no wall-clock or bit-complexity claim is made.
