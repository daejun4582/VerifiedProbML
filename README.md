# Verified ProbML

Lean 4 formalizations of two foundational results from probabilistic machine
learning:

- minimum-variance weighting of independent Gaussian estimates;
- optimality of the true probability under binary cross-entropy.

I built this project while reviewing probability, constrained optimization, and
information theory. The aim is to make the assumptions visible and have Lean
check each algebraic, probabilistic, and optimization step. An earlier exact
bisection exercise is kept as a smaller baseline at the end of the repository.

## 1. Gaussian weighted ensembles

Suppose several estimators have a common mean and variances `σᵢ²`. For weights
whose sum is one, define

```text
X̂ = ∑ i, wᵢ Xᵢ.
```

The Lean development proves:

- the common mean is preserved, so the weighted estimator is unbiased;
- if the estimators are independent, then
  `Var(X̂) = ∑ i, wᵢ² σᵢ²`;
- if the estimators are Gaussian, their independent weighted sum is Gaussian;
- inverse-variance weights minimize the variance among all weights summing to
  one.

The optimal weights are

```text
wᵢ = (1 / σᵢ²) / ∑ j, (1 / σⱼ²).
```

Instead of stopping at the Lagrange multiplier condition, the proof establishes
the global minimum through the identity

```text
V(w) = V(w*) + ∑ i, σᵢ² (wᵢ - wᵢ*)².
```

The main declarations are:

| Result | Lean declaration |
|---|---|
| Weights summing to one preserve a common expectation | `weightedSum_expectation` |
| Variance of an independent weighted sum | `weightedSum_variance` |
| An independent weighted Gaussian sum is Gaussian | `weightedSum_isGaussian` |
| Quadratic variance decomposition | `ensembleVariance_decomposition` |
| Precision weights give a global minimum | `precisionWeight_minimizes` |
| Inverse-variance weights minimize variance | `inverseVarianceWeight_minimizes` |

### Exact three-model example

For model variances `[1, 4, 9]`, Lean checks that the inverse-variance weights
and resulting minimum variance are

```text
weights           = [36/49, 9/49, 4/49]
ensemble variance = 36/49
```

It also proves that this variance is no larger than the variance produced by
any other three weights that sum to one.

## 2. Binary cross-entropy

For a true Bernoulli probability `p` and a reported probability `q`, define

```text
CE(p, q) = -p log(q) - (1-p) log(1-q).
```

For `p,q ∈ (0,1)`, the formalization proves the decomposition

```text
CE(p, q) = H(p) + KL(Bernoulli(p) || Bernoulli(q)).
```

It then proves the Bernoulli version of Gibbs' inequality and concludes

```text
CE(p, p) ≤ CE(p, q).
```

This is the small mathematical statement behind the claim that expected binary
log loss is minimized by reporting the true probability.

| Result | Lean declaration |
|---|---|
| Self cross-entropy equals binary entropy | `crossEntropy_self` |
| Cross-entropy/entropy/KL decomposition | `crossEntropy_eq_entropy_add_kl` |
| Bernoulli KL is nonnegative | `bernoulliKL_nonneg` |
| Truth minimizes expected binary log loss | `crossEntropy_minimized_at_truth` |

The boundary cases `p = 0,1` or `q = 0,1` are deliberately excluded from the
main theorem so that every logarithm has a positive argument.

## 3. Additional baseline: exact bisection

An earlier Lean exercise performs ten rational bisection steps for `x² = 2` and
proves

```text
181/128 ≤ √2 ≤ 1449/1024
interval width = 1/1024.
```

This module is separate from the probabilistic ML results and is kept as a
compact example of an executable calculation carrying a proof certificate.

## Build and run

The toolchain is pinned to Lean `4.34.0` and Mathlib `v4.34.0`.

```bash
lake update
lake build
lake env lean --run Main.lean
```

`lake update` is only needed after the initial clone or when dependencies
change. The executable prints the concrete three-model ensemble result together
with the earlier exact-bisection example.

## Layout

```text
CertifiedBisectionLean/
├── BinaryCrossEntropy.lean  # BCE, binary entropy, and Bernoulli KL
├── GaussianEstimator.lean   # unbiased Gaussian ensembles and optimal weights
├── Interval.lean            # exact rational bisection
└── SqrtTwo.lean             # concrete √2 certificate
Main.lean                    # small executable summary
```

## Verification

`lake build` checks every declaration. The project currently contains no
`sorry`, `admit`, or project-defined axioms. GitHub Actions runs the same Lean
build on each push.
