# CertiBisect

CertiBisect is a small Lean 4 project that computes rational bounds for `√2`
with exact bisection and proves the result correct using Mathlib.

The project is also a compact experiment in MCP-assisted formalization: Codex
can inspect Lean diagnostics and proof goals through `lean-lsp-mcp`, while Lean
remains the final checker for every theorem.

## Status

**Verified MVP complete.** The project builds without errors, warnings,
`sorry`, `admit`, or project-defined axioms.

## Result

Starting with the interval `[1, 2]`, ten exact bisection steps produce

```text
181 / 128 ≤ √2 ≤ 1449 / 1024
interval width = 1 / 1024
```

Running the demo prints:

```text
CertiBisect: certified rational bounds for sqrt(2)
lower = 181/128
upper = 1449/1024
width = 1/1024
Lean theorem: lower ≤ sqrt(2) ≤ upper
```

All interval calculations use rational numbers, so no floating-point rounding
is involved in the certificate.

## What is proved

| Claim | Lean declaration |
|---|---|
| One bisection step halves the interval width | `CertiBisect.Interval.width_step` |
| One step preserves the endpoint-square bracket around `2` | `CertiBisect.Interval.step_preserves_bracket` |
| Any number of steps preserves the bracket | `CertiBisect.Interval.iterate_preserves_bracket` |
| After `n` steps, the width is the initial width divided by `2^n` | `CertiBisect.Interval.width_iterate` |
| Ten steps yield exactly `[181/128, 1449/1024]` | `CertiBisect.sqrtTwoAfterTen_eq` |
| The ten-step interval has width `1/1024` | `CertiBisect.sqrtTwoAfterTen_width` |
| The rational endpoints genuinely bound the real number `√2` | `CertiBisect.sqrtTwoAfterTen_containsRoot` |

The final real-number statement is:

```lean
theorem sqrtTwoAfterTen_containsRoot :
    (181 : ℝ) / 128 ≤ Real.sqrt 2 ∧
      Real.sqrt 2 ≤ (1449 : ℝ) / 1024
```

## How it works

For an interval `[lower, upper]`, CertiBisect calculates the rational midpoint
`m` and checks `m² ≤ 2` exactly.

- If `m² ≤ 2`, the next interval is `[m, upper]`.
- Otherwise, the next interval is `[lower, m]`.

Lean proves that this update keeps `2` between the endpoint squares and cuts
the interval width in half. Induction then lifts both facts to any number of
iterations. The concrete ten-step result is finally connected to `Real.sqrt 2`.

## Requirements

- Lean `4.34.0`, managed with `elan`
- Lake `5.0.0`
- Mathlib `v4.34.0`

The repository's `lean-toolchain` and `lake-manifest.json` pin the required
versions.

## Build and run

From the repository root:

```bash
lake update
lake build
lake env lean --run Main.lean
```

`lake update` is only needed during initial setup or after dependency changes.

An optional native executable target is available as `certibisect`:

```bash
lake build certibisect
lake exe certibisect
```

The first native build may take considerably longer because Mathlib dependencies
need native code generation. The `lean --run` command is faster for this MVP.

## Project structure

```text
.
├── CertifiedBisectionLean/
│   ├── Basic.lean       # Environment smoke test
│   ├── Interval.lean    # Rational interval, bisection, and generic proofs
│   └── SqrtTwo.lean     # Concrete √2 certificate
├── CertifiedBisectionLean.lean
├── Main.lean            # Executable demonstration
├── lakefile.toml
└── lean-toolchain
```

## MCP-assisted workflow

The local Codex setup uses `lean-lsp-mcp` over STDIO. During the MVP it was
used to:

- read file diagnostics;
- inspect an induction proof goal;
- test alternative tactics without editing the file;
- rebuild the Lake project;
- scan key theorems for suspicious source patterns and report used axioms;
- run a standalone Lean smoke test.

The MCP server accelerates the edit-check loop, but it is not part of the
trusted proof result. The Lean source must still elaborate and pass Lean's
checker.

## Verification performed

- `lake build`: passed
- Lean diagnostics for all project files: 0 errors, 0 warnings
- source scan: no `sorry`, `admit`, or project-defined `axiom`
- executable demo: passed
- MCP theorem verification: no suspicious source warnings

## Current scope

This MVP intentionally specializes the algorithm to the equation `x² = 2` and
rational endpoints. Possible extensions include:

- generalizing from `2` to a positive rational constant `c`;
- supporting rational-coefficient polynomials;
- proving a generic bisection theorem for continuous real functions;
- recording a larger benchmark of MCP-assisted proof attempts.
