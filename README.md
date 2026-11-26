# MathFormulations

![Lean CI](https://github.com/FIddo-tech/MathFormulations/actions/workflows/lean_action_ci.yml/badge.svg)

Four short, self-contained formalizations in **Lean 4 + Mathlib**, written while learning
formal proof. Every file starts with `import Mathlib` and contains no `sorry`; the badge above
shows whether the current commit builds.

> **Scope.** All four results are classical and none is claimed to be new. Mathlib already
> contains versions of the first three. The aim is readable, documented proofs with a reproducible
> build.

## Contents

| File | Result | Main theorem |
|------|--------|--------------|
| `SumNat.lean` | Gauss: `2 * (0 + 1 + ... + n) = n * (n + 1)` (non-divisive form) | `sumFirstN_two_mul` |
| `SqrtTwoIrrational.lean` | No coprime `m, n` with `m^2 = 2 * n^2` (`√2` is irrational) | `sqrt2_not_coprime_sq` |
| `EuclidPrimes.lean` | For every `n` there is a prime `p > n` | `exists_prime_greater_than` |
| `HarmonicOscillator.lean` | Energy of the 1D harmonic oscillator has derivative `0` | `energy_conserved` |

### Notes on each proof

- **Sum of naturals.** Stated without division to avoid truncation in `ℕ`; proved by induction.
- **√2.** Parity descent over `ℕ`. A documented pitfall: `Even m` unfolds to `∃ r, m = r + r`, not
  `m = 2 * r`, so the proof converts to the `2 * k` form explicitly before using it.
- **Euclid.** Takes a prime factor of `n! + 1` and shows it must exceed `n`.
- **Harmonic oscillator.** Uses `HasDerivAt` with the hypotheses `x' = v`, `v' = -(k/m) x`, `m ≠ 0`.
  The statement is pointwise; constancy of `E` on all of `ℝ` (mean value theorem) and existence of
  solutions are not formalized.

## Build

Install [elan](https://github.com/leanprover/elan), then from the repository root:

```bash
lake update          # resolve dependencies (Mathlib)
lake exe cache get   # download the prebuilt Mathlib cache
lake build
```

The Lean toolchain is pinned in `lean-toolchain` and the Mathlib release tag (`v4.36.0-rc1`) in `lakefile.toml`.
Continuous integration (`.github/workflows/lean_action_ci.yml`) runs the same build on every push.

## Author

Confidence U. Oghosa

The Lean kernel, decides whether a proof is correct: a proof counts
only if `lake build` succeeds.
