# MathFormulations

Formal proofs in **Lean 4** with **Mathlib**, covering classic results from number theory, algebra and mathematical physics. Every theorem here is machine-checked: if the project builds, the proofs are valid.

## Contents

| File | Result | Main theorem |
|------|--------|--------------|
| [`SumNat.lean`](MathFormulations/SumNat.lean) | Sum of the first *n* natural numbers: ∑ᵢ₌₀ⁿ i = n(n+1)/2 | `sumFirstN_two_mul` |
| [`SqrtTwoIrrational.lean`](MathFormulations/SqrtTwoIrrational.lean) | Irrationality of √2: no coprime naturals *m, n* (n > 0) satisfy m² = 2n² | `sqrt2_not_coprime_sq` |
| [`EuclidPrimes.lean`](MathFormulations/EuclidPrimes.lean) | Euclid's theorem: there are infinitely many primes | `exists_prime_greater_than` |
| [`HarmonicOscillator.lean`](MathFormulations/HarmonicOscillator.lean) | Energy conservation for the 1D harmonic oscillator: dE/dt = 0 | `energy_conserved` |

### Notes on each proof

- **Sum of naturals.** Stated in the division-free form `2 * sumFirstN n = n * (n + 1)` to avoid natural-number truncation. Proved by induction on `n`.
- **√2 is irrational.** Proved by contradiction: if m² = 2n², then m is even, so n is even too, contradicting coprimality.
- **Infinitely many primes.** For any `n`, a prime factor of `n! + 1` must exceed `n`.
- **Harmonic oscillator.** With `m·v'(t) + k·x(t) = 0`, the energy `E = ½mv² + ½kx²` has derivative zero. Uses `HasDerivAt` from Mathlib's calculus library and requires `m ≠ 0`.

## Building the project

You need [Lean 4 via elan](https://lean-lang.org/install/) and Git.

```bash
git clone https://github.com/Fiddo-tech/MathFormulations.git
cd MathFormulations
lake exe cache get   # download prebuilt Mathlib (saves hours of compiling)
lake build
```

A successful run ends with `Build completed successfully`.

To explore the proofs interactively, open the folder in VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) and open any `.lean` file. The infoview panel shows the proof state at your cursor.

## Project layout

```
MathFormulations/
├── MathFormulations.lean        # root file, imports all four modules
├── MathFormulations/
│   ├── SumNat.lean
│   ├── SqrtTwoIrrational.lean
│   ├── EuclidPrimes.lean
│   └── HarmonicOscillator.lean
├── lakefile.toml                # project and Mathlib dependency config
└── lean-toolchain               # pinned Lean version
```

## Author

Built by **Fiddo** as a Lean 4 proof portfolio.
