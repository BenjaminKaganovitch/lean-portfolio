# Lean portfolio

[![build](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml/badge.svg)](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml)

Three small Lean 4 formalizations against Mathlib. Each file states an informal claim,
gives a naive formalization that is wrong or vacuous, proves that it is, and then proves
the corrected theorem. A module docstring in each file explains the design decisions.

Built with AI assistance (Claude). Every proof compiles at the pinned commit with no sorry and standard axioms only.

## Files

- `LeanPortfolio/NumberTheory.lean`: if `1 ≤ n` and `n ∣ 2 ^ n - 1` then `n = 1`. The
  version without `1 ≤ n` fails at `n = 0`.
- `LeanPortfolio/OrderTheory.lean`: a monotone bijection of a finite poset is an order
  isomorphism. Without finiteness it fails, shown with an explicit order on a copy of `ℤ`.
- `LeanPortfolio/Analysis.lean`: if `|f x - f y| ≤ (x - y) ^ 2` for all real `x, y` then
  `f` is constant. Writing `x - y ^ 2` instead gives a statement that is provable only
  because its hypothesis can never hold.

Each file ends with `#print axioms` for its theorems. The output lists only `propext`,
`Classical.choice` and `Quot.sound`.

## Versions

- Lean toolchain: `leanprover/lean4:v4.33.0-rc1` (see `lean-toolchain`)
- Mathlib: `9944fe2973b8dc0b86949101ed98232c07cd54a0` (see `lakefile.toml` and
  `lake-manifest.json`)

## Building

Install [elan](https://github.com/leanprover/elan), then:

```
git clone https://github.com/BenjaminKaganovitch/lean-portfolio.git
cd lean-portfolio
lake exe cache get
lake build
```

`lake exe cache get` downloads prebuilt Mathlib files, so the build only compiles the
three files here. The axiom output appears as info messages during `lake build`. To
check one file on its own, run `lake env lean LeanPortfolio/NumberTheory.lean`.

CI runs the same steps on every push and also fails if any `.lean` file contains `sorry`.
