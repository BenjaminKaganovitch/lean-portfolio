# Lean portfolio

[![build](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml/badge.svg)](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml)

Small Lean 4 files against Mathlib. Each math file proves a naive formalization wrong
or vacuous, then proves the corrected theorem. Each LeetCode file implements the
algorithm, proves it meets a full spec, and exhibits a wrong implementation that meets a
weaker spec. Design notes are in each file's module docstring.

Built with AI assistance (Claude). Every proof compiles at the pinned commit with no sorry and standard axioms only.

## Math

- `LeanPortfolio/NumberTheory.lean`: if `1 ≤ n` and `n ∣ 2 ^ n - 1` then `n = 1`. The
  version without `1 ≤ n` fails at `n = 0`.
- `LeanPortfolio/OrderTheory.lean`: a monotone bijection of a finite poset is an order
  isomorphism. Without finiteness it fails on an explicit order on a copy of `ℤ`.
- `LeanPortfolio/Analysis.lean`: if `|f x - f y| ≤ (x - y) ^ 2` for all real `x, y` then
  `f` is constant. With `x - y ^ 2` the statement is provable only because its hypothesis
  never holds.

## Verified LeetCode

- `LeanPortfolio/LeetCode/TwoSum.lean` (LeetCode 1): quadratic search over pairs. The
  weak spec allows `i = j`, so pairing an element with itself passes.
- `LeanPortfolio/LeetCode/BinarySearch.lean` (LeetCode 704): binary search on a sorted
  array. The weak spec only checks returned indices, so always returning `none` passes.
  The spec checks only input/output behavior; the O(log n) requirement is not verified.
- `LeanPortfolio/LeetCode/MaxSubarray.lean` (LeetCode 53): Kadane's recurrence. The weak
  spec only asks for the sum of some subarray, so returning the first element passes.
- `LeanPortfolio/LeetCode/ValidParentheses.lean` (LeetCode 20): stack scan, proved
  against a grammar over three bracket types, so `(]` is rejected. The weak spec only
  compares bracket counts, so `)(` passes.

Each file ends with `#print axioms` for its main results; every list is a subset of
`propext`, `Classical.choice` and `Quot.sound`.

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

`lake exe cache get` downloads prebuilt Mathlib, so only this repository's files are
compiled. The axiom output appears as info messages. To check one file, run
`lake env lean LeanPortfolio/NumberTheory.lean`.

CI runs the same steps on every push and fails if any `.lean` file contains `sorry`.
