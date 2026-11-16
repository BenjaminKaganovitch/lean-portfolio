# Lean portfolio

[![build](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml/badge.svg)](https://github.com/BenjaminKaganovitch/lean-portfolio/actions/workflows/build.yml)

Seven Lean 4 files built on Mathlib: three math formalizations and four verified LeetCode
problems.

In the math files I start from the statement as someone would naively write it, prove
that version false or vacuous, and then prove the corrected theorem. In the LeetCode
files I implement the algorithm, prove it meets a full spec, and then write a wrong
implementation that still passes a weaker spec, which shows the weaker spec is not
enough. The design notes for each file are in its module docstring.

I used AI assistance (Claude) to build this. Every proof compiles at the pinned commit
with no sorry and only the standard axioms.

## Math

- `LeanPortfolio/NumberTheory.lean`: if `1 ≤ n` and `n ∣ 2 ^ n - 1` then `n = 1`. Drop
  `1 ≤ n` and it fails at `n = 0`.
- `LeanPortfolio/OrderTheory.lean`: a monotone bijection from a finite poset to itself is
  an order isomorphism. Without finiteness the claim is false, and the counterexample is
  an explicit order on a copy of `ℤ`.
- `LeanPortfolio/Analysis.lean`: if `|f x - f y| ≤ (x - y) ^ 2` for all real `x, y` then
  `f` is constant. Writing `x - y ^ 2` instead, which Lean reads as `x - (y ^ 2)`, gives
  a statement that is still provable, but only because no `f` satisfies its hypothesis.

## Verified LeetCode

- `LeanPortfolio/LeetCode/TwoSum.lean` (LeetCode 1): brute-force search over all index
  pairs, not the hash map solution. The weak spec allows `i = j`, so an implementation
  can pair an element with itself and still pass it.
- `LeanPortfolio/LeetCode/BinarySearch.lean` (LeetCode 704): binary search on a sorted
  array. The weak spec only checks the indices that get returned, so always returning
  `none` passes. The spec covers input/output behavior only. I did not verify the
  O(log n) requirement.
- `LeanPortfolio/LeetCode/MaxSubarray.lean` (LeetCode 53): Kadane's recurrence. The weak
  spec only asks for the sum of some subarray, and returning the first element satisfies
  that.
- `LeanPortfolio/LeetCode/ValidParentheses.lean` (LeetCode 20): a stack scan, proved
  equivalent to a grammar over three bracket types, so `(]` is rejected. The weak spec
  still requires valid strings to be accepted, but asks accepted strings only to have
  matching counts of each bracket type, so a checker can accept `)(` and still pass it.

Each file ends with `#print axioms` for its main results. Every list is a subset of
`propext`, `Classical.choice` and `Quot.sound`. I did not verify running time in any
file.

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

`lake exe cache get` downloads prebuilt Mathlib, so only the files in this repository
get compiled. The axiom output shows up as info messages. To check a single file, run
`lake env lean LeanPortfolio/NumberTheory.lean`.

CI runs the same steps on every push and fails if any `.lean` file contains `sorry`.
