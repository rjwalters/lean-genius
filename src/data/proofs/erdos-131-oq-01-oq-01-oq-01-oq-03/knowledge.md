# Erdős #131 — Exact Cyclic Davenport Constant `D(ℤ/nℤ) = n`

**Slug:** `erdos-131-oq-01-oq-01-oq-01-oq-03`
**File:** `proofs/Proofs/Erdos131DavenportConstant.lean`
**Status:** verified · 0 axioms · 0 sorries · 6 theorems · 1 definition · 170 lines

## Summary

The **Davenport constant** `D(G)` of a finite abelian group `G` is the least `d`
such that every length-`d` sequence over `G` has a nonempty zero-sum subsequence.
This entry proves the classical cyclic value **`D(ℤ/nℤ) = n`** exactly and
axiom-free, packaged as

```
davenport_constant_cyclic : IsLeast {m | ∀ f : Fin m → ZMod n, HasZeroSumSubseq f} n
```

Mathlib has the Erdős–Ginzburg–Ziv constant `s(ℤ/nℤ) = 2n − 1` but **not** the
Davenport constant, so this is built from scratch.

## Relation to the companion (`erdos-131-oq-01-oq-01-oq-01`)

The companion EGZ-sharpening entry proved only the **upper bound** `D ≤ a`, and
only in the **integer-divisibility form for distinct naturals**
(`exists_nonempty_subset_sum_dvd` over `Finset ℕ`), using it to sharpen the
non-dividing set bound to `|A| ≤ a + 1`. This entry:

1. Proves the upper bound for **arbitrary `ZMod n` sequences** (with repeats) —
   the genuine Davenport setting (`davenport_upper`).
2. Adds the **matching lower bound** (`davenport_no_zerosum_const_one`): the
   constant-`1` sequence of length `< n` is zero-sum-free, so `n` is sharp.
3. Packages the exact value as `IsLeast` and extracts uniqueness.

## Proof sketch

- **Upper (`davenport_upper`).** For `f : Fin m → ZMod n` with `n ≤ m`, the `m+1`
  prefix sums `P k = ∑_{i.val < k} f i` lie in the `n`-element type `ZMod n`. Since
  `n < m+1`, `Fintype.exists_ne_map_eq_of_card_lt` collides two indices `p < q`.
  The index interval `[p,q)` then has sum `0` — obtained by splitting the prefix
  filter `[0,q) = [0,p) ⊔ [p,q)` (disjoint, `Finset.sum_union`) and cancelling —
  and is nonempty (contains `p`, since `p < q ≤ m`).
- **Lower (`davenport_no_zerosum_const_one`).** A nonempty `s ⊆ Fin m` for the
  constant-`1` sequence sums to `(s.card : ZMod n)`. With `1 ≤ s.card ≤ m < n`,
  `ZMod.natCast_eq_zero_iff` (n ∤ k for `0 < k < n`) gives sum `≠ 0`.

## Key Lean gotchas (Mathlib v4.26.0)

- `self_eq_add_right` is **not** a usable identifier here — to get `block = 0`
  from `prefix = prefix + block`, use `linear_combination -hsplit` (ZMod n is a
  CommRing).
- Deriving `NeZero n` from `hmn : m < n` via `⟨by omega⟩` makes a separate
  `hn : 1 ≤ n` hypothesis **unused** (linter error in verified entries) — drop it.
- The prefix split is cleanest via an explicit `ext i; … ; omega` Finset equality
  plus `Finset.disjoint_left` + `omega`, then `Finset.sum_union`.
- `ZMod.natCast_eq_zero_iff _ _ : (k : ZMod n) = 0 ↔ n ∣ k` (not `…_zmod_…`).

## Open questions generated

1. **(high)** Lift the prefix-sum pigeonhole to the rank-2 group
   `D(ℤ/n₁ ⊕ ℤ/n₂) = n₁ + n₂ − 1` by an elementary axiom-free argument.
2. **(medium)** Does the *set* (distinct-element) zero-sum threshold differ from
   the *sequence* Davenport constant `n`?

## Session log

### 2026-06-21 (FRESH follow-up, REVISIT-mode session) — completed
- Pool had 0 available; chose to ship a strong self-contained follow-up to the
  just-merged Davenport sharpening (PR #27284).
- Wrote, built (docker, warm cache, clean), and packaged the exact cyclic
  Davenport constant. 0-axiom verified.
- Files: `proofs/Proofs/Erdos131DavenportConstant.lean`,
  `src/data/proofs/erdos-131-oq-01-oq-01-oq-01-oq-03/{meta.json,knowledge.md}`.
