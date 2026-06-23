# S3b PREP — Klein-4 case `q = 8` via quadratic-residue refinement of the Euclid construction

**Date**: 2026-05-13 (~03:55 UTC)
**Researcher**: researcher-9
**Mode**: PREP (doc-only — does not modify any `.lean`, `.json`, `state.md`, `knowledge.md`, or `problem.md`)
**Status**: pristine new sessions file. Companion to the merged S3 PREP for `q ∈ {3, 4, 6}` Klein-2 cases (researcher-10, `2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`) — addresses the explicit "defers q ∈ {8, 12, 24} to a separate S3b PREP" sentence in §"Why q ∈ {8, 12, 24} is harder".

## Purpose

The merged S3 PREP (researcher-10, ~80 min ago at push time) covers
parametric `infinitely_many_primes_neg1_mod_q` for `q ∈ {3, 4, 6}`,
which are the **clean Klein-2** cases where `(ℤ/q)ˣ ≅ ℤ/2`. It
explicitly defers the harder `q ∈ {8, 12, 24}` cases to S3b. This
PREP addresses **`q = 8` specifically** — the simplest Klein-4 case
— with:

1. A pinpointed obstruction analysis (why the Klein-2 argument fails).
2. A Mathlib v4.26.0 API audit for the quadratic-residue tools needed
   (verified verbatim against pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
3. A concrete classical construction `N = (4 · ∏ p_i)² − 2` that
   isolates primes ≡ 7 (mod 8).
4. A LOC estimate and dependency graph for the S3b ACT.

The cases `q ∈ {12, 24}` are sketched only briefly in §6 and left for
S3c PREP — they require strictly more machinery (e.g., simultaneous
quadratic-residue constraints at two distinct prime moduli of `q`).

## 1. The obstruction for q = 8

For `q = 8`, `(ℤ/8)ˣ = {1, 3, 5, 7}` has order 4, isomorphic to the
Klein four-group `K₄ = ℤ/2 × ℤ/2`. The Klein-2 dichotomy
"`p ≢ 1 ⇒ p ≡ -1`" used in the S3 PREP for `q ∈ {3, 4, 6}` **fails**
for `q = 8`: a prime coprime to 8 with `p ≢ 1 (mod 8)` could be
`p ≡ 3`, `5`, or `7 (mod 8)`. Only `p ≡ 7 (mod 8)` is the target
`p ≡ -1 (mod 8)`.

The straightforward Euclid-style construction
`N = 8 · ∏ p_i − 1` (where `p_i` are the assumed-finite primes ≡ 7
(mod 8)) yields `N ≡ -1 ≡ 7 (mod 8)`. **However**, `N` having a
prime factor `p ≡ 7 (mod 8)` does not follow from `N ≡ 7 (mod 8)`
alone — `N`'s prime factorisation could entirely consist of primes
`≡ 3` and `5` (mod 8), since `3 · 5 = 15 ≡ 7 (mod 8)`.

**Concrete counterexample at small scale**: `N = 15 = 3 · 5`,
`15 ≡ 7 (mod 8)`, but neither prime factor is `≡ 7 (mod 8)`. So
the construction has a genuine logical gap for `q = 8`.

## 2. Mathlib v4.26.0 quadratic-residue API audit

At the pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`
ships the following (verified via `gh api repos/...contents`):

| Line | Identifier | Statement (paraphrased) |
|---|---|---|
| 60 | `legendreSym.at_two` | `legendreSym p 2 = χ₈ p` (for odd `p`) |
| 65 | `legendreSym.at_neg_two` | `legendreSym p (-2) = χ₈' p` (for odd `p`) |
| **74** | **`exists_sq_eq_two_iff`** | **`IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7`** |
| 80 | `exists_sq_eq_neg_two_iff` | `IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3` |
| 107 | `quadratic_reciprocity` | `(p/q) · (q/p) = (-1) ^ ((p-1)/2 · (q-1)/2)` |
| 156 | `exists_sq_eq_prime_iff_of_mod_four_eq_one` | `IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q)` when `p ≡ 1 (mod 4)` |

**Key load-bearing theorem for the q = 8 construction**:
`exists_sq_eq_two_iff` (line 74) — states that 2 is a square modulo
an odd prime `p` if and only if `p ≡ 1` or `7 (mod 8)`. This is the
**dichotomy generator** for the construction: by selecting an `N`
whose prime factors must all satisfy `IsSquare 2 (mod p)`, we
restrict them to the two residues `{1, 7} (mod 8)`, and a parity
argument forces at least one prime factor to be `≡ 7`.

**Verification command** (verifies the line and statement verbatim):

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | sed -n '70,90p'
```

returns (with `theorem` heading at line 74):

```lean
theorem exists_sq_eq_two_iff (hp : p ≠ 2) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  ...
```

## 3. Classical construction for `p ≡ -1 (mod 8)`

The classical elementary infinitude argument for primes `≡ -1 (mod 8)`
uses the form `N = (4 · ∏ p_i)² − 2`. The proof structure:

### Step 1 — All odd prime factors `p` of `N` satisfy `2 ≡ (4 · ∏ p_i)² (mod p)`.

If `p | N` and `p` is odd, then `(4 · ∏ p_i)² ≡ 2 (mod p)`, so 2 is a
quadratic residue modulo `p`. By `exists_sq_eq_two_iff`:

```
p % 8 = 1  ∨  p % 8 = 7.
```

Hence every odd prime factor of `N` is `≡ 1` or `≡ 7 (mod 8)`.

### Step 2 — `N` is odd, so `N`'s prime factorisation contains only odd primes.

`N = (4 · ∏ p_i)² − 2`. `(4 · ∏ p_i)² = 16 · (∏ p_i)²`, which is
divisible by 4 (in fact by 16). So `N ≡ -2 (mod 4)`, i.e. `N ≡ 2 (mod 4)`.
This gives `N = 2 · M` for some odd `M`. So the prime factorisation
of `N` has exactly one factor of 2, and the rest are odd. The "rest"
(i.e., `M = N/2`) is the load-bearing object.

Actually `M = (8 · (∏ p_i)²) − 1`, so `M ≡ -1 ≡ 7 (mod 8)`. The
odd prime factors of `M` all satisfy Step 1's restriction:
`p % 8 ∈ {1, 7}`.

### Step 3 — Some odd prime factor of `M` is `≡ 7 (mod 8)`.

`M ≡ 7 (mod 8)`. Suppose all odd prime factors of `M` were `≡ 1
(mod 8)`. Then their product would be `≡ 1 (mod 8)`, contradicting
`M ≡ 7 (mod 8)`. So at least one prime factor `p` of `M` is `≡ 7
(mod 8)`, which is `≡ -1 (mod 8)`.

### Step 4 — `p` is not in the original list.

If `p = p_i` for some `i`, then `p | ∏ p_i`, so `p | (4 · ∏ p_i)²`,
so `p | (4 · ∏ p_i)² − N = 2`. But `p ≡ 7 (mod 8)` so `p` is odd
and at least 7. Contradiction.

So we've constructed a new prime `≡ -1 (mod 8)` outside the
finite list — concluding the proof by contradiction.

## 4. Lean blueprint for S3b ACT

The S3b ACT target lemma:

```lean
namespace InfinitudePrimes4k3OQ01.ModEight

open Nat ZMod in
/-- Infinitude of primes ≡ 7 (mod 8) via the (4∏)² - 2 construction
    and `exists_sq_eq_two_iff`. -/
theorem infinitely_many_primes_neg1_mod_8 :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 8 = 7) →
      ∃ q, q.Prime ∧ q % 8 = 7 ∧ q ∉ S := by
  intro S hS
  -- Step A: form N = (4 · ∏ S)² - 2.
  set a := 4 * S.prod id with ha
  set N := a^2 - 2 with hN
  -- Step B: extract some odd prime factor p of N.
  -- Step C: 2 is a square mod p, so p % 8 ∈ {1, 7} by exists_sq_eq_two_iff.
  -- Step D: at least one such factor is ≡ 7 by the parity argument.
  -- Step E: that p is not in S.
  sorry  -- ~80 LOC, mechanical from steps 1-4 above
```

**Companion lemma — extraction of the parity argument**:

```lean
/-- If `M ≡ 7 (mod 8)` and all prime divisors of `M` are `≡ 1` or
    `≡ 7 (mod 8)`, then at least one prime divisor is `≡ 7 (mod 8)`. -/
lemma exists_prime_dvd_mod_eight_eq_seven
    {M : ℕ} (hM : M % 8 = 7)
    (h : ∀ p, p.Prime → p ∣ M → p % 8 = 1 ∨ p % 8 = 7) :
    ∃ p, p.Prime ∧ p ∣ M ∧ p % 8 = 7 := by
  -- Proof by contradiction: if all prime factors ≡ 1, then M ≡ 1.
  -- ~20 LOC via Nat.Prime.factorization + product mod 8.
  sorry
```

**Mathlib API used**:

- `ZMod.IsSquare.of_dvd` / `IsSquare.dvd` / `ZMod.sq_eq_iff` —
  bridge between integer squaring and `ZMod p` squaring.
- `exists_sq_eq_two_iff` (line 74) — the quadratic-residue
  dichotomy.
- `Nat.Prime.factorization` / `Nat.prod_factorization_eq_prod_divisors`
  for the parity argument.
- `Nat.Coprime.factorization_mul` for the not-in-S step.

**Total LOC estimate for the q = 8 case**: ~150 (vs ~100 for each
of `q ∈ {3, 4, 6}` in the merged Klein-2 PREP).

## 5. Dependency graph for S3b ACT

```
infinitely_many_primes_neg1_mod_8       [S3b ACT, ~80 LOC body]
    ├── exists_prime_dvd_mod_eight_eq_seven [companion lemma, ~20 LOC]
    │       └── Nat.Prime.factorization + prod mod 8 + omega
    │
    ├── exists_sq_eq_two_iff       [Mathlib v4.26.0 line 74]
    │
    ├── Nat.Prime.dvd_of_dvd_pow   [Mathlib (standard)]
    │
    ├── Nat.exists_prime_dvd       [Mathlib (standard, for M ≥ 2)]
    │
    └── 2 ≤ N positivity           [via S.prod id ≥ 1 + arithmetic]
```

## 6. Why `q ∈ {12, 24}` need a strictly separate PREP

For `q = 12`: `(ℤ/12)ˣ = {1, 5, 7, 11}` (Klein-4). The CRT
isomorphism `ℤ/12 ≅ ℤ/4 × ℤ/3` reveals the structure: `p ≡ 11 (mod 12)`
iff `p ≡ 3 (mod 4) ∧ p ≡ 2 (mod 3)`. The Klein-2 argument for `q = 3`
gives infinitely many primes `≡ 2 (mod 3)`; the Klein-2 argument for
`q = 4` gives infinitely many `≡ 3 (mod 4)`. **But the intersection
is not automatically infinite** — to combine, one needs a single
construction whose prime factors satisfy BOTH constraints.

The classical construction: `N = 12 · ∏ p_i − 1`, which forces
`N ≡ 11 (mod 12)`. But again, this doesn't force any specific prime
factor to be `≡ 11`. A two-character constraint via simultaneous
quadratic-residue conditions modulo `3` and modulo `4` is the
standard fix; this is a "Klein-4 with two CRT-decomposed Klein-2
projections" pattern that warrants its own PREP.

For `q = 24`: `(ℤ/24)ˣ` has order 8 = φ(24) = φ(8)·φ(3) = 4 · 2, with
structure `K₄ × ℤ/2` — strictly larger than Klein-4. The construction
needs three simultaneous quadratic-residue conditions (one for each
prime power in 24's factorisation: 8 = 2³, 3). Even more delicate.

Recommendation: **defer `q ∈ {12, 24}` to a separate S3c PREP**.
The combinatorial complexity grows quickly and a single PREP per
"hard" modulus is the right granularity.

## 7. Self-audit and honesty boundary

This PREP is **doc-only**. It produces:

- 0 Lean changes.
- 0 sorry deltas.
- 0 axiom changes.
- 0 edits to existing files (no `state.md`, `problem.md`,
  `knowledge.md`, `src/data/...` modifications).
- 1 new file: `sessions/2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`.

The mathematical content (steps 1-4 of §3) is the classical
construction taught in undergraduate number theory; I have not
invented anything. The **Lean blueprint of §4** is a typed
translation of the construction with the Mathlib API connections
explicit. The S3b ACT agent can use the blueprint verbatim,
filling in the two strategic sorries with ~80 + ~20 = ~100 LOC of
mechanical tactic work.

**Build cost**: 0. **Race risk**: 0 (new filename in `sessions/`,
no edits to anything else).

## 8. Race awareness

Push time: 2026-05-13 ~03:55 UTC.

- `gh pr list --search "infinitude-primes-4k3-oq-01 in:title" --state open --repo rjwalters/lean-genius` → empty (verified).
- Last merge on this slug: PR #18490 (S2(c) PREP, doc-only) at 03:07:21Z — ~48 min ago, outside the 30-min-post-merge window.
- File path is unique: `sessions/2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`.

## 9. What this PREP does NOT decide

1. **Whether to ship a `q = 8` Lean file as a separate
   `InfinitudePrimes4k3OQ01ModEight.lean`** or extend the existing
   `InfinitudePrimes4k3OQ01.lean`. Recommendation: separate file,
   since the dependency on Mathlib's `QuadraticReciprocity` is a
   strictly new import not needed for the q = 4 case.
2. **The exact `M` parity-argument formalisation**. Two routes: (i)
   work via `Nat.factorization` (the standard Mathlib approach for
   prime factorisation), or (ii) work via `Multiset` of prime factors
   from `Nat.factors`. The latter is more elementary but less
   well-supported by `simp` lemmas. Decision deferred to S3b ACT.
3. **Whether to also ship the `q = 8` case for `≡ 1 (mod 8)`,
   `≡ 3 (mod 8)`, `≡ 5 (mod 8)`** as companion theorems. These use
   analogous constructions (`(4 · ∏)² + 2` for `≡ 1, 3`,
   `(4 · ∏)² + 4` for `≡ 1, 5` etc., via
   `exists_sq_eq_neg_two_iff` and related). They are not required
   by the slug's goal (`≡ -1 (mod 8)`) but are natural by-products
   and would round out the gallery's coverage of `q = 8` residue
   classes. Decision deferred to S3b ACT planning.

## 10. References

- `proofs/Proofs/InfinitudePrimes4k3.lean:154` —
  `infinitely_many_primes_3_mod_4` (parent, the `q = 4` case
  template).
- `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` — S2 ACT bridge
  corollary (researcher-12, merged PR #18341).
- `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`
  — S3 PREP for Klein-2 `q ∈ {3, 4, 6}` (researcher-10, merged
  PR #18426, ~80 min ago).
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity:74` —
  `exists_sq_eq_two_iff`.
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity:80` —
  `exists_sq_eq_neg_two_iff` (used in the deferred `≡ 3 (mod 8)`
  variant).

---

**End of S3b PREP — no Lean changes, no gallery changes, no state
changes. New entry in the `sessions/` subdirectory.**
