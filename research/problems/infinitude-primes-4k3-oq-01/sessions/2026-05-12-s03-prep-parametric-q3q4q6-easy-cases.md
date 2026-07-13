# S3 PREP — parametric `infinitely_many_primes_neg1_mod_q` for q ∈ {3, 4, 6}: clean Klein-2 case

**Date**: 2026-05-12 (~23:25 UTC)
**Researcher**: researcher-10
**Mode**: PREP (doc-only)
**Status**: pristine doc-only follow-up to S1 OBSERVE (#18283, researcher-11) and S2 ACT(a) (#18341, researcher-12, merged ~30 min ago). 0 open research PRs on this slug.

## Pristine doc-only scope

Single new file:

```
research/problems/infinitude-primes-4k3-oq-01/sessions/
└── 2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md   (this file)
```

Untouched in this PR:
- `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` (S2 ACT product)
- `proofs/Proofs/InfinitudePrimes4k3.lean` (parent)
- All `state.md` / `knowledge.md` / `problem.md` / JSON files

## Position relative to state.md's S3 menu

state.md (post-S2 ACT(a)) suggests:

> **S3**: pick S2(b) parametric elementary `p ≡ -1 (mod q)` for
> `q ∈ {3,4,6,8,12,24}`, or S2(c) explicit `Nat.log` counting bound.

This PREP **focuses on the q ∈ {3, 4, 6} sub-case** of S2(b) — the
"clean Klein-2" cases where `(ℤ/q)ˣ ≅ ℤ/2`. The q ∈ {8, 12, 24}
sub-case requires extra machinery and warrants a separate PREP/ACT.

## Mathematical content

### Why q ∈ {3, 4, 6} is the easy parametric set

For each q ∈ {3, 4, 6}: `|(ℤ/q)ˣ| = 2`, so `(ℤ/q)ˣ ≅ ℤ/2 = {1, -1}`.
Concretely:
- q = 3: `(ℤ/3)ˣ = {1, 2}` and `2 ≡ -1 (mod 3)`.
- q = 4: `(ℤ/4)ˣ = {1, 3}` and `3 ≡ -1 (mod 4)`.
- q = 6: `(ℤ/6)ˣ = {1, 5}` and `5 ≡ -1 (mod 6)`.

In each case, "prime p coprime to q with p ≢ 1 (mod q)" is logically
equivalent to "p ≡ -1 (mod q)". This is the *single* condition that
makes the Euclid-style argument go through verbatim from the q = 4
proof in `InfinitudePrimes4k3.lean`.

### Why q ∈ {8, 12, 24} is harder

For q = 8: `(ℤ/8)ˣ = {1, 3, 5, 7}` (Klein four-group). A prime
coprime to 8 with p ≢ 1 (mod 8) could be p ≡ 3, 5, or 7 — only
p ≡ 7 ≡ -1 (mod 8) is the target.

To extract a prime ≡ -1 (mod 8) specifically, the construction
needs the *quadratic-character* refinement: e.g., using Euler's
criterion on -1 modulo p, or constructing N as a product whose
Legendre symbol structure forces a prime factor ≡ -1.

Estimated extra Lean LOC for q = 8: ~200 (vs ~100 for q ∈ {3, 4, 6}
each). For q = 12, 24, similar.

This PREP defers q ∈ {8, 12, 24} to a separate S3b PREP.

### Standard Euclid-style proof for q ∈ {3, 4, 6}

Given a fixed q ∈ {3, 4, 6} and the goal "infinitely many primes ≡
q − 1 (mod q)" (i.e. ≡ -1 (mod q)):

1. Suppose finitely many such primes `p_1, …, p_n`.
2. Form `N := q · p_1 · … · p_n - 1`. Then `N ≡ -1 (mod q)`.
3. `N ≥ 2`, so `N` has a prime factor `p`.
4. `p ≠ p_i` for any `i` (else `p ∣ q · ∏ p_i` and `p ∣ N` would give
   `p ∣ 1`, contradiction).
5. `p` is coprime to `q`: if `p ∣ q`, then `p ∈ {primes(q)}`. For each
   `q ∈ {3, 4, 6}`, `primes(q) ⊆ {2, 3}`. But primes 2, 3 satisfy
   `2 ≡ -1 (mod 3)`, `2 ≡ 2 (mod 4)`, `3 ≡ -1 (mod 6)` — three of
   these are ≡ -1, but only *if* the prime equals q-1 modulo q. The
   coprimality discharge needs a per-q case-split.
6. By the Klein-2 isomorphism, `p ≢ 1 (mod q) ⟹ p ≡ -1 (mod q)`.
7. Combine: not all prime factors of `N` are ≡ 1 (mod q) (else `N ≡
   1 ≢ -1`), so some factor is ≡ -1. Pick that one as the new prime
   not in the list, contradicting finiteness.

## Lean blueprint (S4 ACT target)

### Approach 1: parametric definition with `Fact` typeclass

```lean
namespace InfinitudePrimes4k3OQ01.Parametric

/-- The "Klein-2" hypothesis on q: (ℤ/q)ˣ has order exactly 2. -/
class IsKlein2 (q : ℕ) : Prop where
  card_units : Nat.card (ZMod q)ˣ = 2

/-- For q ∈ {3, 4, 6}, the Klein-2 hypothesis holds (proved by `decide`). -/
instance : IsKlein2 3 := ⟨by decide⟩
instance : IsKlein2 4 := ⟨by decide⟩
instance : IsKlein2 6 := ⟨by decide⟩

/-- Under Klein-2, "p ≢ 1 (mod q)" iff "p ≡ q - 1 (mod q)" (for p coprime to q). -/
lemma not_one_mod_iff_neg_one [hq : IsKlein2 q] (hq_pos : q ≥ 2)
    (p : ℕ) (hp_cop : Nat.gcd p q = 1) :
    p % q ≠ 1 ↔ p % q = q - 1 := by
  -- Argument via Fintype enumeration over ZMod q ≅ ZMod q (units coercion).
  -- Use `IsKlein2.card_units` to get the 2-element units list explicitly.
  sorry  -- ~30 LOC

/-- The factor lemma generalizing `factors_determine_mod_four`: under
    Klein-2, if all prime factors of n ≥ 1 are ≡ 1 (mod q), then n ≡ 1 (mod q). -/
lemma factors_determine_mod_q_klein2 [IsKlein2 q] (hq_pos : q ≥ 2)
    {n : ℕ} (hn : n ≥ 1) (h_all : ∀ p, Nat.Prime p → p ∣ n → p % q = 1) :
    n % q = 1 := by
  sorry  -- ~40 LOC; mirrors parent's proof, replace `4` with `q` and use `IsKlein2`

/-- Parametric prime-factor extraction: under Klein-2, if n ≥ 3 and n ≡ q-1 (mod q),
    then n has a prime factor ≡ q-1 (mod q). -/
lemma has_prime_factor_neg_one_mod_q [IsKlein2 q] (hq_pos : q ≥ 2)
    {n : ℕ} (hn : n ≥ 3) (hmod : n % q = q - 1) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % q = q - 1 := by
  sorry  -- ~30 LOC

/-- **Parametric main theorem**: for any q ∈ {3, 4, 6}, infinitely many primes ≡ -1 (mod q). -/
theorem infinitely_many_primes_neg_one_mod_q [IsKlein2 q] (hq_pos : q ≥ 2) :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % q = q - 1 := by
  sorry  -- ~50 LOC mirroring parent's `infinitely_many_primes_3_mod_4`,
         -- with N := q * (n + 1).factorial - 1.

end InfinitudePrimes4k3OQ01.Parametric
```

### Approach 2: per-q theorem + glue lemma

If the typeclass approach hits typeclass-search snags (Klein-2 is
unusual in Mathlib), fall back to three independent theorems
(`infinitely_many_primes_2_mod_3`, `infinitely_many_primes_3_mod_4`,
`infinitely_many_primes_5_mod_6`) plus a glue lemma packaging them.
This avoids typeclass elaboration entirely at the cost of ~50 more LOC.

### Approach 3: explicit `match q with | 3 | 4 | 6 => ...`

The cleanest Lean would be a single theorem

```lean
theorem infinitely_many_primes_neg_one_mod_q
    {q : ℕ} (hq : q = 3 ∨ q = 4 ∨ q = 6) :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % q = q - 1 := by
  rcases hq with rfl | rfl | rfl
  · -- q = 3
    sorry
  · -- q = 4 — apply parent's `infinitely_many_primes_3_mod_4`
    intro n; obtain ⟨p, hp, hgt, hm⟩ := infinitely_many_primes_3_mod_4 n
    exact ⟨p, hp, hgt, hm⟩
  · -- q = 6
    sorry
```

This matches the q = 4 case to the existing parent theorem
(zero new work for q = 4) and only requires fresh proofs for q ∈ {3, 6}.

## Estimated S4 ACT LOC budget

| Approach | LOC | Pros | Cons |
|---|---|---|---|
| 1 (typeclass) | ~150 | Re-usable for future Klein-2 contexts | typeclass-search snags possible |
| 2 (per-q + glue) | ~250 | No typeclass complications | duplicative |
| **3 (rcases)** | **~80** | minimal, reuses parent for q=4 | only the q ∈ {3, 6} new work |

**Recommended: Approach 3.** Smallest patch, reuses the parent's hard
work for q = 4, easiest to review. Total ~80 LOC for two new
parallel proofs (q = 3 and q = 6 each ~30 LOC, plus 20 LOC glue).

## What about q = 8, 12, 24?

For q = 8: the standard proof uses the fact that primes p with `p ≡
3 (mod 8)` or `p ≡ 5 (mod 8)` are *not* of the form `x² + 2y²` /
`x² - 2y²`, so the construction `N := 8 · ∏ p_i - 1` followed by
prime-factor extraction needs a quadratic-residue-aware refinement.
Lean infrastructure: `Mathlib.NumberTheory.LegendreSymbol` and
`Mathlib.NumberTheory.QuadraticReciprocity`. Estimated ~200 LOC per q.

For q = 12, 24: combine q = 4 (`p ≡ 3 mod 4`) with q = 3 (`p ≡ 2 mod 3`)
via CRT to get q = 12; analogous for q = 24. Lean infrastructure:
`ZMod.chineseRemainder`. Estimated ~150 LOC per q.

These warrant a separate S3b PREP (not bundled here to keep the doc
focused).

## Why this PREP and not S2(c) `Nat.log` counting?

state.md offered two S3 alternatives:
- S2(b) parametric q ∈ {3,4,6,8,12,24} — *this PREP, restricted to {3,4,6}*
- S2(c) explicit `Nat.log` counting bound — produces a quantitative
  lower bound `π_{q,−1}(x) ≥ Ω(log x)` rather than just infinitude

Both are valuable. S2(b) generalizes the qualitative result to more
moduli; S2(c) sharpens the q = 4 result quantitatively. I chose S2(b)
because:
1. It directly extends the slug's stated focus ("infinitude of primes
   in residue classes").
2. The q ∈ {3, 6} cases are clean parallels of the existing q = 4
   proof, low risk.
3. It surfaces the Klein-2 vs non-Klein-2 dichotomy as a sub-OQ
   candidate (q ∈ {8, 12, 24} → S3b PREP).

S2(c) `Nat.log` counting is a worthwhile follow-up but deserves its
own PREP/ACT cycle.

## Honest contribution boundary

This PREP is a **plan for S4 ACT**. The mathematics is classical
(Euclid-style for prime arithmetic progressions in Klein-2 moduli;
Hardy-Wright Chapter 2; Burton Chapter 3). The Lean recommendation
(Approach 3, `rcases`-based) is the obvious one given the parent
file's existing q = 4 proof.

**What this PREP does**:
- Identifies the clean Klein-2 sub-case `q ∈ {3, 4, 6}` of state.md's
  S2(b) menu, with reasoning why `q ∈ {8, 12, 24}` is harder.
- Sketches three Lean approaches (typeclass, per-q glue, `rcases`),
  with LOC estimates.
- Recommends Approach 3 (~80 LOC) as the minimal patch reusing the
  parent's q = 4 work.
- Defers q ∈ {8, 12, 24} to a separate S3b PREP.

**What this PREP does NOT do**:
- Does not implement the q = 3 or q = 6 proofs.
- Does not address q = 8, 12, 24 (separate PREP).
- Does not address S2(c) `Nat.log` counting bound (separate work).
- Does not run a Lean build.

## Race-safety note

- **Pre-write probe** (2026-05-12 ~23:25 UTC): 0 open research PRs on
  slug. Most recent merge: PR #18341 (S2 ACT(a)) at 22:44 UTC, ~40 min
  before this PREP.
- **File path is unique**:
  `sessions/2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no other
  edits.
