# Finding: exact Mathlib bearer for the G1 Dirichlet gate + why only the *qualitative* theorem is needed

**Session**: researcher-8, 2026-06-14 (Docker timed out; Aristotle `prove` → "Resource not found" — dual-backend blackout, build-free ORIENT only).
**Status**: ORIENT-sharpening. Resolves the deferred TODO in open PR #24149 ("confirm exact Mathlib names at build time" for the qualitative Dirichlet input). Path-disjoint: this is a NEW file, it does not touch `knowledge.md` / `state.md` / `verify_legendre_three_square.py`, all of which #24149 rewrites.

## Context

PR #24149 (S1 ORIENT, open) decomposes the open "if" direction of Legendre's three-square theorem
(`n ≠ 4^a(8b+7) ⟹ ∃ x y z, n = x²+y²+z²`) into:

- **D1+D2** — the Davenport–Cassels lemma (rational ⟹ integral representability for `x²+y²+z²`), *not* in Mathlib, recommended first deliverable (~150–260 LOC);
- **G1** — rational representability of admissible `n`, claimed to need *only the qualitative* Dirichlet theorem (one prime in an arithmetic progression), asserted to be "already in Mathlib" with names to be confirmed at build time.

This note (1) pins the exact Mathlib bearer for G1 with signatures, and (2) supplies the local-analysis reason *why* the qualitative theorem suffices — i.e. why no analytic density / PNT input is required.

## (1) The exact bearer — confirmed from Mathlib source

Mathlib pinned at `2df2f0150c27` (v4.26.0). The qualitative Dirichlet theorem lives in
**`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`** (namespace `Nat`). Verified present at that rev:

```lean
-- the cleanest form for G1 (Nat.ModEq, ℕ residue):
theorem Nat.forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ}
    (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q]

-- supporting / alternative forms in the same file:
theorem Nat.infinite_setOf_prime_and_eq_mod {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) : {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite
theorem Nat.forall_exists_prime_gt_and_eq_mod {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (n : ℕ) : ∃ p > n, p.Prime ∧ (p : ZMod q) = a
theorem Nat.forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ}
    (hq : q ≠ 0) (h : IsCoprime a q) : ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q]
lemma Nat.infinite_setOf_prime_and_modEq {q a : ℕ}
    (hq : q ≠ 0) (h : a.Coprime q) : {p : ℕ | p.Prime ∧ p ≡ a [MOD q]}.Infinite
```

(Note: the old name `Nat.setOf_prime_and_eq_mod_infinite` is now a `@[deprecated (since := "2025-11-01")]` alias of `Nat.infinite_setOf_prime_and_eq_mod` — use the new name.)

**ACT-relevant consequence.** The *only* side-condition any prime-in-AP step must discharge
before invoking `Nat.forall_exists_prime_gt_and_modEq` is the coprimality `Nat.Coprime a q`
of the chosen residue `a` to its modulus `q` (plus the trivial `q ≠ 0`). So #24149's claim
"qualitative Dirichlet, already in Mathlib" is **confirmed**, and the density/PNT version is
indeed *not* needed.

## (2) Why qualitative suffices — the local-obstruction structure

The reason only *existence of one prime* (not density) is needed is a local fact about the form
`Q(x,y,z) = x² + y² + z²`:

> **`Q` has no p-adic obstruction at any odd prime `p` (it is universal mod every odd prime
> power), and its sole local obstruction is at `p = 2`, where the non-represented residues are
> exactly the lifts of the classes `4^a(8b+7)`.**

Because no odd prime contributes a congruence condition, the construction of a rational point
needs to clear only the single 2-adic condition — achieved by producing *one* auxiliary prime in
a suitable coprime residue class and reducing to the two-square theorem (already in Mathlib via
`Nat.Prime.sq_add_sq` / `ZMod` Gaussian machinery). Hence: qualitative Dirichlet, not analytic.

This is verified (exact integer arithmetic) by
`scripts/verify_local_obstruction.py` — `ALL CHECKS PASSED`:

- **[A]** `{x²+y²+z² mod p^k} = ℤ/p^k` for `p ∈ {3,5,7,11,13}`, `k = 1..3` (odd-prime universality).
- **[B]** mod `2^k` (`k = 3..8`) the non-represented residues match exactly the excluded
  2-adic `4^a(8b+7)` classes.
- **[C]** for `n = 0..3000`, `Q` represents `n` over ℤ ⇔ `n` is **not** excluded — i.e. once the
  2-adic obstruction is absent, an integral solution exists and **no odd prime ever vetoes**.

## Recommended ACT order (unchanged from #24149, now with the gate named)

1. Formalize **D1+D2** (Davenport–Cassels rational⟹integral) — gate-free, buildable.
2. Formalize **G1** using `Nat.forall_exists_prime_gt_and_modEq`; the residue/modulus of the AP
   come from the case split on `n mod 8` (Serre, *Cours d'arithmétique*, Ch. IV §1.6 — the exact
   residue classes should be transcribed from a primary source at formalization time, **not**
   guessed). The lone Lean side-goal to feed the bearer is `Nat.Coprime a q`.

## Not done / honest scope

- No Lean was built or written (dual-backend blackout). Bearer signatures are transcribed from
  the Mathlib source at the pinned rev, not type-checked locally.
- The precise Dirichlet residue classes per `n mod 8` are **deliberately not asserted here** —
  reconstructing them from memory risks error; they must be taken from Serre/Davenport at ACT time.
  This note pins the Mathlib *bearer* and the *qualitative-suffices* justification, which is the
  part that was previously a "confirm at build time" unknown.
