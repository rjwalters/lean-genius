# zsqrtd-neg-two-oq-01 — single bi-conditional for primes p = x² + 2y²

## Problem
Unify the complete characterization of primes representable as `x² + 2y²` into a
single `↔` in Lean. Parent: `zsqrtd-neg-two` (ℤ[√−2] Euclidean domain).

## Status: ACT (proof written, build-pending)

Both verification backends were down this session (host Docker containerd blob
I/O corruption, fleet-wide; Aristotle MCP returning 404 "Resource not found").
The proof is verify-by-construction: every Mathlib lemma name was confirmed to
exist by direct inspection of `proofs/.lake/packages/mathlib` (pin v4.26.0).
NOT yet machine-checked → not registered in `Proofs.lean`.

## Session 2026-06-18 (s01) — FRESH

### Key mathematical content
The parent file already proves the two FORWARD implications (`p % 8 = 1` and
`p % 8 = 3` ⟹ representable) via `-2` being a QR mod p. It never assembled them
into an iff and never proved the CONVERSE.

- **Converse (new, elementary):** odd `p = a² + 2b²` ⟹ `p ≡ 1` or `3 (mod 8)`.
  `p` odd ⟹ `a` odd ⟹ `a² ≡ 1 (mod 8)`; `2b² ≡ 0` or `2 (mod 8)`. In `ZMod 8`
  the achievable values of `x²+2y²` are `{0,1,2,3,4,6}` (a 64-case `decide`),
  never `5` or `7`; intersect with odd residues `{1,3,5,7}` ⟹ `{1,3}`.
- **Unified iff:** for prime `p`,
  `(∃ a b : ℤ, a²+2b² = p) ↔ (p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3)`.
  `←`: even case `2 = 0²+2·1²` + parent's two forward theorems.
  `→`: even case + converse.

### Built items
- `ZsqrtdNegTwoOQ01.repr_mod_eight` (converse) — proofs/Proofs/ZsqrtdNegTwoOQ01.lean
- `ZsqrtdNegTwoOQ01.prime_sq_add_two_sq_iff` (the open-question iff) — same file

### Lemmas relied on (all confirmed present in pin v4.26.0)
`ZMod.natCast_mod`, `ZMod.val_natCast`, `Nat.Prime.eq_two_or_odd`,
`SqAddTwoSq.sq_add_two_sq_of_prime_{one,three}_mod_eight` (parent).

### Next steps
1. When Docker/Aristotle recover: `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ01`.
2. If green, register in `proofs/Proofs.lean` and add gallery meta under
   `src/data/proofs/zsqrtd-neg-two/` (or OQ-01 entry).
3. Risk points to watch on first build: the `decide`/`simp` cast-back closers in
   `repr_mod_eight` step (C), and `exact_mod_cast` after `push_cast` in step (A).
