/-
# A single bi-conditional characterization of primes `p = x² + 2y²`

  (`zsqrtd-neg-two-oq-01`, open question on the parent gallery proof
   `zsqrtd-neg-two`: "ℤ[√−2]: Euclidean Domain and x² + 2y² Representations")

## The question

The parent file `Proofs.ZsqrtdNegTwo` proves the two *forward* implications

* `p % 8 = 1 → ∃ a b : ℤ, a² + 2 b² = p`   (`SqAddTwoSq.sq_add_two_sq_of_prime_one_mod_eight`)
* `p % 8 = 3 → ∃ a b : ℤ, a² + 2 b² = p`   (`SqAddTwoSq.sq_add_two_sq_of_prime_three_mod_eight`)

but never assembles them, together with the (missing) *converse* and the even
prime `2 = 0² + 2·1²`, into one bi-conditional.  The open question asks precisely
for that single `↔` statement.

## What this file adds

1. `repr_mod_eight` — the **converse** (the genuinely new content).  If an
   *odd* natural number `p` is represented as `a² + 2 b²` then `p ≡ 1` or
   `3 (mod 8)`.  This is elementary: `p` odd forces `a` odd, so `a² ≡ 1 (mod 8)`,
   while `2 b² ≡ 0` or `2 (mod 8)`; hence `p ≡ 1` or `3 (mod 8)`.  The argument is
   carried out in `ZMod 8`, where the achievable values of `x² + 2 y²` are
   `{0,1,2,3,4,6}` — in particular never `5` or `7` — and the odd residues are
   `{1,3,5,7}`; intersecting gives `{1,3}`.

2. `prime_sq_add_two_sq_iff` — the **unified characterization** the open
   question asks for: for every prime `p`,
   `(∃ a b : ℤ, a² + 2 b² = p) ↔ (p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3)`.

## Status

Build-pending: the host Docker/Lean toolchain and the Aristotle backend were
both unavailable when this file was written, so it has not yet been machine
checked.  Every lemma name used against Mathlib (pin `v4.26.0`) was verified to
exist by direct inspection of `proofs/.lake/packages/mathlib`
(`ZMod.natCast_mod`, `ZMod.val_natCast`, `Nat.Prime.eq_two_or_odd`).  Do **not**
register this file in `Proofs.lean` until it has been Docker-built.
-/
import Mathlib
import Proofs.ZsqrtdNegTwo

open SqAddTwoSq

namespace ZsqrtdNegTwoOQ01

/-- **Converse direction.**  If an odd natural number `p` is representable as
`a² + 2 b²` (with `a b : ℤ`), then `p ≡ 1` or `3 (mod 8)`.

Primality is *not* needed — only that `p` is odd.  The proof reduces the
identity modulo `8`: in `ZMod 8` the value `x² + 2 y²` is never `5` or `7`
(a finite `decide` check), so the odd residue `p % 8 ∈ {1,3,5,7}` must lie in
`{1,3}`. -/
theorem repr_mod_eight (p : ℕ) (hodd : p % 2 = 1)
    (a b : ℤ) (h : a ^ 2 + 2 * b ^ 2 = (p : ℤ)) : p % 8 = 1 ∨ p % 8 = 3 := by
  -- (A) Reduce the representing identity modulo 8.
  have h8 : (a : ZMod 8) ^ 2 + 2 * (b : ZMod 8) ^ 2 = (p : ZMod 8) := by
    have hh := congrArg (Int.castRingHom (ZMod 8)) h
    simpa using hh
  -- (B) `x² + 2 y²` is never `5` or `7` in `ZMod 8` (finite check).
  have hforbidden : ∀ x y : ZMod 8, x ^ 2 + 2 * y ^ 2 ≠ 5 ∧ x ^ 2 + 2 * y ^ 2 ≠ 7 := by
    decide
  have h5 : (p : ZMod 8) ≠ 5 := by
    rw [← h8]; exact (hforbidden (a : ZMod 8) (b : ZMod 8)).1
  have h7 : (p : ZMod 8) ≠ 7 := by
    rw [← h8]; exact (hforbidden (a : ZMod 8) (b : ZMod 8)).2
  -- (C) Transport the two exclusions back to `p % 8`.
  have cast_mod : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
  have hv5 : p % 8 ≠ 5 := by
    intro hc; apply h5; rw [cast_mod, hc]; simp
  have hv7 : p % 8 ≠ 7 := by
    intro hc; apply h7; rw [cast_mod, hc]; simp
  -- (D) `p % 8 < 8` is odd and avoids `5, 7`, hence equals `1` or `3`.
  have hlt : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hpar : p % 8 % 2 = 1 := by omega
  omega

/-- **Unified characterization (the open question).**  For every prime `p`,
`p` is of the form `a² + 2 b²` (with `a b : ℤ`) iff `p = 2` or `p ≡ 1` or
`3 (mod 8)`.

* `→` combines the even prime case `2 = 0² + 2·1²` with `repr_mod_eight`.
* `←` combines the explicit witness for `2` with the parent file's two forward
  theorems. -/
theorem prime_sq_add_two_sq_iff (p : ℕ) (hp : p.Prime) :
    (∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (p : ℤ)) ↔ (p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3) := by
  constructor
  · rintro ⟨a, b, hab⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      exact Or.inr (repr_mod_eight p hodd a b hab)
  · rintro (h2 | h1 | h3)
    · exact ⟨0, 1, by rw [h2]; norm_num⟩
    · haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact sq_add_two_sq_of_prime_one_mod_eight h1
    · haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact sq_add_two_sq_of_prime_three_mod_eight h3

/-- Sanity checks against small primes. -/
example : (∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (2 : ℤ)) := ⟨0, 1, by norm_num⟩
example : (∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (3 : ℤ)) := ⟨1, 1, by norm_num⟩
example : (∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (11 : ℤ)) := ⟨3, 1, by norm_num⟩
example : (∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (17 : ℤ)) := ⟨3, 2, by norm_num⟩

end ZsqrtdNegTwoOQ01
