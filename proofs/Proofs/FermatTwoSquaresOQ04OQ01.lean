/-
  Jacobi's Two-Square Count — the geometric side r₂(n) and its positivity bridge
  Open Question: fermat-two-squares-oq-04-oq-01

  Fermat's two-squares theorem says *which* `n` are sums of two squares; Jacobi's
  theorem says *how many*:

        r₂(n) = 4 · δ(n),   δ(n) = ∑_{d ∣ n} χ₄(d),

  where `χ₄` is the non-principal character mod 4 and `r₂(n)` counts the ordered,
  signed integer pairs `(a,b)` with `a² + b² = n`.  The parent entry
  (`fermat-two-squares-oq-04`, `FermatTwoSquaresOQ04.jacobiSum`) built and
  verified the *arithmetic* right-hand side `δ`: multiplicative, nonnegative, with
  explicit prime-power values and the qualitative bridge
  `0 < δ(n) ⇔ n is a sum of two squares`.

  This file opens the *geometric* left-hand side.  It defines the honest
  representation count

        r₂(n) := #{ (a,b) ∈ ℤ² : a² + b² = n }

  as a `Finset.card` (finiteness is packaged into the definition via an explicit
  bounding box `[-n, n]²`, since every solution has `|a|, |b| ≤ n`), and connects
  it back to the parent by matching the two sides at the level of **positivity** —
  the qualitative shadow of Jacobi's identity:

        0 < r₂(n)  ⇔  n is a sum of two squares  ⇔  0 < δ(n).

  This is the first rigorous bridge between the geometric and arithmetic sides of
  Jacobi's theorem in the gallery: the lattice-point count on the circle of
  radius √n is positive exactly when the divisor-character sum δ is.  The full
  quantitative identity `r₂ = 4δ` (the exact count via Gaussian-integer prime
  splitting, with the factor `4 = #{±1, ±i}` the unit group of ℤ[i]) remains
  open; the divisibility `4 ∣ r₂(n)` is the natural next brick.

  References:
  - Jacobi (1834): r₂(n) = 4 ∑_{d∣n} χ₄(d)
  - Parent FermatTwoSquaresOQ04.lean: the verified δ side
  - Mathlib `Nat.eq_sq_add_sq_iff` (representability criterion)
-/

import Mathlib.Tactic
import Proofs.FermatTwoSquaresOQ04

open Finset

namespace FermatTwoSquaresOQ04OQ01

open FermatTwoSquaresOQ04

-- ============================================================================
-- Part I:  The geometric representation count r₂(n)
-- ============================================================================

/-- The finset of integer representations `{(a,b) ∈ ℤ² : a²+b² = n}`, cut out of
the bounding box `[-n, n]²` (every solution has `|a|, |b| ≤ n`). -/
def sols (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
    fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)

/-- **The two-square representation count** `r₂(n) = #{(a,b) : a²+b² = n}`. -/
def r2 (n : ℕ) : ℕ := (sols n).card

/-- Membership bound: any integer with `a² ≤ n` lies in `[-n, n]`. -/
private lemma mem_Icc_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) :
    a ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
  rw [Finset.mem_Icc]
  constructor
  · rcases le_or_gt 0 a with h1 | h1
    · linarith
    · have h1' : 1 ≤ -a := by omega
      nlinarith [h1', h]
  · rcases le_or_gt a 0 with h1 | h1
    · linarith
    · have h1' : 1 ≤ a := by omega
      nlinarith [h1', h]

/-- `(a,b) ∈ sols n ↔ a²+b² = n`.  The bounding box is automatic. -/
@[simp] theorem mem_sols {n : ℕ} {p : ℤ × ℤ} :
    p ∈ sols n ↔ p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
  rw [sols, mem_filter, mem_product]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨mem_Icc_of_sq_le ?_, mem_Icc_of_sq_le ?_⟩, h⟩
    · nlinarith [sq_nonneg p.2]
    · nlinarith [sq_nonneg p.1]

/-- `r₂(n) > 0` exactly when `n` has an integer representation as a sum of two
squares. -/
theorem r2_pos_iff_exists_int {n : ℕ} :
    0 < r2 n ↔ ∃ a b : ℤ, a ^ 2 + b ^ 2 = (n : ℤ) := by
  rw [r2, Finset.card_pos]
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_sols] at hp
    exact ⟨p.1, p.2, hp⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨(a, b), by rw [mem_sols]; exact hab⟩

/-- Integer and natural-number representability agree. -/
theorem exists_int_iff_exists_nat {n : ℕ} :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = (n : ℤ)) ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a.natAbs, b.natAbs, ?_⟩
    have key : (n : ℤ) = (((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ)) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      linarith [hab]
    exact_mod_cast key
  · rintro ⟨x, y, hxy⟩
    exact ⟨(x : ℤ), (y : ℤ), by rw [hxy]; push_cast; ring⟩

-- ============================================================================
-- Part II:  Positivity bridge — the qualitative Jacobi theorem, both sides
-- ============================================================================

/-- **Positivity bridge (qualitative Jacobi).**  The geometric representation
count is positive exactly when the parent's arithmetic divisor-character sum is:

      0 < r₂(n)  ⇔  0 < δ(n).

Both sides equal "`n` is a sum of two squares", so this is the exact positivity
shadow of Jacobi's identity `r₂ = 4δ`, now established across *both* sides. -/
theorem r2_pos_iff_jacobiSum_pos {n : ℕ} (hn : n ≠ 0) :
    0 < r2 n ↔ 0 < jacobiSum n := by
  rw [r2_pos_iff_exists_int, exists_int_iff_exists_nat,
    ← jacobiSum_pos_iff_sq_add_sq hn]

/-- Complementary vanishing form: `n` has no representation ⇔ `δ(n) = 0`. -/
theorem r2_eq_zero_iff_jacobiSum_eq_zero {n : ℕ} (hn : n ≠ 0) :
    r2 n = 0 ↔ jacobiSum n = 0 := by
  constructor
  · intro h
    by_contra hj
    have hpos : 0 < jacobiSum n := lt_of_le_of_ne (jacobiSum_nonneg n) (Ne.symm hj)
    rw [← r2_pos_iff_jacobiSum_pos hn] at hpos
    omega
  · intro h
    by_contra hr
    have hpos : 0 < r2 n := Nat.pos_of_ne_zero hr
    rw [r2_pos_iff_jacobiSum_pos hn, h] at hpos
    exact lt_irrefl 0 hpos

/-- **Geometric Fermat criterion.**  For a prime `p`, there is a lattice point on
the circle of radius `√p` exactly when `p ≢ 3 (mod 4)` — Fermat's two-squares
criterion recovered from the representation count via the parent's `δ`. -/
theorem r2_prime_pos_iff {p : ℕ} (hp : p.Prime) :
    0 < r2 p ↔ p % 4 ≠ 3 := by
  rw [r2_pos_iff_jacobiSum_pos hp.ne_zero]
  have hkey := jacobiSum_prime_pow_pos_iff hp 1
  rw [pow_one] at hkey
  rw [hkey]
  constructor
  · intro h h3; exact Nat.not_even_one (h h3)
  · intro h h3; exact absurd h3 h

end FermatTwoSquaresOQ04OQ01
