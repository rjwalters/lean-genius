import Mathlib

/-!
# The two-square sufficiency slice of Legendre's three-square theorem

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-03`)**, a companion to
the parent `oq-03` entry *"Legendre's three-square theorem — the if direction"*:

  `n = x² + y² + z²` is solvable  ⟺  `n ≠ 4^a (8b + 7)`  for all `a, b ≥ 0`.

The full **sufficiency** ("if") direction — every `n` outside the excluded family
`4^a(8b+7)` is a sum of three squares — is *open* in the gallery: it is reduced
to one Hasse–Minkowski / Dirichlet input and is not yet axiom-free.  The
**necessity** ("only if") direction is the elementary half and is fully proved in
`Proofs/ZsqrtdNegTwoOQ02.lean` (the mod-8 obstruction plus the `4`-descent).

This file carves out a **genuinely elementary, Dirichlet-free slice of the open
sufficiency direction**, together with a structural contrast that the two-square
theory does *not* share.

## What is new here

Mathlib proves **Fermat's two-square theorem** (`Nat.Prime.sq_add_sq`) and the
full characterisation `Nat.eq_sq_add_sq_iff` (a number is a sum of two squares
iff every prime `≡ 3 (mod 4)` divides it to an even power), but has **no**
three-square result.  We bridge the two:

* `isSumTwoSq_imp_isSumThreeSq` — every sum of two squares is a sum of three
  squares (append `0²`).  Combined with Mathlib's characterisation, this hands
  the open "if" direction an **explicit, infinite, Dirichlet-free family**:
  - `prime_mod_four_ne_three_isSumThreeSq`: every prime `p` with `p % 4 ≠ 3` is a
    sum of three squares;
  - `isSumThreeSq_of_forall_threeMod_even`: every `n` whose primes `≡ 3 (mod 4)`
    all occur to even power is a sum of three squares.

* **Strict containment** (`isSumThreeSq_strictly_contains_twoSq`): the three-square
  numbers strictly contain the two-square numbers — `3 = 1²+1²+1²` is a sum of
  three squares but, being `≡ 3 (mod 4)`, is *not* a sum of two squares.

* **Failure of multiplicative closure** (`isSumThreeSq_not_mul_closed`): unlike the
  two-square numbers, which are closed under multiplication (Brahmagupta–Fibonacci,
  `isSumTwoSq_mul`), the three-square numbers are **not**: `3` and `21` are sums of
  three squares, yet `3 · 21 = 63 = 8·7 + 7` is excluded.  This is the precise
  reason the sufficiency direction cannot be bootstrapped multiplicatively and
  genuinely requires the analytic Dirichlet input.

All proofs are axiom-free and use only kernel `decide` over `ZMod 4` / `ZMod 8`.
-/

namespace LagrangeFourSquaresWaringG2OQ03OQ03

open scoped Classical

/-! ## Representability predicates -/

/-- `n` is a sum of two integer squares. -/
def IsSumTwoSq (n : ℤ) : Prop := ∃ x y : ℤ, x ^ 2 + y ^ 2 = n

/-- `n` is a sum of three integer squares. -/
def IsSumThreeSq (n : ℤ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

/-! ## Elementary modular obstructions

These supply the only inputs needed to pin down the concrete separating and
non-closure witnesses below.  All are finite `decide` checks over `ZMod 4` /
`ZMod 8`, hence kernel-checked and axiom-free. -/

/-- A sum of three integer squares is never `≡ 7 (mod 8)`.  Squares in `ZMod 8`
lie in `{0, 1, 4}`, and no three of those sum to `7`. -/
theorem sumThreeSq_ne_seven_mod_eight (x y z : ℤ) :
    ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 8) ≠ 7 := by
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  push_cast
  exact key _ _ _

/-- A sum of two integer squares is never `≡ 3 (mod 4)`.  Squares in `ZMod 4`
lie in `{0, 1}`, and no two of those sum to `3`. -/
theorem sumTwoSq_ne_three_mod_four (x y : ℤ) :
    ((x ^ 2 + y ^ 2 : ℤ) : ZMod 4) ≠ 3 := by
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
  push_cast
  exact key _ _

/-- **Necessity at the mod-8 level.**  If `n % 8 = 7` then `n` is not a sum of
three integer squares. -/
theorem not_isSumThreeSq_of_mod_eight {n : ℕ} (hn : n % 8 = 7) :
    ¬ IsSumThreeSq (n : ℤ) := by
  rintro ⟨x, y, z, h⟩
  apply sumThreeSq_ne_seven_mod_eight x y z
  rw [h, Int.cast_natCast]
  conv_lhs => rw [← ZMod.natCast_mod n 8, hn]
  decide

/-- **Necessity at the mod-4 level for two squares.**  If `n % 4 = 3` then `n` is
not a sum of two integer squares. -/
theorem not_isSumTwoSq_of_mod_four {n : ℕ} (hn : n % 4 = 3) :
    ¬ IsSumTwoSq (n : ℤ) := by
  rintro ⟨x, y, h⟩
  apply sumTwoSq_ne_three_mod_four x y
  rw [h, Int.cast_natCast]
  conv_lhs => rw [← ZMod.natCast_mod n 4, hn]
  decide

/-! ## The embedding: two squares ⟹ three squares -/

/-- **Embedding.**  Every sum of two squares is a sum of three squares — append
`0²`. -/
theorem isSumTwoSq_imp_isSumThreeSq {n : ℤ} (h : IsSumTwoSq n) : IsSumThreeSq n := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, 0, by rw [← hxy]; ring⟩

/-- A sum of two squares is never `≡ 7 (mod 8)`, so it never lands in the excluded
family `4^a(8b+7)` — the two-square slice is *consistent* with the necessity
direction. -/
theorem isSumTwoSq_ne_seven_mod_eight {n : ℤ} (h : IsSumTwoSq n) :
    (n : ZMod 8) ≠ 7 := by
  obtain ⟨x, y, hxy⟩ := h
  rw [← hxy]
  push_cast
  have key : ∀ a b : ZMod 8, a ^ 2 + b ^ 2 ≠ 7 := by decide
  exact key _ _

/-! ## A Dirichlet-free infinite slice of the open sufficiency direction -/

/-- **Prime slice (Fermat ⟹ three squares).**  Every prime `p` with `p % 4 ≠ 3`
is a sum of three integer squares.  This is unconditional — it rides on Mathlib's
two-square theorem `Nat.Prime.sq_add_sq` and needs no Dirichlet input. -/
theorem prime_mod_four_ne_three_isSumThreeSq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    IsSumThreeSq (p : ℤ) := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp
  exact isSumTwoSq_imp_isSumThreeSq ⟨(a : ℤ), (b : ℤ), by exact_mod_cast hab⟩

/-- **Characterisation slice.**  Every natural number `n` in which each prime
`≡ 3 (mod 4)` occurs to an even power is a sum of three integer squares.  Via
Mathlib's `Nat.eq_sq_add_sq_iff`, this is an *explicit, infinite, Dirichlet-free*
family satisfying the open "if" direction of Legendre's three-square theorem. -/
theorem isSumThreeSq_of_forall_threeMod_even {n : ℕ}
    (H : ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n)) :
    IsSumThreeSq (n : ℤ) := by
  obtain ⟨x, y, h⟩ := Nat.eq_sq_add_sq_iff.mpr H
  exact isSumTwoSq_imp_isSumThreeSq ⟨(x : ℤ), (y : ℤ), by exact_mod_cast h.symm⟩

/-! ## Contrast: two squares are multiplicatively closed, three squares are not -/

/-- **Brahmagupta–Fibonacci.**  The sums of two integer squares are closed under
multiplication (Mathlib `sq_add_sq_mul`). -/
theorem isSumTwoSq_mul {a b : ℤ} (ha : IsSumTwoSq a) (hb : IsSumTwoSq b) :
    IsSumTwoSq (a * b) := by
  obtain ⟨x, y, hx⟩ := ha
  obtain ⟨u, v, hu⟩ := hb
  obtain ⟨r, s, h⟩ := sq_add_sq_mul hx.symm hu.symm
  exact ⟨r, s, h.symm⟩

/-- `3 = 1² + 1² + 1²` is a sum of three squares. -/
theorem three_isSumThreeSq : IsSumThreeSq 3 := ⟨1, 1, 1, by norm_num⟩

/-- `3` is *not* a sum of two squares (`3 ≡ 3 (mod 4)`). -/
theorem three_not_isSumTwoSq : ¬ IsSumTwoSq 3 := by
  have h := not_isSumTwoSq_of_mod_four (n := 3) (by decide)
  simpa using h

/-- **Strict containment.**  The three-square numbers strictly contain the
two-square numbers: `3` witnesses the gap. -/
theorem isSumThreeSq_strictly_contains_twoSq :
    IsSumThreeSq 3 ∧ ¬ IsSumTwoSq 3 :=
  ⟨three_isSumThreeSq, three_not_isSumTwoSq⟩

/-- `21 = 4² + 2² + 1²` is a sum of three squares. -/
theorem twentyOne_isSumThreeSq : IsSumThreeSq 21 := ⟨4, 2, 1, by norm_num⟩

/-- `63 = 8·7 + 7` is excluded, hence *not* a sum of three squares. -/
theorem sixtyThree_not_isSumThreeSq : ¬ IsSumThreeSq 63 := by
  have h := not_isSumThreeSq_of_mod_eight (n := 63) (by decide)
  simpa using h

/-- **Failure of multiplicative closure.**  Unlike the two-square numbers
(`isSumTwoSq_mul`), the three-square numbers are *not* closed under
multiplication: `3` and `21` are each sums of three squares, but their product
`63` is excluded.  This is exactly why the sufficiency direction cannot be
bootstrapped multiplicatively from a prime slice and genuinely requires the
analytic (Dirichlet) input. -/
theorem isSumThreeSq_not_mul_closed :
    IsSumThreeSq 3 ∧ IsSumThreeSq 21 ∧ ¬ IsSumThreeSq (3 * 21) := by
  refine ⟨three_isSumThreeSq, twentyOne_isSumThreeSq, ?_⟩
  have h : (3 * 21 : ℤ) = 63 := by norm_num
  rw [h]
  exact sixtyThree_not_isSumThreeSq

end LagrangeFourSquaresWaringG2OQ03OQ03
