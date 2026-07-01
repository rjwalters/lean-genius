import Mathlib

/-
# Uniform Product Closed Forms for the Figurate-Number Tower

## Open Question (combinations-formula-oq-06, OQ-02)

The sibling entry `combinations-formula-oq-06-oq-01` packaged the whole simplicial
figurate ladder as a single parametrized family `S(k, n) = C(n+k-1, k) = multichoose n k`
and proved the **tower identity** `∑_{m=1}^{n} S(k, m) = S(k+1, n)` uniformly in the
dimension `k`.  It recovered the *closed form* only at the triangular rung,
`S(2, n) = n(n+1)/2`, leaving the tetrahedral rung as the raw binomial `S(3, n) = C(n+2, 3)`.

OQ-02 asks precisely: **can the closed forms for the higher figurate numbers (e.g. the
tetrahedral `n(n+1)(n+2)/6`) be derived inside Lean without a separate induction, mirroring
the `n(n+1)/2` closed form already obtained for the triangular case?**

## Contribution

Yes — and not just for the tetrahedral rung, but for *every* rung at once, with no
induction whatsoever.  The engine is the single identity

  `k ! · S(k, n) = n·(n+1)·⋯·(n+k-1) = ascFactorial n k`          (`factorial_mul_S`)

which is nothing but the classical `choose ↔ ascending-factorial` bridge
(`Nat.ascFactorial_eq_factorial_mul_choose'`) read through `S(k,n) = C(n+k-1, k)`.  This is a
*uniform* statement covering the whole tower; its proof is a one-line rewrite, with no
per-`k` induction.  The division form

  `S(k, n) = ascFactorial n k / k !`                              (`S_closed`)

is its immediate consequence.  Specializing `k`:

* `k = 2` (triangular):  `2 · S(2, n) = n(n+1)`,        `S(2, n) = n(n+1)/2`
* `k = 3` (tetrahedral): `6 · S(3, n) = n(n+1)(n+2)`,   `S(3, n) = n(n+1)(n+2)/6`
* `k = 4` (pentatope):   `24 · S(4, n) = n(n+1)(n+2)(n+3)`, `S(4, n) = n(n+1)(n+2)(n+3)/24`

The tetrahedral form is the exact object OQ-02 asked for; the pentatope rung is a genuinely
new closed form beyond the sibling entry.  Each specialization is obtained by evaluating the
finite product `ascFactorial n k` for a *concrete* `k` (`ascFactorial_two/three/four`, three
`ascFactorial_succ` unfoldings closed by `ring`) — no induction on `n`, no induction on `k`.

## Mathematical Context

`S(k, n)` counts the `k`-multisets drawn from `{1, …, n}`, equivalently the lattice points of
the `k`-dimensional simplex of side `n`; the product `n(n+1)⋯(n+k-1)/k!` is the ascending
(rising-factorial) form of the binomial coefficient `C(n+k-1, k)`.  Reading the closed form
off the ascending factorial is exactly the "no separate induction" phenomenon OQ-02 isolates:
the induction that would normally establish each figurate closed form is absorbed once and for
all into Mathlib's `ascFactorial ↔ choose` lemma.

This entry is self-contained: it re-derives `S` from `Nat.multichoose` rather than importing the
sibling file, so it stands alone while cross-referencing `combinations-formula-oq-06-oq-01`.
-/

namespace CombinationsFigurateClosedForm

open Nat

/-- The `k`-dimensional figurate number `S(k, n) = multichoose n k = C(n+k-1, k)`.
`S(1, n) = n` (linear), `S(2, n)` triangular, `S(3, n)` tetrahedral, `S(4, n)` pentatope. -/
def S (k n : ℕ) : ℕ := Nat.multichoose n k

/-- `S(k, n) = C(n+k-1, k)`: the multiset coefficient as an ordinary binomial coefficient. -/
theorem S_eq_choose (k n : ℕ) : S k n = (n + k - 1).choose k := by
  rw [S, Nat.multichoose_eq]

/-- **Uniform product closed form.** For every dimension `k`, `k! · S(k, n)` equals the
ascending factorial `n(n+1)⋯(n+k-1)`.  A single statement covering the entire figurate tower;
the proof is the `choose ↔ ascending-factorial` bridge, with no per-`k` induction. -/
theorem factorial_mul_S (k n : ℕ) : k ! * S k n = n.ascFactorial k := by
  rw [S_eq_choose]
  exact (Nat.ascFactorial_eq_factorial_mul_choose' n k).symm

/-- **Division form of the uniform closed form:** `S(k, n) = n(n+1)⋯(n+k-1) / k!`, for every
dimension `k` simultaneously. -/
theorem S_closed (k n : ℕ) : S k n = n.ascFactorial k / k ! := by
  rw [S_eq_choose]
  exact Nat.choose_eq_asc_factorial_div_factorial' n k

/-!
### Evaluating the finite product `ascFactorial n k` at concrete dimensions

Each is three-or-fewer `ascFactorial_succ` unfoldings closed by `ring` — no induction. -/

/-- `n(n+1)`: the ascending factorial at dimension 2. -/
theorem ascFactorial_two (n : ℕ) : n.ascFactorial 2 = n * (n + 1) := by
  have h2 : n.ascFactorial 2 = (n + 1) * n.ascFactorial 1 := Nat.ascFactorial_succ
  have h1 : n.ascFactorial 1 = (n + 0) * n.ascFactorial 0 := Nat.ascFactorial_succ
  rw [h2, h1, Nat.ascFactorial_zero]; ring

/-- `n(n+1)(n+2)`: the ascending factorial at dimension 3. -/
theorem ascFactorial_three (n : ℕ) : n.ascFactorial 3 = n * (n + 1) * (n + 2) := by
  have h3 : n.ascFactorial 3 = (n + 2) * n.ascFactorial 2 := Nat.ascFactorial_succ
  rw [h3, ascFactorial_two]; ring

/-- `n(n+1)(n+2)(n+3)`: the ascending factorial at dimension 4. -/
theorem ascFactorial_four (n : ℕ) : n.ascFactorial 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  have h4 : n.ascFactorial 4 = (n + 3) * n.ascFactorial 3 := Nat.ascFactorial_succ
  rw [h4, ascFactorial_three]; ring

/-!
### Multiplied closed forms (division-free)

The cleanest, most honest statements: no natural-number division truncation is involved. -/

/-- Triangular rung: `2 · S(2, n) = n(n+1)`. -/
theorem two_mul_S_two (n : ℕ) : 2 * S 2 n = n * (n + 1) := by
  have h := factorial_mul_S 2 n
  rwa [ascFactorial_two, show (2 : ℕ)! = 2 from rfl] at h

/-- Tetrahedral rung: `6 · S(3, n) = n(n+1)(n+2)` — the object OQ-02 asked for, exact form. -/
theorem six_mul_S_three (n : ℕ) : 6 * S 3 n = n * (n + 1) * (n + 2) := by
  have h := factorial_mul_S 3 n
  rwa [ascFactorial_three, show (3 : ℕ)! = 6 from rfl] at h

/-- Pentatope rung: `24 · S(4, n) = n(n+1)(n+2)(n+3)` — a new closed form beyond oq-06-oq-01. -/
theorem twentyfour_mul_S_four (n : ℕ) : 24 * S 4 n = n * (n + 1) * (n + 2) * (n + 3) := by
  have h := factorial_mul_S 4 n
  rwa [ascFactorial_four, show (4 : ℕ)! = 24 from rfl] at h

/-!
### Divided closed forms

The familiar textbook shapes, recovered by dividing the multiplied forms. -/

/-- Triangular closed form: `S(2, n) = n(n+1)/2`, mirroring the sibling's `S_two_closed`. -/
theorem S_two_closed (n : ℕ) : S 2 n = n * (n + 1) / 2 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (two_mul_S_two n)

/-- **Tetrahedral closed form:** `S(3, n) = n(n+1)(n+2)/6`.  The exact answer to OQ-02. -/
theorem S_three_closed (n : ℕ) : S 3 n = n * (n + 1) * (n + 2) / 6 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (six_mul_S_three n)

/-- Pentatope closed form: `S(4, n) = n(n+1)(n+2)(n+3)/24`. -/
theorem S_four_closed (n : ℕ) : S 4 n = n * (n + 1) * (n + 2) * (n + 3) / 24 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (twentyfour_mul_S_four n)

/-!
### The `k = 1` base rung and concrete sanity checks -/

/-- Linear rung: `S(1, n) = n`. -/
@[simp] theorem S_one (n : ℕ) : S 1 n = n := Nat.multichoose_one_right n

/-- Tetrahedral number `S(3, 4) = 4·5·6/6 = 20`. -/
example : S 3 4 = 20 := by rw [S_three_closed]

/-- Pentatope number `S(4, 3) = 3·4·5·6/24 = 15`. -/
example : S 4 3 = 15 := by rw [S_four_closed]

/-- Triangular number `S(2, 5) = 5·6/2 = 15`. -/
example : S 2 5 = 15 := by rw [S_two_closed]

end CombinationsFigurateClosedForm
