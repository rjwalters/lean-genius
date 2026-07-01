import Mathlib

/-!
# The doubled-argument Fibonacci binomial transform `∑ C(n,k) F₂ₖ`

The parent entry `FibonacciIdentitiesOQ06OQ01` proves the **binomial transform**
of the Fibonacci sequence, `∑_{k≤n} C(n,k)·Fₖ = F₂ₙ` — the transform *doubles* the
index. Its sibling `FibonacciIdentitiesOQ06OQ01OQ02` handles the *alternating*
transform `∑ (−1)ᵏ C(n,k) Fₖ = −Fₙ`. This descendant answers the remaining open
question of that family: **what happens when you feed the transform the
even-indexed Fibonacci numbers `F₂ₖ`** — i.e. the "k-fold iterate"
`∑_{k≤n} C(n,k) F₂ₖ`?

The naive guess is that iterating index-doubling gives `F₄ₙ`. It does **not**.
The sequence

  `Cₙ = ∑_{k≤n} C(n,k) F₂ₖ = 0, 1, 5, 20, 75, 275, 1000, …`

is not a Fibonacci sequence at any index; it is the **Lucas sequence `Uₙ(P,Q)`
with `P = 5, Q = 5`**, i.e. it satisfies the second-order recurrence

  `Cₙ₊₂ = 5·Cₙ₊₁ − 5·Cₙ`,  `C₀ = 0`, `C₁ = 1`.

* `fib_two_k_binom_transform_rec` — the recurrence `Cₙ₊₂ = 5·Cₙ₊₁ − 5·Cₙ`.
* `C2_zero`, `C2_one` — the base values, so the recurrence pins down `Cₙ` uniquely.

**Why `(5,5)`.** By Binet, `∑ C(n,k) φ²ᵏ = (1+φ²)ⁿ`. Since `φ² = φ+1`, the base is
`1+φ² = φ+2 = √5·φ` (as `φ+2 = (5+√5)/2 = √5·(1+√5)/2`), and likewise
`1+ψ² = −√5·ψ`. So `φ+2` and `ψ+2` are the roots of `x² − 5x + 5`, whence the
`(P,Q) = (5,5)` recurrence. Tracking the `√5` factors gives the closed form
`Cₙ = 5^{n/2}·Fₙ` for even `n` and `Cₙ = 5^{(n−1)/2}·Lₙ` for odd `n` (`Lₙ` the
`n`-th Lucas number) — so the transform of `F₂ₖ` really *scales by powers of √5*
and alternates between the Fibonacci and Lucas sequences, rather than landing at a
further-doubled Fibonacci index.

The engine is the general **Pascal convolution over a commutative ring**,
`pascal_conv_ring` (the ring-valued analogue of the parent's `pascal_conv`).
Applying it to `k ↦ F₂ₖ` and to `k ↦ F₂ₖ₊₂`, together with the even-index
Fibonacci recurrence `F_{m+4} = 3·F_{m+2} − F_m`, gives the coupled first-order
system `Cₙ₊₁ = Cₙ + Dₙ`, `Dₙ₊₁ = 4·Dₙ − Cₙ`, which collapses to the stated
second-order recurrence.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ06OQ01OQ03

open Finset

variable {R : Type*} [CommRing R]

/-- **Pascal convolution over a commutative ring.** For any summand `f : ℕ → R`,
`∑_{k<n+2} C(n+1,k)·f(k) = ∑_{k<n+1} C(n,k)·f(k) + ∑_{k<n+1} C(n,k)·f(k+1)`.

The ring-valued analogue of the parent entry's `pascal_conv`: Pascal's rule
`C(n+1,k+1) = C(n,k) + C(n,k+1)` summed against `f`, with the boundary terms
`C(n+1,0) = C(n,0) = 1` and `C(n,n+1) = 0` reconciled by the first- and
last-term range peels. -/
theorem pascal_conv_ring (f : ℕ → R) (n : ℕ) :
    ∑ k ∈ range (n + 2), ((n + 1).choose k : R) * f k
      = (∑ k ∈ range (n + 1), (n.choose k : R) * f k)
        + ∑ k ∈ range (n + 1), (n.choose k : R) * f (k + 1) := by
  rw [Finset.sum_range_succ' (fun k => ((n + 1).choose k : R) * f k) (n + 1)]
  simp only [Nat.choose_succ_succ' n, Nat.choose_zero_right, Nat.cast_add, Nat.cast_one,
    one_mul, add_mul]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : R) * f k) n, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : R) * f (k + 1)) n,
    Nat.choose_succ_self n, Nat.cast_zero, zero_mul, add_zero]
  ring

/-- Even-indexed Fibonacci summand `pₖ = F₂ₖ` (offset `0`). -/
def p (k : ℕ) : ℤ := (Nat.fib (2 * k) : ℤ)

/-- Even-indexed Fibonacci summand `qₖ = F₂ₖ₊₂` (offset `1`, i.e. `F₂₍ₖ₊₁₎`). -/
def q (k : ℕ) : ℤ := (Nat.fib (2 * k + 2) : ℤ)

/-- The doubled-argument binomial transform `Cₙ = ∑_{k≤n} C(n,k) F₂ₖ`. -/
def C2 (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * p k

/-- The shifted doubled-argument transform `Dₙ = ∑_{k≤n} C(n,k) F₂ₖ₊₂`. -/
def D2 (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * q k

/-- Shifting: `pₖ₊₁ = F₂₍ₖ₊₁₎ = F₂ₖ₊₂ = qₖ` (`2·(k+1)` is `2·k+2` definitionally). -/
lemma p_succ (k : ℕ) : p (k + 1) = q k := rfl

/-- Shifting, via `F₂ₖ₊₄ = 3·F₂ₖ₊₂ − F₂ₖ`: `qₖ₊₁ = 3·qₖ − pₖ`. -/
lemma q_succ (k : ℕ) : q (k + 1) = 3 * q k - p k := by
  unfold p q
  have e : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
  rw [e]
  have h4 : Nat.fib (2 * k + 4) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := Nat.fib_add_two
  have h3 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
  have h2 : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
  rw [h4, h3, h2]; push_cast; ring

/-- Recurrence: `Cₙ₊₁ = Cₙ + Dₙ`. -/
lemma C2_succ (n : ℕ) : C2 (n + 1) = C2 n + D2 n := by
  have hp := pascal_conv_ring p n
  have e : C2 (n + 1) = ∑ k ∈ range (n + 2), ((n + 1).choose k : ℤ) * p k := rfl
  rw [e, hp]
  unfold C2 D2
  congr 1

/-- Recurrence: `Dₙ₊₁ = 4·Dₙ − Cₙ`. -/
lemma D2_succ (n : ℕ) : D2 (n + 1) = 4 * D2 n - C2 n := by
  have hp := pascal_conv_ring q n
  have e : D2 (n + 1) = ∑ k ∈ range (n + 2), ((n + 1).choose k : ℤ) * q k := rfl
  rw [e, hp]
  have hqs : (∑ k ∈ range (n + 1), (n.choose k : ℤ) * q (k + 1)) = 3 * D2 n - C2 n := by
    unfold C2 D2
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [q_succ]; ring
  rw [hqs]
  show D2 n + (3 * D2 n - C2 n) = 4 * D2 n - C2 n
  ring

/-- **The doubled-argument binomial transform is a `(5,5)` Lucas sequence.**
`Cₙ = ∑_{k≤n} C(n,k) F₂ₖ` satisfies the second-order recurrence
`Cₙ₊₂ = 5·Cₙ₊₁ − 5·Cₙ`. Together with the base values `C₀ = 0`, `C₁ = 1`
(`C2_zero`, `C2_one`) this characterises `Cₙ` completely as the Lucas sequence
`Uₙ(5,5)` — not a further index-doubled Fibonacci sequence. -/
theorem fib_two_k_binom_transform_rec (n : ℕ) :
    C2 (n + 2) = 5 * C2 (n + 1) - 5 * C2 n := by
  have h1 := C2_succ (n + 1)
  have h2 := D2_succ n
  have h3 := C2_succ n
  have hD : D2 n = C2 (n + 1) - C2 n := by rw [h3]; ring
  rw [h1, h2, hD]; ring

/-- Base value `C₀ = 0` (since `F₀ = 0`). -/
theorem C2_zero : C2 0 = 0 := by
  simp [C2, p]

/-- Base value `C₁ = 1` (since `C₁ = F₀ + F₂ = 0 + 1`). -/
theorem C2_one : C2 1 = 1 := by
  simp [C2, p, Finset.sum_range_succ]

end FibonacciIdentitiesOQ06OQ01OQ03
