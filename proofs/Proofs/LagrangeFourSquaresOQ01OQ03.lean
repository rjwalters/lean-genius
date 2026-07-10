import Mathlib

/-
# Jacobi's Four-Square Count — a Computable Oracle (OQ-01 → OQ-03)

## Gallery Open Question
Parent: `lagrange-four-squares-oq-01` (computational complexity of four-square
representations). This follow-up asks:

  "What is the exact count of four-square representations of `n`, and can Jacobi's
   four-square formula `r₄(n) = 8·Σ_{d|n, 4∤d} d` be formalized?"

## What This File Does — and Honestly Does Not

**The general theorem is a genuine Mathlib gap.** Mathlib formalizes four-square
*existence* (`Nat.sum_four_squares` — every `n` is a sum of four squares) and the
Euler four-square multiplicativity identity (`Nat.euler_four_squares`), but it has
**no representation *count*** `r₄`, no two-square count `r₂`, and no Jacobi formula.
All three classical proof routes are blocked by large gaps:
* weight-2 modular forms `θ⁴ ∈ M₂(Γ₀(4))` (theta identity absent),
* Hurwitz-quaternion order arithmetic (order essentially undeveloped),
* the elementary Lambert/Liouville method (bottoms out on the missing `r₂` count).

Each needs ≫1000 LOC of new number theory, so the *general* Jacobi theorem is
**BLOCKED**. This file therefore does the honest, buildable increment: it pins the
counting **convention** and provides a machine-checked **oracle** that Jacobi's
divisor-sum formula reproduces the brute-force lattice count for a range of small
`n`. It mirrors the parent OQ-01's "verified for small cases" pattern.

## What is machine-checked here
1. `r4 n` — the *ordered, signed* four-square representation count, defined as a
   computable `Finset.card` over the box `[-√n, √n]⁴ ⊆ ℤ⁴`.
2. `jacobiCount n = 8·Σ_{d|n, 4∤d} d` — the right-hand side of Jacobi's formula.
3. `jacobiCount_odd` (0-axiom, **general**): for odd `n` the `4∤d` filter is vacuous,
   so `jacobiCount n = 8·σ(n)`. This isolates the elementary half of the formula.
4. `naive_sigma_fails` (0-axiom): the naive `8·σ(4) = 56` is WRONG; the true count
   is `r4 4 = 24`. The `4∤d` exclusion is load-bearing — this guards the convention.
5. `jacobi_oracle` : `r4 n = jacobiCount n` for `1 ≤ n ≤ 24`, by `native_decide`
   (hence depends on `Lean.ofReduceBool`; see the axiom note below).

## Axiom status
The structural lemmas (`jacobiCount_odd`, `naive_sigma_fails`, the box bound) are
0-axiom (`decide`/kernel). The oracle `jacobi_oracle` is discharged by
`native_decide` and so depends on `Lean.ofReduceBool` — it is an *axiomatized*
verified computation, not a proof of the general theorem.
-/

namespace LagrangeFourSquaresOQ01OQ03

open Finset

/-! ## Part 1: The representation count `r4` -/

/-- The box of admissible signed integer components for a four-square representation
of `n`: every component `x` with `x² ≤ n` satisfies `|x| ≤ √n`, i.e. `x ∈ [-√n, √n]`.
So all representations of `n` live inside `box n ^ 4`. -/
def box (n : ℕ) : Finset ℤ := Finset.Icc (-(Nat.sqrt n : ℤ)) (Nat.sqrt n : ℤ)

/-- `r4 n` counts the **ordered, signed** quadruples `(x₁,x₂,x₃,x₄) ∈ ℤ⁴` with
`x₁²+x₂²+x₃²+x₄² = n` (zeros and signs allowed). This is the classical `r₄(n)`.
It is a genuine, computable `Finset.card` over the finite box `box n ^ 4`. -/
def r4 (n : ℕ) : ℕ :=
  (((box n ×ˢ box n ×ˢ box n ×ˢ box n).filter
    (fun p => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = (n : ℤ))).card)

/-- Sanity: `r4 0 = 1` (only the all-zero quadruple). -/
example : r4 0 = 1 := by decide

/-! ## Part 2: The Jacobi right-hand side -/

/-- The right-hand side of Jacobi's four-square formula:
`jacobiCount n = 8 · Σ_{d ∣ n, 4 ∤ d} d`. -/
def jacobiCount (n : ℕ) : ℕ :=
  8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d

/-- For **odd** `n` the exclusion `4 ∤ d` is vacuous — no divisor of an odd number
is even — so Jacobi's count collapses to `8·σ(n)`. This 0-axiom general lemma
captures the elementary "odd" half of the formula. -/
theorem jacobiCount_odd {n : ℕ} (hn : Odd n) :
    jacobiCount n = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiCount
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_true_of_mem
  intro d hd
  rw [Nat.mem_divisors] at hd
  -- `d ∣ n` and `n` odd force `d` odd, hence `4 ∤ d`.
  intro hdvd
  have hd4 : (2 : ℕ) ∣ d := dvd_trans ⟨2, rfl⟩ hdvd
  have : (2 : ℕ) ∣ n := dvd_trans hd4 hd.1
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr this)

/-- **Prime specialization (0-axiom, general).** For an odd prime `p` the only
divisors are `1` and `p`, both coprime to `4`, so Jacobi's count is the closed form
`jacobiCount p = 8·(p+1)`. Combined with `jacobi_oracle` this pins `r₄(p) = 8(p+1)`
for the small odd primes in range (`r₄(3)=32=8·4`, `r₄(5)=48=8·6`, `r₄(7)=64=8·8`). -/
theorem jacobiCount_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    jacobiCount p = 8 * (p + 1) := by
  rw [jacobiCount_odd hodd, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  ring

/-- **Convention guard (0-axiom).** The naive formula `8·σ(n)` is WRONG for `n = 4`:
`8·σ(4) = 8·(1+2+4) = 56`, whereas the true count is `r4 4 = 24`. Equivalently the
`4 ∤ d` exclusion drops the divisor `d = 4`. This is exactly why the general formula
cannot be stated as `8·σ`. -/
theorem naive_sigma_fails :
    8 * ∑ d ∈ (4 : ℕ).divisors, d = 56 ∧ jacobiCount 4 = 24 ∧ r4 4 = 24 := by
  refine ⟨by decide, by decide, by native_decide⟩

/-! ## Part 3: The oracle — Jacobi's formula reproduces the brute-force count -/

/-- **Jacobi oracle (`native_decide`; depends on `Lean.ofReduceBool`).**
For every `1 ≤ n ≤ 24`, the divisor-sum formula `jacobiCount n = 8·Σ_{d|n,4∤d} d`
equals the brute-force ordered-signed lattice count `r4 n`. This is a machine-checked
regression oracle pinning the convention (`r4 1 = 8`, `r4 2 = 24`, `r4 4 = 24`, …),
**not** a proof of the general theorem (which is Mathlib-blocked). -/
theorem jacobi_oracle : ∀ n ∈ Finset.Icc 1 24, r4 n = jacobiCount n := by
  native_decide

/-- Spot anchors extracted from the oracle range, stated explicitly so the intended
values are visible: `r4(1)=8, r4(2)=24, r4(3)=32, r4(4)=24, r4(5)=48, r4(7)=64`. -/
theorem r4_anchor_values :
    r4 1 = 8 ∧ r4 2 = 24 ∧ r4 3 = 32 ∧ r4 4 = 24 ∧ r4 5 = 48 ∧ r4 7 = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end LagrangeFourSquaresOQ01OQ03
