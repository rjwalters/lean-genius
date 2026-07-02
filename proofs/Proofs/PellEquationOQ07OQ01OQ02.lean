/-
Pell's Equation OQ-07 → OQ-01 → OQ-02: The Cassini Defect Calculus

The sibling entry (`pell-equation-oq-07-oq-01-oq-01`) proves the Cassini / Catalan
identities for the *Pell* coordinate sequences `re(aⁿ)`, `im(aⁿ)` by conjugate
algebra in `ℤ√d`. This entry extracts the **abstract structural theorem** behind
those identities — and behind the Fibonacci Cassini identity `Fₙ₋₁Fₙ₊₁ − Fₙ² =
(−1)ⁿ` — as a small calculus of the *Cassini defect* of any second-order linear
recurrence over any commutative ring.

## The Cassini defect

For a sequence `u : ℕ → R` define the **Cassini defect**

    D(k) = u(k+2)·u(k) − u(k+1)².

If `u` obeys the second-order recurrence `u(n+2) = p·u(n+1) − q·u(n)`, then the
defect obeys a *first-order* recurrence of its own:

    D(k+1) = q·D(k)                                   (`cassiniDefect_succ`)

because substituting the recurrence for the two top terms collapses
`D(k+1) − q·D(k)` to `u(k+2)·(p·u(k+1) − q·u(k) − u(k+2)) = 0`. Integrating,

    D(k) = qᵏ·D(0)                                    (`cassiniDefect_eq`)

— the whole Cassini/Catalan phenomenon in one line. The defect is moreover the
determinant of the 2×2 **state matrix** whose columns are consecutive state
vectors of the recurrence,

    D(k) = det !![u(k+2), u(k+1); u(k+1), u k]        (`cassiniDefect_eq_det`)

and the recurrence companion `C = !![p, −q; 1, 0]` has `det C = q`, so
`D(k) = qᵏ·D(0)` is exactly `det(Cᵏ·W₀) = (det C)ᵏ·det(W₀)` — the determinant
identity `det(Mⁿ) = (det M)ⁿ` the grandparent's companion matrix was pointing at,
now in its sharpest form (`cassini_det_eq`).

## Instantiations

* **Fibonacci** (`p = 1`, `q = −1`): `D(k) = (−1)ᵏ·D(0)`, i.e.
  `Fₖ₊₂Fₖ − Fₖ₊₁² = (−1)ᵏ(F₂F₀ − F₁²)`, giving Cassini `= (−1)ᵏ⁺¹` for the
  standard seed `F₀ = 0, F₁ = 1`.
* **Pell** (`p = 2·re a`, `q = N(a)`, via the grandparent's `re_recurrence`):
  recovers the sibling's `re_cassini`; for a Pell unit (`N(a) = 1`) the defect is
  the *constant* `d·y₁²`, independent of `k`.

## Main results

* `cassiniDefect` (def) — `D(k) = u(k+2)·u(k) − u(k+1)²`.
* `cassiniDefect_succ` — `D(k+1) = q·D(k)` from the recurrence.
* `cassiniDefect_eq` — `D(k) = qᵏ·D(0)` (integration of the scaling law).
* `cassiniDefect_eq_det` — `D(k) = det` of the state matrix.
* `cassini_det_eq` — the determinant form `det(W k) = qᵏ·det(W 0)`, i.e.
  `det(Cᵏ·W₀) = (det C)ᵏ·det(W₀)`.
* Fibonacci and Pell instantiations, and `D = 2` numeric checks.

All proofs are `sorry`-free and axiom-free (the one `decide` is kernel `decide`,
not `native_decide`).

References:
- Sibling: `pell-equation-oq-07-oq-01-oq-01` (the Pell-specific Cassini/Catalan
  identities via conjugate algebra).
- Grandparent: `pell-equation-oq-07` (`Zsqrtd.re_recurrence`, `im_recurrence`).
- Classical: Cassini (1680) `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ`; the second-order-recurrence
  determinant invariant.
-/

import Proofs.PellEquationOQ07OQ01

namespace PellEquationOQ07OQ01OQ02

open Zsqrtd

/-- The **Cassini defect** of a sequence `u` at index `k`:
`D(k) = u(k+2)·u(k) − u(k+1)²`. For a second-order recurrence this off-by-one
product-minus-square is the invariant behind every Cassini/Catalan identity. -/
def cassiniDefect {R : Type*} [CommRing R] (u : ℕ → R) (k : ℕ) : R :=
  u (k + 2) * u k - u (k + 1) ^ 2

/-- **The Cassini defect scales by `q` at each step.** If `u(n+2) = p·u(n+1) −
q·u(n)`, then `D(k+1) = q·D(k)`: substituting the recurrence for the two top terms
makes `D(k+1) − q·D(k)` collapse to `u(k+2)·(p·u(k+1) − q·u(k) − u(k+2)) = 0`. -/
theorem cassiniDefect_succ {R : Type*} [CommRing R] (u : ℕ → R) (p q : R)
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n) (k : ℕ) :
    cassiniDefect u (k + 1) = q * cassiniDefect u k := by
  simp only [cassiniDefect]
  show u (k + 3) * u (k + 1) - u (k + 2) ^ 2
      = q * (u (k + 2) * u k - u (k + 1) ^ 2)
  have h1 : u (k + 3) = p * u (k + 2) - q * u (k + 1) := hrec (k + 1)
  have h2 : u (k + 2) = p * u (k + 1) - q * u k := hrec k
  linear_combination u (k + 1) * h1 - u (k + 2) * h2

/-- **The integrated Cassini identity.** `D(k) = qᵏ·D(0)` — the defect at index `k`
is `qᵏ` times its base value, by induction from the one-step scaling law. This is
the abstract Cassini/Catalan theorem: `u(k+2)·u(k) − u(k+1)² = qᵏ·(u₂·u₀ − u₁²)`. -/
theorem cassiniDefect_eq {R : Type*} [CommRing R] (u : ℕ → R) (p q : R)
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n) (k : ℕ) :
    cassiniDefect u k = q ^ k * cassiniDefect u 0 := by
  induction k with
  | zero => simp
  | succ n ih => rw [cassiniDefect_succ u p q hrec, ih, pow_succ]; ring

/-- **The Cassini defect is a determinant.** `D(k)` is the determinant of the state
matrix `W k = !![u(k+2), u(k+1); u(k+1), u k]`, whose columns are the consecutive
state vectors `(u(k+2),u(k+1))`, `(u(k+1),u k)` of the recurrence. -/
theorem cassiniDefect_eq_det {R : Type*} [CommRing R] (u : ℕ → R) (k : ℕ) :
    cassiniDefect u k
      = (!![u (k + 2), u (k + 1); u (k + 1), u k] : Matrix (Fin 2) (Fin 2) R).det := by
  rw [cassiniDefect, Matrix.det_fin_two_of]; ring

/-- **The determinant form of the Cassini identity.** `det(W k) = qᵏ·det(W 0)` for
the state matrix `W`. Since the recurrence companion `C = !![p,−q;1,0]` has
`det C = q` and advances the state (`W k = Cᵏ·W₀`), this is exactly
`det(Cᵏ·W₀) = (det C)ᵏ·det(W₀)` — the sharp form of `det(Mⁿ) = (det M)ⁿ`. -/
theorem cassini_det_eq {R : Type*} [CommRing R] (u : ℕ → R) (p q : R)
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n) (k : ℕ) :
    (!![u (k + 2), u (k + 1); u (k + 1), u k] : Matrix (Fin 2) (Fin 2) R).det
      = q ^ k * (!![u 2, u 1; u 1, u 0] : Matrix (Fin 2) (Fin 2) R).det := by
  rw [← cassiniDefect_eq_det, ← cassiniDefect_eq_det, cassiniDefect_eq u p q hrec]

/-
## Fibonacci instantiation (`p = 1`, `q = −1`)

The classical Cassini identity `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ` is the `q = −1` case:
`D(k) = (−1)ᵏ·D(0)`.
-/

/-- **Fibonacci Cassini.** Any sequence with `F(n+2) = F(n+1) + F(n)` satisfies
`Fₖ₊₂·Fₖ − Fₖ₊₁² = (−1)ᵏ·(F₂F₀ − F₁²)`; for the standard seed `F₀ = 0, F₁ = 1`
this is `= (−1)ᵏ⁺¹`, i.e. Cassini's identity. -/
example (F : ℕ → ℤ) (hF : ∀ n, F (n + 2) = F (n + 1) + F n) (k : ℕ) :
    F (k + 2) * F k - F (k + 1) ^ 2 = (-1) ^ k * (F 2 * F 0 - F 1 ^ 2) := by
  have h := cassiniDefect_eq F 1 (-1) (fun n => by rw [hF n]; ring) k
  simpa [cassiniDefect] using h

/-
## Pell instantiation (`p = 2·re a`, `q = N(a)`)

Feeding the grandparent's `re_recurrence` into `cassiniDefect_eq` recovers the
sibling's Pell real-coordinate Cassini identity, and for a Pell unit (`N(a) = 1`)
the defect is a constant.
-/

/-- **Pell real-coordinate Cassini** (recovers the sibling `re_cassini`). -/
example {d : ℤ} (a : ℤ√d) (k : ℕ) :
    (a ^ (k + 2)).re * (a ^ k).re - (a ^ (k + 1)).re ^ 2
      = a.norm ^ k * ((a ^ 2).re * (a ^ 0).re - (a ^ 1).re ^ 2) := by
  have h := cassiniDefect_eq (fun n => (a ^ n).re) (2 * a.re) a.norm
    (fun n => PellEquationOQ07.Zsqrtd.re_recurrence a n) k
  simpa [cassiniDefect] using h

/-- **The constant Cassini invariant of a Pell unit.** For `N(a) = 1` the factor
`N(a)ᵏ = 1` disappears, so `re(aₖ₊₁)·re(aₖ₋₁) − re(aₖ)² = d·y₁²` is constant in `k`. -/
example {d : ℤ} (a : ℤ√d) (h : a.norm = 1) (k : ℕ) :
    (a ^ (k + 2)).re * (a ^ k).re - (a ^ (k + 1)).re ^ 2 = d * a.im ^ 2 := by
  have hd := cassiniDefect_eq (fun n => (a ^ n).re) (2 * a.re) a.norm
    (fun n => PellEquationOQ07.Zsqrtd.re_recurrence a n) k
  simp only [cassiniDefect, h, one_pow, one_mul] at hd
  rw [hd]
  have h2 : (a ^ 2).re = a.re ^ 2 + d * a.im ^ 2 := by
    rw [pow_two, Zsqrtd.re_mul]; ring
  rw [h2, pow_zero, pow_one, Zsqrtd.re_one]; ring

/-- **`D = 2` numeric check.** The base defect of the fundamental unit `3 + 2√2`
is `re(a²)·re(a⁰) − re(a¹)² = 17·1 − 9 = 8 = d·y₁² = 2·2²`; being a Pell unit
(`q = 1`), the defect stays `8` at every index. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re * ((⟨3, 2⟩ : ℤ√2) ^ 0).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).re ^ 2 = 8 := by decide

#check @cassiniDefect
#check @cassiniDefect_succ
#check @cassiniDefect_eq
#check @cassiniDefect_eq_det
#check @cassini_det_eq

end PellEquationOQ07OQ01OQ02
