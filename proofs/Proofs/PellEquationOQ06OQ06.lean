/-
Pell's Equation OQ-06-OQ-06: The Brahmagupta Composition Law and the Group
Structure of the Solutions of x² − 2y² = ±1

The parent lineage builds up a great deal of *structure* on the negative-Pell
chain — its closed form as the odd powers of the fundamental unit ζ = 1 + √2
(`pell-equation-oq-06-oq-02`), its linear recurrence (`-oq-03`), its role as best
rational approximations of √2 (`-oq-04`), and the Cassini-type constant determinant
of consecutive solutions (`-oq-05`). Every one of those results is, at bottom, a
shadow of a single algebraic fact that this entry isolates and proves directly:

  **the solutions of x² − 2y² = ±1 are closed under Brahmagupta composition, and
  composition realizes multiplication in ℤ[√2].**

Brahmagupta's composition (the *bhāvanā*, c. 628 CE) is the binary operation

    (x, y) ⊛ (u, v) = (x·u + 2·y·v,  x·v + y·u),

which is exactly the multiplication ⟨x,y⟩ · ⟨u,v⟩ of quadratic integers in ℤ[√2].
Its defining feature is the **Brahmagupta–Fibonacci identity** for the form x² − 2y²:

    (x² − 2y²)(u² − 2v²) = (x·u + 2·y·v)² − 2·(x·v + y·u)².            (brahmagupta)

In Mathlib this is precisely the multiplicativity of `Zsqrtd.norm` (`Zsqrtd.norm_mul`),
but it is never stated in this self-contained, elementary two-integer form, so we
record it directly (a one-line `ring` proof) and then read off its consequences.

Consequences proven here:
  • the composition is commutative, associative, with identity `(1, 0)` — so the
    pairs `(x, y)` form a commutative monoid and the norm `x² − 2y²` is a monoid
    homomorphism to `(ℤ, ·)` (`pellNorm_compose`);
  • the solutions of |x² − 2y²| = 1 (the units of ℤ[√2]) are **closed** under
    composition (`pellNorm_compose_sq`, `compose_unit_closed`);
  • the **sign law**: composing two negative-Pell solutions gives a *positive*-Pell
    solution (`compose_neg_neg`), because (−1)·(−1) = +1 — the deep reason the
    chain only realizes the *odd* powers of ζ;
  • applied to the parent chain, `negPellSeq m ⊛ negPellSeq n = ζ^(2(m+n)+2)`, an
    even power of the fundamental unit and hence a positive-Pell solution
    (`compose_negPellSeq_eq_pow`, `compose_negPellSeq_norm`) — generalizing the
    `m = n` "squaring" result of `-oq-01` to an arbitrary composition.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent: `pell-equation-oq-06` (chain, infinitude); `-oq-02` (powers of ζ).
- Brahmagupta, *Brāhmasphuṭasiddhānta* (628 CE) — the composition law (bhāvanā).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`Zsqrtd`, `Zsqrtd.norm`,
  `Zsqrtd.norm_mul`, `Zsqrtd.norm_def`).
-/

import Mathlib
import Proofs.PellEquationOQ06
import Proofs.PellEquationOQ06OQ02

namespace PellEquationOQ06OQ06

open PellEquationOQ06 PellEquationOQ06OQ02

/-
## Brahmagupta composition and the Pell norm
-/

/-- **Brahmagupta composition (bhāvanā).** The binary operation on pairs that
    realizes multiplication of `⟨x,y⟩ = x + y√2` in ℤ[√2]:
    `(x, y) ⊛ (u, v) = (x·u + 2·y·v, x·v + y·u)`. -/
def compose (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 + 2 * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- The Pell quadratic form `N(x, y) = x² − 2y²` (the norm of `x + y√2`). -/
def pellNorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - 2 * p.2 ^ 2

/-- **The Pell form is the ℤ[√2]-norm.** `N(x, y) = x² − 2y² = Zsqrtd.norm ⟨x, y⟩`,
    so the elementary statements below are the concrete face of Mathlib's
    quadratic-integer norm. -/
theorem pellNorm_eq_zsqrtd_norm (p : ℤ × ℤ) :
    pellNorm p = (⟨p.1, p.2⟩ : ℤ√2).norm := by
  rw [pellNorm, Zsqrtd.norm_def]; ring

/-- **Composition is multiplication in ℤ[√2].** `⟨(p ⊛ q).1, (p ⊛ q).2⟩ = ⟨p⟩ · ⟨q⟩`.
    This is the bridge that makes the monoid laws below free. -/
theorem compose_eq_mul (p q : ℤ × ℤ) :
    (⟨(compose p q).1, (compose p q).2⟩ : ℤ√2)
      = (⟨p.1, p.2⟩ : ℤ√2) * (⟨q.1, q.2⟩ : ℤ√2) := by
  refine Zsqrtd.ext ?_ ?_ <;> simp [compose, Zsqrtd.re_mul, Zsqrtd.im_mul]

/-
## The Brahmagupta–Fibonacci identity and multiplicativity of the norm
-/

/-- **Brahmagupta–Fibonacci identity** for the form `x² − 2y²` (the *bhāvanā*):
    `(x² − 2y²)(u² − 2v²) = (x·u + 2·y·v)² − 2·(x·v + y·u)²`. A single `ring`
    identity — the algebraic heart of the entire Pell lineage. -/
theorem brahmagupta (x y u v : ℤ) :
    (x ^ 2 - 2 * y ^ 2) * (u ^ 2 - 2 * v ^ 2)
      = (x * u + 2 * y * v) ^ 2 - 2 * (x * v + y * u) ^ 2 := by
  ring

/-- **The Pell norm is multiplicative under composition:**
    `N(p ⊛ q) = N(p) · N(q)`. This is `brahmagupta` packaged on pairs — equivalently
    `Zsqrtd.norm_mul` transported through `pellNorm_eq_zsqrtd_norm`. It says
    `pellNorm` is a monoid homomorphism `(ℤ×ℤ, ⊛) → (ℤ, ·)`. -/
theorem pellNorm_compose (p q : ℤ × ℤ) :
    pellNorm (compose p q) = pellNorm p * pellNorm q := by
  simp only [pellNorm, compose]; ring

/-
## Monoid laws (inherited from ℤ[√2])
-/

/-- Composition is **commutative**. -/
theorem compose_comm (p q : ℤ × ℤ) : compose p q = compose q p := by
  simp only [compose, Prod.mk.injEq]; constructor <;> ring

/-- Composition is **associative**. -/
theorem compose_assoc (p q r : ℤ × ℤ) :
    compose (compose p q) r = compose p (compose q r) := by
  simp only [compose, Prod.mk.injEq]; constructor <;> ring

/-- `(1, 0)` (the unit `1 ∈ ℤ[√2]`) is a **two-sided identity** for composition. -/
theorem compose_one (p : ℤ × ℤ) : compose p (1, 0) = p := by
  obtain ⟨a, b⟩ := p
  simp only [compose, Prod.mk.injEq]; constructor <;> ring

/-- The identity `(1, 0)` is itself a (positive) Pell solution: `N(1, 0) = 1`. -/
theorem pellNorm_one : pellNorm (1, 0) = 1 := by decide

/-
## Closure: the units of ℤ[√2] form a group under composition
-/

/-- The squared norm is multiplicative, so units (`N = ±1 ⟺ N² = 1`) are detected
    multiplicatively: `N(p ⊛ q)² = N(p)² · N(q)²`. -/
theorem pellNorm_compose_sq (p q : ℤ × ℤ) :
    pellNorm (compose p q) ^ 2 = pellNorm p ^ 2 * pellNorm q ^ 2 := by
  rw [pellNorm_compose, mul_pow]

/-- **Closure of the unit group.** If `p` and `q` are units of ℤ[√2]
    (i.e. `|N| = 1`, encoded as `N² = 1`), then so is `p ⊛ q`. The solutions of
    `x² − 2y² = ±1` are closed under Brahmagupta composition. -/
theorem compose_unit_closed (p q : ℤ × ℤ)
    (hp : pellNorm p ^ 2 = 1) (hq : pellNorm q ^ 2 = 1) :
    pellNorm (compose p q) ^ 2 = 1 := by
  rw [pellNorm_compose_sq, hp, hq, mul_one]

/-
## The sign law and the parent chain
-/

/-- **Sign law (negative ⊛ negative = positive).** Composing two solutions of the
    *negative* Pell equation `x² − 2y² = −1` yields a solution of the *positive*
    Pell equation `x² − 2y² = +1`, since `(−1)·(−1) = +1`. This is precisely why
    the negative-Pell chain occupies only the *odd* powers of ζ: composition pushes
    it into the even (norm `+1`) powers. -/
theorem compose_neg_neg (p q : ℤ × ℤ)
    (hp : pellNorm p = -1) (hq : pellNorm q = -1) :
    pellNorm (compose p q) = 1 := by
  rw [pellNorm_compose, hp, hq]; ring

/-- `pellNorm` of the parent chain is `−1` (the parent's `negPellSeq_norm`,
    restated for `pellNorm`). -/
theorem pellNorm_negPellSeq (n : ℕ) : pellNorm (negPellSeq n) = -1 :=
  negPellSeq_norm n

/-- **Composition of two chain elements is an even power of ζ.**
    `negPellSeq m ⊛ negPellSeq n = ζ^(2m+1) · ζ^(2n+1) = ζ^(2(m+n)+2)` in ℤ[√2].
    Generalizes the `m = n` squaring of `-oq-01` to an arbitrary composition. -/
theorem compose_negPellSeq_eq_pow (m n : ℕ) :
    (⟨(compose (negPellSeq m) (negPellSeq n)).1,
       (compose (negPellSeq m) (negPellSeq n)).2⟩ : ℤ√2)
      = ζ ^ (2 * (m + n) + 2) := by
  rw [compose_eq_mul, negPellSeq_eq_pow, negPellSeq_eq_pow, ← pow_add]
  congr 1; ring

/-- **The composition of the m-th and n-th negative-Pell solutions solves the
    *positive* Pell equation** `x² − 2y² = +1`. A direct instance of the sign law
    on the parent chain. -/
theorem compose_negPellSeq_norm (m n : ℕ) :
    pellNorm (compose (negPellSeq m) (negPellSeq n)) = 1 :=
  compose_neg_neg _ _ (pellNorm_negPellSeq m) (pellNorm_negPellSeq n)

/-
## Sanity checks
-/

-- The Brahmagupta identity on the fundamental solution composed with itself:
-- (1,1) ⊛ (1,1) = (1·1 + 2·1·1, 1·1 + 1·1) = (3, 2), the norm-+1 unit 3 + 2√2.
example : compose (1, 1) (1, 1) = (3, 2) := by decide
example : pellNorm (3, 2) = 1 := by decide
-- (1,1) is the negative-Pell fundamental solution; composing it with itself
-- lands on the positive-Pell solution (3, 2): negative ⊛ negative = positive.
example : pellNorm (compose (1, 1) (1, 1)) = 1 := compose_neg_neg _ _ (by decide) (by decide)
-- (7,5) ⊛ (1,1) = (7+10, 7+5) = (17, 12): N = 289 − 288 = 1.
example : compose (7, 5) (1, 1) = (17, 12) := by decide
example : pellNorm (17, 12) = 1 := by decide

#check @brahmagupta
#check @compose_eq_mul
#check @pellNorm_compose
#check @compose_assoc
#check @compose_unit_closed
#check @compose_neg_neg
#check @compose_negPellSeq_norm

end PellEquationOQ06OQ06
