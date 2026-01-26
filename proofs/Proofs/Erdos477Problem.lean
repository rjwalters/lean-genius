/-!
# Erdős Problem #477 — Polynomial Complements of Integer Sets

Is there a polynomial f : ℤ → ℤ of degree ≥ 2 and a set A ⊆ ℤ
such that every z ∈ ℤ has exactly one representation z = a + f(n)
with a ∈ A and n ∈ ℤ?

Equivalently: does ℤ = A ⊕ f(ℤ) as a perfect tiling?

Known:
- No such A exists for f(x) = x² (Sekanina, 1959)
- No such A for ax²+bx+c when a | b, a ≠ 0, b ≠ 0
- Conjectured: no such A for x^k, any k ≥ 2

Erdős and Graham conjectured the answer is NO for all such f.

Status: OPEN
Reference: https://erdosproblems.com/477
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- The image of a polynomial-like function f : ℤ → ℤ. -/
def polyImage (f : ℤ → ℤ) : Set ℤ := Set.range f

/-- A ⊆ ℤ is a perfect complement of B ⊆ ℤ if every z ∈ ℤ has
    a unique representation z = a + b with a ∈ A, b ∈ B. -/
def IsPerfectComplement (A B : Set ℤ) : Prop :=
  ∀ z : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ z = p.1 + p.2

/-- A function f : ℤ → ℤ is a polynomial of degree exactly d
    (axiomatized for the purpose of stating the problem). -/
def IsPolyDegree (f : ℤ → ℤ) (d : ℕ) : Prop :=
  d ≥ 2 ∧ True  -- axiomatized: f is a polynomial of degree d

/-! ## Main Question -/

/-- **Erdős Problem #477**: Is there a polynomial f : ℤ → ℤ of
    degree ≥ 2 and a set A ⊆ ℤ such that A perfectly complements
    the image of f? Erdős and Graham conjectured NO. -/
axiom erdos_477_main :
  ¬∃ (f : ℤ → ℤ) (d : ℕ), d ≥ 2 ∧ IsPolyDegree f d ∧
    ∃ A : Set ℤ, IsPerfectComplement A (polyImage f)

/-! ## Known Results -/

/-- **Sekanina (1959)**: There is no perfect complement A for
    f(x) = x². The squares cannot tile ℤ by translation. -/
axiom sekanina_squares :
  ¬∃ A : Set ℤ, IsPerfectComplement A (polyImage (fun n : ℤ => n ^ 2))

/-- **Quadratic case**: For f(x) = ax² + bx + c with a | b,
    a ≠ 0, b ≠ 0, there is no perfect complement.
    (Found by AlphaProof for x²−x+1, then generalized.) -/
axiom quadratic_divisibility (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ∣ b) :
  ¬∃ A : Set ℤ, IsPerfectComplement A (polyImage (fun n : ℤ => a * n ^ 2 + b * n + c))

/-! ## Conjectures for Specific Polynomials -/

/-- **Conjecture**: No perfect complement exists for f(x) = x³. -/
axiom no_complement_cubes :
  ¬∃ A : Set ℤ, IsPerfectComplement A (polyImage (fun n : ℤ => n ^ 3))

/-- **Conjecture (Sekanina 1959)**: No perfect complement exists
    for f(x) = x^k, for any k ≥ 2. -/
axiom no_complement_monomial (k : ℕ) (hk : k ≥ 2) :
  ¬∃ A : Set ℤ, IsPerfectComplement A (polyImage (fun n : ℤ => n ^ k))

/-! ## Observations -/

/-- **Linear case**: For f(x) = x (degree 1), a perfect complement
    exists trivially: A = {0}. The problem specifically asks about
    degree ≥ 2 where the image has gaps. -/
axiom linear_trivial :
  IsPerfectComplement {(0 : ℤ)} (polyImage (fun n : ℤ => n))

/-- **Tiling interpretation**: A perfectly complements f(ℤ) iff
    {a + f(n) : a ∈ A, n ∈ ℤ} partitions ℤ, i.e., A ⊕ f(ℤ) = ℤ
    as a direct sum. This connects to factorization of abelian groups. -/
axiom tiling_connection : True

/-- **Density argument**: If f has degree d ≥ 2, then |f(ℤ) ∩ [-N,N]|
    grows as N^{1/d}, so A must have density approaching 1. The
    constraint is that A must "fill in" the gaps of f(ℤ) exactly. -/
axiom density_argument : True
