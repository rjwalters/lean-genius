/-!
# Erdős Problem #667 — Clique Density Exponent c(p,q)

For fixed integers p, q ≥ 1, define H(n; p, q) as the largest m such that
every graph on n vertices where every set of p vertices spans at least q
edges must contain a complete graph on m vertices.

Define c(p, q) = lim inf (log H(n; p, q)) / (log n).

## Question

Is c(p, q) strictly increasing in q for 1 ≤ q ≤ C(p-1, 2) + 1?

## Known results

- q = 1: reduces to classical Ramsey; 1/(p-1) ≤ c(p,1) ≤ 2/(p+1)
- q = C(p-1,2) + 1: every p-set spans a complete graph, so c(p,q) = 1
- Erdős–Faudree–Rousseau–Schelp: c(p, ⌊(p-1)/2⌋) ≤ 1/2

Reference: https://erdosproblems.com/667
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## The function H(n; p, q) -/

/-- H(n; p, q): the largest clique size guaranteed in any n-vertex graph
    where every p-vertex subset spans at least q edges.
    Axiomatised as a function ℕ → ℕ → ℕ → ℕ. -/
axiom cliqueGuarantee : ℕ → ℕ → ℕ → ℕ

/-- H is monotone in n: more vertices can only help. -/
axiom cliqueGuarantee_mono_n (p q n : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee (n + 1) p q

/-- H is monotone in q: more edges per p-set helps. -/
axiom cliqueGuarantee_mono_q (n p q : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee n p (q + 1)

/-! ## Boundary values -/

/-- When q = C(p-1, 2) + 1, every p-set is a clique, so H(n; p, q) = n
    (every graph satisfying this is complete). -/
axiom cliqueGuarantee_max (n p : ℕ) (hp : 2 ≤ p) :
    cliqueGuarantee n p (Nat.choose (p - 1) 2 + 1) = n

/-- When q = 0, there is no constraint, so H = 1 (trivially). -/
axiom cliqueGuarantee_zero (n p : ℕ) (hn : 1 ≤ n) :
    cliqueGuarantee n p 0 = 1

/-! ## The exponent c(p, q) -/

/-- c(p, q) = lim inf log(H(n;p,q)) / log(n).
    Axiomatised as a rational-valued function. -/
axiom cpq : ℕ → ℕ → ℚ

/-- c(p, 1) ≥ 1/(p-1) (Ramsey lower bound). -/
axiom cpq_lower_ramsey (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℚ) / ((p : ℚ) - 1) ≤ cpq p 1

/-- c(p, 1) ≤ 2/(p+1) (Ramsey upper bound). -/
axiom cpq_upper_ramsey (p : ℕ) (hp : 2 ≤ p) :
    cpq p 1 ≤ (2 : ℚ) / ((p : ℚ) + 1)

/-- c(p, C(p-1,2)+1) = 1. -/
axiom cpq_at_max (p : ℕ) (hp : 2 ≤ p) :
    cpq p (Nat.choose (p - 1) 2 + 1) = 1

/-- Erdős–Faudree–Rousseau–Schelp: c(p, ⌊(p-1)/2⌋) ≤ 1/2. -/
axiom efrs_bound (p : ℕ) (hp : 3 ≤ p) :
    cpq p ((p - 1) / 2) ≤ (1 : ℚ) / 2

/-! ## Main conjecture -/

/-- Erdős Problem 667: c(p, q) is strictly increasing in q for
    1 ≤ q ≤ C(p-1, 2) + 1. -/
def ErdosProblem667 : Prop :=
    ∀ (p : ℕ) (hp : 3 ≤ p),
      ∀ (q : ℕ), 1 ≤ q → q < Nat.choose (p - 1) 2 + 1 →
        cpq p q < cpq p (q + 1)
