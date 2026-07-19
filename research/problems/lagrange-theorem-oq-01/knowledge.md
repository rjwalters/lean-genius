# Knowledge Base: lagrange-theorem-oq-01

**Problem**: Can the Sylow theorems / partial converse of Lagrange be formalized? (finite-group
order-classification programme built on Lagrange's theorem)

## Current state (triage 2026-07-19, researcher-1)

The `LagrangeTheorem*` corpus is large (32 files) and mature. A corpus-wide scan found:

- **0 real sorries** anywhere (`grep` hits are all docstring prose like "0-sorry / 0-axiom").
- **4 `axiom` declarations, all Hall's theorem for solvable groups** — genuinely irreducible
  against Mathlib v4.31:
  - `LagrangeTheoremOQ01OQ03.lean`: `hall_solvable`, `hall_characterizes_solvability`
  - `LagrangeTheoremOQ03.lean`: `hall_existence`, `hall_conjugacy`
  - **Why irreducible:** Mathlib has only the *combinatorial* Hall marriage theorem
    (`Mathlib/Combinatorics/Hall`) and `SchurZassenhaus` (the coprime-normal special case). There
    is **no** general Hall π-subgroup existence/conjugacy theorem for finite solvable groups in
    Mathlib. So these 4 axioms cannot currently be discharged. (Reopen criterion: Mathlib upstreams
    a general solvable-group Hall theorem.)

## Extensions (from the tracker's currentState) — status

- **(b) order-p² groups are abelian, cyclic vs (ℤ/p)² fork — DONE.** `LagrangeTheoremOQ01PSquare.lean`
  (0 sorry / 0 axiom): `card_prime_sq_commutative`, `commGroupOfCardPrimeSq`, the dichotomy
  `card_prime_sq_cyclic_or_pow_p_eq_one`, plus concrete orders 4/9/25/49. Wraps Mathlib
  `IsPGroup.isMulCommutative_of_card_eq_prime_sq`.
- **(a) nonabelian order-pq witness (ℤ/q⋊ℤ/p when q≡1 mod p)** — the corpus already carries
  dihedral / semidirect / metacyclic content (`LagrangeTheoremOQ01OQ01*`, `OQ09`); the pq
  cyclic-vs-metacyclic dichotomy is recorded as CLOSED in the tracker. Any remaining witness-
  construction refinement would be a `SemidirectProduct` build — genuinely finicky, verify against
  existing files before starting to avoid duplication.
- **(c) order p²q / p³ classification** — hard, multi-session; not attempted.

## Assessment

No session-sized formalization gap: the tractable order-classification extensions (p², pq) are
complete, the deep Hall axioms are blocked on missing Mathlib infrastructure, and there are no
sorries to eliminate. Deeper classifications (p²q, p³) are multi-session. Recorded for the next
researcher so the Mathlib-Hall check and the corpus sorry/axiom scan need not be repeated.
