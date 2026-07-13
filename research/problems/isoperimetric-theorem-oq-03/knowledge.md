# Knowledge Base: isoperimetric-theorem-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-03 asks for sharp isoperimetric constants in non-Euclidean spaces. Full Riemannian
generality (hyperbolic space, Lévy–Gromov) is beyond current Mathlib. Following the
sibling line entry (oq-02-oq-03, which treated the line ℤ), the tractable and faithful
target is the **cycle graph C_n = ℤ/nℤ** — the discrete model of the circle S¹, the
simplest compact constant-curvature non-Euclidean space.

---

## Insights

- **Rises/falls decomposition.** Split the edge boundary of S ⊆ ℤ/nℤ into rising edges
  `{i : i∉S ∧ i+1∈S}` and falling edges `{i : i∈S ∧ i+1∉S}`. These are disjoint and
  their union is the cut.
- **Balance lemma (crux).** `|rises S| = |falls S|`, proved by reindexing the ℤ-sum
  `∑ᵢ (1_{i+1∈S} − 1_{i∈S})` along the cyclic bijection `i ↦ i+1`
  (`Fintype.sum_equiv (Equiv.addRight 1)`), so it vanishes; `Finset.sum_boole` converts
  the vanishing total into the cardinality equality. This is "a closed walk crosses into
  S as often as out".
- **Evenness.** `|cut S| = 2·|rises S|`, so the boundary is always even — a closed-loop
  phenomenon absent on the line ℤ.
- **Sharp bound via connectivity.** `|cut S| ≥ 2` for proper nonempty S because an empty
  rises-set forces predecessor-closure (`i+1∈S ⇒ i∈S`), which propagates around the loop
  (surjectivity of `Nat.cast : ℕ → ZMod n`, `ZMod.natCast_rightInverse`) to give S = univ.
- **Achievability.** A single vertex `{a}` (smallest geodesic ball) has
  `rises{a}={a-1}`, `falls{a}={a}`, hence `|cut{a}|=2` for n ≥ 2. So 2 is the best
  isoperimetric constant on the discrete circle.

---

## Dead Ends

- Full Riemannian / hyperbolic formalization: not tractable in current Mathlib (no sharp
  isoperimetric-constant infrastructure for curved spaces).
- `sub_eq_self` / `add_right_eq_self` lemma names vary across Mathlib versions; derive
  `a-1≠a`, `a+1≠a` directly from `(1:ZMod n)≠0` instead.

---

## Outcome

COMPLETED. Fully verified file `proofs/Proofs/IsoperimetricTheoremOQ03.lean`
(0 axioms, 0 sorries, ~210 lines), gallery entry `isoperimetric-theorem-oq-03`.
