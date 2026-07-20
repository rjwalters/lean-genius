# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03

## Session 2026-07-20 (researcher-1) — Frobenius EQUALITY dim C(T) = dim V for cyclic endomorphisms

New file `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Frobenius.lean` (namespace `EndCyclicCommutant`,
imports `...OQ02OQ03` + `...OQ02OQ01`). VERIFIED clean Docker build (v4.31.0); all three theorems
depend only on `[propext, Classical.choice, Quot.sound]` (0 axioms / 0 sorries, `#print axioms`).

Sharpens the general Frobenius LOWER bound (`CyclicCommutantConverse.endK_centralizer_bound`:
`dim_K V ≤ dim_K C(φ)` for every φ, already proven via PID primary decomposition) to an EQUALITY
in the cyclic case:

- `commuting_end_eq_of_apply_eq` — two operators commuting with T that agree on a cyclic vector v
  are equal. (They agree on the whole Krylov basis {Tᵏv} since A·Tᵏv = Tᵏ·Av; `Basis.ext`.)
  = injectivity of the evaluation map A ↦ A·v on the centralizer.
- `finrank_centralizer_le_of_cyclic` — dim C(T) ≤ dim V, via that injective K-linear eval map
  `↥(toSubmodule (centralizer K {T})) →ₗ[K] V`, `LinearMap.finrank_le_finrank_of_injective`.
- `finrank_centralizer_eq_of_cyclic` — dim C(T) = dim V (`le_antisymm` of the two bounds).

This is the minimal-centralizer / nonderogatory edge of the triangle nonderogatory ⟺ cyclic ⟺
C(T)=K[T], lifted to the coordinate-free Module.End setting (the matrix analogue lived in oq-02-oq-01).

### Findings / reuse
- The recorded next-step "endomorphism Frobenius bound dim C(T) ≥ finrank V" was ALREADY DONE in
  general form as `CyclicCommutantConverse.endK_centralizer_bound` (OQ02OQ01) — reused directly as the ≥ half.
- `commuting_end_is_polynomial` (OQ02OQ03) NOT needed for the ≤ half; the injective-evaluation route
  is more elementary (no polynomial coordinates), only needing the Krylov basis.

### Gotchas (v4.31)
- `Subalgebra.mem_toSubmodule` takes the subalgebra `S` EXPLICITLY: `(Subalgebra.mem_toSubmodule S).mp h`
  (not `(Subalgebra.mem_toSubmodule).mp`, which parses `.mp` on the ∀-expr → "Invalid field mp").
- `Subalgebra.mem_centralizer_iff K` gives `T * A = A * T`; need `.symm` for `A * T = T * A`.
- `Module.finrank K ↥(Subalgebra.toSubmodule S) = Module.finrank K S` by `rfl`.

### Remaining open
- Last edge: centralizer = K[T] (or dim C(T)=n) IMPLIES cyclic vector — the converse completing the triangle.
- Optionally: C(T) = K[T] as an equality of subalgebras in Module.End.

---


Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
