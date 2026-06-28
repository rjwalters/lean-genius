# Knowledge Base: inverse-galois-oq-06-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The A₅ realizability entry rests on a single axiom `three_dvd_gal_card`. The
mod-7 Dedekind route to eliminate it has two halves:

1. **Algebraic input** (THIS slug): `q mod 7` = distinct irreducibles of degree
   `(1,1,3)`, squarefree (7 unramified).
2. **Dedekind implication** (sibling `inverse-galois-a5-oq-01`): factor type ⟹
   Frobenius cycle type ⟹ `3 ∣ |Gal|`. Mathlib gap.

Sibling `inverse-galois-oq-06-oq-01` had established only the *shape* of the
factorization and that the cubic has no roots — not irreducibility/squarefree.

---

## Insights

- A degree-3 polynomial over a field with no root is irreducible:
  `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
  `(hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x)`.
  First goal closes by `rw [natDegree_eq]; decide`; second is exactly the
  no-roots fact reused from the sibling.
- Coprimality of distinct linear factors: `isCoprime_X_sub_C_of_isUnit_sub`
  needs `IsUnit (a - b)`; over a field use `isUnit_iff_ne_zero.mpr (by decide)`.
- Coprimality of linear vs cubic: `Irreducible.isRelPrime_iff_not_dvd` +
  `Polynomial.dvd_iff_isRoot` reduces `¬ (X - C a) ∣ cubic` to `eval a cubic ≠ 0`.
- Squarefree of a product of pairwise-coprime squarefrees:
  `squarefree_mul_iff : Squarefree (x*y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y`
  (note: `IsRelPrime`, not `IsCoprime`; convert with `IsCoprime.isRelPrime`).
  `IsCoprime.mul_left` builds `IsCoprime (a*b) c` from the two coprimalities.
- Non-association of equal-degree monic factors: `eq_of_monic_of_associated`
  forces equality, then evaluate at 0 (`congrArg (eval 0)`) and `decide`.
  Different degrees: `natDegree_le_of_dvd` both ways + `omega`.

---

## Packaging completeness (iter 3)

- A "factor type" theorem that lists irreducibles + degrees + distinctness +
  squarefreeness is **incomplete** unless it ALSO carries the factorization
  identity `q.map(ℤ→𝔽ₚ) = f₁·f₂·f₃`. Without it the statement is about an
  arbitrary product, not about `q mod p`. The mod-11 packaging already had this
  conjunct; the mod-7 one did not — fixed by re-exporting
  `q_ℤ_mod7_factorization` through the local factor defs.
- Restating an identity proved with `(X - C 5)` in terms of a `noncomputable def
  linFactor5 := X - C 5`: use `show <goal with X - C 5>; exact <lemma>`. The
  `show` succeeds by defeq (regular defs unfold during `isDefEq`); no `rw`/`simp`
  unfolding of the def is needed.

---

## Dead Ends

- `isCoprime_of_irreducible_of_not_associated` does NOT exist in Mathlib 4.26.
  Use the `Irreducible.isRelPrime_iff_not_dvd` / `dvd_iff_isRoot` route instead.
- `squarefree_mul_iff` is phrased with `IsRelPrime`, not `IsCoprime` — calling
  `IsCoprime.squarefree_mul_iff` fails; convert first.
