import Mathlib
import Proofs.InverseGaloisA5

/-!
# Dedekind-Frobenius Bridge toward `three_dvd_gal_card` (Inverse-Galois A₅, OQ-01)

This companion file scaffolds the eliminator for the parent file's last
axiom

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

The route (R1 in `research/problems/inverse-galois-a5-oq-01/problem.md`)
is the specialised Dedekind theorem at the unramified prime `p = 7`:

* `7 ∤ disc(q) = 32000²` (decidable arithmetic, here);
* Hence some prime `𝔭 ⊂ 𝒪_{q.SplittingField}` above `7` is unramified;
* The parent's Part XII verifies that `q mod 7 = (X-5)(X-6)·(X³+6X²+4X+1)`
  with the cubic factor irreducible over `𝔽₇`;
* By Dedekind's theorem, the Frobenius element at `𝔭` acts on the five
  roots with cycle type `(1, 1, 3)`, so it has order 3 in `q.Gal`;
* `orderOf σ = 3 ⇒ 3 ∣ Fintype.card q.Gal` via `orderOf_dvd_card`.

## Current status (S3 ORIENT refinement)

Only one substantive sorry remains in this file:

* `exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3` — the Frobenius
  construction. S4 will discharge this using the pinned `v4.26.0` API:
  - `AlgHom.IsArithFrobAt` and `IsArithFrobAt.exists_of_isInvariant`
    (`Mathlib/RingTheory/Frobenius.lean`)
  - `arithFrobAt R G Q : G` (explicit Frobenius choice, same file)
  - `Ideal.Quotient.stabilizerHom_surjective` and
    `Algebra.isInvariant_of_isGalois`
    (`Mathlib/RingTheory/Invariant/Basic.lean`)
  - `Ideal.inertiaDegIn`, `card_inertia_eq_ramificationIdxIn`
    (`Mathlib/NumberTheory/RamificationInertia/Galois.lean`)

See `research/problems/inverse-galois-a5-oq-01/knowledge.md` § "S3 —
ORIENT refinement" for the full API audit and the residual Mathlib
gap (the bridge `orderOf (arithFrobAt R G Q) ≥ inertiaDegIn (Q.under R) S`
at unramified primes — the genuine new content for S4 ACT, ~100-150
Lean lines out of a total ~230-360 estimated for S4).

The trivial precondition (`seven_nondiv_disc`) and the trivial bridge
(`three_dvd_gal_card_proved`) are proved with `omega` / `orderOf_dvd_card`.
-/

namespace InverseGaloisA5Dedekind

open Polynomial InverseGaloisA5

/-- The polynomial discriminant of `q` is `32000² = 1_024_000_000`
(see `InverseGaloisA5.disc_value_is_square` and
`InverseGaloisA5.trinomial_disc_computation`). The prime `7` does not
divide this value, so `7` is unramified in `q.SplittingField`.

This is a routine decidable arithmetic check, expressed at the numeric
level so that the statement does not depend on a particular Mathlib
spelling of `Polynomial.discr`. -/
theorem seven_nondiv_disc : ¬ (7 : ℤ) ∣ 1024000000 := by
  -- 1024000000 = 7 · 146285714 + 2, so 7 ∤ 1024000000.
  intro ⟨k, hk⟩
  omega

/-- **S2 sorry** (to be discharged in S3): there is a Galois automorphism
of `q.SplittingField` whose order is exactly 3.

The intended construction is the Frobenius element at any prime
`𝔭 ⊂ 𝒪_{q.SplittingField}` above the unramified prime `p = 7` whose
inertia degree is 3 (corresponding to the irreducible cubic factor
`X³ + 6X² + 4X + 1` of `q mod 7`, see `cubic_factor_no_roots_mod7` in
the parent file). At an unramified prime the decomposition group is
cyclic of order equal to the inertia degree, so the Frobenius generator
has order 3 in `q.Gal`. -/
theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 := by
  sorry

/-- **Bridge theorem**: an order-3 element of `q.Gal` yields `3 ∣ |q.Gal|`
via `orderOf_dvd_card`. This is the eliminator for
`InverseGaloisA5.three_dvd_gal_card`; in S4 the parent's `axiom` will
be rewritten as `theorem three_dvd_gal_card := three_dvd_gal_card_proved`. -/
theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
  obtain ⟨σ, hσ⟩ := exists_gal_order_three
  rw [← hσ]
  exact orderOf_dvd_card

end InverseGaloisA5Dedekind
