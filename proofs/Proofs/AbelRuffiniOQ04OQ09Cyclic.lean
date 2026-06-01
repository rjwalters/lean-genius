/-
Proof: Cyclic-row Shafarevich realizability for `n ≤ 4`.
Date: 2026-06-01 (S9 ACT, researcher-1)
Research: abel-ruffini-oq-04-oq-09, S9 ACT — cyclic-row paste body per
          S6 PREP §3.2 (researcher-11) corrected namespace cite.

This is the **cyclic row** of the `n ≤ 4` Shafarevich slice. It is a
one-line specialisation of `ShafarevichFeasibility.cyclic_realizable`
(proved over arbitrary `n ≥ 1` via Dirichlet's theorem on primes in
arithmetic progressions in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`).

The `_hn4 : n ≤ 4` parameter documents the slice specialisation for
the gallery entry; it is unused by the body. We keep it so downstream
consumers can refer to "the cyclic row of the n≤4 menu" without
having to know about the parent's general-`n` result.

No axioms introduced beyond what `ShafarevichFeasibility.cyclic_realizable`
already loads (`Classical.choice` only, inherited via `IsCyclic`).
The S3 PREP axiom chain trace is:
  `cyclic_realizable` →
  `cyclic_group_realizable` →
  `exists_prime_dvd_pred` →
  `Nat.forall_exists_prime_gt_and_modEq`
  (in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, proved).
-/

import Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01

namespace AbelRuffiniOQ04OQ09

/-- For every `n` with `0 < n ≤ 4`, the cyclic group of order `n` is
realizable as `Gal(L/ℚ)` for some Galois extension `L/ℚ`. This is the
cyclic row of the `n ≤ 4` Shafarevich slice; it is a one-line
specialisation of `ShafarevichFeasibility.cyclic_realizable` (which
works for arbitrary `n ≥ 1`).

The `_hn4` parameter documents the slice specialisation for the
gallery entry; it is unused by the body. -/
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (_hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ShafarevichFeasibility.cyclic_realizable n hn

end AbelRuffiniOQ04OQ09
