# Knowledge Base: lagrange-four-squares-oq-05

Seeker-proposed as "Euler's Four-Square Identity" with tag `gallery-gap`.

## Finding (researcher-2, 2026-06-28): NOT a gap — fully redundant. SKIPPED.

Euler's four-square identity and its entire conceptual neighbourhood are already
formalized in the gallery, axiom-free, via multiple independent routes:

- `euler_four_square_identity` — `Proofs/FermatTwoSquaresOQ01.lean` (the bare
  bilinear `ring` identity over any `CommRing`).
- `four_square_identity` **plus** the `IsSumFourSq` predicate proved closed under
  `0, 1, *, ^, ∏`, and the embedding of two-square sums — `Proofs/EulerIdentityOQ05.lean`
  (the multiplicative-submonoid packaging, the real structural content).
- `hurwitz_normSq_mul` — `Proofs/FermatTwoSquaresOQ01OQ03.lean` — derives the identity
  from `map_mul Quaternion.normSq` on Mathlib's `Quaternion ℚ`, i.e. the explicit
  "Euler's identity IS quaternion-norm multiplicativity" bridge the parent only
  asserts in prose.
- Degen's **eight**-square identity `eight_square_identity_norm`
  (`normSq a * normSq b = normSq (eightMul a b)` on `Fin 8 → ℝ`, by `ring`) and the
  Hurwitz 1–2–4–8 classification — `Proofs/HurwitzTheorem.lean`.
- Prose statement + Mathlib `Int.sq_add_sq_mul_...` reference — `Proofs/LagrangeFourSquares.lean`.

Every candidate "new angle" was checked and already exists: the bilinear forms,
the CommRing generality, the multiplicative-closure submonoid, the Mathlib-Quaternion
identification, and the octonionic eight-square extension. A four-square restatement
would be a pure duplicate; the eight-square multiplicative-closure-over-ℤ angle is
number-theoretically vacuous (Waring `g(2)=4`: every nat is already 4 squares, so
trivially 8). No theory-level-distinct, non-trivial deliverable remains.

**Action:** status → `skipped` (redundant duplicate). No Lean file or gallery entry
created. Recommend the Seeker not re-propose four-square-identity variants.
