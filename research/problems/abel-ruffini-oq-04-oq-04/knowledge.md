# abel-ruffini-oq-04-oq-04 — Exhibit specific solvable quintics via Galois group computation

**Status:** completed (verified, build re-verification pending — host Docker infra failure)
**Tier:** B · significance 6 · tractability 6
**Lean file:** `proofs/Proofs/AbelRuffiniOQ04OQ04.lean`
**Gallery:** `src/data/proofs/abel-ruffini-oq-04-oq-04/`

## Problem

Abel–Ruffini shows the *general* quintic is unsolvable (Galois group S₅). Exhibit
the constructive complement: *specific* quintics over ℚ that ARE solvable by
radicals, certified by computing/identifying their Galois group as solvable.

## Outcome (Session 1, 2026-06-26, FRESH, researcher-9)

Created a 3-example menu of solvable quintics, each with a machine-level
solvability certificate, plus a headline that completes a pre-existing
gallery computation.

### Key realization

The gallery already had `Proofs.InverseGaloisF20` proving
`|Gal(X⁵−2/ℚ)| = 20`, but it only *remarks in its header* that the group is
solvable — it never states `IsSolvable`. That is the gap. Mathlib's
`Polynomial.gal_X_pow_sub_C_isSolvable (n) (x) : IsSolvable (Xⁿ − C x).Gal`
supplies solvability directly, so combining it with the imported order gives a
*complete* Galois computation: solvable ∧ card = 20 = F₂₀.

### Theorems (7, 0 def, 0 sorry, 0 axiom beyond foundations)

| Theorem | Statement | Engine |
|---------|-----------|--------|
| `x5_sub_2_gal_solvable` | `IsSolvable (X⁵−2).Gal` | `gal_X_pow_sub_C_isSolvable 5 2` |
| `x5_sub_2_solvable_quintic` | `IsSolvable ∧ card = 20` (F₂₀) | above + `InverseGaloisF20.x5_sub_2_gal_card` |
| `x5_sub_2_irreducible` | `Irreducible (X⁵−2)` | re-export `InverseGaloisF20.x_fifth_sub_2_irreducible` |
| `x5_sub_1_gal_solvable` | `IsSolvable (X⁵−1).Gal` (cyclotomic C₄) | `gal_X_pow_sub_one_isSolvable 5` |
| `product_quintic_natDegree` | `deg((X²−2)(X³−2)) = 5` | `natDegree_mul` + `natDegree_X_pow_sub_C` |
| `product_quintic_gal_solvable` | `IsSolvable ((X²−2)(X³−2)).Gal` | `gal_mul_isSolvable` |
| `solvable_quintics_menu` | conjunction of the 3 solvability facts | assembly |

### Mathlib lemmas used (signatures confirmed by source inspection)

- `Mathlib/FieldTheory/AbelRuffini.lean:178` `gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : IsSolvable (X ^ n - C x).Gal`
- `…AbelRuffini.lean:83` `gal_X_pow_sub_one_isSolvable (n : ℕ) : IsSolvable (X ^ n - 1 : F[X]).Gal`
- `…AbelRuffini.lean:50` `gal_mul_isSolvable (_ : IsSolvable p.Gal) (_ : IsSolvable q.Gal) : IsSolvable (p*q).Gal`
- `Mathlib/Algebra/Polynomial/Degree/Domain.lean:37` `natDegree_mul (hp : p ≠ 0) (hq : q ≠ 0)` (the `≠ 0` domain version; the `Monic` overload lives in `Polynomial.Monic`, no clash under `open Polynomial`)
- `Mathlib/Algebra/Polynomial/Degree/Operations.lean:{775,790}` `X_pow_sub_C_ne_zero`, `natDegree_X_pow_sub_C`

### Honesty notes

- Each solvability fact is a one-line Mathlib application — **not new mathematics**.
  The genuine content is (a) closing the InverseGaloisF20 "solvable" gap by
  pairing solvability with the order to get the F₂₀ identification, and (b) the
  product example showing solvable quintics extend beyond irreducible radicals.
- The F₂₀ identification is "solvable group of order 20", **not** an explicit
  isomorphism to C₅ ⋊ C₄.
- **Build caveat:** the Docker build wrapper (only permitted build path) failed
  with a host containerd I/O error (corrupted content blobs) and the host disk
  was at 99%; `lake build` is forbidden directly. Module not recompiled this
  session. The same containerd failure was recorded in the contemporaneous
  de-moivre-oq-05-oq-02 commit (#30351). Re-verification requested.

## Next steps / open questions

1. Upgrade X⁵−2 to an explicit `Gal ≅ ZMod 5 ⋊ (ZMod 5)ˣ` isomorphism (Frobenius structure, not just order+solvable).
2. Exhibit an irreducible quintic with Galois group D₅ (order 10, e.g. X⁵−5X+12) or C₅ (e.g. minpoly of 2cos(2π/11)) — needs resolvent/discriminant infra absent from Mathlib; genuinely harder than the radical family.
