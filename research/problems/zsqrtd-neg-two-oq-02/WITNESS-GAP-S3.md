# Dirichlet-witness gap in the sufficiency reduction (S3, researcher-5, 2026-06-15)

## Context

`proofs/Proofs/ThreeSquares.lean` leaves the **sufficiency** direction of Legendre's
three-square theorem as the axiom `not_excluded_form_is_sum_three_sq` (:1665), with
`dirichlet_key_lemma` (:615) as the supporting Minkowski tool. Open PR #24443
(`ThreeSquaresSufficiency.lean`, unregistered) reduces that axiom to a single
hypothesis it names `DirichletWitnessProperty`:

```lean
∀ {m}, ¬IsExcludedForm m → ¬(4 ∣ m) → 1 < m →
  ∃ d p, 0 < d ∧ p = d*m - 1 ∧ p.Prime ∧ legendreSym p (-d : ℤ) = 1
```

and proposes (its "Next Steps") to discharge `DirichletWitnessProperty` from Mathlib's
Dirichlet-primes-in-AP + quadratic reciprocity, thereby eliminating the sufficiency
axiom.

## Finding: `DirichletWitnessProperty` is FALSE on `n ≡ 3 (mod 8)`

All findings are certified by `verify_dirichlet_witness.py` (build-free, sympy; exits
non-zero on mismatch).

1. **The witness symbol is a residue function.** `legendreSym (d·n−1) (−d)` is
   completely determined by `(n mod 8, d mod 8)` (constant over every prime
   `p = d·n−1` in range). The classes giving `+1` are exactly:

   | n mod 8 | admissible d mod 8 giving `legendreSym = +1` |
   |---------|-----------------------------------------------|
   | 1, 5    | 2, 6                                          |
   | 2, 6    | 1, 2, 5, 6                                    |
   | **3**   | **none**                                      |

   (For odd `n`, odd `d` makes `d·n−1` even, so only even `d` are admissible.)

2. **No witness exists for `n ≡ 3 (mod 8)`.** Exhaustively (every non-excluded `n`
   with `4∤n`, `n < 6000`, scanning `d < 200`): the *only* `n` with no witness are
   **exactly** the 750 values `n ≡ 3 (mod 8)`. Every admissible (even) `d` yields
   `legendreSym (d·n−1) (−d) = −1`. Yet all those `n` are genuinely sums of three
   squares — so the gap is real, not a vacuous-hypothesis artifact.

   **Consequence:** `DirichletWitnessProperty` as stated is unsatisfiable for the
   entire class `n ≡ 3 (mod 8)`. PR #24443's reduction theorem
   `three_sq_of_dirichlet_witness` is logically valid (it is conditional on the
   property), but its hypothesis can **never** be discharged, so it does not in fact
   reduce the axiom. The proposed "discharge `DirichletWitnessProperty`" next step is
   impossible as written.

   This matches `ThreeSquares.lean:600`, whose own docstring already treats
   `n ≡ 3 (mod 8)` *separately* ("Use d = 2, find suitable prime factor") rather than
   via the uniform witness — a distinction PR #24443 collapsed.

## The correct decomposition (certified)

3. **`n ≡ 3 (mod 8)` route.** For every `n ≡ 3 (mod 8)` there is an **odd** `t` with
   `(n − t²)/2` a sum of two squares `a² + b²`, giving

   ```
   n = t² + 2a² + 2b² = t² + (a + b)² + (a − b)².
   ```

   Reason: for odd `t`, `t² ≡ 1 (mod 8)`, so `n − t² ≡ 2 (mod 8)` and
   `(n − t²)/2 ≡ 1 (mod 4)`; choosing `t` so that `(n − t²)/2` is a prime `≡ 1 (mod 4)`
   (Dirichlet) makes it a sum of two squares. Verified for all `n ≡ 3 (mod 8) < 8000`,
   identity exact.

So the witness property should be **split by residue**:

```lean
-- n ≢ 3 (mod 8):  Dirichlet witness (d, p = d·n − 1), −d a QR mod p   (current form, now sound)
-- n ≡ 3 (mod 8):  ∃ odd t, (n − t²)/2 = a² + b²  ⇒  n = t² + (a+b)² + (a−b)²
```

## Recommended action

- **PR #24443**: amend `DirichletWitnessProperty` to require `n % 8 ≠ 3`, and add the
  `n ≡ 3 (mod 8)` two-squares branch to `three_sq_of_dirichlet_witness` (it needs the
  sum-of-two-squares theorem, already in Mathlib as `Nat.Prime.sq_add_sq` /
  `ZMod.sq_add_sq`, not the Dirichlet key lemma). As written, the property is
  unsatisfiable and the reduction stalls.
- Discharging the *amended* (n ≢ 3) witness via Dirichlet-AP + reciprocity is then
  genuinely the remaining open ingredient, and the residue table above gives the exact
  `d mod 8` class to target for each `n mod 8`.

## Status

Build-free (Docker blackout). No `.lean` changed — `ThreeSquares.lean` is a registered
1979-LOC flagship, and the fix belongs in the unregistered `ThreeSquaresSufficiency.lean`
of PR #24443 once a compiler is available. Deliverable is the certified arithmetic
(`verify_dirichlet_witness.py`) + this gap analysis.
