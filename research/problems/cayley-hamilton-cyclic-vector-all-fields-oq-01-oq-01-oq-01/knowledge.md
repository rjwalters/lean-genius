# Knowledge: Cyclic Vector Theorem — Biconditional over Commutative Rings (OQ extension 01)

## S1 OBSERVE session (researcher-9, 2026-05-14)

This note records the counterexample analysis and Mathlib API
verification underpinning the S1 conclusion that the biconditional

> `IsNonderogatory M ↔ ∃ v, IsCyclicVector M v`

(true over fields per gallery entry
`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01`) **bifurcates**
over commutative rings:

- Backward direction extends to any nontrivial `CommRing R`.
- Forward direction fails over `ZMod 4` (and presumably over any
  non-domain), with explicit counterexample.

## Worked counterexample: `M = !![0, 2; 0, 0]` over `ZMod 4`

### Setup

Let `R = ZMod 4` and `n = 2`. Define
```
M : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![0, 2; 0, 0]
```

so `M[0,0] = 0`, `M[0,1] = 2`, `M[1,0] = 0`, `M[1,1] = 0`.

### Characteristic polynomial

`M.charpoly = det (X • 1 - M)` where the underlying matrix is

```
X • 1 - M = !![X, -2; 0, X]
```

(upper triangular with diagonal `(X, X)` and off-diagonal `(-2, 0)`).
The determinant of a 2×2 upper-triangular matrix is the product of
diagonal entries:

```
M.charpoly = X * X - (-2) * 0 = X^2
```

Hence `M.charpoly = X^2`, monic of `natDegree = 2`.

### Minimal polynomial

We claim `minpoly (ZMod 4) M = X^2`.

**Upper bound** (degree ≤ 2): `M^2 = 0`.

Computing `M^2`:
```
M^2 = !![0, 2; 0, 0] * !![0, 2; 0, 0]
    = !![ 0·0+2·0,  0·2+2·0 ;
          0·0+0·0,  0·2+0·0 ]
    = !![ 0, 0 ;
          0, 0 ]
```

So `aeval M (X^2) = M^2 = 0`. Since `X^2` is monic of `natDegree = 2`,
the minimal monic annihilator has `natDegree ≤ 2`.

**Lower bound** (degree ≥ 2): no monic polynomial of `natDegree < 2`
annihilates `M`. The only candidates are:

- `natDegree = 0`: `1`. `aeval M 1 = I ≠ 0`.
- `natDegree = 1`: `X - c` for some `c : ZMod 4`. Then
  `aeval M (X - c) = M - c • I = !![-c, 2; 0, -c]`.
  For this to be the zero matrix, both diagonal entries `-c = 0`
  (forcing `c = 0`) and the `[0,1]`-entry `2 = 0` must hold. The latter
  fails in `ZMod 4` since `2 ≠ 0` (`2 ≠ 0 ∈ ZMod 4`). So no `c` works.

By definition of `minpoly` over a `CommRing` (Mathlib's
`Mathlib/FieldTheory/Minpoly/Basic.lean:41`), `minpoly (ZMod 4) M` is
the monic generator of the ideal `{ p : (ZMod 4)[X] | aeval M p = 0 }`
of least degree. Combining the upper bound (`X^2` annihilates) and the
lower bound (no monic deg-1 annihilator exists), we conclude
`minpoly (ZMod 4) M = X^2`.

### `IsNonderogatory M` holds

`minpoly (ZMod 4) M = X^2 = M.charpoly`, so by definition
`IsNonderogatory M`.

### No cyclic vector

We claim `∀ v : Fin 2 → ZMod 4, ¬ IsCyclicVector M v`.

Recall the definition (mirroring
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean:43`):

```
IsCyclicVector M v := ∀ p : (ZMod 4)[X], p.natDegree < 2 →
                       (aeval M p).mulVec v = 0 → p = 0
```

So to show `¬ IsCyclicVector M v` we exhibit a nonzero `p` of
`natDegree < 2` with `(aeval M p).mulVec v = 0`.

Let `v = (a, b) : Fin 2 → ZMod 4`. We compute `M.mulVec v`:

```
M.mulVec v = (M[0,0]·a + M[0,1]·b, M[1,0]·a + M[1,1]·b)
           = (0·a + 2·b, 0·a + 0·b)
           = (2b, 0)
```

And for `p = αX + β : (ZMod 4)[X]`:

```
aeval M p = α·M + β·I = !![β, 2α; 0, β]

(aeval M p).mulVec v = !![β, 2α; 0, β] * (a, b)^T
                     = (β·a + 2α·b, 0·a + β·b)
                     = (βa + 2αb, βb)
```

For `(aeval M p).mulVec v = 0` we need:

1. `βa + 2αb = 0` in `ZMod 4`
2. `βb = 0` in `ZMod 4`

**Case 1: `b = 0`.** Condition 2 is automatic. Condition 1 reduces to
`βa = 0`. Take `p = X` (i.e., `α = 1, β = 0`). Then `βa = 0 ✓` and
`p ≠ 0` with `natDegree p = 1 < 2`. So `v = (a, 0)` is not cyclic.

**Case 2: `b ≠ 0`.** Take `p = 2X` (i.e., `α = 2, β = 0`). Then:

- `βa + 2αb = 0 + 4b = 0` in `ZMod 4` (since `4 ≡ 0 mod 4`).
- `βb = 0 ✓`.
- `p = 2X ≠ 0` (in `(ZMod 4)[X]`, `2X = 0` iff its `1`-coefficient
  `2 = 0`, which fails since `2 ≠ 0` in `ZMod 4`).
- `natDegree (2X) = 1 < 2`.

So `v = (a, b)` with `b ≠ 0` is not cyclic.

**Combined**: for every `v ∈ (ZMod 4)^2`, there exists nonzero
`p : (ZMod 4)[X]` of `natDegree < 2` with `(aeval M p).mulVec v = 0`.
Hence `¬ ∃ v, IsCyclicVector M v`.

### Conclusion

`M = !![0, 2; 0, 0]` over `ZMod 4` satisfies:

- `IsNonderogatory M` (`minpoly = charpoly = X^2`)
- `¬ ∃ v, IsCyclicVector M v`

This **falsifies** the forward direction
`IsNonderogatory M → ∃ v, IsCyclicVector M v` over `ZMod 4`. The
biconditional therefore **does not extend** to general commutative
rings.

The S3 ACT will formalise this as a counterexample theorem in Lean.

## Backward direction: proof sketch over `CommRing R`

The existing field proof in
`proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean:45-95`
generalises to `[CommRing R] [Nontrivial R]` with only one surgical
swap:

| Step | Field-version line | CommRing-version change |
|------|--------------------|-------------------------|
| `minpoly ∣ charpoly via Cayley-Hamilton` | line 52-53 | unchanged — `minpoly.dvd` works over `CommRing` |
| `M.charpoly.Monic` | line 55 | unchanged — needs `Nontrivial R` (auto from `Nontrivial`) |
| `M.charpoly.natDegree = n` | line 57-58 | unchanged — `Matrix.charpoly_natDegree_eq_dim` works over `CommRing R + Nontrivial R` |
| `(minpoly).natDegree ≤ n` from divisibility | line 60-62 | unchanged — `Polynomial.natDegree_le_of_dvd` needs only the divisor monic |
| `(aeval M minpoly).mulVec v = 0` | line 64-67 | unchanged |
| `(minpoly).natDegree ≥ n` from cyclic | line 68-72 | unchanged — `minpoly.ne_zero` needs `Nontrivial R` |
| Extract quotient `r`: `charpoly = minpoly * r` | line 77 | unchanged |
| `r.Monic` from `Monic.of_mul_monic_left` | line 79-80 | unchanged — `Monic.of_mul_monic_left` works over `Semiring R` |
| **Sum of `natDegree`s** | line 83-84 | **SWAP**: `Polynomial.natDegree_mul` (which requires `IsDomain R`) → `(minpoly.monic _).natDegree_mul' hr_monic.ne_zero` (uses `Polynomial.Monic.natDegree_mul'` at `Mathlib/Algebra/Polynomial/Monic.lean:154`, only needs one factor monic and the other nonzero — works over any `Semiring R`) |
| Closing: `r.natDegree = 0`, `r.coeff 0 = 1`, `r = 1` | line 88-95 | unchanged — `eq_C_of_natDegree_eq_zero` and `Monic.leadingCoeff` work over `Semiring R` |

So the entire backward direction transfers to `CommRing R + Nontrivial R`
with a single 1-line lemma-name swap. This is the meat of the S2 ACT.

## Mathlib API verification log

All API names verified at pinned commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/...` lookups.

| Mathlib name | Location | Typeclass | Verified |
|--------------|----------|-----------|----------|
| `minpoly` (def) | `FieldTheory/Minpoly/Basic.lean:41` | `[CommRing A] [Ring B] [Algebra A B]` | ✓ |
| `minpoly.monic` | `FieldTheory/Minpoly/Basic.lean:54` | `[CommRing A] [Ring B] [Algebra A B]` + `IsIntegral A x` | ✓ |
| `minpoly.ne_zero` | `FieldTheory/Minpoly/Basic.lean:60` | adds `[Nontrivial A]` | ✓ |
| `minpoly.aeval` | `FieldTheory/Minpoly/Basic.lean:88` | `[CommRing A] [Ring B] [Algebra A B]` | ✓ |
| `Matrix.isIntegral` | `LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44` | `[CommRing R]` | ✓ |
| `Polynomial.Monic.of_mul_monic_left` | `Algebra/Polynomial/Monic.lean:110` | `[Semiring R]` | ✓ |
| `Polynomial.Monic.natDegree_mul'` | `Algebra/Polynomial/Monic.lean:154` | `[Semiring R]` + `p.Monic` + `q ≠ 0` | ✓ |
| `Polynomial.Monic.natDegree_mul` | `Algebra/Polynomial/Monic.lean:141` | `[Semiring R]` + both `Monic` | ✓ (alternative; needs both monic) |

Sample verification command:
```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Monic.lean" \
  -X GET -f ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.content' \
  | base64 --decode \
  | sed -n '141,156p'
```

confirms the lemma signature at the pinned revision.

## Risk analysis for S2 (Approach A — backward extension)

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `GeneralCyclicVector` namespace from parent file has hidden `[Field K]` typeclass that doesn't generalise | Low | S2 SCAFFOLD does a `grep` of `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` for the `GeneralCyclicVector.IsCyclicVector` definition; if `Field K` is hard-coded, S2 defines a fresh `GeneralCyclicVectorCommRing` namespace in the new file. |
| `Polynomial.Monic.natDegree_mul'` lemma name has drifted at v4.26.0 | Very low | Verified above at the pinned commit. |
| `Monic.eq_one_iff_natDegree_le_zero` doesn't exist (used in proof skeleton's last line) | Medium | Use `eq_C_of_natDegree_eq_zero` + `Monic.leadingCoeff` chain (the pattern used in the field file's lines 88-93) — verified to work over `Semiring`. |
| Build-pending: parent file `CayleyHamiltonCyclicVectorAllFields.lean` has Mathlib v4.26.0 drift | Low | The OQ01OQ01 build was clean as of 2026-05-12 per `meta.json` `mathlib_version: 4.26.0`. Same Mathlib API surface used. |
| `Matrix.charpoly_monic` requires `Nontrivial R`, breaks for `R = Subsingleton`-classified | None | Adding `[Nontrivial R]` to the theorem statement is harmless. |

## Risk analysis for S3 (Approach B — `ZMod 4` counterexample)

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `decide` can't close `(aeval M (2*X)).mulVec v = 0` over `ZMod 4` (finiteness needed) | Medium | `(ZMod 4)^2` has only 16 elements; if `decide` times out, fall back to explicit `interval_cases` on `Fin 4` for each of `a, b`. |
| `Polynomial.natDegree (2 * X)` in `(ZMod 4)[X]` may simplify unexpectedly (e.g., if `Mathlib` proves `natDegree (2*X : (ZMod 4)[X]) = ?` differently than expected) | Low | Use `Polynomial.natDegree_C_mul_X` (if `c ≠ 0`) or compute via explicit `Polynomial.natDegree (C 2 * X)`. In `ZMod 4`, `2 ≠ 0` so this works. |
| `M^2 = 0` calculation needs careful `Matrix.mul_apply` unfolding | Low | 2×2 matrix multiplication is closed-form; `decide` or `ext; simp [Matrix.mul_apply, Fin.sum_univ_succ]` should close. |

## Possible follow-ups beyond S4

- **Status of forward direction over an integral domain `R`**: the
  primary-decomposition proof in
  `CayleyHamiltonCyclicVectorAllFields.lean` relies on the
  factorisation `μ_M = ∏ p_i^{e_i}` of the minimal polynomial into
  distinct monic irreducible primes. Over a UFD this still holds for
  monic polynomials in `R[X]` (Gauss's lemma), but the linkage between
  the primary decomposition of `R[X]/(μ_M)` and the structure of
  `Module R^n` over `R[X]` needs `R[X]` to be a 1-dimensional domain
  (PID) for the full module-theoretic decomposition. The question of
  whether the forward direction extends to UFDs that are not PIDs
  (e.g., `ℤ`) is mathematically subtle and may have a positive answer
  for matrices whose `charpoly` has unit content.

- **Connection to invariant-factor theorem**: a cleaner formulation
  may be: over a PID `R`, the forward direction holds iff `charpoly M`
  has unit content (so that `R^n` is a cyclic `R[X]`-module). This
  would link this OQ to the invariant-factor decomposition of
  `Module R[X] R^n` and the Smith normal form. Worth surveying in a
  later iteration.

## Open questions (for future sessions)

1. Does the forward direction extend to `R` an integral domain?
   (Likely yes for PIDs; subtle for UFDs.)

2. Is there a clean "module-theoretic" reformulation of the
   biconditional that subsumes all the directions uniformly? E.g., is
   the biconditional equivalent to "Module R^n via M-action is a
   cyclic `R[X]`-module"?

3. Over `R = ZMod p^k` for `k ≥ 2` (a non-field but non-domain
   commutative ring), does the structure theorem for finite abelian
   groups give a clean characterization of which `M` admit cyclic
   vectors?
