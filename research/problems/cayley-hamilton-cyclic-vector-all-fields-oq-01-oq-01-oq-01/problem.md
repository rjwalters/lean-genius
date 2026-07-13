# Problem: Cyclic Vector Theorem — Biconditional over Commutative Rings (OQ extension 01)

## Statement

### Plain Language

The gallery entry [`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01`](../../../src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01/meta.json)
proves, over an arbitrary field `K`, the biconditional

> `IsNonderogatory M ↔ ∃ v, IsCyclicVector M v`

for `M : Matrix (Fin n) (Fin n) K`. The first listed open question on that
entry asks whether the biconditional extends to matrices over commutative
(Noetherian) rings, not just fields. This slug investigates that
extension.

### Formal Statement

Let `R` be a (nontrivial) commutative ring, `n : ℕ`, and
`M : Matrix (Fin n) (Fin n) R`. Define, mirroring the gallery file
[`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean`](../../../proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean):

```
IsCyclicVector M v  :=  ∀ p : R[X], p.natDegree < n →
                          (aeval M p).mulVec v = 0 → p = 0
IsNonderogatory M   :=  minpoly R M = M.charpoly
```

The OQ asks: does

$$\text{IsNonderogatory}(M) \;\iff\; \exists\, v,\ \text{IsCyclicVector}(M,\, v)$$

hold over every commutative ring `R`? If not, identify the largest class
of rings for which each direction holds, and exhibit explicit
counterexamples in the remaining cases.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - generalization
  - gallery-extracted
  - commutative-rings
  - cyclic-vector
```

**Significance**: 6/10 — clarifies the precise ring-theoretic boundary
of the cyclic vector characterization, which is the cornerstone of
rational canonical form theory.

**Tractability**: 5/10 — the *backward* direction extends cleanly to any
commutative ring with a short proof tweak; the *forward* direction
fails over non-domains (with an explicit `ℤ/4ℤ` counterexample) and is
subtle to settle over general integral domains.

## Why This Matters

1. **Sharper structure theorem.** Rational canonical form (RCF) is
   classical over a field; the cyclic-vector biconditional is the
   bridge between "nonderogatory" (algebraic condition on `minpoly`)
   and "similar to a single companion matrix" (geometric condition on
   the action of `M`). Pinning down which rings support each direction
   tells us exactly where RCF generalises and where it breaks.

2. **Mathlib gap.** Mathlib has `Matrix.isIntegral` and `minpoly` for
   arbitrary `[CommRing R]` (see API map below) but stops at
   `minpoly_dvd_charpoly` requiring `[Field K]` (Charpoly/Minpoly.lean
   line 47). The backward direction's extension to `CommRing R` is a
   small but real gap-fill.

3. **Counterexample is concrete.** Over `ℤ/4ℤ`, the matrix
   `M = [[0,2],[0,0]]` is nonderogatory (both `minpoly` and `charpoly`
   equal `X^2`) yet admits NO cyclic vector — every `v ∈ (ℤ/4ℤ)^2` is
   annihilated by some nonzero polynomial of degree `< 2`. The
   forward direction is genuinely false over non-domains; the OQ is
   not vacuous.

## Status of the Two Directions (S1 OBSERVE summary)

### Backward direction (cyclic ⇒ nonderogatory)

**Conjecture**: extends to any nontrivial commutative ring `R`.

The existing field-proof in
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean` uses four Mathlib
facts:

| Fact | Mathlib location | Typeclass requirement |
|------|------------------|-----------------------|
| `minpoly.dvd` | `FieldTheory/Minpoly/Basic.lean:200`-ish | `[CommRing A] [Ring B] [Algebra A B]` |
| `Matrix.isIntegral` | `LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44` | `[CommRing R]` |
| `Polynomial.Monic.of_mul_monic_left` | `Algebra/Polynomial/Monic.lean:110` | `[Semiring R]` |
| `Polynomial.natDegree_mul` | `Algebra/Polynomial/Basic.lean` (domain) | `[IsDomain R]` for the version used in the field file |

Only the fourth fact requires the base ring to be a domain. **The fix**:
swap the call

```lean
Polynomial.natDegree_mul (minpoly.ne_zero _) hr_monic.ne_zero
```

for

```lean
(minpoly.monic _).natDegree_mul' hr_monic.ne_zero
```

which is `Polynomial.Monic.natDegree_mul'` at
`Mathlib/Algebra/Polynomial/Monic.lean:154` — it requires only one factor
to be monic and the other to be nonzero, **no domain hypothesis**.
This is the entire technical bridge.

### Forward direction (nonderogatory ⇒ ∃ cyclic vector)

**FAILS** over `ℤ/4ℤ` (and presumably any non-domain). Counterexample
worked out in §S1 of `knowledge.md`:

```
R = ZMod 4,    M = !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)
```

Then `M.charpoly = X^2`, `minpoly (ZMod 4) M = X^2`, so
`IsNonderogatory M`. But for every `v = (a, b) ∈ (ZMod 4)^2`, the
polynomial `2X` (or `X` if `b = 0`) satisfies `natDegree < 2` and
annihilates `v` under `aeval M`, witnessing `¬ IsCyclicVector M v`.
The existential ∃ v IsCyclicVector M v is false.

**Open over integral domains.** Whether the forward direction extends
to `R` an integral domain (e.g. `ℤ`) is conjecturally true (the
primary-decomposition argument over a PID or UFD should still work),
but the parent file's proof goes via `CayleyHamiltonCyclicVectorAllFields.nonderogatory_has_cyclic_vector`,
which uses `K[X]` being a PID/UFD with monic-irreducible factorization
(`UniqueFactorizationMonoid`). Mathlib provides
`UniqueFactorizationMonoid` for `K[X]` only when `K` is a field; for
`R[X]` over a UFD `R`, Mathlib has
`Polynomial.uniqueFactorizationMonoid` which depends on `R` being a
UFD. So the forward direction *might* extend to UFDs but the proof
needs reworking.

## Three Approaches

### Approach A — Backward-only extension (recommended for S2)

Write a new file `CayleyHamiltonCyclicVectorCommRingOQ01.lean`
(~50 LOC) that:

1. Generalises `IsCyclicVector` and `IsNonderogatory` to a `CommRing R`
   base.
2. Proves `cyclic_implies_nonderogatory_commring` by the same
   degree-squeeze, with the `natDegree_mul` swap above.
3. States the forward direction as an open theorem with a strategic
   `sorry` and a docstring pointing to the `ℤ/4ℤ` counterexample.

Pro: very short, completes the easy half, lands a definitive negative
result on the hard half.

Con: doesn't actually advance the gallery on the forward direction.

### Approach B — Counterexample formalisation (recommended for S3)

Write `CayleyHamiltonCyclicVectorZMod4Counterexample.lean` (~40 LOC):

1. Define `M : Matrix (Fin 2) (Fin 2) (ZMod 4)` as `!![0, 2; 0, 0]`.
2. Compute `M.charpoly = X^2` (via `Matrix.charpoly_fin_two` or
   directly).
3. Compute `minpoly (ZMod 4) M = X^2` by exhibiting the lower bound
   (`X` doesn't annihilate) and the upper bound (`M^2 = 0`).
4. Prove `¬ ∃ v, IsCyclicVector M v` by case analysis on `v ∈
   (ZMod 4)^2` (finite, 16 cases — `decide` should close it, or 4-row
   `interval_cases` over `Fin 4`).
5. Conclude the forward direction `IsNonderogatory M → ∃ v,
   IsCyclicVector M v` is **false** for this `M`.

Pro: concrete obstruction; settles the OQ negatively over non-domains
with a fully verified counterexample.

Con: doesn't directly extend the gallery theorem; needs a small
companion gallery entry to surface the result.

### Approach C — Domain extension via UFD primary decomposition

Write `CayleyHamiltonCyclicVectorAllUFDsOQ01.lean` (~150-300 LOC):

1. Generalise the parent file
   `CayleyHamiltonCyclicVectorAllFields.lean` from `[Field K]` to
   `[CommRing R] [UniqueFactorizationMonoid R] [IsDomain R]`.
2. The factorisation bridge needs `R[X]` to inherit
   `UniqueFactorizationMonoid` (Mathlib's
   `Polynomial.uniqueFactorizationMonoid` instance).
3. The primary decomposition step is the bulk of the rewrite — depends
   on whether the `ker (aeval M p^k)` lemma extends past fields.

Pro: a substantial extension of the gallery.

Con: significantly more work; the proof depends crucially on the
`Module.End R^n` decomposition into primary components, which is more
delicate over non-fields.

## Recommended S2 → S3 sequence

1. **S2 (Approach A)**: backward-only extension to `CommRing R`. ~50
   LOC, single PR, doc-only counterexample reference.
2. **S3 (Approach B)**: formalise the `ZMod 4` counterexample.
   ~40 LOC, settles forward direction NO over non-domains.
3. **S4 (Approach C)**: optional — attempt UFD extension of the
   forward direction. Higher risk; defer until S2+S3 land.

Net: S2+S3 give a clean "the field biconditional bifurcates over
commutative rings — backward extends, forward fails by ℤ/4ℤ" result.

## Mathlib API Map (pinned to commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| API | Location | Typeclass |
|-----|----------|-----------|
| `minpoly` def | `Mathlib/FieldTheory/Minpoly/Basic.lean:41` | `[CommRing A] [Ring B] [Algebra A B]` |
| `minpoly.monic` | `Mathlib/FieldTheory/Minpoly/Basic.lean:54` | `[CommRing A] [Ring B] [Algebra A B]` + `IsIntegral A x` |
| `minpoly.ne_zero` | `Mathlib/FieldTheory/Minpoly/Basic.lean:60` | `[CommRing A] [Ring B] [Algebra A B] [Nontrivial A]` |
| `minpoly.aeval` | `Mathlib/FieldTheory/Minpoly/Basic.lean:88` | `[CommRing A] [Ring B] [Algebra A B]` |
| `minpoly.dvd` | `Mathlib/FieldTheory/Minpoly/Basic.lean` (Ring section) | `[CommRing A] [Ring B] [Algebra A B]` |
| `Matrix.isIntegral` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44` | `[CommRing R]` |
| `Matrix.aeval_self_charpoly` | (Cayley-Hamilton, exported) | `[CommRing R]` |
| `Polynomial.Monic.of_mul_monic_left` | `Mathlib/Algebra/Polynomial/Monic.lean:110` | `[Semiring R]` |
| `Polynomial.Monic.natDegree_mul'` | `Mathlib/Algebra/Polynomial/Monic.lean:154` | `[Semiring R]`, needs `p.Monic` + `q ≠ 0` |
| `Polynomial.eq_C_of_natDegree_eq_zero` | `Mathlib/Algebra/Polynomial/Degree/Definitions.lean` | `[Semiring R]` |
| `Matrix.charpoly_natDegree_eq_dim` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` | `[CommRing R]` |
| `Matrix.charpoly_monic` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | `[CommRing R]` + `Nontrivial R` |

Every API in the existing field-proof is available over `[CommRing R]`
with appropriate `Nontrivial R` decoration. The only swap needed for
the backward direction is `Polynomial.natDegree_mul` →
`Polynomial.Monic.natDegree_mul'`.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cayley-hamilton-cyclic-vector-all-fields` | Parent (forward direction over fields) |
| `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01` | Direct ancestor (full biconditional over fields); source of this OQ |
| `cayley-hamilton-cyclic-vector-all-fields-oq-01` | Sibling (factorisation bridge via Multiset UFD) |
| `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02` | Sibling (companion-matrix similarity) |
| `cayley-hamilton-minpoly` | Ancestor (general minpoly theory) |

## References

- Hoffman & Kunze, *Linear Algebra* (2nd ed.), Chapter 7 (RCF over a
  field; the biconditional is stated implicitly via the structure
  theorem for finitely-generated modules over a PID).
- Dummit & Foote, *Abstract Algebra* (3rd ed.), §12.1-12.2 (modules
  over a PID, invariant-factor decomposition).
- Jacobson, *Basic Algebra II* (2nd ed.), §3.7 (cyclic-vector
  characterisation over fields; ring-extensions discussed in §3.10).
- Mathlib `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean` — the
  current API boundary for the over-CommRing extension.
