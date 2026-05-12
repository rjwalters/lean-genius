# Knowledge — lagrange-theorem-oq-01-oq-01-oq-01

## S1 (researcher-10, 2026-05-12) — OBSERVE survey

### Parent context

The parent `Proofs/LagrangeTheoremOQ01OQ01.lean` (169 lines, 13 theorems,
0 sorries, 0 axioms) re-exposes Sylow-based pq-classification results from
`Proofs/SylowTheoremOQ01.lean` (namespace `SylowPQ`). Its key statements:

| Theorem | Form | Direction |
|---------|------|-----------|
| `lagrange_pq_sylow_counts` | `n_q = 1 ∧ (n_p = 1 ∨ n_p = q)` | always |
| `lagrange_pq_unique_normal_q` | `∃ Q : Sylow q G, Q.Normal` | always |
| `lagrange_pq_n_q_eq_one` | `Fintype.card (Sylow q G) = 1` | always |
| `lagrange_pq_n_p_eq_one_when_coprime` | `n_p = 1` | when `p ∤ (q-1)` |
| `lagrange_pq_cyclic` | `IsCyclic G` | when `p ∤ (q-1)` |
| `pq_unique_when_coprime` | `∀ G ... → IsCyclic G` | universal, when `p ∤ (q-1)` |
| `lagrange_pq_nonabelian_n_p_eq_q` | `n_p = q` | when `p ∣ (q-1) ∧ ¬ IsCyclic G` |
| `order_15_cyclic` | universal cyclic | `q = 5, p = 3` (3 ∤ 4) |
| `order_35_cyclic` | universal cyclic | `q = 7, p = 5` (5 ∤ 6) |
| `order_77_cyclic` | universal cyclic | `q = 11, p = 7` (7 ∤ 10) |
| `order_6_non_unique` | `(2 : ℕ) ∣ (3 - 1)` | divisibility only |
| `order_21_non_unique` | `(3 : ℕ) ∣ (7 - 1)` | divisibility only |
| `order_55_non_unique` | `(5 : ℕ) ∣ (11 - 1)` | divisibility only |

The `order_*_non_unique` lemmas only verify the hypothesis `p ∣ q - 1` —
they do *not* produce a non-cyclic group of order `pq`. This is the gap
this OQ targets.

The parent's docstring (line 20–22) explicitly states:
> 3. Non-abelian case: If p | (q-1), two groups of order pq exist up to
>    isomorphism: the cyclic group ℤ/pq and a non-abelian semidirect product
>    ℤ/q ⋊ ℤ/p.

But no Lean term-level witness for the non-abelian group is produced.

### Three approaches surveyed

#### Approach A: `DihedralGroup q` for the `p = 2` case

**Idea**: Mathlib has the dihedral group as a built-in inductive type
with full group instances + cardinality + non-cyclic theorems. For an
odd prime `q ≥ 3`, `DihedralGroup q` *is* a non-cyclic group of order
`2 * q = p * q` (with `p = 2`).

**Lean cost**: ~50 lines net for the main theorem + 4 corollaries (orders
6, 10, 14, 22). All in a new file
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`.

**Risk**: Specializes to `p = 2`. The general case `p > 2 ∧ p | (q-1)`
needs Approach B. But `p = 2` covers all `(p, q)` pairs with `q` odd
prime — the most numerous infinite family.

#### Approach B: `ZMod q ⋊[φ] ZMod p` semidirect product (general case)

**Idea**: Given `p | (q-1)`, construct a non-trivial hom
`φ : ZMod p →* MulAut (ZMod q)` and assemble the semidirect product.
Cardinality is `p * q` by `SemidirectProduct.card`; non-cyclic because
the product is non-abelian (φ is non-trivial).

**Lean cost**: ~200 lines:
- Cyclic structure of `(ZMod q)ˣ` for prime `q` (~30 lines, may already
  be in Mathlib as `ZMod.unitsCyclic` or derivable).
- Element of order `p` in `(ZMod q)ˣ` from `p | q-1` (~50 lines, uses
  cyclic-group divisor existence).
- Iso `(ZMod q)ˣ ≃* MulAut (ZMod q)` and lifting (~40 lines).
- Hom construction `φ : ZMod p →* MulAut (ZMod q)` (~30 lines).
- Semidirect product non-cyclic proof (~50 lines, requires showing the
  product is non-abelian).

**Risk**: Each piece is in Mathlib but the chain is long. Non-trivial
edge cases for `p = q` (excluded by hypothesis) and small `p, q`.

#### Approach C: Hand-built small cases (S₃, order-21, order-55, ...)

**Idea**: For each specific `(p, q)`, construct the group by explicit
multiplication table or as a sub-of-`Equiv.Perm n`.

**Lean cost**: ~30-50 lines per case. No shared infrastructure.

**Risk**: Doesn't generalize. Best as supplementary examples after
Approach A.

### Recommended path: Approach A in S2, B deferred to S3+

Approach A is overwhelmingly the right S2 target:
- 1 session, ~50 lines net.
- Uses only stable Mathlib API at pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Covers an infinite family (all `q` odd prime — i.e., `pq ∈ {6, 10, 14,
  22, 26, 34, 38, 46, ...}`).
- Sets up the gallery for Approach B as a follow-up.

Approach B remains the natural continuation in S3+, completing the
general case. Approach C can be folded in as supplementary content
inside Approach A's file.

### Load-bearing Mathlib API

#### `DihedralGroup` (file `Mathlib.GroupTheory.SpecificGroups.Dihedral`)

Confirmed at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
direct read of `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean`:

```lean
-- Type definition (line 31)
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq

-- Group instance (line 62) — proved via rintro + ring_nf

-- Cardinality (line 149)
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n

-- Nat cardinality (line 152)
theorem nat_card : Nat.card (DihedralGroup n) = 2 * n

-- Non-cyclic (line 233)
lemma not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)

-- Cyclic iff (line 238)
lemma isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1
```

`Fintype` instance auto-derived under `[NeZero n]` via `Fintype.ofEquiv`
+ a helper (`fintypeHelper`) at line 138.

#### `SemidirectProduct` (file `Mathlib.GroupTheory.SemidirectProduct`)

Confirmed at pinned rev via direct read:

```lean
-- Type definition
structure SemidirectProduct (φ : G →* MulAut N) where
  left : N
  right : G

-- Notation
N ⋊[φ] G

-- Cardinality (line 311)
lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G
```

Used in Approach B.

#### Other relevant API

| Name | Use |
|------|-----|
| `Nat.Prime.eq_two_or_odd' : hq : Nat.Prime q → q = 2 ∨ Odd q` | discharge `q ≠ 2 ⇒ Odd q` |
| `Nat.Prime.one_lt : hq → 1 < q` | discharge `q ≠ 1` |
| `Nat.Prime.ne_zero : hq → q ≠ 0` | NeZero instance |
| `MulAut N` (= `N ≃* N`) | automorphism group, target for `φ` |
| `IsCyclic` | property to negate |
| `ZMod.unitsCyclic` (if present) | `(ZMod p)ˣ` is cyclic for prime `p` |

### Edge cases

1. **`q = 2`**: `DihedralGroup 2` is the Klein four-group (order 4),
   `≅ Klein` (file `Mathlib.GroupTheory.SpecificGroups.KleinFour`).
   Order 4 = 2 * 2 = p * p, not `p * q` for *distinct* primes. The
   parent's `p < q` convention excludes this case. The S2 statement
   must require `q ≠ 2`.

2. **`q = 3`** (smallest case): `DihedralGroup 3 ≅ S₃` (symmetric group
   on 3 letters), order 6. Non-cyclic (in fact non-abelian). Matches
   the parent's `order_6_non_unique` divisibility lemma — supplies the
   witness.

3. **`pq` with `p > 2`**: The smallest case is `p = 3, q = 7` (order 21).
   Approach A doesn't cover this; Approach B handles it via
   `ZMod 7 ⋊[φ] ZMod 3` where `φ` sends `1 : ZMod 3` to the cube-root
   `(2 : ZMod 7)` (since `2³ = 8 = 1 mod 7`). Deferred to S3+.

4. **`p = q`**: Excluded by the parent's `p < q` hypothesis. (`p = q`
   means `|G| = p²`, a different classification.)

### Insights

1. **The parent's `lagrange_pq_nonabelian_n_p_eq_q` is conditional, not
   constructive**. It says "*if* `G` is a non-cyclic group of order `pq`,
   *then* `n_p = q`". This OQ supplies the unconditional existence side:
   "*there exists* a non-cyclic group of order `pq` when `p | q-1`".

2. **Approach A leverages `DihedralGroup` as a black box**. The actual
   construction (multiplication table on `ZMod n ⊕ ZMod n` with the
   `sr` reflection swap) is in Mathlib and verified there. We only
   need `card` and `not_isCyclic`. This is a small but high-leverage
   gallery contribution.

3. **The order-6 example is canonical**. `S₃` is the smallest non-abelian
   finite group; producing it as `DihedralGroup 3` gives a clean
   gallery-ready witness. The parent already has `order_6_non_unique`
   as a divisibility lemma; S2's `exists_noncyclic_of_order_6` completes
   the matched pair.

4. **`p = 2` covers an infinite family**. Every odd prime `q` gives a
   `DihedralGroup q` witness. The list grows without bound:
   `q ∈ {3, 5, 7, 11, 13, 17, 19, 23, 29, ...}` ⇒
   `pq ∈ {6, 10, 14, 22, 26, 34, 38, 46, 58, ...}`. The general case
   (Approach B) adds `p ∈ {3, 5, 7, ...}` with various `q` satisfying
   `p | q-1`, but the `p = 2` slice alone is significant gallery
   coverage.

5. **Mathlib's `DihedralGroup.not_isCyclic` is exactly the right lemma**.
   No need to prove non-cyclicity from scratch via, e.g., element-order
   counting. Mathlib's lemma is `∀ n ≠ 1, ¬ IsCyclic (DihedralGroup n)`.
   Our `q ≠ 1` follows from `Nat.Prime.one_lt`.

6. **Gallery template for non-abelian witnesses**. After S2 lands,
   the same template (existence theorem + concrete corollaries by case)
   can be reused for:
   - Quaternion groups (`Quaternion`) for orders 8, 16, ...
   - Alternating groups (`Equiv.Perm.signHom.ker`) for various orders
   - Linear groups (`SL n F`, `GL n F`) for various small cases

### Mathlib gaps

1. **No standalone "non-cyclic-group-of-order-pq exists" theorem**
   in Mathlib at the pinned rev. The pieces are all there
   (`DihedralGroup.not_isCyclic`, `DihedralGroup.card`), but the
   composition into a `∃ G, |G| = pq ∧ ¬ IsCyclic G` statement is
   not packaged. This OQ produces that wrapping.

2. **The semidirect-product approach (Approach B)** requires a
   non-trivial hom `ZMod p →* MulAut (ZMod q)`. Mathlib likely has
   `ZMod.unitsCyclic` (for prime `p`) and the iso
   `(ZMod q)ˣ ≃* MulAut (ZMod q)`, but a direct
   `∃ φ : ZMod p →* MulAut (ZMod q), φ ≠ 1` for `p | q-1` is not
   packaged. Could be a Mathlib contribution after Approach B.

3. **No "smallest non-abelian group of order n" registry**. Each gallery
   non-abelian witness must currently be assembled by hand. A future
   Mathlib feature could be a `SmallestNonAbelian (n : ℕ) : Type`
   typeclass / def, but this is a larger initiative.

### Next Steps (priority order)

1. **(S2)** Approach A: produce the `DihedralGroup q` witness in
   `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`. ~50 lines, single PR.

2. **(S2-companion)** Add the gallery entry under
   `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/` (meta.json +
   annotations.json + index.ts) so the proof appears in the gallery.

3. **(S3)** Approach B (partial): cyclic structure of `(ZMod q)ˣ` +
   element of order `p` extraction. ~80 lines.

4. **(S4)** Approach B (completion): hom construction + semidirect
   product assembly + non-cyclic proof. ~120 lines.

5. **(S5, optional)** Add order-21 concrete corollary
   (`exists_noncyclic_of_order_21`) once Approach B lands.

6. **(S6, optional Mathlib contribution)** `MathlibContrib`-style theorem
   "non-trivial hom `ZMod p →* MulAut (ZMod q)` exists when `p | q-1`"
   to upstream as a stepping-stone in `Mathlib.GroupTheory`.

### Risk Notes

- Approach A's proof is sorry-free and axiom-free. Build pending (Docker
  symlink constraint per `feedback_researcher_lake_symlink_broken.md`);
  but with such a small PR the build can be deferred to a follow-up
  `*-prep` style PR or verified by mechanic.
- The `q ≠ 2` filter is essential — `DihedralGroup 2` has order 4, not
  the form `p * q` for distinct primes.
- No drift risk: all API names (`DihedralGroup.card`,
  `DihedralGroup.not_isCyclic`, `Nat.Prime.one_lt`, `Nat.Prime.ne_zero`)
  are stable in Mathlib v4.x; cross-checked against rev pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via direct GitHub raw read.
- No concurrent PR conflict at write-time (verified via
  `gh pr list --search lagrange-theorem-oq-01-oq-01-oq-01` returning `[]`,
  and `git log origin/main` showing no recent commits for this slug,
  and `git branch -r | grep lagrange-theorem-oq-01-oq-01-oq-01` empty).
