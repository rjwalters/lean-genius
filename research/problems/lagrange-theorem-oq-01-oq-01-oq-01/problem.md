# Problem: Exhibit a non-cyclic group of order `pq` when `p | (q-1)`

## Statement

### Plain Language

The parent gallery proof `lagrange-theorem-oq-01-oq-01` (Sylow-theoretic
classification of pq-groups, file `Proofs/LagrangeTheoremOQ01OQ01.lean`)
proves:

- **Always** (for primes `p < q` and `|G| = pq`): the Sylow q-subgroup is
  unique and normal (`lagrange_pq_unique_normal_q`, `lagrange_pq_n_q_eq_one`).
- **When `p ∤ (q-1)`**: every group of order `pq` is cyclic
  (`pq_unique_when_coprime` — universal quantification).
- **When `p | (q-1)`**: a non-cyclic group of order `pq` *has* `n_p = q`
  (`lagrange_pq_nonabelian_n_p_eq_q` — conditional on existence).

What the parent does **not** prove is that the `p | (q-1)` case is
non-vacuous — i.e., it does not exhibit any non-cyclic witness. The
classification is "two groups exist, the cyclic one and *some* non-abelian
one"; the existence direction of the non-abelian case is left implicit.

This OQ asks: **construct an explicit non-cyclic group of order `pq`
whenever `p | (q-1)`**. Concrete deliverable: a Lean term-level construction
plus a proof that the constructed group has the right cardinality and is
not cyclic.

### Formal Statement

For the smallest case (`p = 2`, `q` an odd prime), produce:

```lean
-- Existence theorem (Approach A, target for S2)
theorem exists_noncyclic_of_order_two_mul_odd_prime
    {q : ℕ} (hq : Nat.Prime q) (hq_odd : q ≠ 2) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 2 * q ∧ ¬ IsCyclic G := by
  refine ⟨DihedralGroup q, inferInstance, inferInstance, ?_, ?_⟩
  · -- 2 * q via DihedralGroup.card
    have : NeZero q := ⟨hq.one_lt.ne' ∘ fun h => absurd h.symm hq.ne_zero⟩
    exact DihedralGroup.card
  · -- non-cyclic via DihedralGroup.not_isCyclic
    exact DihedralGroup.not_isCyclic (by
      intro hq1
      exact (Nat.Prime.one_lt hq).ne' hq1.symm)
```

For the general case (`p < q` primes, `p | (q-1)`), produce:

```lean
-- General existence theorem (Approach B, deferred to S3+)
theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (hdvd : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = p * q ∧ ¬ IsCyclic G := by
  -- Constructed via ZMod q ⋊[φ] ZMod p where φ : ZMod p →* MulAut (ZMod q)
  -- is non-trivial (exists because p | q-1 = |(ZMod q)ˣ|).
  sorry
```

After this OQ resolves, the parent's `lagrange_pq_nonabelian_n_p_eq_q`
(currently conditional on `¬ IsCyclic G`) gains an unconditional companion:
when `p | (q-1)`, such a non-cyclic `G` exists.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - seeker-selected
  - group-theory
  - sylow
  - dihedral-group
  - semidirect-product
  - existence-witness
```

**Significance**: 6/10 — Completes the existence direction of the
pq-classification stated in the parent. Without it, the parent's
"two groups exist when `p | (q-1)`" remains a counting statement
about an unspecified witness. Provides the first explicit non-abelian
finite-group construction in the gallery, and exercises Mathlib's
`DihedralGroup` and `SemidirectProduct` APIs in a load-bearing way.

**Tractability**: 7/10 — Approach A (specialization to `p = 2`) is a
single S2 PR with ~50 lines of Lean, using only stable Mathlib API
(`DihedralGroup`, `DihedralGroup.card`, `DihedralGroup.not_isCyclic`).
Approach B (general `p, q`) requires constructing a non-trivial hom
`ZMod p →* MulAut (ZMod q)` from a primitive `p`-th root of unity in
`(ZMod q)ˣ`; multi-session, ~200 lines.

## Why This Matters

1. **Completes the pq-classification**. The parent proves the cyclic
   case is unique (`p ∤ (q-1) ⇒ G ≅ ZMod (p*q)`) but leaves the non-cyclic
   case at conditional level: "if `G` is non-cyclic, then `n_p = q`".
   Without an existence witness, the user has no proof that the non-cyclic
   case is reachable. This OQ supplies the witness.

2. **First non-abelian construction in the gallery**. The current gallery
   under `lagrange-theorem-oq-01` is entirely about cyclic / abelian
   classification. Building `DihedralGroup q` or `ZMod q ⋊ ZMod p` as a
   verified Lean term puts a concrete non-abelian group on the gallery —
   a precondition for later questions about character theory, representations,
   or Frobenius's theorem.

3. **Sets up Approach B reusability**. The semidirect product `N ⋊[φ] G`
   is a Mathlib structure used in many group-classification proofs (Schur–
   Zassenhaus, p-nilpotent groups, soluble groups). Demonstrating its use
   here for the smallest non-abelian case provides a reusable scaffold for
   the gallery's future group-theory entries.

4. **Surfaces `MulAut (ZMod q)` ↔ `(ZMod q)ˣ` bridge**. Approach B requires
   the canonical isomorphism `MulAut (ZMod q) ≃* (ZMod q)ˣ` (multiplication
   automorphisms of the cyclic additive group). This bridge is in Mathlib
   but rarely used in gallery proofs; surfacing it here pairs with the
   `OQ-04` direction (concrete homomorphism examples).

## Known Results

### Already Proven (in parent `LagrangeTheoremOQ01OQ01.lean`)

- `lagrange_pq_unique_normal_q : ∃ Q : Sylow q G, Q.Normal` — always (line 78).
- `lagrange_pq_n_q_eq_one : Fintype.card (Sylow q G) = 1` — always (line 85).
- `lagrange_pq_n_p_eq_one_when_coprime : ... = 1` when `p ∤ (q-1)` (line 100).
- `pq_unique_when_coprime : ... → ∀ G, ... → IsCyclic G` (line 117). **Universal**.
- `lagrange_pq_nonabelian_n_p_eq_q : ... ∧ ¬ IsCyclic G → ... = q` (line 131). **Conditional**.
- `order_15_cyclic`, `order_35_cyclic`, `order_77_cyclic` — universal cyclic statements.
- `order_6_non_unique`, `order_21_non_unique`, `order_55_non_unique` — only verify
  the divisibility hypothesis `p | q-1`, not existence of non-cyclic witness.

### Available Mathlib Infrastructure (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Need | Mathlib name | Module |
|------|--------------|--------|
| Dihedral group | `DihedralGroup : ℕ → Type` | `Mathlib.GroupTheory.SpecificGroups.Dihedral` |
| Dihedral cardinality | `DihedralGroup.card : Fintype.card (DihedralGroup n) = 2*n` | same |
| Dihedral nat-card | `DihedralGroup.nat_card : Nat.card (DihedralGroup n) = 2*n` | same |
| Dihedral non-cyclic | `DihedralGroup.not_isCyclic : n ≠ 1 → ¬ IsCyclic (DihedralGroup n)` | same |
| Dihedral cyclic iff | `DihedralGroup.isCyclic_iff : IsCyclic ↔ n = 1` | same |
| Dihedral instances | `Fintype (DihedralGroup n)` [`NeZero n`] | same |
| Semidirect product | `SemidirectProduct N G φ` notation `N ⋊[φ] G` | `Mathlib.GroupTheory.SemidirectProduct` |
| Semidirect cardinality | `SemidirectProduct.card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G` | same |
| Mul-aut group | `MulAut (ZMod q)` | `Mathlib.GroupTheory.GroupAction.Defs` |
| Unit group iso | `ZMod.unitsEquivCoprime` and related | `Mathlib.Data.ZMod.Units` |
| Prime is odd or 2 | `Nat.Prime.eq_two_or_odd'` | `Mathlib.Data.Nat.Prime.Basic` |

### Open Sub-Questions

- **Q1** (Approach A): For `q` an odd prime, does `DihedralGroup q` satisfy
  `Fintype.card = 2 * q ∧ ¬ IsCyclic`? **Yes** — `DihedralGroup.card`
  gives the cardinality (under `NeZero q`, which follows from primality);
  `DihedralGroup.not_isCyclic` gives the non-cyclic property (`q ≠ 1`
  follows from `Nat.Prime.one_lt`).

- **Q2** (Approach B): For `p < q` primes with `p | (q-1)`, does a
  non-trivial hom `φ : ZMod p →* MulAut (ZMod q)` exist? **Yes** —
  `(ZMod q)ˣ` has order `q-1` and contains an element of order `p`
  whenever `p | q-1` (cyclic group structure of `(ZMod q)ˣ` for prime
  `q`). The hom sends `1 : ZMod p` to multiplication by that element.

- **Q3** (Approach C): Is direct construction of `S₃` (for order 6) or
  similar small cases simpler than going through `DihedralGroup`?
  **Probably not** — `Equiv.Perm (Fin 3)` has cardinality 6 via
  `Fintype.card_perm`, but the non-cyclic proof is more verbose than
  using `DihedralGroup`.

### Our Goal

This S1 OBSERVE iteration: survey the three approaches; commit to
Approach A as the first attack target; produce the load-bearing
sub-lemma list and Mathlib API map. No Lean changes in this iteration.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `lagrange-theorem-oq-01-oq-01` (parent) | Sylow classification of pq-groups; this OQ supplies the existence witness for the non-cyclic case. |
| `lagrange-theorem-oq-01` | Sylow's theorems as partial converse to Lagrange. |
| `lagrange-theorem` (root) | Lagrange's theorem itself. |
| `lagrange-theorem-oq-02` | Index-divides-order corollary. |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `DihedralGroup q` for the `p = 2` specialization (RECOMMENDED for S2)**.

   For an odd prime `q ≥ 3`, the dihedral group `DihedralGroup q` has
   order `2 * q = p * q` (with `p = 2`) and is non-cyclic. Mathlib provides
   both facts directly:

   ```lean
   theorem DihedralGroup.card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n
   theorem DihedralGroup.not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)
   ```

   The `NeZero q` instance follows from `q` prime (`hq.pos` ⇒ `q ≠ 0`).
   The `q ≠ 1` follows from `hq.one_lt`. The condition `2 | (q - 1)`
   follows from `q` being an odd prime (`q ≠ 2 ⇒ q` odd ⇒ `q - 1` even).

   **Why it might work**: All ingredients are stable Mathlib API. The
   proof is a single `refine` + four short discharges. The hardest step
   is supplying the `NeZero q` instance.

   **Risk**: The case `q = 2` is excluded (DihedralGroup 2 ≅ Klein four,
   which has order 4 = 2*2 = p*p ≠ p*q for distinct primes). The
   statement should require `q ≠ 2` explicitly, matching the parent's
   `p < q` convention.

   **Estimated effort**: 1 PR, ~50 lines of Lean, single session.

2. **Approach B — semidirect product `ZMod q ⋊[φ] ZMod p` (deferred to S3+)**.

   The general construction. Given `p | (q-1)`, the unit group `(ZMod q)ˣ`
   has an element `u` of order `p` (because `(ZMod q)ˣ` is cyclic of
   order `q - 1` for `q` prime, by `ZMod.IsField` + general field theory).
   Define `φ : ZMod p →* MulAut (ZMod q)` by `φ k = (· * u^k)` (lifting
   through the canonical iso `(ZMod q)ˣ ≃* MulAut (ZMod q)` — additive
   automorphisms of `ZMod q` are exactly multiplication by units).

   Then `ZMod q ⋊[φ] ZMod p` is non-cyclic (because φ is non-trivial
   makes the product non-abelian) and has cardinality `p * q` by
   `SemidirectProduct.card`.

   **Why it might work**: Each piece is in Mathlib (`SemidirectProduct`,
   `(ZMod q)ˣ`, `MulAut (ZMod q)`). The hard part is constructing the
   `p`-th root of unity in `(ZMod q)ˣ` and lifting it to `MulAut`.

   **Risk**: The cyclic structure of `(ZMod q)ˣ` for prime `q` requires
   `ZMod.unitsCyclic` or similar; if that's not at the pinned rev,
   we may need to prove it (using `IsCyclic (Subgroup.zpowers x)` or
   `Cardinal.card (ZMod q)ˣ = q - 1`). Multi-session, ~200 lines.

3. **Approach C — direct construction of small cases**.

   For order 6: `Equiv.Perm (Fin 3)` has cardinality 6 by `Fintype.card_perm`
   and is non-cyclic by `Equiv.Perm.not_isCyclic` (for `n ≥ 3`). For
   order 21: build the unique non-abelian group of order 21 via explicit
   multiplication table or as `ZMod 7 ⋊ ZMod 3`. For order 55: similar.

   **Why it might work**: Each case is fully concrete and `decide`-able
   for small `n`. But we'd need a separate case for each `(p, q)` pair.

   **Risk**: Does not generalize. Adds clutter without solving the
   underlying question. Best used as supplementary examples after
   Approach A lands.

### Key Difficulties

- **`NeZero q` instance synthesis**. `NeZero` from `q` prime requires
  either a `Fact (1 < q)` shortcut or manual instance via `⟨hq.ne_zero⟩`.
  Mathlib's `Nat.Prime.one_lt` gives `1 < q`, so `q ≠ 0` is downstream;
  ensure the instance is discoverable in the `refine`.

- **`p = 2` vs `q = 2` ambiguity**. The parent uses `p < q` with `p`
  smaller. For Approach A, `p = 2` and `q ≥ 3` is the natural minimum.
  We must exclude `q = 2`, not just request `q` prime.

- **Approach B requires `(ZMod q)ˣ` cyclic structure**. Mathlib has
  `ZMod.unitsCyclic` (or equivalent) for `q` prime — confirm at pinned
  rev. If absent, we can fall back to `IsCyclic_of_prime_card` once we
  show the unit group has prime order (false for general `q`, so this
  fallback doesn't apply; need the genuine result that `Field.Unit` is
  cyclic for finite fields).

- **The `q ≠ 2` filter for Approach A excludes `pq = 4`**. But `pq = 4`
  is not a product of two distinct primes (`p = q = 2`), so this case
  is outside the parent's `p < q` hypothesis. No new ground lost.

### What Would a Proof Need? (Approach A)

- **Main theorem**: `exists_noncyclic_of_order_two_mul_odd_prime`. Proof
  sketch:
  ```
  Given q prime, q ≠ 2.
  - q is odd (Nat.Prime.eq_two_or_odd' on hq gives q = 2 ∨ Odd q;
    discharge q = 2 via hq_odd).
  - q ≥ 3 ⇒ q ≠ 0 ⇒ NeZero q ⇒ Fintype.card (DihedralGroup q) = 2*q.
  - q ≠ 1 (from q prime, hq.one_lt) ⇒ ¬ IsCyclic (DihedralGroup q).
  ```

- **Existence wrapper** (optional): `exists_two_distinct_groups_of_order_pq`
  packaging the cyclic `ZMod (2*q)` and non-cyclic `DihedralGroup q`
  side-by-side as concrete witnesses.

- **Order-6 corollary** (matches parent's `order_6_non_unique`):
  ```
  ∃ (G : Type) [Group G] [Fintype G], Fintype.card G = 6 ∧ ¬ IsCyclic G
  ```
  Specializes `exists_noncyclic_of_order_two_mul_odd_prime` at `q = 3`.

- **Order-10, order-14, order-22, ...**: same template at `q ∈ {5, 7, 11, ...}`.
  Demonstrates the family.

## Tractability Assessment

**Difficulty**: Low (Approach A) | Medium-High (Approach B) | Low per case (Approach C, but doesn't generalize)

**Justification**:
- Approach A is a single S2 PR with ~50 lines of new Lean (1 main theorem
  + a few corollaries). All API names (`DihedralGroup`, `DihedralGroup.card`,
  `DihedralGroup.not_isCyclic`, `Nat.Prime.eq_two_or_odd'`) are stable in
  Mathlib v4.26.0.
- Approach B is a multi-session effort. Constructing the non-trivial hom
  `φ : ZMod p →* MulAut (ZMod q)` requires:
  (a) the cyclic structure of `(ZMod q)ˣ`,
  (b) the iso `(ZMod q)ˣ ≃* MulAut (ZMod q)`,
  (c) a `p`-th root of unity in `(ZMod q)ˣ` from `p | q-1`.
- Approach C is shallow — doesn't generalize, so the gallery cost-benefit
  doesn't favor it as a standalone target.

**Estimated Effort**:
- Approach A: 1 session, single PR, ~50 lines Lean.
- Approach B: 3-4 sessions, ~200 lines Lean (hom construction + lift to
  semidirect product + cardinality + non-cyclic proof).
- Approach C: 1-2 sessions for each `(p, q)` case, no shared infrastructure.

## References

### Papers / Books
- Burnside, W. (1911). *Theory of Groups of Finite Order*, 2nd ed., §§93–95.
- Dummit, D. & Foote, R. (2004). *Abstract Algebra*, 3rd ed., §4.5, Theorem 14.
- Robinson, D. J. S. (1996). *A Course in the Theory of Groups*, §5.3.

### Mathlib
- `Mathlib.GroupTheory.SpecificGroups.Dihedral` — `DihedralGroup`,
  `DihedralGroup.card`, `DihedralGroup.not_isCyclic`,
  `DihedralGroup.isCyclic_iff`.
- `Mathlib.GroupTheory.SemidirectProduct` — `SemidirectProduct N G φ`,
  notation `N ⋊[φ] G`, `SemidirectProduct.card`.
- `Mathlib.Data.ZMod.Units` — `ZMod.unitsEquivCoprime`, unit group facts.
- `Mathlib.GroupTheory.OrderOfElement` — `orderOf_dvd_card`, existence
  of elements of prescribed order.
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — `IsCyclic`,
  `isCyclic_of_prime_card`.
- `Mathlib.GroupTheory.SpecificGroups.KleinFour` — Klein-four group
  (relevant for `q = 2` edge case).

## Metadata

```yaml
tags:
  - group-theory
  - sylow
  - dihedral-group
  - semidirect-product
  - existence-witness
  - non-abelian
  - seeker-selected
related_proofs:
  - lagrange-theorem-oq-01-oq-01
  - lagrange-theorem-oq-01
  - lagrange-theorem-oq-02
  - lagrange-theorem
difficulty: low
source: gallery-gap
created: 2026-05-12
```
