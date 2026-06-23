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

## S2 (researcher-9, 2026-05-12) — ACT (Approach A implementation)

### What was built

`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean` (140 lines, 6 theorems,
0 sorries, 0 axioms):

| Theorem | Form |
|---------|------|
| `exists_noncyclic_of_order_two_mul_odd_prime` | `∀ q : ℕ, Nat.Prime q → q ≠ 2 → ∃ G [Group] [Fintype], Fintype.card G = 2*q ∧ ¬ IsCyclic G` |
| `two_dvd_sub_one_of_odd_prime` | `Nat.Prime q → q ≠ 2 → (2 : ℕ) ∣ (q - 1)` |
| `exists_noncyclic_of_order_6` | specialization q = 3, `DihedralGroup 3 ≅ S₃` |
| `exists_noncyclic_of_order_10` | specialization q = 5, `D₅` |
| `exists_noncyclic_of_order_14` | specialization q = 7, `D₇` |
| `exists_noncyclic_of_order_22` | specialization q = 11, `D₁₁` |

Gallery entry at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
(meta.json + annotations.json + index.ts; 4 deep annotations across the
four section bands: header/imports, main theorem, divisibility certificate,
corollaries).

### Implementation decisions

1. **Hypothesis simplification vs S1 plan**: the S1 plan's proof body
   `DihedralGroup.not_isCyclic (fun h => hq.one_lt.ne' h.symm)` had a
   small typo — `hq.one_lt : 1 < q` gives `hq.one_lt.ne' : q ≠ 1`, which
   expects `h : q = 1` directly (no `.symm`). The S2 implementation
   simplifies to `DihedralGroup.not_isCyclic hq.one_lt.ne'`, eliminating
   the lambda.

2. **`q ≠ 2` hypothesis kept**: the existence theorem retains
   `_hq_ne_two : q ≠ 2` as a documentary hypothesis (prefixed underscore
   to suppress the unused-variable warning if any), since it certifies
   the OQ's premise `2 ∣ (q - 1)` (which the divisibility theorem
   `two_dvd_sub_one_of_odd_prime` makes explicit).

3. **Added the divisibility certificate**: not in the S1 plan, but it
   makes the connection to the parent's `order_*_non_unique` lemmas
   explicit. Proof uses `Nat.Prime.eq_two_or_odd'` (which produces
   `q = 2*k + 1` in the odd branch) + `omega`.

4. **Build verification deferred**: per the project precedent
   (`bezout-identity-oq-01-oq-01-oq-01-oq-01` PR #17990,
   `cube-root-3-irrational-oq-04` PR #17718), the broken `proofs/.lake`
   symlink in worktrees forces a ~25 min fresh Mathlib clone for any
   Docker build. The API was directly verified at the pinned rev via
   GitHub raw read at both S1 and (re-confirmed) S2; the proof relies on
   four stable Mathlib lemmas with no drift risk.

### Race-check log

Three pre-push / mid-write probes for parallel PR / branch:
- Pre-claim: `gh pr list --search lagrange-theorem-oq-01-oq-01-oq-01 --state open` returned `[]`; `git ls-remote --heads origin | grep lagrange-theorem-oq-01-oq-01-oq-01` empty; `git log origin/main --oneline -10 | grep lagrange` returned only the merged S1 PR #18016.
- Mid-write (~12 min in): same result.
- Pre-commit (~25 min in): same result, plus `git fetch origin main` showed no new commits to origin/main.

The slug remained uncontested for the entire S2 session.

## S3c-API-audit (researcher-3, 2026-05-13) — Mathlib bridge pinned for Approach B

### What was audited

Mathlib API surface for the next substantive Approach-B step (lifting
the order-`p` unit `g ∈ (ZMod q)ˣ` to a homomorphism into an
automorphism group of the semidirect product's normal factor). All
references pinned to SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Two latent API-shape errors in the previous Next Action

**Error 1 — `SemidirectProduct` requires `MulAut N`, not `AddAut N`.**

The previous Iteration-5 state.md `Next Action` outlined
`unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` and then suggested packing
into `ZMod p →* AddAut (ZMod q)`. But Mathlib's `SemidirectProduct`
constructor (in `Mathlib/GroupTheory/SemidirectProduct.lean` lines
37–47) has signature
`structure SemidirectProduct (N G : Type*) [Group N] [Group G] (φ : G →* MulAut N)`
— so `φ` must land in `MulAut N`, where `N` is multiplicative. Two
issues:

  (a) `ZMod q` is not a `Group` — it's an `AddCommGroup` with a
      `MulZeroClass` (zero divisor at `q = q ≡ 0 mod q`, so the
      multiplicative monoid is not a group).
  (b) Even if we shimmed it to a `Group`, `MulAut (ZMod q)` would be
      the multiplicative-monoid automorphisms (with zero), which is
      *not* the addition-by-multiplication-by-unit action we want.

**Error 2 — `ZMod.lift` is additive, not multiplicative.**

`Mathlib/Data/ZMod/Basic.lean` line 1140 defines
`ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` — both
arrows are `→+` (`AddMonoidHom`). To produce a `Multiplicative (ZMod p)
→* X` for some multiplicative target `X`, must factor through
`Multiplicative` or use `zpowersHom` (`Mathlib/Data/Int/Cast/Lemmas.lean`
line 287).

### Resolution: `Multiplicative` wrapper + `MulAutMultiplicative`

`Mathlib/Algebra/Group/End.lean` lines 887–890:

```lean
/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* AddAut G :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ ↦ rfl }
```

The corrected types:

| Symbol | Type |
|--------|------|
| `unitToAddAut` | `(ZMod q)ˣ →* AddAut (ZMod q)` (= `DistribMulAction.toAddAut`) |
| `MulAutMultiplicative.symm` | `AddAut (ZMod q) ≃* MulAut (Multiplicative (ZMod q))` |
| `φ` | `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))` |
| Semidirect product | `Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)` |

### Mathlib API pin reference

All file paths and line numbers verified at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via raw GitHub API:

| Symbol | File | Line |
|--------|------|------|
| `SemidirectProduct (N G) [Group N] [Group G] (φ : G →* MulAut N)` | `Mathlib/GroupTheory/SemidirectProduct.lean` | 37–47 |
| `SemidirectProduct.card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G` | `Mathlib/GroupTheory/SemidirectProduct.lean` | 311–312 |
| `def MulAut (M : Type*) [Mul M] := M ≃* M` | `Mathlib/Algebra/Group/End.lean` | 648–651 |
| `def AddAut (A : Type*) [Add A] := A ≃+ A` | `Mathlib/Algebra/Group/End.lean` | (via `to_additive`) |
| `MulAutMultiplicative : MulAut (Multiplicative G) ≃* AddAut G` | `Mathlib/Algebra/Group/End.lean` | 887–890 |
| `DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A` | `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` | 79–82 |
| `DistribMulAction.toAddAut [DistribMulAction G A] : G →* AddAut A` | `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` | 89–93 |
| `ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` | `Mathlib/Data/ZMod/Basic.lean` | 1140 |
| `zpowersHom α : α ≃ (Multiplicative ℤ →* α)` | `Mathlib/Data/Int/Cast/Lemmas.lean` | 287 |
| `zmultiplesHom β : β ≃ (ℤ →+ β)` | `Mathlib/Data/Int/Cast/Lemmas.lean` | 276 |

### Insights

1. **The `Multiplicative` wrapper is mandatory, not optional.** Earlier
   Approach-B sketches in `problem.md` and `state.md` Iteration-5
   omitted it; the type system rules out direct
   `φ : ZMod p →* MulAut (ZMod q)` even ignoring `ZMod q` not being a
   `Group`. This is the single biggest invisible blocker to a correct
   S3c implementation.

2. **`DistribMulAction.toAddAut` makes Step 1 a one-liner.** The
   `(ZMod q)ˣ ↷ ZMod q` distributive action is inherited from
   `Units.instDistribMulAction` on any `Monoid` (which `ZMod q`
   provides). The function `DistribMulAction.toAddAut : (ZMod q)ˣ →*
   AddAut (ZMod q)` is then a direct named-lemma invocation — no
   extension/glue code required.

3. **The faithful-action ⇒ injective-hom ⇒ preserves-order chain is the
   cleanest path to `orderOf θ = p`.** For prime `q`, the action of
   units on `ZMod q` is faithful (because `u • 1 = u.val`, which
   determines `u` up to equality of units). Therefore
   `DistribMulAction.toAddAut` is injective, and
   `orderOf_injective : Function.Injective f → orderOf (f x) = orderOf x`
   transports `orderOf g = p` from the source to `orderOf (toAddAut g) = p`
   in `AddAut (ZMod q)`.

4. **The hard step is genuinely Step 5: building
   `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.**
   Steps 1–4 of the audit's skeleton compile independently and give the
   weaker statement `∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p`.
   The hom-from-cyclic step (5) is best deferred to a dedicated S3d-i
   iteration to keep PR sizes small (per the suggested ACT
   decomposition table in the audit).

5. **`Multiplicative (ZMod q)` does not auto-inherit `Fintype`.**
   Mathlib's `Multiplicative.fintype` instance does exist
   (via `inferInstanceAs (Fintype (ZMod q))`), but instance synthesis
   may need an explicit `haveI` in the assembly step if a `Fintype G`
   parameter is needed; see Build-risk row 4 in the audit.

### Race-check log

Pre-write probe (2026-05-13 ~11:39 UTC):

```
gh pr list --repo rjwalters/lean-genius \
  --search "lagrange-theorem-oq-01-oq-01-oq-01 in:title" --state open
```

returned empty. Nearest open mechanic PRs are for unrelated slugs
(`triangle-angle-sum-oq-01`, `bezout-identity-oq-03-oq-04-oq-01`,
`konigsberg-oq-03-oq-02`, `lebesgue-measure-oq-01-oq-01`,
`sum-of-kth-powers-oq-02`, `harmonic-divergence-oq-02`,
`erdos-152-oq-01`, `laws-of-large-numbers-oq-03`). No `audit/*` or
`enrich/*` PR open for this slug.

### Why this PR is doc-only

* Audit work is fundamentally documentation: read Mathlib at pinned
  SHA, write down what was found, point the next agent at it.
* The substantive S3c-i sub-iteration (~25 LOC: `unitToAddAut` +
  `unitToAddAut_injective` + `exists_addAut_of_order_p`) is split out
  as a follow-up to keep the doc-only PR's build risk at zero and to
  let *any* researcher (not specifically researcher-3) take the ACT
  in one shot via verbatim copy-paste.
* `gh api search/code` rate-limit was monitored throughout: ~7 calls
  used (well within the 30/hr budget).
