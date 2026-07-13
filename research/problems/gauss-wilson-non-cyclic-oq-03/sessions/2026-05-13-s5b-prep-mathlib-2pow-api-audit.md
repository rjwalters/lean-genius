# S5b PREP — Mathlib 2-power unit-group API audit + S5b.3 design via `orderOf_five` (doc-only)

**Slug**: `gauss-wilson-non-cyclic-oq-03`
**Iteration**: S5b (PREP, doc-only)
**Date**: 2026-05-13
**Researcher**: researcher-8
**Phase**: ACT
**Build**: none performed
**Mathlib pin**: `inputRev v4.26.0`, lake-manifest rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## 1. Summary

This session is a **forward-design PREP** for **S5b**, the even-prime
(`p = 2`) leg of the per-prime-power unit-side `u² = 1` count. It
**audits the in-flight `S5b OBSERVE` plan** (`#18356`, merged
2026-05-12 23:02 UTC) by **pinning Mathlib decl name + file:line** at
the exact `v4.26.0` Mathlib commit the repo currently builds against,
and **closes the principal ambiguity** that `S5b OBSERVE` left open:

> [`S5b OBSERVE` §S5b.3, Option A] "Mathlib structure iso
> `(ZMod 2^k)ˣ ≃* ℤ/2 × ℤ/2^(k-2)` (**name not verified in
> v4.26.0**)."

We **confirm this iso has no `MulEquiv`-form representative in
Mathlib at `v4.26.0`**, and provide a concrete alternative — an
**elementary `orderOf_five`-based cardinality squeeze** that proves
the count is exactly `4` for `k ≥ 3` **using only existing
`Mathlib/RingTheory/ZMod/UnitsCyclic.lean` decls**. The route mirrors
the already-merged `carmichael_two_pow_of_ne_two` proof at
`Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean:135–148`,
which uses the same `orderOf_five` toolchain to prove
`Monoid.exponent (ZMod (2^n))ˣ = 2^(n-1)` for `3 ≤ n` *without* a
structure-iso `MulEquiv`.

**Net deliverable**: this single doc-only file. **No edits** to
`problem.md`, `knowledge.md`, `state.md`, `proofs/Proofs/*.lean`,
gallery `meta.json`, or `src/data/research/problems/<slug>.json`.
0 axiom delta, 0 sorry delta, 0 build.

## 2. Mathlib `v4.26.0` 2-power unit-group API audit

All decls cited below were verified at Mathlib commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= repo's
`proofs/lake-manifest.json` pin) via
`gh api repos/leanprover-community/mathlib4/contents/<path> -f ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 -H "Accept: application/vnd.github.raw"`.

### 2.1 NEGATIVE finding — no `MulEquiv` structure iso for `(ZMod 2^k)ˣ`

**Claim**: Mathlib `v4.26.0` contains **no decl** of the form
`(ZMod (2 ^ k))ˣ ≃* ZMod 2 × ZMod (2 ^ (k - 2))` (or any
`MulEquiv`-typed analogue) for `k ≥ 3`.

**Evidence**:

- `gh api search/code -f q='MulEquiv ZMod two extension:lean repo:leanprover-community/mathlib4'`
  surfaces five files. Spot-grepping each:
  - `Mathlib/RingTheory/ZMod/Torsion.lean`: only
    `MulEquiv.subgroupCongr` reuse for `rootsOfUnity` (line 30); no
    2-power structure decl.
  - `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`: the **`Products`**
    section (lines 254–) handles only the *cyclicity* question via
    CRT pull-back (`Units.mapEquiv (chineseRemainder _).toMulEquiv`),
    never asserting a structure iso between `(ZMod 2^k)ˣ` and any
    product of cyclic factors.
  - `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`: zero `ZMod
    (2^_)`-mentioning MulEquivs.
  - `Mathlib/Data/Nat/Totient.lean`: zero `ZMod` MulEquivs (totient
    formula only).
  - `Mathlib/GroupTheory/FiniteAbelian/Basic.lean`: the abstract
    finite-abelian structure theorem, but **no specialization to
    `(ZMod 2^k)ˣ`**.
- `gh api search/code -f q='ZMod.unitsZMod extension:lean repo:leanprover-community/mathlib4'`:
  zero hits (the `ZMod.unitsZMod_*` prefix the OBSERVE Mathlib-name
  search guessed at simply does not exist).
- `gh api search/code -f q='Klein ZMod units extension:lean repo:leanprover-community/mathlib4'`:
  zero hits.

**Conclusion**: `S5b OBSERVE` §S5b.3 Option A's "Mathlib structure
iso" is a **phantom name** at `v4.26.0`. It would have to be
**constructed** from scratch (most plausibly: a `MulEquiv` from the
two generators `−1` and `5`), but this is **strictly more work**
than the elementary route in §3.3 below and adds no Mathlib value at
this iteration of the slug. Recommend **drop Option A**.

### 2.2 POSITIVE finding — sufficient elementary primitives DO exist

The following decls exist at the pinned commit, **all in**
`Mathlib/RingTheory/ZMod/UnitsCyclic.lean` unless noted, **all
re-verified by direct read of the pinned file**:

| File:line | Decl | Signature | Used for |
| ---- | ---- | ---- | ---- |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:60` | `isCyclic_units_zero` | `IsCyclic (ZMod 0)ˣ` | (not needed; we case-split `k ≥ 1`) |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:63` | `isCyclic_units_one` | `IsCyclic (ZMod 1)ˣ` | edge case `k = 0` if ever needed |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:66` | `isCyclic_units_two` | `IsCyclic (ZMod 2)ˣ` | **S5b.1** (`k = 1`) cyclicity |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:69-73` | `isCyclic_units_four` | `IsCyclic (ZMod 4)ˣ` | **S5b.2** (`k = 2`) cyclicity |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:81-87` | `not_isCyclic_units_eight` | `¬ IsCyclic (ZMod 8)ˣ` | S5b.3 negative side |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:230-241` | `isCyclic_units_two_pow_iff` | `IsCyclic (ZMod (2 ^ n))ˣ ↔ n ≤ 2` | **S5b.3** non-cyclic hypothesis discharger |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:243-247` | `orderOf_one_add_four_mul` | `(a : ℤ) → Odd a → (n : ℕ) → orderOf (1 + 4 * a : ZMod (2 ^ (n + 2))) = 2 ^ n` | direct precursor to `orderOf_five` |
| `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:249-251` | `orderOf_five` | `(n : ℕ) → orderOf (5 : ZMod (2 ^ (n + 2))) = 2 ^ n` | **S5b.3** main lemma; `5` is the cyclic-subgroup generator |
| `Mathlib/Data/ZMod/Basic.lean:792-794` | `ZMod.unitOfCoprime` | `(x : ℕ) → Nat.Coprime x n → (ZMod n)ˣ` | lift bare `5 : ZMod (2^k)` into the units group |
| `Mathlib/Data/ZMod/Basic.lean:796-` | `ZMod.coe_unitOfCoprime` | `(unitOfCoprime x h : ZMod n) = (x : ZMod n)` | bridge unitOfCoprime back to ring |
| `Mathlib/Data/Nat/Totient.lean` | `Nat.totient_prime_pow` | already cited in S5 ACT `#18233` | gives `φ(2^k) = 2^(k-1)` |
| previously cited at `Mathlib/Data/ZMod/Basic.lean` (line varies) | `ZMod.card_units_eq_totient` | `Fintype.card (ZMod n)ˣ = φ n` | already used in S5 ACT |

**Conclusion**: every primitive `S5b.1`/`S5b.2`/`S5b.3` needs is
already a `theorem` or `lemma` at the pinned commit. No
Mathlib-upstream contribution required.

### 2.3 Mathlib precedent for the elementary route — `carmichael_two_pow_of_ne_two`

The Mathlib decl most architecturally similar to S5b.3 is
`Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean:135-148`'s
`carmichael_two_pow_of_ne_two`, which proves:

```
theorem carmichael_two_pow_of_ne_two {n : ℕ} (hn : n ≠ 2) :
    carmichael (2 ^ n) = ...
```

In the `3 ≤ n` branch (lines 146-148), the proof uses **exactly the
toolchain we propose for S5b.3**:

```lean
let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 <| gcd_pow_right_of_gcd_eq_one rfl
rw [← ZMod.orderOf_five (n - 2), show n - 2 + 2 = n by lia,
  show (5 : ZMod (2 ^ n)) = five by rfl, orderOf_units]
```

This is **direct Mathlib precedent** that the elementary `orderOf_five`
route through `ZMod.unitOfCoprime` is the canonical idiom, **not** a
structure-iso MulEquiv. Our S5b.3 design (§3.3) is a straightforward
adaptation of these three lines.

## 3. Concrete S5b sub-iteration designs

The state.md "Next Action" parenthetical reads:

> S5b / S6 next: even-prime case (`k = 1, 2, ≥ 3` give `2, 2, 4`
> respectively) — needs case analysis on `v₂(n)` ...

**Audit-correction (confirms `S5b OBSERVE`)**: the `k = 1` count is
**`1`, not `2`** — `(ZMod 2)ˣ = {1}` (cardinality 1, the only odd
residue mod 2 is `1`), so `u² = 1` has the unique solution `u = 1`.
The S5b OBSERVE table (`#18356` §"What the session covers") is
correct; the state.md parenthetical is off-by-one. Bundle the
correction into the eventual S5b state-update commit, not a separate
PR.

Below: explicit Lean-statement designs for the three sub-iterations,
each ≤ 90 LOC and each conjugate-free against `S5b OBSERVE` Option C
(which we now subsume).

### 3.1 S5b.1 — `k = 1`: `(ZMod 2)ˣ` has 1 solution

**Mathematical content**: `(ZMod 2)ˣ ≅ {1}` (trivial group), so the
filter `{u : (ZMod 2)ˣ | u^2 = 1}` is the entire (1-element) group.

**Proposed lemma**:

```lean
theorem card_filter_sq_eq_one_units_zmod_two :
    ((Finset.univ : Finset ((ZMod 2)ˣ)).filter (fun u => u^2 = 1)).card = 1 := by
  decide
```

**Why `decide` works**: `(ZMod 2)ˣ` is `DecidableEq`, finite of
cardinality 1 (via `ZMod.card_units_eq_totient` and `φ 2 = 1`); the
filter equality `u^2 = 1` is decidable for every element; the
1-element enumeration is fully reducible at elaboration time.

**Estimate**: ≤ 10 Lean LOC including the docstring.

### 3.2 S5b.2 — `k = 2`: `(ZMod 4)ˣ` has 2 solutions via S4 generic

**Mathematical content**: `(ZMod 4)ˣ` is cyclic of order 2 (via
`isCyclic_units_four` + `card_units_eq_totient` + `φ 4 = 2`). The
order is even, so the **S4 generic theorem**
`card_filter_sq_eq_one_cyclic_even` (already merged in `#18125`,
file lines ~280-300) applies directly: count = 2.

**Proposed lemma**:

```lean
theorem card_filter_sq_eq_one_units_zmod_four :
    ((Finset.univ : Finset ((ZMod 4)ˣ)).filter (fun u => u^2 = 1)).card = 2 := by
  haveI : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_four
  have heven : 2 ∣ Fintype.card (ZMod 4)ˣ := by
    rw [ZMod.card_units_eq_totient]; decide -- φ 4 = 2
  exact card_filter_sq_eq_one_cyclic_even heven  -- from S4, #18125 line 280s
```

**Estimate**: ~15-20 Lean LOC (some of which is unfolding totient).

**Trap**: `card_filter_sq_eq_one_cyclic_even`'s expected hypothesis
signature should be checked against the merged S4 file
(`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` post-`#18125`); if its
type is over `Finset.univ.filter (· ^ 2 = 1)` rather than the named
`Finset` form, the `exact` may need a `simp` rewrite. This is a
syntactic, not mathematical, gap.

**Alternative (fallback)**: pure `decide`. `(ZMod 4)ˣ` has 2
elements; the filter is fully enumerable. Estimated ≤ 5 LOC.

### 3.3 S5b.3 — `k ≥ 3`: `(ZMod 2^k)ˣ` has 4 solutions via `orderOf_five`

**Mathematical content** (sketch; full Lean rendering in S5b.3 ACT):

For `k = n + 2` with `n ≥ 1` (so `k ≥ 3`):

1. **Cardinality**: `|(ZMod 2^k)ˣ| = φ(2^k) = 2^(k-1) = 2 · 2^n`
   (via `ZMod.card_units_eq_totient` + `Nat.totient_prime_pow`).
2. **Generator `5`** has order `2^n` (= `2^(k-2)`) via
   `ZMod.orderOf_five n`. Lift to a unit via
   `ZMod.unitOfCoprime 5` (`Mathlib/Data/ZMod/Basic.lean:792`):
   ```lean
   let five : (ZMod (2 ^ k))ˣ := ZMod.unitOfCoprime 5
     (by ...)  -- gcd(5, 2^k) = 1
   ```
3. **Generator `−1`** has order `2` (it is the negation of the unit
   `1`; non-trivial because `−1 ≠ 1` in `ZMod 2^k` for `k ≥ 1`).
4. **Disjointness of cyclic subgroups generated by `−1` and `5`**:
   `5^j ≠ −1` for any `j ∈ [0, 2^n)`. Reason: `5 ≡ 1 (mod 4)`, so
   by induction `5^j ≡ 1 (mod 4)` for all `j`; but `−1 ≡ 3 (mod 4)`
   in `ZMod 2^k` when `k ≥ 2`. Hence
   `⟨−1⟩ ∩ ⟨5⟩ = {1}` in `(ZMod 2^k)ˣ`.
5. **Cardinality squeeze**: the products
   `{(−1)^a · 5^b | a ∈ {0,1}, b ∈ [0, 2^n)}` form a set of size
   `2 · 2^n = 2^(k-1) = |(ZMod 2^k)ˣ|` (by disjointness — step 4).
   So every unit is **uniquely** of the form `(−1)^a · 5^b`.
6. **Count `u² = 1`**: `((−1)^a · 5^b)² = 5^(2b)`. Then
   `5^(2b) = 1 ↔ orderOf 5 ∣ 2b ↔ 2^n ∣ 2b ↔ 2^(n-1) ∣ b`
   (for `n ≥ 1`). The number of `b ∈ [0, 2^n)` satisfying
   `2^(n-1) ∣ b` is exactly **2** (namely `b ∈ {0, 2^(n-1)}`). And
   `a ∈ {0, 1}` is free (since `(−1)² = 1` always). Total:
   **`2 · 2 = 4`**. □

**Proposed lemma signature**:

```lean
theorem card_filter_sq_eq_one_units_zmod_two_pow_ge_three
    (k : ℕ) (hk : 3 ≤ k) :
    ((Finset.univ : Finset ((ZMod (2 ^ k))ˣ)).filter (fun u => u^2 = 1)).card = 4
```

**Estimated breakdown (60-90 Lean LOC)**:

- Lift `5` to a unit via `ZMod.unitOfCoprime` (~5 LOC)
- Lift `(−1)` to a unit via `Units.mkOfMulEqOne (−1) (−1) (by ring)`
  or `Units.neg 1` (~5 LOC)
- `orderOf_units` bridge between `ZMod.orderOf_five` (on the ring
  element) and the unit version (~10 LOC; see Carmichael.lean:147)
- Disjointness `5^j ≠ −1`: induct on `j` showing
  `5^j ≡ 1 (mod 4)`; observe `−1 ≡ 3 (mod 4)` for `k ≥ 2` (~20 LOC)
- The cardinality squeeze + bijection
  `{0,1} × [0, 2^n) → (ZMod 2^k)ˣ` (~20-30 LOC; the work is showing
  the image surjects, since injectivity is from disjointness)
- The final `u² = 1` count: closed-form
  `card_filter_eq_card_filter_of_bijective` + count `b` satisfying
  `2^(n-1) ∣ b` in `[0, 2^n)` (~15 LOC)

**Risks**:

1. **Order of `(−1)` in `ZMod 2`**: in `ZMod 2`, `−1 = 1`, so `−1`
   has order 1, not 2. This is precisely why we need the hypothesis
   `k ≥ 3` (so `2^k ≥ 8`, and `−1 = 2^k - 1` is unambiguously
   distinct from `1`). The hypothesis already screens this off; just
   document it.
2. **`orderOf_units` orientation**: `orderOf_units` reverses ring vs
   units (`orderOf (u : G)` vs `orderOf ((u : Gˣ) : G)`). The
   Carmichael.lean:147 idiom shows the direction we want:
   `rw [← ZMod.orderOf_five (n - 2), show n - 2 + 2 = n by lia,
        show (5 : ZMod (2 ^ n)) = five by rfl, orderOf_units]`.
   Reuse verbatim.
3. **`gcd(5, 2^k) = 1` proof**: `gcd_pow_right_of_gcd_eq_one rfl` is
   the Mathlib idiom; verified at Carmichael.lean:146.
4. **`(−1) * 5^j` enumeration distinct**: the map
   `(a, b) ↦ (−1)^a * 5^b` is a `MonoidHom` from `ZMod 2 × ZMod 2^n`
   IF we set up the iso right; but we don't need the structure iso
   — just injectivity, which is disjointness + `5^b ≠ 5^b'` for
   `b ≠ b'` (from `orderOf 5 = 2^n` exactly).

**Alternative (Option B from S5b OBSERVE)**: `decide` for `k = 3, 4,
5, ..., N` with `N` ≥ 4, then deal with `k > N` via the same Lean
infrastructure as Option A/C. This is **strictly worse** than Option
C: we pay the same setup cost plus a bunch of redundant `decide`
calls. Recommend **drop Option B**.

**Alternative (Option C from S5b OBSERVE)**: direct Hensel-style
enumeration of roots `{1, −1, 2^(k-1)+1, 2^(k-1)−1}`. This is the
mathematical content of our cardinality-squeeze argument expressed in
different coordinates. Hensel-lifting in Lean requires either (a)
explicit four-element enumeration which doesn't generalize cleanly,
or (b) the same orderOf_five machinery just in a more roundabout
direction. **Subsumed by the orderOf_five route above**.

## 4. Audit of S5b OBSERVE table

The table in `S5b OBSERVE` `#18356` reproduces here:

| `k`     | `(ZMod 2^k)ˣ` structure                       | `u² = 1` count |
| ----- | ----------------------------- | -------------- |
| `k = 1` | trivial `{1}`                  | **1**          |
| `k = 2` | `ℤ/2 ≅ {1, 3}`                 | **2**          |
| `k ≥ 3` | `ℤ/2 × ℤ/2^(k-2)` (non-cyclic) | **4**          |

**S5b PREP verification**:

- **Row `k = 1`**: `|(ZMod 2)ˣ| = φ(2) = 1`. The unique unit `1`
  satisfies `1² = 1`. Count = **1**. ✓
- **Row `k = 2`**: `|(ZMod 4)ˣ| = φ(4) = 2`. The two units `1` and
  `3` both satisfy `u² = 1` (`1² = 1`; `3² = 9 ≡ 1 mod 4`). Count =
  **2**. ✓
- **Row `k ≥ 3`**: by §3.3 argument, count = **4**. The four
  solutions are explicitly `{1, −1, 2^(k-1) + 1, 2^(k-1) − 1}`
  (cross-checked with the `state.md` tail: "generator (`2^{k-1} + 1`);
  count is exactly 4, with roots `{1, -1, 2^{k-1}+1, 2^{k-1}-1}`").
  ✓

The `state.md` "Next Action" parenthetical's "`k = 1, 2, ≥ 3` give
`2, 2, 4`" is the off-by-one already flagged in S5b OBSERVE
`#18356`. **No new audit-correction needed** at this PREP.

## 5. Race-safety and orthogonality

### 5.1 Concurrent PRs at audit time (07:54 UTC, 2026-05-13)

`gh pr list --search 'gauss-wilson-non-cyclic-oq-03 in:title' --state open` returns:

- **`#18230`** S5-prep parity of `|(ZMod p^k)ˣ|` at odd primes —
  OPEN since 2026-05-12 18:11 (13h stale, build pending). **S8 PREP
  `#18597` (merged 05:20 UTC) recommends close** as `mechanic` /
  `deployer` work — the parity argument was inlined into S5 ACT
  `#18233`. **No overlap with this PREP**: `#18230` covers odd
  primes; we cover the even prime.

No other open PRs on the slug.

### 5.2 File-disjointness against in-flight PRs

This PREP modifies a **single new file**:

```
research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s5b-prep-mathlib-2pow-api-audit.md
```

Diff against `#18230`:

- `#18230` touches `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`,
  `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`,
  `research/problems/gauss-wilson-non-cyclic-oq-03/state.md`.
- This PREP touches **none of those**. Conflict-free.

### 5.3 Orthogonality against recently-merged PREPs

The session-level deltas of recently-merged PREPs:

- `#18356` S5b OBSERVE: new sessions file
  `2026-05-12-s5b-observe-even-prime-case.md`. **Pristine relative
  to ours** (different filename, different scope: OBSERVE = planning;
  this PREP = API-pinned design + audit).
- `#18423` S6 PREP: new sessions file
  `2026-05-12-s06-prep-crt-multiplicativity.md`. **Different
  topic** (CRT vs 2-power), no overlap.
- `#18465` S7 PREP: new sessions file
  `2026-05-13-s07-prep-main-theorem-induction.md`. **Different
  topic** (induction-on-`primeFactors`), no overlap.
- `#18510` S6/S7 PREP audit: new sessions file
  `2026-05-13-s06-s07-prep-mathlib-api-audit.md`. **Adjacent topic**
  (Mathlib API audit) but **disjoint scope** — `#18510` audited
  `ZMod.chineseRemainder`, `MulEquiv.prodUnits`, induction-on-omega;
  this PREP audits `orderOf_five`, `unitOfCoprime`,
  `isCyclic_units_two_pow_iff`. Filename and content do not collide.
- `#18597` S8 PREP: new sessions file
  `2026-05-13-s8-prep-stale-18230-audit.md`. **Disjoint scope**
  (admin/close-recommendation), no API or design overlap.

No race expected.

## 6. Estimated next-step LOC ledger

If the proposed S5b sub-iterations land in three separate ACT
sessions:

| Sub-iter | New theorems | Sorries delta | Axioms delta | Lean LOC (est.) |
| -------- | ------------ | ------------- | ------------ | --------------- |
| S5b.1    | +1 (`card_filter_sq_eq_one_units_zmod_two`) | 0 | 0 | ~10 |
| S5b.2    | +1 (`card_filter_sq_eq_one_units_zmod_four`) | 0 | 0 | ~15-20 |
| S5b.3    | +1 (`card_filter_sq_eq_one_units_zmod_two_pow_ge_three`) + auxiliaries | 0 | 0 | ~60-90 |
| **Total** | +3-5 | **0** | **0** | **~85-120 LOC** |

This closes the even-prime leg without any new axioms or
sorries, and reduces the main-theorem skeleton in S7 to a
single 4-line `match v₂(n)` dispatcher
(S5 ACT odd case + S5b.1/.2/.3 even cases).

## 7. Honesty (§10 of researcher role)

- **No `lake build` performed**: the worktree `.lake` symlink loop
  (cf. researcher-3's MEMORY entry, `feedback_researcher_lake_symlink_loop_and_wipe.md`)
  precludes local docker build in this iteration. Mathlib API decls
  are pinned by **direct read of `gh api repos/leanprover-community/mathlib4/contents/<path>`
  at commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**.
- **No Lean code changes**: every Lean code snippet in §3 is a
  **design proposal** for S5b.1/.2/.3 ACT, not a tested fragment.
  The `S5b.3` argument (§3.3) is rigorous at the mathematical level
  but the Lean rendering may need adjustment for syntactic details
  (`Finset.univ.filter` vs `.filter`, exact `orderOf_units`
  argument order, etc.).
- **The cardinality squeeze in §3.3 is the original mathematical
  content** of this PREP (going beyond what S5b OBSERVE `#18356`
  worked out). It is standard textbook material (Ireland-Rosen
  §4.1, "Multiplicative Group of `ZMod (p^k)`"), but the Lean
  rendering is novel for this slug.
- **No build verification of the disjointness argument** (`5^j ≢
  −1 (mod 2^k)` for `k ≥ 2`): asserted at the math level. The Lean
  proof will use `Nat.pow_mod` and reduction mod `4`.
- **The `Carmichael.lean:135-148` precedent** is **the strongest
  evidence** that the elementary route works in Lean as proposed.
  We are **adapting** a working Mathlib idiom, not inventing one.

## 8. Recommendation

1. **Merge this PREP** (orthogonal, doc-only, low risk).
2. **S5b.1 ACT next session**: trivial, can be batched with S5b.2
   into a single Lean PR (~25 LOC total).
3. **S5b.2 ACT**: short, well-scoped, S4-generic-reuse.
4. **S5b.3 ACT**: the substantive Lean work (~60-90 LOC); allocate
   a dedicated session.
5. **S6 ACT** (CRT multiplicativity): can run in parallel with
   S5b.1/.2/.3 since the file scopes are disjoint (CRT works on the
   prime-factorization level, S5b on the prime-power level).
6. **S7 ACT** (main induction): requires S5 + S5b + S6 done; depends
   only on the **statements** of the per-prime-power counts, not on
   their proofs, so could be written in parallel as a `match v₂(n)`
   dispatcher with `sorry`s for the missing pieces and filled in as
   they land.

The main-theorem sorry should close in **3-4 more ACT sessions**
based on this design.

---

🤖 Generated by researcher-8
