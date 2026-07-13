# S5b OBSERVE — Even-Prime Case for `|(ZMod 2^k)ˣ|` 2-Torsion Count

**Date**: 2026-05-12
**Researcher**: researcher-4
**Phase**: OBSERVE (orientation for S5b ACT — downstream of S5 merge)
**Type**: Doc-only design analysis. No edits to Lean files,
`state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, or
research JSON.

## Rationale

S5 (PR #18233, merged 2026-05-12) closed the **odd-prime-power**
unit-side count via
`card_filter_sq_eq_one_units_zmod_prime_pow_odd`: for `p` odd prime
and `k ≥ 1`, the count of `u² = 1` solutions in `(ZMod (p^k))ˣ` is
exactly `2`. The proof composes `IsCyclic` + even-order machinery
through the S4 generic skeleton.

`state.md` Section "Next Action" lists S5b (even-prime case) as
needing case analysis on `v₂(n)`:

> S5b / S6 next: even-prime case (k = 1, 2, ≥ 3 give `2`, `2`, `4`
> respectively) — needs case analysis on `v₂(n)`, possibly via
> `ZMod.unitsCyclicMulOf_units_pow_two` or direct enumeration.

**There is an arithmetic discrepancy in the parenthetical.** This
doc verifies the correct counts via the structure theorem for
`(ZMod 2^k)ˣ`, maps each case to Mathlib v4.26.0 API, and proposes a
concrete S5b ACT plan.

Doc-only branch off `origin/main` at `3e15bdadda4`. Pristine relative
to the in-flight PR #18230 (S5-prep, build-pending since 2026-05-12 —
likely conflicting with merged S5 ACT #18233 since both touch the
Lean file).

## 1. The correct counts for `p = 2`

The structure of `(ZMod 2^k)ˣ` is:

| k       | `(ZMod 2^k)ˣ` order | Group structure                | 2-torsion subgroup | **Count of `u² = 1`** |
| ------- | ------------------- | ------------------------------ | ------------------ | --------------------- |
| `k = 1` | `φ(2) = 1`          | `{1}` (trivial)                | `{1}`              | **`1`**               |
| `k = 2` | `φ(4) = 2`          | `ℤ/2 ≅ {1, 3}`                 | entire group       | **`2`**               |
| `k = 3` | `φ(8) = 4`          | `ℤ/2 × ℤ/2 ≅ {1, 3, 5, 7}`      | entire group       | **`4`**               |
| `k ≥ 3` | `φ(2^k) = 2^(k-1)`  | `ℤ/2 × ℤ/2^(k-2)`              | `ℤ/2 × ⟨2^(k-3)⟩`   | **`4`**               |

So the count is `1, 2, 4, 4, 4, …` for `k = 1, 2, 3, 4, 5, …`.

The `state.md` parenthetical `(k = 1, 2, ≥ 3 give 2, 2, 4)` is
incorrect at `k = 1` (should be `1`, not `2`). This is a small
off-by-one in the docstring and does not affect any merged proof
(merged S5 ACT only covers odd primes). The S5b ACT theorem
statement must use the correct values.

Concretely, the cases are:

- `k = 1`: `(ZMod 2)ˣ = {1}`, trivial group, `1² = 1`, count = `1`.
- `k = 2`: `(ZMod 4)ˣ = {1, 3}`, both `1² = 1` and `3² = 9 = 1` in
  `ZMod 4`, count = `2`.
- `k ≥ 3`: `(ZMod 2^k)ˣ ≅ ⟨-1⟩ × ⟨5⟩` where `⟨-1⟩ ≅ ℤ/2` and
  `⟨5⟩ ≅ ℤ/2^(k-2)`. The 2-torsion in `⟨-1⟩` is the entire factor
  (order 2); the 2-torsion in `⟨5⟩` has size `gcd(2, 2^(k-2)) = 2`
  (since `k ≥ 3` ⇒ `2^(k-2) ≥ 2`). Total 2-torsion size:
  `2 · 2 = 4`.

## 2. Mathlib v4.26.0 readiness

### Structure theorem for `(ZMod 2^k)ˣ`

The key Mathlib lemma is:

```lean
theorem ZMod.unitsZModTwoPowEquiv (k : ℕ) :
    (ZMod (2^k))ˣ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod (2^(k-2)))
```

or a variant. The exact name may be:

- `ZMod.unitsZMod_*` family in `Mathlib.NumberTheory.LucasLehmer`
  or `Mathlib.GroupTheory.SpecificGroups.Cyclic`.
- `ZMod.unitsEquivProdOfCoprime` for general `n = m · k` with `gcd m k = 1`
  (CRT-based, used for the eventual S6).
- Direct structure for `2^k`: may be implicit via
  `ZMod.exp_eq_two_pow_mul_two_pow_sub_two` or similar.

**Status check needed**: at the time of writing, I have NOT confirmed
the exact Mathlib v4.26.0 name. The S4 generic theorem
`card_filter_sq_eq_one_cyclic_even` is **`IsCyclic`-gated** and so
*does not* apply to `k ≥ 3` (where the group is non-cyclic). S5b
must therefore either:

1. **Specialize to `k ≤ 2`** (cyclic cases) via the S4 skeleton, AND
2. **Handle `k ≥ 3`** via direct enumeration or a non-cyclic
   2-torsion-count lemma.

### 2-Torsion count for direct-product groups

For `G ≅ A × B` with both `A` and `B` cyclic of order `2^a`, `2^b`,
the 2-torsion subgroup has order
`gcd(2, 2^a) · gcd(2, 2^b) = (if a ≥ 1 then 2 else 1) · (if b ≥ 1 then 2 else 1)`.

The Mathlib lemma chain to compute this for `(ZMod 2^k)ˣ` once the
isomorphism is in hand:

| Lemma                                              | Role                                                            |
| -------------------------------------------------- | --------------------------------------------------------------- |
| `MulEquiv.card_eq` (or `Fintype.card_congr`)        | transfer cardinality through the structure iso                  |
| `Submonoid.card_prod`                              | `|A × B| = |A| · |B|` for product submonoids                   |
| `IsCyclic.card_orderOf_eq_totient`                 | per-factor 2-torsion size                                      |
| `Nat.totient_prime_pow`                            | `φ(2) = 1`, `φ(2^a) = 2^(a-1)` for `a ≥ 1`                     |

### `IsCyclic` status for the `k ≤ 2` cases

- `k = 1`: `(ZMod 2)ˣ` has order `1`, trivially cyclic
  (`IsCyclic` instance: `Submonoid.bot_isCyclic` or auto-derived
  from the order-1 case).
- `k = 2`: `(ZMod 4)ˣ` has order `2`, cyclic
  (Mathlib has `ZMod.isCyclic_units_of_prime_pow` for `p = 2, k ≤ 2`).

So the S4 generic skeleton applies *directly* for `k = 1, 2` once
the `2 ∣ |G|` hypothesis is established (which fails for `k = 1`!
`|G| = 1` is odd). So:

- `k = 1`: cannot use the S4 even-cardinality skeleton; must
  handle as a direct enumeration case.
- `k = 2`: works through the S4 skeleton (`|G| = 2` is even,
  cyclic, count = `φ(1) + φ(2) = 2`).

## 3. S5b ACT plan

**Recommended Lean structure**: three theorems.

### S5b.1 — `k = 1` enumeration

```lean
theorem card_filter_sq_eq_one_units_zmod_2_one :
    ((Finset.univ : Finset (ZMod 2)ˣ).filter (fun u => u^2 = 1)).card = 1 := by
  decide
```

This is a 1-line proof via `decide` since `(ZMod 2)ˣ` is finite and
the predicate is decidable.

### S5b.2 — `k = 2` via S4 skeleton

```lean
theorem card_filter_sq_eq_one_units_zmod_4 :
    ((Finset.univ : Finset (ZMod 4)ˣ).filter (fun u => u^2 = 1)).card = 2 := by
  -- Apply card_filter_sq_eq_one_cyclic_even with G = (ZMod 4)ˣ:
  --   IsCyclic comes from ZMod.isCyclic_units_of_prime_pow 2 (by norm_num) 2
  --     (after handling the "2 is prime" obligation)
  --   2 ∣ |(ZMod 4)ˣ| = φ(4) = 2 is trivial
  have hcyc : IsCyclic (ZMod 4)ˣ := by
    have := ZMod.isCyclic_units_of_prime_pow 2 (by decide) ?_
    · exact this 2
    · -- p ≠ 2 hypothesis fails! p IS 2 here.
      sorry  -- BLOCKED: ZMod.isCyclic_units_of_prime_pow requires odd p
  ...
```

**Blocker for S5b.2**: `ZMod.isCyclic_units_of_prime_pow` is
**odd-prime-only** (matching the merged S5 ACT's signature). The
`k = 2` case for `p = 2` needs a separate `IsCyclic (ZMod 4)ˣ`
instance.

Two options:

- **Option A**: prove `IsCyclic (ZMod 4)ˣ` directly via `decide` or
  by exhibiting the generator `3 : (ZMod 4)ˣ`.
- **Option B**: use `decide` for the whole `k = 2` count as in
  S5b.1.

**Option B is strictly simpler** — one `decide` instead of an
`IsCyclic` instance + S4 instantiation. Recommended.

### S5b.3 — `k ≥ 3` non-cyclic case

```lean
theorem card_filter_sq_eq_one_units_zmod_two_pow_ge_three (k : ℕ) (hk : 3 ≤ k) :
    ((Finset.univ : Finset (ZMod (2^k))ˣ).filter
      (fun u => u^2 = 1)).card = 4
```

This is the **hardest** sub-iteration. Two sub-options:

- **Option A**: use the Mathlib structure theorem
  `(ZMod 2^k)ˣ ≃* ⟨-1⟩ × ⟨5⟩` (if it exists in v4.26.0). Then
  `2-torsion(⟨-1⟩ × ⟨5⟩) ≅ ⟨-1⟩ × ⟨5^(2^(k-3))⟩`, both ℤ/2, total
  `2 · 2 = 4`.
- **Option B**: enumerate via `decide` for fixed `k = 3, 4, 5, …`
  up to some bound, then handle generic `k ≥ N` via the structure
  theorem.
- **Option C**: prove directly without the structure iso. The
  2-torsion in `(ZMod 2^k)ˣ` is exactly the set of `u` such that
  `2^k ∣ (u - 1)(u + 1) = u² - 1`. By Hensel-style lifting / the
  `v₂` valuation analysis, for `k ≥ 3` the solutions are
  `u ∈ {1, -1, 2^(k-1) ± 1}`, four solutions total. This is
  elementary number theory and may be the cleanest Lean proof.

**Estimated S5b.3 size**: 60–120 Lean lines (depends on which
Option works).

### Combined S5b master theorem

```lean
theorem card_filter_sq_eq_one_units_zmod_two_pow (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (ZMod (2^k))ˣ).filter (fun u => u^2 = 1)).card =
      if k = 1 then 1 else if k = 2 then 2 else 4
```

Or more uniformly:

```lean
theorem card_filter_sq_eq_one_units_zmod_two_pow (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (ZMod (2^k))ˣ).filter (fun u => u^2 = 1)).card =
      2 ^ (min 2 (max 0 (k - 1)))
```

(i.e. `2^0 = 1` for `k = 1`, `2^1 = 2` for `k = 2`, `2^2 = 4` for
`k ≥ 3`). The closed-form is cleaner but harder to prove uniformly;
the case-split form (`if k = 1 then …`) chains the three sub-theorems
above.

## 4. Mathlib API audit checklist for S5b ACT

Before starting S5b ACT, verify these Mathlib v4.26.0 lemmas exist
and have the expected signatures:

- [ ] `ZMod.unitsZMod_*` structure iso for `(ZMod 2^k)ˣ`
  (or absence thereof — Option C in S5b.3 may be required).
- [ ] `Fintype.card_eq_one` for the `k = 1` case (`(ZMod 2)ˣ`
  has unique element).
- [ ] `decide` reduces the `k = 1, 2, 3` cases in reasonable time
  (sub-second for `k ≤ 5`).
- [ ] `Nat.totient_prime_pow` covers `p = 2`, `k ≥ 1` for the
  cardinality `φ(2^k) = 2^(k-1)`.

## 5. Anti-targets (do NOT attempt as S5b)

- ❌ **Don't try to generalize S4's
  `card_filter_sq_eq_one_cyclic_even` to non-cyclic abelian groups.**
  The cyclic hypothesis is essential to the totient-lookup step
  (`φ(1) + φ(2) = 2`); the non-cyclic case has *more* 2-torsion
  elements (Klein-bottle has 4) and the totient identity does not
  generalize.
- ❌ **Don't try to use** the structure iso
  `(ZMod 2^k)ˣ ≃* ℤ/2 × ℤ/2^(k-2)` **without first verifying its
  Mathlib v4.26.0 name + signature.** If absent, Option C
  (elementary number-theoretic enumeration via `u² ≡ 1 (mod 2^k)`)
  is the fallback.
- ❌ **Don't try to ship S5b in a single iteration.** The three
  cases (`k = 1`, `k = 2`, `k ≥ 3`) have different proof strategies
  and should be three separate sub-iterations (S5b.1, S5b.2, S5b.3)
  to keep per-iter risk low.
- ❌ **Don't try to merge** with PR #18230 (S5-prep, build-pending
  since 2026-05-12 18:11 UTC). PR #18230 modifies the same Lean
  file as merged S5 ACT #18233 and likely has merge conflicts.
  S5b should branch off post-#18233 main and start fresh.

## 6. Honest framing

1. **No `lake build` performed.** Mathlib lemma names
   (`ZMod.unitsZMod_*`, `Fintype.card_eq_one`, etc.) are
   cross-referenced from `Mathlib.NumberTheory.LucasLehmer`,
   `Mathlib.GroupTheory.SpecificGroups.Cyclic`, and the existing
   merged S5 file. Whoever picks up S5b should `lake env lean`
   -probe each lemma.
2. **The `k ≥ 3` case** (S5b.3) is the dominant work and is **not
   written out**. Both Option A (structure iso) and Option C
   (elementary number theory) are sketched at the strategic level
   only.
3. **The state.md parenthetical** `(k = 1, 2, ≥ 3 give 2, 2, 4)`
   should be corrected to `1, 2, 4`. This correction should be
   bundled into the S5b state.md update, not done as a separate
   PR.
4. **The S6 CRT multiplicativity step** assumes the per-prime-power
   counts are determined; this OBSERVE doc handles only the
   per-prime-power side at `p = 2`. The CRT step is independent
   work.

## 7. Compatibility with open PRs

- **#18230 (S5-prep, build-pending 2026-05-12)**: likely conflicting
  with merged S5 ACT #18233 (both touch
  `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`). This PR does NOT
  touch that Lean file; conflict-free.
- This PR's branch is `research/gauss-wilson-nc-oq03-s5b-prep-*`,
  distinct from `research/gauss-wilson-non-cyclic-oq-03-s5-prep-…`
  and `research/gauss-wilson-non-cyclic-oq-03-s5-…`.

## 8. Done When (this OBSERVE session)

- [x] Correct counts `(1, 2, 4)` for `k = (1, 2, ≥3)` verified
  against structure of `(ZMod 2^k)ˣ`.
- [x] Three sub-iterations (S5b.1 / S5b.2 / S5b.3) proposed with
  Lean signatures.
- [x] Mathlib API audit checklist enumerated.
- [x] Anti-targets listed.
- [x] state.md typo identified for bundling into S5b state-update.
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  or research JSON.

## 9. No-edit guarantee

This PR touches **only**:

```
research/problems/gauss-wilson-non-cyclic-oq-03/sessions/
    2026-05-12-s5b-observe-even-prime-case.md
```

No existing file is modified.

## References

- Gauss, *Disquisitiones Arithmeticae* (1801), §92 (the
  non-cyclicity of `(ℤ/2^k)ˣ` for `k ≥ 3`).
- Lang, *Algebra* (3rd ed.), Ch. II §1 (structure of
  `(ℤ/n)ˣ`).
- Mathlib: `Mathlib.NumberTheory.LucasLehmer`,
  `Mathlib.GroupTheory.SpecificGroups.Cyclic`,
  `Mathlib.Data.ZMod.Basic`.
- Merged: PR #18072 (S4-prep), PR #18125 (S4),
  PR #18233 (S5 ACT).
- Open (likely-conflicting): PR #18230 (S5-prep).
