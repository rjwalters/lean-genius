# Knowledge Base: gauss-wilson-non-cyclic-oq-02

**Question.** Does the 2-torsion bound extend to characterize when the Sylow
2-subgroup of `(ZMod n)ˣ` is *elementary abelian* versus *cyclic*?

---

## Problem Understanding

The parent entry `gauss-wilson-non-cyclic` proves the qualitative fact that for
`n ≥ 3`, `¬IsCyclic (ZMod n)ˣ → ∃ x, x² = 1 ∧ x ≠ ±1` (the 2-torsion subgroup
has order `≥ 3`, i.e. 2-rank `≥ 2`). Sibling `OQ-03` upgrades this to the exact
**count** of square roots of unity,
`#{x : x² = 1} = 2 ^ (ω_odd(n) + ε₂(n))`, which is exactly `2 ^ rank₂(S₂)`.

OQ-02 asks a **different** invariant: not the rank/order of the Sylow
2-subgroup `S₂ := Syl₂((ZMod n)ˣ)`, but its full isomorphism type — specifically
the two boundary cases *cyclic* (rank `≤ 1`) and *elementary abelian*
(exponent `≤ 2`). The count formula of OQ-03 determines the rank but **not** the
exponent, so OQ-02 is not subsumed by OQ-03.

## Resolution (on paper — complete)

By CRT, writing `n = 2^a · ∏ pᵢ^{eᵢ}` with the `pᵢ` distinct odd primes:

```
  (ZMod n)ˣ  ≅  (ZMod 2^a)ˣ × ∏ᵢ (ZMod pᵢ^{eᵢ})ˣ
```

Each odd factor `(ZMod pᵢ^{eᵢ})ˣ` is **cyclic** of order `pᵢ^{eᵢ-1}(pᵢ-1)`; its
Sylow 2-subgroup is cyclic of order `2^{v₂(pᵢ-1)}` (the `pᵢ^{eᵢ-1}` part is odd),
and `v₂(pᵢ-1) ≥ 1` always (odd prime ⇒ `pᵢ-1` even). The 2-part:
`(ZMod 2^a)ˣ` is trivial (`a≤1`), `≅ C₂` (`a=2`), or `≅ C₂ × C_{2^{a-2}}`
(`a≥3`). Hence the Sylow 2-subgroup of the whole group is

```
  S₂(n)  ≅  D(a)  ×  ∏_{odd p | n} C_{2^{v₂(p-1)}},
  where D(a) = 1 (a≤1),  C₂ (a=2),  C₂ × C_{2^{a-2}} (a≥3).
```

This is a finite abelian 2-group, a product of cyclic 2-groups. From it both
boundary characterizations drop out:

- **`S₂(n)` cyclic** ⟺ at most one nontrivial cyclic factor ⟺ `rank₂ ≤ 1`
  ⟺ `ω_odd(n) + ε₂(n) ≤ 1` ⟺ `n ∈ {1, 2, 4, p^k, 2p^k}` (p odd prime).
  Equivalently: **`S₂(n)` is cyclic ⟺ `(ZMod n)ˣ` is itself cyclic.** (The
  reason is that `rank₂ ≤ 1` already forces `n` into the cyclic-classification
  forms, so the odd parts cannot collide either.) This recovers
  `ZMod.isCyclic_units_iff`.

- **`S₂(n)` elementary abelian** ⟺ every cyclic factor has order `2`
  ⟺ `v₂(p-1) = 1` for every odd `p | n` **and** `a ≤ 3`
  ⟺ **every odd prime divisor of `n` is `≡ 3 (mod 4)` and `v₂(n) ≤ 3`.**
  (`a = 3` gives `(ZMod 8)ˣ ≅ C₂ × C₂`, still exponent 2; `a ≥ 4` introduces a
  `C_{2^{a-2}}` with `a-2 ≥ 2`, breaking exponent 2.)

So the answer to OQ-02 is **yes**: the 2-torsion analysis extends to a complete
characterization, and "elementary abelian vs cyclic" are the two extreme shapes
of the general structure formula above. The two coincide (`S₂ ∈ {1, C₂}`)
exactly when `rank₂ ≤ 1` and exponent `≤ 2`.

### Numerical cross-checks (consistent with OQ-03 count = 2^rank)

| n   | factor form        | S₂                | rank | #sqrts | cyclic? | elem.ab.? |
|-----|--------------------|-------------------|------|--------|---------|-----------|
| 8   | 2³                 | C₂×C₂             | 2    | 4      | no      | yes       |
| 16  | 2⁴                 | C₂×C₄             | 2    | 4      | no      | no        |
| 12  | 4·3                | C₂×C₂             | 2    | 4      | no      | yes       |
| 15  | 3·5                | C₂×C₄ (5≡1 mod4)  | 2    | 4      | no      | no        |
| 21  | 3·7                | C₂×C₂             | 2    | 4      | no      | yes       |
| 7   | 7                  | C₂                | 1    | 2      | yes     | yes       |

All `#sqrts = 2^rank` match OQ-03's formula; the `elem.ab.?` column is the new
exponent information OQ-02 adds (note 8 vs 16 and 21 vs 15 differ in exponent at
equal rank).

## Mathlib API inventory (for ACT)

- `ZMod.isCyclic_units_iff` — exact cyclic classification (already used by the
  parent file); directly closes the **cyclic** half.
- `ZMod.chineseRemainder` — CRT ring iso (already used by the parent file).
- Units of odd prime powers cyclic: lemmas in
  `Mathlib.RingTheory.ZMod.UnitsCyclic` (parent imports this).
- **Gap to confirm during ACT:** an explicit Mathlib iso for `(ZMod (2^a))ˣ ≅
  C₂ × C_{2^{a-2}}` (`a ≥ 3`). If absent, this is the one piece to build
  (~80–150 lines; the `5`-generates-the-`2^{a-2}`-part is the classical lemma).
  Without it the *elementary-abelian* direction can still be obtained via the
  `x² = 1` square-root count combined with an exponent computation, but the
  clean structural statement wants the iso.

## Next Steps

1. State two Lean theorems in a new `GaussWilsonNonCyclicOQ02.lean`:
   `s2_cyclic_iff` (Sylow-2 cyclic ↔ `IsCyclic (ZMod n)ˣ`) and
   `s2_elementaryAbelian_iff` ((∀ x in S₂, x²=1) ↔ every odd prime `p ∣ n` has
   `p % 4 = 3` and `n.factorization 2 ≤ 3`).
2. Reuse the CRT decomposition machinery already present in the parent file.
3. Build/locate the `(ZMod 2^a)ˣ` structure lemma (the only likely Mathlib gap).

**Status:** SURVEYED / ORIENT. Core mathematics resolved on paper; formalization
is build-gated (Docker + Aristotle both down 2026-06-13). No Lean written this
session — verification infra unavailable.

---

## Insights

- OQ-02 (exponent / iso-type of `S₂`) is genuinely independent of OQ-03
  (rank / square-root count): equal rank can carry different exponent
  (`n=8` vs `n=16`).
- `S₂` cyclic ⟺ `(ZMod n)ˣ` cyclic — the Sylow-2 shape alone already detects
  the global cyclic classification, because rank `≤ 1` forces `n ∈ {1,2,4,p^k,2p^k}`.
- The elementary-abelian condition is the conjunction of a per-odd-prime
  congruence (`p ≡ 3 mod 4`) and a 2-adic cap (`v₂(n) ≤ 3`).

## Dead Ends

- Trying to read the cyclic/elementary-abelian distinction off OQ-03's count
  formula alone — impossible, since the count is `2^rank` and is blind to the
  exponent (compare `n=8`: C₂×C₂ vs `n=16`: C₂×C₄, both rank 2, count 4).
