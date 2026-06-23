# S5b.3 ACT — `(ZMod 2^k)ˣ` has exactly 4 square roots of unity for `k ≥ 3`

**Slug**: `gauss-wilson-non-cyclic-oq-03`
**Iteration**: S5b.3 (ACT)
**Date**: 2026-06-12
**Researcher**: researcher-2
**Phase**: ACT
**Build**: Docker-verified (`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ03`, exit 0)

## 1. Summary

Closed the **structural even-prime per-prime-power count** — the last of
the three `p = 2` cases and the `ε₂(n) = 2` leg of the two-adic
correction:

> For `k ≥ 3`, `#{u : (ZMod 2^k)ˣ | u² = 1} = 4`.

New `Section 9` in `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`
(396 → 584 lines), two theorems, **0 new sorries, 0 axioms**.

This completes every per-prime-power unit-side count consumed by the
deferred S6 CRT-multiplicativity step:

| Prime power | Theorem | Count |
| ----------- | ------- | ----- |
| odd `p^k`   | `card_filter_sq_eq_one_units_zmod_prime_pow_odd` (S5)  | 2 |
| `2^1`       | `card_filter_sq_eq_one_units_zmod_two` (S5b.1)         | 1 |
| `2^2`       | `card_filter_sq_eq_one_units_zmod_four` (S5b.2)        | 2 |
| `2^k, k≥3`  | `card_filter_sq_eq_one_units_zmod_two_pow_ge_three` (S5b.3) | 4 |

## 2. Deviation from the S5b PREP design

The S5b PREP `#18648` §3.3 proposed proving S5b.3 by an explicit
**generator cardinality-squeeze**: lift `5` and `−1` to units, use
`ZMod.orderOf_five` (`orderOf 5 = 2^(k-2)`), establish the unique
representation `u = (−1)^a · 5^b`, and count `(−1)^a 5^b` solutions of
`u² = 1`. That route mirrors `Carmichael.lean:135-148`.

**This session took a different, more elementary route** that turned out
to be self-contained and avoided all `orderOf_five` / generator
plumbing:

1. **Reduce to the ring side** via the already-merged S3 bridge
   `card_sqrts_one_eq_card_units_sqrts_one (2^k)`:
   `#{u : (ZMod 2^k)ˣ | u²=1} = #{x : ZMod 2^k | x²=1}`.

2. **Count on the ring** by showing the filter equals the image under
   `Nat.cast` of the four explicit naturals
   `S = {1, 2^(k-1)-1, 2^(k-1)+1, 2^k-1}` (all `< 2^k`):
   * **`⊇`** (each is a root): set `t := (2 : ZMod 2^k)^(k-1)`. From
     `(2:ZMod 2^k)^k = 0` (`ZMod.natCast_self` + `push_cast`) one gets
     `t² = 0` (since `2(k-1) = k + (k-2)`) and `2t = 0` (since
     `2·2^(k-1) = 2^k`). Then `(t±1)² = t² ± 2t + 1 = 1`, and the
     `±1` roots are immediate. Cast bridges `e1/e2/e3` relate the
     natural roots to `t-1`, `t+1`, `-1`.
   * **`⊆`** (no other roots): for `x` with `x²=1`, push to
     `x.val² ≡ 1 [MOD 2^k]`, i.e. `2^k ∣ x.val² - 1`; `x.val` is odd
     (else `x.val²-1` is odd, not divisible by `2^k`). The new helper
     `two_pow_dvd_split` then gives `2^(k-1) ∣ x.val ∓ 1`, and the
     bound `x.val < 2^k` forces `x.val ∈ S` (two multiples of `2^(k-1)`
     in each of the two ranges).

3. **Cardinality**: `Nat.cast` is injective on `[0, 2^k)`
   (`ZMod.natCast_eq_natCast_iff` + `Nat.mod_eq_of_lt`), and the four
   naturals are pairwise distinct (`omega` from `4 ≤ 2^(k-1)` and
   `2^k = 2·2^(k-1)`), so `card = 4`.

### Why the deviation

The PREP itself flagged (§2.1) that Mathlib `v4.26.0` has **no**
`MulEquiv`-form structure iso for `(ZMod 2^k)ˣ`. The generator route
needs the unique-representation lemma built by hand. The
divisibility route needs only the elementary fact that two consecutive
even numbers share exactly one factor of `2` — encoded in
`two_pow_dvd_split` via `m, m+1` coprime and `2^(k-2)` a prime power.
Net: ~150 LOC of `omega`/`push_cast`/`Nat.Coprime` rather than
`orderOf_five` + `orderOf_units` + generator bookkeeping. Both are
valid; this one happened to land first and is Mathlib-version-robust.

## 3. The number-theoretic core (`two_pow_dvd_split`)

```
private theorem two_pow_dvd_split (k : ℕ) (hk : 2 ≤ k) {a : ℕ}
    (hodd : Odd a) (hdvd : 2 ^ k ∣ a ^ 2 - 1) :
    2 ^ (k - 1) ∣ a - 1 ∨ 2 ^ (k - 1) ∣ a + 1
```

`a = 2m+1 ⟹ a²-1 = 4·m·(m+1) ⟹ 2^(k-2) ∣ m(m+1)`. Case-split on the
parity of `m`: the even factor (one of `m`, `m+1`) is coprime to nothing
shared with `2^(k-2)`, so by `Nat.Coprime.dvd_of_dvd_mul_{left,right}`
the whole `2^(k-2)` lands on it; multiplying by the `2` from
`a∓1 = 2·(even factor)` yields `2^(k-1)`.

This is the reusable arithmetic fact; it is independent of `ZMod` and
could be hoisted if a later session wants the analogous odd-prime
"Hensel" count, though the odd case is already handled cyclically (S5).

## 4. Build / honesty

- **Docker-verified**: `docker-build.sh Proofs.GaussWilsonNonCyclicOQ03`
  → `Build completed successfully (3062 jobs)`, the OQ03 file built in
  15s. The only `sorry` warning is the pre-existing main theorem
  `card_sqrts_one_eq_numSqrtsOne` (line 131), untouched.
- **0 axioms, 0 structure-encoded assumptions** added. The two new
  theorems are unconditional (given `k ≥ 3` / `k ≥ 2` and the ambient
  `NeZero (2^k)`).
- Iteration history: first Docker build surfaced 5 fixable issues
  (`pow_succ'` orientation mismatch → `mul_comm`+`pow_succ`; missing
  `Fact (1 < 2^k)` for `0 ≠ 1`; nonexistent `Nat.odd_pow` → explicit
  even/odd case split; a multiline-`rw` parse glitch → extracted
  `have`s). Second build clean. The split lemma compiled on the first
  attempt.

## 5. Next

- **S6 ACT (CRT multiplicativity)** is now fully unblocked: all four
  per-prime-power counts are proved theorems. Design in S6 PREP `#18423`.
- **S7 ACT (induction assembly)** closes the main-theorem sorry.

---

🤖 Generated by researcher-2
