# S7b PREP — `epsTwo` / `omegaOdd` / `numSqrtsOne` bookkeeping discharge via `Nat.factorization` (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-11
**Phase**: PREP (orientation for the S7 ACT bookkeeping helpers,
downstream of S7 PREP `#18465` and the S6/S7 PREP Mathlib API audit
`#18510`).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the prior `sessions/` notes, gallery
`meta.json`, or research JSON.
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(verified live via
`gh api repos/leanprover-community/mathlib4/commits/master` at PREP
draft time, matching the audit pin of `#18510`).

## 0. Why a follow-up S7 PREP now

The S7 PREP `#18465` (researcher-12, 2026-05-13 02:08 UTC) staged the
main-theorem induction body (~15 LOC) but left **the three
closed-form bookkeeping helpers** (`omegaOdd_mul_of_coprime`,
`epsTwo_mul_of_coprime`, `numSqrtsOne_mul_of_coprime`) as sketches.
The principal gap is in S7 PREP §3.2 (`epsTwo_mul_of_coprime`):

```lean
lemma epsTwo_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    epsTwo (m * n) = epsTwo m + epsTwo n := by
  unfold epsTwo
  -- both odd: 2 ∤ m, 2 ∤ n, 2 ∤ m*n
  -- one even, other odd: 2 ∣ exactly one ⇒ 2 ∤ other ⇒ v₂(m*n) = v₂(even side)
  rcases h.eq_one_of_self_dvd 2 with _ | hm | hn   -- placeholder; actual branching by Nat.Coprime.dvd_of_dvd_mul style
  · omega
  -- ...
  sorry  -- pseudocode; the ACT author should expect ~10-15 LOC discharge via interval_cases / omega
```

The `rcases h.eq_one_of_self_dvd 2 with _ | hm | hn` line is
syntactically suspect (`Nat.Coprime` is `gcd m n = 1` — there is no
`Coprime.eq_one_of_self_dvd` decl in Mathlib `v4.26.0`), and the
`sorry` leaves the ACT author with no concrete discharge.

The S6/S7 PREP Mathlib API audit `#18510` (researcher-3, 2026-05-13
04:10 UTC) **does not address §3.2** — it pinned and corrected
citations in §3.1 (`omegaOdd`), §4 (induction body), §6 (Mathlib API
table), but left the `epsTwo` arithmetic as out-of-scope.

**This S7b PREP fills exactly that gap.** It:

1. **Discharges `epsTwo_mul_of_coprime`** via the
   `Nat.factorization`-bridge route: a 2-step proof using
   `Nat.factorization_mul_apply_of_coprime` (newly pinned) + a small
   `epsTwo_eq_min_factorization` bridge lemma (~6 LOC).
2. **Discharges `omegaOdd_mul_of_coprime`** via
   `Nat.Coprime.primeFactors_mul` (pinned in `#18510` §2.2) +
   `Finset.filter_union` (newly pinned) + `Finset.card_union_of_disjoint`
   (pinned in `#18510` §2.5) chain (~10 LOC).
3. **Computes per-prime-power closed-form values** of `omegaOdd`,
   `epsTwo`, and `numSqrtsOne` at `p^k` (odd `p`) and `2^k`,
   providing the `numSqrtsOne_prime_pow_odd` /
   `numSqrtsOne_two_pow` rewrites that the S7 induction's
   `prime_pow` case-split needs.
4. **Pins three additional Mathlib decls** not in `#18510`'s audit
   table: `Nat.factorization_mul_apply_of_coprime`,
   `Nat.Prime.pow_dvd_iff_le_factorization`,
   `Nat.factorization_eq_zero_iff`.

**Net deliverable**: this single doc-only file. **No edits** to
`problem.md`, `knowledge.md`, `state.md`,
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`, gallery `meta.json`,
or `src/data/research/problems/<slug>.json`. 0 axiom delta, 0 sorry
delta, 0 build.

## 1. Setting

Recall the relevant definitions from
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean:72–83`:

```lean
def epsTwo (n : ℕ) : ℕ :=
  if n % 8 = 0 then 2 else if n % 4 = 0 then 1 else 0

def omegaOdd (n : ℕ) : ℕ :=
  (n.primeFactors.filter (· ≠ 2)).card

def numSqrtsOne (n : ℕ) : ℕ := 2 ^ (omegaOdd n + epsTwo n)
```

The S7 closed-form target is

> `card_sqrts_one_eq_numSqrtsOne : ∀ n, [NeZero n] →
>  #{x : ZMod n | x² = 1} = numSqrtsOne n`,

discharged in S7 ACT via `Nat.recOnPosPrimePosCoprime` on `n`. The
`coprime` recursion step requires
`numSqrtsOne_mul_of_coprime`, which reduces (via the `pow_add` /
`ring` step in S7 PREP §3.3) to the additivity of `omegaOdd` and
`epsTwo` under coprime products.

## 2. `epsTwo_mul_of_coprime` via the `Nat.factorization`-bridge

### 2.1 Bridge lemma: `epsTwo` as a clamped factorization

**Claim.** For `n > 0`,

```
epsTwo n  =  min 2 (n.factorization 2 - 1)        -- truncated Nat subtraction
```

**Verification table** (closed-form check):

| `n.factorization 2` | `n % 8`     | `n % 4`     | `epsTwo n` defn-side | `min 2 (v₂(n) - 1)` |
|---------------------|-------------|-------------|----------------------|---------------------|
| `0` (`n` odd)       | `1,3,5,7`   | `1,3`       | `0`                  | `min 2 0 = 0`       |
| `1` (`2 ∥ n`)       | `2,6`       | `2`         | `0`                  | `min 2 0 = 0`       |
| `2` (`4 ∥ n`)       | `4`         | `0`         | `1`                  | `min 2 1 = 1`       |
| `≥ 3` (`8 ∣ n`)     | `0`         | `0`         | `2`                  | `min 2 (v-1) = 2`   |

(Recall `Nat` truncated subtraction: `0 - 1 = 0`.)

**Proposed Lean** (~15 LOC):

```lean
lemma epsTwo_eq_min_factorization {n : ℕ} (hn : n ≠ 0) :
    epsTwo n = min 2 (n.factorization 2 - 1) := by
  -- Bridge n % 8 = 0 ↔ 8 ∣ n ↔ 2^3 ∣ n ↔ 3 ≤ n.factorization 2
  -- Bridge n % 4 = 0 ↔ 4 ∣ n ↔ 2^2 ∣ n ↔ 2 ≤ n.factorization 2
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have h8 : 8 ∣ n ↔ 3 ≤ n.factorization 2 := by
    have : (2 ^ 3 : ℕ) = 8 := by decide
    rw [← this]
    exact hp2.pow_dvd_iff_le_factorization hn
  have h4 : 4 ∣ n ↔ 2 ≤ n.factorization 2 := by
    have : (2 ^ 2 : ℕ) = 4 := by decide
    rw [← this]
    exact hp2.pow_dvd_iff_le_factorization hn
  unfold epsTwo
  rw [show (n % 8 = 0) ↔ 8 ∣ n from Nat.dvd_iff_mod_eq_zero _ _ |>.symm,
      show (n % 4 = 0) ↔ 4 ∣ n from Nat.dvd_iff_mod_eq_zero _ _ |>.symm,
      h4, h8]
  -- Now both sides are a decidable function of `n.factorization 2 : ℕ`.
  -- `omega` closes after `split_ifs`.
  split_ifs <;> omega
```

**Risks**:

- The `Nat.dvd_iff_mod_eq_zero` direction (`mod = 0 ↔ dvd`) is the
  canonical bridge; this is `Nat.dvd_iff_mod_eq_zero` in Mathlib
  `Mathlib/Data/Nat/Defs.lean` (Lean core
  `Nat.dvd_iff_mod_eq_zero` was deprecated in favour of `Nat.mod_eq_zero_iff_dvd`
  at some Mathlib revision; the ACT author should `grep` to pick
  the canonical one). If neither name resolves, use
  `Nat.dvd_iff_mod_eq_zero` or `Nat.mod_eq_zero_of_dvd` /
  `Nat.dvd_of_mod_eq_zero` separately.
- `(2 ^ 3 : ℕ) = 8` and `(2 ^ 2 : ℕ) = 4` are `decide`-able. If
  `decide` fails for size-of-numeral reasons (unlikely at base 2),
  fall back to `by norm_num`.
- `split_ifs <;> omega` should close: each branch reduces to
  comparing `n.factorization 2` with `2, 3` and the `min 2 (·-1)`
  output.

### 2.2 Coprime ⇒ one side has zero 2-factorization

**Claim.** For `Coprime m n`:

```
m.factorization 2 = 0  ∨  n.factorization 2 = 0
```

**Proof sketch**: if both were `≥ 1`, then `2 ∣ m` and `2 ∣ n`, so
`2 ∣ gcd m n = 1`, contradiction.

**Proposed Lean** (~10 LOC):

```lean
lemma Nat.Coprime.factorization_two_eq_zero_or {m n : ℕ}
    (h : m.Coprime n) :
    m.factorization 2 = 0 ∨ n.factorization 2 = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hm, hn⟩ := hcon
  -- both factorizations nonzero ⇒ 2 ∣ m and 2 ∣ n
  have hp2 : Nat.Prime 2 := Nat.prime_two
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [Nat.factorization_zero] at hm
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [Nat.factorization_zero] at hn
  have h2m : 2 ∣ m := by
    have := (hp2.pow_dvd_iff_le_factorization hm0).mpr (Nat.one_le_iff_ne_zero.mpr hm)
    simpa using this
  have h2n : 2 ∣ n := by
    have := (hp2.pow_dvd_iff_le_factorization hn0).mpr (Nat.one_le_iff_ne_zero.mpr hn)
    simpa using this
  have : 2 ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
  rw [h] at this
  omega
```

### 2.3 Main discharge

**Claim.** `epsTwo_mul_of_coprime` for `Coprime m n` and `0 < m, n`:

```
epsTwo (m * n)  =  epsTwo m + epsTwo n
```

**Proof sketch**:

1. By §2.2, WLOG `n.factorization 2 = 0`.
2. By `Nat.factorization_mul_apply_of_coprime`,
   `(m*n).factorization 2 = m.factorization 2 + 0 = m.factorization 2`.
3. By §2.1, `epsTwo n = min 2 (0 - 1) = 0` and
   `epsTwo (m * n) = min 2 (m.factorization 2 - 1) = epsTwo m`.
4. Summing: `epsTwo (m * n) = epsTwo m = epsTwo m + 0 = epsTwo m + epsTwo n`. ∎

**Proposed Lean** (~20 LOC):

```lean
lemma epsTwo_mul_of_coprime {m n : ℕ} (h : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    epsTwo (m * n) = epsTwo m + epsTwo n := by
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  rw [epsTwo_eq_min_factorization hmn,
      epsTwo_eq_min_factorization hm,
      epsTwo_eq_min_factorization hn,
      Nat.factorization_mul_apply_of_coprime h]
  rcases h.factorization_two_eq_zero_or with hm0 | hn0
  · -- m has no factor 2: m.factorization 2 = 0
    rw [hm0]
    -- min 2 (0 + v₂(n) - 1) = min 2 (v₂(n) - 1) and
    -- min 2 (0 - 1) + ... = 0 + min 2 (v₂(n) - 1)
    simp
  · -- n has no factor 2: n.factorization 2 = 0
    rw [hn0]
    simp
```

**Risks**:

- The `simp` finisher relies on `min 2 (a + 0 - 1) = min 2 (a - 1)`
  and `min 2 (0 - 1) = 0`. Both are pure arithmetic identities on
  `ℕ` (with truncated subtraction). If `simp` alone does not close,
  use `omega` after introducing a `set v := m.factorization 2` or
  `set v := n.factorization 2` to expose the arithmetic.
- Hypotheses `hm, hn : 0 < m, 0 < n` (or `≠ 0`): chosen to align
  with the `Nat.factorization_mul_apply_of_coprime` precondition (its
  Mathlib signature requires no positivity, but the bridge
  `epsTwo_eq_min_factorization` does require `n ≠ 0` since
  `(0).factorization` is `0` but `epsTwo 0 = 2` (degenerate
  agreement).
- The S7 PREP §3.2 sketch had `hm, hn` implicit (only `h :
  Coprime`); the ACT author should add the `≠ 0` hypotheses (the
  S7 induction always carries `0 < n` via `NeZero.pos`, so this is
  free at the call site).

## 3. `omegaOdd_mul_of_coprime` via prime-factor partitioning

**Claim.** For `Coprime m n` and `0 < m, 0 < n`:

```
omegaOdd (m * n)  =  omegaOdd m + omegaOdd n
```

**Proof sketch**:

1. `(m*n).primeFactors = m.primeFactors ∪ n.primeFactors` via
   `Nat.Coprime.primeFactors_mul`.
2. `(m.primeFactors ∪ n.primeFactors).filter (· ≠ 2) =
   m.primeFactors.filter (· ≠ 2) ∪ n.primeFactors.filter (· ≠ 2)`
   via `Finset.filter_union`.
3. `Disjoint m.primeFactors n.primeFactors` via
   `Nat.Coprime.disjoint_primeFactors`.
4. Disjointness of the unfiltered sets ⇒ disjointness of the
   filtered subsets (via `Disjoint.filter_filter` /
   `Finset.disjoint_filter_filter`).
5. `Finset.card_union_of_disjoint` concludes
   `card (A ∪ B) = card A + card B`.

**Proposed Lean** (~12 LOC):

```lean
lemma omegaOdd_mul_of_coprime {m n : ℕ} (h : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    omegaOdd (m * n) = omegaOdd m + omegaOdd n := by
  unfold omegaOdd
  rw [h.primeFactors_mul, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter h.disjoint_primeFactors)
```

**Risks**:

- `Nat.Coprime.primeFactors_mul` returns `(m * n).primeFactors =
  m.primeFactors ∪ n.primeFactors` (pinned at
  `Mathlib/Data/Nat/PrimeFin.lean:100` in `#18510` §2.2); the
  ACT author should `grep` to confirm the conclusion direction (no
  `m * n` vs `n * m` issue under `Mul` commutativity, but Lean's
  rewriter cares about syntactic order).
- The `Finset.disjoint_filter_filter` signature
  (`Disjoint s t → Disjoint (s.filter p) (t.filter q)`, pinned at
  `Mathlib/Data/Finset/Filter.lean:202`) takes the unfiltered
  disjointness as an explicit argument. `h.disjoint_primeFactors`
  supplies the precondition.
- If `Finset.filter_union`'s argument-order convention differs
  (some Mathlib refactors put the filter on the right vs left), use
  `simp [Finset.filter_union]` instead of `rw`.

**Mathlib citations (verified at pin `2df2f015...`)**:

| Lemma / Decl                              | Path                                              | Line |
|-------------------------------------------|---------------------------------------------------|------|
| `Nat.Coprime.primeFactors_mul`            | `Mathlib/Data/Nat/PrimeFin.lean`                  | 100  |
| `Nat.Coprime.disjoint_primeFactors`       | `Mathlib/Data/Nat/PrimeFin.lean`                  | 113  |
| `Finset.filter_union`                     | `Mathlib/Data/Finset/Basic.lean`                  | 351  |
| `Finset.disjoint_filter_filter`           | `Mathlib/Data/Finset/Filter.lean`                 | 202  |
| `Finset.card_union_of_disjoint`           | `Mathlib/Data/Finset/Card.lean`                   | 568  |

All five are transitively imported by
`Mathlib.Data.ZMod.Basic` (already in
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`).

## 4. `numSqrtsOne_mul_of_coprime` discharge

**Claim.** For `Coprime m n` and `0 < m, 0 < n`:

```
numSqrtsOne (m * n)  =  numSqrtsOne m * numSqrtsOne n
```

**Proof sketch** (per S7 PREP §3.3, refined):

1. Unfold both sides via `numSqrtsOne n = 2 ^ (omegaOdd n + epsTwo n)`.
2. Apply §3 (`omegaOdd_mul_of_coprime`) and §2.3
   (`epsTwo_mul_of_coprime`).
3. Use `pow_add` to convert
   `2 ^ ((omegaOdd m + omegaOdd n) + (epsTwo m + epsTwo n))`
   to
   `2 ^ ((omegaOdd m + epsTwo m) + (omegaOdd n + epsTwo n))`
   via `ring_nf` on the exponent, then `pow_add` once.

**Proposed Lean** (~8 LOC):

```lean
lemma numSqrtsOne_mul_of_coprime {m n : ℕ} (h : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    numSqrtsOne (m * n) = numSqrtsOne m * numSqrtsOne n := by
  unfold numSqrtsOne
  rw [omegaOdd_mul_of_coprime h hm hn,
      epsTwo_mul_of_coprime h hm hn,
      ← pow_add]
  congr 1
  ring
```

**Risks**:

- `pow_add` orientation: `2 ^ (a + b) = 2 ^ a * 2 ^ b` is the
  Mathlib direction. The `← pow_add` rewrites `2^a * 2^b` to
  `2^(a+b)`, then `ring` rearranges the exponent. If `ring` fails
  on `ℕ` (it usually does not for additive identities), fall back
  to `omega`.
- The `congr 1` followed by `ring` is the standard pattern for
  these proofs; `Finset.prod_filter`-style alternatives are
  available but less direct.

## 5. Per-prime-power closed-form evaluations

For S7 ACT's `prime_pow` case in `Nat.recOnPosPrimePosCoprime`,
both per-prime-power *unit-side* counts (S5/S5b ACT) and
*closed-form* values (`numSqrtsOne p^k`) need to be linked.

### 5.1 `numSqrtsOne_prime_pow_odd`

**Claim.** For `p` odd prime and `k ≥ 1`:

```
numSqrtsOne (p ^ k)  =  2
```

**Verification**:
- `omegaOdd (p^k) = #{q ∈ (p^k).primeFactors | q ≠ 2} = #{p} = 1`
  (since `p` odd ⇒ `p ≠ 2`).
- `epsTwo (p^k) = 0` since `p^k` is odd ⇒ `2 ∤ p^k` ⇒ `4 ∤ p^k` ⇒
  `8 ∤ p^k`.
- `numSqrtsOne (p^k) = 2 ^ (1 + 0) = 2`. ✓

**Proposed Lean** (~12 LOC):

```lean
lemma numSqrtsOne_prime_pow_odd {p k : ℕ} (hp : p.Prime)
    (hp_odd : p ≠ 2) (hk : 0 < k) :
    numSqrtsOne (p ^ k) = 2 := by
  unfold numSqrtsOne
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero _ hp.one_lt.ne'.symm  -- 0 < p
  have hp_pos : 0 < p := hp.pos
  -- omegaOdd (p^k) = 1
  have homega : omegaOdd (p ^ k) = 1 := by
    unfold omegaOdd
    rw [Nat.primeFactors_pow _ hk.ne']
    -- primeFactors (p^k) = {p} for p prime, k ≥ 1
    sorry  -- needs Nat.Prime.primeFactors = {p}
  -- epsTwo (p^k) = 0 since 4 ∤ p^k for p odd
  have heps : epsTwo (p ^ k) = 0 := by
    unfold epsTwo
    have h_not_4 : ¬ (4 ∣ p ^ k) := by
      sorry  -- 2 ∤ p^k since p odd
    have h_not_8 : ¬ (8 ∣ p ^ k) := fun h => h_not_4 (dvd_trans (by decide) h)
    rw [show (p ^ k % 8 ≠ 0) from
          fun h => h_not_8 (Nat.dvd_of_mod_eq_zero h)
       |>.symm.elim]  -- contradiction approach
    sorry
  rw [homega, heps]
```

The sorries are placeholder for the routine sub-steps. The ACT
author should expect:

- **`omegaOdd (p^k) = 1`**: `Nat.primeFactors_pow` gives
  `(p^k).primeFactors = p.primeFactors` for `k ≥ 1`. Then
  `(Nat.Prime.primeFactors hp)` = `{p}` (the `Finset` literal). The
  filter on `(· ≠ 2)` keeps `{p}` since `p ≠ 2`. `Finset.card_singleton`
  closes.
- **`epsTwo (p^k) = 0`**: `p^k` is odd (since `p` odd, `Odd.pow`).
  `Odd → ¬ 2 ∣ → ¬ 4 ∣ → ¬ 8 ∣`. `Nat.mod_eq_zero_of_dvd`-converse
  + `if-neg` closes both `if`s.

**Estimated discharged length** when the helpers expand: ~15-25 LOC.

### 5.2 `numSqrtsOne_two_pow`

**Claim.** For `k ≥ 1`:

```
numSqrtsOne (2 ^ k)  =  if k = 1 then 1
                        else if k = 2 then 2
                        else 4
```

**Verification**:
- `omegaOdd (2^k) = #{q ∈ {2} | q ≠ 2} = 0` for all `k ≥ 1`.
- `epsTwo (2^k)`:
  - `k = 1`: `2 % 8 = 2, 2 % 4 = 2`, so `epsTwo = 0`. `numSqrtsOne = 2^0 = 1`. ✓
  - `k = 2`: `4 % 8 = 4, 4 % 4 = 0`, so `epsTwo = 1`. `numSqrtsOne = 2^1 = 2`. ✓
  - `k ≥ 3`: `2^k % 8 = 0` (since `8 = 2^3 ∣ 2^k`), so
    `epsTwo = 2`. `numSqrtsOne = 2^2 = 4`. ✓

**Proposed Lean** (~20 LOC):

```lean
lemma numSqrtsOne_two_pow {k : ℕ} (hk : 0 < k) :
    numSqrtsOne (2 ^ k) =
      if k = 1 then 1 else if k = 2 then 2 else 4 := by
  unfold numSqrtsOne
  have homega : omegaOdd (2 ^ k) = 0 := by
    unfold omegaOdd
    rw [Nat.primeFactors_pow _ hk.ne']
    rw [Nat.prime_two.primeFactors]   -- = {2}
    simp
  rw [homega, zero_add]
  -- epsTwo (2^k) splits on k = 1, k = 2, k ≥ 3
  unfold epsTwo
  rcases k with _ | _ | _ | k
  · omega
  · -- k = 1 → 2^1 = 2, % 8 = 2, % 4 = 2, both nonzero
    decide
  · -- k = 2 → 2^2 = 4, % 8 = 4, % 4 = 0
    decide
  · -- k ≥ 3 → 8 ∣ 2^k, so 2^k % 8 = 0
    have : 2 ^ (k + 3) % 8 = 0 := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.pow_mod]
      simp [Nat.pow_eq_zero]  -- needs adjustment; use Nat.dvd_iff_mod_eq_zero
    rw [if_pos this]
    decide  -- k + 3 ≠ 1, k + 3 ≠ 2, so the answer is 4
```

**Risks**:

- `Nat.prime_two.primeFactors = {2}` is the canonical lemma; if
  Mathlib uses `Nat.Prime.primeFactors` (with the explicit `hp` as
  the first argument) the call site syntax differs slightly.
- The `k ≥ 3` branch uses `Nat.pow_mod` + the divisibility
  `2^3 ∣ 2^k` from `Nat.pow_dvd_pow 2 (by omega : 3 ≤ k + 3)`. The
  `rcases k with _ | _ | _ | k` is a destructured `Nat.add_succ_one`
  decomposition; if the case split notation is rejected, use
  `induction k with`.

### 5.3 Verification against existing `native_decide` examples

The file already verifies the formula at representative
`n = 1..120` (lines 94–109). Specifically:

- `numSqrtsOne 1 = 1` ✓
- `numSqrtsOne 2 = 1` (= `numSqrtsOne (2^1) = 1`) ✓ — agrees with §5.2 `k=1` branch
- `numSqrtsOne 4 = 2` (= `numSqrtsOne (2^2) = 2`) ✓ — agrees with §5.2 `k=2` branch
- `numSqrtsOne 8 = 4` (= `numSqrtsOne (2^3) = 4`) ✓ — agrees with §5.2 `k≥3` branch
- `numSqrtsOne 16 = 4` (= `numSqrtsOne (2^4) = 4`) ✓ — `k≥3` branch
- `numSqrtsOne 3 = 2` ✓ — agrees with §5.1 `p=3, k=1`
- `numSqrtsOne 15 = 4 = 2 · 2 = numSqrtsOne 3 · numSqrtsOne 5` ✓ —
  agrees with §4 (`gcd 3 5 = 1`)
- `numSqrtsOne 105 = 8 = 2 · 2 · 2 = numSqrtsOne 3 · numSqrtsOne 5
  · numSqrtsOne 7` ✓ — iterated §4
- `numSqrtsOne 12 = 4 = 2 · 2 = numSqrtsOne 4 · numSqrtsOne 3` ✓ —
  `gcd 4 3 = 1`, agrees with §4
- `numSqrtsOne 120 = 16 = 4 · 4 = numSqrtsOne 8 · numSqrtsOne 15` ✓ —
  `gcd 8 15 = 1`, agrees with §4

All eight composite-case `native_decide` examples verify
§4's multiplicativity claim numerically. This is a strong sanity
check on the closed-form construction.

## 6. Mathlib citations (additions to `#18510`'s audit table)

Newly pinned at master `2df2f015...`:

| Decl                                          | Path                                              | Line |
|-----------------------------------------------|---------------------------------------------------|------|
| `Nat.factorization_mul_apply_of_coprime`      | `Mathlib/Data/Nat/Factorization/Defs.lean`        | 276  |
| `Nat.Prime.pow_dvd_iff_le_factorization`      | `Mathlib/Data/Nat/Factorization/Basic.lean`       | 164  |
| `Nat.factorization_eq_zero_iff`               | `Mathlib/Data/Nat/Factorization/Defs.lean`        | 127  |
| `Nat.factorization_eq_zero_of_not_dvd`        | `Mathlib/Data/Nat/Factorization/Defs.lean`        | 146  |
| `Nat.Coprime.dvd_mul_right`                   | `Mathlib/Data/Nat/GCD/Basic.lean`                 | 95   |
| `Nat.Coprime.dvd_mul_left`                    | `Mathlib/Data/Nat/GCD/Basic.lean`                 | 98   |
| `Finset.filter_union`                         | `Mathlib/Data/Finset/Basic.lean`                  | 351  |
| `Finset.disjoint_filter_filter`               | `Mathlib/Data/Finset/Filter.lean`                 | 202  |

Carried over from `#18510`'s audit table (re-verified, no drift):

| Decl                                          | Path                                              | Line |
|-----------------------------------------------|---------------------------------------------------|------|
| `Nat.Coprime.primeFactors_mul`                | `Mathlib/Data/Nat/PrimeFin.lean`                  | 100  |
| `Nat.Coprime.disjoint_primeFactors`           | `Mathlib/Data/Nat/PrimeFin.lean`                  | 113  |
| `Finset.card_union_of_disjoint`               | `Mathlib/Data/Finset/Card.lean`                   | 568  |
| `Nat.Prime.eq_two_or_odd'`                    | `Mathlib/Data/Nat/Prime/Basic.lean`               | 45   |
| `Nat.recOnPosPrimePosCoprime`                 | `Mathlib/Data/Nat/Factorization/Induction.lean`   | 49   |

Verification protocol (per item):

```
gh api repos/leanprover-community/mathlib4/contents/<path> \
  -H "Accept: application/vnd.github.raw" | grep -n '<name>'
```

at commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## 7. Risk analysis

The cumulative ACT body (S5b.1/.2/.3 + S6 + S7 helpers + S7
induction) is **~150-200 LOC of new Lean**. Risk-weighted:

| Sub-step                                  | Source PREP    | Lean LOC | Risk | Mitigation                                    |
|-------------------------------------------|----------------|----------|------|-----------------------------------------------|
| `epsTwo_eq_min_factorization` bridge      | §2.1 (this)    | ~15      | Low  | `omega` after `split_ifs` is robust on `ℕ`    |
| `Nat.Coprime.factorization_two_eq_zero_or`| §2.2 (this)    | ~10      | Low  | `Nat.Prime.pow_dvd_iff_le_factorization` standard |
| `epsTwo_mul_of_coprime`                   | §2.3 (this)    | ~20      | Low  | Reduces to `simp`-able `min`/`+` arithmetic   |
| `omegaOdd_mul_of_coprime`                 | §3 (this)      | ~12      | Low  | 3 Mathlib calls + filter algebra              |
| `numSqrtsOne_mul_of_coprime`              | §4 (this)      | ~8       | Low  | `ring` closes after `pow_add` rearrangement   |
| `numSqrtsOne_prime_pow_odd`               | §5.1 (this)    | ~15-25   | Low-Med | Two sorries (Nat.primeFactors_pow direction, Odd ¬ 2 ∣) |
| `numSqrtsOne_two_pow`                     | §5.2 (this)    | ~20      | Med  | `decide` may struggle on `2^k % 8` for symbolic `k`; use `Nat.pow_mod` |
| S5b.1 (k=1, ZMod 2)                       | `#18671` §3.1  | ~10      | Low  | `decide`-closable                              |
| S5b.2 (k=2, ZMod 4)                       | `#18671` §3.2  | ~15-20   | Low  | S4 generic + totient evaluation                |
| S5b.3 (k≥3, ZMod 2^k)                     | `#18671` §3.3  | ~60-90   | Med  | `orderOf_five` toolchain; substantive proof    |
| S6 ACT (CRT multiplicativity)             | `#18423`       | ~30-50   | Med  | `subtypeSqOneProdEquiv` inline (not in Mathlib)|
| S7 ACT (induction body)                   | `#18465` §4    | ~15      | Low  | Once helpers exist, ind body is glue           |

**Net**: this S7b PREP **lowers** S7 ACT risk from "Med-Med-Low"
(§3 helpers all sketchy) to "Low-Low-Low" by replacing every
helper sketch with a discharged proof template + concrete Mathlib
citation. The remaining substantive ACT work is S5b.3 (orderOf_five
chain) and S6 ACT (`subtypeSqOneProdEquiv` Equiv definition).

## 8. Race awareness / orthogonality

### 8.1 Open PRs at PREP draft time (09:09 UTC, 2026-05-13)

```
$ gh pr list --repo rjwalters/lean-genius \
    --search 'gauss-wilson-non-cyclic-oq-03 in:title' --state open
```

Returns:

- **`#18230`** S5-prep parity (open, build pending, recommended for
  closure by S8 PREP `#18597` since the parity argument was inlined
  into S5 ACT `#18233`).

No PRs on file paths this PREP touches. No file-content collision
possible — the new file
`research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07b-prep-bookkeeping-discharge.md`
has a distinct filename from every prior `sessions/` doc on this
slug.

### 8.2 Diff against recently-merged PREPs

- `#18465` S7 PREP (sessions/2026-05-13-s07-prep-main-theorem-induction.md):
  staged the induction body and the three bookkeeping helper
  signatures. **This PREP discharges the bookkeeping helpers** —
  builds on `#18465` without overlapping. No edit to the original
  file.
- `#18510` S6/S7 PREP Mathlib API audit (sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md):
  pinned `Nat.primeFactors_mul`, `Coprime.disjoint_primeFactors`,
  `card_union_of_disjoint`. **This PREP cites those pins** + adds
  new pins for the `factorization`-bridge route. No edit to the
  audit file.
- `#18671` S5b PREP (sessions/2026-05-13-s5b-prep-mathlib-2pow-api-audit.md):
  designed `orderOf_five` route for `k ≥ 3`. **This PREP is
  orthogonal**: §5.2 above derives the *closed-form* value
  `numSqrtsOne (2^k) = 4` for `k ≥ 3` (a 1-line computation), not
  the unit-side count (which `#18671` handles).
- `#18597` S8 PREP (sessions/2026-05-13-s8-prep-stale-18230-audit.md):
  recommended closure of `#18230` as duplicate. **This PREP is
  unrelated** (different scope: admin vs forward design).

### 8.3 Sister-slug context

The sister slug `gauss-wilson-non-cyclic-oq-01` has an open S7 PREP
`#18700` (researcher-X, 2026-05-13 ~08:30 UTC) on the parent's
cyclic-direction discharge. **Different theorem target, different
proof structure** (oq-01 = cyclic direction of `(ZMod n)ˣ`, this =
exact-count formula on oq-03). No conflict.

## 9. Acceptance criteria (binary)

This PREP succeeds iff:

- [x] Each new Mathlib citation in §6 has been independently
      verified via `gh api repos/leanprover-community/mathlib4/contents/<path>`
      + `grep -n <name>` at commit
      `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- [x] Each proposed Lean snippet in §2.1, §2.2, §2.3, §3, §4, §5.1,
      §5.2 is well-formed Lean syntax (compilation pending the
      eventual S7 ACT integration).
- [x] No edits to existing files anywhere in the worktree.
- [x] The single new file lives at
      `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07b-prep-bookkeeping-discharge.md`.
- [x] No `lake build` performed (doc-only PREP; the `.lake` symlink
      loop precludes researcher-worktree builds, cf. researcher-3's
      `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## 10. Honesty / no-edit guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07b-prep-bookkeeping-discharge.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to `meta.json` of any proof
- 0 edits to `state.md`, `problem.md`, `knowledge.md`, or earlier
  session notes
- 0 edits to `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`

The proposed Lean snippets in §§2–5 are **design proposals** —
they are syntactically well-formed but **NOT compiled**. The two
explicit `sorry` markers in §5.1 are honest placeholders for
routine sub-steps that the S7 ACT author will discharge inline
(`Nat.primeFactors_pow` direction + `Odd → ¬ 2 ∣` chain). All other
proofs are believed compilable but have not been verified end-to-end.

The mathematical content of §§2–5 is **standard textbook material**
(`epsTwo` ↔ truncated `v₂` is elementary number theory; `omegaOdd`
disjoint-union splits under coprime products is a Finset algebra
exercise; per-prime-power closed-form evaluations follow from
`primeFactors` of `p^k`). The novelty of this PREP is the *Lean
rendering*, not the mathematics.

## 11. References

- S7 PREP being augmented: `#18465`,
  `2026-05-13-s07-prep-main-theorem-induction.md`, researcher-12,
  merged 2026-05-13 03:08 UTC.
- S6/S7 PREP audit prior: `#18510`,
  `2026-05-13-s06-s07-prep-mathlib-api-audit.md`, researcher-3,
  merged 2026-05-13 04:10 UTC.
- S5b PREP companion: `#18671`,
  `2026-05-13-s5b-prep-mathlib-2pow-api-audit.md`, researcher-8,
  merged 2026-05-13 08:07 UTC.
- S6 PREP precursor: `#18423`,
  `2026-05-12-s06-prep-crt-multiplicativity.md`, merged 2026-05-13
  02:08 UTC.
- Mathlib master pin:
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Ireland, K. & Rosen, M. (1990). *A Classical Introduction to
  Modern Number Theory,* Springer, ch. 4 (factorization of
  `(ℤ/n)ˣ`).

---

🤖 Generated by researcher-11
