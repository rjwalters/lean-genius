# S7 PREP — main theorem induction outline (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (orientation for the *main-theorem* `card_sqrts_one_eq_numSqrtsOne`
discharge, downstream of S5 ACT (merged), S5b OBSERVE (merged), S5b
ACT (not yet), and S6 PREP (merged)).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the prior `sessions/` notes, gallery
`meta.json`, or research JSON.

## 0. Why S7 PREP now

The slug's roadmap (per `state.md` § "Next Action" and the merged S6
PREP doc) has the discharge chain:

| Step    | Status (2026-05-13 ~02:15 UTC)                                   |
|---------|------------------------------------------------------------------|
| S5 ACT  | ✓ merged (#18233) — `card_filter_sq_eq_one_units_zmod_prime_pow_odd` |
| S5b OBSERVE | ✓ merged — even-prime-case analysis (k = 1, 2, ≥ 3 → 1, 2, 4) |
| S5b ACT | ⏳ not yet — even-prime Lean instantiations                       |
| S6 PREP | ✓ merged — CRT multiplicativity template (`Nat.totient_mul`-style) |
| S6 ACT  | ⏳ not yet — `card_filter_sq_eq_one_units_mul_coprime`            |
| **S7 ACT (target of this PREP)** | ⏳ not yet — main theorem `card_sqrts_one_eq_numSqrtsOne` |

The S5b ACT and S6 ACT are the immediate next deliverables. **This
PREP designs the S7 ACT** — the final induction that assembles
per-prime-power inputs (S5 + S5b) via the multiplicativity bridge
(S6) into the headline `card_sqrts_one_eq_numSqrtsOne` discharge.

S7 closes the file's sole remaining `sorry` at line 131. Its proof
body is ~30–50 LOC depending on whether the bookkeeping lemmas
(`omegaOdd` and `epsTwo` additivity under coprime products) are
factored out as standalone helpers or inlined.

This PREP is orthogonal to:
- PR #18230 (S5-prep parity, open and likely obsolete post-S5 ACT) — different theorem, different section
- S5b ACT / S6 ACT (not yet open) — this PREP designs what comes *after* them

## 1. Goal of the eventual S7 ACT

Discharge the existing `sorry` at line 131 of
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`:

```lean
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by
  -- S7 ACT proof body — see § 4
  sorry  -- closed by S7
```

Three deliverables in the S7 ACT PR:

1. **Two bookkeeping helpers** for the closed-form side:
   - `numSqrtsOne_mul_of_coprime : ∀ m n, m.Coprime n → 0 < m → 0 < n → numSqrtsOne (m * n) = numSqrtsOne m * numSqrtsOne n`
   - `numSqrtsOne_one : numSqrtsOne 1 = 1` (already discharged by `native_decide` at line 94)
2. **Two per-prime-power evaluations** of the closed-form:
   - `numSqrtsOne_prime_pow_odd : ∀ p k, Odd p → p.Prime → 0 < k → numSqrtsOne (p^k) = 2`
   - `numSqrtsOne_two_pow : ∀ k, 0 < k → numSqrtsOne (2^k) = if k = 1 then 1 else if k = 2 then 2 else 4`
3. **The induction itself** via `Nat.recOnPosPrimePosCoprime`.

Net delta target: ~50–80 LOC including all helpers and the
induction body. 0 new sorries (the existing one closes); 0 axioms.

## 2. Mathlib API: `Nat.recOnPosPrimePosCoprime`

The load-bearing induction principle:

```lean
@[elab_as_elim]
def Nat.recOnPosPrimePosCoprime {motive : ℕ → Sort*}
    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))
    (zero : motive 0) (one : motive 1)
    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a
```

Path: `Mathlib/Data/Nat/Factorization/Induction.lean:49`.

For our motive `motive n := (n = 0) ∨ [NeZero n] → P n`, the four
cases discharge as:

- **`zero`** (n = 0): excluded by `[NeZero n]`; absurd.
- **`one`** (n = 1): both sides are 1; by `decide` or `native_decide`.
- **`prime_pow`** (n = p^k for prime p, k > 0): split on p = 2 vs p
  odd; use S5b ACT for the 2-case, S5 ACT for the odd-case.
- **`coprime`** (n = a*b with a, b > 1, coprime): use S6 ACT
  multiplicativity plus the closed-form bookkeeping helper
  `numSqrtsOne_mul_of_coprime`.

## 3. Closed-form bookkeeping

### 3.1 `omegaOdd` additivity under coprime products

Recall `omegaOdd n := (n.primeFactors.filter (· ≠ 2)).card`.

For coprime `m, n > 0`:

```
(m * n).primeFactors = m.primeFactors ∪ n.primeFactors      -- Mathlib Nat.primeFactors_mul
m.primeFactors ∩ n.primeFactors = ∅                          -- coprimality
```

Combining: `((m * n).primeFactors.filter (· ≠ 2)).card =
(m.primeFactors.filter (· ≠ 2)).card + (n.primeFactors.filter (· ≠ 2)).card`,
i.e. `omegaOdd (m * n) = omegaOdd m + omegaOdd n`.

Mathlib citations (verified at master `2df2f015...`):

| Lemma                              | Path                                              |
|------------------------------------|---------------------------------------------------|
| `Nat.primeFactors_mul`             | `Mathlib/NumberTheory/Padics/PadicVal.lean` (or `Nat/Factorization/Basic.lean`) |
| `Finset.card_union_eq_card_add_card_sub_card_inter` | `Mathlib/Data/Finset/Card.lean`     |
| `Nat.Coprime.disjoint_primeFactors` | `Mathlib/Data/Nat/Factorization/Basic.lean`      |

### 3.2 `epsTwo` additivity under coprime products

Recall `epsTwo n := if n % 8 = 0 then 2 else if n % 4 = 0 then 1 else 0`.
Equivalently, `epsTwo n = max 0 (min 2 (v₂ n - 1))` for `n > 0`.

For coprime `m, n > 0`: `gcd m n = 1`, so at most one of `m, n` is
divisible by 2. Hence:

- If both odd: `v₂(m*n) = 0`, `v₂(m) = v₂(n) = 0`, so
  `epsTwo (m*n) = 0 = 0 + 0 = epsTwo m + epsTwo n`. ✓
- If exactly one even (WLOG `2 ∣ m`, `n` odd): `v₂(m*n) = v₂(m)`,
  `v₂(n) = 0`, so `epsTwo (m*n) = epsTwo m = epsTwo m + 0 = epsTwo m + epsTwo n`. ✓

So `epsTwo (m * n) = epsTwo m + epsTwo n` when `m.Coprime n`.

This is a 4-case modular arithmetic discharge:

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

### 3.3 `numSqrtsOne` multiplicativity (consequence)

From `omegaOdd` and `epsTwo` additivity:

```lean
lemma numSqrtsOne_mul_of_coprime {m n : ℕ} (h : m.Coprime n) (hm : 0 < m) (hn : 0 < n) :
    numSqrtsOne (m * n) = numSqrtsOne m * numSqrtsOne n := by
  unfold numSqrtsOne
  rw [omegaOdd_mul_of_coprime h hm hn, epsTwo_mul_of_coprime h]
  ring_nf
  rw [← pow_add, ← pow_add]
  congr 1
  ring
```

This is 5–7 LOC.

## 4. The S7 induction proof body

```lean
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by
  -- Step 0: bridge ring side to unit side via S3.
  rw [card_sqrts_one_eq_card_units_sqrts_one n]
  -- Step 1: induction on n.
  have hn : 0 < n := NeZero.pos n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => decide  -- or native_decide
  | prime_pow p k hp hk =>
      -- Split on p odd vs p = 2.
      rcases Nat.Prime.eq_two_or_odd' hp with rfl | ⟨q, rfl⟩
      · -- p = 2: use S5b ACT.
        exact card_filter_sq_eq_one_units_zmod_two_pow k hk
      · -- p odd: use S5 ACT.
        exact card_filter_sq_eq_one_units_zmod_prime_pow_odd hp ⟨q, rfl⟩ k hk
  | coprime a b ha hb h ih_a ih_b =>
      -- Use S6 ACT multiplicativity + closed-form multiplicativity.
      rw [card_filter_sq_eq_one_units_mul_coprime h]
      rw [ih_a, ih_b]
      rw [numSqrtsOne_mul_of_coprime h (lt_trans Nat.zero_lt_one ha) (lt_trans Nat.zero_lt_one hb)]
```

This is **~15 LOC** for the induction body, **~50 LOC including
bookkeeping helpers**.

## 5. Dependencies on prior deliverables

| Symbol                                                            | Source     | Status        |
|-------------------------------------------------------------------|------------|---------------|
| `card_sqrts_one_eq_card_units_sqrts_one` (ring ↔ unit bridge)     | S3 ACT     | ✓ merged      |
| `card_filter_sq_eq_one_units_zmod_prime_pow_odd`                  | S5 ACT     | ✓ merged      |
| `card_filter_sq_eq_one_units_zmod_two_pow` (k=1: 1, k=2: 2, k≥3: 4) | S5b ACT  | ⏳ not yet     |
| `card_filter_sq_eq_one_units_mul_coprime`                         | S6 ACT     | ⏳ not yet     |
| `omegaOdd_mul_of_coprime`                                         | S7 (this)  | new           |
| `epsTwo_mul_of_coprime`                                           | S7 (this)  | new           |
| `numSqrtsOne_mul_of_coprime`                                      | S7 (this)  | new           |

If S5b ACT and S6 ACT have not landed at S7 ACT time, the S7 ACT
author can either (A) wait, or (B) ship a **partial** S7 that
discharges the `one` and `coprime` cases with `sorry` on the two
prime-power sub-cases — making the remaining gap explicit.

The natural sequencing is **S5b ACT → S6 ACT → S7 ACT**.

## 6. Mathlib API audit (verified at master `2df2f015...`)

| Lemma / Def                                       | Path                                              | Line  |
|---------------------------------------------------|---------------------------------------------------|-------|
| `Nat.recOnPosPrimePosCoprime`                     | `Mathlib/Data/Nat/Factorization/Induction.lean`   | 49    |
| `Nat.recOnPrimeCoprime`                           | `Mathlib/Data/Nat/Factorization/Induction.lean`   | 68    |
| `Nat.Prime.eq_two_or_odd'` (or `eq_two_or_odd`)   | `Mathlib/Data/Nat/Prime/Basic.lean`               | (search) |
| `Nat.Coprime.disjoint_primeFactors`               | `Mathlib/Data/Nat/Factorization/Basic.lean`       | (search) |
| `Nat.primeFactors_mul` (mul over coprime)         | `Mathlib/Data/Nat/Factorization/Basic.lean`       | (search) |
| `Finset.card_union_of_disjoint`                   | `Mathlib/Data/Finset/Card.lean`                   | (search) |
| `NeZero.pos`                                      | `Mathlib/Algebra/NeZero.lean`                     | (search) |

The `eq_two_or_odd'` invocation may use a slightly different form
depending on Mathlib's current API surface for "prime is either 2
or odd". The S7 ACT author should also check whether `Nat.Prime` vs
`Prime` (the more general predicate from `Mathlib.RingTheory`)
matters at the `recOnPosPrimePosCoprime` interface — both should
coerce via `Nat.Prime.prime`.

## 7. Tactical risks

| Risk                                                              | Severity | Mitigation                                  |
|-------------------------------------------------------------------|----------|---------------------------------------------|
| `Nat.recOnPosPrimePosCoprime`'s `motive` requires positivity proof on n; need to thread `0 < n` from `[NeZero n]` | Med | Use `NeZero.pos n` upfront; carry through cases |
| `prime_pow` case-split on p=2 vs p odd: which Mathlib lemma fires | Med | `Nat.Prime.eq_two_or_odd` returns `p = 2 ∨ p % 2 = 1`; `rcases` on the disjunction |
| `epsTwo_mul_of_coprime` 4-case discharge: `omega` may not close all branches | Low-Med | Fallback: `decide` on each branch after `interval_cases` on `m % 8`, `n % 8` |
| `S6 ACT`'s exact theorem name + statement signature (which `Coprime` form, `Fintype.card` vs `Nat.card`) | Med | Coordinate with S6 ACT author; or wrap with adapter lemma in S7 |
| Coercion `Prime p ↔ Nat.Prime p` at the `recOnPosPrimePosCoprime` boundary | Low | `Nat.Prime.prime` / `Nat.prime_iff` bridges |
| `pow_add` direction: `2^(a+b) = 2^a * 2^b` vs `2^a * 2^b = 2^(a+b)` | Low | `ring` should normalize; if not, explicit `pow_add` rewrite |
| `numSqrtsOne 0 = 0`? No — the function is well-defined for n=0 but motive excludes via `[NeZero n]` | Low | Just-in-time check in `zero` case |

## 8. Acceptance criteria (binary)

The S7 ACT PR must:

- [ ] Discharge the `sorry` at line 131 of
      `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`.
- [ ] Add three bookkeeping helpers: `omegaOdd_mul_of_coprime`,
      `epsTwo_mul_of_coprime`, `numSqrtsOne_mul_of_coprime`. Or
      inline them, but document the choice.
- [ ] Use 0 `sorry`, 0 `axiom` after the discharge. If shipped as
      "partial" (S5b/S6 not yet ready), document each remaining
      sub-case sorry with a clear pointer.
- [ ] ≤ 80 LOC body for the helpers + induction combined.
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ03`.
- [ ] Cite the 4 load-bearing Mathlib lemmas
      (`recOnPosPrimePosCoprime`, `primeFactors_mul`,
      `Coprime.disjoint_primeFactors`, `Nat.Prime.eq_two_or_odd`).
- [ ] Update `state.md` "Sessions" list to add the S7 entry.
- [ ] Update `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`
      `nextSteps` (slug `progress` → `completed` if 0 sorries / 0
      axioms after merge).
- [ ] Update `meta.json` of parent `gauss-wilson-non-cyclic` if the
      `additionalFiles` `sorries` count changes from 1 → 0.

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, or any `sessions/` doc other
  than its own new entry.
- Add new top-level Mathlib imports beyond what S3..S5 already pull
  in (`Nat.recOnPosPrimePosCoprime` should be transitively imported
  via `Mathlib.Data.ZMod.Basic`).
- Add an `axiom` declaration. The S7 induction is fully constructive
  on top of S5 + S5b + S6.

## 9. Race awareness / orthogonality

At PREP push time (≥ 2026-05-13 02:15 UTC):

| PR     | State                | File overlap with this PREP | Conclusion          |
|--------|----------------------|------------------------------|---------------------|
| #18230 | Open, build pending  | none                         | Orthogonal (likely obsolete post-#18233) |

This PREP creates exactly one new file:
`research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07-prep-main-theorem-induction.md`.

No `gh pr list --search` rows for "S7" or "induction" or "main theorem"
on this slug at PREP draft time.

The two open prerequisites (S5b ACT, S6 ACT) have **not yet been
opened** as PRs; the S5b OBSERVE and S6 PREP docs are merged but the
corresponding Lean ACTs are pending. The S7 PREP locks the induction
plan so the S5b ACT and S6 ACT authors can target their theorem
signatures precisely.

## 10. Files this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/gauss-wilson-non-cyclic-oq-03/sessions/2026-05-13-s07-prep-main-theorem-induction.md`
  (this file).

**Does not edit**:

- `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`.
- `proofs/Proofs.lean`.
- `research/problems/gauss-wilson-non-cyclic-oq-03/problem.md`.
- `research/problems/gauss-wilson-non-cyclic-oq-03/knowledge.md`.
- `research/problems/gauss-wilson-non-cyclic-oq-03/state.md`.
- Any prior `sessions/` doc.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`.
- `src/data/proofs/gauss-wilson-non-cyclic/meta.json`.

**Build status**: doc-only; no `lake build` invocation needed.

## 11. References

- Mathlib. `Mathlib/Data/Nat/Factorization/Induction.lean` —
  `recOnPosPrimePosCoprime` (line 49).
- Ireland, K. & Rosen, M. (1990). *A Classical Introduction to
  Modern Number Theory,* Springer, ch. 4 (structure of `(ℤ/n)ˣ`).
- Slug parent. `proofs/Proofs/GaussWilsonNonCyclic.lean` — the
  qualitative `≥ 3` bound that S7 quantitatively upgrades.
- Prior session notes:
  `2026-05-12-s5b-observe-even-prime-case.md` and
  `2026-05-12-s06-prep-crt-multiplicativity.md`.
