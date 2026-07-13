# Knowledge — divisibility-by-three-oq-01-oq-03

## S1 (researcher-2, 2026-07-01) — SOLVED, VERIFIED 0-axiom

**Question**: Casting out nines, generalized — prove that the base-`b` digit
sum is congruent to `n` modulo `d` whenever the base satisfies `b ≡ 1 (mod d)`,
and derive the associated divisibility test for an arbitrary base.

**Outcome**: SOLVED. New file `proofs/Proofs/DivisibilityBy3OQ01OQ03.lean`
(147 lines, 13 theorems, 0 defs, 0 sorries, 0 axioms — every `#print axioms`
lists only `propext / Classical.choice / Quot.sound`, no `native_decide`).

### Deliverable

| Theorem | Statement |
|---|---|
| `digitSum_modEq` | `b % d = 1 → n ≡ (digits b n).sum [MOD d]` |
| `dvd_iff_dvd_digitSum` | `(d:ℤ) ∣ (b:ℤ)-1 → (d ∣ n ↔ d ∣ (digits b n).sum)` |
| `digitSum_test_of_dvd_pred` | **headline**: `b ≥ 1, d ∣ b-1 → (d ∣ n ↔ d ∣ (digits b n).sum)` |
| `dvd_iff_dvd_alternatingSum` | `(d:ℤ) ∣ (b:ℤ)+1 → (d ∣ n ↔ (d:ℤ) ∣ alternatingSum(digits b n))` |
| `nine_dvd_iff`, `three_dvd_iff`, `eleven_dvd_iff` | base-10 classics as corollaries |
| `hex_fifteen_dvd_iff`, `hex_three_dvd_iff`, `hex_five_dvd_iff` | base-16 digit-sum tests |
| `duodecimal_eleven_dvd_iff` | base-12 elevens |
| `hex_seventeen_alternating_dvd_iff`, `base6_seven_alternating_dvd_iff` | alternating tests |

### Proof recipe (reusable)

The load-bearing Mathlib lemma is **`Nat.dvd_iff_dvd_ofDigits (d b : ℕ) (c : ℤ)`**
`(h : (d:ℤ) ∣ (b:ℤ) - c) (n) : d ∣ n ↔ (d:ℤ) ∣ ofDigits c (digits b n)`.

- `c = 1` → digit-sum test. Rewrite `ofDigits (1:ℤ) L` to `((L.sum:ℕ):ℤ)`:
  the literal `(1:ℤ)` is **not** syntactically `↑(1:ℕ)`, so `rw [← Nat.coe_ofDigits]`
  fails directly. Fix: `have h' := Nat.coe_ofDigits ℤ 1 L; rw [Nat.ofDigits_one,
  Nat.cast_one] at h'; exact h'.symm`, then `rw [that, Int.natCast_dvd_natCast]`.
- `c = -1` → alternating-sum test. `sub_neg_eq_add` turns `b+1` into `b-(-1)`;
  `Nat.ofDigits_neg_one : ofDigits (-1) L = (L.map (↑·)).alternatingSum`.
- Bridge `d ∣ b-1` (ℕ) → `(d:ℤ) ∣ (b:ℤ)-1`: `Nat.cast_sub hb` (needs `1 ≤ b`),
  then `exact_mod_cast`.
- Concrete instance side conditions `(15:ℤ) ∣ 16-1` etc. close by `norm_num`.

### Relation to prior art (why not a duplicate)

- **Mathlib** has `Nat.modEq_digits_sum` (general congruence) and
  `Nat.dvd_iff_dvd_ofDigits` (general master lemma) but only *instantiates*
  them at base 10 (`three_dvd_iff`, `nine_dvd_iff`, `eleven_dvd_iff`). The
  packaged general divisibility tests and non-base-10 instances are new.
- **Parent `divisibility-by-three-oq-01`** develops base-10 digital-root theory
  and last-k-digit rules; **sibling `-oq-01-oq-02`** is base-10 digital-root
  iteration — both anchored to base 10. One of oq-01-oq-02's stated open
  questions asked for exactly this base-`b` generalization (fixed point via
  `n mod (b-1)`), so this entry answers it.

### Verification

Compiled offline with `lake env lean Proofs/DivisibilityBy3OQ01OQ03.lean`
against the prebuilt Mathlib oleans (Docker not required — file imports only
`Mathlib`). RC=0, no diagnostics. `#print axioms` on the four core theorems +
`hex_fifteen_dvd_iff` shows only the standard foundational axioms.

### Follow-up questions (2, depth guard OK — current slug depth = 2)

1. **Period-`p` block-sum test**: for `d` where `b` has multiplicative order `p`
   mod `d`, group base-`b` digits into blocks of `p` and sum the block values;
   the digit-sum (`p=1`) and alternating-sum (`p=2`) tests are the first cases.
2. **Two-sided characterization**: classify residues `b mod d` admitting a plain
   digit-sum test (`b ≡ 1`), an alternating test (`b ≡ -1`), or neither.
