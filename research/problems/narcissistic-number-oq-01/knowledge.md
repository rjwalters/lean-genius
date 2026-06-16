# narcissistic-number-oq-01 — Finiteness of narcissistic numbers

**Statement.** An `n`-digit number `m` is *narcissistic* if it equals the sum of
its decimal digits each raised to the `n`-th power (e.g. `153 = 1³+5³+3³`,
`8208 = 8⁴+2⁴+0⁴+8⁴`). Prove the set of narcissistic numbers is finite.

**Status:** ACT (proof structure written, build-pending under blackout).

---

## Summary

The set is finite by a digit-count bound, not by enumeration:

- An `n`-digit number's digit-power-sum is at most `n · 9ⁿ`.
- An `n`-digit number is at least `10^(n-1)`.
- For all `n ≥ 61`, `10^(n-1) > n · 9ⁿ`, so an `n`-digit number with `n ≥ 61`
  cannot equal its own digit-power-sum.
- Hence every narcissistic number has `< 61` digits, i.e. is `< 10⁶¹`. A set of
  naturals bounded above is finite. ∎

The crossover `n = 61` is Python-certified
(`research/certificates/narcissistic_number_oq01_finiteness.py`): the inequality
flips between `n = 60` (`10⁵⁹ ≤ 60·9⁶⁰`) and `n = 61` (`10⁶⁰ > 61·9⁶¹`). The
bounded brute-force reproduces the known small narcissistic numbers
`1..9, 153, 370, 371, 407, 1634, 8208, 9474, 54748, …`; the full base-10 list has
88 members, largest `115132219018763992565095597973971522401` (39 digits < 10⁶¹).

---

## Session 2026-06-16 (s02) — REVISIT (researcher-9): both HARD sorries discharged

**Mode**: REVISIT · **Outcome**: progress (file now 0 sorries / 0 axioms, build-pending)

### What I did
Discharged the two documented `sorry`s left by s01, so the orphan file is now
mathematically complete (still UNREGISTERED → 0 gallery risk):

- **`crossover : ∀ n, 61 ≤ n → n · 9ⁿ < 10^(n-1)`** — `Nat.le_induction` from 61.
  - Base `61·9⁶¹ < 10⁶⁰` by `norm_num` (evaluates the ~60-digit literals).
  - Step factors out `9ⁿ`: `(n+1)·9^(n+1) = 9·(n+1)·9ⁿ ≤ 10·n·9ⁿ`
    (`Nat.mul_le_mul` with `9·(n+1) ≤ 10·n` by `omega`, valid since `n ≥ 9`),
    then `= 10·(n·9ⁿ) < 10·10^(n-1)` (`mul_lt_mul_of_pos_left ih`), `= 10ⁿ`.
  - Key rewrite `10ⁿ = 10^(n-1)·10` via `← pow_succ` + `Nat.sub_add_cancel`
    (avoids the simultaneous-`n`-rewrite cascade that breaks `rw [hsplit]` on
    a goal containing both `n` and `n-1`).
- **`pow_pred_length_le : m ≠ 0 → 10^(numDigits m − 1) ≤ m`** — from
  `Nat.base_pow_length_digits_le 10 m (1<10) hm : 10^L ≤ 10·m` (L = numDigits),
  split `L = (L-1)+1` (needs `0 < L` via
  `List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hm)`), `pow_succ`,
  `Nat.mul_comm`, then cancel the `10` with `Nat.le_of_mul_le_mul_left`.

### Key findings / API (verified vs offline mathlib4 @ v4.26.0 rev 2df2f0150c)
- `Nat.base_pow_length_digits_le (b m) (hb) : m ≠ 0 → b^(digits b m).length ≤ b·m`
  — the s01 "gap" lemma, name CONFIRMED (was the one flagged "verify when Docker
  returns"). Returns an implication in `m ≠ 0`.
- `List.length_pos_of_ne_nil`, `Nat.digits_ne_nil_iff_ne_zero`,
  `Nat.le_of_mul_le_mul_left`, `mul_lt_mul_of_pos_left`, `Nat.mul_le_mul`,
  `pow_succ`, `Nat.sub_add_cancel` all present at the pin.
- Used term-mode (defeq) for `numDigits m ≡ (digits 10 m).length` instead of
  `rw [numDigits]` (rw-on-plain-def is fragile).

### Blackout (unchanged)
Docker daemon WEDGED (`docker run --rm alpine echo ok` prints `ok` then the wrapper
hangs → rc=124 on teardown; image/cache presumed still wiped) and Aristotle MCP
`prove` returns 404 "Resource not found". So the file is **hand-verified only**, not
machine-checked — kept as an orphan.

### Next steps (when Docker / Aristotle return)
1. `./proofs/scripts/docker-build.sh Proofs.NarcissisticNumberOQ01`; fix any residual
   lemma-name drift from `grep error:` (most-likely suspects: the s01-authored
   `digitPowSum_le` uses `smul_eq_mul; rfl` for `length • 9ⁿ` — may need
   `nsmul_eq_mul`).
2. If green, register in `Proofs.lean` + add gallery data under
   `src/data/proofs/narcissistic-number-oq-01/`.

---

## Session 2026-06-16 (s01) — FRESH

**Mode:** FRESH. **Outcome:** progress (structure + certificate; build-pending).

### Context: full toolchain blackout
- Docker daemon DOWN (host load ~30); `lake build` impossible.
- Aristotle MCP returns `{"status":"error","message":"Resource not found."}` (404).
- Researcher pool thrashing: automorphic / happy / taxicab / amgm slugs each had
  ≥1 sibling agent with a *hung* `docker-build.sh` process. Originally claimed
  `automorphic-number-oq-01`, found researcher-9 **and** researcher-10 already had
  a complete 0-sorry `AutomorphicNumberOQ01.lean` mid-build → released, switched to
  the uncontested `narcissistic-number-oq-01`.

### What I did
- Certified the finiteness bound in Python (crossover `D = 61`, examples match
  OEIS A005188). Saved to `research/certificates/`.
- Wrote orphan `proofs/Proofs/NarcissisticNumberOQ01.lean` (UNREGISTERED):
  - `numDigits`, `Narcissistic` definitions.
  - `digit_le_nine`, `digitPowSum_le` — full proofs (low risk).
  - `numDigits_lt_61`, `narcissistic_finite` — assembled from the two lemmas below.
  - `crossover` (`∀ n ≥ 61, n·9ⁿ < 10^(n-1)`) and `pow_pred_length_le`
    (`m ≠ 0 → 10^(numDigits m − 1) ≤ m`) left as documented `sorry` (HARD).

### Key findings / Mathlib API
- Digit upper bound: `Nat.digits_lt_base` (`d < 10`), `Nat.pow_le_pow_left`,
  `List.sum_le_card_nsmul`, `List.length_map`.
- Number upper bound: `Nat.lt_base_pow_length_digits` (`m < 10^(digits).length`).
- Number lower bound (gap): expected `Nat.base_pow_length_digits_le`
  (`10^(digits).length ≤ 10·m` for `m ≠ 0`) → cancel one `10`. **Verify exact name
  when Docker returns.**
- Finiteness wrapper: `Set.Finite.subset (Set.finite_Iio _)`.

### Crossover induction plan (`crossover`)
`Nat.le_induction` from 61. Base `61·9⁶¹ < 10⁶⁰` via `norm_num`. Step uses
`9·(n+1) ≤ 10·n` for `n ≥ 9`, giving `(n+1)·9^(n+1) ≤ 10·n·9ⁿ < 10·10^(n-1) = 10ⁿ`.

### Next steps (when Docker / Aristotle are back)
1. `./proofs/scripts/docker-build.sh Proofs.NarcissisticNumberOQ01`; fix lemma
   names (esp. `pow_pred_length_le` source lemma) from `grep error:`.
2. Discharge the two `sorry`s manually or submit to Aristotle (both are HARD-known).
3. If green, register in `Proofs.lean` and add gallery data under
   `src/data/proofs/narcissistic-number-oq-01/`.

### Files
- `proofs/Proofs/NarcissisticNumberOQ01.lean` (orphan, build-pending)
- `research/certificates/narcissistic_number_oq01_finiteness.py`
- `research/problems/narcissistic-number-oq-01/knowledge.md`
