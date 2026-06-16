# happy-number-oq-01 — Happy / unhappy dichotomy

**Statement.** Let `S(n)` = sum of squares of the decimal digits of `n`. For every
positive integer, iterating `S` eventually reaches the fixed point `1` (happy) or
enters the cycle `4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4` (unhappy).

## Summary

- **Status:** proof complete, **build-pending** (Docker blackout this session — daemon
  unresponsive, `docker info` rc=124, ~10 stuck build wrappers; Aristotle MCP 404).
- **File:** `proofs/Proofs/HappyNumberOQ01.lean` (UNREGISTERED orphan — not in
  `Proofs.lean`, no gallery dir → zero false-green risk).
- **Axiom status:** `axiomatized`. The finite checks use `native_decide`
  (`Lean.ofReduceBool`). Not `verified`.

## Proof architecture

Headline: `reaches_one_or_four : ∀ n ≥ 1, (∃ k, S^[k] n = 1) ∨ (∃ k, S^[k] n = 4)`.
Built from:

1. `reaches_T : ∀ n ≥ 1, ∃ k, S^[k] n ∈ T` where
   `T = {1,4,16,37,58,89,145,42,20}` is the absorbing set.
2. **Descent** (`descent`): `S n < n` for all `n ≥ 1000`. This is the part that
   covers infinitely many `n` (NOT enumeration). With `L = (digits 10 n).length`:
   - `S n ≤ 81 · L`  (each digit `≤ 9`, via `List.sum_le_card_nsmul` + `digits_lt_base`)
   - `10^(L-1) ≤ n`  (`Nat.base_pow_length_digits_le`)
   - `L ≥ 4`  (`Nat.lt_base_pow_length_digits` + `pow_lt_pow_iff_right'`)
   - `81 · L < 10^(L-1)` for `L ≥ 4`  (`aux_exp`, by `Nat.le_induction`)
3. **Strong induction** (`Nat.strongRecOn`) reduces every `n` to `[1, 999]`;
   `S_pos` (leading digit ≠ 0 via `getLast_digit_ne_zero` + `List.le_sum_of_mem`)
   keeps the orbit positive so the IH applies.
4. **Base case** (`base_reaches`): `native_decide` that every `n ∈ [1,999]` reaches
   `T` within 15 iterations of a bounded checker `reachesT`.
5. From `S^[k] n ∈ T`: if it is a cycle element, a fixed extra number of steps
   (`Function.iterate_add_apply` + `native_decide`) reaches `4`.

## Independent numeric certificate

`verify_happy.py` confirms (Python, base-10):
- `S(1)=1`; the 8-cycle closes exactly.
- `T` is closed under `S`.
- Steps to reach `4` from each cycle element: 16→7, 37→6, 58→5, 89→4, 145→3,
  42→2, 20→1 (these are the exponents used in `reaches_one_or_four`).
- Every `n ∈ [1,999]` reaches `T`; **max steps = 11** (at `n = 269`) → the bound
  `15` in `reachesT` is safe.
- `S(n) < n` for all `1000 ≤ n < 200000` (no counterexamples); `81·L < 10^(L-1)`
  holds for `L = 4..11`.

## Next steps

1. When Docker is back: `./proofs/scripts/docker-build.sh Proofs.HappyNumberOQ01`,
   `grep -i error:` the log. If green, register in `Proofs.lean` + create gallery
   dir `src/data/proofs/happy-number-oq-01/`.
2. Watch points (could need a fix pass on first build):
   - `List.le_sum_of_mem` typeclass resolution for ℕ.
   - `nsmul_eq_mul`/`Nat.cast_id` simp in `hSle` (fallback: `smul_eq_mul`).
   - `Nat.strongRecOn` case label `| _ n ih` (matches existing repo usage).
3. Follow-up OQ candidate: density / counting of happy numbers below `N`
   (asymptotic ~0.146 N is open-ended; the eventual-periodicity is what is proved here).

## Session log

### 2026-06-16 (Session 1, FRESH) — researcher-7
- Mode FRESH. Selected happy-number-oq-01 (only fresh, decidable, unstarted
  available problem; taxicab/automorphic/abundant/keith already done-or-pending).
- Confirmed not in Mathlib, no prior proof file / gallery dir / PR.
- Wrote complete proof (descent + strong induction + native_decide base case),
  name-checked every lemma against offline Mathlib v4.26 (rev 2df2f0150c).
- Verified all numeric claims in Python.
- Dual blackout (Docker rc=124, Aristotle 404) → shipped build-pending orphan.
- Phase: ACT.
