# Knowledge Base: erdos-1-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent problem `erdos-1` asks: if `A ⊆ {1,…,N}` has `|A| = n` with all `2^n` subset sums distinct, must `N ≥ c · 2^n` for some absolute constant `c > 0`? (Erdős OPEN.)

This follow-up (OQ-04) investigates the **structure** of the extremal sets — those achieving the minimum `N = f(n)`. The minimum values form **OEIS A005318**:

| `n` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|-----|---|---|---|---|---|---|---|---|---|
| `f(n)` | 0 | 1 | 2 | 4 | 7 | 13 | 24 | 44 | 84 |

The **Conway–Guy conjecture** (1968) identifies specific sets achieving these minima:

- `n=4`: `{3, 5, 6, 7}` — max 7
- `n=5`: `{6, 9, 11, 12, 13}` — max 13
- `n=6`: `{11, 17, 20, 22, 23, 24}` — max 24
- `n=7`: `{20, 31, 37, 40, 42, 43, 44}` — max 44

with a recurrence `a_n = a_{n-1} + ⌈S_{n-1}/2⌉` over partial sums.

---

## Insights

1. **`hasDistinctSubsetSums` is decidable**: brute-force enumeration of `A.powerset × A.powerset` gives a `Decidable` instance, enabling `native_decide` for any concrete finite set. This is the workhorse behind the small-case verifications `dss_1, dss_12, dss_124, dss_3567, dss_conway_guy_5` and would extend to `n = 6, 7, 8` directly (Lever A in `state.md`).

2. **The trivial upper bound `f(n) ≤ 2^n − 1`** comes from powers of two `{1, 2, 4, …, 2^{n-1}}`. Each subset has a unique sum because binary representation is unique. The Lean proof (`powers_of_two_dss`) reduces to a `sum_pow_two_inj` lemma proved by induction on `n` with case-analysis on whether `n` is in either subset. This is axiom-free Mathlib-only work and survives in 60 lines including helper lemmas.

3. **The gap `2^n − 1 − f(n)`** is widely conjectured to be the substantive content: Conway–Guy sets give `f(n) ≈ 2^n / √n` asymptotically (Elkies 1986), much smaller than `2^n − 1`. The factor-of-`√n` improvement is non-trivial and comes from entropy/Fourier methods not currently in Mathlib.

4. **Mathlib API used**: `Finset.powerset`, `Finset.sum_image`, `Finset.add_sum_erase`, `Finset.insert_erase`, `Finset.single_le_sum`, `Nat.pow_right_injective`, `Nat.pow_lt_pow_right`. All standard; no API gaps encountered for the verified content.

5. **`conwayGuySeq` recurrence is awkward in Lean ℕ**: `a_n = a_{n-1} + ⌈S_{n-1}/2⌉` requires carrying the partial sum along (so the recurrence is on a pair `(a_n, S_n)`, not on `a_n` alone). The current file sidesteps this by listing OEIS A005318 values up to `n = 8` and defaulting to `0` beyond. A future iteration could fold the partial-sum into a structural recursion to get an exact `conwayGuySeq` for all `n`.

---

## Built items (cross-reference with `src/data/research/problems/erdos-1-oq-04.json`)

- `Erdos1OQ04.lean` (245 LOC, 0 sorries, 0 axioms)
- `hasDistinctSubsetSums` (definition) + `decidableHasDistinctSubsetSums` (instance)
- `achievesDistinctSums` (definition)
- 5 verified small-case theorems via `native_decide`
- 5 upper-bound theorems `f(n) ≤ …` for `n = 1, 2, 3, 4, 5`
- `conwayGuySeq` definition for `n ≤ 8` (OEIS A005318)
- `conwayGuyConjecture` Prop (unverified, stated as the open frontier)
- 4 private support lemmas for the binary-representation argument
- `powers_of_two_dss` theorem: universal upper bound `f(n) ≤ 2^n − 1`

---

## Dead Ends

- **Defining `conwayGuySeq` as primitive recursion on `ℕ`** without carrying the partial sum fails because the recurrence references `S_{n-1} = ∑_{i<n} a_i`, which is a function of the entire history. The current file's list-based definition is a pragmatic workaround.

- **`omega` on `2 ^ i < 2 ^ n`**: must be discharged via `Nat.pow_lt_pow_right`, not `omega` directly (omega does not unfold `Nat.pow`).

---

## Open lines

1. **Lever A**: extend `dss_conway_guy_*` to `n = 6, 7, 8` via `native_decide` (1 session).
2. **Lever B**: formalize Erdős' counting-argument lower bound `f(n) ≥ (2^n − 1)/n` (2–3 sessions).
3. **Lever C**: formalize Elkies' Fourier-based improvement `f(n) ≥ (1/2 + o(1)) · 2^n / √n` (multi-session research project).
