# Iteration 38 ACT — 28b-2 witness saturation SHIPPED (build verified)

**Date**: 2026-05-28
**Researcher**: researcher-1
**Phase**: ACT (ships Iter 36 PREP §2–§5 paste-ready code as Lean, discharging both residual `sorry`s)
**Branch**: `research/basel-iter38-act-28b2-*` (off `main`)
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from Iter 36 PREP audit)

## TL;DR

Shipped the long-pending **28b-2 witness saturation** lemma, the missing `=` (tight)
companion to Iter 34a's `factorization_succ_mul_choose_le_log_succ` (28b-1, the `≤`
direction). Three new declarations, **0 sorries, 0 new axioms**, build verified
3066/3066 jobs. The two residual `sorry`s that Iter 36 PREP §5 left open
(the `k = p^a·(m − p^f)` arithmetic and the filter-equality/carry-count discharge)
are both fully closed.

| Declaration | Kind | LOC | Role |
|---|---|---:|---|
| `pow_sub_one_mod_pow` | private lemma | ~30 | Helper 1: `(p^e − 1) % p^i = p^i − 1` for `i ≤ e` |
| `witness_mod_pow_lt` | private lemma | ~30 | Helper 2: `1 ≤ (p^a·(m − p^f)) % p^i` for the witness residue |
| `exists_witness_choose_saturates_log_succ` | theorem | ~75 | Main: `∃ k ≤ n, v_p(n+1) + v_p(C(n,k)) = log_p(n+1)` |

File: 1642 → **1802 LOC** (+160). Sorries: 0 → 0. Axioms: 1 → 1 (`hanson_bound`
unchanged). theorem/lemma count: 74 → **77**.

## What shipped

### Helper 1 — `pow_sub_one_mod_pow {p e i} (hp : 1 < p) (hie : i ≤ e)`
`(p ^ e - 1) % p ^ i = p ^ i - 1`. Proof: `i = 0` closes by `simp [Nat.mod_one]`;
for `i ≥ 1`, write `p^e = p^i · c` (`Nat.pow_dvd_pow`), rearrange
`p^e − 1 = (p^i − 1) + p^i·(c − 1)` (omega over the multiplicative identity
`p^i·c = p^i·(c−1) + p^i`), then `Nat.add_mul_mod_self_left` + `Nat.mod_eq_of_lt`.

### Helper 2 — `witness_mod_pow_lt {p a m f i j} (hp_prime) (hia : i = a+j) (hj_pos) (hf_pos) (hpf_lt : p^f < m) (hmp : ¬ p ∣ m)`
`1 ≤ (p^a · (m − p^f)) % p^i`. Proof: `p^i = p^a·p^j` (`pow_add`),
`Nat.mul_mod_mul_left` factors out `p^a`; then `p^j ∤ (m − p^f)` (else
`p ∣ m` via `dvd_pow_self` + `Nat.sub_add_cancel`, contradicting `hmp`), so
`(m − p^f) % p^j ≥ 1` and `Nat.mul_pos` finishes.

**Note (cleanup vs PREP)**: the PREP's `j ≤ f` hypothesis turned out to be
**unnecessary** — the `p ∤ m` contradiction holds for any `j ≥ 1`. Dropped it,
making the helper strictly more general. (Caught as an unused-variable warning
on the first verified build; removed and re-verified.)

### Main — `exists_witness_choose_saturates_log_succ {p} (hp : p.Prime) {n} (hn : 1 ≤ n)`
`∃ k, k ≤ n ∧ (n+1).factorization p + (C n k).factorization p = log_p (n+1)`.
Witness `k₀ = (n+1) − p^e`, `e = log_p(n+1)`. Case split on `n+1 = p^e`:

- **Case A** (`n+1 = p^e`): `k₀ = 0`, `C(n,0) = 1`, reduces to `v_p(p^e) = e` via
  `Nat.Prime.factorization_pow` + `Finsupp.single_eq_same`.
- **Case B** (`p^e < n+1`): write `n+1 = p^a·m` with `p ∤ m`
  (`Nat.not_dvd_ordCompl`) and `f = e − a`. The carries-set of
  `Nat.factorization_choose` is proved to equal **exactly** `Ico (a+1) (e+1)`:
  the lower bound (`i > a`) reuses Iter 34a's `sum_mod_pow_lt_of_pow_dvd_succ`;
  the upper bound (`i ≤ e ⇒ carry`) combines Helper 1 (the `(n−k₀) % p^i` term)
  and Helper 2 (the `k₀ % p^i ≥ 1` term). Card `= e − a` via `Nat.card_Ico`;
  `a + (e − a) = e`.

## Significance

This is the **tightness certificate** for the 28c divisibility bridge
(`choose_mul_succ_dvd_lcmRange`, Iter 35b): together, 28b-1 (`≤`) and 28b-2 (`=`)
show that along the witness path `k₀`, `(n+1)·C(n,k₀)` exhausts the full
`p`-adic valuation budget `log_p(n+1)` of `lcmRange(n+1)` at each prime.

What remains in the Route B chain toward discharging `axiom hanson_bound`:
1. **28a Beta-integral identity** (Iter 29 PREP #18485 only; Mathlib lacks it in
   rational-denominator form; ~60–100 LOC) — independent of this work.
2. Integer-squeeze assembly once 28a lands + `n₀ ≤ 100` (numerical floor
   `hanson_n1..hanson_n100` provides slack).

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03
⚠ [3066/3066] Built Proofs.BaselProblemOQ01OQ01OQ02OQ03
Build completed successfully (3066 jobs).
```

Warnings: 3 pre-existing (line 97 unused `hn`, line 270 `Finsupp.not_mem_support_iff`
deprecation, line 650 unused `hp`) — all inherited, none introduced by this ACT.

## Honesty / self-audit

- **No new axioms, no sorries.** `axiom hanson_bound` is untouched; this ACT does
  not close the parent open conjecture, only ships one of its remaining sub-lemmas.
- Helper 1 / Helper 2 / Case A / Case B all machine-checked at the pinned SHA.
- ACT-time fallbacks vs Iter 36 PREP: `Nat.pow_pos` takes its exponent implicitly
  at v4.26.0 (4 call sites fixed); Helper 1's `i=0` branch needed explicit
  `Nat.mod_one`; the PREP's `Nat.mul_le_mul_left` / `Nat.dvd_iff_mod_eq_zero`
  risk points were sidestepped with `Nat.mul_pos` / `Nat.dvd_of_mod_eq_zero`;
  `hmp` used `Nat.not_dvd_ordCompl` (PREP Option B) rather than the
  `Nat.factorization_le_of_dvd` chain. Total ACT-time edits: 1 rebuild for the
  `Nat.pow_pos`/`Nat.mod_one` fixes, 1 rebuild for the unused-hypothesis cleanup.
