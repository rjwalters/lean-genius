# Knowledge Base: van-der-waerden-first-moment-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Count length-`k` APs in `[n] = {0,…,n-1}`. Each AP is `(a, d)` with first term `a`, step
`d ≥ 1`, fitting iff `a + (k-1)d < n`. Open question asked to sharpen the base entry's
loose `n²` count to the literal `|family| ≤ n·⌊(n-1)/(k-1)⌋ ≤ n²/(k-1)`.

## State (as of 2026-06-30)

`Proofs/VanDerWaerdenFirstMomentOQ01.lean` — **0-sorry, 0-axiom, COMPLETE** (status
`completed`). PR #30969 already proved the *exact* parameter count
`vdwFilter_card_eq_sum` and a **stronger** factor-2 sharpening
`card_vdwFamily_two_mul_le : 2(k-1)|family| ≤ n²` (i.e. `n²/(2(k-1))`, beating the
requested `n²/(k-1)` by a factor 2), via a telescoping-of-squares engine `two_mul_sum_sq_le`.

## Session 2026-06-30 (researcher-2) — added the LITERAL floor-product bound

**Mode:** ACT (enrich the completed entry to literally match the stated target).
**Outcome:** PROGRESS — added **`card_vdwFamily_le_floor {k} (hk : 2 ≤ k) :
(vdwFamily n k).card ≤ n * ((n-1)/(k-1))`** (ℕ division = floor). **Verified 0-axiom**
(`#print axioms = [propext, Classical.choice, Quot.sound]`), host `lake env lean` EXIT 0
(no warnings), docker build OK.

**Why it's not redundant** (the file already has a numerically sharper bound): the
factor-2 bound `n²/(2(k-1))` is *positive* even when `n ≤ k-1`, but in that regime **no**
length-`k` AP of positive step fits, so the floor-product is the **exact** value `0`
(`⌊(n-1)/(k-1)⌋ = 0`). So `card_vdwFamily_le_floor` is strictly sharper for small `n` and
is the exact shape the open question states. Honestly: incremental — reuses the existing
`card_vdwFamily_le_sum`; the content is the indicator-bound + filter-counting wrapper.

### Proof technique (reusable)
From `card_vdwFamily_le_sum : |family| ≤ ∑_{d∈Icc 1 n}(n-(k-1)d)`, bound each summand by
the indicator `if (k-1)d < n then n else 0` (off-support terms vanish by truncated ℕ-sub),
then `← Finset.sum_filter` + `Finset.sum_const` turns it into `n · |filter|`, and the
filter `{d∈Icc 1 n : (k-1)d < n}` equals `Icc 1 ⌊(n-1)/(k-1)⌋` via
`Nat.le_div_iff_mul_le hk1` (needs an explicit `(k-1)*d = d*(k-1)` comm bridge — omega
treats the two products as distinct atoms otherwise). Finish: `Nat.card_Icc`,
`Nat.add_sub_cancel`, `Nat.mul_comm`.

## Dead Ends / Notes

- A clean ℕ corollary `(k-1)|family| ≤ n(n-1)` is **dominated** by the existing factor-2
  bound (`n²/2 ≤ n(n-1)` for `n ≥ 2`), so not worth adding.

## Next steps
- oq-02: replace the union bound by the Lovász Local Lemma form `W(k) ≳ 2^k/(ek)` (needs
  verified symmetric LLL + AP-overlap degree bound).
