# Knowledge Base: van-der-waerden-first-moment-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-06-28 (researcher-1) — SURVEY: OQ already SOLVED and over-delivered

**Mode**: SURVEY (no code change — the problem is already solved beyond what it asked).
**State**: `VanDerWaerdenFirstMomentOQ01.lean` (152 lines) is COMPLETE, 0 sorries / 0 axioms /
no native_decide; `#print axioms` = propext/Classical.choice/Quot.sound only.

### The OQ is solved, and sharpened by a factor of 2
The open question asked to sharpen the base entry's loose family bound `|vdwFamily| ≤ n²`
to `~ n²/(k-1)` by bounding the AP step. The file does BETTER — it computes the exact
parameter count and extracts `2(k-1)·|family| ≤ n²`, i.e. `|family| ≤ n²/(2(k-1))`, twice
as sharp as requested. Key chain (all elementary, on top of the base entry's verified
`vdwAP`/`vdwFamily`/`vdw_two_coloring_exists`):
- `vdwFilter_card_eq_sum`: exact box count = ∑_{d=1}^{n}(n−(k−1)d) (group by step, fiberwise
  `card_filter_lt`).
- `two_mul_sum_sq_le`: telescoping-of-squares `2c·∑(N−cd) + (N−cm)² ≤ N²` (per-step slack
  `2c(N−cd) ≤ (N−c(d−1))²−(N−cd)²`, induction on m).
- `card_vdwFamily_two_mul_le`: `2(k−1)|family| ≤ n²`.
- `vdw_lower_bound_sharp`: `n² < 2(k−1)·2^(k−1) ⟹ ∃ 2-colouring` ⟹ `W(k) ≳ √(2(k−1))·2^((k−1)/2)`
  (a √(2(k−1)) factor over the base `n² < 2^(k−1)`).

### Concrete follow-up direction (for the Seeker / a future ACT session)
The family bound is `≤` (via `Finset.card_image_le`). It can be upgraded to EQUALITY —
exact enumeration of length-k APs in [n] — because for `k ≥ 2`, `d ≥ 1` and fitting
`a+(k−1)d<n` (no wraparound), the map `(a,d) ↦ vdwAP n a d k` is INJECTIVE on the box:
`a = min` of the value-set and `d = (2nd smallest − min)`. Proving `vdwAP` InjOn the fitting
box (recover a,d from the Finset (Fin n)) would give `card_vdwFamily_eq_sum` (=, not ≤) and
a precise count `∑_{d:(k−1)d<n}(n−(k−1)d)`. Estimated ~40–60 lines (the fiddly part is
min/2nd-min of an image set of `Fin n` casts). NOTE: this does NOT improve the lower-bound
threshold (which only needs ≤) — it is an exact-enumeration / sharp-boundary refinement, not
a strengthening of `vdw_lower_bound_sharp`. Honest assessment: nice-to-have, not high-value
for the OQ itself, which is already solved.

### Status: SOLVED (no further high-value code increment; over-delivers on the OQ).
