# Erdős #1204 - Knowledge Base

## Problem Statement

We call a sequence of integers $0\leq a_1<\cdots <a_k$ admissible if it is missing at least one congruence class modulo every prime $p$. Let $A(k)=\min a_k$. Estimate $A(k)$ - in particular, is it true that\[A(k)\sim k\log k?\]Estimate\[B(k)=\min \frac{a_1+\cdots+a_k}{k}.\]

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #60
- Problem #2
- Problem #855
- Problem #1203
- Problem #1205
- Problem #39
- Problem #1

## References

- Er80
- HeRi73
- Po14c
- El65

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-04-16*

## Session 2026-06-25 (researcher-1) — structural properties + well-definedness of A(k)

Added 4 verified theorems (now 10 thm/1 def, 0 axioms, 0 sorries):
- `Admissible.subset` — downward closure (subset of admissible is admissible).
- `admissible_image_add` — translation invariance (a ↦ a+t preserves admissibility);
  `card_image_add` — translation preserves cardinality.
- `exists_admissible_card` — **an admissible k-set exists for every k** (multiples
  0,N,2N,…,(k-1)N of the primorial N=∏_{p≤k}p), so **A(k) is well-defined**, with the
  explicit weak upper bound A(k) ≤ (k-1)·∏_{p≤k}p.

Insight: admissibility is a property of the *pattern*, not the position. The headline
A(k)∼k log k and B(k) estimate remain OPEN (need sieve theory).

Gotcha: `(N:ZMod p)=0` from `p∣N` via `CharP.cast_eq_zero_iff (ZMod p) p N` (no NeZero needed,
unlike `ZMod.natCast_zmod_eq_zero_iff_dvd`); `push_cast` then `rw [hp0, mul_zero]; exact zero_ne_one`.
