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

## Session 2026-06-25 (researcher-8) — defined A(k) + trivial regime exact values

Added 8 verified theorems + 1 def (now 18 thm / 2 def, 0 axioms, 0 sorries):
- `A (k : ℕ) : ℕ := sInf {a.sup id | a admissible, a.card = k}` — **the central object A(k)
  is now actually defined in Lean** (previously only `Admissible` + existence existed). This
  makes the headline question "A(k) ∼ k log k?" expressible. Uses `a.sup id` (max, ∅↦0) for totality.
- `A_set_nonempty`, `A_mem` — the family is nonempty (via `exists_admissible_card`), so the
  infimum is **attained**: ∃ admissible k-set with max exactly A(k).
- `A_le` — A(k) is a genuine lower bound on the max of any admissible k-set (`Nat.sInf_le`).
- `card_le_sup_succ` (a.card ≤ a.sup id + 1) ⇒ `sub_one_le_A`: **A(k) ≥ k-1** (packing bound).
- `A_zero = 0`, `A_one = 0`, `A_two = 2` exact. **A(2)=2 > 1=k-1** is the first place
  admissibility is *binding*: the densest 2-set {0,1} is inadmissible, forcing the max above
  the packing bound. (Lower bound: a 2-set with max 1 must be {0,1} = not admissible.)

Still OPEN: the asymptotics A(k)∼k log k and B(k) (need sieve theory). The new content brackets
A(k) between k-1 and (k-1)·primorial and nails the trivial small-k regime.

Gotchas: `A_le` k is implicit — `(by decide)` for `card {0,2} = k` fails with "Expected type must
not contain metavariables"; pass `(k := 2)` explicitly. `a.sup id ≥ k-1` via `a ⊆ range (sup+1)`
+ `Finset.le_sup (f := id)`. `Nat.sInf_mem`/`Nat.sInf_le` give attainment + lower bound directly.
