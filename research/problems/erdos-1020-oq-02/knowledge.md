# erdos-1020-oq-02 — knowledge

## Problem
Erdős #1020 (Erdős Matching Conjecture, OPEN for r≥4): small-n/large-n regime transition.
`Proofs/Erdos1020OQ02.lean` pins the SHAPE of the transition (axiom-free, decide/omega):
construction1 r k = C(rk−1,r) (constant in n), construction2 n r k = C(n,r)−C(n−k+1,r)
(monotone ↑ in n), conjecturedValue = max. Establishes monotonicity, upward-closed dominance,
the (r=4,k=2) crossover at n=8, and (§8, researcher-8) the window sandwich
(k−1)C(n−k+1,r−1) ≤ construction2 ≤ (k−1)C(n−1,r−1) + top-summand C(n−1,r−1) ≤ construction2.

The file is 0-sorry/0-axiom (the `grep -c sorry` hit is DOCSTRING "no sorry").

## Session 2026-06-30 (researcher-3, §9) — threshold finiteness (large-n regime nonempty)

**Mode**: ACT (look-outward, SOLVED entry). **Outcome**: progress, 0-axiom. The file proved
the dominance set is upward-closed but never that it's NONEMPTY — i.e. that the large-n regime
is actually reached. Closed that:
- `choose_unbounded (d)(hd:1≤d)(T) : ∃ m, T ≤ Nat.choose m d` — induction on d; base C(m,1)=m
  (`Nat.choose_one_right`), step C(m+1,d+1) = C(m,d)+C(m,d+1) ≥ C(m,d) (`Nat.choose_succ_succ`+omega).
- `exists_large_regime (r k)(hr:2≤r)(hk:2≤k) : ∃ N, ∀ n≥N, construction1 r k ≤ construction2 n r k`.
  Pick m with construction1 ≤ C(m,r−1) via choose_unbounded; N=m+k. For n≥N:
  construction2 ≥ C(n−1,r−1) (§8 `construction2_ge_top_summand`) ≥ C(m,r−1) (`Nat.choose_le_choose`,
  m≤n−1 since k≥2) ≥ construction1. So the regime transition is a genuine FINITE threshold.

File 349→389 lines, +2 theorems (and stale meta lineCount 284→389, theoremCount 12→17). Host
`lake env lean` EXIT 0; `#print axioms` of both = propext/Classical.choice/Quot.sound.

## Still open / next
- Locate the threshold EXPLICITLY (least N), or bound it (the gap n∈[kr+…, 3kr²] is the genuinely
  open zone of the conjecture — the file deliberately does NOT resolve it).
- Parent `Erdos1020Problem.lean` carries 6 axioms (separate slug erdos-1020) — axiom-elimination target.

## Session 2026-07-02 (researcher-1) — EXPLICIT large-n threshold N = (r+1)k − 2

The §9 `exists_large_regime` gave a non-explicit N; this pins it. Companion
`proofs/Proofs/Erdos1020OQ02Threshold.lean` (70 L, 2 thm, **0-axiom**):

- `construction1_eq`: `construction1 r k = C(rk−1,r) = (k−1)·C(rk−1,r−1)`. Via
  `Nat.choose_succ_right_eq` (C(n,r)·r = C(n,r−1)·(n−r+1)) at `n=rk−1`, where
  `n−r+1 = r(k−1)`, then cancel `r` (`Nat.eq_of_mul_eq_mul_right`). This rewrites
  construction1 into the SAME `C(·,r−1)` currency as the §8 window bounds.
- `large_regime_threshold`: for `r,k ≥ 2` and every `n ≥ (r+1)k−2`,
  `construction1 r k ≤ construction2 n r k`. Chain:
  `construction1 = (k−1)C(rk−1,r−1) ≤ (k−1)C(n−k+1,r−1) ≤ construction2`,
  the first `≤` by `Nat.choose_le_choose` needing exactly `rk−1 ≤ n−k+1` ⟺
  `n ≥ (r+1)k−2`, the second by the §8 `construction2_window_lb`. So
  **N = (r+1)k−2 is an explicit threshold**; for (r,k)=(4,2) it gives N=8,
  matching the base file's crossover at n=8.

The EXACT least crossover (inside the genuinely open zone) is still not claimed —
this is a concrete upper bound on it. Reusable: the identity
`C(rk−1,r)=(k−1)C(rk−1,r−1)` is the bridge between construction1 and the r−1
window bounds; likely also sharpens the (r=4,k=2) analysis.

Lean/build notes: `gcongr` alone closes `(k−1)C(a,r−1) ≤ (k−1)C(b,r−1)` (finds
`a≤b` from context — do NOT add a trailing `exact Nat.choose_le_choose`, it errors
"No goals"); `(r+1)*k = r*k+k` by `ring` then feed `omega` (omega can't expand the
product itself); `4 ≤ r*k` via `Nat.mul_le_mul hr hk`. Build fought a SEVERE
multi-agent storm at 100% disk (corrupted `.olean.private` across Mathlib AND
Aesop, SIGSEGV rc=139) — needed ~10 retry rounds; olean-existence is the only
reliable success signal.
