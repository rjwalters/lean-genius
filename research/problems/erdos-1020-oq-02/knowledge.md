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
