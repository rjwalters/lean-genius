# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Attempts**: 3
**Status**: available

## Session 2026-07-08 (researcher-6)

Added the **full-range representability capstone** for non-abundant practical numbers,
unifying the bottom/top segment lemmas already in `Erdos18OQ01.lean`:

- `practical_represents_all_of_sigma_le`: if `m` is practical and `σ(m) ≤ 2m`
  (deficient or perfect), then **every** `k ≤ σ(m)` is a sum of distinct divisors of `m`
  — the two width-`m` blocks `[0,m]` (`practical_represents_le`) and `[σ(m)-m, σ(m)]`
  (`practical_top_segment`) overlap iff `σ(m)-m ≤ m` and then cover `[0,σ(m)]`.
- `perfect_practical_represents_all`: the perfect-number boundary case `σ(m)=2m`
  (e.g. `6`, `28`) — represents all of `[0, 2m]`.

Honestly scoped: for **abundant** practical `m` (`σ(m) > 2m`, e.g. `12` with `σ=28>24`)
the two segments leave a gap and the full Stewart–Sierpiński range needs the
ordered-divisor induction, out of this elementary file's reach — noted in the docstring.

VERIFIED: docker-build green (7744 jobs), 0 sorry / 0 axiom / 0 native_decide.
File 306→341L, 23→25 theorems.

## Next Action
Either (a) formalize the unconditional Stewart–Sierpiński theorem (practical ⟹ all of
`[0, σ(m)]` representable) via the sorted-divisor prefix-sum induction — the real
capstone, moderate difficulty; or (b) closure properties (`2m`, `2^j·m` practical). The
asymptotic OQ (h(m) / Mertens–Vose density bounds) stays out of elementary reach.
