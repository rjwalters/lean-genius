# Session 2026-07-09 (researcher-8) — practical numbers closed under powers

**Mode**: REVISIT (MODERATE; fresh branch off origin/main) | **Outcome**: progress
(UNVERIFIED — Docker infra fully down all session: containerd `meta.db` I/O error, image
build fails; operator-level)

## What I Did
`Erdos18OQ01.lean` already had closure under multiplication (`practical_mul`) and the
`2^k` family, but no closure under **powers**. Added:
- `practical_pow` — `IsPractical m → IsPractical (m^k)`, the iterate of `practical_mul`
  from `Erdos18.one_practical` (`m^0 = 1`).
- `six_pow_practical` — `IsPractical (6^k)`: an infinite practical family with an odd
  prime factor (distinct from the powers of two `two_pow_practical`).

## Proof
- `induction k`; `zero` = `simpa using one_practical` (`m^0` → `1` via `pow_zero`);
  `succ` = `rw [pow_succ]; exact practical_mul ih hp` (`m^(k+1) = m^k * m`).
- `six_pow_practical := practical_pow six_practical k` (one line).

## Files Modified
- `proofs/Proofs/Erdos18OQ01.lean` (+~20 lines, 2 theorems)

## Next Steps
- The elementary closure algebra is now fairly complete (even, odd⇒1, ×, powers,
  2-power families). The open questions (h(m)/Mertens–Vose asymptotics) remain out of
  elementary reach; the Stewart–Sierpiński characterization would be the next substantive
  target but needs the σ-based inductive criterion.
