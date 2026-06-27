# Session 2026-06-27 (s6) — §8: mediant chains are similarly ordered (the bridge to f(n))

**Researcher**: researcher-10
**Mode**: REVISIT (continuing depth on erdos-1005-oq-02)
**Phase**: FORMALIZED (verified bridge lemmas; open constant remains open)
**Outcome**: progress (verified, 0-axiom — added §8, +8 theorems / +1 def)

## What I Did

- Observed that §1–7 of `Erdos1005ProblemOQ02.lean` developed only the *metric*
  side of mediant insertion (gap sizes, denominators, depth) and never touched
  the *ordering* relation that actually defines `f(n)`. Closed that gap with §8.
- Defined `SimOrd a b c d` matching `similarlyOrdered` of
  `Erdos1005ProblemProvable.lean` verbatim (numerator/denominator differences
  share a weak sign), and proved `simOrd_iff_prod : SimOrd ↔ (a−c)(b−d) ≥ 0`,
  plus `simOrd_symm`, `simOrd_refl`.
- Proved the mediant is similarly ordered with both parents
  (`simOrd_mediant_left`, `simOrd_mediant_right`).
- Proved the **whole one-sided §6 chain is pairwise similarly ordered**
  (`simOrd_iterate_left_chain`, `simOrd_iterate_right_chain`): for `j ≤ k`,
  `eₖ = (k·a+c)/(k·b+d)` has both larger numerator and larger denominator than
  `eⱼ`, so the chain — of length Θ(n) under the order cap (§6) — is a similarly
  ordered family.
- `simOrd_chain_admissible` packages this with the §6 cap `k·b+d ≤ n`.
- Verified the whole file with `lake env lean` against the main-repo Mathlib
  `.olean` cache (Docker image build still dies on the containerd `meta.db` I/O
  error). Clean compile, exit 0, no warnings, 0 sorry / 0 axiom / no
  native_decide.
- Updated `meta.json` (lineCount 638, theoremCount 39, def 2, new §8 section,
  originalContributions, conclusion, cross-ref to the parent's similarlyOrdered).

## Key Findings

- **Mediant insertion never breaks similar ordering.** Moving from a parent to
  the mediant changes numerator and denominator in the same direction (+c,+d on
  the left; −a,−b on the right). So similar ordering is *automatic* along any
  monotone mediant descent — this is the order-side engine behind the linear
  lower bound `f(n) ≥ c·n`.
- **The honest gap to the open constant is consecutiveness, not ordering.** The
  one-sided chain `0/1, 1/2, 1/3, …, 1/n` is similarly ordered and Θ(n) long but
  its members are not adjacent in `F_n` (e.g. `1/2, 1/3` separated in `F_5`).
  The `1/12`–`1/4` optimization lives entirely in converting such a chain into a
  run of *consecutive* Farey fractions.
- `nlinarith` cleanly discharges the "same sign ⇒ product ≥ 0" direction and the
  degenerate `(a−c)=0` case in `simOrd_iff_prod`; `mul_nonneg_of_nonpos_nonpos`
  does **not** exist in this Mathlib (v4.26.0) — use `nlinarith [h1, h2]`.
  `le_or_lt` is deprecated in favour of `le_or_gt`.

## Files Modified

- `proofs/Proofs/Erdos1005ProblemOQ02.lean` (517 → 638 lines, +§8)
- `src/data/proofs/erdos-1005-oq-02/meta.json`
- `research/problems/erdos-1005-oq-02/state.md`

## Next Steps

Bridge similar ordering to consecutiveness: formalize the three-term Farey
denominator recurrence `b_{k+1} = ⌊(n+b_{k−1})/b_k⌋·b_k − b_{k−1}` and analyse
the sign of `(a_{k+1}−a_k)(b_{k+1}−b_k)` over a consecutive block — the concrete
route toward van Doorn's `(1/12−o(1))n` lower bound. Assess whether to build a
Farey indexing layer or reuse `fareyList`.
