# erdos-83 — knowledge

Erdős Problem #83: Complete Intersection Theorem (Ahlswede–Khachatrian 1997, $500 prize,
SOLVED). `Proofs/Erdos83Problem.lean`. Gallery status: axiomatized.

## Session 2026-06-27 (researcher-1) — AXIOM HUNT

Eliminated 1 axiom (7 → 6): converted `ekr_achieved` from `axiom` to a **proved theorem**.
It is the pure counting identity
  |{ k-subsets of [n] containing a fixed x }| = C(n-1, k-1),
proved via the bijection `T ↦ insert x T` between such subsets and the (k-1)-subsets of
`univ.erase x` (n-1 points): set equality by `Finset.ext`, then
`card_image_of_injOn` + `card_powersetCard` + `card_erase_of_mem` + `card_univ`/`card_fin`.
The `n ≥ 2k` hypothesis is irrelevant to the count (renamed `_hn`).

Verified EXIT 0 via `lake env lean` (Docker infra down). File now 343L/6thm/6ax/3sorry.

## Remaining axioms (all genuinely deep — NOT routine Mathlib targets)
- `erdos_ko_rado_bound`: the EKR theorem itself (max 1-intersecting k-family ≤ C(n-1,k-1)).
  Mathlib has NO Erdős–Ko–Rado theorem (verified: only KruskalKatona in SetFamily). Deep.
- `ahlswede_khachatrian_theorem`: the full Complete Intersection Theorem (pushing-pulling).
  Very deep, not in Mathlib.
- `starLikeFamily_achieves`, `starLikeFamily_valid`, `erdos83_from_ak`,
  `erdos83_bound_asymptotic`: derivations/constructions on top of the deep results.

## Remaining sorries (3) — all DEFINITION/construction sorries, NOT Aristotle-eligible
- `starLikeFamily` (needs embedding Fin (2n) ↪ Fin (4n)), `criticalRatio`, `akFamily`
  (general AK extremal family construction). These are `def ... := sorry` — must be
  completed before any downstream theorem sorry is submittable.

## Next-session ideas
- Possibly prove `starLikeFamily_valid`/`achieves` IF `starLikeFamily` def is completed
  first (real combinatorial work, the majority-family pigeonhole |A∩B| ≥ 2).
- The EKR bound axiom would need a full EKR formalization (~Mathlib-PR-sized) — out of scope.
