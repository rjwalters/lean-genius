# erdos-83 — knowledge

Erdős Problem #83: Complete Intersection Theorem (Ahlswede–Khachatrian 1997, $500 prize,
SOLVED). `Proofs/Erdos83Problem.lean`. Gallery status: axiomatized.

## Session 2026-07-02 (researcher-4) — VALIDITY PROVED + def sorry completed (6→5 ax, 3→2 sorry)

Completed the `starLikeFamily` **definition** (was a `def ... := sorry`) and converted
`starLikeFamily_valid` from an **axiom to a proved theorem**. Verified EXIT 0 via
`lean` against main's prebuilt Mathlib (Docker infra down, worktree reaped mid-session →
rebuilt in locked `/Users/rwalters/lg-r4-erdos83`). `#print axioms` on both new results:
only `propext, Classical.choice, Quot.sound` (no sorry, no custom axioms).

- New `def erdos83Core n := univ.filter (·.val < 2n)` — the fixed 2n-element core.
- New `theorem erdos83Core_card : (erdos83Core n).card = 2*n` via the order-embedding
  `Fin (2n) ↪ Fin (4n)` (`Fin.castLEEmb`): `erdos83Core n = univ.map (castLEEmb h)`, then
  `card_map`/`card_univ`/`Fintype.card_fin`. (Reverse membership: `Fin.coe_castLE` + `j.isLt`.)
- `def starLikeFamily n := univ.powerset.filter (fun S => S.card = 2n ∧ n+1 ≤ (S ∩ core).card)`.
- `theorem starLikeFamily_valid`: k-uniform is immediate from the filter; 2-intersecting is
  pure pigeonhole on the core. Let X=A∩core, Y=B∩core (both ⊆ core, |X|,|Y| ≥ n+1).
  `card_union_add_card_inter X Y` gives |X∪Y|+|X∩Y| = |X|+|Y|; with |X∪Y| ≤ |core| = 2n,
  `omega` yields |X∩Y| ≥ 2; and X∩Y ⊆ A∩B (`card_le_card`) → |A∩B| ≥ 2.

Now 404L / 8thm / 13def / 5 axioms / 2 sorries. Remaining 2 sorries are BOTH `def` sorries
(`criticalRatio`, `akFamily`) — NOT Aristotle-eligible; must be completed before the AK-side
theorems could be attacked. `starLikeFamily_achieves` (exact count = ½(C(4n,2n)−C(2n,n)²))
stays an axiom — genuinely hard enumeration. The 4 deep axioms (EKR bound, AK theorem,
erdos83_from_ak, bound_asymptotic) remain out of scope (no EKR/AK in Mathlib).

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
