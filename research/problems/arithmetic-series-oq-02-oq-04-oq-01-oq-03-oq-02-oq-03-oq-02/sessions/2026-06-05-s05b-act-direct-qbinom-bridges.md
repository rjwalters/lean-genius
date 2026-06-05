# S5b ACT — Direct bridges to the parent's qBinom / qMultichoose

**Researcher**: researcher-1
**Date**: 2026-06-05
**Phase**: ACT (S5b ACT, follow-up to S5 ACT polynomial-form bridges)
**Outcome**: 4 theorems shipped (~50 LOC added), Docker-verified 7745/7745 jobs

## §0 — TL;DR

Four new theorems close the bridge chain from the polynomial sub-lattice
of `qtMultichoose` at `k ≤ 1` directly to the parent gallery entry's
named objects (`qBinom`, `qMultichoose`), without going through
`qNumber`. The previous S5 ACT (2026-06-01) bridged to `qNumber`;
this iteration composes those with the parent's
`qBinom_one_right` / `qMultichoose_one_right` and the trivial
boundary cases:

1. `qtBinom_zero_right_eq_qBinom` (unconditional) — `k = 0`, both = 1.
2. `qtMultichoose_zero_right_eq_qMultichoose` (unconditional) — corollary.
3. `qtBinom_one_right_eq_qBinom` (under `1 - q ≠ 0`) — `k = 1`,
   composes `qtBinom_one_right_eq_qNumber` (S5 ACT) with the parent's
   `qBinom_one_right`.
4. `qtMultichoose_one_right_eq_qMultichoose` (under `1 - q ≠ 0`) —
   headline, the direct `qMultichoose`-form bridge at `k = 1`.

All four are short composition lemmas (≤ 4 tactic steps each); no new
Mathlib infrastructure, no new private helpers. The file grows from
**428 LOC / 13 theorems** to **~480 LOC / 17 theorems**, **0 sorries /
0 axioms** maintained.

## §1 — Context: why a follow-up to S5 ACT

The S5 ACT (researcher-1, 2026-06-01) shipped three bridges to `qNumber`:

- `qtBinom_one_right_eq_qNumber q t N (hq : 1 - q ≠ 0) : qtBinom q t N 1 = qNumber q N`
- `qtMultichoose_one_right_eq_qNumber q t n (hq : 1 - q ≠ 0) : qtMultichoose q t n 1 = qNumber q n`
- `qtMultichoose_two_two_eq_qNumber q t (htq) (hq) : qtMultichoose q t 2 2 = qNumber q 3`

Those bridges are mathematically the natural target: `qNumber q n =
1 + q + q² + ⋯ + q^(n-1)` is the most "visible" polynomial form.
But the parent gallery entry's *named object* in the meta.json sense
is `qMultichoose`, not `qNumber`. A reader landing on the parent
entry's `qMultichoose q n 1 = qNumber q n` and wanting to see the
analogous (q,t)-statement must currently traverse two hops:

  `qtMultichoose q t n 1 = qNumber q n = qMultichoose q n 1`

with the first hop given by S5 ACT and the second by the parent's
`qMultichoose_one_right`. This iteration **fuses** those two hops
into a single bridge:

  `qtMultichoose q t n 1 = qMultichoose q n 1`  (S5b ACT)

making the (q,t) and the q presentation of the parent's polynomial
sub-lattice point at `k = 1` formally identical (modulo the
non-degeneracy hypothesis).

The same fusion is given at `qtBinom` level
(`qtBinom q t N 1 = qBinom q N 1`) and trivially at `k = 0` (both
sides = 1, no hypothesis needed).

The `(n, k) = (2, 2)` interior point is **NOT** included in this
iteration's bridge chain because the parent's `qMultichoose q 2 2`
expands as `qBinom q 3 2 = qFactorial q 3 / (qFactorial q 2 * qFactorial q 1)`
which evaluates to `qNumber q 3` only via a multi-step calculation
in the parent. A future S5c ACT could add
`qtMultichoose_two_two_eq_qMultichoose` once a parent-side bridge
`qMultichoose q 2 2 = qNumber q 3` is in the parent file (it is not
currently a named theorem).

## §2 — What landed

### `qtBinom_zero_right_eq_qBinom` (unconditional)

```lean
theorem qtBinom_zero_right_eq_qBinom (q t : R) (N : ℕ) :
    qtBinom q t N 0 = qBinom q N 0 := by
  rw [qtBinom_zero_right, qBinom_zero_right]
```

Both sides are 1 by their respective boundary lemmas.

### `qtMultichoose_zero_right_eq_qMultichoose` (unconditional)

Same pattern lifted to `qtMultichoose`.

### `qtBinom_one_right_eq_qBinom` (under `1 - q ≠ 0`)

```lean
theorem qtBinom_one_right_eq_qBinom (q t : R) (N : ℕ)
    (hq : (1 - q : R) ≠ 0) :
    qtBinom q t N 1 = qBinom q N 1 := by
  rw [qtBinom_one_right_eq_qNumber q t N hq, ← qBinom_one_right]
```

Composes the S5 ACT bridge to `qNumber` with the parent's
`qBinom_one_right : qBinom q N 1 = qNumber q N` (used as a
right-to-left rewrite).

### `qtMultichoose_one_right_eq_qMultichoose` (under `1 - q ≠ 0`)

Same pattern lifted to `qtMultichoose`. Headline S5b ACT statement —
connects the (q,t)-multichoose at `k = 1` directly to the parent
gallery's q-multichoose.

## §3 — Build status

**Docker-verified clean**:

```
./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02
→ ✔ [7745/7745] Built ... === Build succeeded ===
```

Mathlib v4.26.0; no new imports or infrastructure required.

## §4 — Counts after S5b ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | ~480 | **17** | 0 | 2 | 0 |

(Up from 428 LOC / 13 theorems at end of S5 ACT.)

## §5 — Mathematical content

Pure-composition iteration: no new mathematical content, just exposing
facts implicit in the chain
`qtMultichoose_one_right_eq_qNumber ∘ qMultichoose_one_right⁻¹`. The
novelty is **naming** the bridges at the parent gallery's named-object
level (`qBinom`/`qMultichoose`), which is the level downstream
consumers (gallery `meta.json`, peer-reviewer, mechanic) will reference.

## §6 — Remaining work (unchanged)

- **Path C (`RatFunc`) migration**: still the canonical route to the
  positive `qtMultichoose 1 1 n k = Nat.multichoose n k`. ~80–120 LOC,
  multi-session.
- **S5c ACT (optional)**: add a parent-side `qMultichoose q 2 2 = qNumber q 3`
  lemma and then `qtMultichoose_two_two_eq_qMultichoose` here.
- **S6 ACT (axiomatised, optional)**: Macdonald polynomial
  principal-specialization identity.
- **S7**: gallery JSON integration with `status: "axiomatized"`. With
  S5b ACT in place, the gallery `meta.json` can directly quote
  `qMultichoose q n 1` and `qBinom q N 1` rather than `qNumber`-form
  values.

## §7 — Honesty

This iteration:

- Adds 4 new theorems (composition lemmas, ≤ 4 tactic steps each).
- ~50 LOC added including doc.
- 0 sorries / 0 axioms net (file remains sorry-free + axiom-free).
- Docker-verified clean at 7745/7745 jobs.
- No new mathematical content; no new Mathlib infrastructure used.

The contribution is **expository**: making the polynomial-form bridge
chain land at the parent gallery's named objects, not just at
`qNumber`. This makes the eventual S7 gallery integration trivially
quotable from the parent gallery entry's vocabulary.

The file's status remains `axiomatized`-bound (since the positive
`at_one_one` recovery still requires Path C); but the **presentation**
of the polynomial sub-lattice for the eventual `meta.json` is now
fully aligned with the parent gallery entry's named objects.
