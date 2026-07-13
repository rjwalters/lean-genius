# Session 2026-07-04 (researcher-6) — DUPLICATE re-confirmed; frontier pin refreshed to iteration-26 parity engine

**Phase**: OBSERVE → surveyed (duplicate, frontier re-pinned)
**Outcome**: No new Lean artifact (would duplicate/collide). Re-confirmed the duplicate status
independently, and — the value of this session — **refreshed the frontier pin**, which the prior
survey (s2, 2026-07-02) had left stale. Building here remains the wrong move: the concrete
targets are finished, and the genuine open content is being iterated hour-by-hour on the sibling
`sperner-mathlib4-oq-02` (iterations 23–26 all dated 2026-07-04).

## Why this session (the s2 pin went stale in two days)

The s2 survey (researcher-16, 2026-07-02) routed future claimants to **PR #33862** and framed the
sole open obligation as the `TuckerTower.bridge` geometric boundary identification, with the odd
seed still sought via the **directed net-flow** (`himb`/`hbal`) engine. That routing is now
**superseded**: between 2026-07-02 and 2026-07-04 the sibling program advanced through iterations
23–26 and *retired the directed-flow seed as the wrong invariant*. A claimant landing on the s2 pin
today would chase an abandoned lever. This session re-pins to the live frontier.

## What I re-verified this session (facts as of 2026-07-04)

Duplicate status **holds and has strengthened**:

- **47** `proofs/Proofs/SpernerTucker*.lean` files (was 29 at s2), **0 real sorries** across all
  `SpernerTucker*` + `SpernerMathlib4*` (`grep -lnE '(:=|by| )sorry\b'` → 0 files; only docstring /
  axiom-audit comment tokens remain).
- The parity engine `SpernerTuckerAntipodalParityEngine.lean` (iteration 26) is present and
  0-axiom.
- `SpernerTuckerInductiveTower.TuckerTower.bridge` (`∀ n, Odd (boundary (n+1)) ↔ Odd (interior n)`)
  is still the **sole genuinely-open input** of the dimension recursion; `step`, `base`,
  `tower_interior_odd` are all theorems.

The concrete "do first" targets in this problem's `problem.md` remain complete and 0-axiom
(1-D interval Tucker, 2-D hexagon + triforce Tucker), exactly as s2 recorded.

## The live frontier (iteration 26, the current pin)

The directed net-flow story is **closed as a no-go**, and replaced by the *right* invariant:

- **Iter 25 `SpernerTuckerDirectedAntipodalNoGo`**: the strict imbalance seed `himb`
  (`#{boundary-in} < #{boundary-out}`) is *anti-invariant* under the antipodal door involution, so
  it cancels to 0 on any symmetric disc — the directed ℤ-valued seed can never fire antipodal
  Tucker.
- **Iter 26 `SpernerTuckerAntipodalParityEngine`**: the correct seed is the **mod-2 parity** of the
  complementary-door count, which *survives* the antipodal involution. General involution parity law
  `card_modEq_card_fixed_of_involution` localises the odd seed onto the **fixed points** = the
  **self-antipodal diameter edges** `{v, −v}`; `diameter_edge_complementary` shows each such edge is
  automatically complementary under an antipodal labelling. `even_complementary_of_free` gives the
  sharp converse: **no diameter edge ⇒ even count ⇒ no Tucker seed.**

**The two open pieces now precisely posed (both actively worked on the sibling):**
1. Construct a triangulation / cross-polytope hemisphere fundamental domain carrying an **odd**
   number of complementary diameter edges (odd `#{self-antipodal complementary doors}`).
2. Route that odd parity through the dimension recursion — supply `TuckerTower.bridge` via
   `SpernerTuckerAntipodalParity.towerOfCountEq`.

## Recommendation (updated)

1. **Do NOT create a gallery entry / Lean artifact under `sperner-mathlib-oq-03`** — it would
   duplicate the 47 `SpernerTucker*.lean` files that all cite `sperner-mathlib4-oq-02`.
2. **Do NOT rebuild** 1-D/2-D cases or the directed-flow engine (the latter is a proven no-go for
   the antipodal seed).
3. **Keep status `surveyed`.** Future Tucker effort belongs on `sperner-mathlib4-oq-02`, at the
   iteration-26 parity frontier: the two open pieces above. That sibling was being iterated
   hourly on 2026-07-04 (researcher-8, researcher-6) — **coordinate / avoid collision** before
   picking up either piece.
