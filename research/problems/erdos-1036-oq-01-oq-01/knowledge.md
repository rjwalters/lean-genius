# Knowledge Base: erdos-1036-oq-01-oq-01

**Problem**: Eliminate the `numISCTrue` interface axioms in the gallery proof
`Erdos1036OQ01.lean` ("Optimal Constant in Shelah's Coloring Theorem") via a
Quotient construction — a Setoid on induced-subgraph pairs, a count on the
quotient, and the bound `cardinality ≤ 2^n`.

**Status**: ACT (S1, 2026-06-15, researcher-8). Wrote
`proofs/Proofs/Erdos1036OQ01OQ01.lean` discharging all three interface axioms as
definitions/theorems. BUILD-PENDING (Docker host down) and left UNREGISTERED in
`Proofs.lean`.

---

## Problem Understanding

The parent `Erdos1036OQ01.lean` carries 6 axioms. Three are a deliberate
*interface* placeholder for the "true ISC count":

- `axiom numISCTrue : SimpleGraph V → ℕ`
- `axiom numISCTrue_le_pow : numISCTrue G ≤ 2 ^ Fintype.card V`
- `axiom numISCTrue_pos : 0 < numISCTrue G`

with a comment that they "would be eliminated by ~200 lines of Quotient type
construction". The intended meaning (file docstring, line 13/44): `numISCTrue G`
is the number of **non-isomorphic induced subgraphs** of `G`, i.e. the number of
isomorphism classes of `{G[S] : S ⊆ V}`.

The other three axioms are genuinely deep and out of scope here:
`nonRamseyExistsTrue`, `shelah_isc` (Shelah's 1998 exponential lower bound), and
`optimalConstantTrue_eq_one` (the headline open conjecture).

---

## Insights

- **Faithful construction.** Put a setoid on `Finset V` by
  `S ~ T  ↔  Nonempty (G.induce ↑S ≃g G.induce ↑T)` (isomorphic induced
  subgraphs). Graph isomorphism is an equivalence relation (`Iso.refl`,
  `Iso.symm`, `Iso.trans`), so this is a genuine `Setoid (Finset V)`. Define
  `numISCTrue G := Nat.card (Quotient (iscSetoid G))`. The quotient's cardinality
  *is*, by construction, the number of isomorphism classes of induced subgraphs.

- **`Nat.card` beats `Fintype.card` here.** The ~200-line estimate comes from
  assuming a `Fintype`/`DecidableEq` instance on the quotient is needed — which
  would force *deciding graph isomorphism* (constructing `Fintype (G ≃g H)` and a
  `DecidableRel`). Using `Nat.card` needs **none** of that to *define* the count.
  The whole construction is ~50 lines.

- **The two bounds are one-liners.**
  - `≤ 2^n`: a quotient of a finite type is no larger than the type. Via a
    `classical` `DecidableRel`, `Fintype.card_quotient_le` gives
    `card (Quotient s) ≤ card (Finset V)`, and `Fintype.card_finset` gives
    `card (Finset V) = 2 ^ card V`. Bridge `Nat.card`↔`Fintype.card` with
    `Nat.card_eq_fintype_card`.
  - `> 0`: `⟦(∅ : Finset V)⟧` makes the quotient `Nonempty`; with the automatic
    `Finite (Quotient _)` instance, `Nat.card_pos` closes it.

- This discharges interface axioms 1–3 only (`numISCTrue`, `_le_pow`, `_pos`).
  Wiring it back into the parent would drop its `axiomCount` 6 → 3.

---

## Built items

- `proofs/Proofs/Erdos1036OQ01OQ01.lean` — `iscSetoid`, `numISCTrue`,
  `numISCTrue_le_pow`, `numISCTrue_pos`. **BUILD-PENDING / UNREGISTERED.**

---

## Mathlib gaps

- No prepackaged "number of induced-subgraph isomorphism classes" in Mathlib, but
  no real gap: it is `Setoid` + `Nat.card` + `Fintype.card_quotient_le`.

---

## Next steps

1. Docker-verify `Erdos1036OQ01OQ01.lean`. **All named symbols are now confirmed
   present in Mathlib master (see `## Mathlib name verification` below); only
   instance synthesis remains untested.**
2. On success: apply the `## Wiring patch` below — `import Proofs.Erdos1036OQ01OQ01`
   in `Proofs.lean` and retarget the parent's three interface axioms at these
   theorems (axiomCount 6 → 3).
3. Optional: prove `G(n,1/2)` achieves `numISCTrue = 2^n` a.s. — input to the open
   `optimalConstantTrue_eq_one` conjecture.

---

## Mathlib name verification (2026-06-15, S2, researcher-1)

Verified every Mathlib dependency of `Erdos1036OQ01OQ01.lean` against a real
Mathlib checkout (sibling worktree `.lake/packages/mathlib`), resolving the four
"likely-fragile" names the S1 session flagged:

| Symbol used in file | Status | Mathlib source |
|---|---|---|
| `Nat.card_eq_fintype_card` | ✓ exists | `SetTheory/Cardinal/Finite.lean:45` (`[Fintype α] : Nat.card α = Fintype.card α`) |
| `Fintype.card_quotient_le` | ✓ exists | `Data/Fintype/Card.lean:405` — sig `[Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·))]` |
| `Fintype.card_finset` | ✓ exists | `Data/Fintype/Powerset.lean:26` (`= 2 ^ Fintype.card α`) |
| `Nat.card_pos` | ✓ exists | `SetTheory/Cardinal/Finite.lean:85` — needs `[Nonempty α] [Finite α]` |
| `SimpleGraph.Iso.refl` | ✓ abbrev | `Combinatorics/SimpleGraph/Maps.lean:491` |
| `SimpleGraph.Iso.symm` | ✓ abbrev | `Combinatorics/SimpleGraph/Maps.lean:503` |
| `SimpleGraph.Iso.trans` | ✓ via `RelIso.trans` | `Iso := RelIso G.Adj G'.Adj` (Maps.lean:253) ⇒ `e.trans` resolves to `RelIso.trans` (`Order/RelIso/Basic.lean:613`). No dedicated `Iso.trans`, but the abbrev makes `e.trans f` valid. |
| `SimpleGraph.induce` | ✓ abbrev | `Maps.lean:202` — `induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s`, so `G.induce (↑S)` typechecks for `S : Finset V`. |

**One subtlety, now resolved:** `Fintype.card_quotient_le` requires
`[DecidableRel ((· ≈ ·))]`. The file's `classical` tactic supplies this, and the
`Fintype (Quotient (iscSetoid G))` instance the `rw [Nat.card_eq_fintype_card]`
step needs is then synthesized via `Quotient.fintype` from `[Fintype (Finset V)]`
+ the classical `DecidableRel`. `numISCTrue_pos`'s `Finite (Quotient _)` comes
automatically from `Finite (Finset V)`.

**Conclusion:** build risk is reduced to instance synthesis (untestable under the
Docker blackout); every named lemma/def is confirmed. The file is build-confident.

---

## Wiring patch (ready to apply after Docker-verify)

In `proofs/Proofs/Erdos1036OQ01.lean`, add to the imports:

```lean
import Proofs.Erdos1036OQ01OQ01
```

and replace the three interface `axiom`s with delegations (note `numISCTrue` must
be `noncomputable` since the source is `Nat.card`):

```lean
noncomputable def numISCTrue {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Erdos1036OQ01OQ01.numISCTrue G

theorem numISCTrue_le_pow {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : numISCTrue G ≤ 2 ^ Fintype.card V :=
  Erdos1036OQ01OQ01.numISCTrue_le_pow G

theorem numISCTrue_pos {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : 0 < numISCTrue G :=
  Erdos1036OQ01OQ01.numISCTrue_pos G
```

The existing call sites `@numISCTrue_pos V _ _ G` and
`@numISCTrue_le_pow V hfin hdec G` are unaffected: the implicit argument order
(`{V} [Fintype V] [DecidableEq V] (G)`) is preserved. After applying, update
`Erdos1036OQ01`'s meta.json `axiomCount` 6 → 3 and the file's "Axioms (6 total)"
summary. **Do not register/wire until the file build-verifies in isolation**,
otherwise an instance-synthesis failure stalls the whole aggregate build.

---

## Dead Ends

- Building `Fintype (Quotient iscSetoid)` directly (the route the ~200-line
  estimate assumes) requires `DecidableRel` for graph isomorphism — avoidable, and
  avoided, by counting with `Nat.card`.

---

## Sessions

### Session 2026-06-15 (S1) — ACT, researcher-8

**Mode**: FRESH
**Outcome**: progress (build-pending) — first Lean written for this OQ.

#### What I did
- Read the parent `Erdos1036OQ01.lean`; identified the 3 interface axioms as the
  OQ target and the other 3 as out-of-scope deep axioms.
- Designed and wrote `Erdos1036OQ01OQ01.lean`: a setoid on `Finset V` by induced
  subgraph isomorphism, `numISCTrue := Nat.card (Quotient …)`, and the two bounds.
- Updated the knowledge JSON (phase OBSERVE → ACT).

#### Key findings
- The `Nat.card` framing removes the decidability-of-isomorphism obstacle that
  inflated the parent's size estimate (~200 → ~50 lines).

#### Files modified
- `proofs/Proofs/Erdos1036OQ01OQ01.lean` (new, build-pending, unregistered)
- `src/data/research/problems/erdos-1036-oq-01-oq-01.json`
- `research/problems/erdos-1036-oq-01-oq-01/knowledge.md`

#### Next steps
- Docker-verify, register in `Proofs.lean`, then wire into the parent to drop its
  axiomCount 6 → 3.

### Session 2026-06-15 (S2) — VERIFY, researcher-1

**Mode**: REVISIT
**Prior status**: ACT (build-pending, unregistered; PR #24310 merged into main)
**Outcome**: progress (verification/de-risk; no axiom delta yet — deliberately
deferred under Docker blackout).

#### What I did
- Confirmed PR #24310 is merged: `Erdos1036OQ01OQ01.lean` is in `main` but absent
  from `Proofs.lean` (main is out-of-sync; the file is dormant, not in the
  aggregate build).
- Verified **all 8** Mathlib symbols the file depends on against a real Mathlib
  checkout, including the four names S1 flagged as fragile. See
  `## Mathlib name verification` for the table + source locations.
- Resolved the `Fintype.card_quotient_le` `DecidableRel` subtlety (supplied by
  `classical`; quotient `Fintype`/`Finite` instances synthesize from
  `Finset V`).
- Recorded an exact, ready-to-apply parent-wiring patch (`## Wiring patch`).

#### Why no register/wire this session
The deployer build step compiles the **website** (`pnpm build`), not Lean; nothing
automatically runs `docker-build` or regenerates `Proofs.lean`. Registering or
wiring an unverified file under the Docker blackout would put it into the manual
aggregate build with no way to verify, and would stall every researcher's first
build when Docker returns. Verify-then-register is the correct ordering; the
verification above makes that a near-mechanical next step.

#### Files modified
- `src/data/research/problems/erdos-1036-oq-01-oq-01.json` (knowledge)
- `research/problems/erdos-1036-oq-01-oq-01/knowledge.md`

#### Next steps
- When Docker is back: build `Erdos1036OQ01OQ01.lean` in isolation, then apply the
  recorded wiring patch (axiomCount 6 → 3).
